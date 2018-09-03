/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

A tactic for discharging linear arithmetic goals using Fourier-Motzkin elimination.

`linarith` is (in principle) complete for ℚ and ℝ. It is not complete for non-dense orders, i.e. ℤ.

@TODO: investigate storing comparisons in a list instead of a set, for possible efficiency gains
@TODO: (partial) support for ℕ by casting to ℤ 
@TODO: alternative discharger to `ring`
@TODO: delay proofs of denominator normalization until after contradiction is found
-/

import tactic.ring data.nat.gcd data.list.basic meta.rb_map

meta def nat.to_pexpr : ℕ → pexpr
| 0 := ``(0)
| 1 := ``(1)
| n := if n % 2 = 0 then ``(bit0 %%(nat.to_pexpr (n/2))) else ``(bit1 %%(nat.to_pexpr (n/2)))

open native 
namespace linarith

section lemmas

lemma eq_of_eq_of_eq {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + b = 0 :=
by simp *

lemma le_of_eq_of_le {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b ≤ 0) : a + b ≤ 0 :=
by simp *

lemma lt_of_eq_of_lt {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0 :=
by simp *

lemma le_of_le_of_eq {α} [ordered_semiring α] {a b : α} (ha : a ≤ 0) (hb : b = 0) : a + b ≤ 0 :=
by simp *

lemma lt_of_lt_of_eq {α} [ordered_semiring α] {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0 :=
by simp *

lemma mul_neg {α} [ordered_ring α] {a b : α} (ha : a < 0) (hb : b > 0) : b * a < 0 :=
have (-b)*a > 0, from mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha,
neg_of_neg_pos (by simpa)

lemma mul_nonpos {α} [ordered_ring α] {a b : α} (ha : a ≤ 0) (hb : b > 0) : b * a ≤ 0 :=
have (-b)*a ≥ 0, from mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha,
nonpos_of_neg_nonneg (by simp at this; exact this)

lemma mul_eq {α} [ordered_semiring α] {a b : α} (ha : a = 0) (hb : b > 0) : b * a = 0 :=
by simp *

lemma eq_of_not_lt_of_not_gt {α} [linear_order α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

lemma add_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) : 
      n * (e1 + e2) = t1 + t2 := by simp [left_distrib, *]

lemma sub_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) : 
      n * (e1 - e2) = t1 - t2 := by simp [left_distrib, *]

lemma neg_subst {α} [ring α] {n e t : α} (h1 : n * e = t) : n * (-e) = -t := by simp *

private meta def apnn : tactic unit := `[norm_num]

lemma mul_subst {α} [comm_ring α] {n1 n2 k e1 e2 t1 t2 : α} (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2) 
     (h3 : n1*n2 = k . apnn) : k * (e1 * e2) = t1 * t2 := 
have h3 : n1 * n2 = k, from h3,
by rw [←h3, mul_comm n1, mul_assoc n2, ←mul_assoc n1, h1, ←mul_assoc n2, mul_comm n2, mul_assoc, h2] -- OUCH

lemma div_subst {α} [field α] {n1 n2 k e1 e2 t1 : α} (h1 : n1 * e1 = t1) (h2 : n2 / e2 = 1) (h3 : n1*n2 = k) :
      k * (e1 / e2) = t1 := 
by rw [←h3, mul_assoc, mul_div_comm, h2, ←mul_assoc, h1, mul_comm, one_mul]

end lemmas 

section datatypes

@[derive decidable_eq]
inductive ineq
| eq | le | lt

open ineq 

def ineq.max : ineq → ineq → ineq
| eq a := a 
| le a := a 
| lt a := lt 

def ineq.is_lt : ineq → ineq → bool 
| eq le := tt
| eq lt := tt 
| le lt := tt 
| _ _ := ff

def ineq.to_string : ineq → string 
| eq := "="
| le := "≤"
| lt := "<"

instance : has_to_string ineq := ⟨ineq.to_string⟩

/--
  The main datatype for FM elimination.
  Variables are represented by natural numbers, each of which has an integer coefficient.
  Index 0 is reserved for constants, i.e. `coeffs.find 0` is the coefficient of 1.
  The represented term is coeffs.keys.sum (λ i, coeffs.find i * Var[i]).
  str determines the direction of the comparison -- is it < 0, ≤ 0, or = 0?
-/
meta structure comp :=
(str : ineq)
(coeffs : rb_map ℕ int)

meta instance : inhabited comp := ⟨⟨ineq.eq, mk_rb_map⟩⟩

meta inductive comp_source 
| assump : ℕ → comp_source
| add : comp_source → comp_source → comp_source
| scale : ℕ → comp_source → comp_source

meta def comp_source.flatten : comp_source → rb_map ℕ ℕ
| (comp_source.assump n) := mk_rb_map.insert n 1
| (comp_source.add c1 c2) := (comp_source.flatten c1).add (comp_source.flatten c2)
| (comp_source.scale n c) := (comp_source.flatten c).map (λ v, v * n)

meta def comp_source.to_string : comp_source → string 
| (comp_source.assump e) := to_string e
| (comp_source.add c1 c2) := comp_source.to_string c1 ++ " + " ++ comp_source.to_string c2
| (comp_source.scale n c) := to_string n ++ " * " ++ comp_source.to_string c 

meta instance comp_source.has_to_format : has_to_format (comp_source) :=
⟨λ a, comp_source.to_string a⟩

meta structure pcomp :=
(c : comp)
(src : comp_source)

def alist_lt : list (ℕ × ℤ) → list (ℕ × ℤ) → bool 
| [] [] := ff
| [] (_::_) := tt
| (_::_) [] := ff
| ((a1, z1)::t1) ((a2, z2)::t2) :=
    (a1 < a2) || ((a1 = a2) && ((z1 < z2) || (z1 = z2 ∧ alist_lt t1 t2)))  

meta def map_lt (m1 m2 : rb_map ℕ int) : bool :=
alist_lt m1.to_list m2.to_list

-- make more efficient
meta def comp.lt (c1 c2 : comp) : bool :=
(c1.str.is_lt c2.str) || (map_lt c1.coeffs c2.coeffs) 

meta instance comp.has_lt : has_lt comp := ⟨λ a b, comp.lt a b⟩
meta instance pcomp.has_lt : has_lt pcomp := ⟨λ p1 p2, p1.c < p2.c⟩
meta instance pcomp.has_lt_dec : decidable_rel ((<) : pcomp → pcomp → Prop) := by apply_instance

meta def comp.coeff_of (c : comp) (a : ℕ) : ℤ :=
c.coeffs.zfind a

meta def comp.scale (c : comp) (n : ℕ) : comp :=
{ c with coeffs := c.coeffs.map ((*) (n : ℤ)) }

meta def comp.add (c1 c2 : comp) : comp :=
⟨c1.str.max c2.str, c1.coeffs.add c2.coeffs⟩

meta def pcomp.scale (c : pcomp) (n : ℕ) : pcomp := 
⟨c.c.scale n, comp_source.scale n c.src⟩ 

meta def pcomp.add (c1 c2 : pcomp) : pcomp :=
⟨c1.c.add c2.c, comp_source.add c1.src c2.src⟩

meta instance pcomp.to_format : has_to_format pcomp :=
⟨λ p, to_fmt p.c.coeffs ++ to_string p.c.str ++ "0"⟩

meta instance comp.to_format : has_to_format comp :=
⟨λ p, to_fmt p.coeffs⟩

end datatypes

section fm_elim

/-- If c1 and c2 both contain variable a with opposite coefficients,
   produces v1, v2, and c such that a has been cancelled in c := v1*c1 + v2*c2 -/
meta def elim_var (c1 c2 : comp) (a : ℕ) : option (ℕ × ℕ × comp) :=
let v1 := c1.coeff_of a,
    v2 := c2.coeff_of a in
if v1 * v2 < 0 then 
  let vlcm :=  nat.lcm v1.nat_abs v2.nat_abs,
      v1' := vlcm / v1.nat_abs,
      v2' := vlcm / v2.nat_abs in
  some ⟨v1', v2', comp.add (c1.scale v1') (c2.scale v2')⟩ 
else none

meta def pelim_var (p1 p2 : pcomp) (a : ℕ) : option pcomp := 
do (n1, n2, c) ← elim_var p1.c p2.c a,
   return ⟨c, comp_source.add (p1.src.scale n1) (p2.src.scale n2)⟩

meta def comp.is_contr (c : comp) : bool := c.coeffs.keys = [] ∧ c.str = ineq.lt

meta def pcomp.is_contr (p : pcomp) : bool := p.c.is_contr

meta def elim_with_set (a : ℕ) (p : pcomp) (comps : rb_set pcomp) : rb_set pcomp :=
if ¬ p.c.coeffs.contains a then mk_rb_set.insert p else 
comps.fold mk_rb_set $ λ pc s, 
match pelim_var p pc a with 
| some pc := s.insert pc
| none := s 
end

meta def find_contr_in_set (comps : rb_set pcomp) : option pcomp :=
match (comps.filter pcomp.is_contr).keys with 
| [] := none 
| (h::t) := some h
end

/-- 
  The state for the elimination monad.
    vars: the set of variables present in comps
    comps: a set of comparisons
    inputs: a set of pairs of exprs (t, pf), where t is a term and pf is a proof that t {<, ≤, =} 0,
      indexed by ℕ.
    has_false: stores a pcomp of 0 < 0 if one has been found
    TODO: is it more efficient to store comps as a list, to avoid comparisons?
-/
meta structure linarith_structure :=
(vars : rb_set ℕ)
(comps : rb_set pcomp)
(inputs : rb_map ℕ (expr × expr)) -- first is term, second is proof of comparison
(has_false : option pcomp) 

@[reducible] meta def linarith_monad := state (linarith_structure)

meta instance : monad (linarith_monad) := state_t.monad 

meta def get_var_list : linarith_monad (list ℕ) :=
⟨λ s, ⟨s.vars.to_list, s⟩⟩

meta def get_vars : linarith_monad (rb_set ℕ) :=
⟨λ s, ⟨s.vars, s⟩⟩

meta def get_comps : linarith_monad (rb_set pcomp) :=
⟨λ s, ⟨s.comps, s⟩⟩

meta def get_contr : linarith_monad (option pcomp) :=
linarith_structure.has_false <$> get

meta def is_contr : linarith_monad bool :=
option.is_some <$> get_contr 

meta def assert_contr (p : pcomp) : linarith_monad unit :=
⟨λ s, ((), { s with has_false := some p })⟩

meta def update_vars_and_comps (vars : rb_set ℕ) (comps : rb_set pcomp) : linarith_monad unit := 
⟨λ s, ⟨(), ⟨vars, comps, s.inputs, s.has_false⟩⟩⟩

-- TODO: possible to short circuit earlier
meta def monad.elim_var (a : ℕ) : linarith_monad unit :=
do vs ← get_vars, isc ← is_contr,
   if (¬ vs.contains a) ∨ isc then return () else
do comps ← get_comps,
   let cs' := comps.fold mk_rb_set (λ p s, s.union (elim_with_set a p comps)),
   match find_contr_in_set cs' with 
   | none := update_vars_and_comps (vs.erase a) cs'
   | some p := assert_contr p 
   end

meta def elim_all_vars : linarith_monad unit := 
do vs ← get_var_list,
   vs.mfoldl (λ _ a, monad.elim_var a) ()

end fm_elim

section parse

open ineq tactic 

meta def map_of_expr_mul_aux (c1 c2 : rb_map ℕ ℤ) : option (rb_map ℕ ℤ) :=
match c1.keys, c2.keys with 
| [0], _ := some $ c2.scale (c1.zfind 0)
| _, [0] := some $ c1.scale (c2.zfind 0)
| _, _ := none
end

/--
  Turns an expression into a map from ℕ to ℤ, for use in a comp object.
    The rb_map expr ℕ argument identifies which expressions have already been assigned numbers.
    The ℕ argument identifies the next unused number.
    Returns a new map and new max.
-/
meta def map_of_expr : rb_map expr ℕ → ℕ → expr → option (rb_map expr ℕ × ℕ × rb_map ℕ ℤ)
| m max `(%%e1 * %%e2) := 
   do (m', max', comp1) ← map_of_expr m max e1, 
      (m', max', comp2) ← map_of_expr m' max' e2,
      mp ← map_of_expr_mul_aux comp1 comp2,
      return (m', max', mp)
| m max `(%%e1 + %%e2) :=
   do (m', max', comp1) ← map_of_expr m max e1, 
      (m', max', comp2) ← map_of_expr m' max' e2,
      return (m', max', comp1.add comp2)
| m max `(%%e1 - %%e2) :=
   do (m', max', comp1) ← map_of_expr m max e1, 
      (m', max', comp2) ← map_of_expr m' max' e2,
      return (m', max', comp1.add (comp2.scale (-1)))
| m max `(-%%e) := do (m', max', comp) ← map_of_expr m max e, return (m', max', comp.scale (-1))
| m max e := 
  match e.to_int, m.find e with
  | some z, _ := return ⟨m, max, mk_rb_map.insert 0 z⟩ 
  | none, some k := return (m, max, mk_rb_map.insert k 1) 
  | none, none := return (m.insert e max, max + 1, mk_rb_map.insert max 1)
  end

meta def parse_into_comp_and_expr : expr → option (ineq × expr)
| `(%%e < 0) := (ineq.lt, e)
| `(%%e ≤ 0) := (ineq.le, e)
| `(%%e = 0) := (ineq.eq, e) 
| _ := none

meta def to_comp (e : expr) (m : rb_map expr ℕ) (max : ℕ) : option (comp × rb_map expr ℕ × ℕ) :=
do (iq, e) ← parse_into_comp_and_expr e,
   (m', max', comp') ← map_of_expr m max e,
   return ⟨⟨iq, comp'⟩, m', max'⟩

meta def to_comp_fold : rb_map expr ℕ → ℕ → list expr → 
      (list (option comp) × rb_map expr ℕ × ℕ)
| m max [] := ([], m, max)
| m max (h::t) := 
  match to_comp h m max with 
  | some (c, m', max') := let (l, mp, n) := to_comp_fold m' max' t in (c::l, mp, n)
  | none := let (l, mp, n) := to_comp_fold m max t in (none::l, mp, n)
  end

def reduce_pair_option {α β} : list (α × option β) → list (α × β)
| [] := []
| ((a,none)::t) := reduce_pair_option t 
| ((a,some b)::t) := (a,b)::reduce_pair_option t 

/--
  Takes a list of proofs of props of the form t {<, ≤, =} 0, and creates a linarith_structure.
-/
meta def mk_linarith_structure (l : list expr) : tactic linarith_structure := 
do pftps ← l.mmap infer_type,
   let (l', map, max) := to_comp_fold mk_rb_map 1 pftps,
   let lz := reduce_pair_option ((l.zip pftps).zip l'),
   let prmap := rb_map.of_list $ (list.range lz.length).map (λ n, (n, (lz.inth n).1)),
   let vars : rb_set ℕ := rb_map.of_list $ (list.range (max)).map (λ k, (k, ())),
   let pc : rb_set pcomp := 
     rb_map.of_list $ (list.range lz.length).map (λ n, (⟨(lz.inth n).2, comp_source.assump n⟩, ())),
   return ⟨vars, pc, prmap, none⟩ 

end parse 

section prove
open ineq tactic 

meta def get_rel_sides : expr → tactic (expr × expr)
| `(%%a < %%b) := return (a, b)
| `(%%a ≤ %%b) := return (a, b)
| `(%%a = %%b) := return (a, b)
| _ := failed

meta def mul_expr (n : ℕ) (e : expr) : pexpr :=
if n = 1 then ``(%%e) else
``(%%(nat.to_pexpr n) * %%e)

meta def add_exprs_aux : pexpr → list pexpr → pexpr 
| p [] := p
| p [a] := ``(%%p + %%a)
| p (h::t) := add_exprs_aux ``(%%p + %%h) t 

meta def add_exprs : list pexpr → pexpr 
| [] := ``(0)
| (h::t) := add_exprs_aux h t

meta def find_contr (m : rb_set pcomp) : option pcomp :=
m.keys.find (λ p, p.c.is_contr)

meta def ineq_const_mul_nm : ineq → name 
| lt := ``mul_neg
| le := ``mul_nonpos
| eq := ``mul_eq

meta def ineq_const_nm : ineq → ineq → (name × ineq)
| eq eq := (``eq_of_eq_of_eq, eq)
| eq le := (``le_of_eq_of_le, le)
| eq lt := (``lt_of_eq_of_lt, lt)
| le eq := (``le_of_le_of_eq, le)
| le le := (`add_nonpos, le)
| le lt := (`add_neg_of_nonpos_of_neg, lt)
| lt eq := (``lt_of_lt_of_eq, lt)
| lt le := (`add_neg_of_neg_of_nonpos, lt)
| lt lt := (`add_neg, lt)

meta def mk_single_comp_zero_pf (c : ℕ) (h : expr) : tactic (ineq × expr) :=
do tp ← infer_type h,
  some (iq, e) ← return $ parse_into_comp_and_expr tp,
  if c = 0 then 
    do e' ← mk_app ``zero_mul [e], return (eq, e')
  else if c = 1 then return (iq, h)
  else      
    do nm ← resolve_name (ineq_const_mul_nm iq), 
       tp ← (prod.snd <$> (infer_type h >>= get_rel_sides)) >>= infer_type,
       cpos ← to_expr ``((%%c.to_pexpr : %%tp) > 0),
       (_, ex) ← solve_aux cpos `[norm_num, done],
--       e' ← mk_app (ineq_const_mul_nm iq) [h, ex], -- this takes many seconds longer in some examples! why?
       e' ← to_expr ``(%%nm %%h %%ex) ff,
       return (iq, e')

meta def mk_lt_zero_pf_aux (c : ineq) (pf npf : expr) (coeff : ℕ) : tactic (ineq × expr) :=
do (iq, h') ← mk_single_comp_zero_pf coeff npf,
   let (nm, niq) := ineq_const_nm c iq,
   n ← resolve_name nm,
   e' ← to_expr ``(%%n %%pf %%h'),
   return (niq, e')

/--
  Takes a list of coefficients [c] and list of expressions, of equal length.
  Each expression is a proof of a prop of the form t {<, ≤, =} 0.
  Produces a proof that the sum of (c*t) {<, ≤, =} 0, where the comp is as strong as possible.
-/
meta def mk_lt_zero_pf : list ℕ → list expr → tactic expr 
| _ [] := fail "no linear hypotheses found"
| [c] [h] := prod.snd <$> mk_single_comp_zero_pf c h
| (c::ct) (h::t) := 
  do (iq, h') ← mk_single_comp_zero_pf c h,
     prod.snd <$> (ct.zip t).mfoldl (λ pr ce, mk_lt_zero_pf_aux pr.1 pr.2 ce.2 ce.1) (iq, h')
| _ _ := fail "not enough args to mk_lt_zero_pf"

meta def term_of_ineq_prf (prf : expr) : tactic expr :=
do (lhs, _) ← infer_type prf >>= get_rel_sides,
   return lhs

meta structure linarith_config :=
(discharger : tactic unit := `[ring])
(restrict_type : option Type := none)
(restrict_type_reflect : reflected restrict_type . apply_instance)

meta def ineq_pf_tp (pf : expr) : tactic expr :=
do (_, z) ← infer_type pf >>= get_rel_sides,
   infer_type z

meta def mk_neg_one_lt_zero_pf (tp : expr) : tactic expr :=
to_expr ``((neg_neg_of_pos zero_lt_one : -1 < (0 : %%tp)))

/--
  Assumes e is a proof that t = 0. Creates a proof that -t = 0.
-/
meta def mk_neg_eq_zero_pf (e : expr) : tactic expr := 
to_expr ``(neg_eq_zero.mpr %%e)

meta def add_neg_eq_pfs : list expr → tactic (list expr)
| [] := return []
| (h::t) := 
  do some (iq, tp) ← parse_into_comp_and_expr <$> infer_type h,
  match iq with 
  | ineq.eq := do nep ← mk_neg_eq_zero_pf h, tl ← add_neg_eq_pfs t, return $ h::nep::tl
  | _ := list.cons h <$> add_neg_eq_pfs t
  end 

/--
  Takes a list of proofs of propositions of the form t {<, ≤, =} 0,
  and tries to prove the goal `false`.
-/
meta def prove_false_by_linarith1 (cfg : linarith_config) : list expr → tactic unit 
| [] := fail "no args to linarith"
| l@(h::t) :=
do extp ← match cfg.restrict_type with 
          | none := do (_, z) ← infer_type h >>= get_rel_sides, infer_type z
          | some rtp := 
             do m ← mk_mvar,
                unify `(some %%m : option Type) cfg.restrict_type_reflect,
                return m
          end,
   hz ← mk_neg_one_lt_zero_pf extp, 
   l' ← if cfg.restrict_type.is_some then 
           l.mfilter (λ e, (ineq_pf_tp e >>= is_def_eq extp >> return tt) <|> return ff)
        else return l,
   l' ← add_neg_eq_pfs l',
   struct ← mk_linarith_structure (hz::l'),
   let e : linarith_structure := (elim_all_vars.run struct).2,
   let contr := e.has_false,
   guard contr.is_some <|> fail "linarith failed to find a contradiction",
   some contr ← return $ contr,
   let coeffs := e.inputs.keys.map (λ k, (contr.src.flatten.ifind k)),
   let pfs : list expr := e.inputs.keys.map (λ k, (e.inputs.ifind k).1), 
   let zip := (coeffs.zip pfs).filter (λ pr, pr.1 ≠ 0),
   coeffs ← return $ zip.map prod.fst,
   pfs ← return $ zip.map prod.snd,
   mls ← zip.mmap (λ pr, do e ← term_of_ineq_prf pr.2, return (mul_expr pr.1 e)),
   sm ← to_expr $ add_exprs mls,
   tgt ← to_expr ``(%%sm = 0),
   (a, b) ← solve_aux tgt (cfg.discharger >> done),
   pf ← mk_lt_zero_pf coeffs pfs,
   pftp ← infer_type pf,
   (_, nep, _) ← rewrite_core b pftp,
   pf' ← mk_eq_mp nep pf,
   mk_app `lt_irrefl [pf'] >>= exact 

end prove

section normalize
open tactic

meta def rearr_comp (prf : expr) : expr → tactic expr 
| `(%%a ≤ 0) := return prf 
| `(%%a < 0) := return prf 
| `(%%a = 0) := return prf 
| `(%%a ≥ 0) := to_expr ``(neg_nonpos.mpr %%prf) 
| `(%%a > 0) := to_expr ``(neg_neg_of_pos %%prf) --mk_app ``neg_neg_of_pos [prf]
| `(%%a ≤ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| `(%%a < %%b) := to_expr ``(sub_neg_of_lt %%prf) -- mk_app ``sub_neg_of_lt [prf]
| `(%%a = %%b) := to_expr ``(sub_eq_zero.mpr %%prf)
| `(%%a > %%b) := to_expr ``(sub_neg_of_lt %%prf) -- mk_app ``sub_neg_of_lt [prf]
| `(%%a ≥ %%b) := to_expr ``(sub_nonpos.mpr %%prf)
| _ := fail "couldn't rearrange comp"

meta def is_numeric : expr → option ℚ 
| `(%%e1 + %%e2) := do v1 ← is_numeric e1, v2 ← is_numeric e2, return $ v1 + v2
| `(%%e1 - %%e2) := do v1 ← is_numeric e1, v2 ← is_numeric e2, return $ v1 - v2
| `(%%e1 * %%e2) := do v1 ← is_numeric e1, v2 ← is_numeric e2, return $ v1 * v2
| `(%%e1 / %%e2) := do v1 ← is_numeric e1, v2 ← is_numeric e2, return $ v1 / v2
| `(-%%e) := rat.neg <$> is_numeric e
| e := e.to_rat

inductive {u} tree (α : Type u) : Type u
| nil {} : tree 
| node : α → tree → tree → tree

def tree.repr {α} [has_repr α] : tree α → string
| tree.nil := "nil"
| (tree.node a t1 t2) := "tree.node " ++ repr a ++ " (" ++ tree.repr t1 ++ ") (" ++ tree.repr t2 ++ ")"

instance {α} [has_repr α] : has_repr (tree α) := ⟨tree.repr⟩

meta def find_cancel_factor : expr → ℕ × tree ℕ
| `(%%e1 + %%e2) := 
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in 
  (lcm, tree.node lcm t1 t2)
| `(%%e1 - %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in 
  (lcm, tree.node lcm t1 t2) 
| `(%%e1 * %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, pd := v1*v2 in 
  (pd, tree.node pd t1 t2) 
| `(%%e1 / %%e2) := --do q ← is_numeric e2, return q.num.nat_abs
  match is_numeric e2 with 
  | some q := let (v1, t1) := find_cancel_factor e1, n := v1.lcm q.num.nat_abs in
    (n, tree.node n t1 (tree.node q.num.nat_abs tree.nil tree.nil))
  | none := (1, tree.node 1 tree.nil tree.nil)
  end
| `(-%%e) := find_cancel_factor e 
| _ := (1, tree.node 1 tree.nil tree.nil)

open tree

meta def mk_prod_prf : ℕ → tree ℕ → expr → tactic expr
| v (node _ lhs rhs) `(%%e1 + %%e2) := 
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``add_subst [v1, v2]
| v (node _ lhs rhs) `(%%e1 - %%e2) := 
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``sub_subst [v1, v2]
| v (node n lhs@(node ln _ _) rhs) `(%%e1 * %%e2) := 
  do tp ← infer_type e1, v1 ← mk_prod_prf ln lhs e1, v2 ← mk_prod_prf (v/ln) rhs e2, 
     ln' ← tp.of_nat ln, vln' ← tp.of_nat (v/ln), v' ← tp.of_nat v,
     ntp ← to_expr ``(%%ln' * %%vln' = %%v'),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     mk_app ``mul_subst [v1, v2, npf]
| v (node n lhs rhs@(node rn _ _)) `(%%e1 / %%e2) := 
  do tp ← infer_type e1, v1 ← mk_prod_prf (v/rn) lhs e1,
     rn' ← tp.of_nat rn, vrn' ← tp.of_nat (v/rn), n' ← tp.of_nat n, v' ← tp.of_nat v,
     ntp ← to_expr ``(%%rn' / %%e2 = 1), 
     (_, npf) ← solve_aux ntp `[norm_num, done],
     ntp2 ← to_expr ``(%%vrn' * %%n' = %%v'),
     (_, npf2) ← solve_aux ntp2 `[norm_num, done],
     mk_app ``div_subst [v1, npf, npf2]
| v t `(-%%e) := do v' ← mk_prod_prf v t e, mk_app ``neg_subst [v'] 
| v _ e := 
  do tp ← infer_type e, 
     v' ← tp.of_nat v,
     e' ← to_expr ``(%%v' * %%e),
     mk_app `eq.refl [e']

/--
 e is a term with rational division. produces a natural number n and a proof that n*e = e', 
 where e' has no division.
-/
meta def kill_factors (e : expr) : tactic (ℕ × expr) :=
let (n, t) := find_cancel_factor e in 
do e' ← mk_prod_prf n t e, return (n, e')

open expr
meta def expr_contains (n : name) : expr → bool 
| (const nm _) := nm = n
| (lam _ _ _ bd) := expr_contains bd 
| (pi _ _ _ bd) := expr_contains bd 
| (app e1 e2) := expr_contains e1 || expr_contains e2
| _ := ff

lemma sub_into_lt {α} [ordered_semiring α] {a b : α} (he : a = b) (hl : a ≤ 0) : b ≤ 0 :=
by rwa he at hl

meta def norm_hyp_aux (h' lhs : expr) : tactic expr :=
do (v, lhs') ← kill_factors lhs, 
   (ih, h'') ← mk_single_comp_zero_pf v h',
   (_, nep, _) ← infer_type h'' >>= rewrite_core lhs',
   mk_eq_mp nep h''

meta def norm_hyp (h : expr) : tactic expr :=
do htp ← infer_type h,
   h' ← rearr_comp h htp,
   some (c, lhs) ← parse_into_comp_and_expr <$> infer_type h',
   if expr_contains `has_div.div lhs then 
     norm_hyp_aux h' lhs 
   else return h' 

meta def get_contr_lemma_name : expr → tactic name
| `(%%a < %%b) := return `lt_of_not_ge
| `(%%a ≤ %%b) := return `le_of_not_gt
| `(%%a = %%b) := return ``eq_of_not_lt_of_not_gt
| `(%%a ≥ %%b) := return `le_of_not_gt
| `(%%a > %%b) := return `lt_of_not_ge
| _ := fail "target type not supported by linarith"

/--
  Takes a list of proofs of propositions.
  Filters out the proofs of linear (in)equalities,
  and tries to use them to prove `false`.
-/
meta def prove_false_by_linarith (cfg : linarith_config) (l : list expr) : tactic unit :=
do ls ← l.mmap (λ h, (do s ← norm_hyp h, return (some s)) <|> return none),
   prove_false_by_linarith1 cfg ls.reduce_option

end normalize

end linarith

section
open tactic linarith

open lean lean.parser interactive tactic interactive.types
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def linarith.interactive_aux (cfg : linarith_config) : 
     parse ident* → (parse (tk "using" *> pexpr_list)?) → tactic unit
| l (some pe) := pe.mmap (λ p, i_to_expr p >>= note_anon) >> linarith.interactive_aux l none
| [] none := 
  do t ← target,
     if t = `(false) then local_context >>= prove_false_by_linarith cfg
     else do nm ← get_contr_lemma_name t, seq (applyc nm) (intro1 >> linarith.interactive_aux [] none)
| ls none := (ls.mmap get_local) >>= prove_false_by_linarith cfg

/--
  If the goal is `false`, tries to prove it by linear arithmetic on hypotheses.
  If the goal is a linear (in)equality, tries to prove it by contradiction.
  `linarith` will use all relevant hypotheses in the local context.
  `linarith h1 h2 h3` will only use hypotheses h1, h2, h3.
  `linarith using [t1, t2, t3]` will add proof terms t1, t2, t3 to the local context.
-/
meta def tactic.interactive.linarith (ids : parse (many ident)) 
     (using_hyps : parse (tk "using" *> pexpr_list)?) (cfg : linarith_config := {}) : tactic unit :=
linarith.interactive_aux cfg ids using_hyps

end