/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.dlist data.dlist.basic data.prod category.basic
  tactic.basic tactic.rcases tactic.generalize_proofs
  tactic.split_ifs meta.expr tactic.ext
  logic.basic

open lean
open lean.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic
namespace interactive
open interactive interactive.types expr

local notation `listΣ` := list_Sigma
local notation `listΠ` := list_Pi

/--
This parser uses the "inverted" meaning for the `many` constructor:
rather than representing a sum of products, here it represents a
product of sums. We fix this by applying `invert`, defined below, to
the result.
-/
@[reducible] def rcases_patt_inverted := rcases_patt

meta def rcases_parse1 (rcases_parse : parser (listΣ rcases_patt_inverted)) :
  parser rcases_patt_inverted | x :=
((rcases_patt.one <$> ident_) <|>
(rcases_patt.many <$> brackets "⟨" "⟩" (sep_by (tk ",") rcases_parse))) x

meta def rcases_parse : parser (listΣ rcases_patt_inverted) :=
with_desc "patt" $
list.cons <$> rcases_parse1 rcases_parse <*> (tk "|" *> rcases_parse1 rcases_parse)*

meta def rcases_parse_single : parser rcases_patt_inverted :=
with_desc "patt_list" $ rcases_parse1 rcases_parse

meta mutual def rcases_parse.invert, rcases_parse.invert'
with rcases_parse.invert : listΣ rcases_patt_inverted → listΣ (listΠ rcases_patt)
| l := l.map $ λ p, match p with
| rcases_patt.one n := [rcases_patt.one n]
| rcases_patt.many l := rcases_parse.invert' <$> l
end
with rcases_parse.invert' : listΣ rcases_patt_inverted → rcases_patt
| [rcases_patt.one n] := rcases_patt.one n
| l := rcases_patt.many (rcases_parse.invert l)

/--
The `rcases` tactic is the same as `cases`, but with more flexibility in the
`with` pattern syntax to allow for recursive case splitting. The pattern syntax
uses the following recursive grammar:

```
patt ::= (patt_list "|")* patt_list
patt_list ::= id | "_" | "⟨" (patt ",")* patt "⟩"
```

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.
-/
meta def rcases (p : parse texpr) (ids : parse (tk "with" *> rcases_parse)?) : tactic unit :=
tactic.rcases p $ rcases_parse.invert $ ids.get_or_else [default _]

meta def rintro_parse : parser rcases_patt :=
rcases_parse.invert' <$> (brackets "(" ")" rcases_parse <|>
  (λ x, [x]) <$> rcases_parse_single)

/--
The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintros (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.
-/
meta def rintro : parse rintro_parse* → tactic unit
| [] := intros []
| l  := tactic.rintro l

/--
This is a "finishing" tactic modification of `simp`. The tactic `simpa [rules, ...] using e`
will simplify the hypothesis `e` using `rules`, then simplify the goal using `rules`, and
try to close the goal using `assumption`. If `e` is a term instead of a local constant,
it is first added to the local context using `have`.
-/
meta def simpa (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  (tgt : parse (tk "using" *> texpr)?) (cfg : simp_config_ext := {}) : tactic unit :=
let simp_at (lc) := simp use_iota_eqn no_dflt hs attr_names (loc.ns lc) cfg >> try (assumption <|> trivial) in
match tgt with
| none := get_local `this >> simp_at [some `this, none] <|> simp_at [none]
| some e :=
  (do e ← i_to_expr e,
    match e with
    | local_const _ lc _ _ := simp_at [some lc, none]
    | e := do
      t ← infer_type e,
      assertv `this t e >> simp_at [some `this, none]
    end) <|> (do
      simp_at [none],
      ty ← target,
      e ← i_to_expr_strict ``(%%e : %%ty), -- for positional error messages, don't care about the result
      pty ← pp ty, ptgt ← pp e,
      -- Fail deliberately, to advise regarding `simp; exact` usage
      fail ("simpa failed, 'using' expression type not directly " ++
        "inferrable. Try:\n\nsimpa ... using\nshow " ++
        to_fmt pty ++ ",\nfrom " ++ ptgt : format))
end

/-- `try_for n { tac }` executes `tac` for `n` ticks, otherwise uses `sorry` to close the goal.
  Never fails. Useful for debugging. -/
meta def try_for (max : parse parser.pexpr) (tac : itactic) : tactic unit :=
do max ← i_to_expr_strict max >>= tactic.eval_expr nat,
   tactic.try_for max tac <|>
     (tactic.trace "try_for timeout, using sorry" >> admit)

/-- Multiple subst. `substs x y z` is the same as `subst x, subst y, subst z`. -/
meta def substs (l : parse ident*) : tactic unit :=
l.mmap' (λ h, get_local h >>= tactic.subst)

/-- Unfold coercion-related definitions -/
meta def unfold_coes (loc : parse location) : tactic unit :=
unfold [``coe,``lift_t,``has_lift_t.lift,``coe_t,``has_coe_t.coe,``coe_b,``has_coe.coe,
        ``coe_fn, ``has_coe_to_fun.coe, ``coe_sort, ``has_coe_to_sort.coe] loc

/-- For debugging only. This tactic checks the current state for any
  missing dropped goals and restores them. Useful when there are no
  goals to solve but "result contains meta-variables". -/
meta def recover : tactic unit :=
do r ← tactic.result,
   tactic.set_goals $ r.fold [] $ λ e _ l,
     match e with
     | expr.mvar _ _ _ := insert e l
     | _ := l
     end

/-- Like `try { tac }`, but in the case of failure it continues
  from the failure state instead of reverting to the original state. -/
meta def continue (tac : itactic) : tactic unit :=
λ s, result.cases_on (tac s)
 (λ a, result.success ())
 (λ e ref, result.success ())

/-- Move goal `n` to the front. -/
meta def swap (n := 2) : tactic unit :=
if n = 2 then tactic.swap else tactic.rotate (n-1)

/-- Generalize proofs in the goal, naming them with the provided list. -/
meta def generalize_proofs : parse ident_* → tactic unit :=
tactic.generalize_proofs

/-- Clear all hypotheses starting with `_`, like `_match` and `_let_match`. -/
meta def clear_ : tactic unit := tactic.repeat $ do
  l ← local_context,
  l.reverse.mfirst $ λ h, do
    name.mk_string s p ← return $ local_pp_name h,
    guard (s.front = '_'),
    cl ← infer_type h >>= is_class, guard (¬ cl),
    tactic.clear h

/-- Same as the `congr` tactic, but takes an optional argument which gives
  the depth of recursive applications. This is useful when `congr`
  is too aggressive in breaking down the goal. For example, given
  `⊢ f (g (x + y)) = f (g (y + x))`, `congr'` produces the goals `⊢ x = y`
  and `⊢ y = x`, while `congr' 2` produces the intended `⊢ x + y = y + x`. -/
meta def congr' : parse (with_desc "n" small_nat)? → tactic unit
| (some 0) := failed
| o        := focus1 (assumption <|> (congr_core >>
  all_goals (reflexivity <|> try (congr' (nat.pred <$> o)))))

/-- Acts like `have`, but removes a hypothesis with the same name as
  this one. For example if the state is `h : p ⊢ goal` and `f : p → q`,
  then after `replace h := f h` the goal will be `h : q ⊢ goal`,
  where `have h := f h` would result in the state `h : p, h : q ⊢ goal`.
  This can be used to simulate the `specialize` and `apply at` tactics
  of Coq. -/
meta def replace (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic unit :=
do let h := h.get_or_else `this,
  old ← try_core (get_local h),
  «have» h q₁ q₂,
  match old, q₂ with
  | none,   _      := skip
  | some o, some _ := tactic.clear o
  | some o, none   := swap >> tactic.clear o >> swap
  end

meta def symm_apply (e : expr) (cfg : apply_cfg := {}) : tactic (list (name × expr)) :=
tactic.apply e cfg <|> (symmetry >> tactic.apply e cfg)
/--
  `apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
  where `head` matches the current goal.

  alternatively, when encountering an assumption of the form `sg₀ → ¬ sg₁`,
  after the main approach failed, the goal is dismissed and `sg₀` and `sg₁`
  are made into the new goal.

  optional arguments:
  - asms: list of rules to consider instead of the local constants
  - tac:  a tactic to run on each subgoals after applying an assumption; if
          this tactic fails, the corresponding assumption will be rejected and
          the next one will be attempted.
 -/
meta def apply_assumption
  (asms : option (list expr) := none)
  (tac : tactic unit := return ()) : tactic unit :=
do { ctx ← asms.to_monad <|> local_context,
     ctx.any_of (λ H, () <$ symm_apply H ; tac) } <|>
do { exfalso,
     ctx ← asms.to_monad <|> local_context,
     ctx.any_of (λ H, () <$ symm_apply H ; tac) }
<|> fail "assumption tactic failed"

open nat

meta def solve_by_elim_aux (discharger : tactic unit) (asms : option (list expr))  : ℕ → tactic unit
| 0 := done
| (succ n) := discharger <|> (apply_assumption asms $ solve_by_elim_aux n)

meta structure by_elim_opt :=
  (discharger : tactic unit := done)
  (restr_hyp_set : option (list expr) := none)
  (max_rep : ℕ := 3)

/--
  `solve_by_elim` calls `apply_assumption` on the main goal to find an assumption whose head matches
  and repeated calls `apply_assumption` on the generated subgoals until no subgoals remains
  or up to `depth` times.

  `solve_by_elim` discharges the current goal or fails

  `solve_by_elim` does some back-tracking if `apply_assumption` chooses an unproductive assumption

  optional arguments:
  - discharger: a subsidiary tactic to try at each step (`cc` is often helpful)
  - asms: list of assumptions / rules to consider instead of local constants
  - depth: number of attempts at discharging generated sub-goals
  -/
meta def solve_by_elim (opt : by_elim_opt := { }) : tactic unit :=
solve_by_elim_aux opt.discharger opt.restr_hyp_set opt.max_rep

/--
  find all assumptions of the shape `¬ (p ∧ q)` or `¬ (p ∨ q)` and
  replace them using de Morgan's law.
-/
meta def de_morgan_hyps : tactic unit :=
do hs ← local_context,
   hs.for_each $ λ h,
     replace (some h.local_pp_name) none ``(not_and_distrib'.mp %%h) <|>
     replace (some h.local_pp_name) none ``(not_and_distrib.mp %%h) <|>
     replace (some h.local_pp_name) none ``(not_or_distrib.mp %%h) <|>
     replace (some h.local_pp_name) none ``(of_not_not %%h) <|>
     replace (some h.local_pp_name) none ``(not_imp.mp %%h) <|>
     replace (some h.local_pp_name) none ``(not_iff.mp %%h) <|>
     skip

/--
  `tautology` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
  and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
  using `reflexivity` or `solve_by_elim`
-/
meta def tautology : tactic unit :=
repeat (do
  gs ← get_goals,
  () <$ tactic.intros;
  de_morgan_hyps,
  casesm (some ()) [``(_ ∧ _),``(_ ∨ _),``(_ ↔ _),``(Exists _),``(false)];
  constructor_matching (some ()) [``(_ ∧ _),``(_ ↔ _),``(true)],
  try (refine ``( or_iff_not_imp_left.mpr _)),
  try (refine ``( or_iff_not_imp_right.mpr _)),
  gs' ← get_goals,
  guard (gs ≠ gs') );
repeat
(reflexivity <|> solve_by_elim <|>
 constructor_matching none [``(_ ∧ _),``(_ ↔ _),``(Exists _)] ) ;
done

/-- Shorter name for the tactic `tautology`. -/
meta def tauto := tautology

/--
  `ext1 id` selects and apply one extensionality lemma (with attribute
  `extensionality`), using `id`, if provided, to name a local constant
  introduced by the lemma. If `id` is omitted, the local constant is
  named automatically, as per `intro`.
 -/
meta def ext1 (x : parse ident_ ?) : tactic unit :=
do ls ← attribute.get_instances `extensionality,
   ls.any_of (λ l, applyc l) <|> fail "no applicable extensionality rule found",
   try ( interactive.intro x )

meta def ext_arg :=
prod.mk <$> (some <$> small_nat)
        <*> (tk "with" *> ident_* <|> pure [])
<|> prod.mk none <$> (ident_*)

/--
  - `ext` applies as many extensionality lemmas as possible;
  - `ext ids`, with `ids` a list of identifiers, finds extentionality and applies them
    until it runs out of identifiers in `ids` to name the local constants.

  When trying to prove:

  ```
  α β : Type,
  f g : α → set β
  ⊢ f = g
  ```

  applying `ext x y` yields:

  ```
  α β : Type,
  f g : α → set β,
  x : α,
  y : β
  ⊢ y ∈ f x ↔ y ∈ f x
  ```

  by applying functional extensionality and set extensionality.

  A maximum depth can be provided with `ext 3 with x y z`.
  -/
meta def ext : parse ext_arg → tactic unit
 | (some n, []) := ext1 none >> iterate_at_most (pred n) (ext1 none)
 | (none,   []) := ext1 none >> repeat (ext1 none)
 | (n, xs) := tactic.ext xs n

private meta def generalize_arg_p_aux : pexpr → parser (pexpr × name)
| (app (app (macro _ [const `eq _ ]) h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "parse error"


private meta def generalize_arg_p : parser (pexpr × name) :=
with_desc "expr = id" $ parser.pexpr 0 >>= generalize_arg_p_aux

lemma {u} generalize_a_aux {α : Sort u}
  (h : ∀ x : Sort u, (α → x) → x) : α := h α id

/--
  Like `generalize` but also considers assumptions
  specified by the user. The user can also specify to
  omit the goal.
  -/
meta def generalize_hyp  (h : parse ident?) (_ : parse $ tk ":")
  (p : parse generalize_arg_p)
  (l : parse location) :
  tactic unit :=
do h' ← get_unused_name `h,
   x' ← get_unused_name `x,
   g ← if ¬ l.include_goal then
       do refine ``(generalize_a_aux _),
          some <$> (prod.mk <$> tactic.intro x' <*> tactic.intro h')
   else pure none,
   n ← l.get_locals >>= tactic.revert_lst,
   generalize h () p,
   intron n,
   match g with
     | some (x',h') :=
        do tactic.apply h',
           tactic.clear h',
           tactic.clear x'
     | none := return ()
   end

/--
  Similar to `refine` but generates equality proof obligations
  for every discrepancy between the goal and the type of the rule.
  -/
meta def convert (sym : parse (with_desc "←" (tk "<-")?)) (r : parse texpr) (n : parse (tk "using" *> small_nat)?) : tactic unit :=
do v ← mk_mvar,
   if sym.is_some
     then refine ``(eq.mp %%v %%r)
     else refine ``(eq.mpr %%v %%r),
   gs ← get_goals,
   set_goals [v],
   congr' n,
   gs' ← get_goals,
   set_goals $ gs' ++ gs

meta def clean_ids : list name :=
[``id, ``id_rhs, ``id_delta]

/-- Remove identity functions from a term. These are normally
  automatically generated with terms like `show t, from p` or
  `(p : t)` which translate to some variant on `@id t p` in
  order to retain the type. -/
meta def clean (q : parse texpr) : tactic unit :=
do tgt : expr ← target,
   e ← i_to_expr_strict ``(%%q : %%tgt),
   tactic.exact $ e.replace (λ e n,
     match e with
     | (app (app (const n _) _) e') :=
       if n ∈ clean_ids then some e' else none
     | (app (lam _ _ _ (var 0)) e') := some e'
     | _ := none
     end)

meta def source_fields (missing : list (name × name)) (e : pexpr) : tactic (list (name × pexpr)) :=
do e ← to_expr e,
   t ← infer_type e,
   let struct_n : name := t.get_app_fn.const_name,
   exp_fields ← (∩ missing) <$> expanded_field_list struct_n,
   exp_fields.mmap $ λ ⟨p,n⟩,
     (prod.mk n ∘ to_pexpr) <$> mk_mapp (n.update_prefix p) [none,some e]

meta def collect_struct' : pexpr → state_t (list $ expr×structure_instance_info) tactic pexpr | e :=
do some str ← pure (e.get_structure_instance_info)
       | e.traverse collect_struct',
   v ← monad_lift mk_mvar,
   modify (list.cons (v,str)),
   pure $ to_pexpr v

meta def collect_struct (e : pexpr) : tactic $ pexpr × list (expr×structure_instance_info) :=
prod.map id list.reverse <$> (collect_struct' e).run []

meta def refine_one (str : structure_instance_info) :
  tactic $ list (expr×structure_instance_info) :=
do    tgt ← target,
      let struct_n : name := tgt.get_app_fn.const_name,
      exp_fields ← expanded_field_list struct_n,
      let missing_f := exp_fields.filter (λ f, (f.2 : name) ∉ str.field_names),
      (src_field_names,src_field_vals) ← (@list.unzip name _ ∘ list.join) <$> str.sources.mmap (source_fields missing_f),
      let provided  := exp_fields.filter (λ f, (f.2 : name) ∈ str.field_names),
      let missing_f' := missing_f.filter (λ x, x.2 ∉ src_field_names),
      vs ← mk_mvar_list missing_f'.length,
      (field_values,new_goals) ← list.unzip <$> (str.field_values.mmap collect_struct : tactic _),
      e' ← to_expr $ pexpr.mk_structure_instance
          { struct := some struct_n
          , field_names  := str.field_names  ++ missing_f'.map prod.snd ++ src_field_names
          , field_values := field_values ++ vs.map to_pexpr         ++ src_field_vals },
      tactic.exact e',
      gs ← with_enable_tags (
        mmap₂ (λ (n : name × name) v, do
           set_goals [v],
           try (interactive.unfold (provided.map $ λ ⟨s,f⟩, f.update_prefix s) (loc.ns [none])),
           apply_auto_param
             <|> apply_opt_param
             <|> (set_main_tag [`_field,n.2,n.1]),
           get_goals)
        missing_f' vs),
      set_goals gs.join,
      return new_goals.join

meta def refine_recursively : expr × structure_instance_info → tactic (list expr) | (e,str) :=
do set_goals [e],
   rs ← refine_one str,
   gs ← get_goals,
   gs' ← rs.mmap refine_recursively,
   return $ gs'.join ++ gs


/-- `refine_struct { .. }` acts like `refine` but works only with structure instance
    literals. It creates a goal for each missing field and tags it with the name of the
    field so that `have_field` can be used to generically refer to the field currently
    being refined.

    As an example, we can use `refine_struct` to automate the construction semigroup
    instances:
    ```
    refine_struct ( { .. } : semigroup α ),
    -- case semigroup, mul
    -- α : Type u,
    -- ⊢ α → α → α

    -- case semigroup, mul_assoc
    -- α : Type u,
    -- ⊢ ∀ (a b c : α), a * b * c = a * (b * c)
    ```
-/
meta def refine_struct : parse texpr → tactic unit | e :=
do (x,xs) ← collect_struct e,
   refine x,
   gs ← get_goals,
   xs' ← xs.mmap refine_recursively,
   set_goals (xs'.join ++ gs)

meta def guard_tags (tags : parse ident*) : tactic unit :=
do (t : list name) ← get_main_tag,
   guard (t = tags)

meta def get_current_field : tactic name :=
do [_,field,str] ← get_main_tag,
   expr.const_name <$> resolve_name (field.update_prefix str)

/-- `have_field`, used after `refine_struct _` poses `field` as a local constant
    with the type of the field of the current goal:

    ```
    refine_struct ({ .. } : semigroup α),
    { have_field, ... },
    { have_field, ... },
    ```
    behaves like
    ```
    refine_struct ({ .. } : semigroup α),
    { have field := @semigroup.mul, ... },
    { have field := @semigroup.mul_assoc, ... },
    ```
-/
meta def have_field : tactic unit :=
propagate_tags $
get_current_field
>>= mk_const
>>= note `field none
>>  return ()

/-- `apply_field` functions as `have_field, apply field, clear field` -/
meta def apply_field : tactic unit :=
propagate_tags $
get_current_field >>= applyc

/-- `elim_cast e with x` matches on `cast _ e` in the goal and replaces it with
    `x`. It also adds `Hx : e == x` as an assumption.

    `elim_cast! e with x` acts similarly but reverts `Hx`.
-/
meta def elim_cast (rev : parse (tk "!")?) (e : parse texpr) (n : parse (tk "with" *> ident)) : tactic unit :=
do h ← get_unused_name ("H" ++ n.to_string : string),
   interactive.generalize h () (``(cast _ %%e), n),
   asm ← get_local h,
   to_expr ``(heq_of_cast_eq _ %%asm) >>= note h none,
   tactic.clear asm,
   when rev.is_some (interactive.revert [n])

end interactive
end tactic
