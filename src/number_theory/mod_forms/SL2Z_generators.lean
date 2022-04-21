import .mat_m
import group_theory.group_action.basic
import linear_algebra.matrix
import linear_algebra.determinant
import data.matrix.notation
import .mod_group

/-  This is an attemmatrix_makrto update the kbb birthday repo, so most is not orginal to me-/

namespace int

theorem mul_eq_one {m n : ℤ} :
  m * n = 1 ↔ m = 1 ∧ n = 1 ∨ m = -1 ∧ n = -1 :=
⟨λ H, or.cases_on (int.units_eq_one_or ⟨m, n, H, by rwa [mul_comm] at H⟩)
  (λ H1, have H2 : m = 1, from units.ext_iff.1 H1,
    or.inl ⟨H2, by rwa [H2, one_mul] at H⟩)
  (λ H1, have H2 : m = -1, from units.ext_iff.1 H1,
    or.inr ⟨H2, by rwa [H2, neg_one_mul, neg_eq_iff_neg_eq, eq_comm] at H⟩),
by simp [or_imp_distrib] {contextual := tt}⟩

lemma nat_abs_lt_nat_abs (i k : ℤ) (hi : 0 ≤ i) (h : i < abs k) : nat_abs i < nat_abs k :=
coe_nat_lt.1 $ by rwa [nat_abs_of_nonneg hi, ← int.abs_eq_nat_abs]

end int

variables (a b c d : ℕ )

namespace SL2Z_M

local notation `SL2Z` := matrix.special_linear_group (fin 2) ℤ

/--These are the generators of `SL(2,ℤ)`-/
def S : SL2Z := ⟨ ![![0, -1], ![1, 0]], by { refl}⟩
def T: SL2Z := ⟨ ![![1, 1], ![0, 1]], by { refl}⟩

@[simp] lemma S_a : S 0 0 = 0 := rfl
@[simp] lemma S_b : S 0 1 = -1 := rfl
@[simp] lemma S_c : S 1 0 = 1 := rfl
@[simp] lemma S_d : S 1 1 = 0 := rfl
@[simp] lemma T_a : T 0 0 = 1 := rfl
@[simp] lemma T_b : T 0 1 = 1 := rfl
@[simp] lemma T_c : T 1 0 = 0 := rfl
@[simp] lemma T_d : T 1 1 = 1 := rfl

variable (m : ℤ)

local notation `Mat` := integral_matrices_with_determinant (fin 2)

lemma S_mul_a (A : Mat m) : (S • A) 0 0 = -A 1 0 :=
begin
 simp
end

 lemma S_mul_b (A : Mat m) : (S • A) 0 1 = -A 1 1 :=
begin
 simp
end

lemma S_mul_c (A : Mat m) : (S • A) 1 0 = A 0 0 :=
begin
simp
end

lemma S_mul_d (A : Mat m) : (S • A) 1 1 =  A 0 1 :=
begin
simp,
end


@[simp] lemma SL2Z_one_a : (1 : SL2Z) 0 0 = 1 := rfl
@[simp] lemma SL2Z_one_b : (1 : SL2Z) 0 1 = 0 := rfl
@[simp] lemma SL2Z_one_c : (1 : SL2Z) 1 0 = 0 := rfl
@[simp] lemma SL2Z_one_d : (1 : SL2Z) 1 1 = 1 := rfl

@[simp] lemma SL2Z_mul_a (A B : SL2Z) : (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 :=
begin
apply (modular_group.mat_mul_expl A B).1,
end


@[simp] lemma SL2Z_mul_b (A B : SL2Z) : (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 :=
begin
apply (modular_group.mat_mul_expl A B).2.1,
end

@[simp] lemma SL2Z_mul_c (A B : SL2Z) : (A * B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 :=
begin
apply (modular_group.mat_mul_expl A B).2.2.1,
end

@[simp] lemma SL2Z_mul_d (A B : SL2Z) : (A * B) 1 1  = A 1 0 * B 0 1 + A 1 1  * B 1 1 :=
begin
apply (modular_group.mat_mul_expl A B).2.2.2,
end

lemma T_pow_aux' (n : ℕ ) : (T^n) 0 0 = 1 ∧ (T^n) 0 1 = n ∧ (T^n) 1 0 = 0 ∧ (T^n) 1 1 = 1 :=
begin
induction n with d hd,
  simp only [SL2Z_one_b, SL2Z_one_d, int.coe_nat_zero,
    SL2Z_one_a, eq_self_iff_true, and_self, SL2Z_one_c, pow_zero],
  simp only [pow_succ, T_d, one_mul, zero_mul, T_a, T_c,
    int.coe_nat_succ, T_b, zero_add, SL2Z_mul_d, SL2Z_mul_c, SL2Z_mul_a, SL2Z_mul_b],
  rw [hd.1],
  simp only [add_right_eq_self],
  rw [hd.2.1],
  simp only [add_right_inj],
  rw [hd.2.2.1, hd.2.2.2],
  simp only [eq_self_iff_true, and_self],
end

lemma T_pow_aux (n : ℤ  ) : (T^n) 0 0 = 1 ∧ (T^n) 0 1 = n ∧ (T^n) 1 0 = 0 ∧ (T^n) 1 1 = 1 :=
begin
  induction n with d hd,
  simp only [int.of_nat_eq_coe, zpow_coe_nat],
  apply T_pow_aux',
  simp only [modular_group.SL2Z_inv_d, modular_group.SL2Z_inv_c, modular_group.SL2Z_inv_b,
  zpow_neg_succ_of_nat, modular_group.SL2Z_inv_a, neg_eq_zero],
  simp only [pow_succ, T_d, one_mul, zero_mul, T_a,
    T_c, T_b, neg_add_rev, zero_add, SL2Z_mul_d, SL2Z_mul_c, SL2Z_mul_a,
  SL2Z_mul_b],
  rw [(T_pow_aux' hd).2.2.1, (T_pow_aux' hd).2.2.2, (T_pow_aux' hd).1,  (T_pow_aux' hd).2.1],
  simp only [true_and, add_zero, and_true, eq_self_iff_true],
  rw int.neg_succ_of_nat_eq', ring,
end

@[simp] lemma T_pow_a (n : ℤ) : (T^n) 0 0 = 1 := (T_pow_aux n).1
@[simp] lemma T_pow_b (n : ℤ) : (T^n) 0 1 = n := (T_pow_aux n).2.1
@[simp] lemma T_pow_c (n : ℤ) : (T^n) 1 0 = 0 := (T_pow_aux n).2.2.1
@[simp] lemma T_pow_d (n : ℤ) : (T^n) 1 1 = 1 := (T_pow_aux n).2.2.2

instance : has_neg SL2Z :=
begin
have:= matrix.special_linear_group.has_neg, apply this, simp, fsplit, exact dec_trivial,
end


@[simp] lemma S_mul_S : S * S = (-1: SL2Z) :=
begin
  ext i j,
  fin_cases i; fin_cases j,
  simp  [integral_matrices_with_determinant.mat_m_neg_elt], refl,
  simp  [integral_matrices_with_determinant.mat_m_neg_elt], refl,
  simp  [integral_matrices_with_determinant.mat_m_neg_elt], refl,
  simp  [integral_matrices_with_determinant.mat_m_neg_elt], refl,
end

lemma S_inv' : -S * S= 1:=
begin
  have S_min: -S = -1 * S, by {ext1, cases j, cases i,simp at *,},
  rw S_min,
  rw  mul_assoc,
  rw S_mul_S,
  ext,
  cases j,
  cases i,
  simp,
end

@[simp] lemma S_inv: -S = S⁻¹ :=
begin
  rw  eq_inv_iff_mul_eq_one,
  rw S_inv',
end

lemma S_n_T: S*S*S*T*S*T*S=T⁻¹ :=
begin
  simp,
  ext i j,
  fin_cases i; fin_cases j,
  refl,
  refl,
  refl,
  refl,
end


lemma fixlem (m : ℤ) (A : Mat m) :
  A 0 0 + -(A 0 0/ A 1 0)*( A 1 0)= A 0 0 % A 1 0:=
begin
  simp,
  rw  ← sub_eq_add_neg,
  rw mul_comm,
  rw  ← int.mod_def,
end

/--The group generated by `S,T`  (and their inveses, which is convinient to have at the start-/
def gengrp :subgroup SL2Z := subgroup.closure ({ S, T,S⁻¹,T⁻¹} : set SL2Z)

lemma gengroup_det (A : gengrp) : matrix.det A =1 :=
begin
  have : matrix.det (A : SL2Z) = 1, by{simp,},
  apply this,
end

lemma Tpows (n: ℤ) : T^n ∈ gengrp:=
begin
have  h1: T ∈ gengrp, by {rw gengrp, apply subgroup.subset_closure, simp,}  ,
 apply subgroup.zpow_mem _ h1,
end

lemma TSS (n: ℤ): T^n*S*S ∈ gengrp :=
begin
have h1:= Tpows n,
have h2: S ∈ gengrp , by {rw gengrp, apply subgroup.subset_closure, simp,},
have:= subgroup.mul_mem _ h1 h2,
apply subgroup.mul_mem _ this h2,
end

lemma UST (n: ℤ) (U ∈ gengrp ): U * S * (T^n)⁻¹ ∈ gengrp:=
begin
 have h1:= Tpows n,
 have hh1: (T^n)⁻¹ ∈ gengrp , by {rw subgroup.inv_mem_iff, exact h1 } ,
 have h2: S ∈ gengrp , by {rw gengrp, apply subgroup.subset_closure, simp,},
 have h3:= subgroup.mul_mem _ h2 hh1,
have:= subgroup.mul_mem _ H h3,
rw ← mul_assoc at this,
exact this,
end


/--Representative elements for the orbits of `Mat m` under the action of `gengrp` (which, is later
shown to be `SL(2,ℤ)`)
 -/
def reps (m : ℤ) : set (Mat m) :=
{A : Mat m | A 1 0 = 0 ∧ 0 < A 0 0 ∧ 0 ≤ A 0 1 ∧ int.nat_abs (A 0 1) < int.nat_abs (A 1 1) }

theorem reduce_aux (m : ℤ) (A : Mat m) (H : int.nat_abs (A 1 0) ≠ 0) :
  int.nat_abs (( S • ( (T^(-((A 0 0) / (A 1 0)))) • A)) 1 0) < int.nat_abs (A 1 0) :=
begin
  have H2 : A 1 0 ≠ 0, from mt (λ H2, show int.nat_abs (A 1 0) = 0, by rw H2; refl) H,
  simp [one_mul, zero_mul, add_zero],
  have:= fixlem m A, simp at this, rw this,
  rw  [← int.coe_nat_lt],
  have hs:=  int.nat_abs_of_nonneg ( int.mod_nonneg _ H2),
  simp at hs,
  rw hs,
  rw [← int.abs_eq_nat_abs],
  exact int.mod_lt _ H2,
end

/--Reduction step to matrices in `Mat m` which moves the matrices towars `reps`.-/
def reduce_step (A : Mat m) : Mat m :=  S • ( (T^(-((A 0 0)/(A 1 0)))) • A)

def c_entry (m :ℤ) (A: Mat m):= A 1 0

@[elab_as_eliminator]
def reduce_rec (m : ℤ) {C : Mat m → Sort*}
  (h₀ : ∀A:Mat m, (A 1 0) = 0 → C A)
  (h₁ : ∀A:Mat m, int.nat_abs (A 1 0) ≠ 0 → C (reduce_step m A) → C A) :
  ∀A, C A | A :=
if hc : int.nat_abs (A 1 0) = 0 then h₀ A (int.eq_zero_of_nat_abs_eq_zero hc)
else
  have int.nat_abs ((reduce_step m A) 1 0) < int.nat_abs (A 1 0), from reduce_aux m A hc,
  h₁ A hc (reduce_rec (reduce_step m A))
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ c_entry m ) ⟩]}

/-- correct if m ≠ 0 -/
def reduce (m : ℤ) : Mat m → Mat m | A :=
if hc : int.nat_abs (A 1 0) = 0
then if ha : 0 < (A 0 0)
  then (T^(-(A 0 1/A 1 1)))•  A
  else (T^(-(-A 0 1/ -A 1 1))) •  ( S • ( S • A))
else
  have int.nat_abs ((reduce_step m A) 1 0) < int.nat_abs (A 1 0), from reduce_aux m A hc,
  reduce (reduce_step  m A)
using_well_founded
  { rel_tac := λ _ _, `[exact ⟨_, measure_wf (int.nat_abs ∘ c_entry m )⟩]}

theorem reduce_eq1 (m : ℤ) {A : Mat m} (hc : int.nat_abs (A 1 0) = 0) (ha : 0 < (A 0 0)) :
  reduce m A =  (T^(-(A 0 1/A 1 1))) •  A :=
by rw [reduce.equations._eqn_1 _ _, if_pos hc, if_pos ha]; refl

theorem reduce_eq2 (m : ℤ) {A : Mat m} (hc : int.nat_abs (A 1 0) = 0) (ha : ¬ 0 < (A 0 0)) :
  reduce m A =  (T^(-(-A 0 1/ -A 1 1)))•  ( S • ( S • A)) :=
by rw [reduce.equations._eqn_1 _ _, if_pos hc, if_neg ha]; refl

theorem reduce_eq3 (m : ℤ) {A : Mat m} (h : int.nat_abs (A 1 0) ≠ 0) :
  reduce m A = reduce m (reduce_step m A) :=
by rw [reduce.equations._eqn_1 _ _, if_neg h]

theorem reduce_spec (m : ℤ) : ∀A : Mat m, ∃ (R: gengrp), R • A = reduce m A :=
begin
  refine reduce_rec m _ _,
  { intros A hc,
    by_cases ha : 0 < (A 0 0),
    {have:= reduce_eq1 m, simp at *, have h1:=this hc ha, simp only at h1,
    simp  [*, int.nat_abs_eq_zero, h1 , exists_apply_eq_apply],
     let gg:= (T ^ (A 0 1 / A 1 1))⁻¹,
     refine ⟨⟨gg, _⟩, _⟩,
     simp only [subgroup.inv_mem_iff],
     apply Tpows,
     simp_rw gg, refl, },
    {simp only [*, int.div_neg, int.nat_abs_eq_zero, not_false_iff, neg_neg, reduce_eq2],
    erw [← mul_smul], rw [← mul_smul],
    let g:= (T ^ (-A 0 1 / A 1 1))*S*S,
    refine ⟨⟨g,_⟩, _ ⟩,
    apply TSS,
    simp_rw g,refl,} },
  { rintros A hc ⟨U, eq⟩, rw reduce_eq3 m hc, rw ← eq, rw reduce_step, simp only [zpow_neg],
    simp only [int.nat_abs_eq_zero, ne.def] at *,
    refine ⟨⟨ (U : SL2Z) * S *(T ^ (A 0 0 / A 1 0))⁻¹,_⟩,_⟩,
    have Umem:= set_like.coe_mem U,
    apply UST _ U Umem,
    have j: ∀ (x y z : SL2Z) (M: Mat m), x • y • z • M = (x * y*z)• M , by {simp_rw ← mul_smul, intros x y z A,
    rw mul_assoc,},
    have:= j (U : SL2Z)  (SL2Z_M.S) (T ^ (A 0 0 / A 1 0))⁻¹ A,
   apply this.symm,
   }
end



theorem reduce_mem_reps (m : ℤ) (hm : m ≠ 0) : ∀(A : Mat m), reduce m A ∈ reps m :=
begin
  refine reduce_rec m (assume A (c_eq : A 1 0 = 0), _) (assume A hc ih, _),
  { have hd : A 1 1 ≠ 0, { intro d_eq,
      apply hm,
      have:= modular_group.det_m m A,
      rw ← this,
      rw d_eq,
      rw c_eq,
      simp only [zero_mul, sub_zero, mul_zero],},
    have eq : ∀b d, b + -(b / d * d) = b % d,
      by { intros, rw [← sub_eq_add_neg, mul_comm, ← int.mod_def] },
    have h : ∀(a b : ℤ), 0 < a → 0 < a ∧ 0 ≤ b % (A 1 1) ∧
          int.nat_abs (b % (A 1 1)) < int.nat_abs (A 1 1) :=
            assume a b ha,
            ⟨ha, int.mod_nonneg _ hd,
              int.nat_abs_lt_nat_abs _ _ (int.mod_nonneg _ hd) (int.mod_lt _ hd)⟩,
    by_cases ha : 0 < A 0 0,
    {simpa only [reduce_eq1, reps, c_eq, ha, eq, neg_mul, true_and,
     T_pow_c, modular_group.SL2Z_inv_d, T_pow_a, add_zero, one_mul,modular_group.SLnZ_M_c,
     modular_group.SLnZ_M_b, zero_mul, int.nat_abs_eq_zero, eq_self_iff_true,
     modular_group.SLnZ_M_a, zero_add, modular_group.SLnZ_M_d,
  set.mem_set_of_eq, mul_zero, T_pow_d, neg_zero, T_pow_b] using h _ _ ha },
    { have a_ne : A 0 0 ≠ 0,
      { intro a_eq,
      apply hm,
      rw [ ← modular_group.det_m m, a_eq, c_eq],
      simp only [zero_mul, sub_zero], simp, },
      have a_pos : -A 0 0 > 0 := neg_pos_of_neg (lt_of_le_of_ne (le_of_not_gt ha) a_ne),
       simp only [reduce_eq2, reps, c_eq, ha, eq, true_and, T_pow_c, T_pow_a, add_zero,
        int.div_neg, one_mul,  modular_group.SLnZ_M_c,  modular_group.SLnZ_M_b,
        S_mul_c, right.neg_pos_iff, zero_mul, int.nat_abs_neg, int.nat_abs_eq_zero,
        eq_self_iff_true, S_mul_a, mul_neg,  modular_group.SLnZ_M_a, zero_add, not_false_iff,
        modular_group.SLnZ_M_d, neg_neg, int.nat_abs, set.mem_set_of_eq,
        reduce_eq2, mul_zero, S_mul_d, T_pow_d, neg_zero, S_mul_b, T_pow_b],
      rw S_a,
      simp,
      simp only [ integral_matrices_with_determinant.mat_m_vals,
        right.neg_pos_iff, subtype.val_eq_coe] at a_pos,
    have a_poss: 0 < (-A.1) 0 0, by {rw ← gt_iff_lt, apply a_pos,},
    have := h (-A.1 0 0) (-A.1 0 1) a_poss,
    simp at this,
    exact this,
   } },
  { rwa [reduce_eq3 m hc] }
end

@[elab_as_eliminator]
protected theorem induction_on {C : Mat m → Prop} (A : Mat m) (mne0 : m ≠ 0)
  (h0 : ∀{A:Mat m}, A 1 0 = 0 → A 0 0 * A 1 1 = m → 0 < A 0 0 → 0 ≤ A 0 1 → int.nat_abs (A 0 1) < int.nat_abs (A 1 1) → C A)
  (hS : ∀ B, C B → C (S • B)) (hT : ∀ B, C B → C ( T • B)) :
  C A :=
have S_eq : ∀ (B : Mat m), (S • ( S • (S • ( S • B)))) = B,
  by  intro b;
    {rw ← mul_smul,
     rw S_mul_S,
     rw ← mul_smul,
     rw ← mul_smul,
      rw mul_assoc,
      rw S_mul_S,
      have min_1 : (-1 : SL2Z) * (-1 : SL2Z) =1, by {ext, cases i, cases j, simp,},
      rw min_1, simp, },
have hS' : ∀{B}, C (S • B) → C B, from
  λ B ih, have h : _ := (hS _ $ hS _ $ hS _ ih), by rwa S_eq B at h,
have eq : ∀ (B: Mat m),
  (S • S • S • T • S • T • S • B) = T⁻¹ • B,
  by intro b; {repeat {rw [← mul_smul]}, rw S_n_T, }; congr,
have hT_inv : ∀ B, C B → C (T⁻¹ • B), from
  λ B ih, have h : _ := (hS _ $ hS _ $ hS _ $ hT _ $ hS _ $ hT _ $ hS _ ih), by rwa eq at h,
have hT' : ∀B, C (T • B) → C B,
{ assume B ih,
  have h := hT_inv (T • B) ih,
  rwa [←mul_smul, mul_left_inv, one_smul] at h },
have hT_inv' : ∀ B, C  (T⁻¹ • B) → C B,
{ assume B ih,
  have H := hT ( T⁻¹ • B) ih,
  rwa [←mul_smul, mul_right_inv, one_smul] at H },
have hTpow' : ∀{B} {n:ℤ}, C ( (T^n) • B) → C B,
{ refine assume B n, int.induction_on n (λh, _) (λi ih1 ih2, ih1 $ hT' _ _) (λi ih1 ih2, ih1 $ hT_inv' _ _),
  { rwa [zpow_zero, one_smul] at h },
  { rwa [add_comm, zpow_add, zpow_one, mul_smul] at ih2 },
  { rwa [sub_eq_neg_add, zpow_add, zpow_neg_one, mul_smul] at ih2 } },
have h_reduce : C (reduce m A),
{ rcases reduce_mem_reps m mne0 A with ⟨H1, H2, H3, H4⟩,
  refine h0 H1 _ H2 H3 H4,
  have:= modular_group.det_m m (reduce m A),
  rw H1 at this, simp at this,
  exact this,},
suffices ∀A : Mat m, C (reduce m A) → C A, from this _ h_reduce,
begin
  refine reduce_rec m _ _,
  { assume A c_eq ih,
    by_cases ha : 0 < A 0 0,
    { simp [reduce_eq1, c_eq, ha, -zpow_neg] at ih, exact hTpow' ih },
    { simp [reduce_eq2, c_eq, ha] at ih, exact (hS' $ hS' $ hTpow' ih) } },
  { assume A hc ih hA,
    rw [reduce_eq3 m hc] at hA,
    exact (hTpow' $ hS' $ ih hA) }
end

/-This is a silly lemma-/
lemma num_gt_sum (h f b  : ℤ)  (h2 : 0  ≤ f)
 (h4 : f.nat_abs < h.nat_abs  ) (h5 : 0 ≤ (f+b*h) )
 (h6 : (f+b*h).nat_abs < h.nat_abs ) :  b = 0:=
begin
  rw ←  int.coe_nat_lt at *,
  rw  int.nat_abs_of_nonneg h2 at h4,
  rw  int.nat_abs_of_nonneg h5 at h6,
  rw ← int.abs_eq_nat_abs at *,
  have hg0: abs h > 0, {apply lt_of_le_of_lt h2 h4,   },
  have hgn0: h ≠ 0, {intros ha, simp at *, solve_by_elim, },
  have hn:  f % abs h = f, { apply   int.mod_eq_of_lt h2 h4, },
  have hn2:  (f +b*h) % abs h = f+b*h, { apply   int.mod_eq_of_lt h5 h6, },
  simp only [int.mod_abs, int.add_mul_mod_self] at hn2,
  simp only [int.mod_abs] at hn,
  have ht: f = f+b*h , {rw ←  hn2, rw hn,    },
  simp only [self_eq_add_right, mul_eq_zero] at ht,
  rw lt_iff_le_not_le at h4,
  cases h4, cases ht, work_on_goal 1 { assumption },
  dsimp at *,
  simp at *,
  solve_by_elim,
end

lemma one_time (a b c : ℤ) (h1 : 0 < a ) (h2 : 0 < c ) (h3: a = b*c) : 0 < b :=
begin
have h4: b*c >0 ,{ rw h3 at h1, exact h1},
replace h2:= le_of_lt h2,
apply pos_of_mul_pos_right  h4 h2,
end

lemma one_time' (a b : ℤ) (h1 : 0 <  a ) (h2 : (a = 1 ∧ b=1) ∨ (a=-1 ∧ b=-1)) : (a=1 ∧ b=1) :=
begin
  by_contra h,
  cases h2,
  work_on_goal 1 { cases h2, simp at *, solve_by_elim },
  cases h2,
  simp at *,
  rw h2_left at h1, have h4 : 0 < (-1: ℤ) ↔ false, simp only [neg_nonpos, not_lt, iff_false],
  work_on_goal 1 { exact dec_trivial },
  cases h4,
  simp at *,
  solve_by_elim,
end

lemma m_a_b' (m : ℤ) (hm : m ≠ 0) (A : gengrp) (M N : integral_matrices_with_determinant (fin 2) m):
 (A • M) = N ↔  N 0 0= A 0 0 * M 0 0 + A 0 1 * M 1 0 ∧
 N 0 1= A 0 0 * M 0 1 + A 0 1 * M 1 1 ∧
 N 1 0= A 1 0 * M 0 0 + A 1 1 * M 1 0 ∧
 N 1 1= A 1 0 * M 0 1 + A 1 1 * M 1 1 :=
begin
  apply modular_group.m_a_b,
  exact hm,
end

theorem reps_unique' (m : ℤ) (hm : m ≠ 0) :
  ∀(M : gengrp) (A B : Mat m), A ∈ reps m → B ∈ reps m →  M • A = B → A = B :=
begin
  rintros  M A B
    ⟨g_eq, e_pos, f_nonneg, f_bound⟩ ⟨k_eq, H6, f'_nonneg, f'_bound⟩ B_eq, rw ← B_eq,
    rw m_a_b' at B_eq,
  have ht: M 1 0 = 0,
    {rw [k_eq, g_eq] at B_eq,
    simp only [add_zero, zero_eq_mul, mul_zero] at B_eq,
    cases B_eq.2.2.1,
    exact h,
    rw h at e_pos,
    exact (irrefl _ e_pos).elim, },
  have d1: (M 0 0)*(M 1 1)=1,
    by {have:= matrix.det_fin_two M, simp at *, rw ht at this, simp at this,
      have hm:= gengroup_det M, rw hm at this, apply this.symm, },
  have mg0: (M  0 0) > 0, by
    {rw g_eq at B_eq, simp only [add_zero, mul_zero] at B_eq,
    exact one_time (B 0 0) (M 0 0) (A 0 0) H6 e_pos B_eq.1, },
  have htt: M 0 0 =1 ∧ M 1 1 =1, by
    { rw int.mul_eq_one at d1, apply one_time' (M 0 0) (M 1 1) mg0 d1,},
  have httv: M 1 1 =1, { simp only [htt], },
  have htv: ((A 0 1)+ (M 0 1)*(A 1 1)) ≥ 0, by
    {rw B_eq.2.1 at f'_nonneg,
    rw htt.1 at f'_nonneg,
    simp only [one_mul] at f'_nonneg,
    exact f'_nonneg},
  have httt: M 0 1 =0, by
    {rw B_eq.2.2.2 at f'_bound,
    rw B_eq.2.1 at f'_bound,
    rw ht at f'_bound,
    rw htt.1 at f'_bound,
    rw httv at f'_bound,
    simp only [one_mul, zero_mul,
    zero_add] at f'_bound,
    apply num_gt_sum (A 1 1) (A 0 1) (M 0 1)  f_nonneg  f_bound htv,
    exact f'_bound, },
  have M1: ↑M = (1: SL2Z), by
      {ext i j,
      fin_cases i;
      fin_cases j,
      exact htt.1,
      exact  httt,
      exact ht,
      exact httv},
    norm_cast at M1,
    rw M1,
    simp only [one_smul],
    exact hm,
end


variable (n:ℕ+)

/--This takes  four integers and creates a matrix in the obvious way-/
def  matrix_makr(a b c d : ℤ ): matrix  (fin 2) (fin 2 ) ℤ:= ![![a, b], ![c, d]]

lemma dm  (a b c d : ℤ ) : (matrix_makr a b c d).det = a*d-b*c:=
begin
  rw matrix_makr,
  apply matrix.det_fin_two (matrix_makr a b c d),
end


@[simp] lemma em  (a b c d : ℤ ) :
  (matrix_makr a b c d) 0 0 = a ∧
  (matrix_makr a b c d) 0 1 = b ∧
  (matrix_makr a b c d) 1 0 = c ∧
  (matrix_makr a b c d) 1 1 = d :=
begin
rw matrix_makr,
simp only [matrix.head_cons, eq_self_iff_true, and_self, matrix.cons_val_one, matrix.cons_val_zero],
end

lemma en_pos (m : ℕ+) (A: matrix (fin 2) (fin 2) ℤ)
(h1: A.det= ↑ m) (h2: 0 < A 0 0) (h3: A 1 0 =0) : 0 ≤ A 1 1:=
begin
  rw matrix.det_fin_two at h1,
  rw h3 at h1,
  simp only [sub_zero, mul_zero, coe_coe] at h1,
  by_contradiction h,
  simp only [not_le] at h,
  have h5: A 1 1 * A 0 0 < 0, {apply mul_neg_of_neg_of_pos h h2},
    rw mul_comm at h1,
    rw h1 at h5,
    cases m,
    dsimp at *,
    rw ← int.coe_nat_lt at m_property,
    rw ←  not_le at h5,
    dsimp at *,
    simp at *,
    assumption,
end


instance reps.fintype_pos (m:ℕ+) : fintype (reps m) :=
fintype.of_equiv {v : fin (m+1) × fin (m+1) × fin (m+1) // v.1.1 * v.2.2.1 = m ∧ v.2.1.1 < v.2.2.1}
{ to_fun := λ A, ⟨ ⟨matrix_makr A.1.1.1  A.1.2.1.1 (0: ℤ)  A.1.2.2.1 ,
by {rw  [dm  A.1.1.1  A.1.2.1.1 (0 : ℤ)  A.1.2.2.1,  mul_zero, sub_zero, ← int.coe_nat_mul, A.2.1, coe_coe] }⟩,
   rfl, by {
          simp  [ int.coe_nat_pos, em, subtype.val_eq_coe],
            have agt: 0 <A.1.1.1,
              by {have age: 0 ≤ A.1.1.1,
                    by {linarith,},
                  rw le_iff_lt_or_eq at age,
                  cases age,
                  exact age,
                  cases m,
                  dsimp at *,
                  rw age,
                  have A_prop:=A.2.1,
                  simp at *,
                  rw ← age at A_prop,
                  simp at *,
                  rw A_prop at m_property,
                  simp at *,
                  exact m_property,},
            exact agt, } ,
  by {
    simp  [ true_and, int.nat_abs_of_nat,
      fin.coe_fin_lt, int.coe_nat_nonneg, em, subtype.val_eq_coe],
    exact A.2.2,} ⟩,
inv_fun := λ A, ⟨ (
    ⟨ int.nat_abs (A.1 0 0), nat.lt_succ_of_le $ nat.le_of_dvd m.2 ⟨int.nat_abs (A.1 1 1),
     by {
        have ao: (A.1).val 1 0 = 0, by { apply A.2.1},
        have := A.1.2,
        simp at *,
        rw matrix.det_fin_two at this,
        rw ao at this,
        simp at this,
        rw [← int.nat_abs_mul],
        rw this,
        simp only [int.nat_abs_of_nat, coe_coe],}  ⟩ ⟩,
  ⟨int.nat_abs (A.1 0 1), nat.lt_succ_of_le $ le_trans (le_of_lt A.2.2.2.2) $ nat.le_of_dvd m.2 ⟨int.nat_abs (A.1 0 0),
     by {
        have ao: (A.1).val 1 0 = 0, by { apply A.2.1},
        have := A.1.2,
        simp at *,
        rw matrix.det_fin_two at this,
        rw ao at this,
        simp at this,
        rw mul_comm at this,
        rw [← int.nat_abs_mul],
        rw this,
        simp only [int.nat_abs_of_nat, coe_coe],}  ⟩ ⟩,
    ⟨int.nat_abs (A.1 1 1), nat.lt_succ_of_le $ nat.le_of_dvd m.2 ⟨int.nat_abs (A.1 0 0),
      by {
        have ao: (A.1).val 1 0 = 0, by { apply A.2.1},
        have := A.1.2,
        simp at *,
        rw matrix.det_fin_two at this,
        rw ao at this,
        simp at this,
        rw mul_comm at this,
        rw [← int.nat_abs_mul],
        rw this,
        simp only [int.nat_abs_of_nat, coe_coe],}  ⟩ ⟩),
     by {
        have ao: (A.1).val 1 0 = 0, by { apply A.2.1},
        have := A.1.2,
        simp at *,
        rw matrix.det_fin_two at this,
        rw ao at this,
        simp at this,
        rw [← int.nat_abs_mul],
        rw this,
        simp only [int.nat_abs_of_nat, coe_coe],},
      A.2.2.2.2⟩,
left_inv := λ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨d, hd⟩⟩, H1, H2⟩, subtype.eq $ prod.ext
  (fin.eq_of_veq $ int.nat_abs_of_nat _) $ prod.ext
  (fin.eq_of_veq $ int.nat_abs_of_nat _)
  (fin.eq_of_veq $ int.nat_abs_of_nat _),
right_inv := λ ⟨ ⟨A ,H1⟩,  H2, H3, H4, H5⟩,
by {
  simp [ subtype.mk_eq_mk],
   ext i j,
   fin_cases i; fin_cases j,
   simp only [em],
   simp  at H3,
   rw ← int.abs_eq_nat_abs,
   apply abs_of_pos H3,
   simp only [em],
   simp  at H4,
   rw ← int.abs_eq_nat_abs,
   apply abs_of_nonneg H4,
   simp only [em],
   simp  at H2,
   simp only [H2],
    simp only [em],
    simp  at H5,
   have h7: A 0 1 < (A 1 1).nat_abs,
      by {
        simp  at H4,
        rw ← int.coe_nat_lt at H5,
        rw  int.nat_abs_of_nonneg H4 at H5,
        exact H5},
    simp  at H4,
    have h8: 0 <(A 1 1).nat_abs,
    by {
      rw ← int.coe_nat_lt,
      apply lt_of_le_of_lt H4 h7 },
      rw ← int.abs_eq_nat_abs,
      rw ← int.coe_nat_lt at h8,
      rw ← int.abs_eq_nat_abs at h8,
      simp only [abs_eq_self],
      simp  at H3,
      apply en_pos m A H1 H3 H2}}



def reps.fintype : Π m : ℤ, m ≠ 0 → fintype (reps m)
| (int.of_nat $ n+1) H := reps.fintype_pos ⟨n+1, nat.zero_lt_succ n⟩
| 0 H := (H rfl).elim
| -[1+ n] H := fintype.of_equiv (reps (⟨n+1, nat.zero_lt_succ _⟩ : pnat))
{to_fun := λ A, ⟨ ⟨matrix_makr(A.1 0 0) (A.1 0 1) (A.1 1 0) (-A.1 1 1),
   have ao: (A.1).val 1 0 = 0, by { apply A.2.1},
    by  {
      have := A.1.2,
      simp only [subtype.val_eq_coe, coe_coe] at this,
      simp only [pnat.mk_coe, int.coe_nat_succ] at this,
      rw matrix.det_fin_two at *,
      simp,
      simp only [subtype.val_eq_coe] at ao,
      rw ao at *,
      simp only [sub_zero, mul_zero] at *,
      rw this,
      rw int.neg_succ_of_nat_coe,
      refl} ⟩,
      A.2.1, A.2.2.1, A.2.2.2.1, trans_rel_left _ A.2.2.2.2 $ eq.symm $ int.nat_abs_neg _⟩,

  inv_fun := λ A, ⟨⟨matrix_makr(A.1 0 0) (A.1 0 1) (A.1 1 0) (-A.1 1 1),
  have ao: (A.1).val 1 0 = 0, by { apply A.2.1},
    by  {
      have := A.1.2,
      simp only [subtype.val_eq_coe, coe_coe] at this,
      rw matrix.det_fin_two at *,
      simp,
      simp only [subtype.val_eq_coe] at ao,
      rw ao at *,
      simp only [sub_zero, mul_zero] at *,
      rw this,
      rw int.neg_succ_of_nat_coe,
      refl} ⟩,
      A.2.1, A.2.2.1, A.2.2.2.1, trans_rel_left _ A.2.2.2.2 $ eq.symm $ int.nat_abs_neg _⟩,

  left_inv := λ ⟨ ⟨A, H1⟩, H2⟩,
   by {
     simp  [subtype.mk_eq_mk, neg_neg, em],
     ext i j,
     fin_cases i; fin_cases j,
     simp only [em],
     simp only [em],
     simp only [em],
     simp only [em],},
  right_inv := λ ⟨⟨A, H1⟩, H2⟩,
  by {
    simp  [ subtype.mk_eq_mk, neg_neg, em],
    ext i j,
    fin_cases i; fin_cases j,
    simp only [em],
    simp only [em],
    simp only [em],
    simp only [em],},
   }


section

/--The relation defined by the action of `gengrp` on `Mat m`-/
def orbit_rel''' (m : ℤ): setoid (Mat m) :=
{ r := λ a b, a ∈ mul_action.orbit gengrp b,
  iseqv := ⟨mul_action.mem_orbit_self, λ a b,
    by
      simp only [mul_action.orbit_eq_iff.symm, eq_comm, imp_self],
    λ a b,
    by
      simp only [mul_action.orbit_eq_iff.symm, implies_true_iff, eq_self_iff_true] {contextual := tt}⟩ }

/--Map from the representatives to the quotient by the orbit relation-/
def π : reps m → quotient (orbit_rel''' m ) :=
  λ A, (@quotient.mk _ (orbit_rel''' m)) A


set_option eqn_compiler.zeta true

def reps_equiv' (hm : m ≠ 0) : quotient (orbit_rel''' m ) ≃ reps m :=
by letI := (orbit_rel''' m ); from
{ to_fun := λ x,
    quotient.lift_on x (λ A, (⟨reduce m A, reduce_mem_reps m hm A⟩ : reps m)) $ λ A B ⟨M, H⟩,
    let ⟨MA, HA⟩ := reduce_spec m A in
    let ⟨MB, HB⟩ := reduce_spec m B in
    subtype.eq $ reps_unique' m hm (MB * M⁻¹ * MA⁻¹) _ _ (reduce_mem_reps m hm A) (reduce_mem_reps m hm B) $
    by {
      simp only,
      rw ← HA,
      rw mul_smul,
      simp only [inv_smul_smul],
      rw mul_smul,
      simp only [_x, forall_true_left] at _fun_match,
      simp only at H,
      rw ← H,
      simp only [exists_imp_distrib] at _let_match,
      rw H,
      rw ← HB,
      simp, rw ← H,
      simp [inv_smul_smul],},
  inv_fun := λ A, ⟦A.1⟧,
  left_inv := λ x, by {
    simp only [subtype.val_eq_coe],
    induction x,
    work_on_goal 1 { cases x, dsimp at *, simp at * },
    work_on_goal 2 { refl },
    apply quotient.sound,
    apply reduce_spec m ⟨ x_val, x_property⟩},
  right_inv := λ A, subtype.eq $
    let ⟨MA, HA⟩ := reduce_spec m A in
    reps_unique' m hm MA⁻¹ _ _ (reduce_mem_reps m hm A) A.2 $
    show  MA⁻¹ • (reduce m A) = A,
    by {rw [← HA], simp only [inv_smul_smul], }, }

protected def decidable_eq (hm : m ≠ 0) : decidable_eq (quotient (orbit_rel''' m )) :=
equiv.decidable_eq (reps_equiv' m hm)

def finiteness (hm : m ≠ 0) : fintype (quotient $ orbit_rel''' m) :=
@fintype.of_equiv _ _ (reps.fintype m hm) (reps_equiv' m hm).symm

lemma Mat1_eq_SL2Z: Mat 1 = SL2Z :=
begin
refl,
end

lemma reps_sl2z: reps 1 = {(1: SL2Z)}:=
begin
  rw reps,
  dsimp,
  ext1,
  split,
  intro hx,
  simp at *,
  have detsl:= matrix.det_fin_two x.1,
  simp at detsl,
  rw hx.1 at detsl,
  simp at detsl,
  have:= detsl.symm,
  rw int.mul_eq_one at this,
  have hx2:= hx.2.1,
  have hh:= one_time' _ _ hx2 this,
  have hx3: x.1 0 1 = 0, by {
    have i1:= hx.2.2.2,
    rw hh.2 at i1,
    simp at i1, simp [i1],},
  simp at hx3, ext,
  fin_cases i; fin_cases j,
  simp [hh.1], simp [hx3],
  simp [hx.1], simp [hh.2],
  intro hx, simp at *, split,
  simp [hx],
  split,
  simp [hx],
  split,
  simp [hx],
  simp [hx],
end


section
universe u
variables {G : Type*} {α : Sort*} [group G] [H : subgroup G]

lemma smul_is_mul_1 (A : SL2Z) (M : integral_matrices_with_determinant (fin 2) 1) :
 ((A • M) : SL2Z) = A * (M : SL2Z) :=
begin
simp [integral_matrices_with_determinant.SLnZ_M],
end

lemma left_rel_to_right_rel_top  (H : subgroup G)  :  (quotient_group.right_rel H) = ⊤ ↔  (quotient_group.left_rel H) = ⊤ :=
begin
let r1:= (quotient_group.left_rel H).r,
let r2:= (quotient_group.right_rel H).r,
have rh1: ∀ x y, r1 x y ↔   x⁻¹ * y ∈ H, by {intros x y, refl,},
have rh2: ∀ x y, r2 x y ↔  y * x⁻¹ ∈ H, by {intros x y, refl,},
split,
intro hr,
rw setoid.eq_top_iff at *,
intros x y,
have hr3:= (rh2 x 1).1 (hr x 1),
have hr3':= (rh2 1 y).1 (hr 1 y),
have : r1 x y, by {rw rh1, simp at *, apply subgroup.mul_mem H ((subgroup.inv_mem_iff H).symm.1 hr3)  hr3',},
convert this,
intro hr,
rw setoid.eq_top_iff at *,
intros x y,
have hr3:= (rh1 x 1).1 (hr x 1),
have hr3':= (rh1 1 y).1 (hr 1 y),
have : r2 x y, by {rw rh2, simp at *, apply subgroup.mul_mem H  hr3' ((subgroup.inv_mem_iff H).symm.1 hr3) ,},
convert this,
end



lemma ring_quot_subsingleton_iff_left_quot_subsingleton (H : subgroup G) :
  subsingleton (quotient (quotient_group.right_rel H)) ↔ subsingleton (G ⧸ H) :=
begin
have : (G ⧸ H) = quotient (quotient_group.left_rel H), by {refl,},
rw this,
split,
intro hr,
rw quotient.subsingleton_iff at *,
apply (left_rel_to_right_rel_top H).1 hr,
intro hr,
rw quotient.subsingleton_iff at *,
apply (left_rel_to_right_rel_top H).2 hr,
end

lemma sl2z_gens: gengrp = (⊤ : subgroup SL2Z) :=
begin
  apply quotient_group.subgroup_eq_top_of_subsingleton,
  rw (ring_quot_subsingleton_iff_left_quot_subsingleton gengrp).symm,
  have h0: (1: ℤ) ≠ 0, by {simp,},
  have h1:= reps_equiv' 1 h0,
  have h2:= reps_sl2z,
  have htt: subsingleton (quotient (orbit_rel''' 1)), by {rw (equiv.subsingleton_congr h1), rw h2, simp, },
  have ht: quotient (orbit_rel''' 1) ≃ (quotient (quotient_group.right_rel gengrp)), by {
  let r1:= ( (orbit_rel''' 1)).r,
  let r2:= (quotient_group.right_rel gengrp).r,
  apply quot.congr_right,
  simp at htt,
  rw htt,
  intros a b,
  have rh1: ∀ x y : SL2Z, r1 x y ↔ x ∈ mul_action.orbit gengrp y, by {intros x y, refl,   },
  have rh2: ∀ x y : SL2Z, r2 x y ↔  y * x⁻¹ ∈ gengrp, by {intros x y, refl,},
  have goal: r2 a b ↔ r1 a b, by {
rw rh1,
rw rh2,
rw mul_action.orbit,
simp,
split,
intro ha,
have haa:= (subgroup.inv_mem_iff gengrp).2 ha,
simp at haa,
refine ⟨⟨(a*b⁻¹ : SL2Z), haa⟩, _⟩,
have:= smul_is_mul_1 (a * b⁻¹) b,
convert this,
have hbb: (a *b⁻¹*b :SL2Z) = (a : SL2Z), by {simp, },
convert hbb.symm,
intro H,
have HB: ∃ y : gengrp , (y : SL2Z) * b =a, by {apply H, },
rw (subgroup.inv_mem_iff gengrp).symm,
simp,
obtain ⟨ y, hy⟩:= HB,
rw ← hy,
simp,},
convert goal.symm,
apply htt.symm, },
rw (equiv.subsingleton_congr ht).symm,
apply htt,
end

end

/--The generators of `SL(2,ℤ)` -/
def Gens:=({ S, T} : set SL2Z)

lemma Gens_subgroup_eq_gengrp : subgroup.closure (Gens) = gengrp :=
begin
  rw Gens,
  rw gengrp,
  refine le_antisymm ((subgroup.closure_le _).2 _) ((subgroup.closure_le _).2 _),
  intros a ha,
  apply subgroup.subset_closure,
  simp only [set.mem_insert_iff, set.mem_singleton_iff] at *,
  cases ha,
  rw ha,
  simp only [true_or, eq_self_iff_true],
  rw ha,
  simp only [true_or, eq_self_iff_true, or_true],
  intros a ha,
  simp only [set.mem_insert_iff, set.mem_singleton_iff, set_like.mem_coe] at *,
  cases ha,
  apply subgroup.subset_closure,
  simp only [set.mem_insert_iff, set.mem_singleton_iff],
  rw ha,
  simp only [true_or, eq_self_iff_true],
  cases ha,
  apply subgroup.subset_closure,
  simp only [set.mem_insert_iff, set.mem_singleton_iff],
  rw ha,
  simp only [eq_self_iff_true, or_true],
  rw (subgroup.inv_mem_iff _ ).symm,
  cases ha,
  apply subgroup.subset_closure,
  rw ha,
  simp only [set.mem_insert_iff, true_or, eq_self_iff_true, inv_inv],
  rw ha,
  simp only [inv_inv],
  apply subgroup.subset_closure,
  simp only [set.mem_insert_iff, set.mem_singleton, or_true],
end

theorem SL2Z_Generators : subgroup.closure (Gens) = ⊤ :=
begin
  rw Gens_subgroup_eq_gengrp,
  apply sl2z_gens,
end

end

end SL2Z_M
