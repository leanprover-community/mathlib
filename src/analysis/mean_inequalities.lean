/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.convex.specific_functions
import analysis.special_functions.pow
import data.real.conjugate_exponents
import tactic.nth_rewrite

/-!
# Mean value inequalities

In this file we prove various inequalities between mean values:
arithmetic mean, geometric mean, generalized mean (natural and integer
cases).

For generalized means we only prove
$\left( ∑_j w_j z_j \right)^n ≤ ∑_j w_j z_j^n$ because standard versions would
require $\sqrt[n]{x}$ which is not implemented in `mathlib` yet.

Probably a better approach to the generalized means inequality is to
prove `convex_on_rpow` in `analysis/convex/specific_functions` first,
then apply it.

It is not yet clear which versions will be useful in the future, so we
provide two different forms of most inequalities : for `ℝ` and for
`ℝ≥0`. For the AM-GM inequality we also prove special cases for `n=2`
and `n=3`.
-/

universes u v

open finset
open_locale classical nnreal big_operators
noncomputable theory

variables {ι : Type u} (s : finset ι)

namespace real

/-- Geometric mean is less than or equal to the arithmetic mean, weighted version
for functions on `finset`s. -/
theorem am_gm_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i in s, w i = 1)
  (hz : ∀ i ∈ s, 0 ≤ z i) :
  (∏ i in s, (z i) ^ (w i)) ≤ ∑ i in s, w i * z i :=
begin
  let s' := s.filter (λ i, w i ≠ 0),
  rw [← sum_filter_ne_zero] at hw',
  suffices : (∏ i in s', (z i) ^ (w i)) ≤ ∑ i in s', w i * z i,
  { have A : ∀ i ∈ s, i ∉ s' → w i = 0,
    { intros i hi hi',
      simpa only [hi, mem_filter, ne.def, true_and, not_not] using hi' },
    have B : ∀ i ∈ s, i ∉ s' → (z i) ^ (w i) = 1,
      from λ i hi hi', by rw [A i hi hi', rpow_zero],
    have C : ∀ i ∈ s, i ∉ s' → w i * z i = 0,
      from λ i hi hi', by rw [A i hi hi', zero_mul],
    rwa [← prod_subset s.filter_subset B, ← sum_subset s.filter_subset C] },
  have A : ∀ i ∈ s', i ∈ s ∧ w i ≠ 0, from λ i hi, mem_filter.1 hi,
  replace hz : ∀ i ∈ s', 0 ≤ z i := λ i hi, hz i (A i hi).1,
  replace hw : ∀ i ∈ s', 0 ≤ w i := λ i hi, hw i (A i hi).1,
  by_cases B : ∃ i ∈ s', z i = 0,
  { rcases B with ⟨i, imem, hzi⟩,
    rw [prod_eq_zero imem],
    { exact sum_nonneg (λ j hj, mul_nonneg (hw j hj) (hz j hj)) },
    { rw hzi, exact zero_rpow (A i imem).2 } },
  { replace hz : ∀ i ∈ s', 0 < z i,
      from λ i hi, lt_of_le_of_ne (hz _ hi) (λ h, B ⟨i, hi, h.symm⟩),
    have := convex_on_exp.map_sum_le hw hw' (λ i _, set.mem_univ $ log (z i)),
    simp only [exp_sum, (∘), smul_eq_mul, mul_comm (w _) (log _)] at this,
    convert this using 1,
    { exact prod_congr rfl (λ i hi, rpow_def_of_pos (hz i hi) _) },
    { exact sum_congr rfl (λ i hi, congr_arg _ (exp_log $ hz i hi).symm) } }
end

end real

namespace nnreal

theorem am_gm_weighted (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) :
  (∏ i in s, (z i) ^ (w i:ℝ)) ≤ ∑ i in s, w i * z i :=
begin
  rw [← nnreal.coe_le_coe],
  push_cast,
  refine real.am_gm_weighted _ _ _ (λ i _, (w i).coe_nonneg) _ (λ i _, (z i).coe_nonneg),
  assumption_mod_cast
end

theorem am_gm2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) (hw : w₁ + w₂ = 1) :
  p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) ≤ w₁ * p₁ + w₂ * p₂ :=
begin
  have := am_gm_weighted (univ : finset (fin 2)) (fin.cons w₁ $ fin.cons w₂ fin_zero_elim)
    (fin.cons p₁ $ fin.cons p₂ $ fin_zero_elim),
  simp only [fin.prod_univ_succ, fin.sum_univ_succ, fin.prod_univ_zero, fin.sum_univ_zero,
    fin.cons_succ, fin.cons_zero, add_zero, mul_one] at this,
  exact this hw
end

theorem am_gm3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) (hw : w₁ + w₂ + w₃ = 1) :
  p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) * p₃ ^ (w₃:ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃:=
begin
  have := am_gm_weighted (univ : finset (fin 3))
    (fin.cons w₁ $ fin.cons w₂ $ fin.cons w₃ fin_zero_elim)
    (fin.cons p₁ $ fin.cons p₂ $ fin.cons p₃ fin_zero_elim),
  simp only [fin.prod_univ_succ, fin.sum_univ_succ, fin.prod_univ_zero, fin.sum_univ_zero,
    fin.cons_succ, fin.cons_zero, add_zero, mul_one, (add_assoc _ _ _).symm,
    (mul_assoc _ _ _).symm] at this,
  exact this hw
end

end nnreal

namespace real

theorem am_gm2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
  (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
nnreal.am_gm2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ $ nnreal.coe_eq.1 $ by assumption

/-- Young's inequality, a version for nonnegative real numbers. -/
theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
  (hpq : p.is_conjugate_exponent q) :
  a * b ≤ a^p / p + b^q / q :=
by simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul]
  using real.am_gm2_weighted hpq.one_div_nonneg hpq.symm.one_div_nonneg
    (rpow_nonneg_of_nonneg ha p) (rpow_nonneg_of_nonneg hb q) hpq.inv_add_inv_conj

/-- Young's inequality, a version for arbitrary real numbers. -/
theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  a * b ≤ (abs a)^p / p + (abs b)^q / q :=
calc a * b ≤ abs (a * b)                   : le_abs_self (a * b)
       ... = abs a * abs b                 : abs_mul a b
       ... ≤ (abs a)^p / p + (abs b)^q / q :
  real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

theorem pow_am_le_am_pow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (n : ℕ) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, (w i * z i ^ n) :=
(convex_on_pow n).map_sum_le hw hw' hz

theorem pow_am_le_am_pow_of_even (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) {n : ℕ} (hn : n.even) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, (w i * z i ^ n) :=
(convex_on_pow_of_even hn).map_sum_le hw hw' (λ _ _, trivial)

theorem fpow_am_le_am_fpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) (m : ℤ) :
  (∑ i in s, w i * z i) ^ m ≤ ∑ i in s, (w i * z i ^ m) :=
(convex_on_fpow m).map_sum_le hw hw' hz

theorem rpow_am_le_am_rpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, w i * z i) ^ p ≤ ∑ i in s, (w i * z i ^ p) :=
(convex_on_rpow hp).map_sum_le hw hw' hz

end real

namespace nnreal

/-- Young's inequality, `ℝ≥0` version -/
theorem young_inequality (a b : ℝ≥0) {p q : ℝ≥0} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
  a * b ≤ a^(p:ℝ) / p + b^(q:ℝ) / q :=
real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg ⟨hp, nnreal.coe_eq.2 hpq⟩

theorem pow_am_le_am_pow (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) (n : ℕ) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, (w i * z i ^ n) :=
begin
  rw [← nnreal.coe_le_coe],
  push_cast,
  refine real.pow_am_le_am_pow s _ _ (λ i _, (w i).coe_nonneg) _ (λ i _, (z i).coe_nonneg) n,
  assumption_mod_cast
end

theorem rpow_am_le_am_rpow (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, w i * z i) ^ p ≤ ∑ i in s, (w i * z i ^ p) :=
begin
  rw [← nnreal.coe_le_coe],
  push_cast,
  refine real.rpow_am_le_am_rpow s _ _ (λ i _, (w i).coe_nonneg) _ (λ i _, (z i).coe_nonneg) hp,
  assumption_mod_cast
end

end nnreal
