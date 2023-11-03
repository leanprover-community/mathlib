/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import measure_theory.integral.fund_thm_calculus
import analysis.special_functions.trigonometric.arctan_deriv

/-!
# Integration of specific interval integrals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains proofs of the integrals of various specific functions. This includes:
* Integrals of simple functions, such as `id`, `pow`, `inv`, `exp`, `log`
* Integrals of some trigonometric functions, such as `sin`, `cos`, `1 / (1 + x^2)`
* The integral of `cos x ^ 2 - sin x ^ 2`
* Reduction formulae for the integrals of `sin x ^ n` and `cos x ^ n` for `n ≥ 2`
* The computation of `∫_{0}^{π} x, sin x ^ n` as a product for even and odd `n` (used in proving the
  Wallis product for pi)
* Integrals of the form `sin x ^ m * cos x ^ n`

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`.
See `test/integration.lean` for specific examples.

This file also contains some facts about the interval integrability of specific functions.

This file is still being developed.

## Tags

integrate, integration, integrable, integrability
-/

open real nat set finset
open_locale real big_operators interval
variables {a b : ℝ} (n : ℕ)

namespace interval_integral
open measure_theory
variables {f : ℝ → ℝ} {μ ν : measure ℝ} [is_locally_finite_measure μ] (c d : ℝ)

/-! ### Interval integrability -/

@[simp]
lemma interval_integrable_pow : interval_integrable (λ x, x^n) μ a b :=
(continuous_pow n).interval_integrable a b

lemma interval_integrable_zpow {n : ℤ} (h : 0 ≤ n ∨ (0 : ℝ) ∉ [a, b]) :
  interval_integrable (λ x, x ^ n) μ a b :=
(continuous_on_id.zpow₀ n $ λ x hx, h.symm.imp (ne_of_mem_of_not_mem hx) id).interval_integrable

/-- See `interval_integrable_rpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
lemma interval_integrable_rpow {r : ℝ} (h : 0 ≤ r ∨ (0 : ℝ) ∉ [a, b]) :
  interval_integrable (λ x, x ^ r) μ a b :=
(continuous_on_id.rpow_const $ λ x hx, h.symm.imp (ne_of_mem_of_not_mem hx) id).interval_integrable

/-- See `interval_integrable_rpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
lemma interval_integrable_rpow' {r : ℝ} (h : -1 < r) :
  interval_integrable (λ x, x ^ r) volume a b :=
begin
  suffices : ∀ (c : ℝ), interval_integrable (λ x, x ^ r) volume 0 c,
  { exact interval_integrable.trans (this a).symm (this b) },
  have : ∀ (c : ℝ), (0 ≤ c) → interval_integrable (λ x, x ^ r) volume 0 c,
  { intros c hc,
    rw [interval_integrable_iff, uIoc_of_le hc],
    have hderiv : ∀ x ∈ Ioo 0 c, has_deriv_at (λ x : ℝ, x ^ (r + 1) / (r + 1)) (x ^ r) x,
    { intros x hx, convert (real.has_deriv_at_rpow_const (or.inl hx.1.ne')).div_const (r + 1),
      field_simp [(by linarith : r + 1 ≠ 0)], ring, },
    apply integrable_on_deriv_of_nonneg _ hderiv,
    { intros x hx, apply rpow_nonneg_of_nonneg hx.1.le, },
    { refine (continuous_on_id.rpow_const _).div_const _, intros x hx, right, linarith } },
  intro c, rcases le_total 0 c with hc|hc,
  { exact this c hc },
  { rw [interval_integrable.iff_comp_neg, neg_zero],
    have m := (this (-c) (by linarith)).smul (cos (r * π)),
    rw interval_integrable_iff at m ⊢,
    refine m.congr_fun _ measurable_set_Ioc, intros x hx,
    rw uIoc_of_le (by linarith : 0 ≤ -c) at hx,
    simp only [pi.smul_apply, algebra.id.smul_eq_mul, log_neg_eq_log, mul_comm,
      rpow_def_of_pos hx.1, rpow_def_of_neg (by linarith [hx.1] : -x < 0)], }
end

/-- See `interval_integrable_cpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
lemma interval_integrable_cpow {r : ℂ} (h : 0 ≤ r.re ∨ (0 : ℝ) ∉ [a, b]) :
  interval_integrable (λ x : ℝ, (x : ℂ) ^ r) μ a b :=
begin
  by_cases h2 : (0:ℝ) ∉ [a,b],
  { -- Easy case #1: 0 ∉ [a, b] -- use continuity.
    refine (continuous_at.continuous_on (λ x hx, _)).interval_integrable,
    exact complex.continuous_at_of_real_cpow_const _ _ (or.inr $ ne_of_mem_of_not_mem hx h2) },
  rw [eq_false_intro h2, or_false] at h,
  rcases lt_or_eq_of_le h with h'|h',
  { -- Easy case #2: 0 < re r -- again use continuity
    exact (complex.continuous_of_real_cpow_const h').interval_integrable _ _ },
  -- Now the hard case: re r = 0 and 0 is in the interval.
  refine (interval_integrable.interval_integrable_norm_iff _).mp _,
  { refine (measurable_of_continuous_on_compl_singleton (0:ℝ) _).ae_strongly_measurable,
    exact continuous_at.continuous_on
      (λ x hx, complex.continuous_at_of_real_cpow_const x r (or.inr hx)) },
  -- reduce to case of integral over `[0, c]`
  suffices : ∀ (c : ℝ), interval_integrable (λ x : ℝ, ‖↑x ^ r‖) μ 0 c,
    from (this a).symm.trans (this b),
  intro c,
  rcases le_or_lt 0 c with hc | hc,
  { -- case `0 ≤ c`: integrand is identically 1
    have : interval_integrable (λ x, 1 : ℝ → ℝ) μ 0 c,
      from interval_integrable_const,
    rw interval_integrable_iff_integrable_Ioc_of_le hc at this ⊢,
    refine integrable_on.congr_fun this (λ x hx, _) measurable_set_Ioc,
    dsimp only,
    rw [complex.norm_eq_abs, complex.abs_cpow_eq_rpow_re_of_pos hx.1, ←h', rpow_zero], },
  { -- case `c < 0`: integrand is identically constant, *except* at `x = 0` if `r ≠ 0`.
    apply interval_integrable.symm,
    rw [interval_integrable_iff_integrable_Ioc_of_le hc.le],
    have : Ioc c 0 = Ioo c 0 ∪ {(0:ℝ)},
    { rw [←Ioo_union_Icc_eq_Ioc hc (le_refl 0), ←Icc_def],
      simp_rw [←le_antisymm_iff, set_of_eq_eq_singleton'] },
    rw [this, integrable_on_union, and.comm], split,
    { refine integrable_on_singleton_iff.mpr (or.inr _),
      exact is_finite_measure_on_compacts_of_is_locally_finite_measure.lt_top_of_is_compact
        is_compact_singleton },
    { have : ∀ (x : ℝ), x ∈ Ioo c 0 → ‖complex.exp (↑π * complex.I * r)‖ = ‖(x:ℂ) ^ r‖,
      { intros x hx,
        rw [complex.of_real_cpow_of_nonpos hx.2.le, norm_mul, ←complex.of_real_neg,
          complex.norm_eq_abs (_ ^ _), complex.abs_cpow_eq_rpow_re_of_pos (neg_pos.mpr hx.2),
          ←h', rpow_zero, one_mul] },
      refine integrable_on.congr_fun _ this measurable_set_Ioo,
      rw integrable_on_const,
      refine or.inr ((measure_mono set.Ioo_subset_Icc_self).trans_lt _),
      exact is_finite_measure_on_compacts_of_is_locally_finite_measure.lt_top_of_is_compact
        is_compact_Icc } },
end

/-- See `interval_integrable_cpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
lemma interval_integrable_cpow' {r : ℂ} (h : -1 < r.re) :
  interval_integrable (λ x:ℝ, (x:ℂ) ^ r) volume a b :=
begin
  suffices : ∀ (c : ℝ), interval_integrable (λ x, (x : ℂ) ^ r) volume 0 c,
  { exact interval_integrable.trans (this a).symm (this b) },
  have : ∀ (c : ℝ), (0 ≤ c) → interval_integrable (λ x, (x : ℂ) ^ r) volume 0 c,
  { intros c hc,
    rw ←interval_integrable.interval_integrable_norm_iff,
    { rw interval_integrable_iff,
      apply integrable_on.congr_fun,
      { rw ←interval_integrable_iff, exact (interval_integral.interval_integrable_rpow' h) },
      { intros x hx,
        rw uIoc_of_le hc at hx,
        dsimp only,
        rw [complex.norm_eq_abs, complex.abs_cpow_eq_rpow_re_of_pos hx.1] },
      { exact measurable_set_uIoc } },
    { refine continuous_on.ae_strongly_measurable _ measurable_set_uIoc,
      refine continuous_at.continuous_on (λ x hx, _),
      rw uIoc_of_le hc at hx,
      refine (continuous_at_cpow_const (or.inl _)).comp complex.continuous_of_real.continuous_at,
      rw complex.of_real_re,
      exact hx.1 } },
  intro c, rcases le_total 0 c with hc | hc,
  { exact this c hc },
  { rw [interval_integrable.iff_comp_neg, neg_zero],
    have m := (this (-c) (by linarith)).const_mul (complex.exp (π * complex.I * r)),
    rw [interval_integrable_iff, uIoc_of_le (by linarith : 0 ≤ -c)] at m ⊢,
    refine m.congr_fun (λ x hx, _) measurable_set_Ioc,
    dsimp only,
    have : -x ≤ 0, by linarith [hx.1],
    rw [complex.of_real_cpow_of_nonpos this, mul_comm],
    simp }
end

@[simp]
lemma interval_integrable_id : interval_integrable (λ x, x) μ a b :=
continuous_id.interval_integrable a b

@[simp]
lemma interval_integrable_const : interval_integrable (λ x, c) μ a b :=
continuous_const.interval_integrable a b

lemma interval_integrable_one_div (h : ∀ x : ℝ, x ∈ [a, b] → f x ≠ 0)
  (hf : continuous_on f [a, b]) :
  interval_integrable (λ x, 1 / f x) μ a b :=
(continuous_on_const.div hf h).interval_integrable

@[simp]
lemma interval_integrable_inv (h : ∀ x : ℝ, x ∈ [a, b] → f x ≠ 0)
  (hf : continuous_on f [a, b]) :
  interval_integrable (λ x, (f x)⁻¹) μ a b :=
by simpa only [one_div] using interval_integrable_one_div h hf

@[simp]
lemma interval_integrable_exp : interval_integrable exp μ a b :=
continuous_exp.interval_integrable a b

@[simp]
lemma _root_.interval_integrable.log
  (hf : continuous_on f [a, b]) (h : ∀ x : ℝ, x ∈ [a, b] → f x ≠ 0) :
  interval_integrable (λ x, log (f x)) μ a b :=
(continuous_on.log hf h).interval_integrable

@[simp]
lemma interval_integrable_log (h : (0:ℝ) ∉ [a, b]) :
  interval_integrable log μ a b :=
interval_integrable.log continuous_on_id $ λ x hx, ne_of_mem_of_not_mem hx h

@[simp]
lemma interval_integrable_sin : interval_integrable sin μ a b :=
continuous_sin.interval_integrable a b

@[simp]
lemma interval_integrable_cos : interval_integrable cos μ a b :=
continuous_cos.interval_integrable a b

lemma interval_integrable_one_div_one_add_sq : interval_integrable (λ x : ℝ, 1 / (1 + x^2)) μ a b :=
begin
  refine (continuous_const.div _ (λ x, _)).interval_integrable a b,
  { continuity },
  { nlinarith },
end

@[simp]
lemma interval_integrable_inv_one_add_sq : interval_integrable (λ x : ℝ, (1 + x^2)⁻¹) μ a b :=
by simpa only [one_div] using interval_integrable_one_div_one_add_sq

/-! ### Integrals of the form `c * ∫_{a}^{b} x, f (c * x + d)` -/

@[simp]
lemma mul_integral_comp_mul_right : c * ∫_{a}^{b} x, f (x * c) = ∫_{a*c}^{b*c} x, f x :=
smul_integral_comp_mul_right f c

@[simp]
lemma mul_integral_comp_mul_left : c * ∫_{a}^{b} x, f (c * x) = ∫_{c*a}^{c*b} x, f x :=
smul_integral_comp_mul_left f c

@[simp]
lemma inv_mul_integral_comp_div : c⁻¹ * ∫_{a}^{b} x, f (x / c) = ∫_{a/c}^{b/c} x, f x :=
inv_smul_integral_comp_div f c

@[simp]
lemma mul_integral_comp_mul_add : c * ∫_{a}^{b} x, f (c * x + d) = ∫_{c*a+d}^{c*b+d} x, f x :=
smul_integral_comp_mul_add f c d

@[simp]
lemma mul_integral_comp_add_mul : c * ∫_{a}^{b} x, f (d + c * x) = ∫_{d+c*a}^{d+c*b} x, f x :=
smul_integral_comp_add_mul f c d

@[simp]
lemma inv_mul_integral_comp_div_add : c⁻¹ * ∫_{a}^{b} x, f (x / c + d) = ∫_{a/c+d}^{b/c+d} x, f x :=
inv_smul_integral_comp_div_add f c d

@[simp]
lemma inv_mul_integral_comp_add_div : c⁻¹ * ∫_{a}^{b} x, f (d + x / c) = ∫_{d+a/c}^{d+b/c} x, f x :=
inv_smul_integral_comp_add_div f c d

@[simp]
lemma mul_integral_comp_mul_sub : c * ∫_{a}^{b} x, f (c * x - d) = ∫_{c*a-d}^{c*b-d} x, f x :=
smul_integral_comp_mul_sub f c d

@[simp]
lemma mul_integral_comp_sub_mul : c * ∫_{a}^{b} x, f (d - c * x) = ∫_{d-c*b}^{d-c*a} x, f x :=
smul_integral_comp_sub_mul f c d

@[simp]
lemma inv_mul_integral_comp_div_sub : c⁻¹ * ∫_{a}^{b} x, f (x / c - d) = ∫_{a/c-d}^{b/c-d} x, f x :=
inv_smul_integral_comp_div_sub f c d

@[simp]
lemma inv_mul_integral_comp_sub_div : c⁻¹ * ∫_{a}^{b} x, f (d - x / c) = ∫_{d-b/c}^{d-a/c} x, f x :=
inv_smul_integral_comp_sub_div f c d

end interval_integral

open interval_integral

/-! ### Integrals of simple functions -/

lemma integral_cpow {r : ℂ} (h : -1 < r.re ∨ (r ≠ -1 ∧ (0 : ℝ) ∉ [a, b])) :
  ∫_{a}^{b} x, (x : ℂ) ^ r = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) :=
begin
  rw sub_div,
  have hr : r + 1 ≠ 0,
  { cases h,
    { apply_fun complex.re,
      rw [complex.add_re, complex.one_re, complex.zero_re, ne.def, add_eq_zero_iff_eq_neg],
      exact h.ne' },
    { rw [ne.def, ←add_eq_zero_iff_eq_neg] at h, exact h.1 } },
  by_cases hab : (0:ℝ) ∉ [a, b],
  { refine integral_eq_sub_of_has_deriv_at (λ x hx, _) (interval_integrable_cpow $ or.inr hab),
    refine has_deriv_at_of_real_cpow (ne_of_mem_of_not_mem hx hab) _,
    contrapose! hr, rwa add_eq_zero_iff_eq_neg },
  replace h : -1 < r.re, by tauto,
  suffices : ∀ (c : ℝ), ∫_{0}^{c} x, (x : ℂ) ^ r =
    c ^ (r + 1) / (r + 1) - 0 ^ (r + 1) / (r + 1),
  { rw [←integral_add_adjacent_intervals (@interval_integrable_cpow' a 0 r h)
      (@interval_integrable_cpow' 0 b r h), integral_symm, this a, this b, complex.zero_cpow hr],
    ring },
  intro c,
  apply integral_eq_sub_of_has_deriv_right,
  { refine ((complex.continuous_of_real_cpow_const _).div_const _).continuous_on,
    rwa [complex.add_re, complex.one_re, ←neg_lt_iff_pos_add] },
  { refine λ x hx, (has_deriv_at_of_real_cpow _ _).has_deriv_within_at,
    { rcases le_total c 0 with hc | hc,
      { rw max_eq_left hc at hx, exact hx.2.ne }, { rw min_eq_left hc at hx, exact hx.1.ne' } },
    { contrapose! hr, rw hr, ring } },
  { exact interval_integrable_cpow' h }
end

lemma integral_rpow {r : ℝ} (h : -1 < r ∨ (r ≠ -1 ∧ (0 : ℝ) ∉ [a, b])) :
  ∫_{a}^{b} x, x ^ r = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) :=
begin
  have h' : -1 < (r:ℂ).re ∨ (r:ℂ) ≠ -1 ∧ (0:ℝ) ∉ [a, b],
  { cases h,
    { left, rwa complex.of_real_re },
    { right, rwa [←complex.of_real_one, ←complex.of_real_neg, ne.def, complex.of_real_inj] } },
  have : ∫_{a}^{b} x, (x:ℂ) ^ (r :ℂ) = ((b:ℂ) ^ (r + 1 : ℂ) - (a:ℂ) ^ (r + 1 : ℂ)) / (r + 1),
    from integral_cpow h',
  apply_fun complex.re at this, convert this,
  { simp_rw [interval_integral_eq_integral_uIoc, complex.real_smul, complex.of_real_mul_re],
    { change complex.re with is_R_or_C.re,
      rw ←integral_re, refl,
      refine interval_integrable_iff.mp _,
      cases h',
      { exact interval_integrable_cpow' h' }, { exact interval_integrable_cpow (or.inr h'.2) } } },
  { rw (by push_cast : ((r:ℂ) + 1) = ((r + 1 : ℝ) : ℂ)),
    simp_rw [div_eq_inv_mul, ←complex.of_real_inv, complex.of_real_mul_re, complex.sub_re],
    refl }
end

lemma integral_zpow {n : ℤ} (h : 0 ≤ n ∨ n ≠ -1 ∧ (0 : ℝ) ∉ [a, b]) :
  ∫_{a}^{b} x, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) :=
begin
  replace h : -1 < (n : ℝ) ∨ (n : ℝ) ≠ -1 ∧ (0 : ℝ) ∉ [a, b], by exact_mod_cast h,
  exact_mod_cast integral_rpow h,
end

@[simp] lemma integral_pow : ∫_{a}^{b} x, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) :=
by simpa only [←int.coe_nat_succ, zpow_coe_nat] using integral_zpow (or.inl (int.coe_nat_nonneg n))

/-- Integral of `|x - a| ^ n` over `Ι a b`. This integral appears in the proof of the
Picard-Lindelöf/Cauchy-Lipschitz theorem. -/
lemma integral_pow_abs_sub_uIoc :
  ∫ x in Ι a b, |x - a| ^ n = |b - a| ^ (n + 1) / (n + 1) :=
begin
  cases le_or_lt a b with hab hab,
  { calc ∫ x in Ι a b, |x - a| ^ n = ∫_{a}^{b} x, |x - a| ^ n :
      by rw [uIoc_of_le hab, ← integral_of_le hab]
    ... = ∫_{0}^{(b - a)} x, x ^ n :
      begin
        simp only [integral_comp_sub_right (λ x, |x| ^ n), sub_self],
        refine integral_congr (λ x hx, congr_arg2 has_pow.pow (abs_of_nonneg $ _) rfl),
        rw uIcc_of_le (sub_nonneg.2 hab) at hx,
        exact hx.1
      end
    ... = |b - a| ^ (n + 1) / (n + 1) : by simp [abs_of_nonneg (sub_nonneg.2 hab)] },
  { calc ∫ x in Ι a b, |x - a| ^ n = ∫_{b}^{a} x, |x - a| ^ n :
      by rw [uIoc_of_lt hab, ← integral_of_le hab.le]
    ... = ∫_{b - a}^{0} x, (-x) ^ n :
      begin
        simp only [integral_comp_sub_right (λ x, |x| ^ n), sub_self],
        refine integral_congr (λ x hx, congr_arg2 has_pow.pow (abs_of_nonpos $ _) rfl),
        rw uIcc_of_le (sub_nonpos.2 hab.le) at hx,
        exact hx.2
      end
    ... = |b - a| ^ (n + 1) / (n + 1) :
      by simp [integral_comp_neg (λ x, x ^ n), abs_of_neg (sub_neg.2 hab)] }
end

@[simp]
lemma integral_id : ∫_{a}^{b} x, x = (b ^ 2 - a ^ 2) / 2 :=
by simpa using integral_pow 1

@[simp]
lemma integral_one : ∫_{a}^{b} x, (1 : ℝ) = b - a :=
by simp only [mul_one, smul_eq_mul, integral_const]

lemma integral_const_on_unit_interval : ∫_{a}^{(a + 1)} x, b = b :=
by simp

@[simp]
lemma integral_inv (h : (0:ℝ) ∉ [a, b]) : ∫_{a}^{b} x, x⁻¹ = log (b / a) :=
begin
  have h' := λ x hx, ne_of_mem_of_not_mem hx h,
  rw [integral_deriv_eq_sub' _ deriv_log' (λ x hx, differentiable_at_log (h' x hx))
        (continuous_on_inv₀.mono $ subset_compl_singleton_iff.mpr h),
      log_div (h' b right_mem_uIcc) (h' a left_mem_uIcc)],
end

@[simp]
lemma integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫_{a}^{b} x, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_uIcc_of_lt ha hb

@[simp]
lemma integral_inv_of_neg (ha : a < 0) (hb : b < 0) : ∫_{a}^{b} x, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_uIcc_of_gt ha hb

lemma integral_one_div (h : (0:ℝ) ∉ [a, b]) : ∫_{a}^{b} x, 1/x = log (b / a) :=
by simp only [one_div, integral_inv h]

lemma integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) : ∫_{a}^{b} x, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_pos ha hb]

lemma integral_one_div_of_neg (ha : a < 0) (hb : b < 0) : ∫_{a}^{b} x, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_neg ha hb]

@[simp]
lemma integral_exp : ∫_{a}^{b} x, exp x = exp b - exp a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_on_exp]

lemma integral_exp_mul_complex {c : ℂ} (hc : c ≠ 0) :
  ∫_{a}^{b} x, complex.exp (c * x) = (complex.exp (c * b) - complex.exp (c * a)) / c :=
begin
  have D : ∀ (x : ℝ), has_deriv_at (λ (y : ℝ), complex.exp (c * y) / c) (complex.exp (c * x)) x,
  { intro x,
    conv { congr, skip, rw ←mul_div_cancel (complex.exp (c * x)) hc, },
    convert ((complex.has_deriv_at_exp _).comp x _).div_const c using 1,
    simpa only [mul_one] using ((has_deriv_at_id (x:ℂ)).const_mul _).comp_of_real, },
  rw integral_deriv_eq_sub' _ (funext (λ x, (D x).deriv)) (λ x hx, (D x).differentiable_at),
  { ring_nf },
  { apply continuous.continuous_on, continuity,}
end

@[simp]
lemma integral_log (h : (0:ℝ) ∉ [a, b]) :
  ∫_{a}^{b} x, log x = b * log b - a * log a - b + a :=
begin
  obtain ⟨h', heq⟩ := ⟨λ x hx, ne_of_mem_of_not_mem hx h, λ x hx, mul_inv_cancel (h' x hx)⟩,
  convert integral_mul_deriv_eq_deriv_mul (λ x hx, has_deriv_at_log (h' x hx))
      (λ x hx, has_deriv_at_id x)
      (continuous_on_inv₀.mono $ subset_compl_singleton_iff.mpr h).interval_integrable
      continuous_on_const.interval_integrable using 1;
    simp [integral_congr heq, mul_comm, ← sub_add],
end

@[simp]
lemma integral_log_of_pos (ha : 0 < a) (hb : 0 < b) :
  ∫_{a}^{b} x, log x = b * log b - a * log a - b + a :=
integral_log $ not_mem_uIcc_of_lt ha hb

@[simp]
lemma integral_log_of_neg (ha : a < 0) (hb : b < 0) :
  ∫_{a}^{b} x, log x = b * log b - a * log a - b + a :=
integral_log $ not_mem_uIcc_of_gt ha hb

@[simp]
lemma integral_sin : ∫_{a}^{b} x, sin x = cos a - cos b :=
by rw integral_deriv_eq_sub' (λ x, -cos x); norm_num [continuous_on_sin]

@[simp]
lemma integral_cos : ∫_{a}^{b} x, cos x = sin b - sin a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_on_cos]

lemma integral_cos_mul_complex {z : ℂ} (hz : z ≠ 0) (a b : ℝ) :
  ∫_{a}^{b} x, complex.cos (z * x) = complex.sin (z * b) / z - complex.sin (z * a) / z :=
begin
  apply integral_eq_sub_of_has_deriv_at,
  swap,
  { apply continuous.interval_integrable,
    exact complex.continuous_cos.comp (continuous_const.mul complex.continuous_of_real) },
  intros x hx,
  have a := complex.has_deriv_at_sin (↑x * z),
  have b : has_deriv_at (λ y, y * z : ℂ → ℂ) z ↑x := has_deriv_at_mul_const _,
  have c : has_deriv_at (λ (y : ℂ), complex.sin (y * z)) _ ↑x := has_deriv_at.comp x a b,
  convert has_deriv_at.comp_of_real (c.div_const z),
  { simp_rw mul_comm },
  { rw [mul_div_cancel _ hz, mul_comm] },
end

lemma integral_cos_sq_sub_sin_sq :
  ∫_{a}^{b} x, cos x ^ 2 - sin x ^ 2 = sin b * cos b - sin a * cos a :=
by simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using integral_deriv_mul_eq_sub
  (λ x hx, has_deriv_at_sin x) (λ x hx, has_deriv_at_cos x) continuous_on_cos.interval_integrable
  continuous_on_sin.neg.interval_integrable

@[simp]
lemma integral_inv_one_add_sq : ∫_{a}^{b} x, (1 + x^2)⁻¹ = arctan b - arctan a :=
begin
  simp only [← one_div],
  refine integral_deriv_eq_sub' _ _ _ (continuous_const.div _ (λ x, _)).continuous_on,
  { norm_num },
  { norm_num },
  { continuity },
  { nlinarith },
end

lemma integral_one_div_one_add_sq : ∫_{a}^{b} x, 1 / (1 + x^2) = arctan b - arctan a :=
by simp only [one_div, integral_inv_one_add_sq]

section rpow_cpow
open complex

lemma integral_mul_cpow_one_add_sq {t : ℂ} (ht : t ≠ -1) :
  ∫_{a}^{b} x, (x:ℂ) * (1 + x ^ 2) ^ t =
  (1 + b ^ 2) ^ (t + 1) / (2 * (t + 1)) - (1 + a ^ 2) ^ (t + 1) / (2 * (t + 1)) :=
begin
  have : t + 1 ≠ 0 := by { contrapose! ht, rwa add_eq_zero_iff_eq_neg at ht },
  apply integral_eq_sub_of_has_deriv_at,
  { intros x hx,
    have f : has_deriv_at (λ y:ℂ, 1 + y ^ 2) (2 * x) x,
    { convert (has_deriv_at_pow 2 (x:ℂ)).const_add 1, { norm_cast }, { simp } },
    have g : ∀ {z : ℂ}, (0 < z.re) → has_deriv_at (λ z, z ^ (t + 1) / (2 * (t + 1))) (z ^ t / 2) z,
    { intros z hz,
      have : z ≠ 0 := by { contrapose! hz, rw [hz, zero_re], },
      convert (has_deriv_at.cpow_const (has_deriv_at_id _) (or.inl hz)).div_const
        (2 * (t + 1)) using 1,
      field_simp,
      ring },
    convert (has_deriv_at.comp ↑x (g _) f).comp_of_real using 1,
    { field_simp, ring },
    { rw [add_re, one_re, ←of_real_pow, of_real_re],
      exact (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg x)) } },
  { apply continuous.interval_integrable,
    refine continuous_of_real.mul _,
    apply continuous.cpow,
    { exact continuous_const.add (continuous_of_real.pow 2)},
    { exact continuous_const },
    { intro a,
      rw [add_re, one_re, ←of_real_pow, of_real_re],
      exact or.inl (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg a)) } }
end

lemma integral_mul_rpow_one_add_sq {t : ℝ} (ht : t ≠ -1) :
  ∫_{a}^{b} x, x * (1 + x ^ 2) ^ t =
  (1 + b ^ 2) ^ (t + 1) / (2 * (t + 1)) - (1 + a ^ 2) ^ (t + 1) / (2 * (t + 1)) :=
begin
  have : ∀ (x s : ℝ), (((1 + x ^ 2) ^ s : ℝ) : ℂ) = (1 + (x : ℂ) ^ 2) ^ ↑s,
  { intros x s,
    rw [of_real_cpow, of_real_add, of_real_pow, of_real_one],
    exact add_nonneg zero_le_one (sq_nonneg x), },
  rw ←of_real_inj,
  convert integral_mul_cpow_one_add_sq (_ : (t:ℂ) ≠ -1),
  { rw ←interval_integral.integral_of_real,
    congr' with x:1,
    rw [of_real_mul, this x t] },
  { simp_rw [of_real_sub, of_real_div, this a (t + 1), this b (t + 1)],
    push_cast },
  { rw [←of_real_one, ←of_real_neg, ne.def, of_real_inj],
    exact ht },
end

end rpow_cpow

/-! ### Integral of `sin x ^ n` -/

lemma integral_sin_pow_aux :
  ∫_{a}^{b} x, sin x ^ (n + 2) = sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
    + (n + 1) * (∫_{a}^{b} x, sin x ^ n) - (n + 1) * ∫_{a}^{b} x, sin x ^ (n + 2) :=
begin
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b,
  have h : ∀ α β γ : ℝ, (β * α * γ) * α = β * (α * α * γ) := λ α β γ, by ring,
  have hu : ∀ x ∈ _, has_deriv_at (λ y, sin y ^ (n + 1)) ((n + 1 : ℕ) * cos x * sin x ^ n) x :=
    λ x hx, by simpa only [mul_right_comm] using (has_deriv_at_sin x).pow (n+1),
  have hv : ∀ x ∈ [a, b], has_deriv_at (-cos) (sin x) x :=
    λ x hx, by simpa only [neg_neg] using (has_deriv_at_cos x).neg,
  have H := integral_mul_deriv_eq_deriv_mul hu hv _ _,
  calc  ∫_{a}^{b} x, sin x ^ (n + 2)
      = ∫_{a}^{b} x, sin x ^ (n + 1) * sin x                   : by simp only [pow_succ']
  ... = C + (n + 1) * ∫_{a}^{b} x, cos x ^ 2 * sin x ^ n       : by simp [H, h, sq]
  ... = C + (n + 1) * ∫_{a}^{b} x, sin x ^ n - sin x ^ (n + 2) : by simp [cos_sq', sub_mul,
                                                                          ← pow_add, add_comm]
  ... = C + (n + 1) * (∫_{a}^{b} x, sin x ^ n) - (n + 1) * ∫_{a}^{b} x, sin x ^ (n + 2) :
    by rw [integral_sub, mul_sub, add_sub_assoc]; apply continuous.interval_integrable; continuity,
  all_goals { apply continuous.interval_integrable, continuity },
end

/-- The reduction formula for the integral of `sin x ^ n` for any natural `n ≥ 2`. -/
lemma integral_sin_pow :
  ∫_{a}^{b} x, sin x ^ (n + 2) = (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b) / (n + 2)
    + (n + 1) / (n + 2) * ∫_{a}^{b} x, sin x ^ n :=
begin
  have : (n : ℝ) + 2 ≠ 0 := by exact_mod_cast succ_ne_zero n.succ,
  field_simp,
  convert eq_sub_iff_add_eq.mp (integral_sin_pow_aux n),
  ring,
end

@[simp]
lemma integral_sin_sq : ∫_{a}^{b} x, sin x ^ 2 = (sin a * cos a - sin b * cos b + b - a) / 2 :=
by field_simp [integral_sin_pow, add_sub_assoc]

theorem integral_sin_pow_odd :
  ∫_{0}^{π} x, sin x ^ (2 * n + 1) = 2 * ∏ i in range n, (2 * i + 2) / (2 * i + 3) :=
begin
  induction n with k ih, { norm_num },
  rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow],
  norm_cast,
  simp [-cast_add] with field_simps,
end

theorem integral_sin_pow_even :
  ∫_{0}^{π} x, sin x ^ (2 * n) = π * ∏ i in range n, (2 * i + 1) / (2 * i + 2) :=
begin
  induction n with k ih, { simp },
  rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow],
  norm_cast,
  simp [-cast_add] with field_simps,
end

lemma integral_sin_pow_pos : 0 < ∫_{0}^{π} x, sin x ^ n :=
begin
  rcases even_or_odd' n with ⟨k, (rfl | rfl)⟩;
  simp only [integral_sin_pow_even, integral_sin_pow_odd];
  refine mul_pos (by norm_num [pi_pos]) (prod_pos (λ n hn, div_pos _ _));
  norm_cast;
  linarith,
end

lemma integral_sin_pow_succ_le : ∫_{0}^{π} x, sin x ^ (n + 1) ≤ ∫_{0}^{π} x, sin x ^ n :=
let H := λ x h, pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1) in
by refine integral_mono_on pi_pos.le _ _ H; exact (continuous_sin.pow _).interval_integrable 0 π

lemma integral_sin_pow_antitone : antitone (λ n : ℕ, ∫_{0}^{π} x, sin x ^ n) :=
antitone_nat_of_succ_le integral_sin_pow_succ_le

/-! ### Integral of `cos x ^ n` -/

lemma integral_cos_pow_aux :
  ∫_{a}^{b} x, cos x ^ (n + 2) = cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
    + (n + 1) * (∫_{a}^{b} x, cos x ^ n) - (n + 1) * ∫_{a}^{b} x, cos x ^ (n + 2) :=
begin
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a,
  have h : ∀ α β γ : ℝ, (β * α * γ) * α = β * (α * α * γ) := λ α β γ, by ring,
  have hu : ∀ x ∈ _, has_deriv_at (λ y, cos y ^ (n + 1)) (-(n + 1 : ℕ) * sin x * cos x ^ n) x :=
    λ x hx, by simpa only [mul_right_comm, neg_mul, mul_neg]
      using (has_deriv_at_cos x).pow (n+1),
  have hv : ∀ x ∈ [a, b], has_deriv_at sin (cos x) x := λ x hx, has_deriv_at_sin x,
  have H := integral_mul_deriv_eq_deriv_mul hu hv _ _,
  calc  ∫_{a}^{b} x, cos x ^ (n + 2)
      = ∫_{a}^{b} x, cos x ^ (n + 1) * cos x                   : by simp only [pow_succ']
  ... = C + (n + 1) * ∫_{a}^{b} x, sin x ^ 2 * cos x ^ n       : by simp [H, h, sq, -neg_add_rev]
  ... = C + (n + 1) * ∫_{a}^{b} x, cos x ^ n - cos x ^ (n + 2) : by simp [sin_sq, sub_mul,
                                                                          ← pow_add, add_comm]
  ... = C + (n + 1) * (∫_{a}^{b} x, cos x ^ n) - (n + 1) * ∫_{a}^{b} x, cos x ^ (n + 2) :
    by rw [integral_sub, mul_sub, add_sub_assoc]; apply continuous.interval_integrable; continuity,
  all_goals { apply continuous.interval_integrable, continuity },
end

/-- The reduction formula for the integral of `cos x ^ n` for any natural `n ≥ 2`. -/
lemma integral_cos_pow :
  ∫_{a}^{b} x, cos x ^ (n + 2) = (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a) / (n + 2)
    + (n + 1) / (n + 2) * ∫_{a}^{b} x, cos x ^ n :=
begin
  have : (n : ℝ) + 2 ≠ 0 := by exact_mod_cast succ_ne_zero n.succ,
  field_simp,
  convert eq_sub_iff_add_eq.mp (integral_cos_pow_aux n),
  ring,
end

@[simp]
lemma integral_cos_sq : ∫_{a}^{b} x, cos x ^ 2 = (cos b * sin b - cos a * sin a + b - a) / 2 :=
by field_simp [integral_cos_pow, add_sub_assoc]

/-! ### Integral of `sin x ^ m * cos x ^ n` -/

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `n` is odd. -/
lemma integral_sin_pow_mul_cos_pow_odd (m n : ℕ) :
  ∫_{a}^{b} x, sin x ^ m * cos x ^ (2 * n + 1) = ∫_{sin a}^{sin b} u, u ^ m * (1 - u ^ 2) ^ n :=
have hc : continuous (λ u : ℝ, u ^ m * (1 - u ^ 2) ^ n), by continuity,
calc  ∫_{a}^{b} x, sin x ^ m * cos x ^ (2 * n + 1)
    = ∫_{a}^{b} x, sin x ^ m * (1 - sin x ^ 2) ^ n * cos x : by simp only [pow_succ', ← mul_assoc,
                                                                           pow_mul, cos_sq']
... = ∫_{sin a}^{sin b} u, u ^ m * (1 - u ^ 2) ^ n         : integral_comp_mul_deriv
                                                              (λ x hx, has_deriv_at_sin x)
                                                                continuous_on_cos hc

/-- The integral of `sin x * cos x`, given in terms of sin².
  See `integral_sin_mul_cos₂` below for the integral given in terms of cos². -/
@[simp]
lemma integral_sin_mul_cos₁ :
  ∫_{a}^{b} x, sin x * cos x = (sin b ^ 2 - sin a ^ 2) / 2 :=
by simpa using integral_sin_pow_mul_cos_pow_odd 1 0

@[simp]
lemma integral_sin_sq_mul_cos :
  ∫_{a}^{b} x, sin x ^ 2 * cos x = (sin b ^ 3 - sin a ^ 3) / 3 :=
by simpa using integral_sin_pow_mul_cos_pow_odd 2 0

@[simp]
lemma integral_cos_pow_three :
  ∫_{a}^{b} x, cos x ^ 3 = sin b - sin a - (sin b ^ 3 - sin a ^ 3) / 3 :=
by simpa using integral_sin_pow_mul_cos_pow_odd 0 1

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` is odd. -/
lemma integral_sin_pow_odd_mul_cos_pow (m n : ℕ) :
  ∫_{a}^{b} x, sin x ^ (2 * m + 1) * cos x ^ n = ∫_{cos b}^{cos a} u, u ^ n * (1 - u ^ 2) ^ m :=
have hc : continuous (λ u : ℝ, u ^ n * (1 - u ^ 2) ^ m), by continuity,
calc   ∫_{a}^{b} x, sin x ^ (2 * m + 1) * cos x ^ n
    = -∫_{b}^{a} x, sin x ^ (2 * m + 1) * cos x ^ n          : by rw integral_symm
... =  ∫_{b}^{a} x, (1 - cos x ^ 2) ^ m * -sin x * cos x ^ n : by simp [pow_succ', pow_mul, sin_sq]
... =  ∫_{b}^{a} x, cos x ^ n * (1 - cos x ^ 2) ^ m * -sin x : by { congr, ext, ring }
... =  ∫_{cos b}^{cos a} u, u ^ n * (1 - u ^ 2) ^ m          : integral_comp_mul_deriv
                                                                (λ x hx, has_deriv_at_cos x)
                                                                  continuous_on_sin.neg hc

/-- The integral of `sin x * cos x`, given in terms of cos².
See `integral_sin_mul_cos₁` above for the integral given in terms of sin². -/
lemma integral_sin_mul_cos₂  :
  ∫_{a}^{b} x, sin x * cos x = (cos a ^ 2 - cos b ^ 2) / 2 :=
by simpa using integral_sin_pow_odd_mul_cos_pow 0 1

@[simp]
lemma integral_sin_mul_cos_sq :
  ∫_{a}^{b} x, sin x * cos x ^ 2 = (cos a ^ 3 - cos b ^ 3) / 3 :=
by simpa using integral_sin_pow_odd_mul_cos_pow 0 2

@[simp]
lemma integral_sin_pow_three :
  ∫_{a}^{b} x, sin x ^ 3 = cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3 :=
by simpa using integral_sin_pow_odd_mul_cos_pow 1 0

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` and `n` are both even. -/
lemma integral_sin_pow_even_mul_cos_pow_even (m n : ℕ) :
    ∫_{a}^{b} x, sin x ^ (2 * m) * cos x ^ (2 * n)
  = ∫_{a}^{b} x, ((1 - cos (2 * x)) / 2) ^ m * ((1 + cos (2 * x)) / 2) ^ n :=
by field_simp [pow_mul, sin_sq, cos_sq, ← sub_sub, (by ring : (2:ℝ) - 1 = 1)]

@[simp]
lemma integral_sin_sq_mul_cos_sq :
  ∫_{a}^{b} x, sin x ^ 2 * cos x ^ 2 = (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 :=
begin
  convert integral_sin_pow_even_mul_cos_pow_even 1 1 using 1,
  have h1 : ∀ c : ℝ, (1 - c) / 2 * ((1 + c) / 2) = (1 - c ^ 2) / 4 := λ c, by ring,
  have h2 : continuous (λ x, cos (2 * x) ^ 2) := by continuity,
  have h3 : ∀ x, cos x * sin x = sin (2 * x) / 2, { intro, rw sin_two_mul, ring },
  have h4 : ∀ d : ℝ, 2 * (2 * d) = 4 * d := λ d, by ring,
  simp [h1, h2.interval_integrable, integral_comp_mul_left (λ x, cos x ^ 2), h3, h4],
  ring,
end
