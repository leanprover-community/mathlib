/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.special_functions.gamma.basic
import analysis.special_functions.polar_coord
import analysis.convex.complex
import analysis.complex.cauchy_integral
import analysis.fourier.poisson_summation

/-!
# Gaussian integral

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove various versions of the formula for the Gaussian integral:
* `integral_gaussian`: for real `b` we have `∫ x:ℝ, exp (-b * x^2) = sqrt (π / b)`.
* `integral_gaussian_complex`: for complex `b` with `0 < re b` we have
  `∫ x:ℝ, exp (-b * x^2) = (π / b) ^ (1 / 2)`.
* `integral_gaussian_Ioi` and `integral_gaussian_complex_Ioi`: variants for integrals over `Ioi 0`.
* `complex.Gamma_one_half_eq`: the formula `Γ (1 / 2) = √π`.

We also prove, more generally, that the Fourier transform of the Gaussian is another Gaussian:

* `integral_cexp_neg_mul_sq_add_const`: for all complex `b` and `c` with `0 < re b` we have
  `∫ (x : ℝ), exp (-b * (x + c) ^ 2) = (π / b) ^ (1 / 2)`.
* `fourier_transform_gaussian`: for all complex `b` and `t` with `0 < re b`, we have
  `∫ x:ℝ, exp (I * t * x) * exp (-b * x^2) = (π / b) ^ (1 / 2) * exp (-t ^ 2 / (4 * b))`.
* `fourier_transform_gaussian_pi`: a variant with `b` and `t` scaled to give a more symmetric
  statement, and formulated in terms of the Fourier transform operator `𝓕`.

As an application, in `real.tsum_exp_neg_mul_int_sq` and `complex.tsum_exp_neg_mul_int_sq`, we use
Poisson summation to prove the identity
`∑' (n : ℤ), exp (-π * a * n ^ 2) = 1 / a ^ (1 / 2) * ∑' (n : ℤ), exp (-π / a * n ^ 2)`
for positive real `a`, or complex `a` with positive real part. (See also
`number_theory.modular_forms.jacobi_theta`.)
-/

noncomputable theory

open real set measure_theory filter asymptotics
open_locale real topology fourier_transform

open complex (hiding exp continuous_exp abs_of_nonneg sq_abs)

notation `cexp` := complex.exp
notation `rexp` := real.exp

lemma exp_neg_mul_sq_is_o_exp_neg {b : ℝ} (hb : 0 < b) :
  (λ x:ℝ, exp (-b * x^2)) =o[at_top] (λ x:ℝ, exp (-x)) :=
begin
  have A : (λ (x : ℝ), -x - -b * x ^ 2) = (λ x, x * (b * x + (- 1))), by { ext x, ring },
  rw [is_o_exp_comp_exp_comp, A],
  apply tendsto.at_top_mul_at_top tendsto_id,
  apply tendsto_at_top_add_const_right at_top (-1 : ℝ),
  exact tendsto.const_mul_at_top hb tendsto_id,
end

lemma rpow_mul_exp_neg_mul_sq_is_o_exp_neg {b : ℝ} (hb : 0 < b) (s : ℝ) :
  (λ x:ℝ, x ^ s * exp (-b * x^2)) =o[at_top] (λ x:ℝ, exp (-(1/2) * x)) :=
begin
  apply ((is_O_refl (λ x:ℝ, x ^ s) at_top).mul_is_o (exp_neg_mul_sq_is_o_exp_neg hb)).trans,
  convert Gamma_integrand_is_o s,
  simp_rw [mul_comm],
end

lemma integrable_on_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
  integrable_on (λ x:ℝ, x ^ s * exp (-b * x^2)) (Ioi 0) :=
begin
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrable_on_union],
  split,
  { rw [←integrable_on_Icc_iff_integrable_on_Ioc],
    refine integrable_on.mul_continuous_on _ _ is_compact_Icc,
    { refine (interval_integrable_iff_integrable_Icc_of_le zero_le_one).mp _,
      exact interval_integral.interval_integrable_rpow' hs },
    { exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).continuous_on } },
  { have B : (0 : ℝ) < 1/2, by norm_num,
    apply integrable_of_is_O_exp_neg B _ (is_o.is_O (rpow_mul_exp_neg_mul_sq_is_o_exp_neg hb _)),
    assume x hx,
    have N : x ≠ 0, { refine (zero_lt_one.trans_le _).ne', exact hx },
    apply ((continuous_at_rpow_const _ _ (or.inl N)).mul _).continuous_within_at,
    exact (continuous_exp.comp (continuous_const.mul (continuous_pow 2))).continuous_at },
end

lemma integrable_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
  integrable (λ x:ℝ, x ^ s * exp (-b * x^2)) :=
begin
  rw [← integrable_on_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrable_on_union,
      integrable_on_Ici_iff_integrable_on_Ioi],
  refine ⟨_, integrable_on_rpow_mul_exp_neg_mul_sq hb hs⟩,
  rw ← (measure.measure_preserving_neg (volume : measure ℝ)).integrable_on_comp_preimage
    ((homeomorph.neg ℝ).to_measurable_equiv.measurable_embedding),
  simp only [function.comp, neg_sq, neg_preimage, preimage_neg_Iio, neg_neg, neg_zero],
  apply integrable.mono' (integrable_on_rpow_mul_exp_neg_mul_sq hb hs),
  { apply measurable.ae_strongly_measurable,
    exact (measurable_id'.neg.pow measurable_const).mul
      ((measurable_id'.pow measurable_const).const_mul (-b)).exp },
  { have : measurable_set (Ioi (0 : ℝ)) := measurable_set_Ioi,
    filter_upwards [ae_restrict_mem this] with x hx,
    have h'x : 0 ≤ x := le_of_lt hx,
    rw [real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le],
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le,
    simpa [abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s }
end

lemma integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
  integrable (λ x:ℝ, exp (-b * x^2)) :=
by simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 0)

lemma integrable_on_Ioi_exp_neg_mul_sq_iff {b : ℝ} :
  integrable_on (λ x:ℝ, exp (-b * x^2)) (Ioi 0) ↔ 0 < b :=
begin
  refine ⟨λ h, _, λ h, (integrable_exp_neg_mul_sq h).integrable_on⟩,
  by_contra' hb,
  have : ∫⁻ x:ℝ in Ioi 0, 1 ≤ ∫⁻ x:ℝ in Ioi 0, ‖exp (-b * x^2)‖₊,
  { apply lintegral_mono (λ x, _),
    simp only [neg_mul, ennreal.one_le_coe_iff, ← to_nnreal_one, to_nnreal_le_iff_le_coe,
      real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, right.nonneg_neg_iff],
    exact mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg _) },
  simpa using this.trans_lt h.2,
end

lemma integrable_exp_neg_mul_sq_iff {b : ℝ} : integrable (λ x:ℝ, exp (-b * x^2)) ↔ 0 < b :=
⟨λ h, integrable_on_Ioi_exp_neg_mul_sq_iff.mp h.integrable_on, integrable_exp_neg_mul_sq⟩

lemma integrable_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) : integrable (λ x:ℝ, x * exp (-b * x^2)) :=
by simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 1)

lemma norm_cexp_neg_mul_sq (b : ℂ) (x : ℝ) : ‖complex.exp (-b * x^2)‖ = exp (-b.re * x^2) :=
by rw [complex.norm_eq_abs, complex.abs_exp, ←of_real_pow, mul_comm (-b) _, of_real_mul_re,
  neg_re, mul_comm]

lemma integrable_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) : integrable (λ x:ℝ, cexp (-b * x^2)) :=
begin
  refine ⟨(complex.continuous_exp.comp
    (continuous_const.mul (continuous_of_real.pow 2))).ae_strongly_measurable, _⟩,
  rw ←has_finite_integral_norm_iff,
  simp_rw norm_cexp_neg_mul_sq,
  exact (integrable_exp_neg_mul_sq hb).2,
end

lemma integrable_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
  integrable (λ x:ℝ, ↑x * cexp (-b * x^2)) :=
begin
  refine ⟨(continuous_of_real.mul (complex.continuous_exp.comp _)).ae_strongly_measurable, _⟩,
  { exact continuous_const.mul (continuous_of_real.pow 2) },
  have := (integrable_mul_exp_neg_mul_sq hb).has_finite_integral,
  rw ←has_finite_integral_norm_iff at this ⊢,
  convert this,
  ext1 x,
  rw [norm_mul, norm_mul, norm_cexp_neg_mul_sq b, complex.norm_eq_abs, abs_of_real,
    real.norm_eq_abs, norm_of_nonneg (exp_pos _).le],
end

lemma integral_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
  ∫ r:ℝ in Ioi 0, (r : ℂ) * cexp (-b * r ^ 2) = (2 * b)⁻¹ :=
begin
  have hb' : b ≠ 0 := by { contrapose! hb, rw [hb, zero_re], },
  have A : ∀ x:ℂ, has_deriv_at (λ x, - (2 * b)⁻¹ * cexp (-b * x^2)) (x * cexp (- b * x^2)) x,
  { intro x,
    convert (((has_deriv_at_pow 2 x)).const_mul (-b)).cexp.const_mul (- (2 * b)⁻¹) using 1,
    field_simp [hb'],
    ring },
  have B : tendsto (λ (y : ℝ), -(2 * b)⁻¹ * cexp (-b * ↑y ^ 2)) at_top (𝓝 (-(2 * b)⁻¹ * 0)),
  { refine (tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.mpr _)),
    simp_rw norm_cexp_neg_mul_sq b,
    exact tendsto_exp_at_bot.comp
      (tendsto.neg_const_mul_at_top (neg_lt_zero.2 hb) (tendsto_pow_at_top two_ne_zero)) },
  convert integral_Ioi_of_has_deriv_at_of_tendsto' (λ x hx, (A ↑x).comp_of_real)
    (integrable_mul_cexp_neg_mul_sq hb).integrable_on B,
  simp only [mul_zero, of_real_zero, zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero,
    not_false_iff, complex.exp_zero, mul_one, sub_neg_eq_add, zero_add],
end

/-- The *square* of the Gaussian integral `∫ x:ℝ, exp (-b * x^2)` is equal to `π / b`. -/
lemma integral_gaussian_sq_complex {b : ℂ} (hb : 0 < b.re) :
  (∫ x:ℝ, cexp (-b * x^2)) ^ 2 = π / b :=
begin
  /- We compute `(∫ exp (-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change
  of coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
  `integral_mul_cexp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
  (∫ x:ℝ, cexp (-b * (x:ℂ)^2)) ^ 2
      = ∫ p : ℝ × ℝ, cexp (-b * ((p.1) : ℂ) ^ 2) * cexp (-b * ((p.2) : ℂ) ^ 2) :
    by { rw [pow_two, ← integral_prod_mul], refl }
  ... = ∫ p : ℝ × ℝ, cexp (- b * (p.1 ^ 2 + p.2 ^ 2)) :
    by { congr, ext1 p, rw [← complex.exp_add, mul_add], }
  ... = ∫ p in polar_coord.target, (p.1) • cexp (- b * ((p.1 * cos p.2) ^ 2 + (p.1 * sin p.2)^2)) :
    begin
      rw ← integral_comp_polar_coord_symm,
      simp only [polar_coord_symm_apply, of_real_mul, of_real_cos, of_real_sin],
    end
  ... = (∫ r in Ioi (0 : ℝ), r * cexp (-b * r^2)) * (∫ θ in Ioo (-π) π, 1) :
    begin
      rw ← set_integral_prod_mul,
      congr' with p : 1,
      rw mul_one,
      congr,
      conv_rhs { rw [← one_mul ((p.1 : ℂ)^2), ← sin_sq_add_cos_sq (p.2 : ℂ)], },
      ring_exp,
    end
  ... = ↑π / b :
    begin
      have : 0 ≤ π + π, by linarith [real.pi_pos],
      simp only [integral_const, measure.restrict_apply', measurable_set_Ioo, univ_inter,
        volume_Ioo, sub_neg_eq_add, ennreal.to_real_of_real, this],
      rw [←two_mul, real_smul, mul_one, of_real_mul, of_real_bit0, of_real_one,
        integral_mul_cexp_neg_mul_sq hb],
      field_simp [(by { contrapose! hb, rw [hb, zero_re] } : b ≠ 0)],
      ring,
    end
end

theorem integral_gaussian (b : ℝ) : ∫ x, exp (-b * x^2) = sqrt (π / b) :=
begin
  /- First we deal with the crazy case where `b ≤ 0`: then both sides vanish. -/
  rcases le_or_lt b 0 with hb|hb,
  { rw [integral_undef, sqrt_eq_zero_of_nonpos],
    { exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb },
    { simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb } },
  /- Assume now `b > 0`. Then both sides are non-negative and their squares agree. -/
  refine (sq_eq_sq _ (sqrt_nonneg _)).1 _,
  { exact integral_nonneg (λ x, (exp_pos _).le) },
  rw [←of_real_inj, of_real_pow, ←integral_of_real, sq_sqrt (div_pos pi_pos hb).le, of_real_div],
  convert integral_gaussian_sq_complex (by rwa of_real_re : 0 < (b:ℂ).re),
  ext1 x,
  rw [of_real_exp, of_real_mul, of_real_pow, of_real_neg],
end

lemma continuous_at_gaussian_integral (b : ℂ) (hb : 0 < re b) :
  continuous_at (λ c:ℂ, ∫ x:ℝ, cexp (-c * x^2)) b :=
begin
  let f : ℂ → ℝ → ℂ := λ (c : ℂ) (x : ℝ), cexp (-c * x ^ 2),
  obtain ⟨d, hd, hd'⟩ := exists_between hb,
  have f_meas : ∀ (c:ℂ), ae_strongly_measurable (f c) volume := λ c, by
  { apply continuous.ae_strongly_measurable,
    exact complex.continuous_exp.comp (continuous_const.mul (continuous_of_real.pow 2)) },
  have f_int : integrable (f b) volume,
  { simp_rw [←integrable_norm_iff (f_meas b), norm_cexp_neg_mul_sq b],
    exact integrable_exp_neg_mul_sq hb, },
  have f_cts : ∀ (x : ℝ), continuous_at (λ c, f c x) b :=
    λ x, (complex.continuous_exp.comp (continuous_id'.neg.mul continuous_const)).continuous_at,
  have f_le_bd : ∀ᶠ (c : ℂ) in 𝓝 b, ∀ᵐ (x : ℝ), ‖f c x‖ ≤ exp (-d * x ^ 2),
  { refine eventually_of_mem ((continuous_re.is_open_preimage _ is_open_Ioi).mem_nhds hd') _,
    refine λ c hc, ae_of_all _ (λ x, _),
    rw [norm_cexp_neg_mul_sq, exp_le_exp],
    exact mul_le_mul_of_nonneg_right (neg_le_neg (le_of_lt hc)) (sq_nonneg _) },
  exact continuous_at_of_dominated (eventually_of_forall f_meas) f_le_bd
    (integrable_exp_neg_mul_sq hd) (ae_of_all _ f_cts),
end

theorem integral_gaussian_complex {b : ℂ} (hb : 0 < re b) :
  ∫ x:ℝ, cexp (-b * x^2) = (π / b) ^ (1 / 2 : ℂ) :=
begin
  have nv : ∀ {b : ℂ}, (0 < re b) → (b ≠ 0),
  { intros b hb, contrapose! hb, rw hb, simp },
  refine (convex_halfspace_re_gt 0).is_preconnected.eq_of_sq_eq
    _ _ (λ c hc, _) (λ c hc, _) (by simp : 0 < re (1 : ℂ)) _ hb,
  { -- integral is continuous
    exact continuous_at.continuous_on continuous_at_gaussian_integral, },
  { -- `(π / b) ^ (1 / 2 : ℂ)` is continuous
    refine continuous_at.continuous_on (λ b hb, (continuous_at_cpow_const (or.inl _)).comp
      (continuous_at_const.div continuous_at_id (nv hb))),
    rw [div_re, of_real_im, of_real_re, zero_mul, zero_div, add_zero],
    exact div_pos (mul_pos pi_pos hb) (norm_sq_pos.mpr (nv hb)), },
  { -- squares of both sides agree
    dsimp only [pi.pow_apply],
    rw [integral_gaussian_sq_complex hc, sq],
    conv_lhs { rw ←cpow_one (↑π / c)},
    rw ← cpow_add _ _ (div_ne_zero (of_real_ne_zero.mpr pi_ne_zero) (nv hc)),
    norm_num },
  { -- RHS doesn't vanish
    rw [ne.def, cpow_eq_zero_iff, not_and_distrib],
    exact or.inl (div_ne_zero (of_real_ne_zero.mpr pi_ne_zero) (nv hc)) },
  { -- equality at 1
    have : ∀ (x : ℝ), cexp (-1 * x ^ 2) = exp (-1 * x ^ 2),
    { intro x,
      simp only [of_real_exp, neg_mul, one_mul, of_real_neg, of_real_pow] },
    simp_rw [this, integral_of_real],
    conv_rhs {  congr, rw [←of_real_one, ←of_real_div], skip,
      rw [←of_real_one, ←of_real_bit0, ←of_real_div]  },
    rw [←of_real_cpow, of_real_inj],
    convert integral_gaussian (1 : ℝ),
    { rwa [sqrt_eq_rpow] },
    { rw [div_one], exact pi_pos.le } },
end

/- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for complex `b`. -/
lemma integral_gaussian_complex_Ioi {b : ℂ} (hb : 0 < re b) :
  ∫ x:ℝ in Ioi 0, cexp (-b * x^2) = (π / b) ^ (1 / 2 : ℂ) / 2 :=
begin
  have full_integral := integral_gaussian_complex hb,
  have : measurable_set (Ioi (0:ℝ)) := measurable_set_Ioi,
  rw [←integral_add_compl this (integrable_cexp_neg_mul_sq hb), compl_Ioi] at full_integral,
  suffices : ∫ x:ℝ in Iic 0, cexp (-b * x^2) = ∫ x:ℝ in Ioi 0, cexp (-b * x^2),
  { rw [this, ←mul_two] at full_integral,
    rwa eq_div_iff, exact two_ne_zero },
  have : ∀ (c : ℝ), ∫_{0}^{c} x, cexp (-b * x^2) = ∫_{-c}^{0} x, cexp (-b * x^2),
  { intro c,
    have := @interval_integral.integral_comp_sub_left _ _ _ _ 0 c (λ x, cexp (-b * x^2)) 0,
    simpa [zero_sub, neg_sq, neg_zero] using this },
  have t1 := interval_integral_tendsto_integral_Ioi _
     ((integrable_cexp_neg_mul_sq hb).integrable_on) tendsto_id,
  have t2 : tendsto (λ c:ℝ, ∫_{0}^{c} x:ℝ,
    cexp (-b * x^2)) at_top (𝓝 ∫ x:ℝ in Iic 0, cexp (-b * x^2)),
  { simp_rw this,
    refine interval_integral_tendsto_integral_Iic _ _ tendsto_neg_at_top_at_bot,
    apply (integrable_cexp_neg_mul_sq hb).integrable_on },
  exact tendsto_nhds_unique t2 t1,
end

/- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for real `b`. -/
lemma integral_gaussian_Ioi (b : ℝ) : ∫ x in Ioi 0, exp (-b * x^2) = sqrt (π / b) / 2 :=
begin
  rcases le_or_lt b 0 with hb|hb,
  { rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div],
    exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb,
    rwa [←integrable_on, integrable_on_Ioi_exp_neg_mul_sq_iff, not_lt] },
  rw [←of_real_inj, ←integral_of_real],
  convert integral_gaussian_complex_Ioi (by rwa of_real_re : 0 < (b:ℂ).re),
  { ext1 x, simp, },
  { rw [sqrt_eq_rpow, ←of_real_div, of_real_div, of_real_cpow],
    norm_num,
    exact (div_pos pi_pos hb).le, }
end

/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
lemma real.Gamma_one_half_eq : real.Gamma (1 / 2) = sqrt π :=
begin
  rw [Gamma_eq_integral one_half_pos, ←integral_comp_rpow_Ioi_of_pos zero_lt_two],
  convert congr_arg (λ x:ℝ, 2 * x) (integral_gaussian_Ioi 1),
  { rw ←integral_mul_left,
    refine set_integral_congr measurable_set_Ioi (λ x hx, _),
    dsimp only,
    have : (x ^ (2:ℝ)) ^ (1 / (2:ℝ) - 1) = x⁻¹,
    { rw ←rpow_mul (le_of_lt hx),
      norm_num,
      rw [rpow_neg (le_of_lt hx), rpow_one] },
    rw [smul_eq_mul, this],
    field_simp [(ne_of_lt hx).symm],
    norm_num, ring },
  { rw [div_one, ←mul_div_assoc, mul_comm, mul_div_cancel _ (two_ne_zero' ℝ)], }
end

/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
lemma complex.Gamma_one_half_eq : complex.Gamma (1 / 2) = π ^ (1 / 2 : ℂ) :=
begin
  convert congr_arg coe real.Gamma_one_half_eq,
  { simpa only [one_div, of_real_inv, of_real_bit0] using Gamma_of_real (1 / 2)},
  { rw [sqrt_eq_rpow, of_real_cpow pi_pos.le, of_real_div, of_real_bit0, of_real_one] }
end

namespace gaussian_fourier
/-! ## Fourier transform of the Gaussian integral
-/
open interval_integral
open_locale real

variables {b : ℂ}

/-- The integral of the Gaussian function over the vertical edges of a rectangle
with vertices at `(±T, 0)` and `(±T, c)`.  -/
def vertical_integral (b : ℂ) (c T : ℝ) : ℂ :=
∫_{0}^{c} y, I * (cexp (-b * (T + y * I) ^ 2) - cexp (-b * (T - y * I) ^ 2))

/-- Explicit formula for the norm of the Gaussian function along the vertical
edges. -/
lemma norm_cexp_neg_mul_sq_add_mul_I (b : ℂ) (c T : ℝ) :
  ‖cexp (-b * (T + c * I) ^ 2)‖ = exp (-(b.re * T ^ 2 - 2 * b.im * c * T - b.re * c ^ 2)) :=
begin
  rw [complex.norm_eq_abs, complex.abs_exp, neg_mul, neg_re, ←re_add_im b],
  simp only [sq, re_add_im, mul_re, mul_im, add_re, add_im, of_real_re, of_real_im, I_re, I_im],
  ring_nf,
end

lemma norm_cexp_neg_mul_sq_add_mul_I' (hb : b.re ≠ 0) (c T : ℝ) :
  ‖cexp (-b * (T + c * I) ^ 2)‖ =
  exp (-(b.re * (T - b.im * c / b.re) ^ 2 - c ^ 2 * (b.im ^ 2 / b.re  + b.re))) :=
begin
  have : (b.re * T ^ 2 - 2 * b.im * c * T - b.re * c ^ 2) =
  b.re * (T - b.im * c / b.re) ^ 2 - c ^ 2 * (b.im ^ 2 / b.re  + b.re),
  { field_simp, ring },
  rw [norm_cexp_neg_mul_sq_add_mul_I, this],
end

lemma vertical_integral_norm_le (hb : 0 < b.re) (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
  ‖vertical_integral b c T‖
    ≤ 2 * |c| * exp (-(b.re * T ^ 2 - 2 * |b.im| * |c| * T - b.re * c ^ 2)) :=
begin
  -- first get uniform bound for integrand
  have vert_norm_bound : ∀ {T : ℝ}, 0 ≤ T → ∀ {c y : ℝ}, |y| ≤ |c| →
    ‖cexp (-b * (T + y * I) ^ 2)‖ ≤ exp (-(b.re * T ^ 2 - 2 * |b.im| * |c| * T - b.re * c ^ 2)),
  { intros T hT c y hy,
    rw [norm_cexp_neg_mul_sq_add_mul_I b, exp_le_exp, neg_le_neg_iff],
    refine sub_le_sub (sub_le_sub (le_refl _) (mul_le_mul_of_nonneg_right _ hT)) _,
    { conv_lhs {rw mul_assoc}, conv_rhs {rw mul_assoc},
      refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans _) zero_le_two,
      rw abs_mul,
      exact mul_le_mul_of_nonneg_left hy (abs_nonneg _), },
    { refine mul_le_mul_of_nonneg_left _ hb.le,
      rwa sq_le_sq, } },
  -- now main proof
  refine (interval_integral.norm_integral_le_of_norm_le_const _).trans _,
  swap 3,
  { rw sub_zero,
    conv_lhs { rw mul_comm },
    conv_rhs { conv { congr, rw mul_comm }, rw mul_assoc } },
  { intros y hy,
    have absy : |y| ≤ |c|,
    { rcases le_or_lt 0 c,
      { rw uIoc_of_le h at hy,
        rw [abs_of_nonneg h, abs_of_pos hy.1],
        exact hy.2, },
      { rw uIoc_of_lt h at hy,
        rw [abs_of_neg h, abs_of_nonpos hy.2, neg_le_neg_iff],
        exact hy.1.le } },
    rw [norm_mul, complex.norm_eq_abs, abs_I, one_mul, two_mul],
    refine (norm_sub_le _ _).trans (add_le_add (vert_norm_bound hT absy) _),
    rw ←abs_neg y at absy,
    simpa only [neg_mul, of_real_neg] using vert_norm_bound hT absy },
end

lemma tendsto_vertical_integral (hb : 0 < b.re) (c : ℝ) :
  tendsto (vertical_integral b c) at_top (𝓝 0) :=
begin
  -- complete proof using squeeze theorem:
  rw tendsto_zero_iff_norm_tendsto_zero,
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds _
    (eventually_of_forall (λ _, norm_nonneg _))
    ((eventually_ge_at_top (0:ℝ)).mp (eventually_of_forall
      (λ T hT, vertical_integral_norm_le hb c hT))),
  rw (by ring : 0 = 2 * |c| * 0),
  refine (tendsto_exp_at_bot.comp (tendsto_neg_at_top_at_bot.comp _)).const_mul _ ,
  apply tendsto_at_top_add_const_right,
  simp_rw [sq, ←mul_assoc, ←sub_mul],
  refine tendsto.at_top_mul_at_top (tendsto_at_top_add_const_right _ _ _) tendsto_id,
  exact (tendsto_const_mul_at_top_of_pos hb).mpr tendsto_id,
end

lemma integrable_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : ℝ) :
  integrable (λ (x : ℝ), cexp (-b * (x + c * I) ^ 2)) :=
begin
  refine ⟨(complex.continuous_exp.comp (continuous_const.mul ((continuous_of_real.add
    continuous_const).pow 2))).ae_strongly_measurable, _⟩,
  rw ←has_finite_integral_norm_iff,
  simp_rw [norm_cexp_neg_mul_sq_add_mul_I' hb.ne', neg_sub _ (c ^ 2 * _),
    sub_eq_add_neg _ (b.re * _), real.exp_add],
  suffices : integrable (λ (x : ℝ), exp (-(b.re * x ^ 2))),
  { exact (integrable.comp_sub_right this (b.im * c / b.re)).has_finite_integral.const_mul _, },
  simp_rw ←neg_mul,
  apply integrable_exp_neg_mul_sq hb,
end

lemma integral_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : ℝ) :
  ∫ (x : ℝ), cexp (-b * (x + c * I) ^ 2) = (π / b) ^ (1 / 2 : ℂ) :=
begin
  refine tendsto_nhds_unique (interval_integral_tendsto_integral
    (integrable_cexp_neg_mul_sq_add_real_mul_I hb c) tendsto_neg_at_top_at_bot tendsto_id) _,
  set I₁ := (λ T, ∫_{-T}^{T} x, cexp (-b * (x + c * I) ^ 2)) with HI₁,
  let I₂ := λ (T : ℝ), ∫_{-T}^{T} x, cexp (-b * x ^ 2),
  let I₄ := λ (T : ℝ), ∫_{0}^{c} y, cexp (-b * (T + y * I) ^ 2),
  let I₅ := λ (T : ℝ), ∫_{0}^{c} y, cexp (-b * (-T + y * I) ^ 2),
  have C : ∀ (T : ℝ), I₂ T - I₁ T + I * I₄ T - I * I₅ T = 0,
  { assume T,
    have := integral_boundary_rect_eq_zero_of_differentiable_on
    (λ z, cexp (-b * z ^ 2)) (-T) (T + c * I)
    (by { refine differentiable.differentiable_on (differentiable.const_mul _ _).cexp,
    exact differentiable_pow 2, }),
    simpa only [neg_im, of_real_im, neg_zero, of_real_zero, zero_mul, add_zero, neg_re, of_real_re,
      add_re, mul_re, I_re, mul_zero, I_im, tsub_zero, add_im, mul_im, mul_one, zero_add,
      algebra.id.smul_eq_mul, of_real_neg] using this },
  simp_rw [id.def, ←HI₁],
  have : I₁ = λ (T : ℝ), I₂ T + vertical_integral b c T,
  { ext1 T,
    specialize C T,
    rw sub_eq_zero at C,
    unfold vertical_integral,
    rw [integral_const_mul, interval_integral.integral_sub],
    { simp_rw (λ a b, by { rw sq, ring_nf } : ∀ (a b : ℂ), (a - b * I)^2 = (- a + b * I)^2),
      change I₁ T = I₂ T + I * (I₄ T - I₅ T),
      rw [mul_sub, ←C],
      abel },
    all_goals { apply continuous.interval_integrable, continuity }, },
  rw [this, ←add_zero ((π / b : ℂ) ^ (1 / 2 : ℂ)), ←integral_gaussian_complex hb],
  refine tendsto.add _ (tendsto_vertical_integral hb c),
  exact interval_integral_tendsto_integral (integrable_cexp_neg_mul_sq hb)
    tendsto_neg_at_top_at_bot tendsto_id,
end

lemma _root_.integral_cexp_neg_mul_sq_add_const (hb : 0 < b.re) (c : ℂ) :
  ∫ (x : ℝ), cexp (-b * (x + c) ^ 2) = (π / b) ^ (1 / 2 : ℂ) :=
begin
  rw ←re_add_im c,
  simp_rw [←add_assoc, ←of_real_add],
  rw integral_add_right_eq_self (λ(x : ℝ), cexp (-b * (↑x + ↑(c.im) * I) ^ 2)),
  { apply integral_cexp_neg_mul_sq_add_real_mul_I hb },
  { apply_instance },
end

lemma _root_.fourier_transform_gaussian (hb : 0 < b.re) (t : ℂ) :
  ∫ (x : ℝ), cexp (I * t * x) * cexp (-b * x ^ 2) = cexp (-t^2 / (4 * b)) * (π / b) ^ (1 / 2 : ℂ) :=
begin
  have : b ≠ 0,
  { contrapose! hb, rw [hb, zero_re] },
  simp_rw [←complex.exp_add],
  have : ∀ (x : ℂ), I * t * x + (-b * x ^ 2) = -t ^ 2 / (4 * b) + -b * (x + (-I * t / 2 / b)) ^ 2,
  { intro x,
    ring_nf SOP,
    rw I_sq,
    field_simp, ring },
  simp_rw [this, complex.exp_add, integral_mul_left, integral_cexp_neg_mul_sq_add_const hb]
end

lemma _root_.fourier_transform_gaussian_pi (hb : 0 < b.re) :
  𝓕 (λ x : ℝ, cexp (-π * b * x ^ 2)) = λ t : ℝ, 1 / b ^ (1 / 2 : ℂ) * cexp (-π / b * t ^ 2) :=
begin
  ext1 t,
  simp_rw [fourier_integral_eq_integral_exp_smul, smul_eq_mul],
  have h1 : 0 < re (π * b) := by { rw of_real_mul_re, exact mul_pos pi_pos hb },
  have h2 : b ≠ 0 := by { contrapose! hb, rw [hb, zero_re], },
  convert _root_.fourier_transform_gaussian h1 (-2 * π * t) using 1,
  { congr' 1 with x:1,
    congr' 2,
    all_goals { push_cast, ring } },
  { conv_lhs { rw mul_comm },
    congr' 2,
    { field_simp [of_real_ne_zero.mpr pi_ne_zero], ring, },
    { rw [←div_div, div_self (of_real_ne_zero.mpr pi_ne_zero), one_div, one_div b, inv_cpow],
      rw [ne.def, arg_eq_pi_iff, not_and_distrib, not_lt],
      exact or.inl hb.le } },
end

end gaussian_fourier

section gaussian_poisson
/-! ## Poisson summation applied to the Gaussian -/

variables {E : Type*} [normed_add_comm_group E]

lemma tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact {a : ℝ} (ha : 0 < a) (s : ℝ) :
  tendsto (λ x : ℝ, |x| ^ s * rexp (-a * x ^ 2)) (cocompact ℝ) (𝓝 0) :=
begin
  conv in (rexp _) { rw ←sq_abs },
  rw [cocompact_eq, ←comap_abs_at_top,
    @tendsto_comap'_iff _ _ _ (λ y, y ^ s * rexp (-a * y ^ 2)) _ _ _
    (mem_at_top_sets.mpr ⟨0, λ b hb, ⟨b, abs_of_nonneg hb⟩⟩)],
  exact (rpow_mul_exp_neg_mul_sq_is_o_exp_neg ha s).tendsto_zero_of_tendsto
    (tendsto_exp_at_bot.comp $ tendsto_id.neg_const_mul_at_top (neg_lt_zero.mpr one_half_pos)),
end

lemma is_o_exp_neg_mul_sq_cocompact {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
  (λ x : ℝ, complex.exp (-a * x ^ 2)) =o[cocompact ℝ] (λ x : ℝ, |x| ^ s) :=
begin
  rw ←is_o_norm_left,
  simp_rw norm_cexp_neg_mul_sq,
  apply is_o_of_tendsto',
  { refine eventually.filter_mono cocompact_le_cofinite _,
    refine (eventually_cofinite_ne 0).mp (eventually_of_forall (λ x hx h, _)),
    exact ((rpow_pos_of_pos (abs_pos.mpr hx) _).ne' h).elim },
  { refine tendsto.congr' (eventually.filter_mono cocompact_le_cofinite _)
      (tendsto_zero_iff_norm_tendsto_zero.mp $
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha (-s)),
    refine (eventually_cofinite_ne 0).mp (eventually_of_forall (λ x hx, _)),
    rw [norm_mul, norm_of_nonneg (rpow_nonneg_of_nonneg (abs_nonneg _) _), mul_comm,
      rpow_neg (abs_nonneg x), div_eq_mul_inv, norm_of_nonneg (exp_pos _).le] },
end

lemma complex.tsum_exp_neg_mul_int_sq {a : ℂ} (ha : 0 < a.re) :
  ∑' (n : ℤ), cexp (-π * a * n ^ 2) = 1 / a ^ (1 / 2 : ℂ) * ∑' (n : ℤ), cexp (-π / a * n ^ 2) :=
begin
  let f := λ x : ℝ, cexp (-π * a * x ^ 2),
  have h1 : 0 < (↑π * a).re,
  { rw [of_real_mul_re],
    exact mul_pos pi_pos ha },
  have h2 : 0 < (↑π / a).re,
  { rw [div_eq_mul_inv, of_real_mul_re, inv_re],
    refine mul_pos pi_pos (div_pos ha $ norm_sq_pos.mpr _),
    contrapose! ha,
    rw [ha, zero_re] },
  have f_bd : f =O[cocompact ℝ] (λ x, |x| ^ (-2 : ℝ)),
  { convert (is_o_exp_neg_mul_sq_cocompact h1 _).is_O,
    ext1 x,
    dsimp only [f],
    congr' 1,
    ring },
  have Ff_bd : 𝓕 f =O[cocompact ℝ] (λ x, |x| ^ (-2 : ℝ)),
  { rw fourier_transform_gaussian_pi ha,
    convert (is_o_exp_neg_mul_sq_cocompact h2 _).is_O.const_mul_left _,
    ext1 x,
    congr' 1,
    ring_nf },
  simpa only [fourier_transform_gaussian_pi ha, tsum_mul_left] using
    real.tsum_eq_tsum_fourier_integral_of_rpow_decay
    (complex.continuous_exp.comp (continuous_const.mul (continuous_of_real.pow 2)) : continuous f)
    one_lt_two f_bd Ff_bd
end

lemma real.tsum_exp_neg_mul_int_sq {a : ℝ} (ha : 0 < a) :
  ∑' (n : ℤ), exp (-π * a * n ^ 2) = 1 / a ^ (1 / 2 : ℝ) * ∑' (n : ℤ), exp (-π / a * n ^ 2) :=
by simpa only [←of_real_inj, of_real_mul, of_real_tsum, of_real_exp, of_real_div, of_real_pow,
  of_real_int_cast, of_real_neg, of_real_cpow ha.le, of_real_bit0, of_real_one] using
  complex.tsum_exp_neg_mul_int_sq (by rwa [of_real_re] : 0 < (a : ℂ).re)

end gaussian_poisson
