/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.fourier.add_circle
import analysis.fourier.fourier_transform
import analysis.p_series
import analysis.schwartz_space
import measure_theory.measure.lebesgue.integral

/-!
# Poisson's summation formula

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove Poisson's summation formula `∑ (n : ℤ), f n = ∑ (n : ℤ), 𝓕 f n`, where `𝓕 f` is the
Fourier transform of `f`, under the following hypotheses:
* `f` is a continuous function `ℝ → ℂ`.
* The sum `∑ (n : ℤ), 𝓕 f n` is convergent.
* For all compacts `K ⊂ ℝ`, the sum `∑ (n : ℤ), sup { ‖f(x + n)‖ | x ∈ K }` is convergent.
See `real.tsum_eq_tsum_fourier_integral` for this formulation.

These hypotheses are potentially a little awkward to apply, so we also provide the less general but
easier-to-use result `real.tsum_eq_tsum_fourier_integral_of_rpow_decay`, in which we assume `f` and
`𝓕 f` both decay as `|x| ^ (-b)` for some `b > 1`, and the even more specific result
`schwartz_map.tsum_eq_tsum_fourier_integral`, where we assume that both `f` and `𝓕 f` are Schwartz
functions.

## TODO

At the moment `schwartz_map.tsum_eq_tsum_fourier_integral` requires separate proofs that both `f`
and `𝓕 f` are Schwartz functions. In fact, `𝓕 f` is automatically Schwartz if `f` is; and once
we have this lemma in the library, we should adjust the hypotheses here accordingly.
-/

noncomputable theory

open function (hiding comp_apply) complex (hiding abs_of_nonneg) real set (hiding restrict_apply)
  topological_space filter measure_theory asymptotics

open_locale real big_operators filter fourier_transform

local attribute [instance] real.fact_zero_lt_one

open continuous_map

/-- The key lemma for Poisson summation: the `m`-th Fourier coefficient of the periodic function
`∑' n : ℤ, f (x + n)` is the value at `m` of the Fourier transform of `f`. -/
lemma real.fourier_coeff_tsum_comp_add {f : C(ℝ, ℂ)}
  (hf : ∀ (K : compacts ℝ), summable (λ n : ℤ, ‖(f.comp (continuous_map.add_right n)).restrict K‖))
  (m : ℤ) :
  fourier_coeff (periodic.lift $ f.periodic_tsum_comp_add_zsmul 1) m = 𝓕 f m :=
begin
  -- NB: This proof can be shortened somewhat by telescoping together some of the steps in the calc
  -- block, but I think it's more legible this way. We start with preliminaries about the integrand.
  let e : C(ℝ, ℂ) := (fourier (-m)).comp ⟨(coe : ℝ → unit_add_circle), continuous_quotient_mk⟩,
  have neK : ∀ (K : compacts ℝ) (g : C(ℝ, ℂ)), ‖(e * g).restrict K‖ = ‖g.restrict K‖,
  { have : ∀ (x : ℝ), ‖e x‖ = 1, from λ x, abs_coe_circle _,
    intros K g,
    simp_rw [norm_eq_supr_norm, restrict_apply, mul_apply, norm_mul, this, one_mul] },
  have eadd : ∀ (n : ℤ), e.comp (continuous_map.add_right n) = e,
  { intro n, ext1 x,
    have : periodic e 1, from periodic.comp (λ x, add_circle.coe_add_period 1 x) _,
    simpa only [mul_one] using this.int_mul n x },
  -- Now the main argument. First unwind some definitions.
  calc fourier_coeff (periodic.lift $ f.periodic_tsum_comp_add_zsmul 1) m
  = ∫_{0}^{1} x, e x * (∑' n : ℤ, f.comp (continuous_map.add_right n)) x :
    by simp_rw [fourier_coeff_eq_interval_integral _ m 0, div_one, one_smul, zero_add, comp_apply,
      coe_mk, periodic.lift_coe, zsmul_one, smul_eq_mul]
  -- Transform sum in C(ℝ, ℂ) evaluated at x into pointwise sum of values.
  ... = ∫_{0}^{1} x, (∑' n : ℤ, (e * f.comp (continuous_map.add_right n)) x) :
    by simp_rw [coe_mul, pi.mul_apply, ←tsum_apply (summable_of_locally_summable_norm hf),
      tsum_mul_left]
  -- Swap sum and integral.
  ... = ∑' n : ℤ, ∫_{0}^{1} x, (e * f.comp (continuous_map.add_right n)) x :
    begin
      refine (interval_integral.tsum_interval_integral_eq_of_summable_norm _).symm,
      convert hf ⟨uIcc 0 1, is_compact_uIcc⟩,
      exact funext (λ n, neK _ _)
    end
  ... = ∑' n : ℤ, ∫_{0}^{1} x, (e * f).comp (continuous_map.add_right n) x :
    begin
      simp only [continuous_map.comp_apply, mul_comp] at eadd ⊢,
      simp_rw eadd,
    end
  -- Rearrange sum of interval integrals into an integral over `ℝ`.
  ... = ∫ x, e x * f x :
    begin
      suffices : integrable ⇑(e * f), from this.has_sum_interval_integral_comp_add_int.tsum_eq,
      apply integrable_of_summable_norm_Icc,
      convert hf ⟨Icc 0 1, is_compact_Icc⟩,
      simp_rw [continuous_map.comp_apply, mul_comp] at eadd ⊢,
      simp_rw eadd,
      exact funext (λ n, neK ⟨Icc 0 1, is_compact_Icc⟩ _),
    end
  -- Minor tidying to finish
  ... = 𝓕 f m :
    begin
      rw fourier_integral_eq_integral_exp_smul,
      congr' 1 with x : 1,
      rw [smul_eq_mul, comp_apply, coe_mk, fourier_coe_apply],
      congr' 2,
      push_cast,
      ring
    end
end

/-- **Poisson's summation formula**, most general form. -/
theorem real.tsum_eq_tsum_fourier_integral {f : C(ℝ, ℂ)}
  (h_norm : ∀ (K : compacts ℝ),
    summable (λ n : ℤ, ‖(f.comp $ continuous_map.add_right n).restrict K‖))
  (h_sum : summable (λ n : ℤ, 𝓕 f n)) :
  ∑' (n : ℤ), f n = ∑' (n : ℤ), 𝓕 f n :=
begin
  let F : C(unit_add_circle, ℂ) := ⟨(f.periodic_tsum_comp_add_zsmul 1).lift,
    continuous_coinduced_dom.mpr (map_continuous _)⟩,
  have : summable (fourier_coeff F),
  { convert h_sum,
    exact funext (λ n, real.fourier_coeff_tsum_comp_add h_norm n) },
  convert (has_pointwise_sum_fourier_series_of_summable this 0).tsum_eq.symm using 1,
  { have := (has_sum_apply (summable_of_locally_summable_norm h_norm).has_sum 0).tsum_eq,
    simpa only [coe_mk, ←quotient_add_group.coe_zero, periodic.lift_coe, zsmul_one, comp_apply,
      coe_add_right, zero_add] using this },
  { congr' 1 with n : 1,
    rw [←real.fourier_coeff_tsum_comp_add h_norm n, fourier_eval_zero, smul_eq_mul, mul_one],
    refl },
end

section rpow_decay

variables {E : Type*} [normed_add_comm_group E]

/-- If `f` is `O(x ^ (-b))` at infinity, then so is the function
`λ x, ‖f.restrict (Icc (x + R) (x + S))‖` for any fixed `R` and `S`. -/
lemma is_O_norm_Icc_restrict_at_top {f : C(ℝ, E)} {b : ℝ} (hb : 0 < b)
  (hf : is_O at_top f (λ x : ℝ, |x| ^ (-b))) (R S : ℝ) :
  is_O at_top (λ x : ℝ, ‖f.restrict (Icc (x + R) (x + S))‖) (λ x : ℝ, |x| ^ (-b)) :=
begin
  -- First establish an explicit estimate on decay of inverse powers.
  -- This is logically independent of the rest of the proof, but of no mathematical interest in
  -- itself, so it is proved using `async` rather than being formulated as a separate lemma.
  have claim : ∀ (x : ℝ), max 0 (-2 * R) < x →
    ∀ (y : ℝ), x + R ≤ y → y ^ (-b) ≤ (1 / 2) ^ (-b) * x ^ (-b),
  { intros x hx y hy,
    rw max_lt_iff at hx,
    have hxR : 0 < x + R,
    { rcases le_or_lt 0 R with h|h,
      { exact add_pos_of_pos_of_nonneg hx.1 h },
      { rw [←sub_lt_iff_lt_add, zero_sub],
        refine lt_trans _ hx.2,
        rwa [neg_mul, neg_lt_neg_iff, two_mul, add_lt_iff_neg_left] } },
    have hy' : 0 < y, from hxR.trans_le hy,
    have : y ^ (-b) ≤ (x + R) ^ (-b),
    { rw [rpow_neg hy'.le, rpow_neg hxR.le,
      inv_le_inv (rpow_pos_of_pos hy' _) (rpow_pos_of_pos hxR _)],
    exact rpow_le_rpow hxR.le hy hb.le },
    refine this.trans _,
    rw [←mul_rpow one_half_pos.le hx.1.le, rpow_neg (mul_pos one_half_pos hx.1).le,
      rpow_neg hxR.le],
    refine inv_le_inv_of_le (rpow_pos_of_pos (mul_pos one_half_pos hx.1) _) _,
    exact rpow_le_rpow (mul_pos one_half_pos hx.1).le (by linarith) hb.le },
  -- Now the main proof.
  obtain ⟨c, hc, hc'⟩ := hf.exists_pos,
  simp only [is_O, is_O_with, eventually_at_top] at hc' ⊢,
  obtain ⟨d, hd⟩ := hc',
  refine ⟨c * (1 / 2) ^ (-b), ⟨max (1 + max 0 (-2 * R)) (d - R), λ x hx, _⟩⟩,
  rw [ge_iff_le, max_le_iff] at hx,
  have hx' : max 0 (-2 * R) < x, by linarith,
  rw max_lt_iff at hx',
  rw [norm_norm, continuous_map.norm_le _
    (mul_nonneg (mul_nonneg hc.le $ rpow_nonneg_of_nonneg one_half_pos.le _) (norm_nonneg _))],
  refine λ y, (hd y.1 (by linarith [hx.1, y.2.1])).trans _,
  have A : ∀ (x : ℝ), 0 ≤ |x| ^ (-b), from λ x, by positivity,
  rwa [mul_assoc, mul_le_mul_left hc, norm_of_nonneg (A _), norm_of_nonneg (A _)],
  convert claim x (by linarith only [hx.1]) y.1 y.2.1,
  { apply abs_of_nonneg, linarith [y.2.1] },
  { exact abs_of_pos hx'.1 },
end

lemma is_O_norm_Icc_restrict_at_bot {f : C(ℝ, E)} {b : ℝ} (hb : 0 < b)
  (hf : is_O at_bot f (λ x : ℝ, |x| ^ (-b))) (R S : ℝ) :
  is_O at_bot (λ x : ℝ, ‖f.restrict (Icc (x + R) (x + S))‖) (λ x : ℝ, |x| ^ (-b)) :=
begin
  have h1 : is_O at_top (f.comp (continuous_map.mk _ continuous_neg)) (λ x : ℝ, |x| ^ (-b)),
  { convert hf.comp_tendsto tendsto_neg_at_top_at_bot,
    ext1 x, simp only [function.comp_app, abs_neg] },
  have h2 := (is_O_norm_Icc_restrict_at_top hb h1 (-S) (-R)).comp_tendsto tendsto_neg_at_bot_at_top,
  have : ((λ (x : ℝ), |x| ^ -b) ∘ has_neg.neg) = (λ (x : ℝ), |x| ^ -b),
  { ext1 x, simp only [function.comp_app, abs_neg] },
  rw this at h2,
  refine (is_O_of_le _ (λ x, _)).trans h2, -- equality holds, but less work to prove `≤` alone
  rw [norm_norm, function.comp_app, norm_norm, continuous_map.norm_le _ (norm_nonneg _)],
  rintro ⟨x, hx⟩,
  rw [continuous_map.restrict_apply_mk],
  refine (le_of_eq _).trans (continuous_map.norm_coe_le_norm _ ⟨-x, _⟩),
  { exact ⟨by linarith [hx.2], by linarith [hx.1]⟩ },
  { rw [continuous_map.restrict_apply_mk, continuous_map.comp_apply, continuous_map.coe_mk,
      neg_neg] }
end

lemma is_O_norm_restrict_cocompact (f : C(ℝ, E)) {b : ℝ} (hb : 0 < b)
  (hf : is_O (cocompact ℝ) f (λ x : ℝ, |x| ^ (-b))) (K : compacts ℝ) :
  is_O (cocompact ℝ) (λ x, ‖(f.comp (continuous_map.add_right x)).restrict K‖) (λ x, |x| ^ (-b)) :=
begin
  obtain ⟨r, hr⟩ := K.is_compact.bounded.subset_ball 0,
  rw [closed_ball_eq_Icc, zero_add, zero_sub] at hr,
  have : ∀ (x : ℝ), ‖(f.comp (continuous_map.add_right x)).restrict K‖ ≤
    ‖f.restrict (Icc (x - r) (x + r))‖,
  { intro x,
    rw continuous_map.norm_le _ (norm_nonneg _),
    rintro ⟨y, hy⟩,
    refine (le_of_eq _).trans (continuous_map.norm_coe_le_norm _ ⟨y + x, _⟩),
    exact ⟨by linarith [(hr hy).1], by linarith [(hr hy).2]⟩,
    simp_rw [continuous_map.restrict_apply, continuous_map.comp_apply,
      continuous_map.coe_add_right, subtype.coe_mk] },
  simp_rw [cocompact_eq, is_O_sup] at hf ⊢,
  split,
  { refine (is_O_of_le at_bot _).trans (is_O_norm_Icc_restrict_at_bot hb hf.1 (-r) r),
    simp_rw norm_norm, exact this },
  { refine (is_O_of_le at_top _).trans (is_O_norm_Icc_restrict_at_top hb hf.2 (-r) r),
    simp_rw norm_norm, exact this },
end


/-- **Poisson's summation formula**, assuming that `f` decays as
`|x| ^ (-b)` for some `1 < b` and its Fourier transform is summable. -/
lemma real.tsum_eq_tsum_fourier_integral_of_rpow_decay_of_summable {f : ℝ → ℂ} (hc : continuous f)
  {b : ℝ} (hb : 1 < b) (hf : is_O (cocompact ℝ) f (λ x : ℝ, |x| ^ (-b)))
  (hFf : summable (λ n : ℤ, 𝓕 f n)) :
  ∑' (n : ℤ), f n = ∑' (n : ℤ), 𝓕 f n :=
real.tsum_eq_tsum_fourier_integral
  (λ K, summable_of_is_O (real.summable_abs_int_rpow hb)
    ((is_O_norm_restrict_cocompact (continuous_map.mk _ hc)
    (zero_lt_one.trans hb) hf K).comp_tendsto int.tendsto_coe_cofinite)) hFf

/-- **Poisson's summation formula**, assuming that both `f` and its Fourier transform decay as
`|x| ^ (-b)` for some `1 < b`. (This is the one-dimensional case of Corollary VII.2.6 of Stein and
Weiss, *Introduction to Fourier analysis on Euclidean spaces*.) -/
lemma real.tsum_eq_tsum_fourier_integral_of_rpow_decay {f : ℝ → ℂ} (hc : continuous f)
  {b : ℝ} (hb : 1 < b) (hf : is_O (cocompact ℝ) f (λ x : ℝ, |x| ^ (-b)))
  (hFf : is_O (cocompact ℝ) (𝓕 f) (λ x : ℝ, |x| ^ (-b))) :
  ∑' (n : ℤ), f n = ∑' (n : ℤ), 𝓕 f n :=
real.tsum_eq_tsum_fourier_integral_of_rpow_decay_of_summable hc hb hf
  (summable_of_is_O (real.summable_abs_int_rpow hb) (hFf.comp_tendsto int.tendsto_coe_cofinite))

end rpow_decay

section schwartz

/-- **Poisson's summation formula** for Schwartz functions. -/
lemma schwartz_map.tsum_eq_tsum_fourier_integral
  (f g : schwartz_map ℝ ℂ) (hfg : 𝓕 f = g) :
  ∑' (n : ℤ), f n = ∑' (n : ℤ), g n :=
begin
  -- We know that Schwartz functions are `O(‖x ^ (-b)‖)` for *every* `b`; for this argument we take
  -- `b = 2` and work with that.
  simp_rw ←hfg,
  exact real.tsum_eq_tsum_fourier_integral_of_rpow_decay f.continuous one_lt_two
    (f.is_O_cocompact_rpow (-2)) (by simpa only [hfg] using g.is_O_cocompact_rpow (-2))
end

end schwartz
