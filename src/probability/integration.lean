/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Zinkevich
-/
import measure_theory.integral.bochner
import measure_theory.integral.lebesgue
import measure_theory.function.l1_space
import probability.independence
import probability.notation

/-!
# Integration in Probability Theory

Integration results for independent random variables. Specifically, for two
independent random variables X and Y over the extended non-negative
reals, `E[X * Y] = E[X] * E[Y]`, and similar results.

## Implementation notes

Many lemmas in this file take two arguments of the same typeclass. It is worth remembering that lean
will always pick the later typeclass in this situation, and does not care whether the arguments are
`[]`, `{}`, or `()`. All of these use the `measurable_space` `M2` to define `μ`:

```lean
example {M1 : measurable_space α} [M2 : measurable_space α] {μ : measure α} : sorry := sorry
example [M1 : measurable_space α] {M2 : measurable_space α} {μ : measure α} : sorry := sorry
```

-/

noncomputable theory
open set measure_theory
open_locale ennreal probability_theory

variables {α : Type*}

namespace probability_theory

/-- This (roughly) proves that if a random variable `f` is independent of an event `T`,
   then if you restrict the random variable to `T`, then
   `E[f * indicator T c 0]=E[f] * E[indicator T c 0]`. It is useful for
   `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space`. -/
lemma lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator
  {Mf : measurable_space α} [M : measurable_space α] {μ : measure α} (hMf : Mf ≤ M)
  (c : ℝ≥0∞) {T : set α} (h_meas_T : measurable_set T)
  (h_ind : indep_sets Mf.measurable_set' {T} μ)
  {f : α → ℝ≥0∞} (h_meas_f : @measurable α ℝ≥0∞ Mf _ f) :
  ∫⁻ a, f a * T.indicator (λ _, c) a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, T.indicator (λ _, c) a ∂μ :=
begin
  revert f,
  have h_mul_indicator : ∀ g, measurable g → measurable (λ a, g a * T.indicator (λ x, c) a),
    from λ g h_mg, h_mg.mul (measurable_const.indicator h_meas_T),
  apply measurable.ennreal_induction,
  { intros c' s' h_meas_s',
    simp_rw [← inter_indicator_mul],
    rw [lintegral_indicator _ (measurable_set.inter (hMf _ h_meas_s') (h_meas_T)),
      lintegral_indicator _ (hMf _ h_meas_s'), lintegral_indicator _ h_meas_T],
    simp only [measurable_const, lintegral_const, univ_inter, lintegral_const_mul,
      measurable_set.univ, measure.restrict_apply],
    ring_nf,
    congr,
    rw [mul_comm, h_ind s' T h_meas_s' (set.mem_singleton _)], },
  { intros f' g h_univ h_meas_f' h_meas_g h_ind_f' h_ind_g,
    have h_measM_f' : measurable f', from h_meas_f'.mono hMf le_rfl,
    have h_measM_g : measurable g, from h_meas_g.mono hMf le_rfl,
    simp_rw [pi.add_apply, right_distrib],
    rw [lintegral_add (h_mul_indicator _ h_measM_f') (h_mul_indicator _ h_measM_g),
      lintegral_add h_measM_f' h_measM_g, right_distrib, h_ind_f', h_ind_g] },
  { intros f h_meas_f h_mono_f h_ind_f,
    have h_measM_f : ∀ n, measurable (f n), from λ n, (h_meas_f n).mono hMf le_rfl,
    simp_rw [ennreal.supr_mul],
    rw [lintegral_supr h_measM_f h_mono_f, lintegral_supr, ennreal.supr_mul],
    { simp_rw [← h_ind_f] },
    { exact λ n, h_mul_indicator _ (h_measM_f n) },
    { exact λ m n h_le a, ennreal.mul_le_mul (h_mono_f h_le a) le_rfl, }, },
end

/-- This (roughly) proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. However, instead of directly using the independence
   of the random variables, it uses the independence of measurable spaces for the
   domains of `f` and `g`. This is similar to the sigma-algebra approach to
   independence. See `lintegral_mul_eq_lintegral_mul_lintegral_of_independent_fn` for
   a more common variant of the product of independent variables. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
  {Mf Mg : measurable_space α} [M : measurable_space α] {μ : measure α}
  (hMf : Mf ≤ M) (hMg : Mg ≤ M) (h_ind : indep Mf Mg μ) {f g : α → ℝ≥0∞}
  (h_meas_f : @measurable α ℝ≥0∞ Mf _ f) (h_meas_g : @measurable α ℝ≥0∞ Mg _ g) :
  ∫⁻ a, f a * g a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, g a ∂μ :=
begin
  revert g,
  have h_measM_f : measurable f, from h_meas_f.mono hMf le_rfl,
  apply measurable.ennreal_induction,
  { intros c s h_s,
    apply lintegral_mul_indicator_eq_lintegral_mul_lintegral_indicator hMf _ (hMg _ h_s) _ h_meas_f,
    apply indep_sets_of_indep_sets_of_le_right h_ind,
    rwa singleton_subset_iff, },
  { intros f' g h_univ h_measMg_f' h_measMg_g h_ind_f' h_ind_g',
    have h_measM_f' : measurable f', from h_measMg_f'.mono hMg le_rfl,
    have h_measM_g : measurable g, from h_measMg_g.mono hMg le_rfl,
    simp_rw [pi.add_apply, left_distrib],
    rw [lintegral_add h_measM_f' h_measM_g,
      lintegral_add (h_measM_f.mul h_measM_f') (h_measM_f.mul h_measM_g),
      left_distrib, h_ind_f', h_ind_g'] },
  { intros f' h_meas_f' h_mono_f' h_ind_f',
    have h_measM_f' : ∀ n, measurable (f' n), from λ n, (h_meas_f' n).mono hMg le_rfl,
    simp_rw [ennreal.mul_supr],
    rw [lintegral_supr, lintegral_supr h_measM_f' h_mono_f', ennreal.mul_supr],
    { simp_rw [← h_ind_f'], },
    { exact λ n, h_measM_f.mul (h_measM_f' n), },
    { exact λ n m (h_le : n ≤ m) a, ennreal.mul_le_mul le_rfl (h_mono_f' h_le a), }, }
end

/-- This proves that if `f` and `g` are independent random variables,
   then `E[f * g] = E[f] * E[g]`. -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun [measurable_space α] {μ : measure α}
  {f g : α → ℝ≥0∞} (h_meas_f : measurable f) (h_meas_g : measurable g)
  (h_indep_fun : indep_fun f g μ) :
  ∫⁻ a, (f * g) a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, g a ∂μ :=
lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurable_space
  (measurable_iff_comap_le.1 h_meas_f) (measurable_iff_comap_le.1 h_meas_g) h_indep_fun
  (measurable.of_comap_le le_rfl) (measurable.of_comap_le le_rfl)

/-- This proves that if `f` and `g` are independent and almost everywhere measurable,
   then `E[f * g] = E[f] * E[g]` (slightly generalizing
   `lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun`). -/
lemma lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' [measurable_space α] {μ : measure α}
  {f g : α → ℝ≥0∞} (h_meas_f : ae_measurable f μ) (h_meas_g : ae_measurable g μ)
  (h_indep_fun : indep_fun f g μ) :
  ∫⁻ a, (f * g) a ∂μ = ∫⁻ a, f a ∂μ * ∫⁻ a, g a ∂μ :=
begin
  rcases h_meas_f with ⟨f',f'_meas,f'_ae⟩,
  rcases h_meas_g with ⟨g',g'_meas,g'_ae⟩,
  have fg_ae : f * g =ᵐ[μ] f' * g' := f'_ae.mul g'_ae,
  rw [lintegral_congr_ae f'_ae, lintegral_congr_ae g'_ae, lintegral_congr_ae fg_ae],
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun f'_meas g'_meas,
  exact h_indep_fun.ae_eq f'_ae g'_ae
end

/-- This shows that the product of two independent, integrable, real_valued random variables
  is itself integrable. -/
lemma indep_fun.integrable_mul [measurable_space α] {μ : measure α}
  {X Y : α → ℝ} (hXY : indep_fun X Y μ) (hX : integrable X μ) (hY : integrable Y μ) :
  integrable (X * Y) μ :=
begin
  let nX : α → ennreal := λ a, ∥X a∥₊,
  let nY : α → ennreal := λ a, ∥Y a∥₊,

  have hXY' : indep_fun (λ a, ∥X a∥₊) (λ a, ∥Y a∥₊) μ :=
    hXY.comp measurable_nnnorm measurable_nnnorm,
  have hXY'' : indep_fun nX nY μ :=
    hXY'.comp measurable_coe_nnreal_ennreal measurable_coe_nnreal_ennreal,

  have hnX : ae_measurable nX μ := hX.1.ae_measurable.nnnorm.coe_nnreal_ennreal,
  have hnY : ae_measurable nY μ := hY.1.ae_measurable.nnnorm.coe_nnreal_ennreal,

  have hmul : ∫⁻ a, nX a * nY a ∂μ = ∫⁻ a, nX a ∂μ * ∫⁻ a, nY a ∂μ :=
    by convert lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' hnX hnY hXY'',

  refine ⟨hX.1.mul hY.1, _⟩,
  simp_rw [has_finite_integral, pi.mul_apply, nnnorm_mul, ennreal.coe_mul, hmul],
  exact ennreal.mul_lt_top_iff.mpr (or.inl ⟨hX.2, hY.2⟩)
end

/-- This shows that the (Bochner) integral of the product of two independent, nonnegative random
  variables is the product of their integrals. The proof is just plumbing around
  `lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun'`. -/
lemma indep_fun.integral_mul_of_nonneg [measurable_space α] {μ : measure α} {X Y : α → ℝ}
  (hXY : indep_fun X Y μ) (hXp : 0 ≤ X) (hYp : 0 ≤ Y)
  (hXm : ae_measurable X μ) (hYm : ae_measurable Y μ) :
  integral μ (X * Y) = integral μ X * integral μ Y :=
begin
  have h1 : ae_measurable (λ a, ennreal.of_real (X a)) μ :=
    ennreal.measurable_of_real.comp_ae_measurable hXm,
  have h2 : ae_measurable (λ a, ennreal.of_real (Y a)) μ :=
    ennreal.measurable_of_real.comp_ae_measurable hYm,
  have h3 : ae_measurable (X * Y) μ := hXm.mul hYm,

  have h4 : 0 ≤ᵐ[μ] X := ae_of_all _ hXp,
  have h5 : 0 ≤ᵐ[μ] Y := ae_of_all _ hYp,
  have h6 : 0 ≤ᵐ[μ] (X * Y) := ae_of_all _ (λ ω, mul_nonneg (hXp ω) (hYp ω)),

  have h7 : ae_strongly_measurable X μ := ae_strongly_measurable_iff_ae_measurable.mpr hXm,
  have h8 : ae_strongly_measurable Y μ := ae_strongly_measurable_iff_ae_measurable.mpr hYm,
  have h9 : ae_strongly_measurable (X * Y) μ := ae_strongly_measurable_iff_ae_measurable.mpr h3,

  rw [integral_eq_lintegral_of_nonneg_ae h4 h7],
  rw [integral_eq_lintegral_of_nonneg_ae h5 h8],
  rw [integral_eq_lintegral_of_nonneg_ae h6 h9],
  simp_rw [←ennreal.to_real_mul, pi.mul_apply, ennreal.of_real_mul (hXp _)],
  congr,
  apply lintegral_mul_eq_lintegral_mul_lintegral_of_indep_fun' h1 h2,
  exact hXY.comp ennreal.measurable_of_real ennreal.measurable_of_real
end

/-- This shows that the (Bochner) integral of the product of two independent, integrable random
  variables is the product of their integrals. The proof is pedestrian decomposition into their
  positive and negative parts in order to apply `indep_fun.integral_mul_of_nonneg` four times. -/
theorem indep_fun.integral_mul_of_integrable [measurable_space α] {μ : measure α} {X Y : α → ℝ}
  (hXY : indep_fun X Y μ) (hX : integrable X μ) (hY : integrable Y μ) :
  integral μ (X * Y) = integral μ X * integral μ Y :=
begin
  let pos : ℝ → ℝ := (λ x, max x 0),
  let neg : ℝ → ℝ := (λ x, max (-x) 0),
  have posm : measurable pos := measurable_id'.max measurable_const,
  have negm : measurable neg := measurable_id'.neg.max measurable_const,

  let Xp := pos ∘ X, -- `X⁺` would look better but it makes `simp_rw` below fail
  let Xm := neg ∘ X,
  let Yp := pos ∘ Y,
  let Ym := neg ∘ Y,

  have hXpm : X = Xp - Xm := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (X ω)).symm),
  have hYpm : Y = Yp - Ym := funext (λ ω, (max_zero_sub_max_neg_zero_eq_self (Y ω)).symm),

  have hp1 : 0 ≤ Xm := λ ω, le_max_right _ _,
  have hp2 : 0 ≤ Xp := λ ω, le_max_right _ _,
  have hp3 : 0 ≤ Ym := λ ω, le_max_right _ _,
  have hp4 : 0 ≤ Yp := λ ω, le_max_right _ _,

  have hm1 : ae_measurable Xm μ := hX.1.ae_measurable.neg.max ae_measurable_const,
  have hm2 : ae_measurable Xp μ := hX.1.ae_measurable.max ae_measurable_const,
  have hm3 : ae_measurable Ym μ := hY.1.ae_measurable.neg.max ae_measurable_const,
  have hm4 : ae_measurable Yp μ := hY.1.ae_measurable.max ae_measurable_const,

  have hv1 : integrable Xm μ := hX.neg.max_zero,
  have hv2 : integrable Xp μ := hX.max_zero,
  have hv3 : integrable Ym μ := hY.neg.max_zero,
  have hv4 : integrable Yp μ := hY.max_zero,

  have hi1 : indep_fun Xm Ym μ := hXY.comp negm negm,
  have hi2 : indep_fun Xp Ym μ := hXY.comp posm negm,
  have hi3 : indep_fun Xm Yp μ := hXY.comp negm posm,
  have hi4 : indep_fun Xp Yp μ := hXY.comp posm posm,

  have hl1 : integrable (Xm * Ym) μ := hi1.integrable_mul hv1 hv3,
  have hl2 : integrable (Xp * Ym) μ := hi2.integrable_mul hv2 hv3,
  have hl3 : integrable (Xm * Yp) μ := hi3.integrable_mul hv1 hv4,
  have hl4 : integrable (Xp * Yp) μ := hi4.integrable_mul hv2 hv4,
  have hl5 : integrable (Xp * Yp - Xm * Yp) μ := hl4.sub hl3,
  have hl6 : integrable (Xp * Ym - Xm * Ym) μ := hl2.sub hl1,

  simp_rw [hXpm, hYpm, mul_sub, sub_mul],
  rw [integral_sub' hl5 hl6, integral_sub' hl4 hl3, integral_sub' hl2 hl1],
  rw [integral_sub' hv2 hv1, integral_sub' hv4 hv3],
  rw [hi1.integral_mul_of_nonneg hp1 hp3 hm1 hm3, hi2.integral_mul_of_nonneg hp2 hp3 hm2 hm3],
  rw [hi3.integral_mul_of_nonneg hp1 hp4 hm1 hm4, hi4.integral_mul_of_nonneg hp2 hp4 hm2 hm4],
  ring
end

end probability_theory
