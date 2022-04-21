/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.parametric_integral
import measure_theory.integral.interval_integral

/-!
# Derivatives of interval integrals depending on parameters

In this file we restate theorems about derivatives of integrals depending on parameters for interval
integrals.  -/


open topological_space measure_theory filter metric
open_locale topological_space filter interval

variables {𝕜 : Type*} [is_R_or_C 𝕜] {μ : measure ℝ}
          {E : Type*} [normed_group E] [normed_space ℝ E] [normed_space 𝕜 E]
          [complete_space E]
          {H : Type*} [normed_group H] [normed_space 𝕜 H]
          {a b ε : ℝ} {bound : ℝ → ℝ}

namespace interval_integral

/-- Differentiation under integral of `x ↦ ∫ t in a..b, F x t` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with a ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_fderiv_at_integral_of_dominated_loc_of_lip {F : H → ℝ → E} {F' : ℝ → (H →L[𝕜] E)} {x₀ : H}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) (μ.restrict (Ι a b)))
  (hF_int : interval_integrable (F x₀) μ a b)
  (hF'_meas : ae_strongly_measurable F' (μ.restrict (Ι a b)))
  (h_lip : ∀ᵐ t ∂μ, t ∈ Ι a b → lipschitz_on_with (real.nnabs $ bound t) (λ x, F x t) (ball x₀ ε))
  (bound_integrable : interval_integrable bound μ a b)
  (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → has_fderiv_at (λ x, F x t) (F' t) x₀) :
  interval_integrable F' μ a b ∧
    has_fderiv_at (λ x, ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ :=
begin
  simp only [interval_integrable_iff, interval_integral_eq_integral_interval_oc,
    ← ae_restrict_iff' measurable_set_interval_oc] at *,
  have := has_fderiv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas h_lip
    bound_integrable h_diff,
  exact ⟨this.1, this.2.const_smul _⟩
end

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a ball around `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_fderiv_at_integral_of_dominated_of_fderiv_le {F : H → ℝ → E} {F' : H → ℝ → (H →L[𝕜] E)}
  {x₀ : H} (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) (μ.restrict (Ι a b)))
  (hF_int : interval_integrable (F x₀) μ a b)
  (hF'_meas : ae_strongly_measurable (F' x₀) (μ.restrict (Ι a b)))
  (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ∥F' x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, has_fderiv_at (λ x, F x t) (F' x t) x) :
  has_fderiv_at (λ x, ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ :=
begin
  simp only [interval_integrable_iff, interval_integral_eq_integral_interval_oc,
    ← ae_restrict_iff' measurable_set_interval_oc] at *,
  exact (has_fderiv_at_integral_of_dominated_of_fderiv_le ε_pos hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff).const_smul _
end

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_deriv_at_integral_of_dominated_loc_of_lip {F : 𝕜 → ℝ → E} {F' : ℝ → E} {x₀ : 𝕜}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) (μ.restrict (Ι a b)))
  (hF_int : interval_integrable (F x₀) μ a b)
  (hF'_meas : ae_strongly_measurable F' (μ.restrict (Ι a b)))
  (h_lipsch : ∀ᵐ t ∂μ, t ∈ Ι a b →
    lipschitz_on_with (real.nnabs $ bound t) (λ x, F x t) (ball x₀ ε))
  (bound_integrable : interval_integrable (bound : ℝ → ℝ) μ a b)
  (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → has_deriv_at (λ x, F x t) (F' t) x₀) :
  (interval_integrable F' μ a b) ∧
    has_deriv_at (λ x, ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ :=
begin
  simp only [interval_integrable_iff, interval_integral_eq_integral_interval_oc,
    ← ae_restrict_iff' measurable_set_interval_oc] at *,
  have := has_deriv_at_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas h_lipsch
    bound_integrable h_diff,
  exact ⟨this.1, this.2.const_smul _⟩
end


/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : ℝ`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
lemma has_deriv_at_integral_of_dominated_loc_of_deriv_le {F : 𝕜 → ℝ → E} {F' : 𝕜 → ℝ → E} {x₀ : 𝕜}
  (ε_pos : 0 < ε)
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) (μ.restrict (Ι a b)))
  (hF_int : interval_integrable (F x₀) μ a b)
  (hF'_meas : ae_strongly_measurable (F' x₀) (μ.restrict (Ι a b)))
  (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ∥F' x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, has_deriv_at (λ x, F x t) (F' x t) x) :
  (interval_integrable (F' x₀) μ a b) ∧
    has_deriv_at (λ x, ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ :=
begin
  simp only [interval_integrable_iff, interval_integral_eq_integral_interval_oc,
    ← ae_restrict_iff' measurable_set_interval_oc] at *,
  have := has_deriv_at_integral_of_dominated_loc_of_deriv_le ε_pos hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff,
  exact ⟨this.1, this.2.const_smul _⟩
end

end interval_integral
