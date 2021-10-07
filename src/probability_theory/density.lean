/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.radon_nikodym
import measure_theory.measure.lebesgue

/-!
# Probability density function

This file defines the probability density function of random variables, by which we mean
measurable functions taking values in a Borel space. In particular, a measurable function `f`
is said to the probability density function of a random variable `X` if for all measurable
sets `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions are one way of describing
the distribution of a random variable, and are useful for calculating probabilities and
finding moments (although the latter is better achieved with moment generating functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `measure_theory.has_pdf` : A random variable `X : α → E` is said to `has_pdf` with
  respect to the measure `ℙ` on `α` and `μ` on `E` if there exists a measurable function `f`
  such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`.
* `measure_theory.pdf` : If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X`
  is the measurable function `f` such that the push-forward measure of `ℙ` along `X` equals
  `μ.with_density f`.
* `measure_theory.pdf.uniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `measure_theory.pdf.integral_fun_mul_eq_integral` : Law of the unconscious statistician,
  i.e. if a random variable `X : α → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, g x * f x dx` for
  all measurable `g : E → ℝ`.
* `measure_theory.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `measure_theory.pdf.uniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.

## TODOs

Ultimately, we would also like to define characteristic functions to describe distributions as
it exists for all random variables. However, to define this, we will need Fourier transforms
which we currently do not have.
-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal

namespace measure_theory

open topological_space measure_theory.measure

variables {α E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [normed_space ℝ E] [complete_space E] [borel_space E]

/-- A random variable `X : α → E` is said to `has_pdf` with respect to the measure `ℙ` on `α` and
`μ` on `E` if there exists a measurable function `f` such that the push-forward measure of `ℙ`
along `X` equals `μ.with_density f`. -/
class has_pdf {m : measurable_space α} (X : α → E)
  (ℙ : measure α) (μ : measure E . volume_tac) : Prop :=
(pdf' : measurable X ∧ ∃ (f : E → ℝ≥0∞), measurable f ∧ map X ℙ = μ.with_density f)

@[measurability]
lemma has_pdf.measurable {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : has_pdf X ℙ μ] :
  measurable X :=
hX.pdf'.1

/-- If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X` is the measurable function `f`
such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`. -/
def pdf {m : measurable_space α} (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) :=
if hX : has_pdf X ℙ μ then classical.some hX.pdf'.2 else 0

lemma pdf_undef {m : measurable_space α} {ℙ : measure α} {μ : measure E} {X : α → E}
  (h : ¬ has_pdf X ℙ μ) :
  pdf X ℙ μ = 0 :=
by simp only [pdf, dif_neg h]

lemma pdf_eq_zero_of_not_measurable {m : measurable_space α}
  {ℙ : measure α} {μ : measure E} {X : α → E} (hX : ¬ measurable X) :
  pdf X ℙ μ = 0 :=
pdf_undef (λ hpdf, hX hpdf.pdf'.1)

lemma measurable_of_pdf_ne_zero {m : measurable_space α}
  {ℙ : measure α} {μ : measure E} (X : α → E) (h : pdf X ℙ μ ≠ 0) :
  measurable X :=
by { by_contra hX, exact h (pdf_eq_zero_of_not_measurable hX) }

@[measurability]
lemma measurable_pdf {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) :
  measurable (pdf X ℙ μ) :=
begin
  by_cases hX : has_pdf X ℙ μ,
  { rw [pdf, dif_pos hX],
    exact (classical.some_spec hX.pdf'.2).1 },
  { rw [pdf, dif_neg hX],
    exact measurable_zero }
end

lemma map_eq_with_density_pdf {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : has_pdf X ℙ μ] :
  measure.map X ℙ = μ.with_density (pdf X ℙ μ) :=
begin
  rw [pdf, dif_pos hX],
  exact (classical.some_spec hX.pdf'.2).2
end

lemma map_eq_set_lintegral_pdf {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : has_pdf X ℙ μ]
  {s : set E} (hs : measurable_set s) :
  measure.map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ :=
by rw [← with_density_apply _ hs, map_eq_with_density_pdf X ℙ μ]

namespace pdf

variables {m : measurable_space α} {ℙ : measure α} {μ : measure E}

lemma lintegral_eq_measure_univ {X : α → E} [has_pdf X ℙ μ] :
  ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ set.univ :=
begin
  rw [← set_lintegral_univ, ← map_eq_set_lintegral_pdf X ℙ μ measurable_set.univ,
      measure.map_apply (has_pdf.measurable X ℙ μ) measurable_set.univ, set.preimage_univ],
end

lemma ae_lt_top [is_finite_measure ℙ] {μ : measure E} {X : α → E} :
  ∀ᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
begin
  by_cases hpdf : has_pdf X ℙ μ,
  { haveI := hpdf,
    refine ae_lt_top (measurable_pdf X ℙ μ) _,
    rw lintegral_eq_measure_univ,
    exact (measure_lt_top _ _).ne },
  { rw [pdf, dif_neg hpdf],
    exact filter.eventually_of_forall (λ x, with_top.zero_lt_top) }
end

lemma of_real_to_real_ae_eq [is_finite_measure ℙ] {X : α → E} :
  (λ x, ennreal.of_real (pdf X ℙ μ x).to_real) =ᵐ[μ] pdf X ℙ μ :=
begin
  by_cases hpdf : has_pdf X ℙ μ,
  { exactI of_real_to_real_ae_eq ae_lt_top },
  { convert ae_eq_refl _,
    ext1 x,
    rw [pdf, dif_neg hpdf, pi.zero_apply, ennreal.zero_to_real, ennreal.of_real_zero] }
end

lemma integrable_iff_integrable_mul_pdf [is_finite_measure ℙ] {X : α → E} [has_pdf X ℙ μ]
  {f : E → ℝ} (hf : measurable f) :
  integrable (λ x, f (X x)) ℙ ↔ integrable (λ x, f x * (pdf X ℙ μ x).to_real) μ :=
begin
  rw [← integrable_map_measure hf.ae_measurable (has_pdf.measurable X ℙ μ),
      map_eq_with_density_pdf X ℙ μ,
      integrable_with_density_iff (measurable_pdf _ _ _) ae_lt_top hf],
  apply_instance
end

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, `f ∘ X` is a random variable with expectation `∫ x, f x * pdf X ∂μ`
where `μ` is a measure on the codomain of `X`. -/
lemma integral_fun_mul_eq_integral [is_finite_measure ℙ]
  {X : α → E} [has_pdf X ℙ μ] {f : E → ℝ} (hf : measurable f) :
  ∫ x, f x * (pdf X ℙ μ x).to_real ∂μ = ∫ x, f (X x) ∂ℙ :=
begin
  by_cases hpdf : integrable (λ x, f x * (pdf X ℙ μ x).to_real) μ,
  { rw [← integral_map (has_pdf.measurable X ℙ μ) hf.ae_measurable,
        map_eq_with_density_pdf X ℙ μ,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part hpdf,
        integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
        lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.neg.ennreal_of_real,
        lintegral_with_density_eq_lintegral_mul _ (measurable_pdf X ℙ μ) hf.ennreal_of_real],
    { congr' 2,
      { have : ∀ x, ennreal.of_real (f x * (pdf X ℙ μ x).to_real) =
          ennreal.of_real (pdf X ℙ μ x).to_real * ennreal.of_real (f x),
        { intro x,
          rw [mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
        simp_rw [this],
        exact lintegral_congr_ae (filter.eventually_eq.mul of_real_to_real_ae_eq (ae_eq_refl _)) },
      { have : ∀ x, ennreal.of_real (- (f x * (pdf X ℙ μ x).to_real)) =
          ennreal.of_real (pdf X ℙ μ x).to_real * ennreal.of_real (-f x),
        { intro x,
          rw [neg_mul_eq_neg_mul, mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
        simp_rw [this],
        exact lintegral_congr_ae (filter.eventually_eq.mul of_real_to_real_ae_eq
          (ae_eq_refl _)) } },
    { refine ⟨hf.ae_measurable, _⟩,
      rw [has_finite_integral, lintegral_with_density_eq_lintegral_mul _
            (measurable_pdf _ _ _) hf.nnnorm.coe_nnreal_ennreal],
      have : (λ x, (pdf X ℙ μ * λ x, ↑∥f x∥₊) x) =ᵐ[μ] (λ x, ∥f x * (pdf X ℙ μ x).to_real∥₊),
      { simp_rw [← smul_eq_mul, nnnorm_smul, ennreal.coe_mul],
        rw [smul_eq_mul, mul_comm],
        refine filter.eventually_eq.mul (ae_eq_refl _) (ae_eq_trans of_real_to_real_ae_eq.symm _),
        convert ae_eq_refl _,
        ext1 x,
        exact real.ennnorm_eq_of_real ennreal.to_real_nonneg },
      rw lintegral_congr_ae this,
      exact hpdf.2 } },
  { rw [integral_undef hpdf, integral_undef],
    rwa ← integrable_iff_integrable_mul_pdf hf at hpdf,
    all_goals { apply_instance } }
end

lemma map_absolutely_continuous {X : α → E} [has_pdf X ℙ μ] : map X ℙ ≪ μ :=
by { rw map_eq_with_density_pdf X ℙ μ, exact with_density_absolutely_continuous _ _, }

/-- A random variable that `has_pdf` is quasi-measure preserving. -/
lemma to_quasi_measure_preserving {X : α → E} [has_pdf X ℙ μ] : quasi_measure_preserving X ℙ μ :=
{ measurable := has_pdf.measurable X ℙ μ,
  absolutely_continuous := map_absolutely_continuous, }

lemma have_lebesgue_decomposition_of_has_pdf {X : α → E} [hX' : has_pdf X ℙ μ] :
  (map X ℙ).have_lebesgue_decomposition μ :=
⟨⟨⟨0, pdf X ℙ μ⟩,
  by simp only [zero_add, measurable_pdf X ℙ μ, true_and, mutually_singular.zero.symm,
    map_eq_with_density_pdf X ℙ μ] ⟩⟩

lemma has_pdf_iff {X : α → E} :
  has_pdf X ℙ μ ↔ measurable X ∧ (map X ℙ).have_lebesgue_decomposition μ ∧ map X ℙ ≪ μ :=
begin
  split,
  { intro hX',
    exactI ⟨hX'.pdf'.1, have_lebesgue_decomposition_of_has_pdf, map_absolutely_continuous⟩ },
  { rintros ⟨hX, h_decomp, h⟩,
    haveI := h_decomp,
    refine ⟨⟨hX, (measure.map X ℙ).rn_deriv μ, measurable_rn_deriv _ _, _⟩⟩,
    rwa with_density_rn_deriv_eq }
end

lemma has_pdf_iff_of_measurable {X : α → E} (hX : measurable X) :
  has_pdf X ℙ μ ↔ (map X ℙ).have_lebesgue_decomposition μ ∧ map X ℙ ≪ μ :=
by { rw has_pdf_iff, simp only [hX, true_and], }

section

variables {F : Type*} [normed_group F] [measurable_space F] [second_countable_topology F]
  [normed_space ℝ F] [complete_space F] [borel_space F] {ν : measure F}

/-- A random variable that `has_pdf` transformed under a `quasi_measure_preserving`
map also `has_pdf` if `(map g (map X ℙ)).have_lebesgue_decomposition μ`.

`quasi_measure_preserving_has_pdf'` is more useful in the case we are working with a
probability measure and a real-valued random variable. -/
lemma quasi_measure_preserving_has_pdf {X : α → E} [has_pdf X ℙ μ]
  {g : E → F} (hg : quasi_measure_preserving g μ ν)
  (hmap : (map g (map X ℙ)).have_lebesgue_decomposition ν) :
  has_pdf (g ∘ X) ℙ ν :=
begin
  rw [has_pdf_iff, ← map_map hg.measurable (has_pdf.measurable X ℙ μ)],
  refine ⟨hg.measurable.comp (has_pdf.measurable X ℙ μ), hmap, _⟩,
  rw [map_eq_with_density_pdf X ℙ μ],
  refine absolutely_continuous.mk (λ s hsm hs, _),
  rw [map_apply hg.measurable hsm, with_density_apply _ (hg.measurable hsm)],
  have := hg.absolutely_continuous hs,
  rw map_apply hg.measurable hsm at this,
  exact set_lintegral_measure_zero _ _ this,
end

lemma quasi_measure_preserving_has_pdf' [is_finite_measure ℙ] [sigma_finite ν]
  {X : α → E} [has_pdf X ℙ μ] {g : E → F} (hg : quasi_measure_preserving g μ ν) :
  has_pdf (g ∘ X) ℙ ν :=
begin
  haveI : is_finite_measure (map g (map X ℙ)) :=
    @is_finite_measure_map _ _ _ _ (map X ℙ)
      (is_finite_measure_map ℙ (has_pdf.measurable X ℙ μ)) _ hg.measurable,
  exact quasi_measure_preserving_has_pdf hg infer_instance,
end

end

section real

variables [is_finite_measure ℙ] {X : α → ℝ}

/-- A real-valued random variable `X` `has_pdf X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
lemma real.has_pdf_iff_of_measurable (hX : measurable X) : has_pdf X ℙ ↔ map X ℙ ≪ volume :=
begin
  haveI : is_finite_measure (map X ℙ) := is_finite_measure_map ℙ hX,
  rw [has_pdf_iff_of_measurable hX, and_iff_right_iff_imp],
  exact λ h, infer_instance,
end

lemma real.has_pdf_iff : has_pdf X ℙ ↔ measurable X ∧ map X ℙ ≪ volume :=
begin
  by_cases hX : measurable X,
  { rw [real.has_pdf_iff_of_measurable hX, iff_and_self],
    exact λ h, hX,
    apply_instance },
  { exact ⟨λ h, false.elim (hX h.pdf'.1), λ h, false.elim (hX h.1)⟩, }
end

/-- If `X` is a real-valued random variable that has pdf `f`, then the expectation of `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
lemma integral_mul_eq_integral [has_pdf X ℙ] :
  ∫ x, x * (pdf X ℙ volume x).to_real = ∫ x, X x ∂ℙ :=
integral_fun_mul_eq_integral measurable_id

lemma has_finite_integral_mul {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞}
  (hg : pdf X ℙ =ᵐ[volume] g) (hgi : ∫⁻ x, ∥f x∥₊ * g x ≠ ∞) :
  has_finite_integral (λ x, f x * (pdf X ℙ volume x).to_real) :=
begin
  rw has_finite_integral,
  have : (λ x, ↑∥f x∥₊ * g x) =ᵐ[volume] (λ x, ∥f x * (pdf X ℙ volume x).to_real∥₊),
  { refine ae_eq_trans (filter.eventually_eq.mul (ae_eq_refl (λ x, ∥f x∥₊))
      (ae_eq_trans hg.symm of_real_to_real_ae_eq.symm)) _,
    simp_rw [← smul_eq_mul, nnnorm_smul, ennreal.coe_mul, smul_eq_mul],
    refine filter.eventually_eq.mul (ae_eq_refl _) _,
    convert ae_eq_refl _,
    ext1 x,
    exact real.ennnorm_eq_of_real ennreal.to_real_nonneg },
  rwa [lt_top_iff_ne_top, ← lintegral_congr_ae this],
end

end real

section

/-! **Uniform Distribution** -/

/-- A random variable `X` has uniform distribution if it has a probability density function `f`
with compact support `s` such that `f = (μ s)⁻¹ 1ₛ` a.e. where `1ₛ` is the indicator function
for `s`.
We require compact support since otherwise the expectation might not be finite. -/
class uniform {m : measurable_space α} (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac)
  extends has_pdf X ℙ μ :=
(support' : set E) (compact_support' : is_compact support')
(support_not_null' : 0 < μ support')
(uniform' : pdf X ℙ μ =ᵐ[μ] support'.indicator ((μ support')⁻¹ • 1))

def is_uniform {m : measurable_space α} (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac)
  (support : set E) :=
pdf X ℙ μ =ᵐ[μ] support.indicator ((μ support)⁻¹ • 1)

namespace uniform

/-- The support of the probability density function of a random variable of uniform distribution. -/
def support {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] : set E :=
hX.support'

lemma is_compact_support {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] :
  is_compact (support X ℙ μ) :=
hX.compact_support'

@[measurability]
lemma measurable_set_support {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] :
  measurable_set (support X ℙ μ) :=
(is_compact_support X ℙ μ).is_closed.measurable_set

lemma support_not_null {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] :
  0 < μ (support X ℙ μ) :=
hX.support_not_null'

lemma pdf_ae_eq {m : measurable_space α} (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac)
  [hX : uniform X ℙ μ] :
  pdf X ℙ μ =ᵐ[μ] (support X ℙ μ).indicator ((μ (support X ℙ μ))⁻¹ • 1) :=
hX.uniform'

lemma pdf_to_real_ae_eq {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] :
  (λ x, (pdf X ℙ μ x).to_real) =ᵐ[μ]
  (λ x, ((support X ℙ μ).indicator ((μ (support X ℙ μ))⁻¹ • (1 : E → ℝ≥0∞)) x).to_real) :=
filter.eventually_eq.fun_comp (pdf_ae_eq X ℙ μ) ennreal.to_real

variables [is_finite_measure ℙ] {X : α → ℝ} [uniform X ℙ volume]

lemma mul_pdf_integrable (hX : measurable X) :
  integrable (λ x : ℝ, x * (pdf X ℙ volume x).to_real) volume :=
begin
  by_cases hsupp : volume (support X ℙ) = ∞,
  { have : pdf X ℙ =ᵐ[volume] 0,
    { refine ae_eq_trans (pdf_ae_eq X ℙ) _,
      simp [hsupp] },
    refine integrable.congr (integrable_zero _ _ _) _,
    rw [(by simp : (λ x, 0 : ℝ → ℝ) = (λ x, x * (0 : ℝ≥0∞).to_real))],
    refine filter.eventually_eq.mul (ae_eq_refl _)
      (filter.eventually_eq.fun_comp this.symm ennreal.to_real) },
  refine ⟨ae_measurable_id'.mul (measurable_pdf X ℙ).ae_measurable.ennreal_to_real, _⟩,
  refine has_finite_integral_mul (pdf_ae_eq X ℙ) _,
  set ind := (volume (support X ℙ))⁻¹ • (1 : ℝ → ℝ≥0∞) with hind,
  have : ∀ x, ↑∥x∥₊ * (support X ℙ).indicator ind x =
    (support X ℙ).indicator (λ x, ∥x∥₊ * ind x) x :=
      λ x, ((support X ℙ).indicator_mul_right (λ x, ↑∥x∥₊) ind).symm,
  simp only [this, lintegral_indicator _ (measurable_set_support X ℙ), hind, mul_one,
             algebra.id.smul_eq_mul, pi.one_apply, pi.smul_apply],
  rw lintegral_mul_const _ measurable_nnnorm.coe_nnreal_ennreal,
  { exact (ennreal.mul_lt_top (set_lintegral_lt_top_of_is_compact
      hsupp (is_compact_support X ℙ) continuous_nnnorm).ne
      (ennreal.inv_lt_top.2 (support_not_null X ℙ)).ne).ne },
  { apply_instance }
end

/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
lemma integral_eq (hX : measurable X) :
  ∫ x, X x ∂ℙ =
  (volume (support X ℙ))⁻¹.to_real * ∫ x in support X ℙ, x ∂(volume) :=
begin
  rw ← integral_mul_eq_integral,
  all_goals { try { apply_instance } },
  rw integral_congr_ae (filter.eventually_eq.mul (ae_eq_refl _) (pdf_to_real_ae_eq X ℙ)),
  have : ∀ x, x * ((support X ℙ).indicator
      ((volume (support X ℙ))⁻¹ • (1 : ℝ → ℝ≥0∞)) x).to_real =
    x * ((support X ℙ).indicator
      ((volume (support X ℙ))⁻¹.to_real • (1 : ℝ → ℝ)) x),
  { refine λ x, congr_arg ((*) x) _,
    by_cases hx : x ∈ support X ℙ,
    { simp [set.indicator_of_mem hx] },
    { simp [set.indicator_of_not_mem hx] }},
  simp_rw [this, ← (support X ℙ).indicator_mul_right (λ x, x),
           integral_indicator (measurable_set_support X ℙ)],
  change ∫ x in support X ℙ, x * ((volume (support X ℙ))⁻¹.to_real • 1) ∂(volume) = _,
  rw [integral_mul_right, mul_comm, algebra.id.smul_eq_mul, mul_one],
end .

end uniform

end

end pdf

end measure_theory
