/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import analysis.calculus.bump_function_inner
import analysis.calculus.parametric_integral
import measure_theory.constructions.prod.integral
import measure_theory.function.locally_integrable
import measure_theory.group.integration
import measure_theory.group.prod
import measure_theory.integral.interval_integral

/-!
# Convolution of functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the convolution on two functions, i.e. `x ↦ ∫ f(t)g(x - t) ∂t`.
In the general case, these functions can be vector-valued, and have an arbitrary (additive)
group as domain. We use a continuous bilinear operation `L` on these function values as
"multiplication". The domain must be equipped with a Haar measure `μ`
(though many individual results have weaker conditions on `μ`).

For many applications we can take `L = lsmul ℝ ℝ` or `L = mul ℝ ℝ`.

We also define `convolution_exists` and `convolution_exists_at` to state that the convolution is
well-defined (everywhere or at a single point). These conditions are needed for pointwise
computations (e.g. `convolution_exists_at.distrib_add`), but are generally not stong enough for any
local (or global) properties of the convolution. For this we need stronger assumptions on `f`
and/or `g`, and generally if we impose stronger conditions on one of the functions, we can impose
weaker conditions on the other.
We have proven many of the properties of the convolution assuming one of these functions
has compact support (in which case the other function only needs to be locally integrable).
We still need to prove the properties for other pairs of conditions (e.g. both functions are
rapidly decreasing)

# Design Decisions

We use a bilinear map `L` to "multiply" the two functions in the integrand.
This generality has several advantages

* This allows us to compute the total derivative of the convolution, in case the functions are
  multivariate. The total derivative is again a convolution, but where the codomains of the
  functions can be higher-dimensional. See `has_compact_support.has_fderiv_at_convolution_right`.
* This allows us to use `@[to_additive]` everywhere (which would not be possible if we would use
  `mul`/`smul` in the integral, since `@[to_additive]` will incorrectly also try to additivize
  those definitions).
* We need to support the case where at least one of the functions is vector-valued, but if we use
  `smul` to multiply the functions, that would be an asymmetric definition.

# Main Definitions
* `convolution f g L μ x = (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ` is the convolution of
  `f` and `g` w.r.t. the continuous bilinear map `L` and measure `μ`.
* `convolution_exists_at f g x L μ` states that the convolution `(f ⋆[L, μ] g) x` is well-defined
  (i.e. the integral exists).
* `convolution_exists f g L μ` states that the convolution `f ⋆[L, μ] g` is well-defined at each
  point.

# Main Results
* `has_compact_support.has_fderiv_at_convolution_right` and
  `has_compact_support.has_fderiv_at_convolution_left`: we can compute the total derivative
  of the convolution as a convolution with the total derivative of the right (left) function.
* `has_compact_support.cont_diff_convolution_right` and
  `has_compact_support.cont_diff_convolution_left`: the convolution is `𝒞ⁿ` if one of the functions
  is `𝒞ⁿ` with compact support and the other function in locally integrable.

Versions of these statements for functions depending on a parameter are also given.

* `convolution_tendsto_right`: Given a sequence of nonnegative normalized functions whose support
  tends to a small neighborhood around `0`, the convolution tends to the right argument.
  This is specialized to bump functions in `cont_diff_bump.convolution_tendsto_right`.

# Notation
The following notations are localized in the locale `convolution`:
* `f ⋆[L, μ] g` for the convolution. Note: you have to use parentheses to apply the convolution
  to an argument: `(f ⋆[L, μ] g) x`.
* `f ⋆[L] g := f ⋆[L, volume] g`
* `f ⋆ g := f ⋆[lsmul ℝ ℝ] g`

# To do
* Existence and (uniform) continuity of the convolution if
  one of the maps is in `ℒ^p` and the other in `ℒ^q` with `1 / p + 1 / q = 1`.
  This might require a generalization of `measure_theory.mem_ℒp.smul` where `smul` is generalized
  to a continuous bilinear map.
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255K)
* The convolution is a `ae_strongly_measurable` function
  (see e.g. [Fremlin, *Measure Theory* (volume 2)][fremlin_vol2], 255I).
* Prove properties about the convolution if both functions are rapidly decreasing.
* Use `@[to_additive]` everywhere
-/

open set function filter measure_theory measure_theory.measure topological_space
open continuous_linear_map metric
open_locale pointwise topology nnreal filter

universes u𝕜 uG uE uE' uE'' uF uF' uF'' uP

variables {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE} {E' : Type uE'} {E'' : Type uE''}
{F : Type uF} {F' : Type uF'} {F'' : Type uF''} {P : Type uP}

variables [normed_add_comm_group E] [normed_add_comm_group E'] [normed_add_comm_group E'']
  [normed_add_comm_group F]
  {f f' : G → E} {g g' : G → E'} {x x' : G} {y y' : E}

section nontrivially_normed_field

variables [nontrivially_normed_field 𝕜]
variables [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E''] [normed_space 𝕜 F]
variables (L : E →L[𝕜] E' →L[𝕜] F)

section no_measurability

variables [add_group G] [topological_space G]

lemma convolution_integrand_bound_right_of_le_of_subset
  {C : ℝ} (hC : ∀ i, ‖g i‖ ≤ C) {x t : G} {s u : set G} (hx : x ∈ s) (hu : - tsupport g + s ⊆ u) :
  ‖L (f t) (g (x - t))‖ ≤ u.indicator (λ t, ‖L‖ * ‖f t‖ * C) t :=
begin
  refine le_indicator (λ t ht, _) (λ t ht, _) t,
  { refine (L.le_op_norm₂ _ _).trans _,
    apply mul_le_mul_of_nonneg_left (hC _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) },
  { have : x - t ∉ support g,
    { refine mt (λ hxt, _) ht,
      apply hu,
      refine ⟨_, _, set.neg_mem_neg.mpr (subset_closure hxt), hx, _⟩,
      rw [neg_sub, sub_add_cancel] },
    rw [nmem_support.mp this, (L _).map_zero, norm_zero] }
end

lemma has_compact_support.convolution_integrand_bound_right_of_subset (hcg : has_compact_support g)
  (hg : continuous g) {x t : G} {s u : set G} (hx : x ∈ s) (hu : - tsupport g + s ⊆ u) :
  ‖L (f t) (g (x - t))‖ ≤ u.indicator (λ t, ‖L‖ * ‖f t‖ * (⨆ i, ‖g i‖)) t :=
begin
  apply convolution_integrand_bound_right_of_le_of_subset _ (λ i, _) hx hu,
  exact le_csupr (hg.norm.bdd_above_range_of_has_compact_support hcg.norm) _,
end

lemma has_compact_support.convolution_integrand_bound_right (hcg : has_compact_support g)
  (hg : continuous g) {x t : G} {s : set G} (hx : x ∈ s) :
  ‖L (f t) (g (x - t))‖ ≤ (- tsupport g + s).indicator (λ t, ‖L‖ * ‖f t‖ * (⨆ i, ‖g i‖)) t :=
hcg.convolution_integrand_bound_right_of_subset L hg hx subset.rfl

lemma continuous.convolution_integrand_fst [has_continuous_sub G] (hg : continuous g) (t : G) :
  continuous (λ x, L (f t) (g (x - t))) :=
L.continuous₂.comp₂ continuous_const $ hg.comp $ continuous_id.sub continuous_const

lemma has_compact_support.convolution_integrand_bound_left (hcf : has_compact_support f)
  (hf : continuous f) {x t : G} {s : set G} (hx : x ∈ s) :
  ‖L (f (x - t)) (g t)‖ ≤ (- tsupport f + s).indicator (λ t, ‖L‖ * (⨆ i, ‖f i‖) * ‖g t‖) t :=
by { convert hcf.convolution_integrand_bound_right L.flip hf hx,
  simp_rw [L.op_norm_flip, mul_right_comm] }

end no_measurability

section measurability

variables [measurable_space G] {μ ν : measure G}

/-- The convolution of `f` and `g` exists at `x` when the function `t ↦ L (f t) (g (x - t))` is
integrable. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists_at [has_sub G] (f : G → E) (g : G → E') (x : G) (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
integrable (λ t, L (f t) (g (x - t))) μ

/-- The convolution of `f` and `g` exists when the function `t ↦ L (f t) (g (x - t))` is integrable
for all `x : G`. There are various conditions on `f` and `g` to prove this. -/
def convolution_exists [has_sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : Prop :=
∀ x : G, convolution_exists_at f g x L μ

section convolution_exists

variables {L}
lemma convolution_exists_at.integrable [has_sub G] {x : G} (h : convolution_exists_at f g x L μ) :
  integrable (λ t, L (f t) (g (x - t))) μ :=
h

variables (L)

section group

variables [add_group G]

lemma measure_theory.ae_strongly_measurable.convolution_integrand'
  [has_measurable_add₂ G] [has_measurable_neg G] [sigma_finite ν]
  (hf : ae_strongly_measurable f ν)
  (hg : ae_strongly_measurable g $ map (λ (p : G × G), p.1 - p.2) (μ.prod ν)) :
  ae_strongly_measurable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
L.ae_strongly_measurable_comp₂ hf.snd $ hg.comp_measurable measurable_sub


section

variables [has_measurable_add G] [has_measurable_neg G]

lemma measure_theory.ae_strongly_measurable.convolution_integrand_snd'
  (hf : ae_strongly_measurable f μ) {x : G}
  (hg : ae_strongly_measurable g $ map (λ t, x - t) μ) :
  ae_strongly_measurable (λ t, L (f t) (g (x - t))) μ :=
L.ae_strongly_measurable_comp₂ hf $ hg.comp_measurable $ measurable_id.const_sub x

lemma measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd'
  {x : G} (hf : ae_strongly_measurable f $ map (λ t, x - t) μ)
  (hg : ae_strongly_measurable g μ) : ae_strongly_measurable (λ t, L (f (x - t)) (g t)) μ :=
L.ae_strongly_measurable_comp₂ (hf.comp_measurable $ measurable_id.const_sub x) hg

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that `f` is integrable on a set `s` and `g` is bounded and ae strongly measurable
on `x₀ - s` (note that both properties hold if `g` is continuous with compact support). -/
lemma bdd_above.convolution_exists_at' {x₀ : G}
  {s : set G} (hbg : bdd_above ((λ i, ‖g i‖) '' ((λ t, - t + x₀) ⁻¹' s)))
  (hs : measurable_set s) (h2s : support (λ t, L (f t) (g (x₀ - t))) ⊆ s)
  (hf : integrable_on f s μ) (hmg : ae_strongly_measurable g $ map (λ t, x₀ - t) (μ.restrict s)) :
  convolution_exists_at f g x₀ L μ :=
begin
  rw [convolution_exists_at, ← integrable_on_iff_integrable_of_support_subset h2s],
  set s' := (λ t, - t + x₀) ⁻¹' s,
  have : ∀ᵐ (t : G) ∂(μ.restrict s),
    ‖L (f t) (g (x₀ - t))‖ ≤ s.indicator (λ t, ‖L‖ * ‖f t‖ * ⨆ i : s', ‖g i‖) t,
  { refine eventually_of_forall _,
    refine le_indicator (λ t ht, _) (λ t ht, _),
    { refine (L.le_op_norm₂ _ _).trans _,
      refine mul_le_mul_of_nonneg_left
        (le_csupr_set hbg $ mem_preimage.mpr _)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      rwa [neg_sub, sub_add_cancel] },
    { have : t ∉ support (λ t, L (f t) (g (x₀ - t))) := mt (λ h, h2s h) ht,
      rw [nmem_support.mp this, norm_zero] } },
  refine integrable.mono' _ _ this,
  { rw [integrable_indicator_iff hs], exact ((hf.norm.const_mul _).mul_const _).integrable_on },
  { exact hf.ae_strongly_measurable.convolution_integrand_snd' L hmg }
end

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
lemma convolution_exists_at.of_norm' {x₀ : G}
  (h : convolution_exists_at (λ x, ‖f x‖) (λ x, ‖g x‖) x₀ (mul ℝ ℝ) μ)
  (hmf : ae_strongly_measurable f μ)
  (hmg : ae_strongly_measurable g $ map (λ t, x₀ - t) μ) :
  convolution_exists_at f g x₀ L μ :=
begin
  refine (h.const_mul ‖L‖).mono' (hmf.convolution_integrand_snd' L hmg)
    (eventually_of_forall $ λ x, _),
  rw [mul_apply', ← mul_assoc],
  apply L.le_op_norm₂,
end

end

section left
variables [has_measurable_add₂ G] [has_measurable_neg G] [sigma_finite μ] [is_add_right_invariant μ]

lemma measure_theory.ae_strongly_measurable.convolution_integrand_snd
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
  (x : G) : ae_strongly_measurable (λ t, L (f t) (g (x - t))) μ :=
hf.convolution_integrand_snd' L $ hg.mono' $
  (quasi_measure_preserving_sub_left_of_right_invariant μ x).absolutely_continuous

lemma measure_theory.ae_strongly_measurable.convolution_integrand_swap_snd
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ)
  (x : G) : ae_strongly_measurable (λ t, L (f (x - t)) (g t)) μ :=
(hf.mono' (quasi_measure_preserving_sub_left_of_right_invariant μ x).absolutely_continuous)
  .convolution_integrand_swap_snd' L hg

/-- If `‖f‖ *[μ] ‖g‖` exists, then `f *[L, μ] g` exists. -/
lemma convolution_exists_at.of_norm {x₀ : G}
  (h : convolution_exists_at (λ x, ‖f x‖) (λ x, ‖g x‖) x₀ (mul ℝ ℝ) μ)
  (hmf : ae_strongly_measurable f μ)
  (hmg : ae_strongly_measurable g μ) :
  convolution_exists_at f g x₀ L μ :=
h.of_norm' L hmf $ hmg.mono'
  (quasi_measure_preserving_sub_left_of_right_invariant μ x₀).absolutely_continuous

end left

section right

variables [has_measurable_add₂ G] [has_measurable_neg G]
[sigma_finite μ] [is_add_right_invariant μ] [sigma_finite ν]

lemma measure_theory.ae_strongly_measurable.convolution_integrand
  (hf : ae_strongly_measurable f ν) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
hf.convolution_integrand' L $ hg.mono'
  (quasi_measure_preserving_sub_of_right_invariant μ ν).absolutely_continuous

lemma measure_theory.integrable.convolution_integrand (hf : integrable f ν) (hg : integrable g μ) :
  integrable (λ p : G × G, L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
begin
  have h_meas : ae_strongly_measurable (λ (p : G × G), L (f p.2) (g (p.1 - p.2))) (μ.prod ν) :=
    hf.ae_strongly_measurable.convolution_integrand L hg.ae_strongly_measurable,
  have h2_meas : ae_strongly_measurable (λ (y : G), ∫ (x : G), ‖L (f y) (g (x - y))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right',
  simp_rw [integrable_prod_iff' h_meas],
  refine ⟨eventually_of_forall (λ t, (L (f t)).integrable_comp (hg.comp_sub_right t)), _⟩,
  refine integrable.mono' _ h2_meas (eventually_of_forall $
    λ t, (_ : _ ≤ ‖L‖ * ‖f t‖ * ∫ x, ‖g (x - t)‖ ∂μ)),
  { simp_rw [integral_sub_right_eq_self (λ t, ‖ g t ‖)],
    exact (hf.norm.const_mul _).mul_const _ },
  { simp_rw [← integral_mul_left],
    rw [real.norm_of_nonneg],
    { exact integral_mono_of_nonneg (eventually_of_forall $ λ t, norm_nonneg _)
        ((hg.comp_sub_right t).norm.const_mul _) (eventually_of_forall $ λ t, L.le_op_norm₂ _ _) },
    exact integral_nonneg (λ x, norm_nonneg _) }
end

lemma measure_theory.integrable.ae_convolution_exists (hf : integrable f ν) (hg : integrable g μ) :
  ∀ᵐ x ∂μ, convolution_exists_at f g x L ν :=
((integrable_prod_iff $ hf.ae_strongly_measurable.convolution_integrand L
  hg.ae_strongly_measurable).mp $ hf.convolution_integrand L hg).1

end right

variables [topological_space G] [topological_add_group G] [borel_space G]

lemma has_compact_support.convolution_exists_at {x₀ : G}
  (h : has_compact_support (λ t, L (f t) (g (x₀ - t)))) (hf : locally_integrable f μ)
  (hg : continuous g) : convolution_exists_at f g x₀ L μ :=
begin
  let u := (homeomorph.neg G).trans (homeomorph.add_right x₀),
  let v := (homeomorph.neg G).trans (homeomorph.add_left x₀),
  apply ((u.is_compact_preimage.mpr h).bdd_above_image hg.norm.continuous_on).convolution_exists_at'
    L is_closed_closure.measurable_set subset_closure (hf.integrable_on_is_compact h),
  have A : ae_strongly_measurable (g ∘ ⇑v)
    (μ.restrict (tsupport (λ (t : G), (L (f t)) (g (x₀ - t))))),
  { apply (hg.comp v.continuous).continuous_on.ae_strongly_measurable_of_is_compact h,
    exact (is_closed_tsupport _).measurable_set },
  convert ((v.continuous.measurable.measure_preserving
    (μ.restrict (tsupport (λ t, L (f t) (g (x₀ - t)))))).ae_strongly_measurable_comp_iff
    v.to_measurable_equiv.measurable_embedding).1 A,
  ext x,
  simp only [homeomorph.neg, sub_eq_add_neg, coe_to_add_units, homeomorph.trans_apply,
    equiv.neg_apply, equiv.to_fun_as_coe, homeomorph.homeomorph_mk_coe, equiv.coe_fn_mk,
    homeomorph.coe_add_left],
end

lemma has_compact_support.convolution_exists_right
  (hcg : has_compact_support g) (hf : locally_integrable f μ) (hg : continuous g) :
  convolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.convolution_exists_at L _ hf hg,
  refine (hcg.comp_homeomorph (homeomorph.sub_left x₀)).mono _,
  refine λ t, mt (λ ht : g (x₀ - t) = 0, _),
  simp_rw [ht, (L _).map_zero]
end

lemma has_compact_support.convolution_exists_left_of_continuous_right
  (hcf : has_compact_support f) (hf : locally_integrable f μ) (hg : continuous g) :
  convolution_exists f g L μ :=
begin
  intro x₀,
  refine has_compact_support.convolution_exists_at L _ hf hg,
  refine hcf.mono _,
  refine λ t, mt (λ ht : f t = 0, _),
  simp_rw [ht, L.map_zero₂]
end

end group

section comm_group

variables [add_comm_group G]

section measurable_group

variables [has_measurable_neg G] [is_add_left_invariant μ]

/-- A sufficient condition to prove that `f ⋆[L, μ] g` exists.
We assume that the integrand has compact support and `g` is bounded on this support (note that
both properties hold if `g` is continuous with compact support). We also require that `f` is
integrable on the support of the integrand, and that both functions are strongly measurable.

This is a variant of `bdd_above.convolution_exists_at'` in an abelian group with a left-invariant
measure. This allows us to state the boundedness and measurability of `g` in a more natural way. -/
lemma bdd_above.convolution_exists_at [has_measurable_add₂ G] [sigma_finite μ] {x₀ : G}
  {s : set G} (hbg : bdd_above ((λ i, ‖g i‖) '' ((λ t, x₀ - t) ⁻¹' s)))
  (hs : measurable_set s) (h2s : support (λ t, L (f t) (g (x₀ - t))) ⊆ s)
  (hf : integrable_on f s μ) (hmg : ae_strongly_measurable g μ) :
    convolution_exists_at f g x₀ L μ :=
begin
  refine bdd_above.convolution_exists_at' L _ hs h2s hf _,
  { simp_rw [← sub_eq_neg_add, hbg] },
  { have : ae_strongly_measurable g (map (λ (t : G), x₀ - t) μ), from hmg.mono'
      (quasi_measure_preserving_sub_left_of_right_invariant μ x₀).absolutely_continuous,
    apply this.mono_measure,
    exact map_mono_of_ae_measurable restrict_le_self
      (measurable_const.sub measurable_id').ae_measurable }
end

variables {L} [has_measurable_add G] [is_neg_invariant μ]

lemma convolution_exists_at_flip :
  convolution_exists_at g f x L.flip μ ↔ convolution_exists_at f g x L μ :=
by simp_rw [convolution_exists_at, ← integrable_comp_sub_left (λ t, L (f t) (g (x - t))) x,
  sub_sub_cancel, flip_apply]

lemma convolution_exists_at.integrable_swap (h : convolution_exists_at f g x L μ) :
  integrable (λ t, L (f (x - t)) (g t)) μ :=
by { convert h.comp_sub_left x, simp_rw [sub_sub_self] }

lemma convolution_exists_at_iff_integrable_swap :
  convolution_exists_at f g x L μ ↔ integrable (λ t, L (f (x - t)) (g t)) μ :=
convolution_exists_at_flip.symm

end measurable_group

variables [topological_space G] [topological_add_group G] [borel_space G]
 [is_add_left_invariant μ] [is_neg_invariant μ]

lemma has_compact_support.convolution_exists_left
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
  convolution_exists f g L μ :=
λ x₀, convolution_exists_at_flip.mp $ hcf.convolution_exists_right L.flip hg hf x₀

lemma has_compact_support.convolution_exists_right_of_continuous_left
  (hcg : has_compact_support g) (hf : continuous f) (hg : locally_integrable g μ) :
  convolution_exists f g L μ :=
λ x₀, convolution_exists_at_flip.mp $
  hcg.convolution_exists_left_of_continuous_right L.flip hg hf x₀

end comm_group

end convolution_exists

variables [normed_space ℝ F] [complete_space F]

/-- The convolution of two functions `f` and `g` with respect to a continuous bilinear map `L` and
measure `μ`. It is defined to be `(f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ`. -/
noncomputable def convolution [has_sub G] (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F)
  (μ : measure G . volume_tac) : G → F :=
λ x, ∫ t, L (f t) (g (x - t)) ∂μ

localized "notation (name := convolution) f ` ⋆[`:67 L:67 `, ` μ:67 `] `:0 g:66 :=
  convolution f g L μ" in convolution
localized "notation (name := convolution.volume) f ` ⋆[`:67 L:67 `]`:0 g:66 :=
  convolution f g L measure_theory.measure_space.volume" in convolution
localized "notation (name := convolution.lsmul) f ` ⋆ `:67 g:66 :=
  convolution f g (continuous_linear_map.lsmul ℝ ℝ) measure_theory.measure_space.volume"
  in convolution

lemma convolution_def [has_sub G] : (f ⋆[L, μ] g) x = ∫ t, L (f t) (g (x - t)) ∂μ := rfl

/-- The definition of convolution where the bilinear operator is scalar multiplication.
Note: it often helps the elaborator to give the type of the convolution explicitly. -/
lemma convolution_lsmul [has_sub G] {f : G → 𝕜} {g : G → F} :
  (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f t • g (x - t) ∂μ := rfl

/-- The definition of convolution where the bilinear operator is multiplication. -/
lemma convolution_mul [has_sub G] [normed_space ℝ 𝕜] [complete_space 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
  (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f t * g (x - t) ∂μ := rfl

section group

variables {L} [add_group G]

lemma smul_convolution [smul_comm_class ℝ 𝕜 F]
  {y : 𝕜} : (y • f) ⋆[L, μ] g = y • (f ⋆[L, μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, L.map_smul₂] }

lemma convolution_smul [smul_comm_class ℝ 𝕜 F]
  {y : 𝕜} : f ⋆[L, μ] (y • g) = y • (f ⋆[L, μ] g) :=
by { ext, simp only [pi.smul_apply, convolution_def, ← integral_smul, (L _).map_smul] }

@[simp] lemma zero_convolution : 0 ⋆[L, μ] g = 0 :=
by { ext, simp_rw [convolution_def, pi.zero_apply, L.map_zero₂, integral_zero] }

@[simp] lemma convolution_zero : f ⋆[L, μ] 0 = 0 :=
by { ext, simp_rw [convolution_def, pi.zero_apply, (L _).map_zero, integral_zero] }

lemma convolution_exists_at.distrib_add {x : G} (hfg : convolution_exists_at f g x L μ)
  (hfg' : convolution_exists_at f g' x L μ) :
  (f ⋆[L, μ] (g + g')) x = (f ⋆[L, μ] g) x + (f ⋆[L, μ] g') x :=
by simp only [convolution_def, (L _).map_add, pi.add_apply, integral_add hfg hfg']

lemma convolution_exists.distrib_add (hfg : convolution_exists f g L μ)
  (hfg' : convolution_exists f g' L μ) : f ⋆[L, μ] (g + g') = f ⋆[L, μ] g + f ⋆[L, μ] g' :=
by { ext, exact (hfg x).distrib_add (hfg' x) }

lemma convolution_exists_at.add_distrib {x : G} (hfg : convolution_exists_at f g x L μ)
  (hfg' : convolution_exists_at f' g x L μ) :
  ((f + f') ⋆[L, μ] g) x = (f ⋆[L, μ] g) x + (f' ⋆[L, μ] g) x :=
by simp only [convolution_def, L.map_add₂, pi.add_apply, integral_add hfg hfg']

lemma convolution_exists.add_distrib (hfg : convolution_exists f g L μ)
  (hfg' : convolution_exists f' g L μ) : (f + f') ⋆[L, μ] g = f ⋆[L, μ] g + f' ⋆[L, μ] g :=
by { ext, exact (hfg x).add_distrib (hfg' x) }

lemma convolution_mono_right {f g g' : G → ℝ}
  (hfg : convolution_exists_at f g x (lsmul ℝ ℝ) μ)
  (hfg' : convolution_exists_at f g' x (lsmul ℝ ℝ) μ)
  (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ g' x) :
  (f ⋆[lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[lsmul ℝ ℝ, μ] g') x :=
begin
  apply integral_mono hfg hfg',
  simp only [lsmul_apply, algebra.id.smul_eq_mul],
  assume t,
  apply mul_le_mul_of_nonneg_left (hg _) (hf _),
end

lemma convolution_mono_right_of_nonneg {f g g' : G → ℝ}
  (hfg' : convolution_exists_at f g' x (lsmul ℝ ℝ) μ)
  (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g x ≤ g' x) (hg' : ∀ x, 0 ≤ g' x) :
  (f ⋆[lsmul ℝ ℝ, μ] g) x ≤ (f ⋆[lsmul ℝ ℝ, μ] g') x :=
begin
  by_cases H : convolution_exists_at f g x (lsmul ℝ ℝ) μ,
  { exact convolution_mono_right H hfg' hf hg },
  have : (f ⋆[lsmul ℝ ℝ, μ] g) x = 0 := integral_undef H,
  rw this,
  exact integral_nonneg (λ y, mul_nonneg (hf y) (hg' (x - y))),
end

variables (L)

lemma convolution_congr [has_measurable_add₂ G] [has_measurable_neg G]
  [sigma_finite μ] [is_add_right_invariant μ] (h1 : f =ᵐ[μ] f') (h2 : g =ᵐ[μ] g') :
  f ⋆[L, μ] g = f' ⋆[L, μ] g' :=
begin
  ext x,
  apply integral_congr_ae,
  exact (h1.prod_mk $ h2.comp_tendsto
    (quasi_measure_preserving_sub_left_of_right_invariant μ x).tendsto_ae).fun_comp ↿(λ x y, L x y)
end

lemma support_convolution_subset_swap : support (f ⋆[L, μ] g) ⊆ support g + support f :=
begin
  intros x h2x,
  by_contra hx,
  apply h2x,
  simp_rw [set.mem_add, not_exists, not_and_distrib, nmem_support] at hx,
  rw [convolution_def],
  convert integral_zero G F,
  ext t,
  rcases hx (x - t) t with h|h|h,
  { rw [h, (L _).map_zero] },
  { rw [h, L.map_zero₂] },
  { exact (h $ sub_add_cancel x t).elim }
end

section
variables [has_measurable_add₂ G] [has_measurable_neg G] [sigma_finite μ] [is_add_right_invariant μ]

lemma measure_theory.integrable.integrable_convolution (hf : integrable f μ) (hg : integrable g μ) :
  integrable (f ⋆[L, μ] g) μ :=
(hf.convolution_integrand L hg).integral_prod_left

end

variables [topological_space G]
variables [topological_add_group G]

lemma has_compact_support.convolution [t2_space G] (hcf : has_compact_support f)
  (hcg : has_compact_support g) : has_compact_support (f ⋆[L, μ] g) :=
is_compact_of_is_closed_subset (hcg.is_compact.add hcf) is_closed_closure $ closure_minimal
  ((support_convolution_subset_swap L).trans $ add_subset_add subset_closure subset_closure)
  (hcg.is_compact.add hcf).is_closed

variables [borel_space G] [first_countable_topology G]
[topological_space P] [first_countable_topology P]

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in a subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
not assuming `t2_space G`. -/
lemma continuous_on_convolution_right_with_param'
  {g : P → G → E'} {s : set P} {k : set G} (hk : is_compact k) (h'k : is_closed k)
  (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : continuous_on (↿g) (s ×ˢ univ)) :
  continuous_on (λ (q : P × G), (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) :=
begin
  assume q₀ hq₀,
  replace hq₀ : q₀.1 ∈ s, by simpa only [mem_prod, mem_univ, and_true] using hq₀,
  have A : ∀ p ∈ s, continuous (g p),
  { assume p hp,
    apply hg.comp_continuous (continuous_const.prod_mk continuous_id') (λ x, _),
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true] using hp },
  have B : ∀ p ∈ s, tsupport (g p) ⊆ k :=
    λ p hp, closure_minimal (support_subset_iff'.2 (λ z hz, hgs _ _ hp hz)) h'k,
  /- We find a small neighborhood of `{q₀.1} × k` on which the function is uniformly bounded.
    This follows from the continuity at all points of the compact set `k`. -/
  obtain ⟨w, C, w_open, q₀w, Cnonneg, hw⟩ :
    ∃ w C, is_open w ∧ q₀.1 ∈ w ∧ 0 ≤ C ∧ ∀ p x, p ∈ w ∩ s → ‖g p x‖ ≤ C,
  { have A : is_compact ({q₀.1} ×ˢ k), from is_compact_singleton.prod hk,
    obtain ⟨t, kt, t_open, ht⟩ :
      ∃ t, {q₀.1} ×ˢ k ⊆ t ∧ is_open t ∧ bounded (↿g '' (t ∩ s ×ˢ univ)),
    { apply exists_is_open_bounded_image_inter_of_is_compact_of_continuous_on A _ hg,
      simp only [prod_subset_prod_iff, hq₀, singleton_subset_iff, subset_univ, and_self, true_or] },
    obtain ⟨C, Cpos, hC⟩ : ∃ C, 0 < C ∧ (↿g) '' (t ∩ s ×ˢ univ) ⊆ closed_ball (0 : E') C,
      from ht.subset_ball_lt 0 0,
    obtain ⟨w, w_open, q₀w, hw⟩ : ∃ w, is_open w ∧ q₀.1 ∈ w ∧ w ×ˢ k ⊆ t,
    { obtain ⟨w, v, w_open, v_open, hw, hv, hvw⟩ :
        ∃ (w : set P) (v : set G), is_open w ∧ is_open v ∧ {q₀.fst} ⊆ w ∧ k ⊆ v ∧ w ×ˢ v ⊆ t,
        from generalized_tube_lemma is_compact_singleton hk t_open kt,
      exact ⟨w, w_open, singleton_subset_iff.1 hw,
        subset.trans (set.prod_mono subset.rfl hv) hvw⟩ },
    refine ⟨w, C, w_open, q₀w, Cpos.le, _⟩,
    rintros p x ⟨hp, hps⟩,
    by_cases hx : x ∈ k,
    { have H : (p, x) ∈ t,
      { apply hw,
        simp only [prod_mk_mem_set_prod_eq, hp, hx, and_true], },
      have H' : (p, x) ∈ (s ×ˢ univ : set (P × G)),
        by simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true] using hps,
      have : g p x ∈ closed_ball (0 : E') C, from hC (mem_image_of_mem _ ⟨H, H'⟩),
      rwa mem_closed_ball_zero_iff at this },
    { have : g p x = 0, from hgs _ _ hps hx,
      rw this,
      simpa only [norm_zero] using Cpos.le } },
  have I1 : ∀ᶠ (q : P × G) in 𝓝[s ×ˢ univ] q₀,
    ae_strongly_measurable (λ (a : G), L (f a) (g q.1 (q.2 - a))) μ,
  { filter_upwards [self_mem_nhds_within],
    rintros ⟨p, x⟩ ⟨hp, hx⟩,
    refine (has_compact_support.convolution_exists_right L _ hf (A _ hp) _).1,
    exact is_compact_of_is_closed_subset hk (is_closed_tsupport _) (B p hp) },
  let K' := - k + {q₀.2},
  have hK' : is_compact K' := hk.neg.add is_compact_singleton,
  obtain ⟨U, U_open, K'U, hU⟩ : ∃ U, is_open U ∧ K' ⊆ U ∧ integrable_on f U μ,
    from hf.integrable_on_nhds_is_compact hK',
  let bound : G → ℝ := indicator U (λ a, ‖L‖ * ‖f a‖ * C),
  have I2 : ∀ᶠ (q : P × G) in 𝓝[s ×ˢ univ] q₀, ∀ᵐ a ∂μ, ‖L (f a) (g q.1 (q.2 - a))‖ ≤ bound a,
  { obtain ⟨V, V_mem, hV⟩ : ∃ (V : set G) (H : V ∈ 𝓝 (0 : G)), K' + V ⊆ U,
      from compact_open_separated_add_right hK' U_open K'U,
    have : ((w ∩ s) ×ˢ ({q₀.2} + V) : set (P × G)) ∈ 𝓝[s ×ˢ univ] q₀,
    { conv_rhs { rw [← @prod.mk.eta _ _ q₀, nhds_within_prod_eq, nhds_within_univ] },
      refine filter.prod_mem_prod _ (singleton_add_mem_nhds_of_nhds_zero q₀.2 V_mem),
      exact mem_nhds_within_iff_exists_mem_nhds_inter.2 ⟨w, w_open.mem_nhds q₀w, subset.rfl⟩ },
    filter_upwards [this],
    rintros ⟨p, x⟩ hpx,
    simp only [prod_mk_mem_set_prod_eq] at hpx,
    apply eventually_of_forall (λ a, _),
    apply convolution_integrand_bound_right_of_le_of_subset _ _ hpx.2 _,
    { assume x,
      exact hw _ _ hpx.1 },
    { rw ← add_assoc,
      apply subset.trans (add_subset_add_right (add_subset_add_right _)) hV,
      rw neg_subset_neg,
      exact B p hpx.1.2 } },
  have I3 : integrable bound μ,
  { rw [integrable_indicator_iff U_open.measurable_set],
    exact (hU.norm.const_mul _).mul_const _ },
  have I4 : ∀ᵐ (a : G) ∂μ, continuous_within_at (λ (q : P × G), L (f a) (g q.1 (q.2 - a)))
    (s ×ˢ univ) q₀,
  { apply eventually_of_forall (λ a, _),
    suffices H : continuous_within_at (λ (q : P × G), (f a, g q.1 (q.2 - a))) (s ×ˢ univ) q₀,
      from L.continuous₂.continuous_at.comp_continuous_within_at H,
    apply continuous_within_at_const.prod,
    change continuous_within_at (λ (q : P × G), ↿g (q.1, q.2 - a)) (s ×ˢ univ) q₀,
    have : continuous_at (λ (q : P × G), (q.1, q.2 - a)) (q₀.1, q₀.2),
      from (continuous_fst.prod_mk (continuous_snd.sub continuous_const)).continuous_at,
    rw ← @prod.mk.eta _ _ q₀,
    have h'q₀ : (q₀.1, q₀.2 - a) ∈ (s ×ˢ univ : set (P × G)) := ⟨hq₀, mem_univ _⟩,
    refine continuous_within_at.comp (hg _ h'q₀) this.continuous_within_at _,
    rintros ⟨q, x⟩ ⟨hq, hx⟩,
    exact ⟨hq, mem_univ _⟩ },
  exact continuous_within_at_of_dominated I1 I2 I3 I4,
end

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in a subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
lemma continuous_on_convolution_right_with_param
  [t2_space G] {g : P → G → E'} {s : set P} {k : set G} (hk : is_compact k)
  (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : continuous_on (↿g) (s ×ˢ univ)) :
  continuous_on (λ (q : P × G), (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) :=
continuous_on_convolution_right_with_param' L hk hk.is_closed hgs hf hg

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in an open subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of compositions with an additional continuous map.
Version not assuming `t2_space G`. -/
lemma continuous_on_convolution_right_with_param_comp'
  {s : set P} {v : P → G} (hv : continuous_on v s)
  {g : P → G → E'} {k : set G}
  (hk : is_compact k) (h'k : is_closed k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : continuous_on (↿g) (s ×ˢ univ)) :
  continuous_on (λ x, (f ⋆[L, μ] g x) (v x)) s :=
begin
  apply (continuous_on_convolution_right_with_param' L hk h'k hgs hf hg).comp
    (continuous_on_id.prod hv),
  assume x hx,
  simp only [hx, prod_mk_mem_set_prod_eq, mem_univ, and_self, id.def],
end

/-- The convolution `f * g` is continuous if `f` is locally integrable and `g` is continuous and
compactly supported. Version where `g` depends on an additional parameter in an open subset `s` of
a parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of compositions with an additional continuous map. -/
lemma continuous_on_convolution_right_with_param_comp [t2_space G]
  {s : set P} {v : P → G} (hv : continuous_on v s)
  {g : P → G → E'} {k : set G}
  (hk : is_compact k) (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : continuous_on (↿g) (s ×ˢ univ)) :
  continuous_on (λ x, (f ⋆[L, μ] g x) (v x)) s :=
continuous_on_convolution_right_with_param_comp' L hv hk hk.is_closed hgs hf hg

/-- The convolution is continuous if one function is locally integrable and the other has compact
support and is continuous. -/
lemma has_compact_support.continuous_convolution_right
  (hcg : has_compact_support g) (hf : locally_integrable f μ)
  (hg : continuous g) : continuous (f ⋆[L, μ] g) :=
begin
  rw continuous_iff_continuous_on_univ,
  let g' : G → G → E' := λ p q, g q,
  have : continuous_on (↿g') (univ ×ˢ univ) := (hg.comp continuous_snd).continuous_on,
  exact continuous_on_convolution_right_with_param_comp' L
    (continuous_iff_continuous_on_univ.1 continuous_id) hcg (is_closed_tsupport _)
    (λ p x hp hx, image_eq_zero_of_nmem_tsupport hx) hf this,
end

/-- The convolution is continuous if one function is integrable and the other is bounded and
continuous. -/
lemma bdd_above.continuous_convolution_right_of_integrable [second_countable_topology G]
  (hbg : bdd_above (range (λ x, ‖g x‖))) (hf : integrable f μ) (hg : continuous g) :
    continuous (f ⋆[L, μ] g) :=
begin
  refine continuous_iff_continuous_at.mpr (λ x₀, _),
  have : ∀ᶠ x in 𝓝 x₀, ∀ᵐ (t : G) ∂μ,
    ‖L (f t) (g (x - t))‖ ≤ ‖L‖ * ‖f t‖ * (⨆ i, ‖g i‖),
  { refine eventually_of_forall (λ x, eventually_of_forall $ λ t, _),
    refine (L.le_op_norm₂ _ _).trans _,
    exact mul_le_mul_of_nonneg_left (le_csupr hbg $ x - t)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) },
  refine continuous_at_of_dominated _ this _ _,
  { exact eventually_of_forall
      (λ x, hf.ae_strongly_measurable.convolution_integrand_snd' L hg.ae_strongly_measurable) },
  { exact (hf.norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t, (L.continuous₂.comp₂ continuous_const $
      hg.comp $ continuous_id.sub $ by apply continuous_const).continuous_at) }
end

end group

section comm_group

variables [add_comm_group G]

lemma support_convolution_subset : support (f ⋆[L, μ] g) ⊆ support f + support g :=
(support_convolution_subset_swap L).trans (add_comm _ _).subset

variables [is_add_left_invariant μ] [is_neg_invariant μ]

section measurable
variables [has_measurable_neg G]
variables [has_measurable_add G]

variable (L)
/-- Commutativity of convolution -/
lemma convolution_flip : g ⋆[L.flip, μ] f = f ⋆[L, μ] g :=
begin
  ext1 x,
  simp_rw [convolution_def],
  rw [← integral_sub_left_eq_self _ μ x],
  simp_rw [sub_sub_self, flip_apply]
end

/-- The symmetric definition of convolution. -/
lemma convolution_eq_swap : (f ⋆[L, μ] g) x = ∫ t, L (f (x - t)) (g t) ∂μ :=
by { rw [← convolution_flip], refl }

/-- The symmetric definition of convolution where the bilinear operator is scalar multiplication. -/
lemma convolution_lsmul_swap {f : G → 𝕜} {g : G → F}:
  (f ⋆[lsmul 𝕜 𝕜, μ] g : G → F) x = ∫ t, f (x - t) • g t ∂μ :=
convolution_eq_swap _

/-- The symmetric definition of convolution where the bilinear operator is multiplication. -/
lemma convolution_mul_swap [normed_space ℝ 𝕜] [complete_space 𝕜] {f : G → 𝕜} {g : G → 𝕜} :
  (f ⋆[mul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) * g t ∂μ :=
convolution_eq_swap _

/-- The convolution of two even functions is also even. -/
lemma convolution_neg_of_neg_eq (h1 : ∀ᵐ x ∂μ, f (-x) = f x) (h2 : ∀ᵐ x ∂μ, g (-x) = g x) :
  (f ⋆[L, μ] g) (-x) = (f ⋆[L, μ] g) x :=
calc ∫ (t : G), (L (f t)) (g (-x - t)) ∂μ
    = ∫ (t : G), (L (f (-t))) (g (x + t)) ∂μ :
  begin
    apply integral_congr_ae,
    filter_upwards [h1, (eventually_add_left_iff μ x).2 h2] with t ht h't,
    simp_rw [ht, ← h't, neg_add'],
  end
... = ∫ (t : G), (L (f t)) (g (x - t)) ∂μ :
  by { rw ← integral_neg_eq_self, simp only [neg_neg, ← sub_eq_add_neg] }

end measurable

variables [topological_space G]
variables [topological_add_group G]
variables [borel_space G]

lemma has_compact_support.continuous_convolution_left [first_countable_topology G]
  (hcf : has_compact_support f) (hf : continuous f) (hg : locally_integrable g μ) :
  continuous (f ⋆[L, μ] g) :=
by { rw [← convolution_flip], exact hcf.continuous_convolution_right L.flip hg hf }

lemma bdd_above.continuous_convolution_left_of_integrable [second_countable_topology G]
  (hbf : bdd_above (range (λ x, ‖f x‖))) (hf : continuous f) (hg : integrable g μ) :
  continuous (f ⋆[L, μ] g) :=
by { rw [← convolution_flip], exact hbf.continuous_convolution_right_of_integrable L.flip hg hf }

end comm_group

section normed_add_comm_group

variables [seminormed_add_comm_group G]

/-- Compute `(f ⋆ g) x₀` if the support of the `f` is within `metric.ball 0 R`, and `g` is constant
on `metric.ball x₀ R`.

We can simplify the RHS further if we assume `f` is integrable, but also if `L = (•)` or more
generally if `L` has a `antilipschitz_with`-condition. -/
lemma convolution_eq_right' {x₀ : G} {R : ℝ}
  (hf : support f ⊆ ball (0 : G) R)
  (hg : ∀ x ∈ ball x₀ R, g x = g x₀) : (f ⋆[L, μ] g) x₀ = ∫ t, L (f t) (g x₀) ∂μ :=
begin
  have h2 : ∀ t, L (f t) (g (x₀ - t)) = L (f t) (g x₀),
  { intro t, by_cases ht : t ∈ support f,
    { have h2t := hf ht,
      rw [mem_ball_zero_iff] at h2t,
      specialize hg (x₀ - t),
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg,
      rw [hg h2t] },
    { rw [nmem_support] at ht,
      simp_rw [ht, L.map_zero₂] } },
  simp_rw [convolution_def, h2],
end

variables [borel_space G] [second_countable_topology G]
variables [is_add_left_invariant μ] [sigma_finite μ]

/-- Approximate `(f ⋆ g) x₀` if the support of the `f` is bounded within a ball, and `g` is near
`g x₀` on a ball with the same radius around `x₀`. See `dist_convolution_le` for a special case.

We can simplify the second argument of `dist` further if we add some extra type-classes on `E`
and `𝕜` or if `L` is scalar multiplication. -/
lemma dist_convolution_le' {x₀ : G} {R ε : ℝ} {z₀ : E'}
  (hε : 0 ≤ ε)
  (hif : integrable f μ)
  (hf : support f ⊆ ball (0 : G) R)
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
  dist ((f ⋆[L, μ] g : G → F) x₀) (∫ t, L (f t) z₀ ∂μ) ≤ ‖L‖ * ∫ x, ‖f x‖ ∂μ * ε :=
begin
  have hfg : convolution_exists_at f g x₀ L μ,
  { refine bdd_above.convolution_exists_at L _ metric.is_open_ball.measurable_set
    (subset_trans _ hf) hif.integrable_on hmg,
    swap, { refine λ t, mt (λ ht : f t = 0, _), simp_rw [ht, L.map_zero₂] },
    rw [bdd_above_def],
    refine ⟨‖z₀‖ + ε, _⟩,
    rintro _ ⟨x, hx, rfl⟩,
    refine norm_le_norm_add_const_of_dist_le (hg x _),
    rwa [mem_ball_iff_norm, norm_sub_rev, ← mem_ball_zero_iff] },
  have h2 : ∀ t, dist (L (f t) (g (x₀ - t))) (L (f t) z₀) ≤ ‖L (f t)‖ * ε,
  { intro t, by_cases ht : t ∈ support f,
    { have h2t := hf ht,
      rw [mem_ball_zero_iff] at h2t,
      specialize hg (x₀ - t),
      rw [sub_eq_add_neg, add_mem_ball_iff_norm, norm_neg, ← sub_eq_add_neg] at hg,
      refine ((L (f t)).dist_le_op_norm _ _).trans _,
      exact mul_le_mul_of_nonneg_left (hg h2t) (norm_nonneg _) },
    { rw [nmem_support] at ht,
      simp_rw [ht, L.map_zero₂, L.map_zero, norm_zero, zero_mul, dist_self] } },
  simp_rw [convolution_def],
  simp_rw [dist_eq_norm] at h2 ⊢,
  rw [← integral_sub hfg.integrable], swap, { exact (L.flip z₀).integrable_comp hif },
  refine (norm_integral_le_of_norm_le ((L.integrable_comp hif).norm.mul_const ε)
    (eventually_of_forall h2)).trans _,
  rw [integral_mul_right],
  refine mul_le_mul_of_nonneg_right _ hε,
  have h3 : ∀ t, ‖L (f t)‖ ≤ ‖L‖ * ‖f t‖,
  { intros t,
    exact L.le_op_norm (f t) },
  refine (integral_mono (L.integrable_comp hif).norm (hif.norm.const_mul _) h3).trans_eq _,
  rw [integral_mul_left]
end

variables [normed_space ℝ E] [normed_space ℝ E'] [complete_space E']

/-- Approximate `f ⋆ g` if the support of the `f` is bounded within a ball, and `g` is near `g x₀`
on a ball with the same radius around `x₀`.

This is a special case of `dist_convolution_le'` where `L` is `(•)`, `f` has integral 1 and `f` is
nonnegative. -/
lemma dist_convolution_le {f : G → ℝ} {x₀ : G} {R ε : ℝ} {z₀ : E'}
  (hε : 0 ≤ ε)
  (hf : support f ⊆ ball (0 : G) R)
  (hnf : ∀ x, 0 ≤ f x)
  (hintf : ∫ x, f x ∂μ = 1)
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ R, dist (g x) z₀ ≤ ε) :
  dist ((f ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) z₀ ≤ ε :=
begin
  have hif : integrable f μ,
  { by_contra hif, exact zero_ne_one ((integral_undef hif).symm.trans hintf) },
  convert (dist_convolution_le' _ hε hif hf hmg hg).trans _,
  { simp_rw [lsmul_apply, integral_smul_const, hintf, one_smul] },
  { simp_rw [real.norm_of_nonneg (hnf _), hintf, mul_one],
    exact (mul_le_mul_of_nonneg_right op_norm_lsmul_le hε).trans_eq (one_mul ε) }
end

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of nonnegative functions with integral `1` as `i` tends to `l`;
* The support of `φ` tends to small neighborhoods around `(0 : G)` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ᶠ 𝓝 x₀`;
* `k i` tends to `x₀`.

See also `cont_diff_bump.convolution_tendsto_right`.
-/
lemma convolution_tendsto_right
  {ι} {g : ι → G → E'} {l : filter ι} {x₀ : G} {z₀ : E'}
  {φ : ι → G → ℝ} {k : ι → G}
  (hnφ : ∀ᶠ i in l, ∀ x, 0 ≤ φ i x)
  (hiφ : ∀ᶠ i in l, ∫ x, φ i x ∂μ = 1) -- todo: we could weaken this to "the integral tends to 1"
  (hφ : tendsto (λ n, support (φ n)) l (𝓝 0).small_sets)
  (hmg : ∀ᶠ i in l, ae_strongly_measurable (g i) μ)
  (hcg : tendsto (uncurry g) (l ×ᶠ 𝓝 x₀) (𝓝 z₀))
  (hk : tendsto k l (𝓝 x₀)) :
  tendsto (λ i : ι, (φ i ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) :=
begin
  simp_rw [tendsto_small_sets_iff] at hφ,
  rw [metric.tendsto_nhds] at hcg ⊢,
  simp_rw [metric.eventually_prod_nhds_iff] at hcg,
  intros ε hε,
  have h2ε : 0 < ε / 3 := div_pos hε (by norm_num),
  obtain ⟨p, hp, δ, hδ, hgδ⟩ := hcg _ h2ε,
  dsimp only [uncurry] at hgδ,
  have h2k := hk.eventually (ball_mem_nhds x₀ $ half_pos hδ),
  have h2φ := (hφ (ball (0 : G) _) $ ball_mem_nhds _ (half_pos hδ)),
  filter_upwards [hp, h2k, h2φ, hnφ, hiφ, hmg] with i hpi hki hφi hnφi hiφi hmgi,
  have hgi : dist (g i (k i)) z₀ < ε / 3 := hgδ hpi (hki.trans $ half_lt_self hδ),
  have h1 : ∀ x' ∈ ball (k i) (δ / 2), dist (g i x') (g i (k i)) ≤ ε / 3 + ε / 3,
  { intros x' hx',
    refine (dist_triangle_right _ _ _).trans (add_le_add (hgδ hpi _).le hgi.le),
    exact ((dist_triangle _ _ _).trans_lt (add_lt_add hx'.out hki)).trans_eq (add_halves δ) },
  have := dist_convolution_le (add_pos h2ε h2ε).le hφi hnφi hiφi hmgi h1,
  refine ((dist_triangle _ _ _).trans_lt (add_lt_add_of_le_of_lt this hgi)).trans_eq _,
  field_simp, ring_nf
end

end normed_add_comm_group

namespace cont_diff_bump

variables {n : ℕ∞}
variables [normed_space ℝ E']
variables [normed_add_comm_group G] [normed_space ℝ G] [has_cont_diff_bump G]
variables [complete_space E']
variables {a : G} {φ : cont_diff_bump (0 : G)}

/-- If `φ` is a bump function, compute `(φ ⋆ g) x₀` if `g` is constant on `metric.ball x₀ φ.R`. -/
lemma convolution_eq_right {x₀ : G}
  (hg : ∀ x ∈ ball x₀ φ.R, g x = g x₀) : (φ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = integral μ φ • g x₀ :=
by simp_rw [convolution_eq_right' _ φ.support_eq.subset hg, lsmul_apply, integral_smul_const]

variables [borel_space G]
variables [is_locally_finite_measure μ] [is_open_pos_measure μ]
variables [finite_dimensional ℝ G]

/-- If `φ` is a normed bump function, compute `φ ⋆ g` if `g` is constant on `metric.ball x₀ φ.R`. -/
lemma normed_convolution_eq_right {x₀ : G}
  (hg : ∀ x ∈ ball x₀ φ.R, g x = g x₀) : (φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀ = g x₀ :=
by { simp_rw [convolution_eq_right' _ φ.support_normed_eq.subset hg, lsmul_apply],
  exact integral_normed_smul φ μ (g x₀) }

variables [is_add_left_invariant μ]

/-- If `φ` is a normed bump function, approximate `(φ ⋆ g) x₀` if `g` is near `g x₀` on a ball with
radius `φ.R` around `x₀`. -/
lemma dist_normed_convolution_le {x₀ : G} {ε : ℝ}
  (hmg : ae_strongly_measurable g μ)
  (hg : ∀ x ∈ ball x₀ φ.R, dist (g x) (g x₀) ≤ ε) :
  dist ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) (g x₀) ≤ ε :=
dist_convolution_le (by simp_rw [← dist_self (g x₀), hg x₀ (mem_ball_self φ.R_pos)])
  φ.support_normed_eq.subset φ.nonneg_normed φ.integral_normed hmg hg

/-- `(φ i ⋆ g i) (k i)` tends to `z₀` as `i` tends to some filter `l` if
* `φ` is a sequence of normed bump functions such that `(φ i).R` tends to `0` as `i` tends to `l`;
* `g i` is `mu`-a.e. strongly measurable as `i` tends to `l`;
* `g i x` tends to `z₀` as `(i, x)` tends to `l ×ᶠ 𝓝 x₀`;
* `k i` tends to `x₀`. -/
lemma convolution_tendsto_right {ι} {φ : ι → cont_diff_bump (0 : G)}
  {g : ι → G → E'} {k : ι → G} {x₀ : G} {z₀ : E'} {l : filter ι}
  (hφ : tendsto (λ i, (φ i).R) l (𝓝 0))
  (hig : ∀ᶠ i in l, ae_strongly_measurable (g i) μ)
  (hcg : tendsto (uncurry g) (l ×ᶠ 𝓝 x₀) (𝓝 z₀))
  (hk : tendsto k l (𝓝 x₀)) :
  tendsto (λ i, ((λ x, (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g i : G → E') (k i)) l (𝓝 z₀) :=
convolution_tendsto_right (eventually_of_forall $ λ i, (φ i).nonneg_normed)
  (eventually_of_forall $ λ i, (φ i).integral_normed)
  (tendsto_support_normed_small_sets hφ) hig hcg hk

/-- Special case of `cont_diff_bump.convolution_tendsto_right` where `g` is continuous,
  and the limit is taken only in the first function. -/
lemma convolution_tendsto_right_of_continuous {ι} {φ : ι → cont_diff_bump (0 : G)}
  {l : filter ι} (hφ : tendsto (λ i, (φ i).R) l (𝓝 0))
  (hg : continuous g) (x₀ : G) :
  tendsto (λ i, ((λ x, (φ i).normed μ x) ⋆[lsmul ℝ ℝ, μ] g : G → E') x₀) l (𝓝 (g x₀)) :=
convolution_tendsto_right hφ (eventually_of_forall $ λ _, hg.ae_strongly_measurable)
  ((hg.tendsto x₀).comp tendsto_snd) tendsto_const_nhds

end cont_diff_bump

end measurability

end nontrivially_normed_field

open_locale convolution

section is_R_or_C

variables [is_R_or_C 𝕜]
variables [normed_space 𝕜 E]
variables [normed_space 𝕜 E']
variables [normed_space 𝕜 E'']
variables [normed_space ℝ F] [normed_space 𝕜 F]
variables {n : ℕ∞}
variables [complete_space F]
variables [measurable_space G] {μ ν : measure G}
variables (L : E →L[𝕜] E' →L[𝕜] F)

section assoc
variables [normed_add_comm_group F'] [normed_space ℝ F'] [normed_space 𝕜 F'] [complete_space F']
variables [normed_add_comm_group F''] [normed_space ℝ F''] [normed_space 𝕜 F''] [complete_space F'']
variables {k : G → E''}
variables (L₂ : F →L[𝕜] E'' →L[𝕜] F')
variables (L₃ : E →L[𝕜] F'' →L[𝕜] F')
variables (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')
variables [add_group G]
variables [sigma_finite μ] [sigma_finite ν] [is_add_right_invariant μ]

lemma integral_convolution
  [has_measurable_add₂ G] [has_measurable_neg G]
  [normed_space ℝ E] [normed_space ℝ E']
  [complete_space E] [complete_space E']
  (hf : integrable f ν) (hg : integrable g μ) :
  ∫ x, (f ⋆[L, ν] g) x ∂μ = L (∫ x, f x ∂ν) (∫ x, g x ∂μ) :=
begin
  refine (integral_integral_swap (by apply hf.convolution_integrand L hg)).trans _,
  simp_rw [integral_comp_comm _ (hg.comp_sub_right _), integral_sub_right_eq_self],
  exact (L.flip (∫ x, g x ∂μ)).integral_comp_comm hf
end

variables [has_measurable_add₂ G] [is_add_right_invariant ν] [has_measurable_neg G]

/-- Convolution is associative. This has a weak but inconvenient integrability condition.
See also `convolution_assoc`. -/
lemma convolution_assoc' (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z))
  {x₀ : G}
  (hfg : ∀ᵐ y ∂μ, convolution_exists_at f g y L ν)
  (hgk : ∀ᵐ x ∂ν, convolution_exists_at g k x L₄ μ)
  (hi : integrable (uncurry (λ x y, (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x))))) (μ.prod ν)) :
  ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] (g ⋆[L₄, μ] k)) x₀ :=
calc    ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀
      = ∫ t, L₂ (∫ s, L (f s) (g (t - s)) ∂ν) (k (x₀ - t)) ∂μ : rfl
  ... = ∫ t, ∫ s, L₂ (L (f s) (g (t - s))) (k (x₀ - t)) ∂ν ∂μ :
    integral_congr_ae (hfg.mono $ λ t ht, ((L₂.flip (k (x₀ - t))).integral_comp_comm ht).symm)
  ... = ∫ t, ∫ s, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂ν ∂μ : by simp_rw hL
  ... = ∫ s, ∫ t, L₃ (f s) (L₄ (g (t - s)) (k (x₀ - t))) ∂μ ∂ν : by rw [integral_integral_swap hi]
  ... = ∫ s, ∫ u, L₃ (f s) (L₄ (g u) (k ((x₀ - s) - u))) ∂μ ∂ν : begin
    congr', ext t,
    rw [eq_comm, ← integral_sub_right_eq_self _ t],
    { simp_rw [sub_sub_sub_cancel_right] },
    { apply_instance },
  end
  ... = ∫ s, L₃ (f s) (∫ u, L₄ (g u) (k ((x₀ - s) - u)) ∂μ) ∂ν : begin
    refine integral_congr_ae _,
    refine ((quasi_measure_preserving_sub_left_of_right_invariant ν x₀).ae hgk).mono (λ t ht, _),
    exact (L₃ (f t)).integral_comp_comm ht,
  end
  ... = (f ⋆[L₃, ν] (g ⋆[L₄, μ] k)) x₀ : rfl

/-- Convolution is associative. This requires that
* all maps are a.e. strongly measurable w.r.t one of the measures
* `f ⋆[L, ν] g` exists almost everywhere
* `‖g‖ ⋆[μ] ‖k‖` exists almost everywhere
* `‖f‖ ⋆[ν] (‖g‖ ⋆[μ] ‖k‖)` exists at `x₀` -/
lemma convolution_assoc (hL : ∀ (x : E) (y : E') (z : E''), L₂ (L x y) z = L₃ x (L₄ y z))
  {x₀ : G}
  (hf : ae_strongly_measurable f ν)
  (hg : ae_strongly_measurable g μ)
  (hk : ae_strongly_measurable k μ)
  (hfg : ∀ᵐ y ∂μ, convolution_exists_at f g y L ν)
  (hgk : ∀ᵐ x ∂ν, convolution_exists_at (λ x, ‖g x‖) (λ x, ‖k x‖) x (mul ℝ ℝ) μ)
  (hfgk : convolution_exists_at (λ x, ‖f x‖) ((λ x, ‖g x‖) ⋆[mul ℝ ℝ, μ] (λ x, ‖k x‖))
    x₀ (mul ℝ ℝ) ν) :
  ((f ⋆[L, ν] g) ⋆[L₂, μ] k) x₀ = (f ⋆[L₃, ν] (g ⋆[L₄, μ] k)) x₀ :=
begin
  refine convolution_assoc' L L₂ L₃ L₄ hL hfg (hgk.mono $ λ x hx, hx.of_norm L₄ hg hk) _,
  /- the following is similar to `integrable.convolution_integrand` -/
  have h_meas : ae_strongly_measurable
      (uncurry (λ x y, L₃ (f y) (L₄ (g x) (k (x₀ - y - x))))) (μ.prod ν),
  { refine L₃.ae_strongly_measurable_comp₂ hf.snd _,
    refine L₄.ae_strongly_measurable_comp₂ hg.fst _,
    refine (hk.mono' _).comp_measurable ((measurable_const.sub measurable_snd).sub measurable_fst),
    refine quasi_measure_preserving.absolutely_continuous _,
    refine quasi_measure_preserving.prod_of_left
      ((measurable_const.sub measurable_snd).sub measurable_fst) (eventually_of_forall $ λ y, _),
    dsimp only,
    exact quasi_measure_preserving_sub_left_of_right_invariant μ _ },
  have h2_meas : ae_strongly_measurable (λ y, ∫ x, ‖L₃ (f y) (L₄ (g x) (k (x₀ - y - x)))‖ ∂μ) ν :=
    h_meas.prod_swap.norm.integral_prod_right',
  have h3 : map (λ z : G × G, (z.1 - z.2, z.2)) (μ.prod ν) = μ.prod ν :=
    (measure_preserving_sub_prod μ ν).map_eq,
  suffices : integrable (uncurry (λ x y, L₃ (f y) (L₄ (g x) (k (x₀ - y - x))))) (μ.prod ν),
  { rw [← h3] at this,
    convert this.comp_measurable (measurable_sub.prod_mk measurable_snd),
    ext ⟨x, y⟩,
    simp_rw [uncurry, function.comp_apply, sub_sub_sub_cancel_right] },
  simp_rw [integrable_prod_iff' h_meas],
  refine ⟨((quasi_measure_preserving_sub_left_of_right_invariant ν x₀).ae hgk).mono
    (λ t ht, (L₃ (f t)).integrable_comp $ ht.of_norm L₄ hg hk), _⟩,
  refine (hfgk.const_mul (‖L₃‖ * ‖L₄‖)).mono' h2_meas
    (((quasi_measure_preserving_sub_left_of_right_invariant ν x₀).ae hgk).mono $ λ t ht, _),
  { simp_rw [convolution_def, mul_apply', mul_mul_mul_comm ‖L₃‖ ‖L₄‖, ← integral_mul_left],
    rw [real.norm_of_nonneg],
    { refine integral_mono_of_nonneg (eventually_of_forall $ λ t, norm_nonneg _)
        ((ht.const_mul _).const_mul _) (eventually_of_forall $ λ s, _),
      refine (L₃.le_op_norm₂ _ _).trans _,
      refine mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
      rw [← mul_assoc],
      apply L₄.le_op_norm₂ },
    exact integral_nonneg (λ x, norm_nonneg _) }
end

end assoc

variables [normed_add_comm_group G] [borel_space G]

lemma convolution_precompR_apply {g : G → E'' →L[𝕜] E'}
  (hf : locally_integrable f μ) (hcg : has_compact_support g) (hg : continuous g)
  (x₀ : G) (x : E'') : (f ⋆[L.precompR E'', μ] g) x₀ x = (f ⋆[L, μ] (λ a, g a x)) x₀  :=
begin
  have := hcg.convolution_exists_right (L.precompR E'' : _) hf hg x₀,
  simp_rw [convolution_def, continuous_linear_map.integral_apply this],
  refl,
end

variables [normed_space 𝕜 G] [sigma_finite μ] [is_add_left_invariant μ]

/-- Compute the total derivative of `f ⋆ g` if `g` is `C^1` with compact support and `f` is locally
integrable. To write down the total derivative as a convolution, we use
`continuous_linear_map.precompR`. -/
lemma has_compact_support.has_fderiv_at_convolution_right
  (hcg : has_compact_support g) (hf : locally_integrable f μ) (hg : cont_diff 𝕜 1 g) (x₀ : G) :
  has_fderiv_at (f ⋆[L, μ] g) ((f ⋆[L.precompR G, μ] fderiv 𝕜 g) x₀) x₀ :=
begin
  rcases hcg.eq_zero_or_finite_dimensional 𝕜 hg.continuous with rfl|fin_dim,
  { have : fderiv 𝕜 (0 : G → E') = 0, from fderiv_const (0 : E'),
    simp only [this, convolution_zero, pi.zero_apply],
    exact has_fderiv_at_const (0 : F) x₀ },
  resetI,
  haveI : proper_space G, from finite_dimensional.proper_is_R_or_C 𝕜 G,
  set L' := L.precompR G,
  have h1 : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (λ t, L (f t) (g (x - t))) μ :=
  eventually_of_forall
    (hf.ae_strongly_measurable.convolution_integrand_snd L hg.continuous.ae_strongly_measurable),
  have h2 : ∀ x, ae_strongly_measurable (λ t, L' (f t) (fderiv 𝕜 g (x - t))) μ,
  { exact hf.ae_strongly_measurable.convolution_integrand_snd L'
      (hg.continuous_fderiv le_rfl).ae_strongly_measurable },
  have h3 : ∀ x t, has_fderiv_at (λ x, g (x - t)) (fderiv 𝕜 g (x - t)) x,
  { intros x t,
    simpa using (hg.differentiable le_rfl).differentiable_at.has_fderiv_at.comp x
      ((has_fderiv_at_id x).sub (has_fderiv_at_const t x)) },
  let K' := - tsupport (fderiv 𝕜 g) + closed_ball x₀ 1,
  have hK' : is_compact K' := (hcg.fderiv 𝕜).neg.add (is_compact_closed_ball x₀ 1),
  refine has_fderiv_at_integral_of_dominated_of_fderiv_le
    zero_lt_one h1 _ (h2 x₀) _ _ _,
  { exact K'.indicator (λ t, ‖L'‖ * ‖f t‖ * (⨆ x, ‖fderiv 𝕜 g x‖)) },
  { exact hcg.convolution_exists_right L hf hg.continuous x₀ },
  { refine eventually_of_forall (λ t x hx, _),
    exact (hcg.fderiv 𝕜).convolution_integrand_bound_right L'
      (hg.continuous_fderiv le_rfl) (ball_subset_closed_ball hx) },
  { rw [integrable_indicator_iff hK'.measurable_set],
    exact ((hf.integrable_on_is_compact hK').norm.const_mul _).mul_const _ },
  { exact eventually_of_forall (λ t x hx, (L _).has_fderiv_at.comp x (h3 x t)) },
end

lemma has_compact_support.has_fderiv_at_convolution_left [is_neg_invariant μ]
  (hcf : has_compact_support f) (hf : cont_diff 𝕜 1 f) (hg : locally_integrable g μ) (x₀ : G) :
  has_fderiv_at (f ⋆[L, μ] g) ((fderiv 𝕜 f ⋆[L.precompL G, μ] g) x₀) x₀ :=
begin
  simp only [← convolution_flip] {single_pass := tt},
  exact hcf.has_fderiv_at_convolution_right L.flip hg hf x₀,
end

end is_R_or_C

section real
/-! The one-variable case -/

variables [is_R_or_C 𝕜]
variables [normed_space 𝕜 E]
variables [normed_space 𝕜 E']
variables [normed_space ℝ F] [normed_space 𝕜 F]
variables {f₀ : 𝕜 → E} {g₀ : 𝕜 → E'}
variables {n : ℕ∞}
variables (L : E →L[𝕜] E' →L[𝕜] F)
variables [complete_space F]
variables {μ : measure 𝕜}
variables [is_add_left_invariant μ] [sigma_finite μ]

lemma has_compact_support.has_deriv_at_convolution_right
  (hf : locally_integrable f₀ μ) (hcg : has_compact_support g₀) (hg : cont_diff 𝕜 1 g₀)
  (x₀ : 𝕜) :
  has_deriv_at (f₀ ⋆[L, μ] g₀) ((f₀ ⋆[L, μ] deriv g₀) x₀) x₀ :=
begin
  convert (hcg.has_fderiv_at_convolution_right L hf hg x₀).has_deriv_at,
  rw [convolution_precompR_apply L hf (hcg.fderiv 𝕜) (hg.continuous_fderiv le_rfl)],
  refl,
end

lemma has_compact_support.has_deriv_at_convolution_left [is_neg_invariant μ]
  (hcf : has_compact_support f₀) (hf : cont_diff 𝕜 1 f₀)
  (hg : locally_integrable g₀ μ) (x₀ : 𝕜) :
  has_deriv_at (f₀ ⋆[L, μ] g₀) ((deriv f₀ ⋆[L, μ] g₀) x₀) x₀ :=
begin
  simp only [← convolution_flip] {single_pass := tt},
  exact hcf.has_deriv_at_convolution_right L.flip hg hf x₀,
end

end real

section with_param

variables [is_R_or_C 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 E'']
[normed_space ℝ F] [normed_space 𝕜 F] [complete_space F] [measurable_space G]
[normed_add_comm_group G] [borel_space G] [normed_space 𝕜 G]
[normed_add_comm_group P] [normed_space 𝕜 P]
{μ : measure G} (L : E →L[𝕜] E' →L[𝕜] F)

/-- The derivative of the convolution `f * g` is given by `f * Dg`, when `f` is locally integrable
and `g` is `C^1` and compactly supported. Version where `g` depends on an additional parameter in an
open subset `s` of a parameter space `P` (and the compact support `k` is independent of the
parameter in `s`). -/
lemma has_fderiv_at_convolution_right_with_param
  {g : P → G → E'} {s : set P} {k : set G} (hs : is_open s) (hk : is_compact k)
  (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : cont_diff_on 𝕜 1 ↿g (s ×ˢ univ))
  (q₀ : P × G) (hq₀ : q₀.1 ∈ s) :
  has_fderiv_at (λ (q : P × G), (f ⋆[L, μ] g q.1) q.2)
    ((f ⋆[L.precompR (P × G), μ] (λ (x : G), fderiv 𝕜 ↿g (q₀.1, x))) q₀.2) q₀ :=
begin
  let g' := fderiv 𝕜 ↿g,
  have A : ∀ p ∈ s, continuous (g p),
  { assume p hp,
    apply hg.continuous_on.comp_continuous (continuous_const.prod_mk continuous_id') (λ x, _),
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true] using hp },
  have A' : ∀ (q : P × G), q.1 ∈ s → s ×ˢ univ ∈ 𝓝 q,
  { assume q hq,
    apply (hs.prod is_open_univ).mem_nhds,
    simpa only [mem_prod, mem_univ, and_true] using hq },
  /- The derivative of `g` vanishes away from `k`. -/
  have g'_zero : ∀ p x, p ∈ s → x ∉ k → g' (p, x) = 0,
  { assume p x hp hx,
    refine (has_fderiv_at_zero_of_eventually_const 0 _).fderiv,
    have M2 : kᶜ ∈ 𝓝 x, from is_open.mem_nhds hk.is_closed.is_open_compl hx,
    have M1 : s ∈ 𝓝 p, from hs.mem_nhds hp,
    rw nhds_prod_eq,
    filter_upwards [prod_mem_prod M1 M2],
    rintros ⟨p, y⟩ ⟨hp, hy⟩,
    exact hgs p y hp hy },
  /- We find a small neighborhood of `{q₀.1} × k` on which the derivative is uniformly bounded. This
  follows from the continuity at all points of the compact set `k`. -/
  obtain ⟨ε, C, εpos, Cnonneg, h₀ε, hε⟩ :
    ∃ ε C, 0 < ε ∧ 0 ≤ C ∧ ball q₀.1 ε ⊆ s ∧ ∀ p x, ‖p - q₀.1‖ < ε → ‖g' (p, x)‖ ≤ C,
  { have A : is_compact ({q₀.1} ×ˢ k), from is_compact_singleton.prod hk,
    obtain ⟨t, kt, t_open, ht⟩ : ∃ t, {q₀.1} ×ˢ k ⊆ t ∧ is_open t ∧ bounded (g' '' t),
    { have B : continuous_on g' (s ×ˢ univ),
        from hg.continuous_on_fderiv_of_open (hs.prod is_open_univ) le_rfl,
      apply exists_is_open_bounded_image_of_is_compact_of_continuous_on A
        (hs.prod is_open_univ) _ B,
      simp only [prod_subset_prod_iff, hq₀, singleton_subset_iff, subset_univ, and_self, true_or] },
    obtain ⟨ε, εpos, hε, h'ε⟩ :
      ∃ (ε : ℝ), 0 < ε ∧ thickening ε ({q₀.fst} ×ˢ k) ⊆ t ∧ ball q₀.1 ε ⊆ s,
    { obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ), 0 < ε ∧ thickening ε ({q₀.fst} ×ˢ k) ⊆ t,
        from A.exists_thickening_subset_open t_open kt,
      obtain ⟨δ, δpos, hδ⟩ : ∃ (δ : ℝ) (H : 0 < δ), ball q₀.1 δ ⊆ s,
        from metric.is_open_iff.1 hs _ hq₀,
      refine ⟨min ε δ, lt_min εpos δpos, _, _⟩,
      { exact subset.trans (thickening_mono (min_le_left _ _) _) hε },
      { exact subset.trans (ball_subset_ball (min_le_right _ _)) hδ } },
    obtain ⟨C, Cpos, hC⟩ : ∃ C, 0 < C ∧ g' '' t ⊆ closed_ball 0 C, from ht.subset_ball_lt 0 0,
    refine ⟨ε, C, εpos, Cpos.le, h'ε, λ p x hp, _⟩,
    have hps : p ∈ s, from h'ε (mem_ball_iff_norm.2 hp),
    by_cases hx : x ∈ k,
    { have H : (p, x) ∈ t,
      { apply hε,
        refine mem_thickening_iff.2 ⟨(q₀.1, x), _, _⟩,
        { simp only [hx, singleton_prod, mem_image, prod.mk.inj_iff, eq_self_iff_true, true_and,
            exists_eq_right] },
        { rw ← dist_eq_norm at hp,
          simpa only [prod.dist_eq, εpos, dist_self, max_lt_iff, and_true] using hp } },
      have : g' (p, x) ∈ closed_ball (0 : P × G →L[𝕜] E') C, from hC (mem_image_of_mem _ H),
      rwa mem_closed_ball_zero_iff at this },
    { have : g' (p, x) = 0, from g'_zero _ _ hps hx,
      rw this,
      simpa only [norm_zero] using Cpos.le } },
  /- Now, we wish to apply a theorem on differentiation of integrals. For this, we need to check
  trivial measurability or integrability assumptions (in `I1`, `I2`, `I3`), as well as a uniform
  integrability assumption over the derivative (in `I4` and `I5`) and pointwise differentiability
  in `I6`. -/
  have I1 : ∀ᶠ (x : P × G) in 𝓝 q₀,
    ae_strongly_measurable (λ (a : G), L (f a) (g x.1 (x.2 - a))) μ,
  { filter_upwards [A' q₀ hq₀],
    rintros ⟨p, x⟩ ⟨hp, hx⟩,
    refine (has_compact_support.convolution_exists_right L _ hf (A _ hp) _).1,
    apply is_compact_of_is_closed_subset hk (is_closed_tsupport _),
    exact closure_minimal (support_subset_iff'.2 (λ z hz, hgs _ _ hp hz)) hk.is_closed, },
  have I2 : integrable (λ (a : G), L (f a) (g q₀.1 (q₀.2 - a))) μ,
  { have M : has_compact_support (g q₀.1),
      from has_compact_support.intro hk (λ x hx, hgs q₀.1 x hq₀ hx),
    apply M.convolution_exists_right L hf (A q₀.1 hq₀) q₀.2 },
  have I3 : ae_strongly_measurable (λ (a : G), (L (f a)).comp (g' (q₀.fst, q₀.snd - a))) μ,
  { have T : has_compact_support (λ y, g' (q₀.1, y)),
      from has_compact_support.intro hk (λ x hx, g'_zero q₀.1 x hq₀ hx),
    apply (has_compact_support.convolution_exists_right (L.precompR (P × G) : _) T hf _ q₀.2).1,
    have : continuous_on g' (s ×ˢ univ),
        from hg.continuous_on_fderiv_of_open (hs.prod is_open_univ) le_rfl,
    apply this.comp_continuous (continuous_const.prod_mk continuous_id'),
    assume x,
    simpa only [prod_mk_mem_set_prod_eq, mem_univ, and_true] using hq₀ },
  set K' := - k + {q₀.2} with K'_def,
  have hK' : is_compact K' := hk.neg.add is_compact_singleton,
  obtain ⟨U, U_open, K'U, hU⟩ : ∃ U, is_open U ∧ K' ⊆ U ∧ integrable_on f U μ,
    from hf.integrable_on_nhds_is_compact hK',
  obtain ⟨δ, δpos, δε, hδ⟩ : ∃ δ, (0 : ℝ) < δ ∧ δ ≤ ε ∧ K' + ball 0 δ ⊆ U,
  { obtain ⟨V, V_mem, hV⟩ : ∃ (V : set G) (V_mem : V ∈ 𝓝 (0 : G)), K' + V ⊆ U,
      from compact_open_separated_add_right hK' U_open K'U,
    rcases metric.mem_nhds_iff.1 V_mem with ⟨δ, δpos, hδ⟩,
    refine ⟨min δ ε, lt_min δpos εpos, min_le_right _ _, _⟩,
    exact (add_subset_add_left ((ball_subset_ball (min_le_left _ _)).trans hδ)).trans hV },
  let bound : G → ℝ := indicator U (λ a, ‖L.precompR (P × G)‖ * ‖f a‖ * C),
  have I4 : ∀ᵐ (a : G) ∂μ, ∀ (x : P × G), dist x q₀ < δ →
    ‖L.precompR (P × G) (f a) (g' (x.fst, x.snd - a))‖ ≤ bound a,
  { apply eventually_of_forall,
    assume a x hx,
    rw [prod.dist_eq, dist_eq_norm, dist_eq_norm] at hx,
    have : -tsupport (λ a, g' (x.1, a)) + ball q₀.2 δ ⊆ U,
    { apply subset.trans _ hδ,
      rw [K'_def, add_assoc],
      apply add_subset_add,
      { rw neg_subset_neg,
        apply closure_minimal (support_subset_iff'.2 (λ z hz, _)) hk.is_closed,
        apply g'_zero x.1 z (h₀ε _) hz,
        rw mem_ball_iff_norm,
        exact ((le_max_left _ _).trans_lt hx).trans_le δε },
      { simp only [add_ball, thickening_singleton, zero_vadd] } },
    apply convolution_integrand_bound_right_of_le_of_subset _ _ _ this,
    { assume y,
      exact hε _ _ (((le_max_left _ _).trans_lt hx).trans_le δε) },
    { rw mem_ball_iff_norm,
      exact (le_max_right _ _).trans_lt hx } },
  have I5 : integrable bound μ,
  { rw [integrable_indicator_iff U_open.measurable_set],
    exact (hU.norm.const_mul _).mul_const _ },
  have I6 : ∀ᵐ (a : G) ∂μ, ∀ (x : P × G), dist x q₀ < δ →
    has_fderiv_at (λ (x : P × G), L (f a) (g x.1 (x.2 - a)))
      ((L (f a)).comp (g' (x.fst, x.snd - a))) x,
  { apply eventually_of_forall,
    assume a x hx,
    apply (L _).has_fderiv_at.comp x,
    have N : s ×ˢ univ ∈ 𝓝 (x.1, x.2 - a),
    { apply A',
      apply h₀ε,
      rw prod.dist_eq at hx,
      exact lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hx) δε },
    have Z := ((hg.differentiable_on le_rfl).differentiable_at N).has_fderiv_at,
    have Z' : has_fderiv_at (λ (x : P × G), (x.1, x.2 - a)) (continuous_linear_map.id 𝕜 (P × G)) x,
    { have : (λ (x : P × G), (x.1, x.2 - a)) = id - (λ x, (0, a)),
      { ext x; simp only [pi.sub_apply, id.def, prod.fst_sub, sub_zero, prod.snd_sub] },
      simp_rw [this],
      exact (has_fderiv_at_id x).sub_const (0, a) },
    exact Z.comp x Z' },
  exact has_fderiv_at_integral_of_dominated_of_fderiv_le δpos I1 I2 I3 I4 I5 I6,
end

/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`).
In this version, all the types belong to the same universe (to get an induction working in the
proof). Use instead `cont_diff_on_convolution_right_with_param`, which removes this restriction. -/
lemma cont_diff_on_convolution_right_with_param_aux
  {G : Type uP} {E' : Type uP} {F : Type uP} {P : Type uP}
  [normed_add_comm_group E'] [normed_add_comm_group F]
  [normed_space 𝕜 E'] [normed_space ℝ F] [normed_space 𝕜 F] [complete_space F]
  [measurable_space G] {μ : measure G} [normed_add_comm_group G] [borel_space G] [normed_space 𝕜 G]
  [normed_add_comm_group P] [normed_space 𝕜 P]
  {f : G → E} {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F)
  {g : P → G → E'}
  {s : set P} {k : set G} (hs : is_open s) (hk : is_compact k)
  (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : cont_diff_on 𝕜 n ↿g (s ×ˢ univ)) :
  cont_diff_on 𝕜 n (λ (q : P × G), (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) :=
begin
  /- We have a formula for the derivation of `f * g`, which is of the same form, thanks to
  `has_fderiv_at_convolution_right_with_param`. Therefore, we can prove the result by induction on
  `n` (but for this we need the spaces at the different steps of the induction to live in the same
  universe, which is why we make the assumption in the lemma that all the relevant spaces
  come from the same universe). -/
  unfreezingI { induction n using enat.nat_induction with n ih ih generalizing g E' F },
  { rw [cont_diff_on_zero] at hg ⊢,
    exact continuous_on_convolution_right_with_param L hk hgs hf hg },
  { let f' : P → G → (P × G →L[𝕜] F) := λ p a,
      (f ⋆[L.precompR (P × G), μ] (λ (x : G), fderiv 𝕜 (uncurry g) (p, x))) a,
    have A : ∀ (q₀ : P × G), q₀.1 ∈ s →
      has_fderiv_at (λ (q : P × G), (f ⋆[L, μ] g q.1) q.2) (f' q₀.1 q₀.2) q₀,
        from has_fderiv_at_convolution_right_with_param L hs hk hgs hf hg.one_of_succ,
    rw cont_diff_on_succ_iff_fderiv_of_open (hs.prod (@is_open_univ G _)) at ⊢ hg,
    split,
    { rintros ⟨p, x⟩ ⟨hp, hx⟩,
      exact (A (p, x) hp).differentiable_at.differentiable_within_at, },
    { suffices H : cont_diff_on 𝕜 n ↿f' (s ×ˢ univ),
      { apply H.congr,
        rintros ⟨p, x⟩ ⟨hp, hx⟩,
        exact (A (p, x) hp).fderiv },
      have B : ∀ (p : P) (x : G), p ∈ s → x ∉ k → fderiv 𝕜 (uncurry g) (p, x) = 0,
      { assume p x hp hx,
        apply (has_fderiv_at_zero_of_eventually_const (0 : E') _).fderiv,
        have M2 : kᶜ ∈ 𝓝 x, from is_open.mem_nhds hk.is_closed.is_open_compl hx,
        have M1 : s ∈ 𝓝 p, from hs.mem_nhds hp,
        rw nhds_prod_eq,
        filter_upwards [prod_mem_prod M1 M2],
        rintros ⟨p, y⟩ ⟨hp, hy⟩,
        exact hgs p y hp hy },
      apply ih (L.precompR (P × G) : _) B,
      convert hg.2,
      apply funext,
      rintros ⟨p, x⟩,
      refl } },
  { rw [cont_diff_on_top] at hg ⊢,
    assume n,
    exact ih n L hgs (hg n) }
end

/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
lemma cont_diff_on_convolution_right_with_param
  {f : G → E} {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F) {g : P → G → E'}
  {s : set P} {k : set G} (hs : is_open s) (hk : is_compact k)
  (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : cont_diff_on 𝕜 n ↿g (s ×ˢ univ)) :
  cont_diff_on 𝕜 n (λ (q : P × G), (f ⋆[L, μ] g q.1) q.2) (s ×ˢ univ) :=
begin
  /- The result is known when all the universes are the same, from
  `cont_diff_on_convolution_right_with_param_aux`. We reduce to this situation by pushing
  everything through `ulift` continuous linear equivalences. -/
  let eG : Type (max uG uE' uF uP) := ulift G,
  borelize eG,
  let eE' : Type (max uE' uG uF uP) := ulift E',
  let eF : Type (max uF uG uE' uP) := ulift F,
  let eP : Type (max uP uG uE' uF) := ulift P,
  have isoG : eG ≃L[𝕜] G := continuous_linear_equiv.ulift,
  have isoE' : eE' ≃L[𝕜] E' := continuous_linear_equiv.ulift,
  have isoF : eF ≃L[𝕜] F := continuous_linear_equiv.ulift,
  have isoP : eP ≃L[𝕜] P := continuous_linear_equiv.ulift,
  let ef := f ∘ isoG,
  let eμ : measure eG := measure.map isoG.symm μ,
  let eg : eP → eG → eE' := λ ep ex, isoE'.symm (g (isoP ep) (isoG ex)),
  let eL := continuous_linear_map.comp
    ((continuous_linear_equiv.arrow_congr isoE' isoF).symm : (E' →L[𝕜] F) →L[𝕜] eE' →L[𝕜] eF) L,
  let R := (λ (q : eP × eG), (ef ⋆[eL, eμ] eg q.1) q.2),
  have R_contdiff : cont_diff_on 𝕜 n R ((isoP ⁻¹' s) ×ˢ univ),
  { have hek : is_compact (isoG ⁻¹' k),
      from isoG.to_homeomorph.closed_embedding.is_compact_preimage hk,
    have hes : is_open (isoP ⁻¹' s), from isoP.continuous.is_open_preimage _ hs,
    refine cont_diff_on_convolution_right_with_param_aux eL hes hek _ _ _,
    { assume p x hp hx,
      simp only [comp_app, continuous_linear_equiv.prod_apply, linear_isometry_equiv.coe_coe,
        continuous_linear_equiv.map_eq_zero_iff],
      exact hgs _ _ hp hx },
    { apply (locally_integrable_map_homeomorph isoG.symm.to_homeomorph).2,
      convert hf,
      ext1 x,
      simp only [ef, continuous_linear_equiv.coe_to_homeomorph, comp_app,
        continuous_linear_equiv.apply_symm_apply], },
    { apply isoE'.symm.cont_diff.comp_cont_diff_on,
      apply hg.comp ((isoP.prod isoG).cont_diff).cont_diff_on,
      rintros ⟨p, x⟩ ⟨hp, hx⟩,
      simpa only [mem_preimage, continuous_linear_equiv.prod_apply, prod_mk_mem_set_prod_eq,
        mem_univ, and_true] using hp } },
  have A : cont_diff_on 𝕜 n (isoF ∘ R ∘ (isoP.prod isoG).symm) (s ×ˢ univ),
  { apply isoF.cont_diff.comp_cont_diff_on,
    apply R_contdiff.comp (continuous_linear_equiv.cont_diff _).cont_diff_on,
    rintros ⟨p, x⟩ ⟨hp, hx⟩,
    simpa only [mem_preimage, mem_prod, mem_univ, and_true, continuous_linear_equiv.prod_symm,
      continuous_linear_equiv.prod_apply, continuous_linear_equiv.apply_symm_apply] using hp },
  have : isoF ∘ R ∘ (isoP.prod isoG).symm = (λ (q : P × G), (f ⋆[L, μ] g q.1) q.2),
  { apply funext,
    rintros ⟨p, x⟩,
    simp only [R, linear_isometry_equiv.coe_coe, comp_app, continuous_linear_equiv.prod_symm,
      continuous_linear_equiv.prod_apply],
    simp only [convolution, eL, coe_comp', continuous_linear_equiv.coe_coe, comp_app, eμ],
    rw [closed_embedding.integral_map, ← isoF.integral_comp_comm],
    swap, { exact isoG.symm.to_homeomorph.closed_embedding },
    congr' 1,
    ext1 a,
    simp only [ef, eg, comp_app, continuous_linear_equiv.apply_symm_apply, coe_comp',
      continuous_linear_equiv.prod_apply, continuous_linear_equiv.map_sub,
      continuous_linear_equiv.arrow_congr, continuous_linear_equiv.arrow_congrSL_symm_apply,
      continuous_linear_equiv.coe_coe, comp_app, continuous_linear_equiv.apply_symm_apply ] },
  simp_rw [this] at A,
  exact A,
end

/-- The convolution `f * g` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of composition with an additional smooth function. -/
lemma cont_diff_on_convolution_right_with_param_comp
  {n : ℕ∞} (L : E →L[𝕜] E' →L[𝕜] F)
  {s : set P} {v : P → G} (hv : cont_diff_on 𝕜 n v s)
  {f : G → E} {g : P → G → E'} {k : set G} (hs : is_open s) (hk : is_compact k)
  (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : cont_diff_on 𝕜 n ↿g (s ×ˢ univ)) :
  cont_diff_on 𝕜 n (λ x, (f ⋆[L, μ] g x) (v x)) s :=
begin
  apply (cont_diff_on_convolution_right_with_param L hs hk hgs hf hg).comp
    (cont_diff_on_id.prod hv),
  assume x hx,
  simp only [hx, mem_preimage, prod_mk_mem_set_prod_eq, mem_univ, and_self, id.def],
end

/-- The convolution `g * f` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`). -/
lemma cont_diff_on_convolution_left_with_param [μ.is_add_left_invariant] [μ.is_neg_invariant]
  (L : E' →L[𝕜] E →L[𝕜] F) {f : G → E} {n : ℕ∞}
  {g : P → G → E'} {s : set P} {k : set G} (hs : is_open s) (hk : is_compact k)
  (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : cont_diff_on 𝕜 n ↿g (s ×ˢ univ)) :
  cont_diff_on 𝕜 n (λ (q : P × G), (g q.1 ⋆[L, μ] f) q.2) (s ×ˢ univ) :=
by simpa only [convolution_flip]
  using cont_diff_on_convolution_right_with_param L.flip hs hk hgs hf hg

/-- The convolution `g * f` is `C^n` when `f` is locally integrable and `g` is `C^n` and compactly
supported. Version where `g` depends on an additional parameter in an open subset `s` of a
parameter space `P` (and the compact support `k` is independent of the parameter in `s`),
given in terms of composition with additional smooth functions. -/
lemma cont_diff_on_convolution_left_with_param_comp [μ.is_add_left_invariant] [μ.is_neg_invariant]
  (L : E' →L[𝕜] E →L[𝕜] F) {s : set P} {n : ℕ∞} {v : P → G} (hv : cont_diff_on 𝕜 n v s)
  {f : G → E} {g : P → G → E'} {k : set G} (hs : is_open s) (hk : is_compact k)
  (hgs : ∀ p, ∀ x, p ∈ s → x ∉ k → g p x = 0)
  (hf : locally_integrable f μ) (hg : cont_diff_on 𝕜 n ↿g (s ×ˢ univ)) :
  cont_diff_on 𝕜 n (λ x, (g x ⋆[L, μ] f) (v x)) s :=
begin
  apply (cont_diff_on_convolution_left_with_param L hs hk hgs hf hg).comp (cont_diff_on_id.prod hv),
  assume x hx,
  simp only [hx, mem_preimage, prod_mk_mem_set_prod_eq, mem_univ, and_self, id.def],
end

lemma has_compact_support.cont_diff_convolution_right {n : ℕ∞}
  (hcg : has_compact_support g) (hf : locally_integrable f μ) (hg : cont_diff 𝕜 n g) :
  cont_diff 𝕜 n (f ⋆[L, μ] g) :=
begin
  rcases exists_compact_iff_has_compact_support.2 hcg with ⟨k, hk, h'k⟩,
  rw ← cont_diff_on_univ,
  exact cont_diff_on_convolution_right_with_param_comp L cont_diff_on_id is_open_univ hk
    (λ p x hp hx, h'k x hx) hf (hg.comp cont_diff_snd).cont_diff_on,
end

lemma has_compact_support.cont_diff_convolution_left [μ.is_add_left_invariant] [μ.is_neg_invariant]
  {n : ℕ∞} (hcf : has_compact_support f) (hf : cont_diff 𝕜 n f) (hg : locally_integrable g μ) :
  cont_diff 𝕜 n (f ⋆[L, μ] g) :=
by { rw [← convolution_flip], exact hcf.cont_diff_convolution_right L.flip hg hf }

end with_param

section nonneg

variables [normed_space ℝ E] [normed_space ℝ E'] [normed_space ℝ F] [complete_space F]

/-- The forward convolution of two functions `f` and `g` on `ℝ`, with respect to a continuous
bilinear map `L` and measure `ν`. It is defined to be the function mapping `x` to
`∫_{0}^{x} t, L (f t) (g (x - t)) ∂ν` if `0 < x`, and 0 otherwise. -/
noncomputable def pos_convolution
  (f : ℝ → E) (g : ℝ → E') (L : E →L[ℝ] E' →L[ℝ] F) (ν : measure ℝ . volume_tac) : ℝ → F :=
indicator (Ioi (0:ℝ)) (λ x, ∫_{0}^{x} t, L (f t) (g (x - t)) ∂ν)

lemma pos_convolution_eq_convolution_indicator
  (f : ℝ → E) (g : ℝ → E') (L : E →L[ℝ] E' →L[ℝ] F) (ν : measure ℝ . volume_tac) [has_no_atoms ν] :
  pos_convolution f g L ν = convolution (indicator (Ioi 0) f) (indicator (Ioi 0) g) L ν :=
begin
  ext1 x,
  rw [convolution, pos_convolution, indicator],
  split_ifs,
  { rw [interval_integral.integral_of_le (le_of_lt h),
      integral_Ioc_eq_integral_Ioo,
      ←integral_indicator (measurable_set_Ioo : measurable_set (Ioo 0 x))],
    congr' 1 with t : 1,
    have : (t ≤ 0) ∨ (t ∈ Ioo 0 x) ∨ (x ≤ t),
    { rcases le_or_lt t 0 with h | h,
      { exact or.inl h },
      { rcases lt_or_le t x with h' | h',
        exacts [or.inr (or.inl ⟨h, h'⟩), or.inr (or.inr h')] } },
    rcases this with ht|ht|ht,
    { rw [indicator_of_not_mem (not_mem_Ioo_of_le ht), indicator_of_not_mem (not_mem_Ioi.mpr ht),
        continuous_linear_map.map_zero, continuous_linear_map.zero_apply] },
    { rw [indicator_of_mem ht, indicator_of_mem (mem_Ioi.mpr ht.1),
        indicator_of_mem (mem_Ioi.mpr $ sub_pos.mpr ht.2)] },
    { rw [indicator_of_not_mem (not_mem_Ioo_of_ge ht),
        indicator_of_not_mem (not_mem_Ioi.mpr (sub_nonpos_of_le ht)),
        continuous_linear_map.map_zero] } },
  { convert (integral_zero ℝ F).symm,
    ext1 t,
    by_cases ht : 0 < t,
    { rw [indicator_of_not_mem (_ : x - t ∉ Ioi 0), continuous_linear_map.map_zero],
      rw not_mem_Ioi at h ⊢,
      exact sub_nonpos.mpr (h.trans ht.le) },
    { rw [indicator_of_not_mem (mem_Ioi.not.mpr ht), continuous_linear_map.map_zero,
        continuous_linear_map.zero_apply] } }
end

lemma integrable_pos_convolution {f : ℝ → E} {g : ℝ → E'} {μ ν : measure ℝ}
  [sigma_finite μ] [sigma_finite ν] [is_add_right_invariant μ] [has_no_atoms ν]
  (hf : integrable_on f (Ioi 0) ν) (hg : integrable_on g (Ioi 0) μ) (L : E →L[ℝ] E' →L[ℝ] F) :
  integrable (pos_convolution f g L ν) μ :=
begin
  rw ←integrable_indicator_iff (measurable_set_Ioi : measurable_set (Ioi (0:ℝ))) at hf hg,
  rw pos_convolution_eq_convolution_indicator f g L ν,
  exact (hf.convolution_integrand L hg).integral_prod_left,
end

/-- The integral over `Ioi 0` of a forward convolution of two functions is equal to the product
of their integrals over this set. (Compare `integral_convolution` for the two-sided convolution.) -/
lemma integral_pos_convolution [complete_space E] [complete_space E'] {μ ν : measure ℝ}
  [sigma_finite μ] [sigma_finite ν] [is_add_right_invariant μ] [has_no_atoms ν]
  {f : ℝ → E} {g : ℝ → E'} (hf : integrable_on f (Ioi 0) ν)
  (hg : integrable_on g (Ioi 0) μ) (L : E →L[ℝ] E' →L[ℝ] F)  :
  ∫ x:ℝ in Ioi 0, (∫_{0}^{x} t:ℝ, L (f t) (g (x - t)) ∂ν) ∂μ =
    L (∫ x:ℝ in Ioi 0, f x ∂ν) (∫ x:ℝ in Ioi 0, g x ∂μ) :=
begin
  rw ←integrable_indicator_iff (measurable_set_Ioi : measurable_set (Ioi (0:ℝ))) at hf hg,
  simp_rw ←integral_indicator measurable_set_Ioi,
  convert integral_convolution L hf hg using 2,
  apply pos_convolution_eq_convolution_indicator,
end

end nonneg
