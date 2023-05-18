/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import measure_theory.measure.giry_monad
import dynamics.ergodic.measure_preserving
import measure_theory.integral.lebesgue
import measure_theory.measure.open_pos

/-!
# The product measure

In this file we define and prove properties about the binary product measure. If `α` and `β` have
σ-finite measures `μ` resp. `ν` then `α × β` can be equipped with a σ-finite measure `μ.prod ν` that
satisfies `(μ.prod ν) s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`.
We also have `(μ.prod ν) (s ×ˢ t) = μ s * ν t`, i.e. the measure of a rectangle is the product of
the measures of the sides.

We also prove Tonelli's theorem.

## Main definition

* `measure_theory.measure.prod`: The product of two measures.

## Main results

* `measure_theory.measure.prod_apply` states `μ.prod ν s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`
  for measurable `s`. `measure_theory.measure.prod_apply_symm` is the reversed version.
* `measure_theory.measure.prod_prod` states `μ.prod ν (s ×ˢ t) = μ s * ν t` for measurable sets
  `s` and `t`.
* `measure_theory.lintegral_prod`: Tonelli's theorem. It states that for a measurable function
  `α × β → ℝ≥0∞` we have `∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ`. The version
  for functions `α → β → ℝ≥0∞` is reversed, and called `lintegral_lintegral`. Both versions have
  a variant with `_symm` appended, where the order of integration is reversed.
  The lemma `measurable.lintegral_prod_right'` states that the inner integral of the right-hand side
  is measurable.

## Implementation Notes

Many results are proven twice, once for functions in curried form (`α → β → γ`) and one for
functions in uncurried form (`α × β → γ`). The former often has an assumption
`measurable (uncurry f)`, which could be inconvenient to discharge, but for the latter it is more
common that the function has to be given explicitly, since Lean cannot synthesize the function by
itself. We name the lemmas about the uncurried form with a prime.
Tonelli's theorem has a different naming scheme, since the version for the uncurried version is
reversed.

## Tags

product measure, Tonelli's theorem, Fubini-Tonelli theorem
-/

noncomputable theory
open_locale classical topology ennreal measure_theory
open set function real ennreal
open measure_theory measurable_space measure_theory.measure
open topological_space (hiding generate_from)
open filter (hiding prod_eq map)

variables {α α' β β' γ E : Type*}

/-- Rectangles formed by π-systems form a π-system. -/
lemma is_pi_system.prod {C : set (set α)} {D : set (set β)} (hC : is_pi_system C)
  (hD : is_pi_system D) : is_pi_system (image2 (×ˢ) C D) :=
begin
  rintro _ ⟨s₁, t₁, hs₁, ht₁, rfl⟩ _ ⟨s₂, t₂, hs₂, ht₂, rfl⟩ hst,
  rw [prod_inter_prod] at hst ⊢, rw [prod_nonempty_iff] at hst,
  exact mem_image2_of_mem (hC _ hs₁ _ hs₂ hst.1) (hD _ ht₁ _ ht₂ hst.2)
end

/-- Rectangles of countably spanning sets are countably spanning. -/
lemma is_countably_spanning.prod {C : set (set α)} {D : set (set β)}
  (hC : is_countably_spanning C) (hD : is_countably_spanning D) :
  is_countably_spanning (image2 (×ˢ) C D) :=
begin
  rcases ⟨hC, hD⟩ with ⟨⟨s, h1s, h2s⟩, t, h1t, h2t⟩,
  refine ⟨λ n, (s n.unpair.1) ×ˢ (t n.unpair.2), λ n, mem_image2_of_mem (h1s _) (h1t _), _⟩,
  rw [Union_unpair_prod, h2s, h2t, univ_prod_univ]
end

variables [measurable_space α] [measurable_space α'] [measurable_space β] [measurable_space β']
variables [measurable_space γ]
variables {μ μ' : measure α} {ν ν' : measure β} {τ : measure γ}
variables [normed_add_comm_group E]

/-! ### Measurability

Before we define the product measure, we can talk about the measurability of operations on binary
functions. We show that if `f` is a binary measurable function, then the function that integrates
along one of the variables (using either the Lebesgue or Bochner integral) is measurable.
-/

/-- The product of generated σ-algebras is the one generated by rectangles, if both generating sets
  are countably spanning. -/
lemma generate_from_prod_eq {α β} {C : set (set α)} {D : set (set β)}
  (hC : is_countably_spanning C) (hD : is_countably_spanning D) :
  @prod.measurable_space _ _ (generate_from C) (generate_from D) =
    generate_from (image2 (×ˢ) C D) :=
begin
  apply le_antisymm,
  { refine sup_le _ _; rw [comap_generate_from];
      apply generate_from_le; rintro _ ⟨s, hs, rfl⟩,
    { rcases hD with ⟨t, h1t, h2t⟩,
      rw [← prod_univ, ← h2t, prod_Union],
      apply measurable_set.Union,
      intro n, apply measurable_set_generate_from,
      exact ⟨s, t n, hs, h1t n, rfl⟩ },
    { rcases hC with ⟨t, h1t, h2t⟩,
      rw [← univ_prod, ← h2t, Union_prod_const],
      apply measurable_set.Union,
      rintro n, apply measurable_set_generate_from,
      exact mem_image2_of_mem (h1t n) hs } },
  { apply generate_from_le, rintro _ ⟨s, t, hs, ht, rfl⟩, rw [prod_eq],
    apply (measurable_fst _).inter (measurable_snd _),
    { exact measurable_set_generate_from hs },
    { exact measurable_set_generate_from ht } }
end

/-- If `C` and `D` generate the σ-algebras on `α` resp. `β`, then rectangles formed by `C` and `D`
  generate the σ-algebra on `α × β`. -/
lemma generate_from_eq_prod {C : set (set α)} {D : set (set β)} (hC : generate_from C = ‹_›)
  (hD : generate_from D = ‹_›) (h2C : is_countably_spanning C) (h2D : is_countably_spanning D) :
    generate_from (image2 (×ˢ) C D) = prod.measurable_space :=
by rw [← hC, ← hD, generate_from_prod_eq h2C h2D]

/-- The product σ-algebra is generated from boxes, i.e. `s ×ˢ t` for sets `s : set α` and
  `t : set β`. -/
lemma generate_from_prod :
  generate_from (image2 (×ˢ) {s : set α | measurable_set s} {t : set β | measurable_set t}) =
  prod.measurable_space :=
generate_from_eq_prod generate_from_measurable_set generate_from_measurable_set
  is_countably_spanning_measurable_set is_countably_spanning_measurable_set

/-- Rectangles form a π-system. -/
lemma is_pi_system_prod :
  is_pi_system (image2 (×ˢ) {s : set α | measurable_set s} {t : set β | measurable_set t}) :=
is_pi_system_measurable_set.prod is_pi_system_measurable_set

/-- If `ν` is a finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
  a measurable function. `measurable_measure_prod_mk_left` is strictly more general. -/
lemma measurable_measure_prod_mk_left_finite [is_finite_measure ν] {s : set (α × β)}
  (hs : measurable_set s) : measurable (λ x, ν (prod.mk x ⁻¹' s)) :=
begin
  refine induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ hs,
  { simp [measurable_zero, const_def] },
  { rintro _ ⟨s, t, hs, ht, rfl⟩, simp only [mk_preimage_prod_right_eq_if, measure_if],
    exact measurable_const.indicator hs },
  { intros t ht h2t,
    simp_rw [preimage_compl, measure_compl (measurable_prod_mk_left ht) (measure_ne_top ν _)],
    exact h2t.const_sub _ },
  { intros f h1f h2f h3f, simp_rw [preimage_Union],
    have : ∀ b, ν (⋃ i, prod.mk b ⁻¹' f i) = ∑' i, ν (prod.mk b ⁻¹' f i) :=
      λ b, measure_Union (λ i j hij, disjoint.preimage _ (h1f hij))
        (λ i, measurable_prod_mk_left (h2f i)),
    simp_rw [this], apply measurable.ennreal_tsum h3f },
end

/-- If `ν` is a σ-finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
  a measurable function. -/
lemma measurable_measure_prod_mk_left [sigma_finite ν] {s : set (α × β)}
  (hs : measurable_set s) : measurable (λ x, ν (prod.mk x ⁻¹' s)) :=
begin
  have : ∀ x, measurable_set (prod.mk x ⁻¹' s) := λ x, measurable_prod_mk_left hs,
  simp only [← @supr_restrict_spanning_sets _ _ ν, this],
  apply measurable_supr, intro i,
  haveI := fact.mk (measure_spanning_sets_lt_top ν i),
  exact measurable_measure_prod_mk_left_finite hs
end

/-- If `μ` is a σ-finite measure, and `s ⊆ α × β` is measurable, then `y ↦ μ { x | (x, y) ∈ s }` is
  a measurable function. -/
lemma measurable_measure_prod_mk_right {μ : measure α} [sigma_finite μ] {s : set (α × β)}
  (hs : measurable_set s) : measurable (λ y, μ ((λ x, (x, y)) ⁻¹' s)) :=
measurable_measure_prod_mk_left (measurable_set_swap_iff.mpr hs)

lemma measurable.map_prod_mk_left [sigma_finite ν] : measurable (λ x : α, map (prod.mk x) ν) :=
begin
  apply measurable_of_measurable_coe, intros s hs,
  simp_rw [map_apply measurable_prod_mk_left hs],
  exact measurable_measure_prod_mk_left hs
end

lemma measurable.map_prod_mk_right {μ : measure α} [sigma_finite μ] :
  measurable (λ y : β, map (λ x : α, (x, y)) μ) :=
begin
  apply measurable_of_measurable_coe, intros s hs,
  simp_rw [map_apply measurable_prod_mk_right hs],
  exact measurable_measure_prod_mk_right hs
end

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable. -/
lemma measurable.lintegral_prod_right' [sigma_finite ν] :
  ∀ {f : α × β → ℝ≥0∞} (hf : measurable f), measurable (λ x, ∫⁻ y, f (x, y) ∂ν) :=
begin
  have m := @measurable_prod_mk_left,
  refine measurable.ennreal_induction _ _ _,
  { intros c s hs, simp only [← indicator_comp_right],
    suffices : measurable (λ x, c * ν (prod.mk x ⁻¹' s)),
    { simpa [lintegral_indicator _ (m hs)] },
    exact (measurable_measure_prod_mk_left hs).const_mul _ },
  { rintro f g - hf hg h2f h2g, simp_rw [pi.add_apply, lintegral_add_left (hf.comp m)],
    exact h2f.add h2g },
  { intros f hf h2f h3f,
    have := measurable_supr h3f,
    have : ∀ x, monotone (λ n y, f n (x, y)) := λ x i j hij y, h2f hij (x, y),
    simpa [lintegral_supr (λ n, (hf n).comp m), this] }
end

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
lemma measurable.lintegral_prod_right [sigma_finite ν] {f : α → β → ℝ≥0∞}
  (hf : measurable (uncurry f)) : measurable (λ x, ∫⁻ y, f x y ∂ν) :=
hf.lintegral_prod_right'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable. -/
lemma measurable.lintegral_prod_left' [sigma_finite μ] {f : α × β → ℝ≥0∞}
  (hf : measurable f) : measurable (λ y, ∫⁻ x, f (x, y) ∂μ) :=
(measurable_swap_iff.mpr hf).lintegral_prod_right'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
lemma measurable.lintegral_prod_left [sigma_finite μ] {f : α → β → ℝ≥0∞}
  (hf : measurable (uncurry f)) : measurable (λ y, ∫⁻ x, f x y ∂μ) :=
hf.lintegral_prod_left'

/-! ### The product measure -/

namespace measure_theory

namespace measure

/-- The binary product of measures. They are defined for arbitrary measures, but we basically
  prove all properties under the assumption that at least one of them is σ-finite. -/
@[irreducible] protected def prod (μ : measure α) (ν : measure β) : measure (α × β) :=
bind μ $ λ x : α, map (prod.mk x) ν

instance prod.measure_space {α β} [measure_space α] [measure_space β] : measure_space (α × β) :=
{ volume := volume.prod volume }

variables [sigma_finite ν]

lemma volume_eq_prod (α β) [measure_space α] [measure_space β] :
  (volume : measure (α × β)) = (volume : measure α).prod (volume : measure β) :=
rfl

lemma prod_apply {s : set (α × β)} (hs : measurable_set s) :
  μ.prod ν s = ∫⁻ x, ν (prod.mk x ⁻¹' s) ∂μ :=
by simp_rw [measure.prod, bind_apply hs measurable.map_prod_mk_left,
  map_apply measurable_prod_mk_left hs]

/-- The product measure of the product of two sets is the product of their measures. Note that we
do not need the sets to be measurable. -/
@[simp] lemma prod_prod (s : set α) (t : set β) : μ.prod ν (s ×ˢ t) = μ s * ν t :=
begin
  apply le_antisymm,
  { set ST := (to_measurable μ s) ×ˢ (to_measurable ν t),
    have hSTm : measurable_set ST :=
      (measurable_set_to_measurable _ _).prod (measurable_set_to_measurable _ _),
    calc μ.prod ν (s ×ˢ t) ≤ μ.prod ν ST :
      measure_mono $ set.prod_mono (subset_to_measurable _ _) (subset_to_measurable _ _)
    ... = μ (to_measurable μ s) * ν (to_measurable ν t) :
      by simp_rw [prod_apply hSTm, mk_preimage_prod_right_eq_if, measure_if,
        lintegral_indicator _ (measurable_set_to_measurable _ _), lintegral_const,
        restrict_apply_univ, mul_comm]
    ... = μ s * ν t : by rw [measure_to_measurable, measure_to_measurable] },
  { /- Formalization is based on https://mathoverflow.net/a/254134/136589 -/
    set ST := to_measurable (μ.prod ν) (s ×ˢ t),
    have hSTm : measurable_set ST := measurable_set_to_measurable _ _,
    have hST : s ×ˢ t ⊆ ST := subset_to_measurable _ _,
    set f : α → ℝ≥0∞ := λ x, ν (prod.mk x ⁻¹' ST),
    have hfm : measurable f := measurable_measure_prod_mk_left hSTm,
    set s' : set α := {x | ν t ≤ f x},
    have hss' : s ⊆ s' := λ x hx, measure_mono (λ y hy, hST $ mk_mem_prod hx hy),
    calc μ s * ν t ≤ μ s' * ν t : mul_le_mul_right' (measure_mono hss') _
    ... = ∫⁻ x in s', ν t ∂μ    : by rw [set_lintegral_const, mul_comm]
    ... ≤ ∫⁻ x in s', f x ∂μ    : set_lintegral_mono measurable_const hfm (λ x, id)
    ... ≤ ∫⁻ x, f x ∂μ          : lintegral_mono' restrict_le_self le_rfl
    ... = μ.prod ν ST           : (prod_apply hSTm).symm
    ... = μ.prod ν (s ×ˢ t)     : measure_to_measurable _ }
end

instance {X Y : Type*} [topological_space X] [topological_space Y]
  {m : measurable_space X} {μ : measure X} [is_open_pos_measure μ]
  {m' : measurable_space Y} {ν : measure Y} [is_open_pos_measure ν] [sigma_finite ν] :
  is_open_pos_measure (μ.prod ν) :=
begin
  constructor,
  rintros U U_open ⟨⟨x, y⟩, hxy⟩,
  rcases is_open_prod_iff.1 U_open x y hxy with ⟨u, v, u_open, v_open, xu, yv, huv⟩,
  refine ne_of_gt (lt_of_lt_of_le _ (measure_mono huv)),
  simp only [prod_prod, canonically_ordered_comm_semiring.mul_pos],
  split,
  { exact u_open.measure_pos μ ⟨x, xu⟩ },
  { exact v_open.measure_pos ν ⟨y, yv⟩ }
end

instance {α β : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  (μ : measure α) (ν : measure β) [is_finite_measure μ] [is_finite_measure ν] :
  is_finite_measure (μ.prod ν) :=
begin
  constructor,
  rw [← univ_prod_univ, prod_prod],
  exact mul_lt_top (measure_lt_top _ _).ne (measure_lt_top _ _).ne,
end

instance {α β : Type*} {mα : measurable_space α} {mβ : measurable_space β}
  (μ : measure α) (ν : measure β) [is_probability_measure μ] [is_probability_measure ν] :
  is_probability_measure (μ.prod ν) :=
⟨by rw [← univ_prod_univ, prod_prod, measure_univ, measure_univ, mul_one]⟩

instance {α β : Type*} [topological_space α] [topological_space β]
  {mα : measurable_space α} {mβ : measurable_space β} (μ : measure α) (ν : measure β)
  [is_finite_measure_on_compacts μ] [is_finite_measure_on_compacts ν] [sigma_finite ν] :
  is_finite_measure_on_compacts (μ.prod ν) :=
begin
  refine ⟨λ K hK, _⟩,
  set L := (prod.fst '' K) ×ˢ (prod.snd '' K) with hL,
  have : K ⊆ L,
  { rintros ⟨x, y⟩ hxy,
    simp only [prod_mk_mem_set_prod_eq, mem_image, prod.exists, exists_and_distrib_right,
      exists_eq_right],
    exact ⟨⟨y, hxy⟩, ⟨x, hxy⟩⟩ },
  apply lt_of_le_of_lt (measure_mono this),
  rw [hL, prod_prod],
  exact mul_lt_top ((is_compact.measure_lt_top ((hK.image continuous_fst))).ne)
                   ((is_compact.measure_lt_top ((hK.image continuous_snd))).ne)
end

lemma ae_measure_lt_top {s : set (α × β)} (hs : measurable_set s)
  (h2s : (μ.prod ν) s ≠ ∞) : ∀ᵐ x ∂μ, ν (prod.mk x ⁻¹' s) < ∞ :=
by { simp_rw [prod_apply hs] at h2s, refine ae_lt_top (measurable_measure_prod_mk_left hs) h2s }

/-- Note: the assumption `hs` cannot be dropped. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
lemma measure_prod_null {s : set (α × β)}
  (hs : measurable_set s) : μ.prod ν s = 0 ↔ (λ x, ν (prod.mk x ⁻¹' s)) =ᵐ[μ] 0 :=
by simp_rw [prod_apply hs, lintegral_eq_zero_iff (measurable_measure_prod_mk_left hs)]

/-- Note: the converse is not true without assuming that `s` is measurable. For a counterexample,
  see Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
lemma measure_ae_null_of_prod_null {s : set (α × β)}
  (h : μ.prod ν s = 0) : (λ x, ν (prod.mk x ⁻¹' s)) =ᵐ[μ] 0 :=
begin
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h,
  simp_rw [measure_prod_null mt] at ht,
  rw [eventually_le_antisymm_iff],
  exact ⟨eventually_le.trans_eq
    (eventually_of_forall $ λ x, (measure_mono (preimage_mono hst) : _)) ht,
    eventually_of_forall $ λ x, zero_le _⟩
end

lemma absolutely_continuous.prod [sigma_finite ν'] (h1 : μ ≪ μ') (h2 : ν ≪ ν') :
  μ.prod ν ≪ μ'.prod ν' :=
begin
  refine absolutely_continuous.mk (λ s hs h2s, _),
  simp_rw [measure_prod_null hs] at h2s ⊢,
  exact (h2s.filter_mono h1.ae_le).mono (λ _ h, h2 h)
end

/-- Note: the converse is not true. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
lemma ae_ae_of_ae_prod {p : α × β → Prop} (h : ∀ᵐ z ∂μ.prod ν, p z) :
  ∀ᵐ x ∂ μ, ∀ᵐ y ∂ ν, p (x, y) :=
measure_ae_null_of_prod_null h

/-- `μ.prod ν` has finite spanning sets in rectangles of finite spanning sets. -/
noncomputable! def finite_spanning_sets_in.prod {ν : measure β} {C : set (set α)} {D : set (set β)}
  (hμ : μ.finite_spanning_sets_in C) (hν : ν.finite_spanning_sets_in D) :
  (μ.prod ν).finite_spanning_sets_in (image2 (×ˢ) C D) :=
begin
  haveI := hν.sigma_finite,
  refine ⟨λ n, hμ.set n.unpair.1 ×ˢ hν.set n.unpair.2,
    λ n, mem_image2_of_mem (hμ.set_mem _) (hν.set_mem _), λ n, _, _⟩,
  { rw [prod_prod],
    exact mul_lt_top (hμ.finite _).ne (hν.finite _).ne },
  { simp_rw [Union_unpair_prod, hμ.spanning, hν.spanning, univ_prod_univ] }
end

lemma quasi_measure_preserving_fst : quasi_measure_preserving prod.fst (μ.prod ν) μ :=
begin
  refine ⟨measurable_fst, absolutely_continuous.mk (λ s hs h2s, _)⟩,
  rw [map_apply measurable_fst hs, ← prod_univ, prod_prod, h2s, zero_mul],
end

lemma quasi_measure_preserving_snd : quasi_measure_preserving prod.snd (μ.prod ν) ν :=
begin
  refine ⟨measurable_snd, absolutely_continuous.mk (λ s hs h2s, _)⟩,
  rw [map_apply measurable_snd hs, ← univ_prod, prod_prod, h2s, mul_zero]
end

variables [sigma_finite μ]

instance prod.sigma_finite : sigma_finite (μ.prod ν) :=
(μ.to_finite_spanning_sets_in.prod ν.to_finite_spanning_sets_in).sigma_finite

/-- A measure on a product space equals the product measure if they are equal on rectangles
  with as sides sets that generate the corresponding σ-algebras. -/
lemma prod_eq_generate_from {μ : measure α} {ν : measure β} {C : set (set α)}
  {D : set (set β)} (hC : generate_from C = ‹_›)
  (hD : generate_from D = ‹_›) (h2C : is_pi_system C) (h2D : is_pi_system D)
  (h3C : μ.finite_spanning_sets_in C) (h3D : ν.finite_spanning_sets_in D)
  {μν : measure (α × β)}
  (h₁ : ∀ (s ∈ C) (t ∈ D), μν (s ×ˢ t) = μ s * ν t) : μ.prod ν = μν :=
begin
  refine (h3C.prod h3D).ext
    (generate_from_eq_prod hC hD h3C.is_countably_spanning h3D.is_countably_spanning).symm
    (h2C.prod h2D) _,
  { rintro _ ⟨s, t, hs, ht, rfl⟩, haveI := h3D.sigma_finite,
    rw [h₁ s hs t ht, prod_prod] }
end

/-- A measure on a product space equals the product measure if they are equal on rectangles. -/
lemma prod_eq {μν : measure (α × β)}
  (h : ∀ s t, measurable_set s → measurable_set t → μν (s ×ˢ t) = μ s * ν t) : μ.prod ν = μν :=
prod_eq_generate_from generate_from_measurable_set generate_from_measurable_set
  is_pi_system_measurable_set is_pi_system_measurable_set
  μ.to_finite_spanning_sets_in ν.to_finite_spanning_sets_in (λ s hs t ht, h s t hs ht)

lemma prod_swap : map prod.swap (μ.prod ν) = ν.prod μ :=
begin
  refine (prod_eq _).symm,
  intros s t hs ht,
  simp_rw [map_apply measurable_swap (hs.prod ht), preimage_swap_prod, prod_prod, mul_comm]
end

lemma measure_preserving_swap : measure_preserving prod.swap (μ.prod ν) (ν.prod μ) :=
⟨measurable_swap, prod_swap⟩

lemma prod_apply_symm {s : set (α × β)} (hs : measurable_set s) :
  μ.prod ν s = ∫⁻ y, μ ((λ x, (x, y)) ⁻¹' s) ∂ν :=
by { rw [← prod_swap, map_apply measurable_swap hs],
     simp only [prod_apply (measurable_swap hs)], refl }

lemma prod_assoc_prod [sigma_finite τ] :
  map measurable_equiv.prod_assoc ((μ.prod ν).prod τ) = μ.prod (ν.prod τ) :=
begin
  refine (prod_eq_generate_from generate_from_measurable_set generate_from_prod
    is_pi_system_measurable_set is_pi_system_prod μ.to_finite_spanning_sets_in
    (ν.to_finite_spanning_sets_in.prod τ.to_finite_spanning_sets_in) _).symm,
  rintro s hs _ ⟨t, u, ht, hu, rfl⟩, rw [mem_set_of_eq] at hs ht hu,
  simp_rw [map_apply (measurable_equiv.measurable _) (hs.prod (ht.prod hu)),
    measurable_equiv.prod_assoc, measurable_equiv.coe_mk, equiv.prod_assoc_preimage,
    prod_prod, mul_assoc]
end

/-! ### The product of specific measures -/

lemma prod_restrict (s : set α) (t : set β) :
  (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) :=
begin
  refine prod_eq (λ s' t' hs' ht', _),
  rw [restrict_apply (hs'.prod ht'), prod_inter_prod, prod_prod, restrict_apply hs',
    restrict_apply ht']
end

lemma restrict_prod_eq_prod_univ (s : set α) :
  (μ.restrict s).prod ν = (μ.prod ν).restrict (s ×ˢ (univ : set β)) :=
begin
  have : ν = ν.restrict set.univ := measure.restrict_univ.symm,
  rwa [this, measure.prod_restrict, ← this],
end

lemma prod_dirac (y : β) : μ.prod (dirac y) = map (λ x, (x, y)) μ :=
begin
  refine prod_eq (λ s t hs ht, _),
  simp_rw [map_apply measurable_prod_mk_right (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
    dirac_apply' _ ht, ← indicator_mul_right _ (λ x, μ s), pi.one_apply, mul_one]
end

lemma dirac_prod (x : α) : (dirac x).prod ν = map (prod.mk x) ν :=
begin
  refine prod_eq (λ s t hs ht, _),
  simp_rw [map_apply measurable_prod_mk_left (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
    dirac_apply' _ hs, ← indicator_mul_left _ _ (λ x, ν t), pi.one_apply, one_mul]
end

lemma dirac_prod_dirac {x : α} {y : β} : (dirac x).prod (dirac y) = dirac (x, y) :=
by rw [prod_dirac, map_dirac measurable_prod_mk_right]

lemma prod_sum {ι : Type*} [finite ι] (ν : ι → measure β) [∀ i, sigma_finite (ν i)] :
  μ.prod (sum ν) = sum (λ i, μ.prod (ν i)) :=
begin
  refine prod_eq (λ s t hs ht, _),
  simp_rw [sum_apply _ (hs.prod ht), sum_apply _ ht, prod_prod, ennreal.tsum_mul_left]
end

lemma sum_prod {ι : Type*} [finite ι] (μ : ι → measure α) [∀ i, sigma_finite (μ i)] :
  (sum μ).prod ν = sum (λ i, (μ i).prod ν) :=
begin
  refine prod_eq (λ s t hs ht, _),
  simp_rw [sum_apply _ (hs.prod ht), sum_apply _ hs, prod_prod, ennreal.tsum_mul_right]
end

lemma prod_add (ν' : measure β) [sigma_finite ν'] : μ.prod (ν + ν') = μ.prod ν + μ.prod ν' :=
by { refine prod_eq (λ s t hs ht, _), simp_rw [add_apply, prod_prod, left_distrib] }

lemma add_prod (μ' : measure α) [sigma_finite μ'] : (μ + μ').prod ν = μ.prod ν + μ'.prod ν :=
by { refine prod_eq (λ s t hs ht, _), simp_rw [add_apply, prod_prod, right_distrib] }

@[simp] lemma zero_prod (ν : measure β) : (0 : measure α).prod ν = 0 :=
by { rw measure.prod, exact bind_zero_left _ }

@[simp] lemma prod_zero (μ : measure α) : μ.prod (0 : measure β) = 0 :=
by simp [measure.prod]

lemma map_prod_map {δ} [measurable_space δ] {f : α → β} {g : γ → δ}
  {μa : measure α} {μc : measure γ} (hfa : sigma_finite (map f μa))
  (hgc : sigma_finite (map g μc)) (hf : measurable f) (hg : measurable g) :
  (map f μa).prod (map g μc) = map (prod.map f g) (μa.prod μc) :=
begin
  haveI := hgc.of_map μc hg.ae_measurable,
  refine prod_eq (λ s t hs ht, _),
  rw [map_apply (hf.prod_map hg) (hs.prod ht), map_apply hf hs, map_apply hg ht],
  exact prod_prod (f ⁻¹' s) (g ⁻¹' t)
end

end measure

open measure

namespace measure_preserving

variables {δ : Type*} [measurable_space δ] {μa : measure α} {μb : measure β}
  {μc : measure γ} {μd : measure δ}

lemma skew_product [sigma_finite μb] [sigma_finite μd]
  {f : α → β} (hf : measure_preserving f μa μb) {g : α → γ → δ}
  (hgm : measurable (uncurry g)) (hg : ∀ᵐ x ∂μa, map (g x) μc = μd) :
  measure_preserving (λ p : α × γ, (f p.1, g p.1 p.2)) (μa.prod μc) (μb.prod μd) :=
begin
  classical,
  have : measurable (λ p : α × γ, (f p.1, g p.1 p.2)) := (hf.1.comp measurable_fst).prod_mk hgm,
  /- if `μa = 0`, then the lemma is trivial, otherwise we can use `hg`
  to deduce `sigma_finite μc`. -/
  rcases eq_or_ne μa 0 with (rfl|ha),
  { rw [← hf.map_eq, zero_prod, measure.map_zero, zero_prod],
    exact ⟨this, by simp only [measure.map_zero]⟩ },
  haveI : sigma_finite μc,
  { rcases (ae_ne_bot.2 ha).nonempty_of_mem hg with ⟨x, hx : map (g x) μc = μd⟩,
    exact sigma_finite.of_map _ hgm.of_uncurry_left.ae_measurable (by rwa hx) },
  -- Thus we can apply `measure.prod_eq` to prove equality of measures.
  refine ⟨this, (prod_eq $ λ s t hs ht, _).symm⟩,
  rw [map_apply this (hs.prod ht)],
  refine (prod_apply (this $ hs.prod ht)).trans _,
  have : ∀ᵐ x ∂μa, μc ((λ y, (f x, g x y)) ⁻¹' s ×ˢ t) = indicator (f ⁻¹' s) (λ y, μd t) x,
  { refine hg.mono (λ x hx, _), unfreezingI { subst hx },
    simp only [mk_preimage_prod_right_fn_eq_if, indicator_apply, mem_preimage],
    split_ifs,
    exacts [(map_apply hgm.of_uncurry_left ht).symm, measure_empty] },
  simp only [preimage_preimage],
  rw [lintegral_congr_ae this, lintegral_indicator _ (hf.1 hs),
    set_lintegral_const, hf.measure_preimage hs, mul_comm]
end

/-- If `f : α → β` sends the measure `μa` to `μb` and `g : γ → δ` sends the measure `μc` to `μd`,
then `prod.map f g` sends `μa.prod μc` to `μb.prod μd`. -/
protected lemma prod [sigma_finite μb] [sigma_finite μd] {f : α → β} {g : γ → δ}
  (hf : measure_preserving f μa μb) (hg : measure_preserving g μc μd) :
  measure_preserving (prod.map f g) (μa.prod μc) (μb.prod μd) :=
have measurable (uncurry $ λ _ : α, g), from (hg.1.comp measurable_snd),
hf.skew_product this $ filter.eventually_of_forall $ λ _, hg.map_eq

end measure_preserving

namespace quasi_measure_preserving

lemma prod_of_right {f : α × β → γ} {μ : measure α} {ν : measure β} {τ : measure γ}
  (hf : measurable f) [sigma_finite ν]
  (h2f : ∀ᵐ x ∂μ, quasi_measure_preserving (λ y, f (x, y)) ν τ) :
  quasi_measure_preserving f (μ.prod ν) τ :=
begin
  refine ⟨hf, _⟩,
  refine absolutely_continuous.mk (λ s hs h2s, _),
  simp_rw [map_apply hf hs, prod_apply (hf hs), preimage_preimage,
    lintegral_congr_ae (h2f.mono (λ x hx, hx.preimage_null h2s)), lintegral_zero],
end

lemma prod_of_left {α β γ} [measurable_space α] [measurable_space β]
  [measurable_space γ] {f : α × β → γ} {μ : measure α} {ν : measure β} {τ : measure γ}
  (hf : measurable f) [sigma_finite μ] [sigma_finite ν]
  (h2f : ∀ᵐ y ∂ν, quasi_measure_preserving (λ x, f (x, y)) μ τ) :
  quasi_measure_preserving f (μ.prod ν) τ :=
begin
  rw [← prod_swap],
  convert (quasi_measure_preserving.prod_of_right (hf.comp measurable_swap) h2f).comp
    ((measurable_swap.measure_preserving (ν.prod μ)).symm measurable_equiv.prod_comm)
    .quasi_measure_preserving,
  ext ⟨x, y⟩, refl,
end

end quasi_measure_preserving

end measure_theory

open measure_theory.measure

section

lemma ae_measurable.prod_swap [sigma_finite μ] [sigma_finite ν] {f : β × α → γ}
  (hf : ae_measurable f (ν.prod μ)) : ae_measurable (λ (z : α × β), f z.swap) (μ.prod ν) :=
by { rw ← prod_swap at hf, exact hf.comp_measurable measurable_swap }

lemma ae_measurable.fst [sigma_finite ν] {f : α → γ}
  (hf : ae_measurable f μ) : ae_measurable (λ (z : α × β), f z.1) (μ.prod ν) :=
hf.comp_quasi_measure_preserving quasi_measure_preserving_fst

lemma ae_measurable.snd [sigma_finite ν] {f : β → γ}
  (hf : ae_measurable f ν) : ae_measurable (λ (z : α × β), f z.2) (μ.prod ν) :=
hf.comp_quasi_measure_preserving quasi_measure_preserving_snd

end

namespace measure_theory

/-! ### The Lebesgue integral on a product -/

variables [sigma_finite ν]

lemma lintegral_prod_swap [sigma_finite μ] (f : α × β → ℝ≥0∞)
  (hf : ae_measurable f (μ.prod ν)) : ∫⁻ z, f z.swap ∂(ν.prod μ) = ∫⁻ z, f z ∂(μ.prod ν) :=
by { rw ← prod_swap at hf, rw [← lintegral_map' hf measurable_swap.ae_measurable, prod_swap] }

/-- **Tonelli's Theorem**: For `ℝ≥0∞`-valued measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
lemma lintegral_prod_of_measurable :
  ∀ (f : α × β → ℝ≥0∞) (hf : measurable f), ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
begin
  have m := @measurable_prod_mk_left,
  refine measurable.ennreal_induction _ _ _,
  { intros c s hs, simp only [← indicator_comp_right],
    simp [lintegral_indicator, m hs, hs, lintegral_const_mul, measurable_measure_prod_mk_left hs,
      prod_apply] },
  { rintro f g - hf hg h2f h2g,
    simp [lintegral_add_left, measurable.lintegral_prod_right', hf.comp m, hf, h2f, h2g] },
  { intros f hf h2f h3f,
    have kf : ∀ x n, measurable (λ y, f n (x, y)) := λ x n, (hf n).comp m,
    have k2f : ∀ x, monotone (λ n y, f n (x, y)) := λ x i j hij y, h2f hij (x, y),
    have lf : ∀ n, measurable (λ x, ∫⁻ y, f n (x, y) ∂ν) := λ n, (hf n).lintegral_prod_right',
    have l2f : monotone (λ n x, ∫⁻ y, f n (x, y) ∂ν) := λ i j hij x, lintegral_mono (k2f x hij),
    simp only [lintegral_supr hf h2f, lintegral_supr (kf _), k2f, lintegral_supr lf l2f, h3f] },
end

/-- **Tonelli's Theorem**: For `ℝ≥0∞`-valued almost everywhere measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
lemma lintegral_prod (f : α × β → ℝ≥0∞) (hf : ae_measurable f (μ.prod ν)) :
  ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
begin
  have A : ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ z, hf.mk f z ∂(μ.prod ν) :=
    lintegral_congr_ae hf.ae_eq_mk,
  have B : ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ = ∫⁻ x, ∫⁻ y, hf.mk f (x, y) ∂ν ∂μ,
  { apply lintegral_congr_ae,
    filter_upwards [ae_ae_of_ae_prod hf.ae_eq_mk] with _ ha using lintegral_congr_ae ha, },
  rw [A, B, lintegral_prod_of_measurable _ hf.measurable_mk],
  apply_instance
end

/-- The symmetric verion of Tonelli's Theorem: For `ℝ≥0∞`-valued almost everywhere measurable
functions on `α × β`,  the integral of `f` is equal to the iterated integral, in reverse order. -/
lemma lintegral_prod_symm [sigma_finite μ] (f : α × β → ℝ≥0∞)
  (hf : ae_measurable f (μ.prod ν)) : ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
by { simp_rw [← lintegral_prod_swap f hf], exact lintegral_prod _ hf.prod_swap }

/-- The symmetric verion of Tonelli's Theorem: For `ℝ≥0∞`-valued measurable
functions on `α × β`,  the integral of `f` is equal to the iterated integral, in reverse order. -/
lemma lintegral_prod_symm' [sigma_finite μ] (f : α × β → ℝ≥0∞)
  (hf : measurable f) : ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
lintegral_prod_symm f hf.ae_measurable

/-- The reversed version of **Tonelli's Theorem**. In this version `f` is in curried form, which
makes it easier for the elaborator to figure out `f` automatically. -/
lemma lintegral_lintegral ⦃f : α → β → ℝ≥0∞⦄
  (hf : ae_measurable (uncurry f) (μ.prod ν)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.1 z.2 ∂(μ.prod ν) :=
(lintegral_prod _ hf).symm

/-- The reversed version of **Tonelli's Theorem** (symmetric version). In this version `f` is in
curried form, which makes it easier for the elaborator to figure out `f` automatically. -/
lemma lintegral_lintegral_symm [sigma_finite μ] ⦃f : α → β → ℝ≥0∞⦄
  (hf : ae_measurable (uncurry f) (μ.prod ν)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.2 z.1 ∂(ν.prod μ) :=
(lintegral_prod_symm _ hf.prod_swap).symm

/-- Change the order of Lebesgue integration. -/
lemma lintegral_lintegral_swap [sigma_finite μ] ⦃f : α → β → ℝ≥0∞⦄
  (hf : ae_measurable (uncurry f) (μ.prod ν)) :
  ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν :=
(lintegral_lintegral hf).trans (lintegral_prod_symm _ hf)

lemma lintegral_prod_mul {f : α → ℝ≥0∞} {g : β → ℝ≥0∞}
  (hf : ae_measurable f μ) (hg : ae_measurable g ν) :
  ∫⁻ z, f z.1 * g z.2 ∂(μ.prod ν) = ∫⁻ x, f x ∂μ * ∫⁻ y, g y ∂ν :=
by simp [lintegral_prod _ (hf.fst.mul hg.snd), lintegral_lintegral_mul hf hg]

/-! ### Marginals of a measure defined on a product -/

namespace measure

variables {ρ : measure (α × β)}

/-- Marginal measure on `α` obtained from a measure `ρ` on `α × β`, defined by `ρ.map prod.fst`. -/
noncomputable
def fst (ρ : measure (α × β)) : measure α := ρ.map prod.fst

lemma fst_apply {s : set α} (hs : measurable_set s) : ρ.fst s = ρ (prod.fst ⁻¹' s) :=
by rw [fst, measure.map_apply measurable_fst hs]

lemma fst_univ : ρ.fst univ = ρ univ :=
by rw [fst_apply measurable_set.univ, preimage_univ]

instance [is_finite_measure ρ] : is_finite_measure ρ.fst := by { rw fst, apply_instance, }

instance [is_probability_measure ρ] : is_probability_measure ρ.fst :=
{ measure_univ := by { rw fst_univ, exact measure_univ, } }

/-- Marginal measure on `β` obtained from a measure on `ρ` `α × β`, defined by `ρ.map prod.snd`. -/
noncomputable
def snd (ρ : measure (α × β)) : measure β := ρ.map prod.snd

lemma snd_apply {s : set β} (hs : measurable_set s) : ρ.snd s = ρ (prod.snd ⁻¹' s) :=
by rw [snd, measure.map_apply measurable_snd hs]

lemma snd_univ : ρ.snd univ = ρ univ :=
by rw [snd_apply measurable_set.univ, preimage_univ]

instance [is_finite_measure ρ] : is_finite_measure ρ.snd := by { rw snd, apply_instance, }

instance [is_probability_measure ρ] : is_probability_measure ρ.snd :=
{ measure_univ := by { rw snd_univ, exact measure_univ, } }

end measure


end measure_theory
