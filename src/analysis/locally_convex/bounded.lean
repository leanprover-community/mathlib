/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.locally_convex.basic
import analysis.locally_convex.balanced_core_hull
import analysis.normed_space.is_R_or_C
import analysis.seminorm
import topology.bornology.basic
import topology.algebra.uniform_group
import topology.uniform_space.cauchy

/-!
# Von Neumann Boundedness

This file defines natural or von Neumann bounded sets and proves elementary properties.

## Main declarations

* `bornology.is_vonN_bounded`: A set `s` is von Neumann-bounded if every neighborhood of zero
absorbs `s`.
* `bornology.vonN_bornology`: The bornology made of the von Neumann-bounded sets.

## Main results

* `bornology.is_vonN_bounded_of_topological_space_le`: A coarser topology admits more
von Neumann-bounded sets.
* `bornology.is_vonN_bounded.image`: A continuous linear image of a bounded set is bounded.
* `linear_map.continuous_of_locally_bounded`: If `E` is first countable, then every
locally bounded linear map `E →ₛₗ[σ] F` is continuous.

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

variables {𝕜 𝕜' E F ι : Type*}

open filter
open_locale topological_space pointwise

namespace bornology

section semi_normed_ring

section has_zero

variables (𝕜)
variables [semi_normed_ring 𝕜] [has_smul 𝕜 E] [has_zero E]
variables [topological_space E]

/-- A set `s` is von Neumann bounded if every neighborhood of 0 absorbs `s`. -/
def is_vonN_bounded (s : set E) : Prop := ∀ ⦃V⦄, V ∈ 𝓝 (0 : E) → absorbs 𝕜 V s

variables (E)

@[simp] lemma is_vonN_bounded_empty : is_vonN_bounded 𝕜 (∅ : set E) :=
λ _ _, absorbs_empty

variables {𝕜 E}

lemma is_vonN_bounded_iff (s : set E) : is_vonN_bounded 𝕜 s ↔ ∀ V ∈ 𝓝 (0 : E), absorbs 𝕜 V s :=
iff.rfl

lemma _root_.filter.has_basis.is_vonN_bounded_basis_iff {q : ι → Prop} {s : ι → set E} {A : set E}
  (h : (𝓝 (0 : E)).has_basis q s) :
  is_vonN_bounded 𝕜 A ↔ ∀ i (hi : q i), absorbs 𝕜 (s i) A :=
begin
  refine ⟨λ hA i hi, hA (h.mem_of_mem hi), λ hA V hV, _⟩,
  rcases h.mem_iff.mp hV with ⟨i, hi, hV⟩,
  exact (hA i hi).mono_left hV,
end

/-- Subsets of bounded sets are bounded. -/
lemma is_vonN_bounded.subset {s₁ s₂ : set E} (h : s₁ ⊆ s₂) (hs₂ : is_vonN_bounded 𝕜 s₂) :
  is_vonN_bounded 𝕜 s₁ :=
λ V hV, (hs₂ hV).mono_right h

/-- The union of two bounded sets is bounded. -/
lemma is_vonN_bounded.union {s₁ s₂ : set E} (hs₁ : is_vonN_bounded 𝕜 s₁)
  (hs₂ : is_vonN_bounded 𝕜 s₂) :
  is_vonN_bounded 𝕜 (s₁ ∪ s₂) :=
λ V hV, (hs₁ hV).union (hs₂ hV)

end has_zero

end semi_normed_ring

section multiple_topologies

variables [semi_normed_ring 𝕜] [add_comm_group E] [module 𝕜 E]

/-- If a topology `t'` is coarser than `t`, then any set `s` that is bounded with respect to
`t` is bounded with respect to `t'`. -/
lemma is_vonN_bounded.of_topological_space_le {t t' : topological_space E} (h : t ≤ t') {s : set E}
  (hs : @is_vonN_bounded 𝕜 E _ _ _ t s) : @is_vonN_bounded 𝕜 E _ _ _ t' s :=
λ V hV, hs $ (le_iff_nhds t t').mp h 0 hV

end multiple_topologies

section image

variables {𝕜₁ 𝕜₂ : Type*} [normed_division_ring 𝕜₁] [normed_division_ring 𝕜₂]
  [add_comm_group E] [module 𝕜₁ E] [add_comm_group F] [module 𝕜₂ F]
  [topological_space E] [topological_space F]

/-- A continuous linear image of a bounded set is bounded. -/
lemma is_vonN_bounded.image {σ : 𝕜₁ →+* 𝕜₂} [ring_hom_surjective σ] [ring_hom_isometric σ]
  {s : set E} (hs : is_vonN_bounded 𝕜₁ s) (f : E →SL[σ] F) :
  is_vonN_bounded 𝕜₂ (f '' s) :=
begin
  let σ' := ring_equiv.of_bijective σ ⟨σ.injective, σ.is_surjective⟩,
  have σ_iso : isometry σ := add_monoid_hom_class.isometry_of_norm σ
    (λ x, ring_hom_isometric.is_iso),
  have σ'_symm_iso : isometry σ'.symm := σ_iso.right_inv σ'.right_inv,
  have f_tendsto_zero := f.continuous.tendsto 0,
  rw map_zero at f_tendsto_zero,
  intros V hV,
  rcases hs (f_tendsto_zero hV) with ⟨r, hrpos, hr⟩,
  refine ⟨r, hrpos, λ a ha, _⟩,
  rw ← σ'.apply_symm_apply a,
  have hanz : a ≠ 0 := norm_pos_iff.mp (hrpos.trans_le ha),
  have : σ'.symm a ≠ 0 := (map_ne_zero σ'.symm.to_ring_hom).mpr hanz,
  change _ ⊆ σ _ • _,
  rw [set.image_subset_iff, preimage_smul_setₛₗ _ _ _ f this.is_unit],
  refine hr (σ'.symm a) _,
  rwa σ'_symm_iso.norm_map_of_map_zero (map_zero _)
end

end image

section normed_field

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [topological_space E] [has_continuous_smul 𝕜 E]

/-- Singletons are bounded. -/
lemma is_vonN_bounded_singleton (x : E) : is_vonN_bounded 𝕜 ({x} : set E) :=
λ V hV, (absorbent_nhds_zero hV).absorbs

/-- The union of all bounded set is the whole space. -/
lemma is_vonN_bounded_covers : ⋃₀ (set_of (is_vonN_bounded 𝕜)) = (set.univ : set E) :=
set.eq_univ_iff_forall.mpr (λ x, set.mem_sUnion.mpr
  ⟨{x}, is_vonN_bounded_singleton _, set.mem_singleton _⟩)

variables (𝕜 E)

/-- The von Neumann bornology defined by the von Neumann bounded sets.

Note that this is not registered as an instance, in order to avoid diamonds with the
metric bornology.-/
@[reducible] -- See note [reducible non-instances]
def vonN_bornology : bornology E :=
bornology.of_bounded (set_of (is_vonN_bounded 𝕜)) (is_vonN_bounded_empty 𝕜 E)
  (λ _ hs _ ht, hs.subset ht) (λ _ hs _, hs.union) is_vonN_bounded_singleton

variables {E}

@[simp] lemma is_bounded_iff_is_vonN_bounded {s : set E} :
  @is_bounded _ (vonN_bornology 𝕜 E) s ↔ is_vonN_bounded 𝕜 s :=
is_bounded_of_bounded_iff _

end normed_field

end bornology

section uniform_add_group

variables (𝕜) [nontrivially_normed_field 𝕜] [add_comm_group E] [module 𝕜 E]
variables [uniform_space E] [uniform_add_group E] [has_continuous_smul 𝕜 E]

lemma totally_bounded.is_vonN_bounded {s : set E} (hs : totally_bounded s) :
  bornology.is_vonN_bounded 𝕜 s :=
begin
  rw totally_bounded_iff_subset_finite_Union_nhds_zero at hs,
  intros U hU,
  have h : filter.tendsto (λ (x : E × E), x.fst + x.snd) (𝓝 (0,0)) (𝓝 ((0 : E) + (0 : E))) :=
    tendsto_add,
  rw add_zero at h,
  have h' := (nhds_basis_balanced 𝕜 E).prod (nhds_basis_balanced 𝕜 E),
  simp_rw [←nhds_prod_eq, id.def] at h',
  rcases h.basis_left h' U hU with ⟨x, hx, h''⟩,
  rcases hs x.snd hx.2.1 with ⟨t, ht, hs⟩,
  refine absorbs.mono_right _ hs,
  rw ht.absorbs_Union,
  have hx_fstsnd : x.fst + x.snd ⊆ U,
  { intros z hz,
    rcases set.mem_add.mp hz with ⟨z1, z2, hz1, hz2, hz⟩,
    have hz' : (z1, z2) ∈ x.fst ×ˢ x.snd := ⟨hz1, hz2⟩,
    simpa only [hz] using h'' hz' },
  refine λ y hy, absorbs.mono_left _ hx_fstsnd,
  rw [←set.singleton_vadd, vadd_eq_add],
  exact (absorbent_nhds_zero hx.1.1).absorbs.add hx.2.2.absorbs_self,
end

end uniform_add_group

section continuous_linear_map

variables [add_comm_group E] [uniform_space E] [uniform_add_group E]
variables [add_comm_group F] [uniform_space F]

section nontrivially_normed_field

variables [uniform_add_group F]
variables [nontrivially_normed_field 𝕜] [module 𝕜 E] [module 𝕜 F] [has_continuous_smul 𝕜 E]

/-- Construct a continuous linear map from a linear map `f : E →ₗ[𝕜] F` and the existence of a
neighborhood of zero that gets mapped into a bounded set in `F`. -/
def linear_map.clm_of_exists_bounded_image (f : E →ₗ[𝕜] F)
  (h : ∃ (V : set E) (hV : V ∈ 𝓝 (0 : E)), bornology.is_vonN_bounded 𝕜 (f '' V)) : E →L[𝕜] F :=
⟨f, begin
  -- It suffices to show that `f` is continuous at `0`.
  refine continuous_of_continuous_at_zero f _,
  rw [continuous_at_def, f.map_zero],
  intros U hU,
  -- Continuity means that `U ∈ 𝓝 0` implies that `f ⁻¹' U ∈ 𝓝 0`.
  rcases h with ⟨V, hV, h⟩,
  rcases h hU with ⟨r, hr, h⟩,
  rcases normed_field.exists_lt_norm 𝕜 r with ⟨x, hx⟩,
  specialize h x hx.le,
  -- After unfolding all the definitions, we know that `f '' V ⊆ x • U`. We use this to show the
  -- inclusion `x⁻¹ • V ⊆ f⁻¹' U`.
  have x_ne := norm_pos_iff.mp (hr.trans hx),
  have : x⁻¹ • V ⊆ f⁻¹' U :=
  calc x⁻¹ • V ⊆  x⁻¹ • (f⁻¹' (f '' V)) : set.smul_set_mono (set.subset_preimage_image ⇑f V)
  ... ⊆ x⁻¹ • (f⁻¹' (x • U)) : set.smul_set_mono (set.preimage_mono h)
  ... = f⁻¹' (x⁻¹ • (x • U)) :
      by ext; simp only [set.mem_inv_smul_set_iff₀ x_ne, set.mem_preimage, linear_map.map_smul]
  ... ⊆ f⁻¹' U : by rw inv_smul_smul₀ x_ne _,
  -- Using this inclusion, it suffices to show that `x⁻¹ • V` is in `𝓝 0`, which is trivial.
  refine mem_of_superset _ this,
  convert set_smul_mem_nhds_smul hV (inv_ne_zero x_ne),
  exact (smul_zero _).symm,
end⟩

lemma linear_map.clm_of_exists_bounded_image_coe {f : E →ₗ[𝕜] F}
  {h : ∃ (V : set E) (hV : V ∈ 𝓝 (0 : E)), bornology.is_vonN_bounded 𝕜 (f '' V)} :
  (f.clm_of_exists_bounded_image h : E →ₗ[𝕜] F) = f := rfl

@[simp] lemma linear_map.clm_of_exists_bounded_image_apply {f : E →ₗ[𝕜] F}
  {h : ∃ (V : set E) (hV : V ∈ 𝓝 (0 : E)), bornology.is_vonN_bounded 𝕜 (f '' V)} {x : E} :
  f.clm_of_exists_bounded_image h x = f x := rfl

end nontrivially_normed_field

section is_R_or_C

open topological_space bornology

variables [first_countable_topology E]
variables [is_R_or_C 𝕜] [module 𝕜 E] [has_continuous_smul 𝕜 E]
variables [is_R_or_C 𝕜'] [module 𝕜' F] [has_continuous_smul 𝕜' F]
variables {σ : 𝕜 →+* 𝕜'}

lemma linear_map.continuous_at_zero_of_locally_bounded (f : E →ₛₗ[σ] F)
  (hf : ∀ (s : set E) (hs : is_vonN_bounded 𝕜 s), is_vonN_bounded 𝕜' (f '' s)) :
  continuous_at f 0 :=
begin
  -- Assume that f is not continuous at 0
  by_contradiction,
  -- We use the a decreasing balanced basis for 0 : E and a balanced basis for 0 : F
  -- and reformulate non-continuity in terms of these bases
  rcases (nhds_basis_balanced 𝕜 E).exists_antitone_subbasis with ⟨b, bE1, bE⟩,
  simp only [id.def] at bE,
  have bE' : (𝓝 (0 : E)).has_basis (λ (x : ℕ), x ≠ 0) (λ n : ℕ, (n : 𝕜)⁻¹ • b n) :=
  begin
    refine bE.1.to_has_basis _ _,
    { intros n _,
      use n+1,
      simp only [ne.def, nat.succ_ne_zero, not_false_iff, nat.cast_add, nat.cast_one, true_and],
      -- `b (n + 1) ⊆ b n` follows from `antitone`.
      have h : b (n + 1) ⊆ b n := bE.2 (by simp),
      refine subset_trans _ h,
      rintros y ⟨x, hx, hy⟩,
      -- Since `b (n + 1)` is balanced `(n+1)⁻¹ b (n + 1) ⊆ b (n + 1)`
      rw ←hy,
      refine (bE1 (n+1)).2.smul_mem  _ hx,
      have h' : 0 < (n : ℝ) + 1 := n.cast_add_one_pos,
      rw [norm_inv, ←nat.cast_one, ←nat.cast_add, is_R_or_C.norm_eq_abs, is_R_or_C.abs_cast_nat,
        nat.cast_add, nat.cast_one, inv_le h' zero_lt_one],
      norm_cast,
      simp, },
    intros n hn,
    -- The converse direction follows from continuity of the scalar multiplication
    have hcont : continuous_at (λ (x : E), (n : 𝕜) • x) 0 :=
    (continuous_const_smul (n : 𝕜)).continuous_at,
    simp only [continuous_at, map_zero, smul_zero] at hcont,
    rw bE.1.tendsto_left_iff at hcont,
    rcases hcont (b n) (bE1 n).1 with ⟨i, _, hi⟩,
    refine ⟨i, trivial, λ x hx, ⟨(n : 𝕜) • x, hi hx, _⟩⟩,
    simp [←mul_smul, hn],
  end,
  rw [continuous_at, map_zero, bE'.tendsto_iff (nhds_basis_balanced 𝕜' F)] at h,
  push_neg at h,
  rcases h with ⟨V, ⟨hV, hV'⟩, h⟩,
  simp only [id.def, forall_true_left] at h,
  -- There exists `u : ℕ → E` such that for all `n : ℕ` we have `u n ∈ n⁻¹ • b n` and `f (u n) ∉ V`
  choose! u hu hu' using h,
  -- The sequence `(λ n, n • u n)` converges to `0`
  have h_tendsto : tendsto (λ n : ℕ, (n : 𝕜) • u n) at_top (𝓝 (0 : E)) :=
  begin
    apply bE.tendsto,
    intros n,
    by_cases h : n = 0,
    { rw [h, nat.cast_zero, zero_smul],
      refine mem_of_mem_nhds (bE.1.mem_of_mem $ by triv) },
    rcases hu n h with ⟨y, hy, hu1⟩,
    convert hy,
    rw [←hu1, ←mul_smul],
    simp only [h, mul_inv_cancel, ne.def, nat.cast_eq_zero, not_false_iff, one_smul],
  end,
  -- The image `(λ n, n • u n)` is von Neumann bounded:
  have h_bounded : is_vonN_bounded 𝕜 (set.range (λ n : ℕ, (n : 𝕜) • u n)) :=
  h_tendsto.cauchy_seq.totally_bounded_range.is_vonN_bounded 𝕜,
  -- Since `range u` is bounded it absorbs `V`
  rcases hf _ h_bounded hV with ⟨r, hr, h'⟩,
  cases exists_nat_gt r with n hn,
  -- We now find a contradiction between `f (u n) ∉ V` and the absorbing property
  have h1 : r ≤ ∥(n : 𝕜')∥ :=
  by { rw [is_R_or_C.norm_eq_abs, is_R_or_C.abs_cast_nat], exact hn.le },
  have hn' : 0 < ∥(n : 𝕜')∥ := lt_of_lt_of_le hr h1,
  rw [norm_pos_iff, ne.def, nat.cast_eq_zero] at hn',
  have h'' : f (u n) ∈ V :=
  begin
    simp only [set.image_subset_iff] at h',
    specialize h' (n : 𝕜') h1 (set.mem_range_self n),
    simp only [set.mem_preimage, linear_map.map_smulₛₗ, map_nat_cast] at h',
    rcases h' with ⟨y, hy, h'⟩,
    apply_fun (λ y : F, (n : 𝕜')⁻¹ • y) at h',
    simp only [hn', inv_smul_smul₀, ne.def, nat.cast_eq_zero, not_false_iff] at h',
    rwa ←h',
  end,
  exact hu' n hn' h'',
end

/-- If `E` is first countable, then every locally bounded linear map `E →ₛₗ[σ] F` is continuous. -/
lemma linear_map.continuous_of_locally_bounded [uniform_add_group F] (f : E →ₛₗ[σ] F)
  (hf : ∀ (s : set E) (hs : is_vonN_bounded 𝕜 s), is_vonN_bounded 𝕜' (f '' s)) :
  continuous f :=
(uniform_continuous_of_continuous_at_zero f $ f.continuous_at_zero_of_locally_bounded hf).continuous

end is_R_or_C

end continuous_linear_map

section vonN_bornology_eq_metric

variables (𝕜 E) [nontrivially_normed_field 𝕜] [seminormed_add_comm_group E] [normed_space 𝕜 E]

namespace normed_space

lemma is_vonN_bounded_ball (r : ℝ) :
  bornology.is_vonN_bounded 𝕜 (metric.ball (0 : E) r) :=
begin
  rw [metric.nhds_basis_ball.is_vonN_bounded_basis_iff, ← ball_norm_seminorm 𝕜 E],
  exact λ ε hε, (norm_seminorm 𝕜 E).ball_zero_absorbs_ball_zero hε
end

lemma is_vonN_bounded_closed_ball (r : ℝ) :
  bornology.is_vonN_bounded 𝕜 (metric.closed_ball (0 : E) r) :=
(is_vonN_bounded_ball 𝕜 E (r+1)).subset (metric.closed_ball_subset_ball $ by linarith)

lemma is_vonN_bounded_iff (s : set E) :
  bornology.is_vonN_bounded 𝕜 s ↔ bornology.is_bounded s :=
begin
  rw [← metric.bounded_iff_is_bounded, metric.bounded_iff_subset_ball (0 : E)],
  split,
  { intros h,
    rcases h (metric.ball_mem_nhds 0 zero_lt_one) with ⟨ρ, hρ, hρball⟩,
    rcases normed_field.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩,
    specialize hρball a ha.le,
    rw [← ball_norm_seminorm 𝕜 E, seminorm.smul_ball_zero (hρ.trans ha),
        ball_norm_seminorm, mul_one] at hρball,
    exact ⟨∥a∥, hρball.trans metric.ball_subset_closed_ball⟩ },
  { exact λ ⟨C, hC⟩, (is_vonN_bounded_closed_ball 𝕜 E C).subset hC }
end

/-- In a normed space, the von Neumann bornology (`bornology.vonN_bornology`) is equal to the
metric bornology. -/
lemma vonN_bornology_eq : bornology.vonN_bornology 𝕜 E = pseudo_metric_space.to_bornology :=
begin
  rw bornology.ext_iff_is_bounded,
  intro s,
  rw bornology.is_bounded_iff_is_vonN_bounded,
  exact is_vonN_bounded_iff 𝕜 E s
end

variable (𝕜)

lemma is_bounded_iff_subset_smul_ball {s : set E} :
  bornology.is_bounded s ↔ ∃ a : 𝕜, s ⊆ a • metric.ball 0 1 :=
begin
  rw ← is_vonN_bounded_iff 𝕜,
  split,
  { intros h,
    rcases h (metric.ball_mem_nhds 0 zero_lt_one) with ⟨ρ, hρ, hρball⟩,
    rcases normed_field.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩,
    exact ⟨a, hρball a ha.le⟩ },
  { rintros ⟨a, ha⟩,
    exact ((is_vonN_bounded_ball 𝕜 E 1).image (a • 1 : E →L[𝕜] E)).subset ha }
end

lemma is_bounded_iff_subset_smul_closed_ball {s : set E} :
  bornology.is_bounded s ↔ ∃ a : 𝕜, s ⊆ a • metric.closed_ball 0 1 :=
begin
  split,
  { rw is_bounded_iff_subset_smul_ball 𝕜,
    exact exists_imp_exists
      (λ a ha, ha.trans $ set.smul_set_mono $ metric.ball_subset_closed_ball) },
  { rw ← is_vonN_bounded_iff 𝕜,
    rintros ⟨a, ha⟩,
    exact ((is_vonN_bounded_closed_ball 𝕜 E 1).image (a • 1 : E →L[𝕜] E)).subset ha }
end

end normed_space

end vonN_bornology_eq_metric
