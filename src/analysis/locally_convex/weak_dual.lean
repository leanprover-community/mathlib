/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import topology.algebra.module.weak_dual
import analysis.normed.normed_field
import analysis.seminorm

/-!
# Weak Dual in Topological Vector Spaces

## Main definitions

* `weak_bilin_basis_zero`: a basis for the neighborhood filter at 0.
* `linear_map.to_seminorm_family`: turn a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`
into a map `F → seminorm 𝕜 E`.

## Main statements

* `with_seminorms B.to_seminorm_family`: the topology of a weak space is induced by the family of
seminorm `B.to_seminorm_family`.
* `weak_bilin.to_locally_convex_space'`: a spaced endowed with a weak topology is locally convex.

## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

weak dual, seminorm
-/

variables {α β 𝕜 E F ι : Type*}

open_locale topological_space

section topological_add_group


-- Stuff to be moved to `analysis.seminorm`

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F]
variables [topological_space E] [topological_add_group E]
variables [nonempty ι]


lemma with_seminorms_of_nhds (p : ι → seminorm 𝕜 E)
  (h : 𝓝 (0 : E) = (seminorm.seminorm_module_filter_basis p).to_filter_basis.filter) :
  seminorm.with_seminorms p :=
begin
  refine ⟨topological_add_group.ext (by apply_instance)
    ((seminorm.seminorm_add_group_filter_basis _).is_topological_add_group) _⟩,
  rw add_group_filter_basis.nhds_zero_eq,
  exact h,
end

lemma with_seminorms_of_has_basis (p : ι → seminorm 𝕜 E) (h : (𝓝 (0 : E)).has_basis
  (λ (s : set E), s ∈ (seminorm.seminorm_basis_zero p)) id) :
  seminorm.with_seminorms p :=
with_seminorms_of_nhds p $ filter.has_basis.eq_of_same_basis h
  ((seminorm.seminorm_add_group_filter_basis p).to_filter_basis.has_basis)

end topological_add_group

section seminorm_sup

namespace seminorm

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F]

lemma sup_le_apply (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {a : ℝ} (ha : 0 < a):
  (∀ (i : ι), i ∈ s → p i x ≤ a) → s.sup p x ≤ a :=
begin
  intro h,
  rw [finset_sup_apply, ←a.coe_to_nnreal ha.le, nnreal.coe_le_coe],
  refine finset.sup_le (λ i hi, _),
  rw [←nnreal.coe_le_coe, subtype.coe_mk, a.coe_to_nnreal ha.le],
  exact h i hi,
end

lemma sup_lt_apply {p : ι → seminorm 𝕜 E} {s : finset ι} {x : E} {a : ℝ} (ha : 0 < a):
  (∀ (i : ι), i ∈ s → p i x < a) → s.sup p x < a :=
begin
  intro h,
  rw [finset_sup_apply, ←a.coe_to_nnreal ha.le, nnreal.coe_lt_coe],
  refine (finset.sup_lt_iff (real.to_nnreal_pos.mpr ha)).mpr (λ i hi, _),
  rw [←nnreal.coe_lt_coe, subtype.coe_mk, a.coe_to_nnreal ha.le],
  exact h i hi,
end

end seminorm

end seminorm_sup


section linear_maps

namespace linear_map

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F]

def to_seminorm (f : E →ₗ[𝕜] 𝕜) : seminorm 𝕜 E :=
{ to_fun := λ x, ∥f x∥,
  smul' := λ a x, by simp only [map_smulₛₗ, ring_hom.id_apply, smul_eq_mul, norm_mul],
  triangle' := λ x x', by { simp only [map_add, add_apply], exact norm_add_le _ _ } }

lemma coe_to_seminorm {f : E →ₗ[𝕜] 𝕜} :
  ⇑f.to_seminorm = λ x, ∥f x∥ := rfl

@[simp] lemma to_seminorm_apply {f : E →ₗ[𝕜] 𝕜} {x : E} :
  f.to_seminorm x = ∥f x∥ := rfl

lemma to_seminorm_ball_zero {f : E →ₗ[𝕜] 𝕜} {r : ℝ} :
  seminorm.ball f.to_seminorm 0 r = { x : E | ∥f x∥ < r} :=
by simp only [seminorm.ball_zero_eq, to_seminorm_apply]

lemma to_seminorm_comp (f : F →ₗ[𝕜] 𝕜) (g : E →ₗ[𝕜] F) :
  f.to_seminorm.comp g = (f.comp g).to_seminorm :=
by { ext, simp only [seminorm.comp_apply, to_seminorm_apply, coe_comp] }


end linear_map

end linear_maps

-- End of stuff to be moved to `analysis.seminorm`


section topology

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F]
variables [nonempty ι]

variables {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (x : E) (y : F)

namespace linear_map

def to_seminorm_family (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (y : F) : seminorm 𝕜 E := (B.flip y).to_seminorm

@[simp] lemma to_seminorm_family_apply {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {x y} :
  (B.to_seminorm_family y) x = ∥B x y∥ := rfl

end linear_map

namespace seminorm

def weak_bilin_basis_zero (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : set (set E) :=
⋃ (s : finset F) (hs : s.nonempty) r (hr : 0 < r), { s.inf' hs (λ y, { x : E | ∥B x y∥ < r}) }

lemma weak_bilin_basis_zero_iff {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} {U : set E}:
  U ∈ weak_bilin_basis_zero B ↔ ∃ (s : finset F) (hs : s.nonempty) r (hr : 0 < r),
    U = s.inf' hs (λ y, { x : E | ∥B x y∥ < r}) :=
by simp only [weak_bilin_basis_zero, set.mem_Union, set.mem_singleton_iff]

end seminorm


lemma has_basis_weak_bilin (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
  (𝓝 (0 : weak_bilin B)).has_basis (seminorm.seminorm_basis_zero B.to_seminorm_family) id :=
begin
  let p := B.to_seminorm_family,
  rw [nhds_induced, nhds_pi],
  simp only [map_zero, linear_map.zero_apply],
  have h := @metric.nhds_basis_ball 𝕜 _ 0,
  have h' := filter.has_basis_pi (λ (i : F), h),
  have h'' := filter.has_basis.comap (λ x y, B x y) h',
  refine h''.to_has_basis _ _,
  { rintros (U : set F × (F → ℝ)) hU,
    cases hU with hU₁ hU₂,
    simp only [id.def],
    let U' := hU₁.to_finset,
    simp only at hU₂,
    by_cases hU₃ : U.fst.nonempty,
    { have hU₃' : U'.nonempty := (set.finite.to_finset.nonempty hU₁).mpr hU₃,
      let r := U'.inf' hU₃' U.snd,
      have hr : 0 < r :=
      (finset.lt_inf'_iff hU₃' _).mpr (λ y hy, hU₂ y ((set.finite.mem_to_finset hU₁).mp hy)),
      use [seminorm.ball (U'.sup p) (0 : E) r],
      refine ⟨seminorm.seminorm_basis_zero_mem _ _ hr, λ x hx y hy, _⟩,
      simp only [set.mem_preimage, set.mem_pi, mem_ball_zero_iff],
      rw seminorm.mem_ball_zero at hx,
      rw ←linear_map.to_seminorm_family_apply,
      have hyU' : y ∈ U' := (set.finite.mem_to_finset hU₁).mpr hy,
      have hp : p y ≤ U'.sup p := finset.le_sup hyU',
      refine lt_of_le_of_lt (hp x) (lt_of_lt_of_le hx _),
      exact finset.inf'_le _ hyU' },
    rw set.not_nonempty_iff_eq_empty.mp hU₃,
    simp only [set.empty_pi, set.preimage_univ, set.subset_univ, and_true],
    exact Exists.intro ((p 0).ball 0 1) (seminorm.seminorm_basis_zero_singleton_mem p 0 one_pos) },
  rintros U (hU : U ∈ seminorm.seminorm_basis_zero p),
  rw seminorm.seminorm_basis_zero_iff at hU,
  rcases hU with ⟨s, r, hr, hU⟩,
  rw hU,
  refine ⟨(s, λ _, r), ⟨by simp only [s.finite_to_set], λ y hy, hr⟩, λ x hx, _⟩,
  simp only [set.mem_preimage, set.mem_pi, finset.mem_coe, mem_ball_zero_iff] at hx,
  simp only [id.def, seminorm.mem_ball, sub_zero],
  refine seminorm.sup_lt_apply hr (λ y hy, _),
  rw linear_map.to_seminorm_family_apply,
  exact hx y hy,
end

instance : seminorm.with_seminorms (linear_map.to_seminorm_family B : F → seminorm 𝕜 (weak_bilin B)) :=
with_seminorms_of_has_basis _ (has_basis_weak_bilin _)

variables [has_scalar ℝ 𝕜] [module ℝ E] [is_scalar_tower ℝ 𝕜 E]

-- todo: it should be possible to this in more generality in `topology.algebra.module.weak_dual`
instance module_ℝ [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F]
  [module 𝕜 F] [has_scalar ℝ 𝕜] [module ℝ E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
  module ℝ (weak_bilin B) :=
by { dunfold weak_bilin, apply_instance }

instance scalar_tower_ℝ [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F]
  [module 𝕜 F] [has_scalar ℝ 𝕜] [module ℝ E] [is_scalar_tower ℝ 𝕜 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
  is_scalar_tower ℝ 𝕜 (weak_bilin B) :=
by { dunfold weak_bilin, apply_instance }


end topology

section locally_convex

-- todo: fix stuff in `analysis.seminorm` so that `normed_linear_ordered_field` is not used.
variables [normed_linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F]
  [module 𝕜 F]
variables [nonempty ι]
variables [normed_space ℝ 𝕜] [module ℝ E] [is_scalar_tower ℝ 𝕜 E]
variables {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜}

lemma weak_bilin.to_locally_convex_space' :
  locally_convex_space ℝ (weak_bilin B) :=
begin
  refine seminorm.with_seminorms.to_locally_convex_space
    (B.to_seminorm_family : F → seminorm 𝕜 (weak_bilin B)),
end

end locally_convex
