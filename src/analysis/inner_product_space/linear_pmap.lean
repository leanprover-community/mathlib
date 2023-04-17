/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.inner_product_space.adjoint
import topology.algebra.module.linear_pmap
import topology.algebra.module.basic

/-!

# Partially defined linear operators on Hilbert spaces

We will develop the basics of the theory of unbounded operators on Hilbert spaces.

## Main definitions

* `linear_pmap.is_formal_adjoint`: An operator `T` is a formal adjoint of `S` if for all `x` in the
domain of `T` and `y` in the domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`.
* `linear_pmap.adjoint`: The adjoint of a map `E →ₗ.[𝕜] F` as a map `F →ₗ.[𝕜] E`.

## Main statements

* `linear_pmap.adjoint_is_formal_adjoint`: The adjoint is a formal adjoint

## Notation

* For `T : E →ₗ.[𝕜] F` the adjoint can be written as `T†`.
This notation is localized in `linear_pmap`.

## Implementation notes

We use the junk value pattern to define the adjoint for all `linear_pmap`s. In the case that
`T : E →ₗ.[𝕜] F` is not densely defined the adjoint `T†` is the zero map from `T.adjoint_domain` to
`E`.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]

## Tags

Unbounded operators, closed operators
-/


noncomputable theory

open is_R_or_C
open_locale complex_conjugate classical

variables {𝕜 E F G : Type*} [is_R_or_C 𝕜]
variables [normed_add_comm_group E] [inner_product_space 𝕜 E]
variables [normed_add_comm_group F] [inner_product_space 𝕜 F]

local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace linear_pmap

/-- An operator `T` is a formal adjoint of `S` if for all `x` in the domain of `T` and `y` in the
domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`. -/
def is_formal_adjoint (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] E) : Prop :=
∀ (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫

variables {T : E →ₗ.[𝕜] F} {S : F →ₗ.[𝕜] E}

@[protected] lemma is_formal_adjoint.symm (h : T.is_formal_adjoint S) : S.is_formal_adjoint T :=
λ y _, by rw [←inner_conj_symm, ←inner_conj_symm (y : F), h]

variables (T)

/-- The domain of the adjoint operator.

This definition is needed to construct the adjoint operator and the preferred version to use is
`T.adjoint.domain` instead of `T.adjoint_domain`. -/
def adjoint_domain : submodule 𝕜 F :=
{ carrier := {y | continuous ((innerₛₗ 𝕜 y).comp T.to_fun)},
  zero_mem' := by { rw [set.mem_set_of_eq, linear_map.map_zero, linear_map.zero_comp],
      exact continuous_zero },
  add_mem' := λ x y hx hy, by { rw [set.mem_set_of_eq, linear_map.map_add] at *, exact hx.add hy },
  smul_mem' := λ a x hx, by { rw [set.mem_set_of_eq, linear_map.map_smulₛₗ] at *,
    exact hx.const_smul (conj a) } }

/-- The operator `λ x, ⟪y, T x⟫` considered as a continuous linear operator from `T.adjoint_domain`
to `𝕜`. -/
def adjoint_domain_mk_clm (y : T.adjoint_domain) : T.domain →L[𝕜] 𝕜 :=
⟨(innerₛₗ 𝕜 (y : F)).comp T.to_fun, y.prop⟩

lemma adjoint_domain_mk_clm_apply (y : T.adjoint_domain) (x : T.domain) :
  adjoint_domain_mk_clm T y x = ⟪(y : F), T x⟫ := rfl

variable {T}
variable (hT : dense (T.domain : set E))

include hT

/-- The unique continuous extension of the operator `adjoint_domain_mk_clm` to `E`. -/
def adjoint_domain_mk_clm_extend (y : T.adjoint_domain) :
  E →L[𝕜] 𝕜 :=
(T.adjoint_domain_mk_clm y).extend (submodule.subtypeL T.domain)
  hT.dense_range_coe uniform_embedding_subtype_coe.to_uniform_inducing

@[simp] lemma adjoint_domain_mk_clm_extend_apply (y : T.adjoint_domain) (x : T.domain) :
  adjoint_domain_mk_clm_extend hT y (x : E) = ⟪(y : F), T x⟫ :=
continuous_linear_map.extend_eq _ _ _ _ _

variables [complete_space E]

lemma exists_unique_adjoint_elem (y : T.adjoint_domain) : ∃! (w : E),
  ∀ (x : T.domain), ⟪w, x⟫ = ⟪(y : F), T x⟫ :=
exists_unique_of_exists_of_unique
  -- For the existence we use the Fréchet-Riesz representation theorem and extend
  -- the map that is only defined on `T.domain` to `E`:
  ⟨(inner_product_space.to_dual 𝕜 E).symm (adjoint_domain_mk_clm_extend hT y),
    -- Implementation note: this is true `by simp`
    by simp only [inner_product_space.to_dual_symm_apply, adjoint_domain_mk_clm_extend_apply hT,
      eq_self_iff_true, forall_const]⟩
  -- The uniqueness follows directly from the fact that `T.domain` is dense in `E`.
  (λ _ _ hy₁ hy₂, hT.eq_of_inner_left (λ v, (hy₁ v).trans (hy₂ v).symm))

/-- The image of the adjoint operator.

This is an auxiliary definition needed to define the adjoint operator as a `linear_pmap`. -/
def adjoint_elem (y : T.adjoint_domain) : E :=
(exists_unique_adjoint_elem hT y).exists.some

lemma adjoint_elem_spec (y : T.adjoint_domain) (x : T.domain) :
  ⟪adjoint_elem hT y, x⟫ = ⟪(y : F), T x⟫ :=
(exists_unique_adjoint_elem hT y).exists.some_spec _

/-- The adjoint as a linear map from its domain to `E`.

This is an auxiliary definition needed to define the adjoint operator as a `linear_pmap` without
the assumption that `T.domain` is dense. -/
def adjoint_aux : T.adjoint_domain →ₗ[𝕜] E :=
{ to_fun := adjoint_elem hT,
  map_add' := λ _ _, hT.eq_of_inner_left $ λ _,
    by simp only [inner_add_left, adjoint_elem_spec, submodule.coe_add],
  map_smul' := λ _ _, hT.eq_of_inner_left $ λ _,
    by simp only [inner_smul_left, adjoint_elem_spec, submodule.coe_smul_of_tower,
      ring_hom.id_apply] }

omit hT

variable (T)

/-- The adjoint operator as a partially defined linear operator. -/
def adjoint : F →ₗ.[𝕜] E :=
{ domain := T.adjoint_domain,
  to_fun := if hT : dense (T.domain : set E) then adjoint_aux hT else 0 }

localized "postfix (name := adjoint) `†`:1100 := linear_pmap.adjoint" in linear_pmap

variable {T}

lemma adjoint_apply_of_not_dense (hT : ¬ dense (T.domain : set E)) (y : T†.domain) : T† y = 0 :=
begin
  change (if hT : dense (T.domain : set E) then adjoint_aux hT else 0) y = _,
  simp only [hT, not_false_iff, dif_neg, linear_map.zero_apply],
end

include hT

lemma adjoint_apply_of_dense (y : T†.domain) : T† y = adjoint_elem hT y :=
begin
  change (if hT : dense (T.domain : set E) then adjoint_aux hT else 0) y = _,
  simp only [hT, adjoint_aux, dif_pos, linear_map.coe_mk],
end

/-- The fundamental property of the adjoint. -/
lemma adjoint_is_formal_adjoint : T†.is_formal_adjoint T :=
begin
  intros x y,
  rw adjoint_apply_of_dense hT,
  exact adjoint_elem_spec hT x y,
end

lemma mem_adjoint_domain_iff (y : F) :
  y ∈ T†.domain ↔ continuous ((innerₛₗ 𝕜 y).comp T.to_fun) := iff.rfl

lemma mem_adjoint_domain_of_exists (y : F) (h : ∃ w : E, ∀ (x : T.domain), ⟪w, x⟫ = ⟪y, T x⟫) :
  y ∈ T†.domain :=
begin
  cases h with w hw,
  rw mem_adjoint_domain_iff hT,
  have : continuous ((innerSL 𝕜 w).comp T.domain.subtypeL) := by continuity,
  convert this using 1,
  exact funext (λ x, (hw x).symm),
end

lemma is_formal_adjoint.le_adjoint (h : T.is_formal_adjoint S) : S ≤ T† :=
-- Trivially, every `x : S.domain` is in `T.adjoint.domain`
⟨λ x hx, mem_adjoint_domain_of_exists hT _ ⟨S ⟨x, hx⟩, h.symm ⟨x, hx⟩⟩,
  -- Equality on `S.domain` follows from equality
  -- `⟪v, S x⟫ = ⟪v, T.adjoint y⟫` for all `v : T.domain`:
  λ _ _ hxy, hT.eq_of_inner_right (λ _, by rw [← h, hxy, ← (adjoint_is_formal_adjoint hT).symm])⟩

end linear_pmap

namespace continuous_linear_map

variables [complete_space E] [complete_space F]
variable (A : E →L[𝕜] F)

/-- The adjoint of `linear_pmap` and the adjoint of `continuous_linear_map` coincide. -/
lemma to_pmap_adjoint_eq_adjoint_to_pmap : (A.to_pmap ⊤).adjoint = A.adjoint.to_pmap ⊤ :=
begin
  have hT : dense ((A.to_pmap ⊤).domain : set E) :=
  begin
    change dense (⊤ : set E),
    simp only [set.top_eq_univ, dense_univ],
  end,
  ext,
  { change _ ↔ x ∈ ⊤,
    simp only [submodule.mem_top, iff_true],
    rw linear_pmap.mem_adjoint_domain_iff hT x,
    dsimp only [linear_map.coe_comp, innerₛₗ_apply_coe],
    exact (innerSL 𝕜 x).cont.comp (A.continuous.comp continuous_subtype_coe) },
  intros x y hxy,
  simp only [linear_map.to_pmap_apply, to_linear_map_eq_coe, coe_coe],
  refine hT.eq_of_inner_left (λ v, _),
  rw [linear_pmap.adjoint_is_formal_adjoint hT x v, adjoint_inner_left, hxy],
  simp only [linear_map.to_pmap_apply, to_linear_map_eq_coe, coe_coe],
end

end continuous_linear_map
