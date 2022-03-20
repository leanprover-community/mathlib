/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import topology.algebra.module.weak_dual
import algebra.algebra.spectrum

/-!
# Character space of a topological algebra

The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an
isomorphism between a commutative C⋆-algebra and continuous functions on the character space
of the algebra. This, in turn, is used to construct the continuous functional calculus on
C⋆-algebras.


## Implementation notes

We define `character_space 𝕜 A` as a subset of the weak dual, which automatically puts the
correct topology on the space. We then define `to_alg_hom` which provides the algebra homomorphism
corresponding to any element. We also provide `to_clm` which provides the element as a
continuous linear map. (Even though `weak_dual 𝕜 A` is a type copy of `A →L[𝕜] 𝕜`, this is
often more convenient.)

## TODO

* Prove that the character space is a compact subset of the weak dual. This requires the
  Banach-Alaoglu theorem.

## Tags

character space, Gelfand transform, functional calculus

-/

/-- The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def character_space (𝕜 : Type*) (A : Type*) [comm_semiring 𝕜] [topological_space 𝕜]
  [has_continuous_add 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  [semiring A] [topological_space A] [module 𝕜 A] :=
  {φ : weak_dual 𝕜 A | (φ 1 = 1) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

variables {𝕜 : Type*} {A : Type*}

namespace character_space

section semiring

variables [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [semiring A] [algebra 𝕜 A]

/-- An element of the character space, as a continuous linear map. -/
def to_clm (φ : character_space 𝕜 A) : A →L[𝕜] 𝕜 := (φ : weak_dual 𝕜 A)

lemma to_clm_apply (φ : character_space 𝕜 A) (x : A) : φ x = to_clm φ x := rfl

/-- An element of the character space, as an algebra homomorphism. -/
@[simps] def to_alg_hom (φ : character_space 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
{ to_fun := (φ : A → 𝕜),
  map_one' := φ.prop.1,
  map_mul' := φ.prop.2,
  map_zero' := continuous_linear_map.map_zero _,
  map_add' := continuous_linear_map.map_add _,
  commutes' := λ r, by {
    rw [algebra.algebra_map_eq_smul_one, algebra.id.map_eq_id, ring_hom.id_apply],
    change ((φ : weak_dual 𝕜 A) : A →L[𝕜] 𝕜) (r • 1) = r,
    rw [continuous_linear_map.map_smul, algebra.id.smul_eq_mul, φ.prop.1, mul_one] } }

lemma map_one (φ : character_space 𝕜 A) : φ 1 = 1 := (to_alg_hom φ).map_one
lemma map_mul (φ : character_space 𝕜 A) (x y : A) : φ (x * y) = φ x * φ y :=
  (to_alg_hom φ).map_mul _ _
lemma map_zero (φ : character_space 𝕜 A) : φ 0 = 0 := (to_alg_hom φ).map_zero
lemma map_add (φ : character_space 𝕜 A) (x y : A) : φ (x + y) = φ x + φ y :=
  (to_alg_hom φ).map_add _ _
lemma map_smul (φ : character_space 𝕜 A) (r : 𝕜) (x : A) : φ (r • x) = r • (φ x) :=
  (to_clm φ).map_smul _ _
lemma continuous (φ : character_space 𝕜 A) : continuous φ := (to_clm φ).continuous

end semiring

section ring

variables [comm_ring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [ring A] [algebra 𝕜 A]

lemma apply_mem_spectrum [nontrivial 𝕜] (φ : character_space 𝕜 A) (a : A) : φ a ∈ spectrum 𝕜 a :=
(to_alg_hom φ).apply_mem_spectrum a

end ring

end character_space
