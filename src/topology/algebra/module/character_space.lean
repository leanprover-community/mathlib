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

## Tags

character space, Gelfand transform, functional calculus

-/

namespace weak_dual

/-- The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
def character_space (𝕜 : Type*) (A : Type*) [comm_semiring 𝕜] [topological_space 𝕜]
  [has_continuous_add 𝕜] [has_continuous_const_smul 𝕜 𝕜]
  [non_unital_non_assoc_semiring A] [topological_space A] [module 𝕜 A] :=
  {φ : weak_dual 𝕜 A | (φ ≠ 0) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))}

variables {𝕜 : Type*} {A : Type*}

namespace character_space

section non_unital_non_assoc_semiring

variables [comm_semiring 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [non_unital_non_assoc_semiring A] [topological_space A]
  [module 𝕜 A]

@[simp, norm_cast, protected]
lemma coe_coe (φ : character_space 𝕜 A) : ⇑(φ : weak_dual 𝕜 A) = φ := rfl

/-- Elements of the character space are continuous linear maps. -/
instance : continuous_linear_map_class (character_space 𝕜 A) 𝕜 A 𝕜 :=
{ coe := λ φ, (φ : A → 𝕜),
  coe_injective' := λ φ ψ h, by { ext, exact congr_fun h x },
  map_smulₛₗ := λ φ, (φ : weak_dual 𝕜 A).map_smul,
  map_add := λ φ, (φ : weak_dual 𝕜 A).map_add,
  map_continuous := λ φ, (φ : weak_dual 𝕜 A).cont }

/-- An element of the character space, as a continuous linear map. -/
def to_clm (φ : character_space 𝕜 A) : A →L[𝕜] 𝕜 := (φ : weak_dual 𝕜 A)

@[simp] lemma coe_to_clm (φ : character_space 𝕜 A) : ⇑(to_clm φ) = φ := rfl

/-- Elements of the character space are non-unital algebra homomorphisms. -/
instance : non_unital_alg_hom_class (character_space 𝕜 A) 𝕜 A 𝕜 :=
{ map_smul := λ φ, map_smul φ,
  map_zero := λ φ, map_zero φ,
  map_mul := λ φ, φ.prop.2,
  .. character_space.continuous_linear_map_class }

/-- An element of the character space, as an non-unital algebra homomorphism. -/
def to_non_unital_alg_hom (φ : character_space 𝕜 A) : A →ₙₐ[𝕜] 𝕜 :=
{ to_fun := (φ : A → 𝕜),
  map_mul' := map_mul φ,
  map_smul' := map_smul φ,
  map_zero' := map_zero φ,
  map_add' := map_add φ }

@[simp]
lemma coe_to_non_unital_alg_hom (φ : character_space 𝕜 A) : ⇑(to_non_unital_alg_hom φ) = φ := rfl

end non_unital_non_assoc_semiring

section unital

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [semiring A] [algebra 𝕜 A]

/-- In a unital algebra, elements of the character space are algebra homomorphisms. -/
instance : alg_hom_class (character_space 𝕜 A) 𝕜 A 𝕜 :=
have map_one' : ∀ φ : character_space 𝕜 A, φ 1 = 1 := λ φ,
begin
  have h₁ : (φ 1) * (1 - φ 1) = 0 := by rw [mul_sub, sub_eq_zero, mul_one, ←map_mul φ, one_mul],
  rcases mul_eq_zero.mp h₁ with h₂ | h₂,
  { have : ∀ a, φ (a * 1) = 0 := λ a, by simp only [map_mul φ, h₂, mul_zero],
    exact false.elim (φ.prop.1 $ continuous_linear_map.ext $ by simpa only [mul_one] using this) },
  { exact (sub_eq_zero.mp h₂).symm },
end,
{ map_one := map_one',
  commutes := λ φ r,
  begin
  { rw [algebra.algebra_map_eq_smul_one, algebra.id.map_eq_id, ring_hom.id_apply],
    change ((φ : weak_dual 𝕜 A) : A →L[𝕜] 𝕜) (r • 1) = r,
    rw [map_smul, algebra.id.smul_eq_mul, character_space.coe_coe, map_one' φ, mul_one] },
  end,
  .. character_space.non_unital_alg_hom_class }

/-- An element of the character space of a unital algebra, as an algebra homomorphism. -/
@[simps] def to_alg_hom (φ : character_space 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
{ map_one' := map_one φ,
  commutes' := alg_hom_class.commutes φ,
  ..to_non_unital_alg_hom φ }

lemma eq_set_map_one_map_mul [nontrivial 𝕜] : character_space 𝕜 A =
  {φ : weak_dual 𝕜 A | (φ 1 = 1) ∧ (∀ (x y : A), φ (x * y) = (φ x) * (φ y))} :=
begin
  ext x,
  refine ⟨λ h, ⟨map_one (⟨x, h⟩ : character_space 𝕜 A), h.2⟩, λ h, ⟨_, h.2⟩⟩,
  rintro rfl,
  simpa using h.1,
end

lemma is_closed [nontrivial 𝕜] [t2_space 𝕜] [has_continuous_mul 𝕜] :
  is_closed (character_space 𝕜 A) :=
begin
  rw [eq_set_map_one_map_mul],
  refine is_closed.inter (is_closed_eq (eval_continuous _) continuous_const) _,
  change is_closed {φ : weak_dual 𝕜 A | ∀ x y : A, φ (x * y) = φ x * φ y},
  rw [set.set_of_forall],
  refine is_closed_Inter (λ a, _),
  rw [set.set_of_forall],
  exact is_closed_Inter (λ _, is_closed_eq (eval_continuous _)
    ((eval_continuous _).mul (eval_continuous _)))
end

end unital

section ring

variables [comm_ring 𝕜] [no_zero_divisors 𝕜] [topological_space 𝕜] [has_continuous_add 𝕜]
  [has_continuous_const_smul 𝕜 𝕜] [topological_space A] [ring A] [algebra 𝕜 A]

lemma apply_mem_spectrum [nontrivial 𝕜] (φ : character_space 𝕜 A) (a : A) : φ a ∈ spectrum 𝕜 a :=
alg_hom.apply_mem_spectrum φ a

end ring

end character_space

end weak_dual
