/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Topaz.
-/
import algebra.free_algebra
import algebra.ring_quot
import algebra.triv_sq_zero_ext

/-!
# Tensor Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the tensor algebra of `M`.
This is the free `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

1. `tensor_algebra R M` is the tensor algebra itself. It is endowed with an R-algebra structure.
2. `tensor_algebra.ι R` is the canonical R-linear map `M → tensor_algebra R M`.
3. Given a linear map `f : M → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
  `R`-algebra morphism `tensor_algebra R M → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : tensor_algebra R M → A` is
  given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.

## Implementation details

As noted above, the tensor algebra of `M` is constructed as the free `R`-algebra generated by `M`,
modulo the additional relations making the inclusion of `M` into an `R`-linear map.
-/

variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_monoid M] [semimodule R M]

namespace tensor_algebra

/--
An inductively defined relation on `pre R M` used to force the initial algebra structure on
the associated quotient.
-/
inductive rel : free_algebra R M → free_algebra R M → Prop
-- force `ι` to be linear
| add {a b : M} :
  rel (free_algebra.ι R (a+b)) (free_algebra.ι R a + free_algebra.ι R b)
| smul {r : R} {a : M} :
  rel (free_algebra.ι R (r • a)) (algebra_map R (free_algebra R M) r * free_algebra.ι R a)

end tensor_algebra

/--
The tensor algebra of the module `M` over the commutative semiring `R`.
-/
@[derive [inhabited, semiring, algebra R]]
def tensor_algebra := ring_quot (tensor_algebra.rel R M)

namespace tensor_algebra

instance {S : Type*} [comm_ring S] [semimodule S M] : ring (tensor_algebra S M) :=
ring_quot.ring (rel S M)

variables {M}
/--
The canonical linear map `M →ₗ[R] tensor_algebra R M`.
-/
def ι : M →ₗ[R] (tensor_algebra R M) :=
{ to_fun := λ m, (ring_quot.mk_alg_hom R _ (free_algebra.ι R m)),
  map_add' := λ x y, by { rw [←alg_hom.map_add], exact ring_quot.mk_alg_hom_rel R rel.add, },
  map_smul' := λ r x, by { rw [←alg_hom.map_smul], exact ring_quot.mk_alg_hom_rel R rel.smul, } }

lemma ring_quot_mk_alg_hom_free_algebra_ι_eq_ι (m : M) :
  ring_quot.mk_alg_hom R (rel R M) (free_algebra.ι R m) = ι R m := rfl

/--
Given a linear map `f : M → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `tensor_algebra R M → A`.
-/
@[simps symm_apply]
def lift {A : Type*} [semiring A] [algebra R A] : (M →ₗ[R] A) ≃ (tensor_algebra R M →ₐ[R] A) :=
{ to_fun := ring_quot.lift_alg_hom R ∘ λ f,
    ⟨free_algebra.lift R ⇑f, λ x y (h : rel R M x y), by induction h; simp [algebra.smul_def]⟩,
  inv_fun := λ F, F.to_linear_map.comp (ι R),
  left_inv := λ f, by { ext, simp [ι], },
  right_inv := λ F, by { ext, simp [ι], } }

variables {R}

@[simp]
theorem ι_comp_lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A) :
  (lift R f).to_linear_map.comp (ι R) = f := (lift R).symm_apply_apply f

@[simp]
theorem lift_ι_apply {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A) (x) :
  lift R f (ι R x) = f x := by { dsimp [lift, ι], refl, }

@[simp]
theorem lift_unique {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (g : tensor_algebra R M →ₐ[R] A) : g.to_linear_map.comp (ι R) = f ↔ g = lift R f :=
(lift R).symm_apply_eq

-- Marking `tensor_algebra` irreducible makes `ring` instances inaccessible on quotients.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.
attribute [irreducible] ι lift

@[simp]
theorem lift_comp_ι {A : Type*} [semiring A] [algebra R A] (g : tensor_algebra R M →ₐ[R] A) :
  lift R (g.to_linear_map.comp (ι R)) = g :=
by { rw ←lift_symm_apply, exact (lift R).apply_symm_apply g }

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {A : Type*} [semiring A] [algebra R A] {f g : tensor_algebra R M →ₐ[R] A}
  (w : f.to_linear_map.comp (ι R) = g.to_linear_map.comp (ι R)) : f = g :=
begin
  rw [←lift_symm_apply, ←lift_symm_apply] at w,
  exact (lift R).symm.injective w,
end

/-- The left-inverse of `algebra_map`. -/
def algebra_map_inv : tensor_algebra R M →ₐ[R] R :=
lift R (0 : M →ₗ[R] R)

lemma algebra_map_left_inverse :
  function.left_inverse algebra_map_inv (algebra_map R $ tensor_algebra R M) :=
λ x, by simp [algebra_map_inv]

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `triv_sq_zero_ext` which has a suitable
algebra structure. -/
def ι_inv : tensor_algebra R M →ₗ[R] M :=
(triv_sq_zero_ext.snd_hom R M).comp (lift R (triv_sq_zero_ext.inr_hom R M)).to_linear_map

lemma ι_left_inverse : function.left_inverse ι_inv (ι R : M → tensor_algebra R M) :=
λ x, by simp [ι_inv]

end tensor_algebra

namespace free_algebra

variables {R M}

/-- The canonical image of the `free_algebra` in the `tensor_algebra`, which maps
`free_algebra.ι R x` to `tensor_algebra.ι R x`. -/
def to_tensor : free_algebra R M →ₐ[R] tensor_algebra R M :=
free_algebra.lift R (tensor_algebra.ι R)

@[simp] lemma to_tensor_ι (m : M) : (free_algebra.ι R m).to_tensor = tensor_algebra.ι R m :=
by simp [to_tensor]

end free_algebra
