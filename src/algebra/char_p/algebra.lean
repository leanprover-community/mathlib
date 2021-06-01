/-
Copyright (c) 2021 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Eric Wieser
-/
import algebra.char_p.basic
import ring_theory.localization
import algebra.free_algebra


/-!
# Characteristics of algebras

In this file we describe the characteristic of `R`-algebras.

In particular we are interested in the characteristic of the fraction field
`fraction_ring R`.


## Main results

- `char_p_of_injective_algebra_map` If `R→+*A` is an injective algebra map
  then `A` has the same characteristic as `R`.

Instances were this can be applied:
- Any `free_algebra R X` has the same characteristic as `R`.
- The `fraction_ring R` of an integral domain `R` has the same characteristic as `R`.

-/


/-- If the algebra map `R →+* A` is injective then `A` has the same characteristic as `R`. -/
lemma char_p_of_injective_algebra_map {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (h : function.injective (algebra_map R A)) (p : ℕ) [char_p R p] : char_p A p :=
{ cast_eq_zero_iff := λx,
  begin
    rw ←char_p.cast_eq_zero_iff R p x,
    change algebra_map ℕ A x = 0 ↔ algebra_map ℕ R x = 0,
    rw is_scalar_tower.algebra_map_apply ℕ R A x,
    refine iff.trans _ h.eq_iff,
    rw ring_hom.map_zero,
  end }

/-- If the algebra map `R →+*A` is injective then `A` has the same characteristic as `R`. -/
lemma char_zero_of_injective_algebra_map {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (h : function.injective (algebra_map R A)) [char_zero R] : char_zero A :=
{ cast_injective := λ x y hxy,
  begin
    change algebra_map ℕ A x = algebra_map ℕ A y at hxy,
    rw is_scalar_tower.algebra_map_apply ℕ R A x at hxy,
    rw is_scalar_tower.algebra_map_apply ℕ R A y at hxy,
    exact char_zero.cast_injective (h hxy),
  end }
-- `char_p.char_p_to_char_zero A _ (char_p_of_injective_algebra_map h 0)` does not work
-- here as it would require `ring A`.

namespace free_algebra

variables {R X: Type*} [comm_semiring R] (p : ℕ)

/-- If `R` has characteristic `p`, then so does `free_algebra R X`. -/
instance char_p [char_p R p] : char_p (free_algebra R X) p :=
char_p_of_injective_algebra_map (free_algebra.algebra_map_injective R X) p

/-- If `R` has characteristic `0`, then so does `free_algebra R X`. -/
instance char_zero [char_zero R] : char_zero (free_algebra R X) :=
char_zero_of_injective_algebra_map (free_algebra.algebra_map_injective R X)

end free_algebra

namespace fraction_ring

variables {R : Type*} [integral_domain R] (p : ℕ)

/-- If `R` has characteristic `p`, then so does `fraction_ring R`. -/
instance char_p [char_p R p] : char_p (fraction_ring R) p :=
char_p_of_injective_algebra_map (fraction_map.injective (fraction_ring.of R)) p

/-- If `R` has characteristic `0`, then so does `fraction_ring R`. -/
instance char_zero [char_zero R] : char_zero (fraction_ring R) :=
char_p.char_p_to_char_zero (fraction_ring R)

end fraction_ring
