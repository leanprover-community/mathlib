/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

The Special Linear group $SL(n, R)$
-/
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.to_lin

/-!
# The Special Linear group $SL(n, R)$

This file defines the elements of the Special Linear group `special_linear_group n R`,
also written `SL(n, R)` or `SLₙ(R)`, consisting of all `n` by `n` `R`-matrices with
determinant `1`.  In addition, we define the group structure on `special_linear_group n R`
and the embedding into the general linear group `general_linear_group R (n → R)`
(i.e. `GL(n, R)` or `GLₙ(R)`).

## Main definitions

 * `matrix.special_linear_group` is the type of matrices with determinant 1
 * `matrix.special_linear_group.group` gives the group structure (under multiplication)
 * `matrix.special_linear_group.to_GL` is the embedding `SLₙ(R) → GLₙ(R)`

## Implementation notes
The inverse operation in the `special_linear_group` is defined to be the adjugate
matrix, so that `special_linear_group n R` has a group structure for all `comm_ring R`.

We define the elements of `special_linear_group` to be matrices, since we need to
compute their determinant. This is in contrast with `general_linear_group R M`,
which consists of invertible `R`-linear maps on `M`.

We provide `matrix.special_linear_group.has_coe_to_fun` for convenience, but do not state any
lemmas about it, and use `matrix.special_linear_group.coe_fn_eq_coe` to eliminate it `⇑` in favor
of a regular `↑` coercion.

## References

 * https://en.wikipedia.org/wiki/Special_linear_group

## Tags

matrix group, group, matrix inverse
-/

namespace matrix
universes u v
open_locale matrix
open linear_map


section

variables (n : Type u) [decidable_eq n] [fintype n] (R : Type v) [comm_ring R]

/-- `special_linear_group n R` is the group of `n` by `n` `R`-matrices with determinant equal to 1.
-/
def special_linear_group := { A : matrix n n R // A.det = 1 }

end

namespace special_linear_group

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

instance has_coe_to_matrix : has_coe (special_linear_group n R) (matrix n n R) :=
⟨λ A, A.val⟩

local prefix `↑ₘ`:1024 := @coe _ (matrix n n R) _

lemma ext_iff (A B : special_linear_group n R) : A = B ↔ (∀ i j, ↑ₘA i j = ↑ₘB i j) :=
iff.trans subtype.ext_iff_val ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : special_linear_group n R) : (∀ i j, ↑ₘA i j = ↑ₘB i j) → A = B :=
(special_linear_group.ext_iff A B).mpr

instance has_inv : has_inv (special_linear_group n R) :=
⟨λ A, ⟨adjugate A, det_adjugate_eq_one A.2⟩⟩

instance has_mul : has_mul (special_linear_group n R) :=
⟨λ A B, ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩⟩

instance has_one : has_one (special_linear_group n R) :=
⟨⟨1, det_one⟩⟩

instance : inhabited (special_linear_group n R) := ⟨1⟩

section coe_lemmas

variables (A B : special_linear_group n R)

@[simp] lemma coe_inv : ↑ₘ(A⁻¹) = adjugate A := rfl

@[simp] lemma coe_mul : ↑ₘ(A * B) = ↑ₘA ⬝ ↑ₘB := rfl

@[simp] lemma coe_one : ↑ₘ(1 : special_linear_group n R) = (1 : matrix n n R) := rfl

@[simp] lemma det_coe : det ↑ₘA = 1 := A.2

end coe_lemmas

instance : monoid (special_linear_group n R) :=
function.injective.monoid coe subtype.coe_injective coe_one coe_mul

instance : group (special_linear_group n R) :=
{ mul_left_inv := λ A, by { ext1, simp [adjugate_mul] },
  ..special_linear_group.monoid,
  ..special_linear_group.has_inv }

/-- `matrix.to_lin' A` is a linear equivalence on the special linear group. -/
def to_lin' (A : special_linear_group n R) : (n → R) ≃ₗ[R] (n → R) :=
linear_equiv.of_linear
  (matrix.to_lin' ↑ₘA)
  (matrix.to_lin' ↑ₘ(A⁻¹))
  (by rw [←to_lin'_mul, ←coe_mul, mul_right_inv, coe_one, to_lin'_one])
  (by rw [←to_lin'_mul, ←coe_mul, mul_left_inv, coe_one, to_lin'_one])

@[simp]
lemma to_lin'_one : (1 : special_linear_group n R).to_lin' = linear_equiv.refl _ _ :=
linear_equiv.to_linear_map_injective matrix.to_lin'_one

@[simp]
lemma to_lin'_mul (A B : special_linear_group n R) :
  (A * B).to_lin' = B.to_lin'.trans A.to_lin' :=
linear_equiv.to_linear_map_injective $ matrix.to_lin'_mul A B

lemma to_lin'_apply (A : special_linear_group n R) (v : n → R) :
  A.to_lin' v = matrix.to_lin' ↑ₘA v := rfl

lemma to_lin'_symm_apply (A : special_linear_group n R) (v : n → R) :
  A.to_lin'.symm v = matrix.to_lin' ↑ₘ(A⁻¹) v := rfl

/-- `matrix.special_linear_group.to_lin'` as a `monoid_hom`. -/
@[simps]
def to_lin'_hom : special_linear_group n R →* (n → R) ≃ₗ[R] (n → R) :=
{ to_fun := to_lin', map_one' := to_lin'_one, map_mul' := to_lin'_mul }

/-- `to_GL` is the map from the special linear group to the general linear group -/
def to_GL : special_linear_group n R →* general_linear_group R (n → R) :=
(general_linear_group.general_linear_equiv _ _).symm.to_monoid_hom.comp to_lin'_hom

lemma coe_to_GL (A : special_linear_group n R) : ↑A.to_GL = A.to_lin'.to_linear_map := rfl

-- this section should be last to ensure we do not use it in lemmas
section coe_fn_instance

/-- This instance is here for convenience, but is not the simp-normal form. -/
instance : has_coe_to_fun (special_linear_group n R) :=
{ F   := λ _, n → n → R,
  coe := λ A, A.val }

@[simp]
lemma coe_fn_eq_coe (s : special_linear_group n R) : ⇑s = ↑ₘs := rfl

end coe_fn_instance

end special_linear_group

end matrix
