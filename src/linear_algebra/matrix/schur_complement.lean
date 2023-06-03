/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Eric Wieser, Jeremy Avigad, Johan Commelin
-/
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def

/-! # 2×2 block matrices and the Schur complement

This file proves properties of 2×2 block matrices `[A B; C D]` that relate to the Schur complement
`D - C⬝A⁻¹⬝B`.

## Main results

 * `matrix.det_from_blocks₁₁`, `matrix.det_from_blocks₂₂`: determinant of a block matrix in terms of
   the Schur complement.
 * `matrix.det_one_add_mul_comm`: the **Weinstein–Aronszajn identity**.
 * `matrix.schur_complement_pos_semidef_iff` : If a matrix `A` is positive definite, then
  `[A B; Bᴴ D]` is postive semidefinite if and only if `D - Bᴴ A⁻¹ B` is postive semidefinite.

-/

variables {l m n α : Type*}

namespace matrix
open_locale matrix

section comm_ring
variables [fintype l] [fintype m] [fintype n]
variables [decidable_eq l] [decidable_eq m] [decidable_eq n]
variables [comm_ring α]

/-- LDU decomposition of a block matrix with an invertible top-left corner, using the
Schur complement. -/
lemma from_blocks_eq_of_invertible₁₁
  (A : matrix m m α) (B : matrix m n α) (C : matrix l m α) (D : matrix l n α) [invertible A] :
  from_blocks A B C D =
    from_blocks 1 0 (C⬝⅟A) 1 ⬝ from_blocks A 0 0 (D - C⬝(⅟A)⬝B) ⬝ from_blocks 1 (⅟A⬝B) 0 1 :=
by simp only [from_blocks_multiply, matrix.mul_zero, matrix.zero_mul, add_zero, zero_add,
      matrix.one_mul, matrix.mul_one, matrix.inv_of_mul_self, matrix.mul_inv_of_self_assoc,
        matrix.mul_inv_of_mul_self_cancel, matrix.mul_assoc, add_sub_cancel'_right]

/-- LDU decomposition of a block matrix with an invertible bottom-right corner, using the
Schur complement. -/
lemma from_blocks_eq_of_invertible₂₂
  (A : matrix l m α) (B : matrix l n α) (C : matrix n m α) (D : matrix n n α) [invertible D] :
  from_blocks A B C D =
    from_blocks 1 (B⬝⅟D) 0 1 ⬝ from_blocks (A - B⬝⅟D⬝C) 0 0 D ⬝ from_blocks 1 0 (⅟D ⬝ C) 1 :=
(matrix.reindex (equiv.sum_comm _ _) (equiv.sum_comm _ _)).injective $ by
  simpa [reindex_apply, equiv.sum_comm_symm,
    ←submatrix_mul_equiv _ _ _ (equiv.sum_comm n m),
    ←submatrix_mul_equiv _ _ _ (equiv.sum_comm n l),
    equiv.sum_comm_apply, from_blocks_submatrix_sum_swap_sum_swap]
    using from_blocks_eq_of_invertible₁₁ D C B A

/-! ### Lemmas about `matrix.det` -/

section det

/-- Determinant of a 2×2 block matrix, expanded around an invertible top left element in terms of
the Schur complement. -/
lemma det_from_blocks₁₁ (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible A] : (matrix.from_blocks A B C D).det = det A * det (D - C ⬝ (⅟A) ⬝ B) :=
by rw [from_blocks_eq_of_invertible₁₁, det_mul, det_mul, det_from_blocks_zero₂₁,
  det_from_blocks_zero₂₁, det_from_blocks_zero₁₂, det_one, det_one, one_mul, one_mul, mul_one]

@[simp] lemma det_from_blocks_one₁₁ (B : matrix m n α) (C : matrix n m α) (D : matrix n n α) :
  (matrix.from_blocks 1 B C D).det = det (D - C ⬝ B) :=
begin
  haveI : invertible (1 : matrix m m α) := invertible_one,
  rw [det_from_blocks₁₁, inv_of_one, matrix.mul_one, det_one, one_mul],
end

/-- Determinant of a 2×2 block matrix, expanded around an invertible bottom right element in terms
of the Schur complement. -/
lemma det_from_blocks₂₂ (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) (D : matrix n n α)
  [invertible D] : (matrix.from_blocks A B C D).det = det D * det (A - B ⬝ (⅟D) ⬝ C) :=
begin
  have : from_blocks A B C D
    = (from_blocks D C B A).submatrix (equiv.sum_comm _ _) (equiv.sum_comm _ _),
  { ext i j,
    cases i; cases j; refl },
  rw [this, det_submatrix_equiv_self, det_from_blocks₁₁],
end

@[simp] lemma det_from_blocks_one₂₂ (A : matrix m m α) (B : matrix m n α) (C : matrix n m α) :
  (matrix.from_blocks A B C 1).det = det (A - B ⬝ C) :=
begin
  haveI : invertible (1 : matrix n n α) := invertible_one,
  rw [det_from_blocks₂₂, inv_of_one, matrix.mul_one, det_one, one_mul],
end

/-- The **Weinstein–Aronszajn identity**. Note the `1` on the LHS is of shape m×m, while the `1` on
the RHS is of shape n×n. -/
lemma det_one_add_mul_comm (A : matrix m n α) (B : matrix n m α) :
  det (1 + A ⬝ B) = det (1 + B ⬝ A) :=
calc  det (1 + A ⬝ B)
    = det (from_blocks 1 (-A) B 1) : by rw [det_from_blocks_one₂₂, matrix.neg_mul, sub_neg_eq_add]
... = det (1 + B ⬝ A)              : by rw [det_from_blocks_one₁₁, matrix.mul_neg, sub_neg_eq_add]

/-- Alternate statement of the **Weinstein–Aronszajn identity** -/
lemma det_mul_add_one_comm (A : matrix m n α) (B : matrix n m α) :
  det (A ⬝ B + 1) = det (B ⬝ A + 1) :=
by rw [add_comm, det_one_add_mul_comm, add_comm]

lemma det_one_sub_mul_comm (A : matrix m n α) (B : matrix n m α) :
  det (1 - A ⬝ B) = det (1 - B ⬝ A) :=
by rw [sub_eq_add_neg, ←matrix.neg_mul, det_one_add_mul_comm, matrix.mul_neg, ←sub_eq_add_neg]

/-- A special case of the **Matrix determinant lemma** for when `A = I`.

TODO: show this more generally. -/
lemma det_one_add_col_mul_row (u v : m → α) : det (1 + col u ⬝ row v) = 1 + v ⬝ᵥ u :=
by rw [det_one_add_mul_comm, det_unique, pi.add_apply, pi.add_apply, matrix.one_apply_eq,
       matrix.row_mul_col_apply]

end det

end comm_ring

/-! ### Lemmas about `ℝ` and `ℂ`-/

section is_R_or_C

open_locale matrix
variables {𝕜 : Type*} [is_R_or_C 𝕜]

localized "infix ` ⊕ᵥ `:65 := sum.elim" in matrix

lemma schur_complement_eq₁₁ [fintype m] [decidable_eq m] [fintype n]
  {A : matrix m m 𝕜} (B : matrix m n 𝕜) (D : matrix n n 𝕜) (x : m → 𝕜) (y : n → 𝕜)
  [invertible A] (hA : A.is_hermitian) :
vec_mul (star (x ⊕ᵥ y)) (from_blocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vec_mul (star (x + (A⁻¹ ⬝ B).mul_vec y)) A ⬝ᵥ (x + (A⁻¹ ⬝ B).mul_vec y) +
    vec_mul (star y) (D - Bᴴ ⬝ A⁻¹ ⬝ B) ⬝ᵥ y :=
begin
  simp [function.star_sum_elim, from_blocks_mul_vec, vec_mul_from_blocks, add_vec_mul,
    dot_product_mul_vec, vec_mul_sub, matrix.mul_assoc, vec_mul_mul_vec, hA.eq,
    conj_transpose_nonsing_inv, star_mul_vec],
  abel
end

lemma schur_complement_eq₂₂ [fintype m] [fintype n] [decidable_eq n]
  (A : matrix m m 𝕜) (B : matrix m n 𝕜) {D : matrix n n 𝕜} (x : m → 𝕜) (y : n → 𝕜)
  [invertible D] (hD : D.is_hermitian) :
vec_mul (star (x ⊕ᵥ y)) (from_blocks A B Bᴴ D) ⬝ᵥ (x ⊕ᵥ y) =
  vec_mul (star ((D⁻¹ ⬝ Bᴴ).mul_vec x + y)) D ⬝ᵥ ((D⁻¹ ⬝ Bᴴ).mul_vec x + y) +
    vec_mul (star x) (A - B ⬝ D⁻¹ ⬝ Bᴴ) ⬝ᵥ x :=
begin
  simp [function.star_sum_elim, from_blocks_mul_vec, vec_mul_from_blocks, add_vec_mul,
    dot_product_mul_vec, vec_mul_sub, matrix.mul_assoc, vec_mul_mul_vec, hD.eq,
    conj_transpose_nonsing_inv, star_mul_vec],
  abel
end

lemma is_hermitian.from_blocks₁₁ [fintype m] [decidable_eq m]
  {A : matrix m m 𝕜} (B : matrix m n 𝕜) (D : matrix n n 𝕜)
  (hA : A.is_hermitian) :
  (from_blocks A B Bᴴ D).is_hermitian ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).is_hermitian :=
begin
  have hBAB : (Bᴴ ⬝ A⁻¹ ⬝ B).is_hermitian,
  { apply is_hermitian_conj_transpose_mul_mul,
    apply hA.inv },
  rw [is_hermitian_from_blocks_iff],
  split,
  { intro h,
    apply is_hermitian.sub h.2.2.2 hBAB },
  { intro h,
    refine ⟨hA, rfl, conj_transpose_conj_transpose B, _⟩,
    rw ← sub_add_cancel D,
    apply is_hermitian.add h hBAB }
end

lemma is_hermitian.from_blocks₂₂ [fintype n] [decidable_eq n]
  (A : matrix m m 𝕜) (B : matrix m n 𝕜) {D : matrix n n 𝕜}
  (hD : D.is_hermitian) :
  (from_blocks A B Bᴴ D).is_hermitian ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).is_hermitian :=
begin
  rw [←is_hermitian_submatrix_equiv (equiv.sum_comm n m), equiv.sum_comm_apply,
    from_blocks_submatrix_sum_swap_sum_swap],
  convert is_hermitian.from_blocks₁₁ _ _ hD; simp
end

lemma pos_semidef.from_blocks₁₁ [fintype m] [decidable_eq m] [fintype n]
  {A : matrix m m 𝕜} (B : matrix m n 𝕜) (D : matrix n n 𝕜)
  (hA : A.pos_def) [invertible A] :
  (from_blocks A B Bᴴ D).pos_semidef ↔ (D - Bᴴ ⬝ A⁻¹ ⬝ B).pos_semidef :=
begin
  rw [pos_semidef, is_hermitian.from_blocks₁₁ _ _ hA.1],
  split,
  { refine λ h, ⟨h.1, λ x, _⟩,
    have := h.2 (- ((A⁻¹ ⬝ B).mul_vec x) ⊕ᵥ x),
    rw [dot_product_mul_vec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_self,
      dot_product_zero, zero_add] at this,
    rw [dot_product_mul_vec], exact this },
  { refine λ h, ⟨h.1, λ x, _⟩,
    rw [dot_product_mul_vec, ← sum.elim_comp_inl_inr x, schur_complement_eq₁₁ B D _ _ hA.1,
      map_add],
    apply le_add_of_nonneg_of_le,
    { rw ← dot_product_mul_vec,
      apply hA.pos_semidef.2, },
    { rw ← dot_product_mul_vec, apply h.2 } }
end

lemma pos_semidef.from_blocks₂₂ [fintype m] [fintype n] [decidable_eq n]
  (A : matrix m m 𝕜) (B : matrix m n 𝕜) {D : matrix n n 𝕜}
  (hD : D.pos_def) [invertible D] :
  (from_blocks A B Bᴴ D).pos_semidef ↔ (A - B ⬝ D⁻¹ ⬝ Bᴴ).pos_semidef :=
begin
  rw [←pos_semidef_submatrix_equiv (equiv.sum_comm n m), equiv.sum_comm_apply,
    from_blocks_submatrix_sum_swap_sum_swap],
  convert pos_semidef.from_blocks₁₁ _ _ hD; apply_instance <|> simp
end

end is_R_or_C

end matrix
