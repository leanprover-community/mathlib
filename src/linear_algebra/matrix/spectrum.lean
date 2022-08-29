/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import analysis.inner_product_space.spectrum
import linear_algebra.matrix.hermitian

/-! # Spectral theory of hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`diagonalization_basis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem

-/

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜] {n : Type*} [fintype n] [decidable_eq n]
variables {A : matrix n n 𝕜}

open_locale matrix
open_locale big_operators

namespace is_hermitian

variables (hA : A.is_hermitian)

/-- The eigenvalues of a hermitian matrix, indexed by `fin (fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : fin (fintype.card n) → ℝ :=
(is_hermitian_iff_is_symmetric.1 hA).eigenvalues finrank_euclidean_space

/-- The eigenvalues of a hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ :=
λ i, hA.eigenvalues₀ $ (fintype.equiv_of_card_eq (fintype.card_fin _)).symm i

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvector_basis : orthonormal_basis n 𝕜 (euclidean_space 𝕜 n) :=
((is_hermitian_iff_is_symmetric.1 hA).eigenvector_basis finrank_euclidean_space).reindex
  (fintype.equiv_of_card_eq (fintype.card_fin _))

/-- A matrix whose columns are an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvector_matrix : matrix n n 𝕜 :=
(pi.basis_fun 𝕜 n).to_matrix (eigenvector_basis hA).to_basis

/-- The inverse of `eigenvector_matrix` -/
noncomputable def eigenvector_matrix_inv : matrix n n 𝕜 :=
(eigenvector_basis hA).to_basis.to_matrix (pi.basis_fun 𝕜 n)

lemma eigenvector_matrix_mul_inv :
  hA.eigenvector_matrix ⬝ hA.eigenvector_matrix_inv = 1 :=
by apply basis.to_matrix_mul_to_matrix_flip

/-- *Diagonalization theorem*, *spectral theorem* for matrices; A hermitian matrix can be
diagonalized by a change of basis.

For the spectral theorem on linear maps, see `diagonalization_basis_apply_self_apply`. -/
theorem spectral_theorem :
  hA.eigenvector_matrix_inv ⬝ A =
    diagonal (coe ∘ hA.eigenvalues) ⬝ hA.eigenvector_matrix_inv :=
begin
  rw [eigenvector_matrix_inv, basis_to_matrix_basis_fun_mul],
  ext i j,
  convert @linear_map.is_symmetric.diagonalization_basis_apply_self_apply 𝕜 _ _
    (pi_Lp 2 (λ (_ : n), 𝕜)) _ A.to_lin' (is_hermitian_iff_is_symmetric.1 hA) _ (fintype.card n)
    finrank_euclidean_space (euclidean_space.single j 1)
    ((fintype.equiv_of_card_eq (fintype.card_fin _)).symm i),
  { rw [eigenvector_basis, to_lin'_apply],
    simp only [basis.to_matrix, basis.coe_to_orthonormal_basis_repr, basis.equiv_fun_apply],
    simp_rw [orthonormal_basis.coe_to_basis_repr_apply, orthonormal_basis.reindex_repr,
      euclidean_space.single, pi_Lp.equiv_symm_apply', mul_vec_single, mul_one],
    refl },
  { simp only [diagonal_mul, (∘), eigenvalues, eigenvector_basis],
    rw [basis.to_matrix_apply,
      orthonormal_basis.coe_to_basis_repr_apply, orthonormal_basis.reindex_repr,
      pi.basis_fun_apply, eigenvalues₀, linear_map.coe_std_basis,
      euclidean_space.single, pi_Lp.equiv_symm_apply'] }
end

/-- The determinant of a hermitian matrix is the product of its eigenvalues. -/
lemma det_eq_prod_eigenvalues_of_is_hermitian : det A = ∏ i, hA.eigenvalues i :=
begin
  apply mul_left_cancel₀ (det_ne_zero_of_left_inverse (eigenvector_matrix_mul_inv hA)),
  rw [←det_mul, spectral_theorem, det_mul, mul_comm, det_diagonal]
end

end is_hermitian

end matrix
