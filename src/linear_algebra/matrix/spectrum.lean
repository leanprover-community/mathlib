/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import analysis.inner_product_space.spectrum
/-! # Spectral theory of hermitian matrices

This file defines hermitian matrices (`matrix.is_hermitian`) and proves the spectral theorem for
matrices. The proof of the spectral theorem is based on the spectral theorem for linear maps
(`diagonalization_basis_apply_self_apply`).

## Tags

self-adjoint matrix, hermitian matrix, spectral theorem, diagonalization theorem

-/

namespace matrix

variables {𝕜 : Type*} [is_R_or_C 𝕜] [decidable_eq 𝕜] {n : Type*} [fintype n] [decidable_eq n]
variables {A : matrix n n 𝕜}

open_locale matrix

local notation `⟪`x`, `y`⟫` := @inner 𝕜 (pi_Lp 2 (λ (_ : n), 𝕜)) _ x y

/-- A matrix is hermitian if it is equal to its conjugate transpose. On the reals, this definition
captures symmetric matrices. -/
def is_hermitian (A : matrix n n 𝕜) : Prop := Aᴴ = A

/-- A matrix is hermitian iff the corresponding linear map is self adjoint. -/
lemma is_hermitian_iff_is_self_adjoint {A : matrix n n 𝕜} :
  is_hermitian A ↔ @inner_product_space.is_self_adjoint 𝕜 (pi_Lp 2 (λ (_ : n), 𝕜)) _ _ A.to_lin' :=
begin
  split,
  show A.is_hermitian → ∀ x y, ⟪A.mul_vec x, y⟫ = ⟪x, A.mul_vec y⟫,
  { intros h x y,
    unfold is_hermitian at h,
    simp only [euclidean_space.inner_eq_star_dot_product, star_mul_vec, matrix.dot_product_mul_vec,
      h, star_eq_conj_transpose] },
  show (∀ x y, ⟪A.mul_vec x, y⟫ = ⟪x, A.mul_vec y⟫) → A.is_hermitian,
  { intro h,
    ext i j,
    have := h (euclidean_space.single i 1) (euclidean_space.single j 1),
    simpa [euclidean_space.inner_single_right, euclidean_space.inner_single_left] using this}
end

namespace is_hermitian

variables (hA : A.is_hermitian)

/-- The eigenvalues of a hermitian matrix, indexed by `fin (fintype.card n)` where `n` is the index
type of the matrix. -/
noncomputable def eigenvalues₀ : fin (fintype.card n) → ℝ :=
@inner_product_space.is_self_adjoint.eigenvalues 𝕜 _ _ (pi_Lp 2 (λ (_ : n), 𝕜)) _ A.to_lin'
  (is_hermitian_iff_is_self_adjoint.1 hA) _ (fintype.card n) finrank_euclidean_space

/-- The eigenvalues of a hermitian matrix, reusing the index `n` of the matrix entries. -/
noncomputable def eigenvalues : n → ℝ :=
  λ i, hA.eigenvalues₀ $ (fintype.equiv_of_card_eq (fintype.card_fin _)).symm i

/-- A choice of an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvector_basis : basis n 𝕜 (n → 𝕜) :=
  (@inner_product_space.is_self_adjoint.eigenvector_basis 𝕜 _ _
  (pi_Lp 2 (λ (_ : n), 𝕜)) _ A.to_lin' (is_hermitian_iff_is_self_adjoint.1 hA) _ (fintype.card n)
  finrank_euclidean_space).reindex (fintype.equiv_of_card_eq (fintype.card_fin _))

/-- A matrix whose columns are an orthonormal basis of eigenvectors of a hermitian matrix. -/
noncomputable def eigenvector_matrix : matrix n n 𝕜 :=
  (pi.basis_fun 𝕜 n).to_matrix (eigenvector_basis hA)

/-- The inverse of `eigenvector_matrix` -/
noncomputable def eigenvector_matrix_inv : matrix n n 𝕜 :=
  (eigenvector_basis hA).to_matrix (pi.basis_fun 𝕜 n)

lemma eigenvector_matrix_mul_inv :
  hA.eigenvector_matrix ⬝ hA.eigenvector_matrix_inv = 1 :=
by apply basis.to_matrix_mul_to_matrix_flip

/-- *Diagonalization theorem*, *spectral theorem* for matrices; A hermitian matrix can be
diagonalized by a change of basis.

For the spectral theorem on linear maps, see `diagonalization_basis_apply_self_apply`. -/
theorem spectral_theorem :
  hA.eigenvector_matrix_inv ⬝ A
    = diagonal (coe ∘ hA.eigenvalues) ⬝ hA.eigenvector_matrix_inv :=
begin
  rw [eigenvector_matrix_inv, basis_to_matrix_basis_fun_mul],
  ext i j,
  convert @inner_product_space.is_self_adjoint.diagonalization_basis_apply_self_apply 𝕜 _ _
    (pi_Lp 2 (λ (_ : n), 𝕜)) _ A.to_lin' (is_hermitian_iff_is_self_adjoint.1 hA) _ (fintype.card n)
    finrank_euclidean_space (euclidean_space.single j 1)
    ((fintype.equiv_of_card_eq (fintype.card_fin _)).symm i),
  { rw [eigenvector_basis, inner_product_space.is_self_adjoint.diagonalization_basis,
      to_lin'_apply],
    simp only [basis.to_matrix, basis.coe_to_orthonormal_basis_repr, basis.equiv_fun_apply],
    rw [basis.reindex_repr, euclidean_space.mul_vec_single],
    refl },
  { simp only [diagonal_mul, (∘), eigenvalues, eigenvector_basis,
      inner_product_space.is_self_adjoint.diagonalization_basis],
    rw [basis.to_matrix_apply, basis.coe_to_orthonormal_basis_repr, basis.reindex_repr,
      basis.equiv_fun_apply, pi.basis_fun_apply],
    refl }
end

end is_hermitian

end matrix
