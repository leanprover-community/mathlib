/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.matrix.determinant
import tactic.fin_cases

/-!
# Block matrices and their determinant

This file defines a predicate `matrix.block_triangular` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

 * `matrix.block_triangular` expresses that a `o` by `o` matrix is block triangular,
   if the rows and columns are ordered according to some order `b : o → α`

## Main results
  * `det_of_block_triangular`: the determinant of a block triangular matrix
    is equal to the product of the determinants of all the blocks
  * `det_of_upper_triangular` and `det_of_lower_triangular`: the determinant of
    a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/

open finset function order_dual
open_locale big_operators matrix

universes v

variables {α m n : Type*}
variables {R : Type v} [comm_ring R] {M : matrix m m R} {b : m → α}

namespace matrix

section has_lt
variables [has_lt α]

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `α`s. Then
`block_triangular M n b` says the matrix is block triangular. -/
def block_triangular (M : matrix m m R) (b : m → α) : Prop := ∀ ⦃i j⦄, b j < b i → M i j = 0

@[simp] protected lemma block_triangular.submatrix {f : n → m} (h : M.block_triangular b) :
  (M.submatrix f f).block_triangular (b ∘ f) :=
λ i j hij, h hij

lemma block_triangular_reindex_iff {b : n → α} {e : m ≃ n} :
  (reindex e e M).block_triangular b ↔ M.block_triangular (b ∘ e) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { convert h.submatrix,
    simp only [reindex_apply, submatrix_submatrix, submatrix_id_id, equiv.symm_comp_self] },
  { convert h.submatrix,
    simp only [comp.assoc b e e.symm, equiv.self_comp_symm, comp.right_id] }
end

protected lemma block_triangular.transpose :
  M.block_triangular b → Mᵀ.block_triangular (to_dual ∘ b) := swap

@[simp] protected lemma block_triangular_transpose_iff {b : m → αᵒᵈ} :
  Mᵀ.block_triangular b ↔ M.block_triangular (of_dual ∘ b) := forall_swap

end has_lt

lemma upper_two_block_triangular [preorder α]
  (A : matrix m m R) (B : matrix m n R) (D : matrix n n R) {a b : α} (hab : a < b) :
  block_triangular (from_blocks A B 0 D) (sum.elim (λ i, a) (λ j, b)) :=
begin
  intros k1 k2 hk12,
  have hor : ∀ (k : m ⊕ n), sum.elim (λ i, a) (λ j, b) k = a ∨ sum.elim (λ i, a) (λ j, b) k = b,
  { simp },
  have hne : a ≠ b, from λ h, lt_irrefl _ (lt_of_lt_of_eq hab h.symm),
  have ha : ∀ (k : m ⊕ n), sum.elim (λ i, a) (λ j, b) k = a → ∃ i, k = sum.inl i,
  { simp [hne.symm] },
  have hb : ∀ (k : m ⊕ n), sum.elim (λ i, a) (λ j, b) k = b → ∃ j, k = sum.inr j,
  { simp [hne] },
  cases (hor k1) with hk1 hk1; cases (hor k2) with hk2 hk2; rw [hk1, hk2] at hk12,
  { exact false.elim (lt_irrefl a hk12), },
  { exact false.elim (lt_irrefl _ (lt_trans hab hk12)) },
  { obtain ⟨i, hi⟩ := hb k1 hk1,
    obtain ⟨j, hj⟩ := ha k2 hk2,
    rw [hi, hj], simp },
  { exact absurd hk12 (irrefl b) }
end

/-! ### Determinant -/

variables [decidable_eq m] [fintype m] [decidable_eq n] [fintype n]

lemma equiv_block_det (M : matrix m m R) {p q : m → Prop} [decidable_pred p] [decidable_pred q]
  (e : ∀ x, q x ↔ p x) : (to_square_block_prop M p).det = (to_square_block_prop M q).det :=
by convert matrix.det_reindex_self (equiv.subtype_equiv_right e) (to_square_block_prop M q)

@[simp] lemma det_to_square_block_id (M : matrix m m R) (i : m) :
  (M.to_square_block id i).det = M i i :=
begin
  letI : unique {a // id a = i} := ⟨⟨⟨i, rfl⟩⟩, λ j, subtype.ext j.property⟩,
  exact (det_unique _).trans rfl,
end

lemma det_to_block (M : matrix m m R) (p : m → Prop) [decidable_pred p] :
  M.det = (from_blocks (to_block M p p) (to_block M p $ λ j, ¬p j)
    (to_block M (λ j, ¬p j) p) $ to_block M (λ j, ¬p j) $ λ j, ¬p j).det :=
begin
  rw ←matrix.det_reindex_self (equiv.sum_compl p).symm M,
  rw [det_apply', det_apply'],
  congr, ext σ, congr, ext,
  generalize hy : σ x = y,
  cases x; cases y;
  simp only [matrix.reindex_apply, to_block_apply, equiv.symm_symm,
    equiv.sum_compl_apply_inr, equiv.sum_compl_apply_inl,
    from_blocks_apply₁₁, from_blocks_apply₁₂, from_blocks_apply₂₁, from_blocks_apply₂₂,
    matrix.submatrix_apply],
end

lemma two_block_triangular_det (M : matrix m m R) (p : m → Prop) [decidable_pred p]
  (h : ∀ i, ¬ p i → ∀ j, p j → M i j = 0) :
  M.det = (to_square_block_prop M p).det * (to_square_block_prop M (λ i, ¬p i)).det :=
begin
  rw det_to_block M p,
  convert det_from_blocks_zero₂₁ (to_block M p p) (to_block M p (λ j, ¬p j))
    (to_block M (λ j, ¬p j) (λ j, ¬p j)),
  ext,
  exact h ↑i i.2 ↑j j.2
end

lemma two_block_triangular_det' (M : matrix m m R) (p : m → Prop) [decidable_pred p]
  (h : ∀ i, p i → ∀ j, ¬ p j → M i j = 0) :
  M.det = (to_square_block_prop M p).det * (to_square_block_prop M (λ i, ¬p i)).det :=
begin
  rw [M.two_block_triangular_det (λ i, ¬ p i), mul_comm],
  simp_rw not_not,
  congr' 1,
  exact equiv_block_det _ (λ _, not_not.symm),
  simpa only [not_not] using h,
end

protected lemma block_triangular.det [decidable_eq α] [linear_order α] (hM : block_triangular M b) :
  M.det = ∏ a in univ.image b, (M.to_square_block b a).det :=
begin
  unfreezingI { induction hs : univ.image b using finset.strong_induction
    with s ih generalizing m },
  subst hs,
  by_cases h : univ.image b = ∅,
  { haveI := univ_eq_empty_iff.1 (image_eq_empty.1 h),
    simp [h] },
  { let k := (univ.image b).max' (nonempty_of_ne_empty h),
    rw two_block_triangular_det' M (λ i, b i = k),
    { have : univ.image b = insert k ((univ.image b).erase k),
      { rw insert_erase, apply max'_mem },
      rw [this, prod_insert (not_mem_erase _ _)],
      refine congr_arg _ _,
      let b' := λ i : {a // b a ≠ k}, b ↑i,
      have h' :  block_triangular (M.to_square_block_prop (λ (i : m), b i ≠ k)) b',
      { intros i j, apply hM },
      have hb' : image b' univ = (image b univ).erase k,
      { apply subset_antisymm,
        { rw image_subset_iff,
          intros i _,
          apply mem_erase_of_ne_of_mem i.2 (mem_image_of_mem _ (mem_univ _)) },
        { intros i hi,
          rw mem_image,
          rcases mem_image.1 (erase_subset _ _ hi) with ⟨a, _, ha⟩,
          subst ha,
          exact ⟨⟨a, ne_of_mem_erase hi⟩, mem_univ _, rfl⟩ } },
      rw ih ((univ.image b).erase k) (erase_ssubset (max'_mem _ _)) h' hb',
      apply finset.prod_congr rfl,
      intros l hl,
      let he : {a // b' a = l} ≃ {a // b a = l},
      { have hc : ∀ (i : m), (λ a, b a = l) i → (λ a, b a ≠ k) i,
        { intros i hbi, rw hbi, exact ne_of_mem_erase hl },
        exact equiv.subtype_subtype_equiv_subtype hc },
      simp only [to_square_block_def],
      rw ← matrix.det_reindex_self he.symm (λ (i j : {a // b a = l}), M ↑i ↑j),
      refine congr_arg _ _,
      ext,
      simp [to_square_block_def, to_square_block_prop_def] },
  { intros i hi j hj,
    apply hM,
    rw hi,
    apply lt_of_le_of_ne _ hj,
    exact finset.le_max' (univ.image b) _ (mem_image_of_mem _ (mem_univ _)) } }
end

lemma block_triangular.det_fintype [decidable_eq α] [fintype α] [linear_order α]
  (h : block_triangular M b) :
  M.det = ∏ k : α, (M.to_square_block b k).det :=
begin
  refine h.det.trans (prod_subset (subset_univ _) $ λ a _ ha, _),
  have : is_empty {i // b i = a} := ⟨λ i, ha $ mem_image.2 ⟨i, mem_univ _, i.2⟩⟩,
  exactI det_is_empty,
end

lemma det_of_upper_triangular [linear_order m] (h : M.block_triangular id) :
  M.det = ∏ i : m, M i i :=
begin
  haveI : decidable_eq R := classical.dec_eq _,
  simp_rw [h.det, image_id, det_to_square_block_id],
end

lemma det_of_lower_triangular [linear_order m] (M : matrix m m R) (h : M.block_triangular to_dual) :
  M.det = ∏ i : m, M i i :=
by { rw ←det_transpose, exact det_of_upper_triangular h.transpose }

end matrix
