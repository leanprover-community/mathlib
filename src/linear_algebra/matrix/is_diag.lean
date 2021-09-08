/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.orthogonal
import data.matrix.kronecker

/-!
# Diagonal matrices

This file contains the definition and basic results about diagonal matrices.

## Main results

- `matrix.is_diag`: a proposition that stats a given square matrix `A` is diagonal
                    (i.e. `∀ m n, i ≠ j → A m n = 0`).

## Tags

diag, diagonal, matrix
-/

namespace matrix

variables {α β R n m : Type*}

open function
open_locale matrix kronecker

/-- `A.is_diag` means square matrix `A` is a dianogal matrix: `∀ i j, i ≠ j → A i j = 0`. -/
def is_diag [has_zero α] (A : matrix n n α) : Prop := ∀ ⦃i j⦄, i ≠ j → A i j = 0

/-- Matrix `A` is diagonal iff there is a vector `d`
    such that A is the diagonal matix generated by `d`. -/
lemma is_diag_iff_eq_diagonal [has_zero α] [decidable_eq n] (A : matrix n n α) :
  A.is_diag ↔ (∃ d, A = diagonal d) :=
begin
  split,
  { intros h,
    use (λ i, A i i),
    ext i j,
    by_cases g : i = j;
    simp [@h i j, g] },
  { rintros ⟨d, rfl⟩ i j h, simp [h] }
end

/-- Every unit matrix is diagonal. -/
@[simp] lemma is_diag_unit [has_zero α] [subsingleton n] (A : matrix n n α) : A.is_diag :=
by { intros i j h, have h' := subsingleton.elim i j, contradiction }

/-- Every zero matrix is diagonal. -/
@[simp] lemma is_diag_zero [has_zero α] : (0 : matrix n n α).is_diag :=
λ i j h, rfl

/-- Every identity matrix is diagonal. -/
@[simp] lemma is_diag_one [decidable_eq n] [has_zero α] [has_one α] :
  (1 : matrix n n α).is_diag :=
λ i j, one_apply_ne

@[simp] lemma is_diag.map [has_zero α] [has_zero β]
{A : matrix n n α} (ha : A.is_diag) {f : α → β} (hf : f 0 = 0) :
  (A.map f).is_diag :=
by { intros i j h, simp [ha h, hf] }

lemma is_diag.neg [add_group α] {A : matrix n n α} (ha : A.is_diag) :
  (-A).is_diag :=
by { intros i j h, simp [ha h] }

@[simp] lemma is_diag.add
  [add_zero_class α] {A B : matrix n n α} (ha : A.is_diag) (hb : B.is_diag) :
  (A + B).is_diag :=
by { intros i j h, simp [ha h, hb h] }

@[simp] lemma is_diag.sub [add_group α]
  {A B : matrix n n α} (ha : A.is_diag) (hb : B.is_diag) :
  (A - B).is_diag :=
by { intros i j h, simp [ha h, hb h] }

@[simp] lemma is_diag.smul [monoid R] [add_monoid α] [distrib_mul_action R α]
  {k : R} {A : matrix n n α} (ha : A.is_diag) :
  (k • A).is_diag :=
by { intros i j h, simp [ha h] }

@[simp] lemma is_diag.transpose [has_zero α] {A : matrix n n α} (ha : A.is_diag) : Aᵀ.is_diag :=
λ i j h, ha h.symm

@[simp] lemma is_diag.conj_transpose
  [semiring α] [star_ring α] {A : matrix n n α} (ha : A.is_diag) :
  Aᴴ.is_diag :=
ha.transpose.map (star_zero _)

@[simp] lemma is_diag.minor [has_zero α]
  {A : matrix n n α} (ha : A.is_diag) {f : m → n} (hf : injective f) :
  (A.minor f f).is_diag :=
λ i j h, ha (hf.ne h)

/-- `(A ⊗ B).is_diag` if both `A` and `B` are diagonal. -/
@[simp] lemma is_diag.kronecker [mul_zero_class α]
  {A : matrix m m α} {B : matrix n n α} (hA: A.is_diag) (hB: B.is_diag) :
  (A ⊗ₖ B).is_diag :=
begin
  rintros ⟨a, b⟩ ⟨c, d⟩ h,
  dsimp [kronecker_apply],
  by_cases hac: a = c,
  { have hbd: b ≠ d, { tidy }, simp [hB hbd] },
  { simp [hA hac] },
end

@[simp] lemma is_diag.diagonal [has_zero α] [decidable_eq n] (d : n → α) :
  (diagonal d).is_diag :=
λ i j, matrix.diagonal_apply_ne

lemma is_diag.is_symm [has_zero α] {A : matrix n n α} (h : A.is_diag) :
  A.is_symm :=
begin
  ext i j,
  by_cases g : i = j, { rw g },
  simp [h g, h (ne.symm g)],
end

/-- The block matrix `A.from_blocks 0 0 D` is diagonal if  `A` and `D` are diagonal. -/
lemma is_diag.from_blocks [has_zero α]
  {A : matrix m m α} {D : matrix n n α}
  (ha : A.is_diag) (hd : D.is_diag) :
  (A.from_blocks 0 0 D).is_diag :=
begin
  rintros (i | i) (j | j) hij,
  { exact ha (ne_of_apply_ne _ hij) },
  { refl },
  { refl },
  { exact hd (ne_of_apply_ne _ hij) },
end

/-- This is the `iff` version of `matrix.is_diag.from_blocks`. -/
lemma is_diag_from_blocks_iff [has_zero α]
  {A : matrix m m α} {B : matrix m n α} {C : matrix n m α} {D : matrix n n α} :
  (A.from_blocks B C D).is_diag ↔ A.is_diag ∧ B = 0 ∧ C = 0 ∧ D.is_diag :=
begin
  split,
  { intros h,
    refine ⟨λ i j hij, _, ext $ λ i j, _, ext $ λ i j, _, λ i j hij, _⟩,
    { exact h (sum.inl_injective.ne hij), },
    { exact h sum.inl_ne_inr, },
    { exact h sum.inr_ne_inl, },
    { exact h (sum.inr_injective.ne hij), }, },
  { rintros ⟨ha, hb, hc, hd⟩,
    convert is_diag.from_blocks ha hd }
end

/-- A symmetric block matrix `A.from_blocks B C D` is diagonal
    if  `A` and `D` are diagonal and `B` is `0`. -/
lemma is_diag.from_blocks_of_is_symm [has_zero α]
  {A : matrix m m α} {C : matrix n m α} {D : matrix n n α}
  (h : (A.from_blocks 0 C D).is_symm) (ha : A.is_diag) (hd : D.is_diag) :
  (A.from_blocks 0 C D).is_diag :=
begin
  rw ←(is_symm_from_blocks_iff.1 h).2.1,
  exact ha.from_blocks hd,
end

/-- `(A ⬝ Aᵀ).is_diag` iff `A.has_orthogonal_rows`. -/
lemma mul_transpose_self_is_diag_iff_has_orthogonal_rows
  [fintype n] [has_mul α] [add_comm_monoid α] {A : matrix m n α} :
  (A ⬝ Aᵀ).is_diag ↔ A.has_orthogonal_rows :=
begin
  split,
  any_goals
  { rintros h i₁ i₂ hi,
    have h' := h hi,
    simp [dot_product, mul_apply, *] at * },
end

/-- `(Aᵀ ⬝ A).is_diag` iff `A.has_orthogonal_cols`. -/
lemma transpose_mul_self_is_diag_iff_has_orthogonal_cols
  [fintype m] [has_mul α] [add_comm_monoid α] {A : matrix m n α} :
  (Aᵀ ⬝ A).is_diag ↔ A.has_orthogonal_cols :=
begin
  rw [←transpose_has_orthogonal_rows_iff_has_orthogonal_cols],
  convert mul_transpose_self_is_diag_iff_has_orthogonal_rows,
  simp,
end

end matrix
