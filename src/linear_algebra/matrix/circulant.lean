/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import linear_algebra.matrix.symmetric
import data.polynomial.monomial
import data.matrix.pequiv
import data.equiv.fin

/-!
# Circulant matrices

This file contains the definition and basic results about circulant matrices.

## Main results

- `matrix.cir`: introduce the definition of a circulant matrix
                generated by a given vector `v : I → α`.

## Implementation notes

`fin.foo` is the `fin n` version of `foo`.
Namely, the index type of the circulant matrices in discussion is `fin n`.

## Tags

cir, matrix
-/

variables {α β I J R : Type*} {n : ℕ}

namespace matrix
open_locale matrix big_operators

/-- Given the condition `[has_sub I]` and a vector `v : I → α`,
    we define `cir v` to be the circulant matrix generated by `v` of type `matrix I I α`. -/
def cir [has_sub I] (v : I → α) : matrix I I α
| i j := v (i - j)

lemma cir_col_zero_eq [add_group I] (v : I → α) :
  (λ i, (cir v) i 0) = v :=
by ext; simp [cir]

lemma cir_ext_iff [add_group I] {v w : I → α} :
  cir v = cir w ↔ v = w :=
begin
  split,
  { intro h, rw [← cir_col_zero_eq v, ← cir_col_zero_eq w, h] },
  { rintro rfl, refl }
end

lemma fin.cir_ext_iff {v w : fin n → α} :
  cir v = cir w ↔ v = w :=
begin
  induction n with n ih,
  { tidy },
  exact cir_ext_iff
end

lemma transpose_cir [add_group I] (v : I → α) :
  (cir v)ᵀ =  cir (λ i, v (-i)) :=
by ext; simp [cir]

lemma conj_transpose_cir [has_star α] [add_group I] (v : I → α) :
  (cir v)ᴴ = cir (star (λ i, v (-i))) :=
by ext; simp [cir]

lemma fin.transpose_cir (v : fin n → α) :
  (cir v)ᵀ =  cir (λ i, v (-i)) :=
begin
  induction n with n ih, {tidy},
  simp [transpose_cir]
end

lemma fin.conj_transpose_cir [has_star α] (v : fin n → α) :
  (cir v)ᴴ = cir (star (λ i, v (-i))) :=
begin
  induction n with n ih, {tidy},
  simp [conj_transpose_cir]
end

lemma map_cir [has_sub I] (v : I → α) (f : α → β) :
  (cir v).map f = cir (λ i, f (v i)) :=
by ext; simp [cir]

lemma cir_neg [has_neg α] [has_sub I] (v : I → α) :
  cir (- v) = - cir v :=
by ext; simp [cir]

lemma cir_add [has_add α] [has_sub I] (v w : I → α) :
  cir v + cir w = cir (v + w) :=
by ext; simp [cir]

lemma cir_sub [has_sub α] [has_sub I] (v w : I → α) :
  cir v - cir w = cir (v - w) :=
by ext; simp [cir]

lemma cir_mul [comm_semiring α] [fintype I] [add_comm_group I] (v w : I → α) :
  cir v ⬝ cir w = cir (mul_vec (cir w) v) :=
begin
  ext i j,
  simp only [mul_apply, mul_vec, cir, dot_product, mul_comm],
  refine fintype.sum_equiv (equiv.sub_left i) _ _ (by simp),
end

lemma fin.cir_mul [comm_semiring α] (v w : fin n → α) :
  cir v ⬝ cir w = cir (mul_vec (cir w) v) :=
begin
  induction n with n ih, {refl},
  exact cir_mul v w,
end

/-- Circulant matrices commute in multiplication under certain condations. -/
lemma cir_mul_comm
[comm_semigroup α] [add_comm_monoid α] [fintype I] [add_comm_group I] (v w : I → α) :
  cir v ⬝ cir w = cir w ⬝ cir v :=
begin
  ext i j,
  simp only [mul_apply, cir, mul_comm],
  refine fintype.sum_equiv ((equiv.sub_left i).trans (equiv.add_right j)) _ _ _,
  intro x,
  congr' 2,
  { simp },
  { simp only [equiv.coe_add_right, function.comp_app,
               equiv.coe_trans, equiv.sub_left_apply],
    abel }
end

lemma fin.cir_mul_comm
[comm_semigroup α] [add_comm_monoid α] (v w : fin n → α) :
  cir v ⬝ cir w = cir w ⬝ cir v :=
begin
  induction n with n ih, {refl},
  exact cir_mul_comm v w,
end

/-- `k • cir v` is another circluant matrix `cir (k • v)`. -/
lemma cir_smul [has_sub I] [has_scalar R α] {k : R} {v : I → α} :
  cir (k • v) = k • cir v :=
by {ext, simp [cir]}

lemma zero_eq_cir [has_zero α] [has_sub I]:
  (0 : matrix I I α) = cir (λ i, 0) :=
by ext; simp [cir]

/-- The identity matrix is a circulant matrix. -/
lemma one_eq_cir [has_zero α] [has_one α] [decidable_eq I] [add_group I]:
  (1 : matrix I I α) = cir (λ i, ite (i = 0) 1 0) :=
begin
  ext,
  simp only [cir, one_apply],
  congr' 1,
  apply propext sub_eq_zero.symm,
end

/-- An alternative version of `one_eq_cir`. -/
lemma one_eq_cir' [has_zero α] [has_one α] [decidable_eq I] [add_group I]:
  (1 : matrix I I α) = cir (λ i, (1 : matrix I I α) i 0) :=
one_eq_cir

lemma fin.one_eq_cir [has_zero α] [has_one α] :
  (1 : matrix (fin n) (fin n) α) = cir (λ i, ite (i.1 = 0) 1 0) :=
begin
  induction n with n, {dec_trivial},
  convert one_eq_cir,
  ext, congr' 1,
  apply propext,
  exact (fin.ext_iff x 0).symm,
end

/-- For a one-ary predicate `p`, `p` applied to every entry of `cir v` is true
    if `p` applied to every entry of `v` is true. -/
lemma pred_cir_entry_of_pred_vec_entry [has_sub I] {p : α → Prop} {v : I → α} :
  (∀ k, p (v k)) → ∀ i j, p ((cir v) i j) :=
begin
  intros h i j,
  simp [cir],
  exact h (i - j),
end

/-- Given a set `S`, every entry of `cir v` is in `S` if every entry of `v` is in `S`. -/
lemma cir_entry_in_of_vec_entry_in [has_sub I] {S : set α} {v : I → α} :
  (∀ k, v k ∈ S) → ∀ i j, (cir v) i j ∈ S :=
@pred_cir_entry_of_pred_vec_entry α I _ S v

/-- The circulant matrix `cir v` is symmetric iff `∀ i j, v (j - i) = v (i - j)`. -/
lemma cir_is_sym_ext_iff' [has_sub I] {v : I → α} :
  (cir v).is_symm ↔ ∀ i j, v (j - i) = v (i - j) :=
by simp [is_symm.ext_iff, cir]

/-- The circulant matrix `cir v` is symmetric iff `v (- i) = v i` if `[add_group I]`. -/
lemma cir_is_sym_ext_iff [add_group I] {v : I → α} :
  (cir v).is_symm ↔ ∀ i, v (- i) = v i :=
begin
  rw [cir_is_sym_ext_iff'],
  split,
  { intros h i, convert h i 0; simp },
  { intros h i j, convert h (i - j), simp }
end

lemma fin.cir_is_sym_ext_iff {v : fin n → α} :
  (cir v).is_symm ↔ ∀ i, v (- i) = v i :=
begin
  induction n with n ih,
  { rw [cir_is_sym_ext_iff'],
    split;
    {intros h i, have :=i.2, simp* at *} },
  convert cir_is_sym_ext_iff,
end

/-- If `cir v` is symmetric, `∀ i j : I, v (j - i) = v (i - j)`. -/
lemma cir_is_sym_apply' [has_sub I] {v : I → α} (h : (cir v).is_symm) (i j : I) :
  v (j - i) = v (i - j) :=
cir_is_sym_ext_iff'.1 h i j

/-- If `cir v` is symmetric, `∀ i j : I, v (- i) = v i`. -/
lemma cir_is_sym_apply [add_group I] {v : I → α} (h : (cir v).is_symm) (i : I) :
  v (-i) = v i :=
cir_is_sym_ext_iff.1 h i

lemma fin.cir_is_sym_apply {v : fin n → α} (h : (cir v).is_symm) (i : fin n) :
  v (-i) = v i :=
fin.cir_is_sym_ext_iff.1 h i

/-- The associated polynomial `(v 0) + (v 1) * X + ... + (v (n-1)) * X ^ (n-1)` to `cir v`.-/
noncomputable
def cir_poly [semiring α] (v : fin n → α) : polynomial α :=
∑ i : fin n, polynomial.monomial i (v i)

/-- `cir_perm n` is the cyclic permutation over `fin n`. -/
def cir_perm : Π n, equiv.perm (fin n) := λ n, equiv.symm (fin_rotate n)

/-- `cir_P α n` is the cyclic permutation matrix of order `n` with entries of type `α`. -/
def cir_P (α) [has_zero α] [has_one α] (n : ℕ) : matrix (fin n) (fin n) α :=
(cir_perm n).to_pequiv.to_matrix

end matrix
