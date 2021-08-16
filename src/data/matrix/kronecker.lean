/-
Copyright (c) 2021 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Eric Wieser
-/

import data.matrix.basic
import linear_algebra.tensor_product
import ring_theory.tensor_product

/-!
# Kronecker product of matrices

This defines the [Kronecker product](https://en.wikipedia.org/wiki/Kronecker_product).

## Main definitions

* `matrix.kronecker_map`: A generalization of the Kronecker product: given a map `f : α → β → γ`
  and matrices `A` and `B` with coefficients in `α` and `β`, respectively, it is defined as the
  matrix with coefficients in `γ` such that
  `kronecker_map f A B (i₁, i₂) (j₁, j₂) = f (A i₁ j₁) (B i₁ j₂)`.
* `matrix.kronecker_map_linear`: when `f` is bilinear, so is `kronecker_map f`.

## Specializations

* `matrix.kronecker`: An alias of `kronecker_map (*)`. Prefer using the notation.
* `matrix.kronecker_bilinear`: `matrix.kronecker` is bilinear

* `matrix.kronecker_tmul`: An alias of `kronecker_map (⊗ₜ)`. Prefer using the notation.
* `matrix.kronecker_tmul_bilinear`: `matrix.tmul_kronecker` is bilinear

## Notations

These require `open_locale kronecker`:

* `A ⊗ₖ B` for `kronecker_map (*) A B`. Lemmas about this notation use the token `kronecker`.
* `A ⊗ₖₜ B` and `A ⊗ₖₜ[R] B` for `kronecker_map (⊗ₜ) A B`.  Lemmas about this notation use the token
  `kronecker_tmul`.

-/

namespace matrix

open_locale matrix

variables {R α α' β β' γ γ' : Type*}
variables {l m n p : Type*} [fintype l] [fintype m] [fintype n] [fintype p]
variables {l' m' n' p' : Type*} [fintype l'] [fintype m'] [fintype n'] [fintype p']

section kronecker_map

/-- Produce a matrix with `f` applied to every pair of elements from `A` and `B`. -/
@[simp] def kronecker_map (f : α → β → γ) (A : matrix l m α) (B : matrix n p β) :
  matrix (l × n) (m × p) γ
| i j := f (A i.1 j.1) (B i.2 j.2)

lemma kronecker_map_transpose (f : α → β → γ)
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f Aᵀ Bᵀ = (kronecker_map f A B)ᵀ :=
ext $ λ i j, rfl

lemma kronecker_map_map_left (f : α' → β → γ) (g : α → α')
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f (A.map g) B = kronecker_map (λ a b, f (g a) b) A B :=
ext $ λ i j, rfl

lemma kronecker_map_map_right (f : α → β' → γ) (g : β → β')
  (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f A (B.map g) = kronecker_map (λ a b, f a (g b)) A B :=
ext $ λ i j, rfl

lemma kronecker_map_map (f : α → β → γ) (g : γ → γ')
  (A : matrix l m α) (B : matrix n p β) :
  (kronecker_map f A B).map g = kronecker_map (λ a b, g (f a b)) A B :=
ext $ λ i j, rfl

@[simp] lemma kronecker_map_zero_left [has_zero α] [has_zero γ]
  (f : α → β → γ) (hf : ∀ b, f 0 b = 0) (B : matrix n p β) :
  kronecker_map f (0 : matrix l m α) B = 0:=
ext $ λ i j,hf _

@[simp] lemma kronecker_map_zero_right [has_zero β] [has_zero γ]
  (f : α → β → γ) (hf : ∀ a, f a 0 = 0) (A : matrix l m α) :
  kronecker_map f A (0 : matrix n p β) = 0 :=
ext $ λ i j, hf _

lemma kronecker_map_add_left [has_add α] [has_add γ] (f : α → β → γ)
  (hf : ∀ a₁ a₂ b, f (a₁ + a₂) b = f a₁ b + f a₂ b)
  (A₁ A₂ : matrix l m α) (B : matrix n p β) :
  kronecker_map f (A₁ + A₂) B = kronecker_map f A₁ B + kronecker_map f A₂ B :=
ext $ λ i j, hf _ _ _

lemma kronecker_map_add_right [has_add β] [has_add γ] (f : α → β → γ)
  (hf : ∀ a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂)
  (A : matrix l m α) (B₁ B₂ : matrix n p β) :
  kronecker_map f A (B₁ + B₂) = kronecker_map f A B₁ + kronecker_map f A B₂ :=
ext $ λ i j, hf _ _ _

lemma kronecker_map_smul_left [has_scalar R α] [has_scalar R γ] (f : α → β → γ)
  (r : R) (hf : ∀ a b, f (r • a) b = r • f a b) (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f (r • A) B = r • kronecker_map f A B :=
ext $ λ i j, hf _ _

lemma kronecker_map_smul_right [has_scalar R β] [has_scalar R γ] (f : α → β → γ)
  (r : R) (hf : ∀ a b, f a (r • b) = r • f a b) (A : matrix l m α) (B : matrix n p β) :
  kronecker_map f A (r • B) = r • kronecker_map f A B :=
ext $ λ i j, hf _ _

lemma kronecker_map_diagonal_diagonal [has_zero α] [has_zero β] [has_zero γ]
  [decidable_eq m] [decidable_eq n]
  (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (a : m → α) (b : n → β):
  kronecker_map f (diagonal a) (diagonal b) = diagonal (λ mn, f (a mn.1) (b mn.2)) :=
begin
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩,
  simp [diagonal, apply_ite f, ite_and, ite_apply, apply_ite (f (a i₁)), hf₁, hf₂],
end

@[simp] lemma kronecker_map_one_one [has_zero α] [has_zero β] [has_zero γ]
  [has_one α] [has_one β] [has_one γ] [decidable_eq m] [decidable_eq n]
  (f : α → β → γ) (hf₁ : ∀ b, f 0 b = 0) (hf₂ : ∀ a, f a 0 = 0) (hf₃ : f 1 1 = 1) :
  kronecker_map f (1 : matrix m m α) (1 : matrix n n β) = 1 :=
(kronecker_map_diagonal_diagonal _ hf₁ hf₂ _ _).trans $ by simp only [hf₃, diagonal_one]

/-- When `f` is bilinear then `matrix.kronecker_map f` is also bilinear. -/
@[simps]
def kronecker_map_linear [comm_semiring R]
  [add_comm_monoid α] [add_comm_monoid β] [add_comm_monoid γ]
  [module R α] [module R β] [module R γ]
  (f : α →ₗ[R] β →ₗ[R] γ) :
  matrix l m α →ₗ[R] matrix n p β →ₗ[R] matrix (l × n) (m × p) γ :=
linear_map.mk₂ R
  (kronecker_map (λ r s, f r s))
  (kronecker_map_add_left _ $ f.map_add₂)
  (λ r, kronecker_map_smul_left _ _ $ f.map_smul₂ _)
  (kronecker_map_add_right _ $ λ a, (f a).map_add)
  (λ r, kronecker_map_smul_right _ _ $ λ a, (f a).map_smul r)

/-- `matrix.kronecker_map_linear` commutes with `⬝` if `f` commutes with `*`.

This is primarily used with `R = ℕ` to prove `matrix.mul_kronecker_mul`. -/
lemma kronecker_map_linear_mul_mul [comm_semiring R]
  [non_unital_non_assoc_semiring α] [non_unital_non_assoc_semiring β]
  [non_unital_non_assoc_semiring γ]
  [module R α] [module R β] [module R γ]
  (f : α →ₗ[R] β →ₗ[R] γ) (h_comm : ∀ a b a' b', f (a * b) (a' * b') = f a a' * f b b')
  (A : matrix l m α) (B : matrix m n α) (A' : matrix l' m' β) (B' : matrix m' n' β) :
  kronecker_map_linear f (A ⬝ B) (A' ⬝ B') =
    (kronecker_map_linear f A A') ⬝ (kronecker_map_linear f B B') :=
begin
  ext ⟨i, i'⟩ ⟨j, j'⟩,
  simp only [kronecker_map_linear_apply_apply, mul_apply, ← finset.univ_product_univ,
    finset.sum_product, kronecker_map],
  simp_rw [f.map_sum, linear_map.sum_apply, linear_map.map_sum, h_comm],
end

lemma kronecker_map_assoc {δ ξ ω ω' : Type*} (f : α → β → γ) (g : γ → δ → ω) (f' : α → ξ → ω')
  (g' : β → δ → ξ) {q r : Type*} [fintype q] [fintype r] (A : matrix l m α) (B : matrix n p β)
  (D : matrix q r δ) (φ : ω ≃ ω') (hφ : ∀ a b d, φ (g (f a b) d ) = f' a (g' b d )) :
  (reindex (equiv.prod_assoc l n q) (equiv.prod_assoc m p r)).trans (equiv.map_matrix φ)
    (kronecker_map g (kronecker_map f A B) D) = kronecker_map f' A (kronecker_map g' B D) :=
begin
  ext i j,
  simp only [equiv.prod_assoc_symm_apply, function.comp_app, minor_apply, equiv.map_matrix_apply,
    map_apply, reindex_apply, equiv.coe_trans, kronecker_map],
  apply hφ,
end

end kronecker_map

/-! ### Specialization to `matrix.kronecker_map (*)` -/

section kronecker

variables (R)

open_locale matrix

/-- The Kronecker product. This is just a shorthand for `kronecker_map (*)`. Prefer the notation
`⊗ₖ` rather than this definition. -/
@[simp] def kronecker [has_mul α] : matrix l m α → matrix n p α → matrix (l × n) (m × p) α :=
kronecker_map (*)

localized "infix ` ⊗ₖ `:100 := matrix.kronecker_map (*)" in kronecker

@[simp]
lemma kronecker_apply [has_mul α] (A : matrix l m α) (B : matrix n p α) (i₁ i₂ j₁ j₂) :
  (A ⊗ₖ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ * B i₂ j₂ := rfl

/-- `matrix.kronecker` as a bilinear map. -/
def kronecker_bilinear [comm_semiring R] [semiring α] [algebra R α] :
  matrix l m α →ₗ[R] matrix n p α →ₗ[R] matrix (l × n) (m × p) α :=
kronecker_map_linear (algebra.lmul R α).to_linear_map

/-! What follows is a copy, in order, of every `matrix.kronecker_map` lemma above that has
hypotheses which can be filled by properties of `*`. -/

@[simp] lemma zero_kronecker [mul_zero_class α] (B : matrix n p α) : (0 : matrix l m α) ⊗ₖ B = 0 :=
kronecker_map_zero_left _ zero_mul B

@[simp] lemma kronecker_zero [mul_zero_class α] (A : matrix l m α) : A ⊗ₖ (0 : matrix n p α) = 0 :=
kronecker_map_zero_right _ mul_zero A

lemma add_kronecker [distrib α] (A₁ A₂ : matrix l m α) (B : matrix n p α) :
  (A₁ + A₂) ⊗ₖ B = A₁ ⊗ₖ B + A₂ ⊗ₖ B :=
kronecker_map_add_left _ add_mul _ _ _

lemma kronecker_add [distrib α] (A : matrix l m α) (B₁ B₂ : matrix n p α) :
  A ⊗ₖ (B₁ + B₂) = A ⊗ₖ B₁ + A ⊗ₖ B₂ :=
kronecker_map_add_right _ mul_add _ _ _

lemma smul_kronecker [monoid R] [monoid α] [mul_action R α] [is_scalar_tower R α α]
  (r : R) (A : matrix l m α) (B : matrix n p α) :
  (r • A) ⊗ₖ B = r • (A ⊗ₖ B) :=
kronecker_map_smul_left _ _ (λ _ _, smul_mul_assoc _ _ _) _ _

lemma kronecker_smul [monoid R] [monoid α] [mul_action R α] [smul_comm_class R α α]
  (r : R) (A : matrix l m α) (B : matrix n p α) :
  A ⊗ₖ (r • B) = r • (A ⊗ₖ B) :=
kronecker_map_smul_right _ _ (λ _ _, mul_smul_comm _ _ _) _ _

lemma diagonal_kronecker_diagonal [mul_zero_class α]
  [decidable_eq m] [decidable_eq n]
  (a : m → α) (b : n → α):
  (diagonal a) ⊗ₖ (diagonal b) = diagonal (λ mn, (a mn.1) * (b mn.2)) :=
kronecker_map_diagonal_diagonal _ zero_mul mul_zero _ _

@[simp] lemma one_kronecker_one [mul_zero_one_class α] [decidable_eq m] [decidable_eq n] :
  (1 : matrix m m α) ⊗ₖ (1 : matrix n n α) = 1 :=
kronecker_map_one_one _ zero_mul mul_zero (one_mul _)

lemma mul_kronecker_mul [comm_semiring α]
  (A : matrix l m α) (B : matrix m n α) (A' : matrix l' m' α) (B' : matrix m' n' α) :
  (A ⬝ B) ⊗ₖ (A' ⬝ B') = (A ⊗ₖ A') ⬝ (B ⊗ₖ B') :=
kronecker_map_linear_mul_mul (algebra.lmul ℕ α).to_linear_map mul_mul_mul_comm A B A' B'

lemma kronecker_assoc [comm_semiring α] {q r : Type*} [fintype q] [fintype r]
  (A : matrix l m α) (B : matrix n p α) (C : matrix q r α) :
  reindex (equiv.prod_assoc l n q) (equiv.prod_assoc m p r) ((A ⊗ₖ B) ⊗ₖ C) = A ⊗ₖ (B ⊗ₖ C):=
kronecker_map_assoc _ _ _ _ A B C (equiv.cast rfl) mul_assoc

end kronecker

/-! ### Specialization to `matrix.kronecker_map (⊗ₜ)` -/

section kronecker_tmul

variables (R)
open tensor_product
open_locale matrix tensor_product

section module

variables [comm_semiring R] [add_comm_monoid α] [add_comm_monoid β] [module R α] [module R β]

/-- The Kronecker tensor product. This is just a shorthand for `kronecker_map (⊗ₜ)`.
Prefer the notation `⊗ₖₜ` rather than this definition. -/
@[simp] def kronecker_tmul :
  matrix l m α → matrix n p β → matrix (l × n) (m × p) (α ⊗[R] β) :=
kronecker_map (⊗ₜ)

localized "infix ` ⊗ₖₜ `:100 := matrix.kronecker_map (⊗ₜ)" in kronecker
localized
  "notation x ` ⊗ₖₜ[`:100 R `] `:0 y:100 := matrix.kronecker_map (tensor_product.tmul R) x y"
    in kronecker

@[simp]
lemma kronecker_tmul_apply (A : matrix l m α) (B : matrix n p β) (i₁ i₂ j₁ j₂) :
  (A ⊗ₖₜ B) (i₁, i₂) (j₁, j₂) = A i₁ j₁ ⊗ₜ[R] B i₂ j₂ := rfl

/-- `matrix.kronecker` as a bilinear map. -/
def kronecker_tmul_bilinear :
  matrix l m α →ₗ[R] matrix n p β →ₗ[R] matrix (l × n) (m × p) (α ⊗[R] β) :=
kronecker_map_linear (tensor_product.mk R α β)

/-! What follows is a copy, in order, of every `matrix.kronecker_map` lemma above that has
hypotheses which can be filled by properties of `⊗ₜ`. -/

@[simp] lemma zero_kronecker_tmul (B : matrix n p β) : (0 : matrix l m α) ⊗ₖₜ[R] B = 0 :=
kronecker_map_zero_left _ (zero_tmul α) B

@[simp] lemma kronecker_tmul_zero (A : matrix l m α) : A ⊗ₖₜ[R] (0 : matrix n p β) = 0 :=
kronecker_map_zero_right _ (tmul_zero β) A

lemma add_kronecker_tmul (A₁ A₂ : matrix l m α) (B : matrix n p α) :
  (A₁ + A₂) ⊗ₖₜ[R] B = A₁ ⊗ₖₜ B + A₂ ⊗ₖₜ B :=
kronecker_map_add_left _ add_tmul _ _ _

lemma kronecker_tmul_add (A : matrix l m α) (B₁ B₂ : matrix n p α) :
  A ⊗ₖₜ[R] (B₁ + B₂) = A ⊗ₖₜ B₁ + A ⊗ₖₜ B₂ :=
kronecker_map_add_right _ tmul_add _ _ _

lemma smul_kronecker_tmul
  (r : R) (A : matrix l m α) (B : matrix n p α) :
  (r • A) ⊗ₖₜ[R] B = r • (A ⊗ₖₜ B) :=
kronecker_map_smul_left _ _ (λ _ _, smul_tmul' _ _ _) _ _

lemma kronecker_tmul_smul
  (r : R) (A : matrix l m α) (B : matrix n p α) :
  A ⊗ₖₜ[R] (r • B) = r • (A ⊗ₖₜ B) :=
kronecker_map_smul_right _ _ (λ _ _, tmul_smul _ _ _) _ _

lemma diagonal_kronecker_tmul_diagonal
  [decidable_eq m] [decidable_eq n]
  (a : m → α) (b : n → α):
  (diagonal a) ⊗ₖₜ[R] (diagonal b) = diagonal (λ mn, a mn.1 ⊗ₜ b mn.2) :=
kronecker_map_diagonal_diagonal _ (zero_tmul _) (tmul_zero _) _ _

end module

section algebra
variables [comm_semiring R] [semiring α] [semiring β] [algebra R α] [algebra R β]

open_locale kronecker
open algebra.tensor_product

@[simp] lemma one_kronecker_tmul_one [decidable_eq m] [decidable_eq n] :
  (1 : matrix m m α) ⊗ₖₜ[R] (1 : matrix n n α) = 1 :=
kronecker_map_one_one _ (zero_tmul _) (tmul_zero _) rfl

lemma mul_kronecker_tmul_mul
  (A : matrix l m α) (B : matrix m n α) (A' : matrix l' m' β) (B' : matrix m' n' β) :
  (A ⬝ B) ⊗ₖₜ[R] (A' ⬝ B') = (A ⊗ₖₜ A') ⬝ (B ⊗ₖₜ B') :=
kronecker_map_linear_mul_mul (tensor_product.mk R α β) tmul_mul_tmul A B A' B'

end algebra

-- insert lemmas specific to `kronecker_tmul` below this line

end kronecker_tmul

end matrix
