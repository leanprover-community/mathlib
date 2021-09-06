/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Lu-Ming Zhang
-/
import combinatorics.simple_graph.basic
import data.rel
import linear_algebra.matrix.trace
import linear_algebra.matrix.symmetric

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `matrix.is_adj_matrix`: `A : matrix V V α` is qualified as an "adjacency matrix" if
  (1) every entry of `A` is `0` or `1`,
  (2) `A` is symmetric,
  (3) every diagonal entry of `A` is `0`.

* `matrix.is_adj_matrix.to_graph`: for `A : matrix V V α` and `h : A.is_adj_matrix`,
  `h.to_graph` is the simple graph induced by `A`.

* `matrix.compl`: for `A : matrix V V α`, `A.compl` is supposed to be
  the adjacency matrix of the complement graph of the graph induced by `A`.

* `simple_graph.adj_matrix`: the adjacency matrix of a `simple_graph`.

-/

open_locale big_operators matrix
open finset matrix simple_graph

variables {V α β : Type*}

namespace matrix

/-- `A : matrix V V α` is qualified as an "adjacency matrix" if
    (1) every entry of `A` is `0` or `1`,
    (2) `A` is symmetric,
    (3) every diagonal entry of `A` is `0`. -/
structure is_adj_matrix [has_zero α] [has_one α] (A : matrix V V α) : Prop :=
(zero_or_one : ∀ i j, (A i j) = 0 ∨ (A i j) = 1 . obviously)
(symm : A.is_symm . obviously)
(loopless : ∀ i, A i i = 0 . obviously)

namespace is_adj_matrix

variables {A : matrix V V α}

lemma apply_diag [has_zero α] [has_one α] (h : is_adj_matrix A) (i : V) :
  A i i = 0 :=
by simp [h.loopless]

@[simp]
lemma apply_diag_ne [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) (i : V) :
  ¬ A i i = 1 :=
by simp [h.apply_diag i]

@[simp]
lemma apply_ne_one_iff [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) (i j : V) :
  ¬ A i j = 1 ↔ A i j = 0 :=
begin
  replace h := h.zero_or_one i j,
  split,
  { tauto },
  { rintros g, simp [g] }
end

@[simp]
lemma apply_ne_zero_iff [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) (i j : V) :
  ¬ A i j = 0 ↔ A i j = 1 :=
by { rw [←apply_ne_one_iff h], simp }

/-- For `A : matrix V V α` and `h : is_adj_matrix A`,
    `h.to_graph` is the simple graph whose adjacency matrix is `A`. -/
def to_graph [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) :
  simple_graph V :=
{ adj := λ i j, A i j = 1,
  sym := λ i j hij, by simp only [h.symm.apply i j]; convert hij,
  loopless := λ i, by simp [h] }

instance [mul_zero_one_class α] [nontrivial α] [decidable_eq α] (h : is_adj_matrix A) :
  decidable_rel h.to_graph.adj :=
by {simp [to_graph], apply_instance}

end is_adj_matrix

/-- For `A : matrix V V α`, `A.compl` is supposed to be the adjacency matrix of
    the complement graph of the graph induced by `A.adj_matrix`. -/
def compl [has_zero α] [has_one α] [decidable_eq α] [decidable_eq V] (A : matrix V V α) :
  matrix V V α :=
λ i j, ite (i = j) 0 (ite (A i j = 0) 1 0)

section compl

variables [decidable_eq α] [decidable_eq V] (A : matrix V V α)

@[simp]
lemma compl_apply_diag [has_zero α] [has_one α] (i : V) :
  A.compl i i = 0 :=
by simp [compl]

@[simp]
lemma compl_apply [has_zero α] [has_one α] (i j : V) :
  A.compl i j = 0 ∨ A.compl i j = 1 :=
begin
  unfold compl,
  by_cases h : i = j, {simp [h]},
  by_cases g : A i j = 0; simp [h , g]
end

@[simp]
lemma is_symm_compl [has_zero α] [has_one α] (h : A.is_symm) :
  A.compl.is_symm :=
begin
  ext,
  unfold compl,
  congr' 1, {tidy},
  congr' 1,
  apply propext,
  rw [h.apply i j]
end

@[simp]
lemma is_adj_matrix_compl [has_zero α] [has_one α] (h : A.is_symm) :
  is_adj_matrix A.compl :=
{ symm := by simp [h] }

namespace is_adj_matrix

variable {A}

@[simp]
lemma compl [has_zero α] [has_one α] (h : is_adj_matrix A) :
  is_adj_matrix A.compl :=
is_adj_matrix_compl A h.symm

lemma compl_to_graph_eq [mul_zero_one_class α] [nontrivial α] (h : is_adj_matrix A) :
  h.compl.to_graph = (h.to_graph)ᶜ :=
begin
  ext v w,
  dsimp [simple_graph.has_compl, to_graph],
  simp only [and_true, if_false_right_eq_and, matrix.compl],
  split,
  { intros h₁,
    by_cases h₂ : v = w,
    { simp * at * },
    refine ⟨h₂, _⟩,
    intros g,
    rw [← apply_ne_zero_iff h] at g,
    simp * at *  },
  { rintros ⟨h₁, h₂⟩,
    rw [apply_ne_one_iff h] at h₂,
    simp [h₁, h₂] }
end

end is_adj_matrix

end compl

end matrix

open matrix

namespace simple_graph

variables (G : simple_graph V) [decidable_rel G.adj]
variables (α)

/-- `adj_matrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adj_matrix [has_zero α] [has_one α] : matrix V V α
| i j := if (G.adj i j) then 1 else 0

variable {α}

@[simp]
lemma adj_matrix_apply (v w : V) [has_zero α] [has_one α] :
  G.adj_matrix α v w = if (G.adj v w) then 1 else 0 := rfl

@[simp]
theorem transpose_adj_matrix [has_zero α] [has_one α] :
  (G.adj_matrix α)ᵀ = G.adj_matrix α :=
by { ext, simp [adj_comm] }

@[simp]
lemma is_symm_adj_matrix [has_zero α] [has_one α] :
  (G.adj_matrix α).is_symm :=
transpose_adj_matrix G

/-- The adjacency matrix of `G` is an adjacency matrix. -/
@[simp]
lemma is_adj_matrix_adj_matrix (α) [has_zero α] [has_one α] :
  (G.adj_matrix α).is_adj_matrix :=
{ zero_or_one := λ i j, by by_cases G.adj i j; simp [h] }

variables [fintype V]

@[simp]
lemma adj_matrix_dot_product [non_assoc_semiring α] (v : V) (vec : V → α) :
  dot_product (G.adj_matrix α v) vec = ∑ u in G.neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter]

@[simp]
lemma dot_product_adj_matrix [non_assoc_semiring α] (v : V) (vec : V → α) :
  dot_product vec (G.adj_matrix α v) = ∑ u in G.neighbor_finset v, vec u :=
by simp [neighbor_finset_eq_filter, dot_product, sum_filter, finset.sum_apply]

@[simp]
lemma adj_matrix_mul_vec_apply [non_assoc_semiring α] (v : V) (vec : V → α) :
  ((G.adj_matrix α).mul_vec vec) v = ∑ u in G.neighbor_finset v, vec u :=
by rw [mul_vec, adj_matrix_dot_product]

@[simp]
lemma adj_matrix_vec_mul_apply [non_assoc_semiring α] (v : V) (vec : V → α) :
  ((G.adj_matrix α).vec_mul vec) v = ∑ u in G.neighbor_finset v, vec u :=
begin
  rw [← dot_product_adj_matrix, vec_mul],
  refine congr rfl _, ext,
  rw [← transpose_apply (adj_matrix α G) x v, transpose_adj_matrix],
end

@[simp]
lemma adj_matrix_mul_apply [non_assoc_semiring α] (M : matrix V V α) (v w : V) :
  (G.adj_matrix α ⬝ M) v w = ∑ u in G.neighbor_finset v, M u w :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter]

@[simp]
lemma mul_adj_matrix_apply [non_assoc_semiring α] (M : matrix V V α) (v w : V) :
  (M ⬝ G.adj_matrix α) v w = ∑ u in G.neighbor_finset w, M v u :=
by simp [mul_apply, neighbor_finset_eq_filter, sum_filter, adj_comm]

variable (α)

theorem trace_adj_matrix [non_assoc_semiring α] [semiring β] [module β α]:
  matrix.trace _ β _ (G.adj_matrix α) = 0 :=
by simp

variable {α}

theorem adj_matrix_mul_self_apply_self [non_assoc_semiring α] (i : V) :
  ((G.adj_matrix α) ⬝ (G.adj_matrix α)) i i = degree G i :=
by simp [degree]

variable {G}

@[simp]
lemma adj_matrix_mul_vec_const_apply [semiring α] {a : α} {v : V} :
  (G.adj_matrix α).mul_vec (function.const _ a) v = G.degree v * a :=
by simp [degree]

lemma adj_matrix_mul_vec_const_apply_of_regular
[semiring α] {d : ℕ} {a : α} (hd : G.is_regular_of_degree d)
  {v : V} :
  (G.adj_matrix α).mul_vec (function.const _ a) v = (d * a) :=
by simp [hd v]

end simple_graph
