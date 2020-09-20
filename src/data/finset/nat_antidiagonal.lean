/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.finset.basic
import data.multiset.nat_antidiagonal

/-!
# The "antidiagonal" {(0,n), (1,n-1), ..., (n,0)} as a finset.
-/

namespace finset

namespace nat

/-- The antidiagonal of a natural number `n` is
    the finset of pairs `(i,j)` such that `i+j = n`. -/
def antidiagonal (n : ℕ) : finset (ℕ × ℕ) :=
⟨multiset.nat.antidiagonal n, multiset.nat.nodup_antidiagonal n⟩

/-- A pair (i,j) is contained in the antidiagonal of `n` if and only if `i+j=n`. -/
@[simp] lemma mem_antidiagonal {n : ℕ} {x : ℕ × ℕ} :
  x ∈ antidiagonal n ↔ x.1 + x.2 = n :=
by rw [antidiagonal, finset.mem_def, multiset.nat.mem_antidiagonal]

/-- The cardinality of the antidiagonal of `n` is `n+1`. -/
@[simp] lemma card_antidiagonal (n : ℕ) : (antidiagonal n).card = n+1 :=
by simp [antidiagonal]

/-- The antidiagonal of `0` is the list `[(0,0)]` -/
@[simp] lemma antidiagonal_zero : antidiagonal 0 = {(0, 0)} :=
rfl

lemma antidiagonal_succ {n : ℕ} :
  finset.nat.antidiagonal (n + 1) = insert (0,n + 1) ((finset.nat.antidiagonal n).map ⟨prod.map nat.succ id, function.injective.prod_map nat.succ_injective function.injective_id⟩ ) :=
begin
  apply finset.eq_of_veq,
  rw [finset.insert_val_of_not_mem, finset.map_val],
  {apply multiset.nat.antidiagonal_succ},
  { intro con, rcases finset.mem_map.1 con with ⟨⟨a,b⟩, ⟨h1, h2⟩⟩,
    simp only [id.def, prod.mk.inj_iff, function.embedding.coe_fn_mk, prod.map_mk] at h2,
    apply nat.succ_ne_zero a h2.1, }
end

lemma sum_antidiagonal_succ {α : Type*} [add_comm_monoid α] {n : ℕ} {f : ℕ × ℕ → α} :
  (finset.nat.antidiagonal (n + 1)).sum f = f (0, n + 1) + ((finset.nat.antidiagonal n).map ⟨prod.map nat.succ id, function.injective.prod_map nat.succ_injective function.injective_id⟩).sum f :=
begin
  rw [finset.nat.antidiagonal_succ, finset.sum_insert],
  intro con, rcases finset.mem_map.1 con with ⟨⟨a,b⟩, ⟨h1, h2⟩⟩,
  simp only [id.def, prod.mk.inj_iff, function.embedding.coe_fn_mk, prod.map_mk] at h2,
  apply nat.succ_ne_zero a h2.1,
end

lemma map_swap_antidiagonal {n : ℕ} :
  (finset.nat.antidiagonal n).map ⟨prod.swap, prod.swap_right_inverse.injective⟩ = finset.nat.antidiagonal n :=
begin
  ext,
  simp only [exists_prop, finset.mem_map, finset.nat.mem_antidiagonal, function.embedding.coe_fn_mk, prod.swap_prod_mk,
 prod.exists],
  rw add_comm,
  split,
  { rintro ⟨b, c, ⟨rfl, rfl⟩⟩,
    simp },
  { rintro rfl,
    use a.snd,
    use a.fst,
    simp }
end

end nat

end finset
