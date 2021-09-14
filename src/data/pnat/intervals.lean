/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yaël Dillies
-/
import data.pnat.basic
import order.locally_finite

/-!
# Intervals of positive naturals

This file proves that `ℕ+` is a `locally_finite_order` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

open finset pnat

instance : locally_finite_order ℕ+ :=
{ finset_Icc := λ a b, (list.range' a (b + 1 - a)).to_finset,
  finset_mem_Icc := λ a b x, begin
    rw [list.mem_to_finset, list.mem_range'],
    cases le_or_lt a b,
    { rw [nat.add_sub_cancel' (nat.lt_succ_of_le h).le, nat.lt_succ_iff] },
    { rw [nat.sub_eq_zero_iff_le.2 h, add_zero],
      exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2)) }
end }

namespace pnat
variables (a b : ℕ+)

/-- `Ico a b` is the set of positive natural numbers `b ≤ k < a`. -/
def pnat_Ico (a b : ℕ+) : finset ℕ+ :=
(finset.Ico a b).attach.map
  { to_fun := λ n, ⟨(n : ℕ), lt_of_lt_of_le a.2 (finset.Ico.mem.1 n.2).1⟩,
    -- why can't we do this directly?
    inj' := λ n m h, subtype.eq (by { replace h := congr_arg subtype.val h, exact h }) }

@[simp] lemma pnat_Ico.mem : ∀ {n m l : ℕ+}, l ∈ pnat_Ico n m ↔ n ≤ l ∧ l < m :=
by { rintro ⟨n, hn⟩ ⟨m, hm⟩ ⟨l, hl⟩, simp [pnat_Ico] }

@[simp] lemma card_finset_Icc : (Icc a b).card = b + 1 - a := sorry

@[simp] lemma card_finset_Ico : (Ico a b).card = b - a := sorry

@[simp] lemma card_finset_Ioc : (Ioc a b).card = b - a := sorry

@[simp] lemma card_finset_Ioo : (Ioo a b).card = b - a - 1 := sorry

@[simp] lemma card_fintype_Icc : fintype.card (set.Icc a b) = b + 1 - a :=
by rw [←card_finset_Icc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ico : fintype.card (set.Ico a b) = b - a :=
by rw [←card_finset_Ico, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioc : fintype.card (set.Ioc a b) = b - a :=
by rw [←card_finset_Ioc, fintype.card_of_finset]

@[simp] lemma card_fintype_Ioo : fintype.card (set.Ioo a b) = b - a - 1 :=
by rw [←card_finset_Ioo, fintype.card_of_finset]

end pnat
