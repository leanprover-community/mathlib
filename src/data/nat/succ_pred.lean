/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.succ_pred.basic

/-!
# Successors and predecessors of naturals

In this file, we show that `ℕ` is both an archimedean `succ_order` and an archimedean `pred_order`.
-/

open function nat

@[reducible] -- so that Lean reads `nat.succ` through `succ_order.succ`
instance : succ_order ℕ :=
{ succ := succ,
  ..succ_order.of_succ_le_iff succ (λ a b, iff.rfl) }

@[reducible] -- so that Lean reads `nat.pred` through `pred_order.pred`
instance : pred_order ℕ :=
{ pred := pred,
  pred_le := pred_le,
  minimal_of_le_pred := λ a ha b h, begin
    cases a,
    { exact b.not_lt_zero h },
    { exact nat.lt_irrefl a ha }
  end,
  le_pred_of_lt := λ a b h, begin
    cases b,
    { exact (a.not_lt_zero h).elim },
    { exact le_of_succ_le_succ h }
  end,
  le_of_pred_lt := λ a b h, begin
    cases a,
    { exact b.zero_le },
    { exact h }
  end }

lemma nat.succ_iterate (a : ℕ) : ∀ n, succ^[n] a = a + n
| 0       := rfl
| (n + 1) := by { rw [function.iterate_succ', add_succ], exact congr_arg _ n.succ_iterate }

lemma nat.pred_iterate (a : ℕ) : ∀ n, pred^[n] a = a - n
| 0       := rfl
| (n + 1) := by { rw [function.iterate_succ', sub_succ], exact congr_arg _ n.pred_iterate }

instance : is_succ_archimedean ℕ :=
⟨λ a b h, ⟨b - a, by rw [nat.succ_iterate, add_tsub_cancel_of_le h]⟩⟩

instance : is_pred_archimedean ℕ :=
⟨λ a b h, ⟨b - a, by rw [nat.pred_iterate, tsub_tsub_cancel_of_le h]⟩⟩

/-! ### Covering relation -/

protected lemma nat.cov_by_iff_succ_eq {m n : ℕ} : m ⋖ n ↔ m + 1 = n := cov_by_iff_succ_eq

@[simp] lemma fin.coe_cov_by_iff {n : ℕ} (a b : fin n) : (a : ℕ) ⋖ b ↔ a ⋖ b :=
and_congr_right' ⟨λ h c hc, h hc, λ h c ha hb, @h ⟨c, hb.trans b.prop⟩ ha hb⟩
