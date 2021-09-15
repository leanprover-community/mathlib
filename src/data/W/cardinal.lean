/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import set_theory.cardinal_ordinal
import data.W.basic
/-!
# Cardinality of W-types

This file proves some theorems about the cardinality of W-types. The main result is
`cardinal_mk_le_max_omega_of_fintype` which says that if for any `a : α`,
`β a` is finite, then the cardinality of `W_type β` is at most the maximum of the
cardinality of `α` or `cardinal.omega`.
This has applications in first order logic, and can be used to prove that in the
cardinality of the set of terms in a language with is bound by the cardinality
of the set of function and constant symbols if that set is infinite, and the set of terms is
countable if there are finitely many constant and function symbols.

## Tags

W, W type, cardinal, first order
-/
universe u

variables {α : Type u} {β : α → Type u}

noncomputable theory

open cardinal

namespace W_type

lemma cardinal_mk_eq_sum : cardinal.mk (W_type β) =
  cardinal.sum (λ a : α, cardinal.mk (W_type β) ^ cardinal.mk (β a)) :=
begin
  simp only [cardinal.lift_mk, cardinal.power_def, cardinal.sum_mk],
  exact cardinal.eq.2 ⟨equiv_sigma β⟩
end

lemma cardinal_mk_le_of_le {κ : cardinal.{u}}
  (hκ : cardinal.sum (λ a : α, κ ^ cardinal.mk (β a)) ≤ κ) :
  cardinal.mk (W_type β) ≤ κ :=
begin
  conv_rhs { rw ← cardinal.mk_out κ},
  rw [← cardinal.mk_out κ] at hκ,
  simp only [cardinal.power_def, cardinal.sum_mk, cardinal.le_def] at hκ,
  cases hκ,
  exact cardinal.mk_le_of_injective (to_type_injective _ hκ.1 hκ.2)
end

/-- If, for any `a : α`, `β a` is finite, then the cardinality of `W_type β`
  is at most the maximum of the cardinality of `α` and `omega`  -/
lemma cardinal_mk_le_max_omega_of_fintype [Π a, fintype (β a)] : cardinal.mk (W_type β) ≤
  max (cardinal.mk α) omega :=
(is_empty_or_nonempty α).elim
  (begin
    introI h,
    rw [@cardinal.eq_zero_of_is_empty (W_type β)],
    exact zero_le _
  end) $
λ hn,
let m := max (cardinal.mk α) omega in
cardinal_mk_le_of_le $
calc cardinal.sum (λ a : α, m ^ cardinal.mk.{u} (β a))
    ≤ cardinal.mk α * cardinal.sup.{u u}
      (λ a : α, m ^ cardinal.mk.{u} (β a)) :
  cardinal.sum_le_sup _
... ≤ m * cardinal.sup.{u u}
      (λ a : α, m ^ cardinal.mk.{u} (β a)) :
  mul_le_mul' (le_max_left _ _) (le_refl _)
... = m : mul_eq_left.{u} (le_max_right _ _)
  (cardinal.sup_le.2 (λ i, begin
    cases lt_omega.1 (lt_omega_iff_fintype.2 ⟨show fintype (β i), by apply_instance⟩) with n hn,
    rw [hn],
    exact power_nat_le (le_max_right _ _)
  end))
  (pos_iff_ne_zero.1 (succ_le.1
    begin
      rw [succ_zero],
      obtain ⟨a⟩ : nonempty α, from hn,
      refine le_trans _ (le_sup _ a),
      rw [← @power_zero m],
      exact power_le_power_left (pos_iff_ne_zero.1
        (lt_of_lt_of_le omega_pos (le_max_right _ _))) (zero_le _)
    end))


end W_type
