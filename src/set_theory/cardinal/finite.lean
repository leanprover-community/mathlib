/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.fintype.card
import set_theory.cardinal.basic

/-!
# Finite Cardinality Functions

## Main Definitions

* `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`.
* `part_enat.card α` is the cardinality of `α` as an extended natural number
  (`part ℕ` implementation). If `α` is infinite, `part_enat.card α = ⊤`.
-/

open cardinal
noncomputable theory

variables {α β : Type*}

namespace nat

/-- `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`. -/
protected def card (α : Type*) : ℕ := (mk α).to_nat

@[simp]
lemma card_eq_fintype_card [fintype α] : nat.card α = fintype.card α := mk_to_nat_eq_card

@[simp]
lemma card_eq_zero_of_infinite [infinite α] : nat.card α = 0 := mk_to_nat_of_infinite

lemma card_congr (f : α ≃ β) : nat.card α = nat.card β :=
cardinal.to_nat_congr f

lemma card_eq_of_bijective (f : α → β) (hf : function.bijective f) : nat.card α = nat.card β :=
card_congr (equiv.of_bijective f hf)

lemma card_eq_of_equiv_fin {α : Type*} {n : ℕ}
  (f : α ≃ fin n) : nat.card α = n :=
by simpa using card_congr f

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `fin (nat.card α)`. See also `finite.equiv_fin`. -/
def equiv_fin_of_card_pos {α : Type*} (h : nat.card α ≠ 0) :
  α ≃ fin (nat.card α) :=
begin
  casesI fintype_or_infinite α,
  { simpa using fintype.equiv_fin α },
  { simpa using h },
end

lemma card_of_subsingleton (a : α) [subsingleton α] : nat.card α = 1 :=
begin
  letI := fintype.of_subsingleton a,
  rw [card_eq_fintype_card, fintype.card_of_subsingleton a]
end

@[simp] lemma card_unique [unique α] : nat.card α = 1 :=
card_of_subsingleton default

lemma card_eq_one_iff_unique : nat.card α = 1 ↔ subsingleton α ∧ nonempty α :=
cardinal.to_nat_eq_one_iff_unique

theorem card_of_is_empty [is_empty α] : nat.card α = 0 := by simp

@[simp] lemma card_prod (α β : Type*) : nat.card (α × β) = nat.card α * nat.card β :=
by simp only [nat.card, mk_prod, to_nat_mul, to_nat_lift]

@[simp] lemma card_ulift (α : Type*) : nat.card (ulift α) = nat.card α :=
card_congr equiv.ulift

@[simp] lemma card_plift (α : Type*) : nat.card (plift α) = nat.card α :=
card_congr equiv.plift

open_locale big_operators

/-- `cardinal.to_nat` as a `monoid_with_zero_hom`. -/
def to_nat_hom : cardinal →*₀ ℕ :=
{ to_fun := to_nat,
  map_zero' := zero_to_nat,
  map_one' := one_to_nat,
  map_mul' := to_nat_mul }

lemma to_nat_finset_prod (s : finset α) (f : α → cardinal) :
  to_nat (∏ i in s, f i) = ∏ i in s, to_nat (f i) :=
map_prod to_nat_hom _ _

lemma {u v} prod_of_fintype_eq {α : Type u} [fintype α] (f : α → cardinal.{v}) :
  prod f = cardinal.lift.{u} ∏ (i : α), (f i) :=
begin
  revert f,
  refine fintype.induction_empty_option _ _ _ α,
  { intros α β hβ e h f,
    letI := hβ,
    letI := fintype.of_equiv β e.symm,
    rw [←e.prod_comp f, ←h],
    exact mk_congr (e.Pi_congr_left _).symm },
  { intro f,
    rw [fintype.univ_pempty, finset.prod_empty, lift_one, cardinal.prod, mk_eq_one] },
  { intros α hα h f,
    rw [cardinal.prod, mk_congr equiv.pi_option_equiv_prod, mk_prod, lift_umax', mk_out,
        ←cardinal.prod, lift_prod, fintype.prod_option, lift_mul, ←h (λ a, f (some a))],
    simp only [lift_id] },
end

lemma card_pi {β : α → Type*} [fintype α] : nat.card (Π a, β a) = ∏ a, nat.card (β a) :=
by simp_rw [nat.card, mk_pi, prod_of_fintype_eq, to_nat_lift, to_nat_finset_prod]

end nat

namespace part_enat

/-- `part_enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `part_enat.card α = ⊤`. -/
def card (α : Type*) : part_enat := (mk α).to_part_enat

@[simp]
lemma card_eq_coe_fintype_card [fintype α] : card α = fintype.card α := mk_to_part_enat_eq_coe_card

@[simp]
lemma card_eq_top_of_infinite [infinite α] : card α = ⊤ := mk_to_part_enat_of_infinite

end part_enat
