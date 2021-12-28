/-
Copyright (c) 2021 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
import data.fintype.basic
import order.antichain

/-!
# `r`-sets and slice

This file defines the `r`-th slice of a set family and provides a way to say that a set family is
made of `r`-sets.

An `r`-set is a finset of cardinality `r` (aka of *size* `r`). The `r`-th slice of a set family is
the set family made of its `r`-sets.

## Main declarations

* `set.sized`: `A.sized r` means that `A` only contains `r`-sets.
* `finset.slice`: `A.slice r` is the set of `r`-sets in `A`.

## Notation

`A # r` is notation for `A.slice r` in locale `finset_family`.
-/

open finset nat

variables {α : Type*}

namespace set
variables {A B : set (finset α)} {r : ℕ}

/-! ### Families of `r`-sets -/

/-- `sized r A` means that every finset in `A` has size `r`. -/
def sized (r : ℕ) (A : set (finset α)) : Prop := ∀ ⦃x⦄, x ∈ A → card x = r

lemma sized.mono (h : A ⊆ B) (hB : B.sized r) : A.sized r := λ x hx, hB $ h hx

lemma sized_union : (A ∪ B).sized r ↔ A.sized r ∧ B.sized r :=
⟨λ hA, ⟨hA.mono $ subset_union_left _ _, hA.mono $ subset_union_right _ _⟩,
  λ hA x hx, hx.elim (λ h, hA.1 h) $ λ h, hA.2 h⟩

alias sized_union ↔ _ set.sized.union

protected lemma sized.is_antichain (hA : A.sized r) : is_antichain (⊆) A :=
λ s hs t ht h hst, h $ eq_of_subset_of_card_le hst ((hA ht).trans (hA hs).symm).le

end set

namespace finset
section sized
variables [fintype α] {𝒜 : finset (finset α)} {s : finset α} {r : ℕ}

lemma subset_powerset_len_univ_iff : 𝒜 ⊆ powerset_len r univ ↔ (𝒜 : set (finset α)).sized r :=
forall_congr $ λ A, by rw [mem_powerset_len_univ_iff, mem_coe]

alias subset_powerset_len_univ_iff  ↔ _ set.sized.subset_powerset_len_univ

lemma _root_.set.sized.card_le (h𝒜 : (𝒜 : set (finset α)).sized r) :
  card 𝒜 ≤ (fintype.card α).choose r :=
begin
  rw [fintype.card, ←card_powerset_len],
  exact card_le_of_subset h𝒜.subset_powerset_len_univ,
end

end sized

/-! ### Slices -/

section slice
variables {𝒜 : finset (finset α)} {A A₁ A₂ : finset α} {r r₁ r₂ : ℕ}

/-- The `r`-th slice of a set family is the subset of its elements which have cardinality `r`. -/
def slice (𝒜 : finset (finset α)) (r : ℕ) : finset (finset α) := 𝒜.filter (λ i, i.card = r)

localized "infix ` # `:90 := finset.slice" in finset_family

/-- `A` is in the `r`-th slice of `𝒜` iff it's in `𝒜` and has cardinality `r`. -/
lemma mem_slice : A ∈ 𝒜 # r ↔ A ∈ 𝒜 ∧ A.card = r := mem_filter

/-- The `r`-th slice of `𝒜` is a subset of `𝒜`. -/
lemma slice_subset : 𝒜 # r ⊆ 𝒜 := filter_subset _ _

/-- Everything in the `r`-th slice of `𝒜` has size `r`. -/
lemma sized_slice : (𝒜 # r : set (finset α)).sized r := λ _, and.right ∘ mem_slice.mp

lemma eq_of_mem_slice (h₁ : A ∈ 𝒜 # r₁) (h₂ : A ∈ 𝒜 # r₂) : r₁ = r₂ :=
(sized_slice h₁).symm.trans $ sized_slice h₂

/-- Elements in distinct slices must be distinct. -/
lemma ne_of_mem_slice (h₁ : A₁ ∈ 𝒜 # r₁) (h₂ : A₂ ∈ 𝒜 # r₂) : r₁ ≠ r₂ → A₁ ≠ A₂ :=
mt $ λ h, (sized_slice h₁).symm.trans ((congr_arg card h).trans (sized_slice h₂))

variables [decidable_eq α]

lemma pairwise_disjoint_slice : (set.univ : set ℕ).pairwise_disjoint (slice 𝒜) :=
λ m _ n _ hmn, disjoint_filter.2 $ λ s hs hm hn, hmn $ hm.symm.trans hn

end slice
end finset
