/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
<<<<<<< HEAD
Authors: Mario Carneiro, Yaël Dillies, Bhavik Mehta
-/
import data.finset.card
=======
Authors: Mario Carneiro
-/
import data.finset.lattice
>>>>>>> origin/master

/-!
# Finite sets in a sigma type

<<<<<<< HEAD
This file defines a few `finset` constructions on `Σ i, α i`.
=======
This file defines a `finset` construction on `Σ i, α i`.
>>>>>>> origin/master

## Main declarations

* `finset.sigma`: Given a finset `s` in `ι` and finsets `t i` in each `α i`, `s.sigma t` is the
  finset of the dependent sum `Σ i, α i`
<<<<<<< HEAD
* `finset.sigma_lift`: Lifts maps `α i → β i → finset (γ i)` to a map
  `Σ i, α i → Σ i, β i → finset (Σ i, γ i)`.
=======
>>>>>>> origin/master
-/

open function multiset

<<<<<<< HEAD
variables {ι : Type*} {α β γ : ι → Type*}

namespace finset
section sigma
variables (s s₁ s₂ : finset ι) (t t₁ t₂ : Π i, finset (α i))
=======
namespace finset
variables {ι β : Type*} {α : ι → Type*} (s s₁ s₂ : finset ι) (t t₁ t₂ : Π i, finset (α i))
>>>>>>> origin/master

/-- `s.sigma t` is the finset of dependent pairs `⟨i, a⟩` such that `i ∈ s` and `a ∈ t i`. -/
protected def sigma : finset (Σ i, α i) := ⟨_, nodup_sigma s.2 (λ i, (t i).2)⟩

variables {s s₁ s₂ t t₁ t₂}

<<<<<<< HEAD
@[simp] lemma mem_sigma {p : sigma α} : p ∈ s.sigma t ↔ p.1 ∈ s ∧ p.2 ∈ t (p.1) := mem_sigma

@[simp] lemma sigma_nonempty : (s.sigma t).nonempty ↔ ∃ x ∈ s, (t x).nonempty :=
by simp [finset.nonempty]

@[simp] lemma sigma_eq_empty : s.sigma t = ∅ ↔ ∀ x ∈ s, t x = ∅ :=
by simp only [← not_nonempty_iff_eq_empty, sigma_nonempty, not_exists]

@[mono] lemma sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ a, t₁ a ⊆ t₂ a) : s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
λ ⟨i, a⟩ h, let ⟨hi, ha⟩ := mem_sigma.1 h in mem_sigma.2 ⟨hs hi, ht i ha⟩

lemma sigma_eq_bUnion [decidable_eq (Σ a, α a)] (s : finset ι) (t : Π i, finset (α i)) :
  s.sigma t = s.bUnion (λ i, (t i).map $ embedding.sigma_mk i) :=
by { ext ⟨x, y⟩, simp [and.left_comm] }

end sigma

section sigma_lift
variables [decidable_eq ι]

/-- Lifts maps `α i → β i → finset (γ i)` to a map `Σ i, α i → Σ i, β i → finset (Σ i, γ i)`. -/
def sigma_lift (f : Π ⦃i⦄, α i → β i → finset (γ i)) (a : sigma α) (b : sigma β) :
  finset (sigma γ) :=
dite (a.1 = b.1) (λ h, (f (h.rec a.2) b.2).map $ embedding.sigma_mk _) (λ _, ∅)

lemma mem_sigma_lift (f : Π ⦃i⦄, α i → β i → finset (γ i))
  (a : sigma α) (b : sigma β) (x : sigma γ) :
  x ∈ sigma_lift f a b ↔ ∃ (ha : a.1 = x.1) (hb : b.1 = x.1), x.2 ∈ f (ha.rec a.2) (hb.rec b.2) :=
begin
  obtain ⟨⟨i, a⟩, j, b⟩ := ⟨a, b⟩,
  obtain rfl | h := decidable.eq_or_ne i j,
  { split,
    { simp_rw [sigma_lift, dif_pos rfl, mem_map, embedding.sigma_mk_apply],
      rintro ⟨x, hx, rfl⟩,
      exact ⟨rfl, rfl, hx⟩ },
    { rintro ⟨⟨⟩, ⟨⟩, hx⟩,
      rw [sigma_lift, dif_pos rfl, mem_map],
      exact ⟨_, hx, by simp [sigma.ext_iff]⟩ } },
  { rw [sigma_lift, dif_neg h],
    refine iff_of_false (not_mem_empty _) _,
    rintro ⟨⟨⟩, ⟨⟩, _⟩,
    exact h rfl }
end

variables {f g : Π ⦃i⦄, α i → β i → finset (γ i)} {a : Σ i, α i} {b : Σ i, β i}

lemma sigma_lift_nonempty :
  (sigma_lift f a b).nonempty ↔ ∃ h : a.1 = b.1, (f (h.rec a.2) b.2).nonempty :=
begin
  simp_rw nonempty_iff_ne_empty,
  convert dite_ne_right_iff,
  ext h,
  simp_rw ←nonempty_iff_ne_empty,
  exact map_nonempty.symm,
end

lemma sigma_lift_eq_empty : (sigma_lift f a b) = ∅ ↔ ∀ h : a.1 = b.1, (f (h.rec a.2) b.2) = ∅ :=
begin
  convert dite_eq_right_iff,
  exact forall_congr_eq (λ h, propext map_eq_empty.symm),
end

lemma sigma_lift_mono (h : ∀ ⦃i⦄ ⦃a : α i⦄ ⦃b : β i⦄, f a b ⊆ g a b) (a : Σ i, α i) (b : Σ i, β i) :
  sigma_lift f a b ⊆ sigma_lift g a b :=
begin
  rintro x hx,
  rw mem_sigma_lift at ⊢ hx,
  obtain ⟨ha, hb, hx⟩ := hx,
  exact ⟨ha, hb, h hx⟩,
end

variables (f a b)

lemma card_sigma_lift :
  (sigma_lift f a b).card = dite (a.1 = b.1) (λ h, (f (h.rec a.2) b.2).card) (λ _, 0) :=
by { convert apply_dite _ _ _ _, ext h, exact (card_map _).symm }

end sigma_lift
=======
@[simp] lemma mem_sigma {a : Σ i, α i} : a ∈ s.sigma t ↔ a.1 ∈ s ∧ a.2 ∈ t a.1 := mem_sigma

@[simp] lemma sigma_nonempty : (s.sigma t).nonempty ↔ ∃ i ∈ s, (t i).nonempty :=
by simp [finset.nonempty]

@[simp] lemma sigma_eq_empty : s.sigma t = ∅ ↔ ∀ i ∈ s, t i = ∅ :=
by simp only [← not_nonempty_iff_eq_empty, sigma_nonempty, not_exists]

@[mono] lemma sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
λ ⟨i, a⟩ h, let ⟨hi, ha⟩ := mem_sigma.1 h in mem_sigma.2 ⟨hs hi, ht i ha⟩

lemma sigma_eq_bUnion [decidable_eq (Σ i, α i)] (s : finset ι) (t : Π i, finset (α i)) :
  s.sigma t = s.bUnion (λ i, (t i).map $ embedding.sigma_mk i) :=
by { ext ⟨x, y⟩, simp [and.left_comm] }

variables (s t) (f : (Σ i, α i) → β)

lemma sup_sigma [semilattice_sup β] [order_bot β] :
  (s.sigma t).sup f = s.sup (λ i, (t i).sup $ λ b, f ⟨i, b⟩) :=
begin
  refine (sup_le _).antisymm (sup_le $ λ i hi, sup_le $ λ b hb, le_sup $ mem_sigma.2 ⟨hi, hb⟩),
  rintro ⟨i, b⟩ hb,
  rw mem_sigma at hb,
  refine le_trans _ (le_sup hb.1),
  convert le_sup hb.2,
end

lemma inf_sigma [semilattice_inf β] [order_top β] :
  (s.sigma t).inf f = s.inf (λ i, (t i).inf $ λ b, f ⟨i, b⟩) :=
@sup_sigma _ (order_dual β) _ _ _ _ _ _

>>>>>>> origin/master
end finset
