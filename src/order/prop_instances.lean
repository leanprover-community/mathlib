/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.disjoint
import order.with_bot

/-!

# The order on `Prop`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/792
> Any changes to this file require a corresponding PR to mathlib4.

Instances on `Prop` such as `distrib_lattice`, `bounded_order`, `linear_order`.

-/

instance Prop.le_is_total : is_total Prop (≤) :=
⟨λ p q, by { change (p → q) ∨ (q → p), tauto! }⟩

noncomputable instance Prop.linear_order : linear_order Prop :=
by classical; exact lattice.to_linear_order Prop

@[simp] lemma sup_Prop_eq : (⊔) = (∨) := rfl
@[simp] lemma inf_Prop_eq : (⊓) = (∧) := rfl

namespace pi

variables {ι : Type*} {α' : ι → Type*} [Π i, partial_order (α' i)]

lemma disjoint_iff [Π i, order_bot (α' i)] {f g : Π i, α' i} :
  disjoint f g ↔ ∀ i, disjoint (f i) (g i) :=
begin
  split,
  { intros h i x hf hg,
    refine (update_le_iff.mp $
    -- this line doesn't work
      h (update_le_iff.mpr ⟨hf, λ _ _, _⟩) (update_le_iff.mpr ⟨hg, λ _ _, _⟩)).1,
    { exact ⊥},
    { exact bot_le },
    { exact bot_le }, },
  { intros h x hf hg i,
    apply h i (hf i) (hg i) },
end

lemma codisjoint_iff [Π i, order_top (α' i)] {f g : Π i, α' i} :
  codisjoint f g ↔ ∀ i, codisjoint (f i) (g i) :=
@disjoint_iff _ (λ i, (α' i)ᵒᵈ) _ _ _ _

lemma is_compl_iff [Π i, bounded_order (α' i)] {f g : Π i, α' i} :
  is_compl f g ↔ ∀ i, is_compl (f i) (g i) :=
by simp_rw [is_compl_iff, disjoint_iff, codisjoint_iff, forall_and_distrib]

end pi

@[simp] lemma Prop.disjoint_iff {P Q : Prop} : disjoint P Q ↔ ¬(P ∧ Q) := disjoint_iff_inf_le
@[simp] lemma Prop.codisjoint_iff {P Q : Prop} : codisjoint P Q ↔ P ∨ Q :=
codisjoint_iff_le_sup.trans $ forall_const _
@[simp] lemma Prop.is_compl_iff {P Q : Prop} : is_compl P Q ↔ ¬(P ↔ Q) :=
begin
  rw [is_compl_iff, Prop.disjoint_iff, Prop.codisjoint_iff, not_iff],
  tauto,
end
