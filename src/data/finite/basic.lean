/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import set_theory.cardinal.finite

/-!
# Finite types

This module defines a finiteness predicate on types called `finite`.

The `fintype` class also represents finiteness of a type, but a key
difference is that a `fintype` instance represents finiteness in a
computable way: it provides an algorithm to produce a `finset` whose
elements enumerate the terms of the given type. A `finite` instance is
instead a mere proposition, and as such it gets to take advantage of
proof irrelevance.

One should prefer defining `finite` instances rather than noncomputable
`fintype` instances to preserve the property that `fintype` instances
can be used for computation.

The cardinality of a finite type `α` is given by `nat.card α`.

## Main definitions

* `finite α` denotes that `α` is a finite type.
* `finite.of_fintype` creates a `finite` from a `fintype.
* `fintype.of_finite` noncomputably creates a `fintype` from a `finite`.
* `finite_or_infinite` is that every type is either `finite` or `infinite`.

-/

noncomputable theory
open_locale classical

variables {α β γ : Type*}

/-- A type is `finite` if it is in bijective correspondence to some
`fin n`.

While this could be defined as `nonempty (fintype α)`, it is defined
in this way to allow there to be `finite` instances for propositions.
-/
class finite (α : Sort*) : Prop :=
(exists_equiv_fin [] : ∃ (n : ℕ), nonempty (α ≃ fin n))

lemma finite.of_fintype {α : Type*} (h : fintype α) : finite α :=
⟨⟨fintype.card α, ⟨fintype.equiv_fin α⟩⟩⟩

/-- For efficiency reasons, we want `finite` instances to have higher
priority than ones coming from `fintype` instances. -/
@[priority 900]
instance finite.of_fintype' (α : Type*) [fintype α] : finite α := finite.of_fintype ‹_›

/-- There is (noncomputably) an equivalence between a finite type `α` and `fin (nat.card α)`. -/
def finite.equiv_fin (α : Type*) [finite α] : α ≃ fin (nat.card α) :=
begin
  have := (finite.exists_equiv_fin α).some_spec.some,
  rwa nat.card_eq_of_equiv_fin this,
end

/-- Similar to `finite.equiv_fin` but with control over the term used for the cardinality. -/
def finite.equiv_fin_of_card_eq [finite α] {n : ℕ} (h : nat.card α = n) : α ≃ fin n :=
by { subst h, apply finite.equiv_fin }

/-- Noncomputably get a `fintype` instance from a `finite` instance. This is not an
instance because we want `fintype` instances to be useful for computations. -/
def fintype.of_finite (α : Type*) [finite α] : fintype α :=
fintype.of_equiv _ (finite.equiv_fin α).symm

lemma finite_iff_nonempty_fintype (α : Type*) :
  finite α ↔ nonempty (fintype α) :=
⟨λ _, by exactI ⟨fintype.of_finite α⟩, λ ⟨_⟩, by exactI infer_instance⟩

lemma finite_or_infinite (α : Type*) :
  finite α ∨ infinite α :=
begin
  casesI fintype_or_infinite α,
  { exact or.inl infer_instance },
  { exact or.inr infer_instance }
end

lemma not_finite (α : Type*) [h1 : infinite α] [h2 : finite α] : false :=
by { haveI := fintype.of_finite α, exact not_fintype α }

lemma finite.of_not_infinite {α : Type*} (h : ¬ infinite α) : finite α :=
finite.of_fintype (fintype_of_not_infinite h)

lemma finite.card_pos_iff [finite α] :
  0 < nat.card α ↔ nonempty α :=
begin
  haveI := fintype.of_finite α,
  simp only [nat.card_eq_fintype_card],
  exact fintype.card_pos_iff,
end

@[nolint instance_priority]
instance finite.prop (p : Prop) : finite p :=
begin
  classical,
  refine if h : p then _ else _,
  { exact ⟨⟨1, ⟨(equiv.prop_equiv_punit h).trans (by simpa using fintype.equiv_fin punit)⟩⟩⟩ },
  { exact ⟨⟨0, ⟨(equiv.prop_equiv_pempty h).trans (by simpa using fintype.equiv_fin pempty)⟩⟩⟩ }
end

namespace finite

lemma exists_max [finite α] [nonempty α] [linear_order β] (f : α → β) :
  ∃ x₀ : α, ∀ x, f x ≤ f x₀ :=
by { haveI := fintype.of_finite α, exact fintype.exists_max f }

lemma exists_min [finite α] [nonempty α] [linear_order β] (f : α → β) :
  ∃ x₀ : α, ∀ x, f x₀ ≤ f x :=
by { haveI := fintype.of_finite α, exact fintype.exists_min f }

lemma of_bijective [finite α] (f : α → β) (H : function.bijective f) : finite β :=
by { haveI := fintype.of_finite α, haveI := fintype.of_bijective f H, apply_instance }

lemma of_surjective [finite α] (f : α → β) (H : function.surjective f) : finite β :=
by { haveI := fintype.of_finite α, haveI := fintype.of_surjective f H, apply_instance }

lemma of_injective [finite β] (f : α → β) (H : function.injective f) : finite α :=
by { haveI := fintype.of_finite β, haveI := fintype.of_injective f H, apply_instance }

lemma of_equiv (α : Type*) [finite α] (f : α ≃ β) : finite β := of_bijective _ f.bijective

lemma card_eq [finite α] [finite β] : nat.card α = nat.card β ↔ nonempty (α ≃ β) :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, simp [fintype.card_eq] }

lemma of_subsingleton [subsingleton α] : finite α :=
by { haveI := fintype.of_subsingleton' α, apply_instance }

lemma card_le_one_iff_subsingleton [finite α] : nat.card α ≤ 1 ↔ subsingleton α :=
by { haveI := fintype.of_finite α, simp [fintype.card_le_one_iff_subsingleton] }

lemma one_lt_card_iff_nontrivial [finite α] : 1 < nat.card α ↔ nontrivial α :=
by { haveI := fintype.of_finite α, simp [fintype.one_lt_card_iff_nontrivial] }

lemma one_lt_card [finite α] [h : nontrivial α] : 1 < nat.card α :=
one_lt_card_iff_nontrivial.mpr h

@[simp] lemma card_option [finite α] : nat.card (option α) = nat.card α + 1 :=
by { haveI := fintype.of_finite α, simp }

lemma prod_left (β) [finite (α × β)] [nonempty β] : finite α :=
by { haveI := fintype.of_finite (α × β), apply finite.of_fintype, apply @fintype.prod_left α β }

lemma prod_right (α) [finite (α × β)] [nonempty α] : finite β :=
by { haveI := fintype.of_finite (α × β), apply finite.of_fintype, apply @fintype.prod_right α β }

instance [finite α] : finite (ulift α) :=
by { haveI := fintype.of_finite α, apply_instance }

instance [finite α] [finite β] : finite (α ⊕ β) :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, apply_instance }

lemma sum_left (β) [finite (α ⊕ β)] : finite α :=
of_injective (sum.inl : α → α ⊕ β) sum.inl_injective

lemma sum_right (α) [finite (α ⊕ β)] : finite β :=
of_injective (sum.inr : β → α ⊕ β) sum.inr_injective

lemma card_sum [finite α] [finite β] : nat.card (α ⊕ β) = nat.card α + nat.card β :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, simp }

lemma card_le_of_injective [finite β] (f : α → β) (hf : function.injective f) :
  nat.card α ≤ nat.card β :=
by { haveI := fintype.of_finite β, haveI := fintype.of_injective f hf,
     simpa using fintype.card_le_of_injective f hf }

lemma card_le_of_embedding [finite β] (f : α ↪ β) : nat.card α ≤ nat.card β :=
card_le_of_injective _ f.injective

lemma card_le_of_surjective [finite α] (f : α → β) (hf : function.surjective f) :
  nat.card β ≤ nat.card α :=
by { haveI := fintype.of_finite α, haveI := fintype.of_surjective f hf,
     simpa using fintype.card_le_of_surjective f hf }

lemma card_eq_zero_iff [finite α] : nat.card α = 0 ↔ is_empty α :=
by { haveI := fintype.of_finite α, simp [fintype.card_eq_zero_iff] }

end finite

instance subtype.finite [finite α] {p : α → Prop} : finite {x // p x} :=
by { haveI := fintype.of_finite α, apply_instance }

theorem finite.card_subtype_le [finite α] (p : α → Prop) :
  nat.card {x // p x} ≤ nat.card α :=
by { haveI := fintype.of_finite α, simpa using fintype.card_subtype_le p }

theorem finite.card_subtype_lt [finite α] {p : α → Prop} {x : α} (hx : ¬ p x) :
  nat.card {x // p x} < nat.card α :=
by { haveI := fintype.of_finite α, simpa using fintype.card_subtype_lt hx }

instance pi.finite {α : Type*} {β : α → Type*} [finite α] [∀ a, finite (β a)] : finite (Π a, β a) :=
by { haveI := fintype.of_finite α, haveI := λ a, fintype.of_finite (β a), apply_instance }

instance vector.finite {α : Type*} [finite α] {n : ℕ} : finite (vector α n) :=
by { haveI := fintype.of_finite α, apply_instance }

instance quotient.finite [finite α] (s : setoid α) : finite (quotient s) :=
by { haveI := fintype.of_finite α, apply_instance }

instance function.embedding.finite {α β} [finite α] [finite β]: finite (α ↪ β) :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, apply_instance }

instance [finite α] {n : ℕ} : finite (sym α n) :=
by { haveI := fintype.of_finite α, apply_instance }
