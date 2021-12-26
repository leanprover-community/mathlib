/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

import data.multiset.basic
import data.vector.basic
import tactic.apply_fun

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `data.sym.sym2`.

TODO: This was created as supporting material for `sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/

universes u

/--
The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `multiset` since these are well developed in the
library.  We also give a definition `sym.sym'` in terms of vectors, and we
show these are equivalent in `sym.sym_equiv_sym'`.
-/
def sym (α : Type u) (n : ℕ) := {s : multiset α // s.card = n}

/--
This is the `list.perm` setoid lifted to `vector`.

See note [reducible non-instances].
-/
@[reducible]
def vector.perm.is_setoid (α : Type u) (n : ℕ) : setoid (vector α n) :=
{ r := λ a b, list.perm a.1 b.1,
  iseqv := by { rcases list.perm.eqv α with ⟨hr, hs, ht⟩, tidy, } }

local attribute [instance] vector.perm.is_setoid

namespace sym

variables {α : Type u} {n : ℕ}

/--
This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
def of_vector (x : vector α n) : sym α n :=
⟨↑x.val, by { rw multiset.coe_card, exact x.2 }⟩

instance : has_lift (vector α n) (sym α n) :=
{ lift := of_vector }

/--
The unique element in `sym α 0`.
-/
@[pattern] def nil : sym α 0 := ⟨0, by tidy⟩

/--
Inserts an element into the term of `sym α n`, increasing the length by one.
-/
@[pattern] def cons : α → sym α n → sym α (nat.succ n)
| a ⟨s, h⟩ := ⟨a ::ₘ s, by rw [multiset.card_cons, h]⟩

notation a :: b := cons a b

@[simp]
lemma cons_inj_right (a : α) (s s' : sym α n) : a :: s = a :: s' ↔ s = s' :=
by { cases s, cases s', delta cons, simp, }

@[simp]
lemma cons_inj_left (a a' : α) (s : sym α n) : a :: s = a' :: s ↔ a = a' :=
by { cases s, delta cons, simp, }

lemma cons_swap (a b : α) (s : sym α n) : a :: b :: s = b :: a :: s :=
by { cases s, ext, delta cons, rw subtype.coe_mk, dsimp, exact multiset.cons_swap a b s_val }

/--
`α ∈ s` means that `a` appears as one of the factors in `s`.
-/
def mem (a : α) (s : sym α n) : Prop := a ∈ s.1

instance : has_mem α (sym α n) := ⟨mem⟩

instance decidable_mem [decidable_eq α] (a : α) (s : sym α n) : decidable (a ∈ s) :=
by { cases s, change decidable (a ∈ s_val), apply_instance }

@[simp] lemma mem_cons {a b : α} {s : sym α n} : a ∈ b :: s ↔ a = b ∨ a ∈ s :=
begin cases s, change a ∈ b ::ₘ s_val ↔ a = b ∨ a ∈ s_val, simp, end

lemma mem_cons_of_mem {a b : α} {s : sym α n} (h : a ∈ s) : a ∈ b :: s :=
mem_cons.2 (or.inr h)

@[simp] lemma mem_cons_self (a : α) (s : sym α n) : a ∈ a :: s :=
mem_cons.2 (or.inl rfl)

lemma cons_of_coe_eq (a : α) (v : vector α n) : a :: (↑v : sym α n) = ↑(a ::ᵥ v) :=
by { unfold_coes, delta of_vector, delta cons, delta vector.cons, tidy }

lemma sound {a b : vector α n} (h : a.val ~ b.val) : (↑a : sym α n) = ↑b :=
begin
  cases a, cases b, unfold_coes, dunfold of_vector,
  simp only [subtype.mk_eq_mk, multiset.coe_eq_coe],
  exact h,
end

/-- `erase s a h` is the sym that subtracts 1 from the
  multiplicity of `a` if a is present in the sym. -/
def erase [decidable_eq α] (s : sym α (n + 1)) (a : α) (h : a ∈ s) : sym α n :=
⟨s.val.erase a, (multiset.card_erase_of_mem h).trans $ s.property.symm ▸ n.pred_succ⟩

/--
Another definition of the nth symmetric power, using vectors modulo permutations. (See `sym`.)
-/
def sym' (α : Type u) (n : ℕ) := quotient (vector.perm.is_setoid α n)

/--
This is `cons` but for the alternative `sym'` definition.
-/
def cons' {α : Type u} {n : ℕ} : α → sym' α n → sym' α (nat.succ n) :=
λ a, quotient.map (vector.cons a) (λ ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h, list.perm.cons _ h)

notation a :: b := cons' a b

/--
Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def sym_equiv_sym' {α : Type u} {n : ℕ} : sym α n ≃ sym' α n :=
equiv.subtype_quotient_equiv_quotient_subtype _ _ (λ _, by refl) (λ _ _, by refl)

lemma cons_equiv_eq_equiv_cons (α : Type u) (n : ℕ) (a : α) (s : sym α n) :
  a :: sym_equiv_sym' s = sym_equiv_sym' (a :: s) :=
by tidy

section inhabited
-- Instances to make the linter happy

instance inhabited_sym [inhabited α] (n : ℕ) : inhabited (sym α n) :=
⟨⟨multiset.repeat (default α) n, multiset.card_repeat _ _⟩⟩

instance inhabited_sym' [inhabited α] (n : ℕ) : inhabited (sym' α n) :=
⟨quotient.mk' (vector.repeat (default α) n)⟩

end inhabited

instance has_zero : has_zero (sym α 0) := ⟨⟨0, rfl⟩⟩
instance has_emptyc : has_emptyc (sym α 0) := ⟨0⟩

lemma eq_nil_of_card_zero (s : sym α 0) : s = nil :=
begin
  obtain ⟨a, h⟩ := s,
  rw multiset.card_eq_zero at h,
  subst h,
  refl,
end

instance unique_zero : unique (sym α 0) :=
⟨⟨nil⟩, eq_nil_of_card_zero⟩

/-- `repeat a n` is the sym containing only `a` with multiplicity `n`. -/
def repeat (a : α) (n : ℕ) : sym α n := ⟨multiset.repeat a n, multiset.card_repeat _ _⟩

lemma repeat_succ {a : α} {n : ℕ} : repeat a n.succ = a :: repeat a n := rfl

lemma exists_eq_cons_of_succ (s : sym α n.succ) : ∃ (a : α) (s' : sym α n), s = a :: s' :=
begin
  classical,
  obtain ⟨m, h⟩ := s,
  have : 0 < multiset.card m,
  { rw h,
    exact nat.succ_pos n, },
  rw multiset.card_pos_iff_exists_mem at this,
  obtain ⟨a, ha⟩ := this,
  use [a, m.erase a],
  { rw [multiset.card_erase_of_mem ha, h],
    refl, },
  { rw cons,
    congr,
    rw multiset.cons_erase ha, },
end

lemma eq_repeat_of_subsingleton [subsingleton α] (a : α) {n : ℕ} (s : sym α n) : s = repeat a n :=
begin
  induction n with n ih,
  { rw eq_nil_of_card_zero s,
    refl, },
  { obtain ⟨b, s', rfl⟩ := exists_eq_cons_of_succ s,
    rw [repeat_succ, ih s'],
    congr, },
end

instance subsingleton (n : ℕ) [subsingleton α] : subsingleton (sym α n) :=
⟨begin
  cases n,
  { simp, },
  { intros s s',
    obtain ⟨b, s, rfl⟩ := exists_eq_cons_of_succ s,
    rw [eq_repeat_of_subsingleton b s', eq_repeat_of_subsingleton b s, repeat_succ], },
end⟩

instance is_empty (n : ℕ) [is_empty α] : is_empty (sym α n.succ) :=
⟨λ s, by { obtain ⟨a, s, rfl⟩ := exists_eq_cons_of_succ s, exact is_empty_elim a }⟩

instance unique (n : ℕ) [unique α] : unique (sym α n) := unique.mk' _

lemma repeat_left_injective (n : ℕ) (h : n ≠ 0) : function.injective (λ x : α, repeat x n) :=
begin
  intros a b x,
  simp only [repeat, subtype.mk.inj_eq] at x,
  exact (multiset.repeat_left_inj a b n h).mp x,
end

lemma repeat_left_inj (a b : α) (n : ℕ) (h : n ≠ 0) : repeat a n = repeat b n ↔ a = b :=
(repeat_left_injective n h).eq_iff

instance nontrivial (n : ℕ) [nontrivial α] : nontrivial (sym α (n + 1)) :=
(repeat_left_injective n.succ n.succ_ne_zero).nontrivial

def map {α β : Type*} {n : ℕ} (f : α → β) (x : sym α n) : sym β n :=
⟨x.val.map f, by simpa [multiset.card_map] using x.property⟩

@[simp] lemma mem_map {α β : Type*} {n : ℕ} {f : α → β} {b : β} {l : sym α n} :
  b ∈ sym.map f l ↔ ∃ a, a ∈ l ∧ f a = b := multiset.mem_map

@[simp] lemma map_id {α : Type*} {n : ℕ} (s : sym α n) : sym.map id s = s :=
by simp [sym.map, subtype.mk.inj_eq]

@[simp] lemma map_map {α β γ : Type*} {n : ℕ} (g : β → γ) (f : α → β) (s : sym α n) :
  sym.map g (sym.map f s) = sym.map (g ∘ f) s :=
by simp [sym.map, subtype.mk.inj_eq]

@[simp] lemma map_zero {α β : Type*} (f : α → β) :
  sym.map f (0 : sym α 0) = (0 : sym β 0) := rfl

@[simp] lemma map_cons {α β : Type*} {n : ℕ} (f : α → β) (a : α) (s : sym α n) :
  (a :: s).map f = (f a) :: s.map f :=
by { cases s, simp [map, cons] }

/-- Mapping an equivalence `α ≃ β` using `sym.map` gives an equivalence between `sym α n` and
`sym β n`. -/
@[simps]
def equiv_congr {β : Type u} (e : α ≃ β) : sym α n ≃ sym β n :=
{ to_fun := map e,
  inv_fun := map e.symm,
  left_inv := λ x, by rw [map_map, equiv.symm_comp_self, map_id],
  right_inv := λ x, by rw [map_map, equiv.self_comp_symm, map_id] }

end sym
