/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura, Jeremy Avigad, Minchao Wu

Finite sets.
-/
import data.list.set data.list.perm tactic.finish
open list subtype nat

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

@[simp] lemma or_self_or (a b : Prop) : a ∨ a ∨ b ↔ a ∨ b :=
calc a ∨ a ∨ b ↔ (a ∨ a) ∨ b : or.assoc.symm
  ... ↔ _ : by rw [or_self]

theorem perm_insert_cons_of_not_mem [decidable_eq α] {a : α} {l : list α} (h : a ∉ l) : perm (list.insert a l) (a :: l) :=
have list.insert a l = a :: l, from if_neg h, by rw this

def nodup_list (α : Type u) := {l : list α // nodup l}

def to_nodup_list_of_nodup {l : list α} (n : nodup l) : nodup_list α :=
⟨l, n⟩

def to_nodup_list [decidable_eq α] (l : list α) : nodup_list α :=
@to_nodup_list_of_nodup α (erase_dup l) (nodup_erase_dup l)

private def eqv (l₁ l₂ : nodup_list α) :=
perm l₁.1 l₂.1

local infix ~ := eqv

private def eqv.refl (l : nodup_list α) : l ~ l :=
perm.refl _

private def eqv.symm {l₁ l₂ : nodup_list α} : l₁ ~ l₂ → l₂ ~ l₁ :=
perm.symm

private def eqv.trans {l₁ l₂ l₃ : nodup_list α} : l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃ :=
perm.trans

instance finset.nodup_list_setoid  (α : Type u) : setoid (nodup_list α) :=
setoid.mk (@eqv α) (mk_equivalence (@eqv α) (@eqv.refl α) (@eqv.symm α) (@eqv.trans α))

def finset (α : Type u) : Type u :=
quotient (finset.nodup_list_setoid α)

namespace finset

def to_finset_of_nodup (l : list α) (n : nodup l) : finset α :=
⟦to_nodup_list_of_nodup n⟧

@[elab_as_eliminator]
protected theorem induction_on_to_finset {α : Type u} {p : finset α → Prop} (s : finset α)
  (h : ∀ (l : list α) (h : nodup l), p (to_finset_of_nodup l h)) : p s :=
quot.induction_on s $ assume ⟨l, hl⟩, h l hl

def to_finset [decidable_eq α] (l : list α) : finset α :=
⟦to_nodup_list l⟧

lemma to_finset_eq_of_nodup [decidable_eq α] {l : list α} (n : nodup l) :
  to_finset_of_nodup l n = to_finset l :=
have p : to_nodup_list_of_nodup n = to_nodup_list l, from
  begin
    dsimp [to_nodup_list], have eq : erase_dup l = l,
    {apply erase_dup_eq_of_nodup n},
    {simp [eq]} -- rw [eq] doesn't work
  end,
quotient.sound (eq.subst p (setoid.refl _))

instance has_decidable_eq  [decidable_eq α] : decidable_eq (finset α) :=
λ s₁ s₂, quotient.rec_on_subsingleton₂ s₁ s₂
  (λ l₁ l₂,
     match perm.decidable_perm l₁.1 l₂.1 with
     | decidable.is_true e := decidable.is_true (quot.sound e)
     | decidable.is_false n := decidable.is_false (λ e : ⟦l₁⟧ = ⟦l₂⟧, absurd (quotient.exact e) n)
     end)

section mem

def mem (a : α) (s : finset α) : Prop :=
quot.lift_on s (λ l, a ∈ l.1)
 (λ l₁ l₂ (e : l₁ ~ l₂), propext (iff.intro
   (λ ainl₁, perm.mem_of_perm e ainl₁)
   (λ ainl₂, perm.mem_of_perm (perm.symm e) ainl₂)))

instance : has_mem α (finset α) := ⟨mem⟩

@[simp] lemma mem_to_finset_of_nodup_eq {a : α} {l : list α} (n : nodup l) :
  (a ∈ to_finset_of_nodup l n) = (a ∈ l) :=
rfl

theorem mem_of_mem_list {a : α} {l : nodup_list α} : a ∈ l.1 → a ∈ @id (finset α) ⟦l⟧ :=
λ ainl, ainl

theorem mem_list_of_mem {a : α} {l : nodup_list α} : a ∈ @id (finset α) ⟦l⟧ → a ∈ l.1 :=
λ ainl, ainl

instance decidable_mem [h : decidable_eq α] : ∀ (a : α) (s : finset α), decidable (a ∈ s) :=
λ a s, quot.rec_on_subsingleton s
  (λ l, match list.decidable_mem a l.1 with
        | decidable.is_true p := decidable.is_true (mem_of_mem_list p)
        | decidable.is_false n := decidable.is_false (λ p, absurd (mem_list_of_mem p) n)
        end)

theorem mem_to_finset [decidable_eq α] {a : α} {l : list α} : a ∈ l → a ∈ to_finset l :=
λ ainl, mem_erase_dup.mpr ainl

/- extensionality -/
theorem ext {s₁ s₂ : finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
quotient.induction_on₂ s₁ s₂ (λ l₁ l₂ e, quot.sound (perm.perm_ext l₁.2 l₂.2 e))

end mem

/- subset -/
section subset
protected def subset (s₁ s₂ : finset α) : Prop :=
quotient.lift_on₂ s₁ s₂ (λ l₁ l₂, l₁.1 ⊆ l₂.1)
  (λ v₁ v₂ w₁ w₂ p₁ p₂, propext (iff.intro
    (λ s₁ a i, perm.mem_of_perm p₂ (s₁ (perm.mem_of_perm (perm.symm p₁) i)))
    (λ s₂ a i, perm.mem_of_perm (perm.symm p₂) (s₂ (perm.mem_of_perm p₁ i)))))

instance : has_subset (finset α) := ⟨finset.subset⟩

-- theorem subset_univ [h : fintype α] (s : finset α) : s ⊆ univ :=
-- quot.induction_on s (λ l a i, fintype.complete a)

theorem subset.refl (s : finset α) : s ⊆ s :=
quot.induction_on s (λ l, list.subset.refl l.1)

theorem subset.trans {s₁ s₂ s₃ : finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
quotient.induction_on₃ s₁ s₂ s₃ (λ l₁ l₂ l₃ h₁ h₂, list.subset.trans h₁ h₂)

theorem mem_of_subset_of_mem {s₁ s₂ : finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
quotient.induction_on₂ s₁ s₂ (λ l₁ l₂ h₁ h₂, h₁ h₂)

theorem subset.antisymm {s₁ s₂ : finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
ext (λ x, iff.intro (λ H, mem_of_subset_of_mem H₁ H) (λ H, mem_of_subset_of_mem H₂ H))

theorem subset_of_forall {s₁ s₂ : finset α} : (∀x, x ∈ s₁ → x ∈ s₂) → s₁ ⊆ s₂ :=
quotient.induction_on₂ s₁ s₂ (λ l₁ l₂ H, H)

end subset

section empty
variables {s : finset α} {a b : α}

/- empty -/
protected def empty : finset α :=
to_finset_of_nodup [] nodup_nil

instance : has_emptyc (finset α) := ⟨finset.empty⟩

@[simp] theorem not_mem_empty : a ∉ (∅ : finset α) := λ aine, aine

@[simp] theorem mem_empty_iff : a ∈ (∅ : finset α) ↔ false := iff_false_intro not_mem_empty

theorem empty_subset : ∅ ⊆ s := quot.induction_on s (λ l, list.nil_subset l.1)

theorem eq_empty_of_forall_not_mem (H : ∀x, x ∉ s) : s = ∅ := ext (λ x, iff_false_intro (H x))

theorem eq_empty_of_subset_empty (h : s ⊆ ∅) : s = ∅ := subset.antisymm h empty_subset

theorem subset_empty_iff (x : finset α) : x ⊆ ∅ ↔ x = ∅ :=
iff.intro eq_empty_of_subset_empty (λ xeq, by rw xeq; apply subset.refl ∅)

theorem exists_mem_of_ne_empty : s ≠ ∅ → ∃ a : α, a ∈ s :=
finset.induction_on_to_finset s $ assume l hl,
  match l, hl with
  | [] := assume _ h, false.elim $ h rfl
  | (a :: l) := assume _ _, ⟨a, by simp⟩
  end

end empty

-- /- universe -/
-- def univ [h : fintype A] : finset A :=
-- to_finset_of_nodup (@fintype.elems A h) (@fintype.unique A h)

-- theorem mem_univ [fintype A] (x : A) : x ∈ univ :=
-- fintype.complete x

-- theorem mem_univ_eq [fintype A] (x : A) : x ∈ univ = true := propext (iff_true_intro !mem_univ)

/- insert -/
section insert
variables [decidable_eq α] {s t : finset α} {a b : α}

protected def insert (a : α) (s : finset α) : finset α :=
quot.lift_on s
  (λ l, to_finset_of_nodup (insert a l.1) (nodup_insert l.2))
  (λ (l₁ l₂ : nodup_list α) (p : l₁ ~ l₂), quot.sound (perm.perm_insert a p))

instance : has_insert α (finset α) := ⟨finset.insert⟩

@[simp] theorem mem_insert_iff : a ∈ insert b s ↔ (a = b ∨ a ∈ s) :=
finset.induction_on_to_finset s $ assume l hl, show a ∈ insert b l ↔ (a = b ∨ a ∈ l), by simp

theorem mem_insert : a ∈ insert a s := by simp
theorem mem_insert_of_mem : a ∈ s → a ∈ insert b s := by simp {contextual := tt}
theorem mem_of_mem_insert_of_ne (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
or_resolve_right (mem_insert_iff.mp h)

@[simp] theorem insert_eq_of_mem (h : a ∈ s) : insert a s = s :=
ext (λ x, by rw mem_insert_iff; apply or_iff_right_of_imp; intro eq; rw eq; assumption)

@[simp] theorem insert.comm : insert a (insert b s) = insert b (insert a s) :=
ext $ by simp

@[simp] theorem insert_idem : insert a (insert a s) = insert a s :=
ext $ by simp [mem_insert_iff]

@[simp] theorem insert_ne_empty : insert a s ≠ ∅ :=
assume h, @not_mem_empty α a $ h ▸ by simp

theorem subset_insert [h : decidable_eq α] : s ⊆ insert a s :=
subset_of_forall (λ x h, mem_insert_of_mem h)

theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t :=
subset_of_forall $ assume x, by simp; exact or.imp_right (mem_of_subset_of_mem h)

@[recursor 6] protected theorem induction {p : finset α → Prop}
  (h₁ : p ∅) (h₂ : ∀⦃a : α⦄, ∀{s : finset α}, a ∉ s → p s → p (insert a s)) (s) : p s :=
finset.induction_on_to_finset s $ λl, list.rec_on l
  (assume _, h₁)
  (assume a l ih hal,
    let l' := to_finset_of_nodup l $ nodup_of_nodup_cons hal in
    have insert a l' = to_finset_of_nodup (a :: l) hal,
      from ext $ by simp,
    this ▸ @h₂ a l' (not_mem_of_nodup_cons hal) (ih _))

protected theorem induction_on {p : finset α → Prop} (s : finset α)
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄, ∀ {s : finset α}, a ∉ s → p s → p (insert a s)) : p s :=
finset.induction h₁ h₂ s

-- useful in proofs by induction
theorem forall_of_forall_insert {p : α → Prop} (H : ∀ x, x ∈ insert a s → p x) :
  ∀ x, x ∈ s → p x :=
λ x xs, H x (mem_insert_of_mem xs)

end insert

section singleton
variables [decidable_eq α] {a b : α} {s : finset α}

@[simp] theorem mem_singleton_iff : b ∈ ({a} : finset α) ↔ (b = a) :=
show b ∈ insert a ∅ ↔ b = a, by simp

theorem mem_singleton : a ∈ ({a} : finset α) := mem_insert

theorem mem_singleton_of_eq (h : b = a) : b ∈ ({a} : finset α) :=
by rw h; apply mem_insert

theorem eq_of_mem_singleton (h : b ∈ ({a}:finset α)) : b = a :=
iff.mp mem_singleton_iff h

theorem eq_of_singleton_eq (h : {a} = ({b}:finset α)) : a = b :=
have a ∈ ({b} : finset α), by rw ←h; apply mem_singleton,
eq_of_mem_singleton this

@[simp] theorem singleton_ne_empty : ({a} : finset α) ≠ ∅ := insert_ne_empty

@[simp] theorem insert_singelton_self_eq  : ({a, a} : finset α) = {a} :=
show insert a {a} = ({a} : finset α), by rw [insert_eq_of_mem]; apply mem_singleton

end singleton

/- union -/
section union
variable [decidable_eq α]

protected def union (s₁ s₂ : finset α) : finset α :=
quotient.lift_on₂ s₁ s₂
  (λ l₁ l₂,
    to_finset_of_nodup (list.union l₁.1 l₂.1)
                       (nodup_union l₁.1 l₂.2))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm.perm_union p₁ p₂))

instance : has_union (finset α) := ⟨finset.union⟩

@[simp] theorem mem_union_iff {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
quotient.induction_on₂ s₁ s₂ (λ l₁ l₂, list.mem_union_iff)

theorem mem_union_left {a : α} {s₁ : finset α} (s₂ : finset α) : a ∈ s₁ → a ∈ s₁ ∪ s₂ :=
by rw [mem_union_iff]; exact or.inl

theorem mem_union_right {a : α} {s₂ : finset α} (s₁ : finset α) : a ∈ s₂ → a ∈ s₁ ∪ s₂ :=
by rw [mem_union_iff]; exact or.inr

theorem mem_or_mem_of_mem_union {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∪ s₂ → a ∈ s₁ ∨ a ∈ s₂ :=
mem_union_iff.mp

@[simp] theorem union_comm (s₁ s₂ : finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
ext $ by simp

@[simp] theorem union_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
ext $ by simp

theorem union_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
ext $ by simp

theorem union_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
ext $ by simp

@[simp] theorem union_self (s : finset α) : s ∪ s = s :=
ext $ by simp

@[simp] theorem union_empty (s : finset α) : s ∪ ∅ = s :=
ext $ by simp

@[simp] theorem empty_union (s : finset α) : ∅ ∪ s = s :=
ext $ by simp

theorem insert_eq (a : α) (s : finset α) : insert a s = {a} ∪ s :=
ext $ by simp

@[simp] theorem insert_union (a : α) (s t : finset α) : insert a s ∪ t = insert a (s ∪ t) :=
ext $ by simp

@[simp] theorem union_insert (a : α) (s t : finset α) : s ∪ insert a t = insert a (s ∪ t) :=
ext $ by simp

end union

/- inter -/
section inter
variable [decidable_eq α]

protected def inter (s₁ s₂ : finset α) : finset α :=
quotient.lift_on₂ s₁ s₂
  (λ l₁ l₂, to_finset_of_nodup (list.inter l₁.1 l₂.1) (nodup_inter_of_nodup _ l₁.2))
  (λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound (perm.perm_inter p₁ p₂))

instance : has_inter (finset α) := ⟨finset.inter⟩

@[simp] theorem mem_inter_iff (a : α) (s₁ s₂ : finset α) : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
quotient.induction_on₂ s₁ s₂ (λ l₁ l₂, mem_inter_iff _ _ _)

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∩ s₂ → a ∈ s₁ :=
by rw [mem_inter_iff]; exact and.left

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∩ s₂ → a ∈ s₂ :=
by rw [mem_inter_iff]; exact and.right

theorem mem_inter {a : α} {s₁ s₂ : finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
by rw [mem_inter_iff]; exact and.intro

@[simp] theorem inter_comm (s₁ s₂ : finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
ext $ by simp

@[simp] theorem inter_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
ext $ by simp

@[simp] theorem inter_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
ext $ by simp

@[simp] theorem inter_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
ext $ by simp

@[simp] theorem inter_self (s : finset α) : s ∩ s = s :=
ext $ by simp

@[simp] theorem inter_empty (s : finset α) : s ∩ ∅ = ∅ :=
ext $ by simp

@[simp] theorem empty_inter (s : finset α) : ∅ ∩ s = ∅ :=
ext $ by simp

@[simp] theorem insert_inter_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₂) :
  insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
ext $ by simp; intro x; constructor; finish

@[simp] theorem inter_insert_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₁) :
  s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) :=
by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp] theorem insert_inter_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₂) :
  insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
ext $ assume a', by by_cases a' = a with h'; simp [mem_inter_iff, mem_insert_iff, h, h']

@[simp] theorem inter_insert_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₁) :
  s₁ ∩ insert a s₂ = s₁ ∩ s₂ :=
by rw [inter_comm, insert_inter_of_not_mem h, inter_comm]

@[simp] theorem singleton_inter_of_mem {a : α} {s : finset α} : a ∈ s → {a} ∩ s = {a} :=
show a ∈ s → insert a ∅ ∩ s = insert a ∅, by simp {contextual := tt}

@[simp] theorem singleton_inter_of_not_mem {a : α} {s : finset α} : a ∉ s → {a} ∩ s = ∅ :=
show a ∉ s → insert a ∅ ∩ s = ∅, by simp {contextual := tt}

@[simp] theorem inter_singleton_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ∩ {a} = {a} :=
by rw [inter_comm, singleton_inter_of_mem h]

@[simp] theorem inter_singleton_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : s ∩ {a} = ∅ :=
by rw [inter_comm, singleton_inter_of_not_mem h]

end inter

/- distributivity laws -/
section inter
variable [decidable_eq α]

theorem inter_distrib_left (s t u : finset α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
ext $ begin simp [mem_inter_iff, mem_union_iff], intro x, apply iff.intro, repeat {finish} end

theorem inter_distrib_right (s t u : finset α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext $ begin simp [mem_inter_iff, mem_union_iff], intro x, apply iff.intro, repeat {finish} end

theorem union_distrib_left (s t u : finset α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext $ begin simp [mem_inter_iff, mem_union_iff], intro x, apply iff.intro, repeat {finish} end

theorem union_distrib_right (s t u : finset α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
ext $ begin simp [mem_inter_iff, mem_union_iff], intro x, apply iff.intro, repeat {finish} end

end inter

/- erase -/
section erase
variables [decidable_eq α] {a b c : α} {s t : finset α}

def erase (a : α) (s : finset α) : finset α :=
quot.lift_on s
  (λ l, to_finset_of_nodup (l.1.erase a) (nodup_erase_of_nodup a l.2))
  (λ (l₁ l₂ : nodup_list α) (p : l₁ ~ l₂), quot.sound (perm.erase_perm_erase_of_perm a p))

@[simp] theorem mem_erase_iff : a ∈ erase b s ↔ a ≠ b ∧ a ∈ s :=
finset.induction_on_to_finset s $ λ l hl, mem_erase_iff_of_nodup hl

theorem not_mem_erase : a ∉ erase a s := by simp

@[simp] theorem erase_empty : erase a ∅ = ∅ := rfl

theorem ne_of_mem_erase : b ∈ erase a s → b ≠ a := by simp {contextual:=tt}

theorem mem_of_mem_erase : b ∈ erase a s → b ∈ s := by simp {contextual:=tt}

theorem mem_erase_of_ne_of_mem : a ≠ b → a ∈ s → a ∈ erase b s := by simp {contextual:=tt}

theorem erase_insert (h : a ∉ s) : erase a (insert a s) = s :=
ext $ assume x, by simp; constructor; finish

theorem insert_erase (h : a ∈ s) : insert a (erase a s) = s :=
ext $ assume x, by simp; constructor; finish

theorem erase_subset_erase (h : s ⊆ t) : erase a s ⊆ erase a t :=
subset_of_forall $ assume x, by simp; exact and_implies_right (mem_of_subset_of_mem h)

theorem erase_subset : erase a s ⊆ s :=
subset_of_forall $ assume x, by simp {contextual:=tt}

theorem erase_eq_of_not_mem (h : a ∉ s) : erase a s = s :=
ext $ assume b, by by_cases b = a; simp [*]

theorem erase_insert_subset : erase a (insert a s) ⊆ s :=
by by_cases a ∈ s; simp [h, erase_subset, erase_insert, subset.refl]

theorem erase_subset_of_subset_insert (h : s ⊆ insert a t) : erase a s ⊆ t :=
subset.trans (erase_subset_erase h) erase_insert_subset

theorem insert_erase_subset : s ⊆ insert a (erase a s) :=
decidable.by_cases
  (λ ains : a ∈ s, by rw [insert_erase ains]; apply subset.refl)
  (λ nains : a ∉ s, by rw[erase_eq_of_not_mem nains]; apply subset_insert)

theorem subset_insert_of_erase_subset (h : erase a s ⊆ t) : s ⊆ insert a t :=
subset.trans insert_erase_subset (insert_subset_insert h)

theorem subset_insert_iff (s t : finset α) (a : α) : s ⊆ insert a t ↔ erase a s ⊆ t :=
iff.intro erase_subset_of_subset_insert subset_insert_of_erase_subset

end erase

/- upto -/
section upto
variables {n m l : ℕ}

def upto (n : ℕ) : finset ℕ :=
to_finset_of_nodup (list.upto n) (nodup_upto n)

theorem lt_of_mem_upto : m ∈ upto n → m < n :=
@list.lt_of_mem_upto n m

theorem mem_upto_succ_of_mem_upto : m ∈ upto n → m ∈ upto (succ n) :=
list.mem_upto_succ_of_mem_upto

theorem mem_upto_of_lt : m < n → m ∈ upto n :=
@list.mem_upto_of_lt n m

theorem mem_upto_iff : m ∈ upto n ↔ m < n :=
iff.intro lt_of_mem_upto mem_upto_of_lt

theorem upto_zero : upto 0 = ∅ := rfl

theorem upto_succ : upto (succ n) = insert n (upto n) :=
ext $ by simp [mem_upto_iff, mem_insert_iff, lt_succ_iff_le, le_iff_lt_or_eq]

end upto

/- useful rules for calculations with quantifiers -/
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : finset α) ∧ p x) ↔ false :=
⟨λ⟨x, hx⟩, not_mem_empty (hx.left), false.elim⟩

theorem exists_mem_insert_iff [d : decidable_eq α]
    (a : α) (s : finset α) (p : α → Prop) :
  (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ (∃ x, x ∈ s ∧ p x) :=
iff.intro
  (λ H,
    let ⟨x,H1,H2⟩ := H in
    or.elim (mem_insert_iff.mp H1)
      (λ l, or.inl (eq.subst l H2))
      (λ r, or.inr ⟨x, ⟨r, H2⟩⟩))
  (λ H,
    or.elim H
      (λ l, ⟨a, ⟨mem_insert, l⟩⟩)
      (λ r, let ⟨x,H2,H3⟩ := r in ⟨x, ⟨mem_insert_of_mem H2, H3⟩⟩))

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : finset α) → p x) ↔ true :=
iff.intro (λ H, trivial) (λ H x H', absurd H' not_mem_empty)

theorem forall_mem_insert_iff [d : decidable_eq α]
    (a : α) (s : finset α) (p : α → Prop) :
  (∀ x, x ∈ insert a s → p x) ↔ p a ∧ (∀ x, x ∈ s → p x) :=
iff.intro
  (λ H, and.intro (H _ mem_insert) (λ x H', H _ (mem_insert_of_mem H')))
  (λ H x, λ H' : x ∈ insert a s,
    or.elim (mem_insert_iff.mp H')
      (λ l, eq.subst (eq.symm l) H.left)
      (λ r, and.right H _ r))

section image
variables (f : α → β) (s : finset α) [decidable_eq β]

protected def image : finset β :=
quot.lift_on s (λl, to_finset $ l.val.map f) $ assume ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ (h : perm l₁ l₂),
  quotient.sound $ perm.perm_erase_dup_of_perm $ perm.perm_map _ $ h

variables {f s} [decidable_eq α]

lemma erase_dup_map_erase_dup_eq {f : α → β} :
  ∀{l : list α}, erase_dup (map f (erase_dup l)) = (erase_dup $ map f l)
| [] := by simp
| (x :: xs) :=
  have f x ∈ map f (erase_dup xs) ↔ f x ∈ map f xs, by simp [mem_map_iff, mem_erase_dup],
  by by_cases x ∈ xs; by_cases f x ∈ map f xs; simp [mem_map, erase_dup, *] at *

lemma image_to_finset {l : list α} : (to_finset l).image f = to_finset (l.map f) :=
quot.sound $ show perm (erase_dup $ map f $ erase_dup l) (erase_dup $ map f l),
  by rw [erase_dup_map_erase_dup_eq]

lemma image_to_finset_of_nodup {l : list α} (hl : nodup l) (h : ∀x∈l, ∀y∈l, f x = f y → x = y) :
  (to_finset_of_nodup l hl).image f = to_finset_of_nodup (l.map f) (nodup_map_on h hl) :=
quot.sound $ show perm (erase_dup (map f l)) (l.map f),
  by rw [erase_dup_eq_of_nodup (nodup_map_on h hl)]

lemma image_id : s.image id = s :=
quot.induction_on s $ assume ⟨l, hl⟩, show to_finset (l.map id) = to_finset_of_nodup l hl,
  by rw [map_id, to_finset_eq_of_nodup]

lemma image_image [decidable_eq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
quot.induction_on s $ assume ⟨l, hl⟩,
  show ((to_finset_of_nodup l hl).image f).image g = (to_finset_of_nodup l hl).image (g ∘ f),
    by simp [to_finset_eq_of_nodup, image_to_finset]

end image

section card
variables [decidable_eq α] {a : α} {s : finset α} {n : ℕ}

/- card -/
def card (s : finset α) : nat :=
quot.lift_on s (λ l, length l.1) (λ l₁ l₂ p, perm.length_eq_length_of_perm p)

@[simp] theorem card_empty : card (∅ : finset α) = 0 := rfl

lemma ne_empty_of_card_eq_succ : card s = succ n → s ≠ ∅ :=
λ h hn, by rw hn at h; contradiction

@[simp] theorem card_insert_of_not_mem : a ∉ s → card (insert a s) = card s + 1 :=
quot.induction_on s (λ (l : nodup_list α) (nainl : a ∉ ⟦l⟧), list.length_insert_of_not_mem nainl)

theorem card_insert_le : card (insert a s) ≤ card s + 1 :=
if h : a ∈ s then by simp [h, le_add_left] else by rw [card_insert_of_not_mem h]

theorem eq_empty_of_card_eq_zero : card s = 0 → s = ∅ :=
s.induction_on
  (assume _, rfl)
  (assume a s ha ih, by rw [card_insert_of_not_mem ha]; exact assume h, nat.no_confusion h)

theorem card_erase_of_mem : a ∈ s → card (erase a s) = pred (card s) :=
quot.induction_on s (λ l ainl, list.length_erase_of_mem ainl)

theorem card_upto : card (upto n) = n :=
list.length_upto n

end card

end finset
