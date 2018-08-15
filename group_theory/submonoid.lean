/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro
-/
import algebra.group_power

variables {α : Type*} [monoid α] {s : set α}
variables {β : Type*} [add_monoid β] {t : set β}

/-- `s` is a submonoid: a set containing 1 and closed under multiplication. -/
class is_submonoid (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

/-- `s` is an additive submonoid: a set containing 0 and closed under addition. -/
class is_add_submonoid (s : set β) : Prop :=
(zero_mem : (0:β) ∈ s)
(add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s)

attribute [to_additive is_add_submonoid] is_submonoid
attribute [to_additive is_add_submonoid.zero_mem] is_submonoid.one_mem
attribute [to_additive is_add_submonoid.add_mem] is_submonoid.mul_mem
attribute [to_additive is_add_submonoid.mk] is_submonoid.mk

instance additive.is_add_submonoid
  (s : set α) : ∀ [is_submonoid s], @is_add_submonoid (additive α) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem additive.is_add_submonoid_iff
  {s : set α} : @is_add_submonoid (additive α) _ s ↔ is_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by resetI; apply_instance⟩

instance multiplicative.is_submonoid
  (s : set β) : ∀ [is_add_submonoid s], @is_submonoid (multiplicative β) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem multiplicative.is_submonoid_iff
  {s : set β} : @is_submonoid (multiplicative β) _ s ↔ is_add_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by resetI; apply_instance⟩

section powers

def powers (x : α) : set α := {y | ∃ n:ℕ, x^n = y}
def multiples (x : β) : set β := {y | ∃ n:ℕ, add_monoid.smul n x = y}
attribute [to_additive multiples] powers

instance powers.is_submonoid (x : α) : is_submonoid (powers x) :=
{ one_mem := ⟨0, by simp⟩,
  mul_mem := λ x₁ x₂ ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩, ⟨n₁ + n₂, by simp [pow_add, *]⟩ }

instance multiples.is_add_submonoid (x : β) : is_add_submonoid (multiples x) :=
multiplicative.is_submonoid_iff.1 $ powers.is_submonoid _
attribute [to_additive multiples.is_add_submonoid] powers.is_submonoid

lemma is_submonoid.pow_mem {a : α} [is_submonoid s] (h : a ∈ s) : ∀ {n : ℕ}, a ^ n ∈ s
| 0 := is_submonoid.one_mem s
| (n + 1) := is_submonoid.mul_mem h is_submonoid.pow_mem

lemma is_add_submonoid.smul_mem {a : β} [is_add_submonoid t] :
  ∀ (h : a ∈ t) {n : ℕ}, add_monoid.smul n a ∈ t :=
@is_submonoid.pow_mem (multiplicative β) _ _ _ _
attribute [to_additive is_add_submonoid.smul_mem] is_submonoid.pow_mem

lemma is_submonoid.power_subset {a : α} [is_submonoid s] (h : a ∈ s) : powers a ⊆ s :=
assume x ⟨n, hx⟩, hx ▸ is_submonoid.pow_mem h

lemma is_add_submonoid.multiple_subset {a : β} [is_add_submonoid t] :
  a ∈ t → multiples a ⊆ t :=
@is_submonoid.power_subset (multiplicative β) _ _ _ _
attribute [to_additive is_add_submonoid.multiple_subset] is_add_submonoid.multiple_subset

end powers

@[to_additive is_add_submonoid.list_sum_mem]
lemma is_submonoid.list_prod_mem [is_submonoid s] : ∀{l : list α}, (∀x∈l, x ∈ s) → l.prod ∈ s
| []     h := is_submonoid.one_mem s
| (a::l) h :=
  suffices a * l.prod ∈ s, by simpa,
  have a ∈ s ∧ (∀x∈l, x ∈ s), by simpa using h,
  is_submonoid.mul_mem this.1 (is_submonoid.list_prod_mem this.2)

instance subtype.monoid {s : set α} [is_submonoid s] : monoid s :=
{ mul       := λ a b : s, ⟨a * b, is_submonoid.mul_mem a.2 b.2⟩,
  one       := ⟨1, is_submonoid.one_mem s⟩,
  mul_assoc := λ a b c, subtype.eq $ mul_assoc _ _ _,
  one_mul   := λ a, subtype.eq $ one_mul _,
  mul_one   := λ a, subtype.eq $ mul_one _ }
attribute [to_additive subtype.add_monoid._proof_1] subtype.monoid._proof_1
attribute [to_additive subtype.add_monoid._proof_2] subtype.monoid._proof_2
attribute [to_additive subtype.add_monoid._proof_3] subtype.monoid._proof_3
attribute [to_additive subtype.add_monoid._proof_4] subtype.monoid._proof_4
attribute [to_additive subtype.add_monoid] subtype.monoid

namespace monoid

inductive in_closure (s : set α) : α → Prop
| basic {a : α} : a ∈ s → in_closure a
| one : in_closure 1
| mul {a b : α} : in_closure a → in_closure b → in_closure (a * b)

def closure (s : set α) : set α := {a | in_closure s a }

instance closure.is_submonoid (s : set α) : is_submonoid (closure s) :=
{ one_mem := in_closure.one s, mul_mem := assume a b, in_closure.mul }

theorem subset_closure {s : set α} : s ⊆ closure s :=
assume a, in_closure.basic

theorem closure_subset {s t : set α} [is_submonoid t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, is_submonoid.one_mem, is_submonoid.mul_mem]

theorem exists_list_of_mem_closure {s : set α} {a : α} (h : a ∈ closure s) :
  (∃l:list α, (∀x∈l, x ∈ s) ∧ l.prod = a) :=
begin
  induction h,
  case in_closure.basic : a ha { existsi ([a]), simp [ha] },
  case in_closure.one { existsi ([]), simp },
  case in_closure.mul : a b _ _ ha hb {
    rcases ha with ⟨la, ha, eqa⟩,
    rcases hb with ⟨lb, hb, eqb⟩,
    existsi (la ++ lb),
    simp [eqa.symm, eqb.symm, or_imp_distrib],
    exact assume a, ⟨ha a, hb a⟩
  }
end

end monoid

namespace add_monoid

def closure (s : set β) : set β := @monoid.closure (multiplicative β) _ s

instance closure.is_add_submonoid (s : set β) : is_add_submonoid (closure s) :=
multiplicative.is_submonoid_iff.1 $ monoid.closure.is_submonoid s

theorem subset_closure {s : set β} : s ⊆ closure s :=
@monoid.subset_closure (multiplicative β) _ _

theorem closure_subset {s t : set β} [is_add_submonoid t] : s ⊆ t → closure s ⊆ t :=
@monoid.closure_subset (multiplicative β) _ _ _ _

theorem exists_list_of_mem_closure {s : set β} {a : β} :
  a ∈ closure s → ∃l:list β, (∀x∈l, x ∈ s) ∧ l.sum = a :=
@monoid.exists_list_of_mem_closure (multiplicative β) _ _ _

end add_monoid
