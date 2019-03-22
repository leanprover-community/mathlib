/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.set.finite group_theory.coset

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)

infixr ` • `:73 := has_scalar.smul

class monoid_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one : ∀ b : β, (1 : α) • b = b)
(mul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)

namespace monoid_action

variables (α) [monoid α] [monoid_action α β]

def orbit (b : β) := set.range (λ x : α, x • b)

variable {α}

@[simp] lemma mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
iff.rfl

@[simp] lemma mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
⟨x, rfl⟩

@[simp] lemma mem_orbit_self (b : β) : b ∈ orbit α b :=
⟨1, by simp [monoid_action.one]⟩

instance orbit_fintype (b : β) [fintype α] [decidable_eq β] :
  fintype (orbit α b) := set.fintype_range _

variable (α)

def stabilizer (b : β) : set α :=
{x : α | x • b = b}

variable {α}

@[simp] lemma mem_stabilizer_iff {b : β} {x : α} :
  x ∈ stabilizer α b ↔ x • b = b := iff.rfl

variables (α) (β)

def fixed_points : set β := {b : β | ∀ x, x ∈ stabilizer α b}

variables {α} (β)

@[simp] lemma mem_fixed_points {b : β} :
  b ∈ fixed_points α β ↔ ∀ x : α, x • b = b := iff.rfl

lemma mem_fixed_points' {b : β} : b ∈ fixed_points α β ↔
  (∀ b', b' ∈ orbit α b → b' = b) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, mem_stabilizer_iff.2 (h _ (mem_orbit _ _))⟩

def comp_hom [monoid γ] (g : γ → α) [is_monoid_hom g] :
  monoid_action γ β :=
{ smul := λ x b, (g x) • b,
  one := by simp [is_monoid_hom.map_one g, monoid_action.one],
  mul := by simp [is_monoid_hom.map_mul g, monoid_action.mul] }

end monoid_action

class group_action (α : Type u) (β : Type v) [group α] extends monoid_action α β

namespace group_action
variables [group α] [group_action α β]

section
open monoid_action quotient_group

variables (α) (β)

def to_perm (g : α) : equiv.perm β :=
{ to_fun := (•) g,
  inv_fun := (•) g⁻¹,
  left_inv := λ a, by rw [← monoid_action.mul, inv_mul_self, monoid_action.one],
  right_inv := λ a, by rw [← monoid_action.mul, mul_inv_self, monoid_action.one] }

variables {α} {β}

instance : is_group_hom (to_perm α β) :=
{ mul := λ x y, equiv.ext _ _ (λ a, monoid_action.mul x y a) }

lemma bijective (g : α) : function.bijective (λ b : β, g • b) :=
(to_perm α β g).bijective

lemma orbit_eq_iff {a b : β} :
   orbit α a = orbit α b ↔ a ∈ orbit α b:=
⟨λ h, h ▸ mem_orbit_self _,
λ ⟨x, (hx : x • b = a)⟩, set.ext (λ c, ⟨λ ⟨y, (hy : y • a = c)⟩, ⟨y * x,
  show (y * x) • b = c, by rwa [monoid_action.mul, hx]⟩,
  λ ⟨y, (hy : y • b = c)⟩, ⟨y * x⁻¹,
    show (y * x⁻¹) • a = c, by
      conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
        monoid_action.mul, hx]}⟩⟩)⟩

instance (b : β) : is_subgroup (stabilizer α b) :=
{ one_mem := monoid_action.one _ _,
  mul_mem := λ x y (hx : x • b = b) (hy : y • b = b),
    show (x * y) • b = b, by rw monoid_action.mul; simp *,
  inv_mem := λ x (hx : x • b = b), show x⁻¹ • b = b,
    by rw [← hx, ← monoid_action.mul, inv_mul_self, monoid_action.one, hx] }

variables (β)

def comp_hom [group γ] (g : γ → α) [is_group_hom g] :
  group_action γ β := { ..monoid_action.comp_hom β g }

variables (α)

def orbit_rel : setoid β :=
{ r := λ a b, a ∈ orbit α b,
  iseqv := ⟨mem_orbit_self, λ a b, by simp [orbit_eq_iff.symm, eq_comm],
    λ a b, by simp [orbit_eq_iff.symm, eq_comm] {contextual := tt}⟩ }

variables {β}

open quotient_group

noncomputable def orbit_equiv_quotient_stabilizer (b : β) :
  orbit α b ≃ quotient (stabilizer α b) :=
equiv.symm (@equiv.of_bijective _ _
  (λ x : quotient (stabilizer α b), quotient.lift_on' x
    (λ x, (⟨x • b, mem_orbit _ _⟩ : orbit α b))
    (λ g h (H : _ = _), subtype.eq $ (group_action.bijective (g⁻¹)).1
      $ show g⁻¹ • (g • b) = g⁻¹ • (h • b),
      by rw [← monoid_action.mul, ← monoid_action.mul,
        H, inv_mul_self, monoid_action.one]))
⟨λ g h, quotient.induction_on₂' g h (λ g h H, quotient.sound' $
  have H : g • b = h • b := subtype.mk.inj H,
  show (g⁻¹ * h) • b = b,
  by rw [monoid_action.mul, ← H, ← monoid_action.mul, inv_mul_self, monoid_action.one]),
  λ ⟨b, ⟨g, hgb⟩⟩, ⟨g, subtype.eq hgb⟩⟩)

end

open quotient_group  monoid_action is_subgroup

def mul_left_cosets (H : set α) [is_subgroup H]
  (x : α) (y : quotient H) : quotient H :=
quotient.lift_on' y (λ y, quotient_group.mk ((x : α) * y))
  (λ a b (hab : _ ∈ H), quotient_group.eq.2
    (by rwa [mul_inv_rev, ← mul_assoc, mul_assoc (a⁻¹), inv_mul_self, mul_one]))

instance (H : set α) [is_subgroup H] : group_action α (quotient H) :=
{ smul := mul_left_cosets H,
  one := λ a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [is_submonoid.one_mem])),
  mul := λ x y a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [mul_inv_rev, is_submonoid.one_mem, mul_assoc])) }

instance mul_left_cosets_comp_subtype_val (H I : set α) [is_subgroup H] [is_subgroup I] :
  group_action I (quotient H) :=
group_action.comp_hom (quotient H) (subtype.val : I → α)

end group_action
