/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/
import group_theory.subgroup data.equiv.basic data.quot
open set function

variable {α : Type*}

def left_coset [has_mul α] (a : α) (s : set α) : set α := (λ x, a * x) '' s
def right_coset [has_mul α] (s : set α) (a : α) : set α := (λ x, x * a) '' s

local infix ` *l `:70 := left_coset
local infix ` *r `:70 := right_coset

section coset_mul
variable [has_mul α]

lemma mem_left_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a *l s :=
mem_image_of_mem (λ b : α, a * b) hxS

lemma mem_right_coset {s : set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ s *r a :=
mem_image_of_mem (λ b : α, b * a) hxS

def left_coset_equiv (s : set α) (a b : α) := a *l s = b *l s

lemma left_coset_equiv_rel (s : set α) : equivalence (left_coset_equiv s) :=
mk_equivalence (left_coset_equiv s) (λ a, rfl) (λ a b, eq.symm) (λ a b c, eq.trans)

end coset_mul

section coset_semigroup
variable [semigroup α]

@[simp] lemma left_coset_assoc (s : set α) (a b : α) : a *l (b *l s) = (a * b) *l s :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

@[simp] lemma right_coset_assoc (s : set α) (a b : α) : s *r a *r b = s *r (a * b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

lemma left_coset_right_coset (s : set α) (a b : α) : a *l s *r b = a *l (s *r b) :=
by simp [left_coset, right_coset, (image_comp _ _ _).symm, function.comp, mul_assoc]

end coset_semigroup

section coset_monoid
variables [monoid α] (s : set α)

@[simp] lemma one_left_coset : 1 *l s = s :=
set.ext $ by simp [left_coset]

@[simp] lemma right_coset_one : s *r 1 = s :=
set.ext $ by simp [right_coset]

end coset_monoid

section coset_submonoid
open is_submonoid
variables [monoid α] (s : set α) [is_submonoid s]

lemma mem_own_left_coset (a : α) : a ∈ a *l s :=
suffices a * 1 ∈ a *l s, by simpa,
mem_left_coset a (one_mem s)

lemma mem_own_right_coset (a : α) : a ∈ s *r a :=
suffices 1 * a ∈ s *r a, by simpa,
mem_right_coset a (one_mem s)

lemma mem_left_coset_left_coset {a : α} (ha : a *l s = s) : a ∈ s :=
by rw [←ha]; exact mem_own_left_coset s a

lemma mem_right_coset_right_coset {a : α} (ha : s *r a = s) : a ∈ s :=
by rw [←ha]; exact mem_own_right_coset s a

end coset_submonoid

section coset_group
variables [group α] {s : set α} {x : α}

lemma mem_left_coset_iff (a : α) : x ∈ a *l s ↔ a⁻¹ * x ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨a⁻¹ * x, h, by simp⟩)

lemma mem_right_coset_iff (a : α) : x ∈ s *r a ↔ x * a⁻¹ ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, by simp [eq.symm, hb])
  (assume h, ⟨x * a⁻¹, h, by simp⟩)

end coset_group

section coset_subgroup
open is_submonoid
open is_subgroup
variables [group α] (s : set α) [is_subgroup s]

lemma left_coset_mem_left_coset {a : α} (ha : a ∈ s) : a *l s = s :=
set.ext $ by simp [mem_left_coset_iff, mul_mem_cancel_right s (inv_mem ha)]

lemma right_coset_mem_right_coset {a : α} (ha : a ∈ s) : s *r a = s :=
set.ext $ assume b, by simp [mem_right_coset_iff, mul_mem_cancel_left s (inv_mem ha)]

theorem normal_of_eq_cosets [normal_subgroup s] (g : α) : g *l s = s *r g :=
set.ext $ assume a, by simp [mem_left_coset_iff, mem_right_coset_iff]; rw [mem_norm_comm_iff]

theorem eq_cosets_of_normal (h : ∀ g, g *l s = s *r g) : normal_subgroup s :=
⟨assume a ha g, show g * a * g⁻¹ ∈ s,
  by rw [← mem_right_coset_iff, ← h]; exact mem_left_coset g ha⟩

theorem normal_iff_eq_cosets : normal_subgroup s ↔ ∀ g, g *l s = s *r g :=
⟨@normal_of_eq_cosets _ _ s _, eq_cosets_of_normal s⟩

end coset_subgroup

def left_rel [group α] (s : set α) [is_subgroup s] : setoid α :=
⟨λ x y, x⁻¹ * y ∈ s,
  assume x, by simp [is_submonoid.one_mem],
  assume x y hxy,
  have (x⁻¹ * y)⁻¹ ∈ s, from is_subgroup.inv_mem hxy,
  by simpa using this,
  assume x y z hxy hyz,
  have x⁻¹ * y * (y⁻¹ * z) ∈ s, from is_submonoid.mul_mem hxy hyz,
  by simpa [mul_assoc] using this⟩

def left_cosets [group α] (s : set α) [is_subgroup s] : Type* := quotient (left_rel s)

namespace left_cosets

variables [group α] {s : set α} [is_subgroup s]

def mk (a : α) : left_cosets s :=
quotient.mk' a

instance : has_coe α (left_cosets s) := ⟨mk⟩

instance [group α] (s : set α) [is_subgroup s] : inhabited (left_cosets s) :=
⟨((1 : α) : left_cosets s)⟩

@[simp] protected lemma eq {a b : α} : (a : left_cosets s) = b ↔ a⁻¹ * b ∈ s :=
quotient.eq'

lemma eq_class_eq_left_coset [group α] (s : set α) [is_subgroup s] (g : α) : 
  {x : α | (x : left_cosets s) = g} = left_coset g s :=
set.ext $ λ z, by simp [eq_comm, mem_left_coset_iff]; refl

end left_cosets

namespace is_subgroup
variables [group α] {s : set α}

def left_coset_equiv_subgroup (g : α) : left_coset g s ≃ s :=
⟨λ x, ⟨g⁻¹ * x.1, (mem_left_coset_iff _).1 x.2⟩,
 λ x, ⟨g * x.1, x.1, x.2, rfl⟩,
 λ ⟨x, hx⟩, subtype.eq $ by simp,
 λ ⟨g, hg⟩, subtype.eq $ by simp⟩

local attribute [instance] left_rel

noncomputable def group_equiv_left_cosets_times_subgroup (hs : is_subgroup s) :
  α ≃ (left_cosets s × s) :=
calc α ≃ Σ L : left_cosets s, {x : α // (x : left_cosets s)= L} :
  equiv.equiv_fib left_cosets.mk
    ... ≃ Σ L : left_cosets s, left_coset (quotient.out' L) s :
  equiv.sigma_congr_right (λ L, 
    begin rw ← left_cosets.eq_class_eq_left_coset, 
      show {x // quotient.mk' x = L} ≃ {x : α // quotient.mk' x = quotient.mk' _},
      simp [-quotient.eq']
    end)
    ... ≃ Σ L : left_cosets s, s :
  equiv.sigma_congr_right (λ L, left_coset_equiv_subgroup _)
    ... ≃ (left_cosets s × s) :
  equiv.sigma_equiv_prod _ _

end is_subgroup

namespace left_cosets

instance [group α] (s : set α) [normal_subgroup s] : group (left_cosets s) :=
{ one := (1 : α),
  mul := λ a b, quotient.lift_on₂' a b
    (λ a b, ((a * b : α) : left_cosets s))
  (λ a₁ a₂ b₁ b₂ hab₁ hab₂,
      quot.sound
    ((is_subgroup.mul_mem_cancel_left s (is_subgroup.inv_mem hab₂)).1
        (by rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (a₂⁻¹ * a₁⁻¹),
          mul_assoc _ b₂, ← mul_assoc b₂, mul_inv_self, one_mul, mul_assoc (a₂⁻¹)];
          exact normal_subgroup.normal _ hab₁ _))),
  mul_assoc := λ a b c, quotient.induction_on₃' a b c 
    (λ a b c, congr_arg mk (mul_assoc a b c)), 
  one_mul := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (one_mul a)),
  mul_one := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_one a)),
  inv := λ a, quotient.lift_on' a (λ a, ((a⁻¹ : α) : left_cosets s))
    (λ a b hab, quotient.sound' begin
      show a⁻¹⁻¹ * b⁻¹ ∈ s,
      rw ← mul_inv_rev,
      exact is_subgroup.inv_mem (is_subgroup.mem_norm_comm hab)
    end),
  mul_left_inv := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_left_inv a)) }

instance [group α] (s : set α) [normal_subgroup s] :
  is_group_hom (mk : α → left_cosets s) := ⟨λ _ _, rfl⟩

instance [comm_group α] (s : set α) [normal_subgroup s] : comm_group (left_cosets s) :=
{ mul_comm := λ a b, quotient.induction_on₂' a b 
    (λ a b, congr_arg mk (mul_comm a b)),
  ..left_cosets.group s }

@[simp] lemma coe_one [group α] (s : set α) [normal_subgroup s] : 
  ((1 : α) : left_cosets s) = 1 := rfl

@[simp] lemma coe_mul [group α] (s : set α) [normal_subgroup s] (a b : α) :
  ((a * b : α) : left_cosets s) = a * b := rfl

@[simp] lemma coe_inv [group α] (s : set α) [normal_subgroup s] (a : α) :
  ((a⁻¹ : α) : left_cosets s) = a⁻¹ := rfl

@[simp] lemma coe_pow [group α] (s : set α) [normal_subgroup s] (a : α) (n : ℕ) :
  ((a ^ n : α) : left_cosets s) = a ^ n := @is_group_hom.pow _ _ _ _ mk _ a n

@[simp] lemma coe_gpow [group α] (s : set α) [normal_subgroup s] (a : α) (n : ℤ) :
  ((a ^ n : α) : left_cosets s) = a ^ n := @is_group_hom.gpow _ _ _ _ mk _ a n

end left_cosets