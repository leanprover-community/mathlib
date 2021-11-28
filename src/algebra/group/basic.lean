/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/

import algebra.group.defs
import logic.function.basic

/-!
# Basic lemmas about semigroups, monoids, and groups

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`algebra/group/defs.lean`.
-/

universe u

section associative
variables {α : Type u} (f : α → α → α) [is_associative α f] (x y : α)

/--
Composing two associative operations of `f : α → α → α` on the left
is equal to an associative operation on the left.
-/
lemma comp_assoc_left : (f x) ∘ (f y) = (f (f x y)) :=
by { ext z, rw [function.comp_apply, @is_associative.assoc _ f] }

/--
Composing two associative operations of `f : α → α → α` on the right
is equal to an associative operation on the right.
-/
lemma comp_assoc_right : (λ z, f z x) ∘ (λ z, f z y) = (λ z, f z (f y x)) :=
by { ext z, rw [function.comp_apply, @is_associative.assoc _ f] }

end associative

section semigroup
variables {α : Type*}

/--
Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[simp, to_additive
"Composing two additions on the left by `y` then `x`
is equal to a addition on the left by `x + y`."]
lemma comp_mul_left [semigroup α] (x y : α) :
  ((*) x) ∘ ((*) y) = ((*) (x * y)) :=
comp_assoc_left _ _ _

/--
Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[simp, to_additive
"Composing two additions on the right by `y` and `x`
is equal to a addition on the right by `y + x`."]
lemma comp_mul_right [semigroup α] (x y : α) :
  (* x) ∘ (* y) = (* (y * x)) :=
comp_assoc_right _ _ _

end semigroup

section mul_one_class
variables {M : Type u} [mul_one_class M]

@[to_additive]
lemma ite_mul_one {P : Prop} [decidable P] {a b : M} :
  ite P (a * b) 1 = ite P a 1 * ite P b 1 :=
by { by_cases h : P; simp [h], }

@[to_additive]
lemma ite_one_mul {P : Prop} [decidable P] {a b : M} :
  ite P 1 (a * b) = ite P 1 a * ite P 1 b :=
by { by_cases h : P; simp [h], }

@[to_additive]
lemma eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 :=
by split; { rintro rfl, simpa using h }

@[to_additive]
lemma one_mul_eq_id : ((*) (1 : M)) = id := funext one_mul

@[to_additive]
lemma mul_one_eq_id : (* (1 : M)) = id := funext mul_one

end mul_one_class

section comm_semigroup
variables {G : Type u} [comm_semigroup G]

@[no_rsimp, to_additive]
lemma mul_left_comm : ∀ a b c : G, a * (b * c) = b * (a * c) :=
left_comm has_mul.mul mul_comm mul_assoc

@[to_additive]
lemma mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
right_comm has_mul.mul mul_comm mul_assoc

@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : (a * b) * (c * d) = (a * c) * (b * d) :=
by simp only [mul_left_comm, mul_assoc]

end comm_semigroup

local attribute [simp] mul_assoc sub_eq_add_neg

section add_monoid
variables {M : Type u} [add_monoid M] {a b c : M}

@[simp] lemma bit0_zero : bit0 (0 : M) = 0 := add_zero _
@[simp] lemma bit1_zero [has_one M] : bit1 (0 : M) = 1 :=
by rw [bit1, bit0_zero, zero_add]

end add_monoid

section comm_monoid
variables {M : Type u} [comm_monoid M] {x y z : M}

@[to_additive] lemma inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
left_inv_eq_right_inv (trans (mul_comm _ _) hy) hz

end comm_monoid

section left_cancel_monoid

variables {M : Type u} [left_cancel_monoid M] {a b : M}

@[simp, to_additive] lemma mul_right_eq_self : a * b = a ↔ b = 1 :=
calc a * b = a ↔ a * b = a * 1 : by rw mul_one
           ... ↔ b = 1         : mul_left_cancel_iff

@[simp, to_additive] lemma self_eq_mul_right : a = a * b ↔ b = 1 :=
eq_comm.trans mul_right_eq_self

end left_cancel_monoid

section right_cancel_monoid

variables {M : Type u} [right_cancel_monoid M] {a b : M}

@[simp, to_additive] lemma mul_left_eq_self : a * b = b ↔ a = 1 :=
calc a * b = b ↔ a * b = 1 * b : by rw one_mul
           ... ↔ a = 1         : mul_right_cancel_iff

@[simp, to_additive] lemma self_eq_mul_left : b = a * b ↔ a = 1 :=
eq_comm.trans mul_left_eq_self

end right_cancel_monoid

section div_inv_monoid

variables {G : Type u} [div_inv_monoid G]

@[to_additive]
lemma inv_eq_one_div (x : G) :
  x⁻¹ = 1 / x :=
by rw [div_eq_mul_inv, one_mul]

@[to_additive]
lemma mul_one_div (x y : G) :
  x * (1 / y) = x / y :=
by rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

@[to_additive]
lemma mul_div_assoc (a b c : G) : a * b / c = a * (b / c) :=
by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]

@[to_additive]
lemma mul_div_assoc' (a b c : G) : a * (b / c) = (a * b) / c :=
(mul_div_assoc _ _ _).symm

@[simp, to_additive] lemma one_div (a : G) : 1 / a = a⁻¹ :=
(inv_eq_one_div a).symm

end div_inv_monoid

section group
variables {G : Type u} [group G] {a b c d : G}

@[simp, to_additive]
lemma inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a :=
by simp [mul_assoc]

@[simp, to_additive neg_zero]
lemma one_inv : 1⁻¹ = (1 : G) :=
inv_eq_of_mul_eq_one (one_mul 1)

@[to_additive]
theorem left_inverse_inv (G) [group G] :
  function.left_inverse (λ a : G, a⁻¹) (λ a, a⁻¹) :=
inv_inv

@[simp, to_additive]
lemma inv_involutive : function.involutive (has_inv.inv : G → G) := inv_inv

@[simp, to_additive]
lemma inv_surjective : function.surjective (has_inv.inv : G → G) :=
inv_involutive.surjective

@[to_additive]
lemma inv_injective : function.injective (has_inv.inv : G → G) :=
inv_involutive.injective

@[simp, to_additive] theorem inv_inj : a⁻¹ = b⁻¹ ↔ a = b := inv_injective.eq_iff

@[simp, to_additive]
lemma mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b :=
by rw [← mul_assoc, mul_right_inv, one_mul]

@[to_additive]
theorem mul_left_surjective (a : G) : function.surjective ((*) a) :=
λ x, ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩

@[to_additive]
theorem mul_right_surjective (a : G) : function.surjective (λ x, x * a) :=
λ x, ⟨x * a⁻¹, inv_mul_cancel_right x a⟩

@[simp, to_additive neg_add_rev]
lemma mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
inv_eq_of_mul_eq_one $ by simp

@[to_additive]
lemma eq_inv_of_eq_inv (h : a = b⁻¹) : b = a⁻¹ :=
by simp [h]

@[to_additive]
lemma eq_inv_of_mul_eq_one (h : a * b = 1) : a = b⁻¹ :=
have a⁻¹ = b, from inv_eq_of_mul_eq_one h,
by simp [this.symm]

@[to_additive]
lemma eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ :=
by simp [h.symm]

@[to_additive]
lemma eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c :=
by simp [h.symm]

@[to_additive]
lemma inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c :=
by simp [h]

@[to_additive]
lemma mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c :=
by simp [h]

@[to_additive]
lemma eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c :=
by simp [h.symm]

@[to_additive]
lemma eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c :=
by simp [h.symm, mul_inv_cancel_left]

@[to_additive]
lemma mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c :=
by rw [h, mul_inv_cancel_left]

@[to_additive]
lemma mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c :=
by simp [h]

@[simp, to_additive]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
by rw [← @inv_inj _ _ a 1, one_inv]

@[simp, to_additive]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
by rw [eq_comm, inv_eq_one]

@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
not_congr inv_eq_one

@[to_additive]
theorem eq_inv_iff_eq_inv : a = b⁻¹ ↔ b = a⁻¹ :=
⟨eq_inv_of_eq_inv, eq_inv_of_eq_inv⟩

@[to_additive]
theorem inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
eq_comm.trans $ eq_inv_iff_eq_inv.trans eq_comm

@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
⟨eq_inv_of_mul_eq_one, λ h, by rw [h, mul_left_inv]⟩

@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b :=
by rw [mul_eq_one_iff_eq_inv, eq_inv_iff_eq_inv, eq_comm]

@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
mul_eq_one_iff_eq_inv.symm

@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
mul_eq_one_iff_inv_eq.symm

@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
⟨λ h, by rw [h, inv_mul_cancel_right], λ h, by rw [← h, mul_inv_cancel_right]⟩

@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
⟨λ h, by rw [h, mul_inv_cancel_left], λ h, by rw [← h, inv_mul_cancel_left]⟩

@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
⟨λ h, by rw [← h, mul_inv_cancel_left], λ h, by rw [h, inv_mul_cancel_left]⟩

@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
⟨λ h, by rw [← h, inv_mul_cancel_right], λ h, by rw [h, mul_inv_cancel_right]⟩

@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b :=
by rw [mul_eq_one_iff_eq_inv, inv_inv]

@[to_additive]
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b :=
by rw [mul_eq_one_iff_eq_inv, inv_inj]

@[to_additive]
lemma div_left_injective : function.injective (λ a, a / b) :=
by simpa only [div_eq_mul_inv] using λ a a' h, mul_left_injective (b⁻¹) h

@[to_additive]
lemma div_right_injective : function.injective (λ a, b / a) :=
by simpa only [div_eq_mul_inv] using λ a a' h, inv_injective (mul_right_injective b h)

-- The unprimed version is used by `group_with_zero`.  This is the preferred choice.
-- See https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/.60div_one'.60
@[simp, to_additive sub_zero]
lemma div_one' (a : G) : a / 1 = a :=
calc  a / 1 = a * 1⁻¹ : div_eq_mul_inv a 1
          ... = a * 1 : congr_arg _ one_inv
          ... = a     : mul_one a

@[simp, to_additive neg_sub]
lemma inv_div' (a b : G) : (a / b)⁻¹ = b / a :=
inv_eq_of_mul_eq_one ( by rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc, inv_mul_cancel_left,
  mul_right_inv])

@[simp, to_additive sub_add_cancel]
lemma div_mul_cancel' (a b : G) : a / b * b = a :=
by rw [div_eq_mul_inv, inv_mul_cancel_right a b]

@[simp, to_additive sub_self] lemma div_self' (a : G) : a / a = 1 :=
by rw [div_eq_mul_inv, mul_right_inv a]

@[simp, to_additive add_sub_cancel] lemma mul_div_cancel'' (a b : G) : a * b / b = a :=
by rw [div_eq_mul_inv, mul_inv_cancel_right a b]

@[to_additive eq_of_sub_eq_zero] lemma eq_of_div_eq_one' (h : a / b = 1) : a = b :=
calc a = a / b * b : (div_mul_cancel' a b).symm
   ... = b         : by rw [h, one_mul]

@[to_additive] lemma div_ne_one_of_ne (h : a ≠ b) : a / b ≠ 1 :=
mt eq_of_div_eq_one' h

@[simp, to_additive] lemma div_inv_eq_mul (a b : G) : a / (b⁻¹) = a * b :=
by rw [div_eq_mul_inv, inv_inv]

local attribute [simp] mul_assoc

@[to_additive] lemma mul_div (a b c : G) : a * (b / c) = a * b / c :=
by simp only [mul_assoc, div_eq_mul_inv]

@[to_additive] lemma div_mul_eq_div_div_swap (a b c : G) : a / (b * c) = a / c / b :=
by simp only [mul_assoc, mul_inv_rev , div_eq_mul_inv]

@[simp, to_additive] lemma mul_div_mul_right_eq_div (a b c : G) : (a * c) / (b * c) = a / b :=
by rw [div_mul_eq_div_div_swap]; simp only [mul_left_inj, eq_self_iff_true, mul_div_cancel'']

@[to_additive eq_sub_of_add_eq] lemma eq_div_of_mul_eq' (h : a * c = b) : a = b / c :=
by simp [← h]

@[to_additive sub_eq_of_eq_add] lemma div_eq_of_eq_mul'' (h : a = c * b) : a / b = c :=
by simp [h]

@[to_additive] lemma eq_mul_of_div_eq (h : a / c = b) : a = b * c :=
by simp [← h]

@[to_additive] lemma mul_eq_of_eq_div (h : a = c / b) : a * b = c :=
by simp [h]

@[simp, to_additive] lemma div_right_inj : a / b = a / c ↔ b = c :=
div_right_injective.eq_iff

@[simp, to_additive] lemma div_left_inj : b / a = c / a ↔ b = c :=
by { rw [div_eq_mul_inv, div_eq_mul_inv], exact mul_left_inj _ }

@[to_additive sub_add_sub_cancel] lemma div_mul_div_cancel' (a b c : G) : (a / b) * (b / c) = a / c
:= by rw [← mul_div_assoc, div_mul_cancel']

@[to_additive sub_sub_sub_cancel_right] lemma div_div_div_cancel_right' (a b c : G) :
(a / c) / (b / c) = a / b := by rw [← inv_div' c b, div_inv_eq_mul, div_mul_div_cancel']

@[to_additive] theorem div_div_assoc_swap : a / (b / c) = a * c / b :=
by simp only [mul_assoc, mul_inv_rev, inv_inv, div_eq_mul_inv]

@[to_additive] theorem div_eq_one : a / b = 1 ↔ a = b :=
⟨eq_of_div_eq_one', λ h, by rw [h, div_self']⟩

alias div_eq_one ↔ _ div_eq_one_of_eq
alias sub_eq_zero ↔ _ sub_eq_zero_of_eq

@[to_additive] theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
not_congr div_eq_one

@[simp, to_additive] theorem div_eq_self : a / b = a ↔ b = 1 :=
by rw [div_eq_mul_inv, mul_right_eq_self, inv_eq_one]

@[to_additive eq_sub_iff_add_eq] theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b :=
by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]

@[to_additive] theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b :=
by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]

@[to_additive] theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d :=
by rw [← div_eq_one, H, div_eq_one]

@[to_additive]
theorem left_inverse_div_mul_left (c : G) : function.left_inverse (λ x, x / c) (λ x, x * c) :=
assume x, mul_div_cancel'' x c

@[to_additive]
theorem left_inverse_mul_left_div (c : G) : function.left_inverse (λ x, x * c) (λ x, x / c) :=
assume x, div_mul_cancel' x c

@[to_additive]
theorem left_inverse_mul_right_inv_mul (c : G) :
  function.left_inverse (λ x, c * x) (λ x, c⁻¹ * x) :=
assume x, mul_inv_cancel_left c x

@[to_additive]
theorem left_inverse_inv_mul_mul_right (c : G) :
  function.left_inverse (λ x, c⁻¹ * x) (λ x, c * x) :=
assume x, inv_mul_cancel_left c x

end group

section comm_group
variables {G : Type u} [comm_group G]

@[to_additive neg_add]
lemma mul_inv (a b : G) : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
by rw [mul_inv_rev, mul_comm]

@[to_additive]
lemma div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c :=
by rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]

@[to_additive]
lemma div_mul_comm (a b c d : G) : a / b * (c / d) = a * c / (b * d) :=
by rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_assoc,
  mul_left_cancel_iff, mul_comm, mul_assoc]

end comm_group

section add_comm_group
-- TODO: Generalize the contents of this section with to_additive as per
-- https://leanprover.zulipchat.com/#narrow/stream/144837-PR-reviews/topic/.238667
variables {G : Type u} [add_comm_group G] {a b c d : G}

local attribute [simp] add_assoc add_comm add_left_comm sub_eq_add_neg

lemma sub_add_eq_sub_sub (a b c : G) : a - (b + c) = a - b - c :=
by simp

lemma neg_add_eq_sub (a b : G) : -a + b = b - a :=
by simp

lemma sub_add_eq_add_sub (a b c : G) : a - b + c = a + c - b :=
by simp

lemma sub_sub (a b c : G) : a - b - c = a - (b + c) :=
by simp

lemma sub_add (a b c : G) : a - b + c = a - (b - c) :=
by simp

@[simp] lemma add_sub_add_left_eq_sub (a b c : G) : (c + a) - (c + b) = a - b :=
by simp

lemma eq_sub_of_add_eq' (h : c + a = b) : a = b - c :=
by simp [h.symm]

lemma eq_add_of_sub_eq' (h : a - b = c) : a = b + c :=
by simp [h.symm]

lemma add_eq_of_eq_sub' (h : b = c - a) : a + b = c :=
begin simp [h], rw [add_comm c, add_neg_cancel_left] end

lemma sub_sub_self (a b : G) : a - (a - b) = b :=
by simpa using add_neg_cancel_left a b

lemma add_sub_comm (a b c d : G) : a + b - (c + d) = (a - c) + (b - d) :=
by simp

lemma sub_eq_sub_add_sub (a b c : G) : a - b = c - b + (a - c) :=
begin simp, rw [add_left_comm c], simp end

lemma neg_neg_sub_neg (a b : G) : - (-a - -b) = a - b :=
by simp

@[simp] lemma sub_sub_cancel (a b : G) : a - (a - b) = b := sub_sub_self a b

@[simp] lemma sub_sub_cancel_left (a b : G) : a - b - a = -b := by simp

lemma sub_eq_neg_add (a b : G) : a - b = -b + a :=
by rw [sub_eq_add_neg, add_comm _ _]

theorem neg_add' (a b : G) : -(a + b) = -a - b :=
by rw [sub_eq_add_neg, neg_add a b]

@[simp]
lemma neg_sub_neg (a b : G) : -a - -b = b - a :=
by simp [sub_eq_neg_add, add_comm]

lemma eq_sub_iff_add_eq' : a = b - c ↔ c + a = b :=
by rw [eq_sub_iff_add_eq, add_comm]

lemma sub_eq_iff_eq_add' : a - b = c ↔ a = b + c :=
by rw [sub_eq_iff_eq_add, add_comm]

@[simp]
lemma add_sub_cancel' (a b : G) : a + b - a = b :=
by rw [sub_eq_neg_add, neg_add_cancel_left]

@[simp]
lemma add_sub_cancel'_right (a b : G) : a + (b - a) = b :=
by rw [← add_sub_assoc, add_sub_cancel']

@[simp] lemma sub_add_cancel' (a b : G) : a - (a + b) = -b :=
by rw [← neg_sub, add_sub_cancel']

-- This lemma is in the `simp` set under the name `add_neg_cancel_comm_assoc`,
-- defined  in `algebra/group/commute`
lemma add_add_neg_cancel'_right (a b : G) : a + (b + -a) = b :=
by rw [← sub_eq_add_neg, add_sub_cancel'_right a b]

lemma sub_right_comm (a b c : G) : a - b - c = a - c - b :=
by { repeat { rw sub_eq_add_neg }, exact add_right_comm _ _ _ }

@[simp] lemma add_add_sub_cancel (a b c : G) : (a + c) + (b - c) = a + b :=
by rw [add_assoc, add_sub_cancel'_right]

@[simp] lemma sub_add_add_cancel (a b c : G) : (a - c) + (b + c) = a + b :=
by rw [add_left_comm, sub_add_cancel, add_comm]

@[simp] lemma sub_add_sub_cancel' (a b c : G) : (a - b) + (c - a) = c - b :=
by rw add_comm; apply sub_add_sub_cancel

@[simp] lemma add_sub_sub_cancel (a b c : G) : (a + b) - (a - c) = b + c :=
by rw [← sub_add, add_sub_cancel']

@[simp] lemma sub_sub_sub_cancel_left (a b c : G) : (c - a) - (c - b) = b - a :=
by rw [← neg_sub b c, sub_neg_eq_add, add_comm, sub_add_sub_cancel]

lemma sub_eq_sub_iff_add_eq_add : a - b = c - d ↔ a + d = c + b :=
begin
  rw [sub_eq_iff_eq_add, sub_add_eq_add_sub, eq_comm, sub_eq_iff_eq_add'],
  simp only [add_comm, eq_comm]
end

lemma sub_eq_sub_iff_sub_eq_sub : a - b = c - d ↔ a - c = b - d :=
by rw [sub_eq_iff_eq_add, sub_add_eq_add_sub, sub_eq_iff_eq_add', add_sub_assoc]

end add_comm_group
