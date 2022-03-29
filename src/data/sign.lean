/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import order.basic
import algebra.algebra.basic
import tactic.derive_fintype

/-!
# Sign function

This file defines the sign function for types with zero and a decidable less-than relation, and
proves some basic theorems about it.
-/

/-- The type of signs. -/
@[derive [decidable_eq, inhabited, fintype]]
inductive sign_type
| zero | neg | pos

namespace sign_type

instance : has_zero sign_type := ⟨zero⟩
instance :  has_one sign_type := ⟨pos⟩

instance : has_neg sign_type :=
⟨λ s, match s with
| neg  := pos
| zero := zero
| pos  := neg
end⟩

@[simp] lemma zero_eq_zero   : zero = 0 := rfl
@[simp] lemma neg_eq_neg_one : neg = -1 := rfl
@[simp] lemma pos_eq_one     : pos = 1  := rfl

/-- The multiplication on `sign_type`. -/
def mul : sign_type → sign_type → sign_type
| neg neg  := pos
| neg zero := zero
| neg pos  := neg
| zero _   := zero
| pos h    := h

instance : has_mul sign_type := ⟨mul⟩

/-- The less-than relation on signs. -/
inductive le : sign_type → sign_type → Prop
| of_neg (a) : le neg a
| zero       : le zero zero
| of_pos (a) : le a pos

instance : has_le sign_type := ⟨le⟩

instance : decidable_rel le :=
λ a b, by cases a; cases b; exact is_false (by rintro ⟨⟩) <|> exact is_true (by constructor)

/- We can define a `field` instance on `sign_type`, but it's not mathematically sensible,
so we only define the `comm_group_with_zero`. -/
instance : comm_group_with_zero sign_type :=
{ zero            := 0,
  one             := 1,
  mul             := (*),
  inv             := id,
  mul_zero        := λ a, by cases a; refl,
  zero_mul        := λ a, by cases a; refl,
  mul_one         := λ a, by cases a; refl,
  one_mul         := λ a, by cases a; refl,
  mul_inv_cancel  := λ a ha,  by cases a; trivial,
  mul_comm        := λ a b,   by casesm* _; refl,
  mul_assoc       := λ a b c, by casesm* _; refl,
  exists_pair_ne  := ⟨0, 1,   by rintro ⟨⟩⟩,
  inv_zero        := rfl }

instance : linear_order sign_type :=
{ le           := (≤),
  le_refl      := λ a, by cases a; constructor,
  le_total     := λ a b, by casesm* _; dec_trivial,
  le_antisymm  := λ a b ha hb, by casesm* _; refl,
  le_trans     := λ a b c hab hbc, by casesm* _; constructor,
  decidable_le := le.decidable_rel }

instance : has_distrib_neg sign_type :=
{ neg_neg := λ x, by cases x; refl,
  neg_mul := λ x y, by casesm* _; refl,
  mul_neg := λ x y, by casesm* _; refl,
..sign_type.has_neg }

@[simp] lemma neg_zero {α} [mul_zero_class α] [has_distrib_neg α] : (-0 : α) = 0 :=
begin
  nth_rewrite 0 [←zero_mul (0 : α)],
  rw [←neg_mul, mul_zero]
end

/-- `sign_type` is equivalent to `fin 3`. -/
def fin3_equiv : sign_type ≃* fin 3 :=
{ to_fun :=  λ a, a.rec_on 0 (-1) 1,
  inv_fun := λ a, match a with
    | ⟨0, h⟩   := 0
    | ⟨1, h⟩   := 1
    | ⟨2, h⟩   := -1
    | ⟨n+3, h⟩ := (h.not_le le_add_self).elim
  end,
  left_inv :=  λ a, by cases a; refl,
  right_inv := λ a, match a with
    | ⟨0, h⟩   := rfl
    | ⟨1, h⟩   := rfl
    | ⟨2, h⟩   := rfl
    | ⟨n+3, h⟩ := (h.not_le le_add_self).elim
  end,
  map_mul' := λ x y, by casesm* _; refl }

/-- Turn a `sign_type` into zero, one, or minus one. This is a coercion instance, not note it is
only a `has_coe_t` instance: see note [use has_coe_t]. -/
def cast {α} [has_zero α] [has_one α] [has_neg α] : sign_type → α
| zero :=  0
| pos  :=  1
| neg  := -1

@[simp] lemma cast_zero    {α} [has_zero α] [has_one α] [has_neg α] : cast 0 = (0 : α) := rfl
@[simp] lemma cast_one     {α} [has_zero α] [has_one α] [has_neg α] : cast 1 = (1 : α) := rfl
@[simp] lemma cast_neg_one {α} [has_zero α] [has_one α] [has_neg α] : cast (-1) = (-1 : α) := rfl

instance {α} [has_zero α] [has_one α] [has_neg α] : has_coe_t sign_type α := ⟨cast⟩

/-- `sign_type.cast` as a `mul_with_zero_hom`. -/
@[simps] def cast_hom {α} [mul_zero_one_class α] [has_distrib_neg α] : sign_type →*₀ α :=
{ to_fun    := cast,
  map_zero' := rfl,
  map_one'  := rfl,
  map_mul'  := λ x y, by cases x; cases y; simp }

end sign_type

variables {α : Type*}

open sign_type

section preorder

variables [has_zero α] [preorder α] [decidable_rel ((<) : α → α → Prop)] {a : α}

/-- The sign of an element is 1 if it's positive, -1 if negative, 0 otherwise. -/
def sign : α →o sign_type :=
⟨λ a, if 0 < a then 1 else if a < 0 then -1 else 0, λ a b h, begin
  dsimp,
  split_ifs; try {constructor},
  { cases lt_irrefl 0 (h_1.trans $ h.trans_lt h_3) },
  { cases h_2 (h_1.trans_le h) },
  { cases h_2 (h.trans_lt h_4) }
  end⟩

lemma sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0) := rfl

@[simp] lemma sign_zero : sign (0 : α) = 0 := by simp [sign_apply]
@[simp] lemma sign_pos (ha : 0 < a) :  sign a = 1 := by rwa [sign_apply, if_pos]
@[simp] lemma sign_neg (ha : a < 0) : sign a = -1 := by rwa [sign_apply, if_neg $ asymm ha, if_pos]

end preorder

section linear_order

variables [has_zero α] [linear_order α] {a : α}

lemma sign_ne_zero (h : a ≠ 0) : sign a ≠ 0 :=
begin
  contrapose! h,
  rw sign_apply at h,
  split_ifs at h,
  { cases h },
  { cases h },
  exact ((lt_trichotomy a 0).resolve_left h_2).resolve_right h_1
end

end linear_order

section linear_ordered_ring

variables [linear_ordered_ring α] {a b : α}

/- I'm not sure why this is necessary, see https://leanprover.zulipchat.com/#narrow/stream/
113488-general/topic/type.20class.20inference.20issues/near/276937942 -/
local attribute [instance] linear_ordered_ring.decidable_lt

-- TODO: determine whether `ring` is required. Current thinking is that it is, for the implication
-- a < 0 → b < 0 → 0 < a * b.
/-- `sign` as a `monoid_with_zero_hom` for a nontrivial ordered semiring. Note that linearity
is required; consider ℂ with the order `z ≤ w` iff they have the same imaginary part and
`z - w ≤ 0` in the reals; then `1 + i` and `1 - i` are incomparable to zero, and thus we have:
`0 * 0 = sign (1 + i) * sign (1 - i) ≠ sign 2 = 1`. (`complex.ordered_comm_ring`) -/
def sign_hom : α →*₀ sign_type :=
{ to_fun := sign,
  map_zero' := sign_zero,
  map_one' := sign_pos zero_lt_one,
  map_mul' := λ x y, begin
    rcases lt_trichotomy x 0 with hx | rfl | hx; rcases lt_trichotomy y 0 with hy | rfl | hy,
    any_goals { simp only [sign_zero, mul_zero, zero_mul] },
    all_goals { simp only [sign_pos, sign_neg, hx, hy, mul_one, neg_one_mul, neg_neg, one_mul] },
    { exact sign_pos (mul_pos_of_neg_of_neg hx hy) },
    { exact sign_neg (mul_neg_of_neg_of_pos hx hy) },
    { exact sign_neg (mul_neg_of_pos_of_neg hx hy) },
    { exact sign_pos (mul_pos hx hy) }
  end }

end linear_ordered_ring
