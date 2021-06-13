/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa
-/

import algebra.covariant_and_contravariant
import order.basic

/-!
# Ordered monoids
This file develops the basics of ordered monoids.

## Implementation details
Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

## Remark
No monoid is actually present in this file: all assumptions have been generalized to `has_mul` or
`mul_one_class`.
-/

-- TODO: If possible, uniformize lemma names, taking special care of `'`,
-- after the `ordered`-refactor is done

variables {α : Type*} {a b c d : α}

section left
variables [preorder α]

section has_mul
variables [has_mul α]

@[to_additive lt_of_add_lt_add_left]
lemma lt_of_mul_lt_mul_left' [contravariant_class α α (*) (<)] :
  a * b < a * c → b < c :=
contravariant_class.elim a

variable [covariant_class α α (*) (≤)]

@[to_additive add_le_add_left]
lemma mul_le_mul_left' (h : a ≤ b) (c) :
  c * a ≤ c * b :=
covariant_class.elim c h

@[to_additive]
lemma mul_lt_of_mul_lt_left (h : a * b < c) (hle : d ≤ b) :
  a * d < c :=
(mul_le_mul_left' hle a).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_left (h : a * b ≤ c) (hle : d ≤ b) :
  a * d ≤ c :=
(mul_le_mul_left' hle a).trans h

@[to_additive]
lemma lt_mul_of_lt_mul_left (h : a < b * c) (hle : c ≤ d) :
  a < b * d :=
h.trans_le (mul_le_mul_left' hle b)

@[to_additive]
lemma le_mul_of_le_mul_left (h : a ≤ b * c) (hle : c ≤ d) :
  a ≤ b * d :=
h.trans (mul_le_mul_left' hle b)

end has_mul

-- here we start using properties of one.
section mul_one_class
variables [mul_one_class α] [covariant_class α α (*) (≤)]

@[to_additive le_add_of_nonneg_right]
lemma le_mul_of_one_le_right' (h : 1 ≤ b) : a ≤ a * b :=
by simpa only [mul_one] using mul_le_mul_left' h a

@[to_additive add_le_of_nonpos_right]
lemma mul_le_of_le_one_right' (h : b ≤ 1) : a * b ≤ a :=
by simpa only [mul_one] using mul_le_mul_left' h a

@[to_additive]
lemma lt_of_mul_lt_of_one_le_left (h : a * b < c) (hle : 1 ≤ b) : a < c :=
(le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_left (h : a * b ≤ c) (hle : 1 ≤ b) : a ≤ c :=
(le_mul_of_one_le_right' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_left (h : a < b * c) (hle : c ≤ 1) : a < b :=
h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_left (h : a ≤ b * c) (hle : c ≤ 1) : a ≤ b :=
h.trans (mul_le_of_le_one_right' hle)

end mul_one_class

end left

section right

section preorder
variables [preorder α]

section has_mul
variables [has_mul α]

@[to_additive lt_of_add_lt_add_right]
lemma lt_of_mul_lt_mul_right' [contravariant_class α α (function.swap (*)) (<)]
  (h : a * b < c * b) :
  a < c :=
contravariant_class.elim b h

variable  [covariant_class α α (function.swap (*)) (≤)]

@[to_additive add_le_add_right]
lemma mul_le_mul_right' (h : a ≤ b) (c) :
  a * c ≤ b * c :=
covariant_class.elim c h

@[to_additive]
lemma mul_lt_of_mul_lt_right (h : a * b < c) (hle : d ≤ a) :
  d * b < c :=
(mul_le_mul_right' hle b).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_right (h : a * b ≤ c) (hle : d ≤ a) :
  d * b ≤ c :=
(mul_le_mul_right' hle b).trans h

@[to_additive]
lemma lt_mul_of_lt_mul_right (h : a < b * c) (hle : b ≤ d) :
  a < d * c :=
h.trans_le (mul_le_mul_right' hle c)

@[to_additive]
lemma le_mul_of_le_mul_right (h : a ≤ b * c) (hle : b ≤ d) :
  a ≤ d * c :=
h.trans (mul_le_mul_right' hle c)

end has_mul

-- here we start using properties of one.
section mul_one_class
variables [mul_one_class α] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive le_add_of_nonneg_left]
lemma le_mul_of_one_le_left' (h : 1 ≤ b) : a ≤ b * a :=
by simpa only [one_mul] using mul_le_mul_right' h a

@[to_additive add_le_of_nonpos_left]
lemma mul_le_of_le_one_left' (h : b ≤ 1) : b * a ≤ a :=
by simpa only [one_mul] using mul_le_mul_right' h a

@[to_additive]
lemma lt_of_mul_lt_of_one_le_right (h : a * b < c) (hle : 1 ≤ a) : b < c :=
(le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_right (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
(le_mul_of_one_le_left' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_right (h : a < b * c) (hle : b ≤ 1) : a < c :=
h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_right (h : a ≤ b * c) (hle : b ≤ 1) : a ≤ c :=
h.trans (mul_le_of_le_one_left' hle)

end mul_one_class

end preorder

end right

section preorder
variables [preorder α]

section has_mul_left_right
variables [has_mul α]
  [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive add_le_add]
lemma mul_le_mul' (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)

@[to_additive]
lemma mul_le_mul_three {e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) : a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

end has_mul_left_right

-- here we start using properties of one.
section mul_one_class_left_right
variables [mul_one_class α]

section covariant
variable  [covariant_class α α (*) (≤)]

@[to_additive add_pos_of_pos_of_nonneg]
lemma one_lt_mul_of_lt_of_le' (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_of_lt_of_le ha $ le_mul_of_one_le_right' hb

@[to_additive add_pos]
lemma one_lt_mul' (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
one_lt_mul_of_lt_of_le' ha hb.le

@[to_additive]
lemma lt_mul_of_lt_of_one_le' (hbc : b < c) (ha : 1 ≤ a) :
  b < c * a :=
hbc.trans_le $ le_mul_of_one_le_right' ha

@[to_additive]
lemma lt_mul_of_lt_of_one_lt' (hbc : b < c) (ha : 1 < a) :
  b < c * a :=
lt_mul_of_lt_of_one_le' hbc ha.le

end covariant

section contravariant
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive add_pos_of_nonneg_of_pos]
lemma one_lt_mul_of_le_of_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt' (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
hbc.trans_le $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt' (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt' ha.le hbc

end contravariant

variables [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma le_mul_of_one_le_of_le (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
one_mul b ▸ mul_le_mul' ha hbc

@[to_additive]
lemma le_mul_of_le_of_one_le (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
mul_one b ▸ mul_le_mul' hbc ha

@[to_additive add_nonneg]
lemma one_le_mul (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_one_le_of_le ha hb

@[to_additive add_nonpos]
lemma mul_le_one' (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
one_mul (1:α) ▸ (mul_le_mul' ha hb)

@[to_additive]
lemma mul_le_of_le_one_of_le' (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one' (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one' (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
(mul_le_of_le_of_le_one' le_rfl hb).trans_lt ha

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one' (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
(mul_le_of_le_one_of_le' ha le_rfl).trans_lt hb

@[to_additive]
lemma mul_lt_one' (ha : a < 1) (hb : b < 1) : a * b < 1 :=
mul_lt_one_of_le_one_of_lt_one' ha.le hb

@[to_additive]
lemma mul_lt_of_le_one_of_lt' (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
lt_of_le_of_lt (mul_le_of_le_one_of_le' ha le_rfl) hbc

@[to_additive]
lemma mul_lt_of_lt_of_le_one' (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
lt_of_le_of_lt (mul_le_of_le_of_le_one' le_rfl ha) hbc

@[to_additive]
lemma mul_lt_of_lt_one_of_lt' (ha : a < 1) (hbc : b < c) : a * b < c :=
mul_lt_of_le_one_of_lt' ha.le hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one' (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_lt_of_lt_of_le_one' hbc ha.le

end mul_one_class_left_right

end preorder

section partial_order
variables [mul_one_class α] [partial_order α]
  [covariant_class α α (*) (≤)] [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_eq_one_iff' (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
iff.intro
  (assume hab : a * b = 1,
   have a ≤ 1, from hab ▸ le_mul_of_le_of_one_le le_rfl hb,
   have a = 1, from le_antisymm this ha,
   have b ≤ 1, from hab ▸ le_mul_of_one_le_of_le ha le_rfl,
   have b = 1, from le_antisymm this hb,
   and.intro ‹a = 1› ‹b = 1›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', mul_one])

section mono
variables {β : Type*} [preorder β] {f g : β → α}

@[to_additive monotone.add]
lemma monotone.mul' (hf : monotone f) (hg : monotone g) : monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

@[to_additive monotone.add_const]
lemma monotone.mul_const' (hf : monotone f) (a : α) : monotone (λ x, f x * a) :=
hf.mul' monotone_const

@[to_additive monotone.const_add]
lemma monotone.const_mul' (hf : monotone f) (a : α) : monotone (λ x, a * f x) :=
monotone_const.mul' hf

end mono

end partial_order

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' [partial_order α] [left_cancel_semigroup α]
  [contravariant_class α α (*) (<)]
  {a b c : α} (bc : a * b ≤ a * c) :
  b ≤ c :=
begin
  cases le_iff_eq_or_lt.mp bc,
  { exact le_iff_eq_or_lt.mpr (or.inl ((mul_right_inj a).mp h)) },
  { exact (lt_of_mul_lt_mul_left' h).le }
end

@[to_additive le_of_add_le_add_right]
lemma le_of_mul_le_mul_right' [partial_order α] [right_cancel_semigroup α]
  [contravariant_class α α (function.swap (*)) (<)]
  {a b c : α} (bc : b * a ≤ c * a) :
  b ≤ c :=
begin
  cases le_iff_eq_or_lt.mp bc,
  { exact le_iff_eq_or_lt.mpr (or.inl ((mul_left_inj a).mp h)) },
  { exact (lt_of_mul_lt_mul_right' h).le }
end

variable [partial_order α]

section left_co_co
variables [left_cancel_monoid α]
  [covariant_class α α (*) (≤)]
  [contravariant_class α α (*) (<)]
@[to_additive add_lt_add_left]

lemma mul_lt_mul_left' (h : a < b) (c : α) : c * a < c * b :=
lt_of_le_not_le (mul_le_mul_left' h.le _)
  (λ j, not_le_of_gt h (le_of_mul_le_mul_left' j))

@[to_additive lt_add_of_pos_right]
lemma lt_mul_of_one_lt_right' (a : α) {b : α} (h : 1 < b) : a < a * b :=
have a * 1 < a * b, from mul_lt_mul_left' h a,
by rwa [mul_one] at this

@[simp, to_additive]
lemma mul_le_mul_iff_left (a : α) {b c : α} : a * b ≤ a * c ↔ b ≤ c :=
⟨le_of_mul_le_mul_left', λ h, mul_le_mul_left' h _⟩

@[simp, to_additive]
lemma mul_lt_mul_iff_left (a : α) {b c : α} : a * b < a * c ↔ b < c :=
⟨lt_of_mul_lt_mul_left', λ h, mul_lt_mul_left' h _⟩

@[simp, to_additive le_add_iff_nonneg_right]
lemma le_mul_iff_one_le_right' (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
have a * 1 ≤ a * b ↔ 1 ≤ b, from mul_le_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive lt_add_iff_pos_right]
lemma lt_mul_iff_one_lt_right' (a : α) {b : α} : a < a * b ↔ 1 < b :=
have a * 1 < a * b ↔ 1 < b, from mul_lt_mul_iff_left a,
by rwa mul_one at this

@[simp, to_additive add_le_iff_nonpos_right]
lemma mul_le_iff_le_one_right' : a * b ≤ a ↔ b ≤ 1 :=
by { convert mul_le_mul_iff_left a, rw [mul_one] }

@[simp, to_additive add_lt_iff_neg_left]
lemma mul_lt_iff_lt_one_left' : a * b < a ↔ b < 1 :=
by { convert mul_lt_mul_iff_left a, rw [mul_one] }

end left_co_co

section right_cos_cos

variables [right_cancel_monoid α]
  [covariant_class α α (function.swap (*)) (≤)]
  [contravariant_class α α (function.swap (*)) (<)]

@[to_additive add_lt_add_right]
lemma mul_lt_mul_right' (h : a < b) (c : α) : a * c < b * c :=
(mul_le_mul_right' h.le _).lt_of_not_le
  (λ j, not_le_of_gt h (le_of_mul_le_mul_right' j))

@[to_additive lt_add_of_pos_left]
lemma lt_mul_of_one_lt_left' (a : α) {b : α} (h : 1 < b) : a < b * a :=
have 1 * a < b * a, from mul_lt_mul_right' h a,
by rwa [one_mul] at this

@[simp, to_additive]
lemma mul_le_mul_iff_right (c : α) : a * c ≤ b * c ↔ a ≤ b :=
⟨le_of_mul_le_mul_right', λ h, mul_le_mul_right' h _⟩

@[simp, to_additive]
lemma mul_lt_mul_iff_right (c : α) : a * c < b * c ↔ a < b :=
⟨lt_of_mul_lt_mul_right', λ h, mul_lt_mul_right' h _⟩

@[simp, to_additive le_add_iff_nonneg_left]
lemma le_mul_iff_one_le_left' (a : α) {b : α} : a ≤ b * a ↔ 1 ≤ b :=
have 1 * a ≤ b * a ↔ 1 ≤ b, from mul_le_mul_iff_right a,
by rwa one_mul at this

@[simp, to_additive lt_add_iff_pos_left]
lemma lt_mul_iff_one_lt_left' (a : α) {b : α} : a < b * a ↔ 1 < b :=
have 1 * a < b * a ↔ 1 < b, from mul_lt_mul_iff_right a,
by rwa one_mul at this

@[simp, to_additive add_le_iff_nonpos_left]
lemma mul_le_iff_le_one_left' : a * b ≤ b ↔ a ≤ 1 :=
by { convert mul_le_mul_iff_right b, rw [one_mul] }

@[simp, to_additive add_lt_iff_neg_right]
lemma mul_lt_iff_lt_one_right' : a * b < b ↔ a < 1 :=
by { convert mul_lt_mul_iff_right b, rw [one_mul] }

end right_cos_cos

section right_co_cos

variables [right_cancel_monoid α]
  [covariant_class α α (*) (≤)]
  [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma mul_lt_mul_of_lt_of_le (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
lt_of_lt_of_le ((covariant_class.elim c h₁.le).lt_of_ne (λ h, h₁.ne ((mul_left_inj c).mp h)))
  (mul_le_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_one_of_lt_one_of_le_one (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_lt_of_le ha hb)

@[to_additive]
lemma lt_mul_of_one_lt_of_le (ha : 1 < a) (hbc : b ≤ c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma mul_le_of_le_one_of_le (ha : a ≤ 1) (hbc : b ≤ c) : a * b ≤ c :=
one_mul c ▸ mul_le_mul' ha hbc

@[to_additive]
lemma mul_le_of_le_of_le_one (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
mul_one c ▸ mul_le_mul' hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_le (ha : a < 1) (hbc : b ≤ c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_lt_of_le ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_le (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_lt_of_le hbc ha

@[to_additive]
lemma mul_lt_of_lt_of_le_one (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
mul_one c ▸ mul_lt_mul_of_lt_of_le hbc ha

end right_co_cos

variables [cancel_monoid α]
  [covariant_class α α (*) (≤)]
  [contravariant_class α α (*) (<)]
  [covariant_class α α (function.swap (*)) (≤)]

section special

@[to_additive]
lemma mul_lt_mul_of_le_of_lt (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_lt_one_of_le_one_of_lt_one (ha : a ≤ 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul_of_le_of_lt ha hb)

@[to_additive]
lemma lt_mul_of_le_of_one_lt (hbc : b ≤ c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma mul_lt_of_le_of_lt_one (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul_of_le_of_lt hbc ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul_of_le_of_lt ha hbc

@[to_additive]
lemma mul_lt_of_le_one_of_lt (ha : a ≤ 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul_of_le_of_lt ha hbc

end special

variables [contravariant_class α α (function.swap (*)) (<)]

@[to_additive add_lt_add]
lemma mul_lt_mul''' (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
(mul_lt_mul_right' h₁ c).trans (mul_lt_mul_left' h₂ b)

@[to_additive]
lemma mul_eq_one_iff_eq_one_of_one_le
  (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
⟨λ hab : a * b = 1,
by split; apply le_antisymm; try {assumption};
   rw ← hab; simp [ha, hb],
λ ⟨ha', hb'⟩, by rw [ha', hb', mul_one]⟩

@[to_additive]
lemma mul_lt_one (ha : a < 1) (hb : b < 1) : a * b < 1 :=
one_mul (1:α) ▸ (mul_lt_mul''' ha hb)

@[to_additive]
lemma lt_mul_of_one_lt_of_lt (ha : 1 < a) (hbc : b < c) : b < a * c :=
one_mul b ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma lt_mul_of_lt_of_one_lt (hbc : b < c) (ha : 1 < a) : b < c * a :=
mul_one b ▸ mul_lt_mul''' hbc ha

@[to_additive]
lemma mul_lt_of_lt_one_of_lt (ha : a < 1) (hbc : b < c) : a * b < c :=
one_mul c ▸ mul_lt_mul''' ha hbc

@[to_additive]
lemma mul_lt_of_lt_of_lt_one (hbc : b < c) (ha : a < 1) : b * a < c :=
mul_one c ▸ mul_lt_mul''' hbc ha
