/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import order.bounds
import algebra.order.field.defs
import algebra.group_with_zero.power

/-!
# Linear ordered (semi)fields

A linear ordered (semi)field is a (semi)field equipped with a linear order such that
* addition respects the order: `a ≤ b → c + a ≤ c + b`;
* multiplication of positives is positive: `0 < a → 0 < b → 0 < a * b`;
* `0 < 1`.

## Main Definitions

* `linear_ordered_semifield`: Typeclass for linear order semifields.
* `linear_ordered_field`: Typeclass for linear ordered fields.
-/

set_option old_structure_cmd true

open function order_dual

variables {ι α β : Type*}

namespace function

/-- Pullback a `linear_ordered_semifield` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
def injective.linear_ordered_semifield [linear_ordered_semifield α] [has_zero β] [has_one β]
  [has_add β] [has_mul β] [has_pow β ℕ] [has_smul ℕ β] [has_nat_cast β] [has_inv β] [has_div β]
  [has_pow β ℤ] [has_sup β] [has_inf β] (f : β → α) (hf : injective f) (zero : f 0 = 0)
  (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
  (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_semifield β :=
{ ..hf.linear_ordered_semiring f zero one add mul nsmul npow nat_cast hsup hinf,
  ..hf.semifield f zero one add mul inv div nsmul npow zpow nat_cast }

/-- Pullback a `linear_ordered_field` under an injective map. -/
@[reducible] -- See note [reducible non-instances]
def injective.linear_ordered_field [linear_ordered_field α] [has_zero β] [has_one β] [has_add β]
  [has_mul β] [has_neg β] [has_sub β] [has_pow β ℕ] [has_smul ℕ β] [has_smul ℤ β] [has_smul ℚ β]
  [has_nat_cast β] [has_int_cast β] [has_rat_cast β] [has_inv β] [has_div β] [has_pow β ℤ]
  [has_sup β] [has_inf β]
  (f : β → α) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
  (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (nsmul : ∀ x (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ x (n : ℤ), f (n • x) = n • f x)
  (qsmul : ∀ x (n : ℚ), f (n • x) = n • f x)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n)
  (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) (rat_cast : ∀ n : ℚ, f n = n)
  (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
  linear_ordered_field β :=
{ .. hf.linear_ordered_ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast hsup hinf,
  .. hf.field f zero one add mul neg sub inv div nsmul zsmul qsmul npow zpow nat_cast int_cast
      rat_cast }

end function

section linear_ordered_semifield
variables [linear_ordered_semifield α] {a b c d e : α} {m n : ℤ}

/-- `equiv.mul_left₀` as an order_iso. -/
@[simps {simp_rhs := tt}]
def order_iso.mul_left₀ (a : α) (ha : 0 < a) : α ≃o α :=
{ map_rel_iff' := λ _ _, mul_le_mul_left ha, ..equiv.mul_left₀ a ha.ne' }

/-- `equiv.mul_right₀` as an order_iso. -/
@[simps {simp_rhs := tt}]
def order_iso.mul_right₀ (a : α) (ha : 0 < a) : α ≃o α :=
{ map_rel_iff' := λ _ _, mul_le_mul_right ha, ..equiv.mul_right₀ a ha.ne' }

/-!
### Lemmas about pos, nonneg, nonpos, neg
-/

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a :=
suffices ∀ a : α, 0 < a → 0 < a⁻¹,
from ⟨λ h, inv_inv a ▸ this _ h, this a⟩,
assume a ha, flip lt_of_mul_lt_mul_left ha.le $ by simp [ne_of_gt ha, zero_lt_one]

alias inv_pos ↔ _ inv_pos_of_pos

@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a :=
by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

alias inv_nonneg ↔ _ inv_nonneg_of_nonneg

@[simp] lemma inv_lt_zero : a⁻¹ < 0 ↔ a < 0 :=
by simp only [← not_le, inv_nonneg]

@[simp] lemma inv_nonpos : a⁻¹ ≤ 0 ↔ a ≤ 0 :=
by simp only [← not_lt, inv_pos]

lemma one_div_pos : 0 < 1 / a ↔ 0 < a :=
inv_eq_one_div a ▸ inv_pos

lemma one_div_neg : 1 / a < 0 ↔ a < 0 :=
inv_eq_one_div a ▸ inv_lt_zero

lemma one_div_nonneg : 0 ≤ 1 / a ↔ 0 ≤ a :=
inv_eq_one_div a ▸ inv_nonneg

lemma one_div_nonpos : 1 / a ≤ 0 ↔ a ≤ 0 :=
inv_eq_one_div a ▸ inv_nonpos

lemma div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b :=
by { rw div_eq_mul_inv, exact mul_pos ha (inv_pos.2 hb) }

lemma div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
by { rw div_eq_mul_inv, exact mul_nonneg ha (inv_nonneg.2 hb) }

lemma div_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 :=
by { rw div_eq_mul_inv, exact mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg.2 hb) }

lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 :=
by { rw div_eq_mul_inv, exact mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb) }

lemma zpow_nonneg (ha : 0 ≤ a) : ∀ n : ℤ, 0 ≤ a ^ n
| (n : ℕ) := by { rw zpow_coe_nat, exact pow_nonneg ha _ }
| -[1+n]  := by { rw zpow_neg_succ_of_nat, exact inv_nonneg.2 (pow_nonneg ha _) }

lemma zpow_pos_of_pos (ha : 0 < a) : ∀ n : ℤ, 0 < a ^ n
| (n : ℕ) := by { rw zpow_coe_nat, exact pow_pos ha _ }
| -[1+n]  := by { rw zpow_neg_succ_of_nat, exact inv_pos.2 (pow_pos ha _) }

/-!
### Relating one division with another term.
-/

lemma le_div_iff (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
⟨λ h, div_mul_cancel b (ne_of_lt hc).symm ▸ mul_le_mul_of_nonneg_right h hc.le,
  λ h, calc
    a   = a * c * (1 / c) : mul_mul_div a (ne_of_lt hc).symm
    ... ≤ b * (1 / c)     : mul_le_mul_of_nonneg_right h (one_div_pos.2 hc).le
    ... = b / c           : (div_eq_mul_one_div b c).symm⟩

lemma le_div_iff' (hc : 0 < c) : a ≤ b / c ↔ c * a ≤ b :=
by rw [mul_comm, le_div_iff hc]

lemma div_le_iff (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b :=
⟨λ h, calc
  a = a / b * b : by rw (div_mul_cancel _ (ne_of_lt hb).symm)
  ... ≤ c * b     : mul_le_mul_of_nonneg_right h hb.le,
  λ h, calc
  a / b = a * (1 / b)     : div_eq_mul_one_div a b
  ... ≤ (c * b) * (1 / b) : mul_le_mul_of_nonneg_right h (one_div_pos.2 hb).le
  ... = (c * b) / b       : (div_eq_mul_one_div (c * b) b).symm
  ... = c                 : by refine (div_eq_iff (ne_of_gt hb)).mpr rfl⟩

lemma div_le_iff' (hb : 0 < b) : a / b ≤ c ↔ a ≤ b * c :=
by rw [mul_comm, div_le_iff hb]

lemma lt_div_iff (hc : 0 < c) : a < b / c ↔ a * c < b :=
lt_iff_lt_of_le_iff_le $ div_le_iff hc

lemma lt_div_iff' (hc : 0 < c) : a < b / c ↔ c * a < b :=
by rw [mul_comm, lt_div_iff hc]

lemma div_lt_iff (hc : 0 < c) : b / c < a ↔ b < a * c :=
lt_iff_lt_of_le_iff_le (le_div_iff hc)

lemma div_lt_iff' (hc : 0 < c) : b / c < a ↔ b < c * a :=
by rw [mul_comm, div_lt_iff hc]

lemma inv_mul_le_iff (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ b * c :=
begin
  rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div],
  exact div_le_iff' h,
end

lemma inv_mul_le_iff' (h : 0 < b) : b⁻¹ * a ≤ c ↔ a ≤ c * b :=
by rw [inv_mul_le_iff h, mul_comm]

lemma mul_inv_le_iff (h : 0 < b) : a * b⁻¹ ≤ c ↔ a ≤ b * c :=
by rw [mul_comm, inv_mul_le_iff h]

lemma mul_inv_le_iff' (h : 0 < b) : a * b⁻¹ ≤ c ↔ a ≤ c * b :=
by rw [mul_comm, inv_mul_le_iff' h]

lemma div_self_le_one (a : α) : a / a ≤ 1 :=
if h : a = 0 then by simp [h] else by simp [h]

lemma inv_mul_lt_iff (h : 0 < b) : b⁻¹ * a < c ↔ a < b * c :=
begin
  rw [inv_eq_one_div, mul_comm, ← div_eq_mul_one_div],
  exact div_lt_iff' h,
end

lemma inv_mul_lt_iff' (h : 0 < b) : b⁻¹ * a < c ↔ a < c * b :=
by rw [inv_mul_lt_iff h, mul_comm]

lemma mul_inv_lt_iff (h : 0 < b) : a * b⁻¹ < c ↔ a < b * c :=
by rw [mul_comm, inv_mul_lt_iff h]

lemma mul_inv_lt_iff' (h : 0 < b) : a * b⁻¹ < c ↔ a < c * b :=
by rw [mul_comm, inv_mul_lt_iff' h]

lemma inv_pos_le_iff_one_le_mul (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ b * a :=
by { rw [inv_eq_one_div], exact div_le_iff ha }

lemma inv_pos_le_iff_one_le_mul' (ha : 0 < a) : a⁻¹ ≤ b ↔ 1 ≤ a * b :=
by { rw [inv_eq_one_div], exact div_le_iff' ha }

lemma inv_pos_lt_iff_one_lt_mul (ha : 0 < a) : a⁻¹ < b ↔ 1 < b * a :=
by { rw [inv_eq_one_div], exact div_lt_iff ha }

lemma inv_pos_lt_iff_one_lt_mul' (ha : 0 < a) : a⁻¹ < b ↔ 1 < a * b :=
by { rw [inv_eq_one_div], exact div_lt_iff' ha }

/-- One direction of `div_le_iff` where `b` is allowed to be `0` (but `c` must be nonnegative) -/
lemma div_le_of_nonneg_of_le_mul (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c :=
by { rcases eq_or_lt_of_le hb with rfl|hb', simp [hc], rwa [div_le_iff hb'] }

lemma div_le_one_of_le (h : a ≤ b) (hb : 0 ≤ b) : a / b ≤ 1 :=
div_le_of_nonneg_of_le_mul hb zero_le_one $ by rwa one_mul

/-!
### Bi-implications of inequalities using inversions
-/

lemma inv_le_inv_of_le (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
by rwa [← one_div a, le_div_iff' ha, ← div_eq_mul_inv, div_le_iff (ha.trans_le h), one_mul]

/-- See `inv_le_inv_of_le` for the implication from right-to-left with one fewer assumption. -/
lemma inv_le_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by rw [← one_div, div_le_iff ha, ← div_eq_inv_mul, le_div_iff hb, one_mul]

/-- In a linear ordered field, for positive `a` and `b` we have `a⁻¹ ≤ b ↔ b⁻¹ ≤ a`.
See also `inv_le_of_inv_le` for a one-sided implication with one fewer assumption. -/
lemma inv_le (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by rw [← inv_le_inv hb (inv_pos.2 ha), inv_inv]

lemma inv_le_of_inv_le (ha : 0 < a) (h : a⁻¹ ≤ b) : b⁻¹ ≤ a :=
(inv_le ha ((inv_pos.2 ha).trans_le h)).1 h

lemma le_inv (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by rw [← inv_le_inv (inv_pos.2 hb) ha, inv_inv]

/-- See `inv_lt_inv_of_lt` for the implication from right-to-left with one fewer assumption. -/
lemma inv_lt_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
lt_iff_lt_of_le_iff_le (inv_le_inv hb ha)

lemma inv_lt_inv_of_lt (hb : 0 < b) (h : b < a) : a⁻¹ < b⁻¹ :=
(inv_lt_inv (hb.trans h) hb).2 h

/-- In a linear ordered field, for positive `a` and `b` we have `a⁻¹ < b ↔ b⁻¹ < a`.
See also `inv_lt_of_inv_lt` for a one-sided implication with one fewer assumption. -/
lemma inv_lt (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a :=
lt_iff_lt_of_le_iff_le (le_inv hb ha)

lemma inv_lt_of_inv_lt (ha : 0 < a) (h : a⁻¹ < b) : b⁻¹ < a :=
(inv_lt ha ((inv_pos.2 ha).trans h)).1 h

lemma lt_inv (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ :=
lt_iff_lt_of_le_iff_le (inv_le hb ha)

lemma inv_lt_one (ha : 1 < a) : a⁻¹ < 1 :=
by rwa [inv_lt ((@zero_lt_one α _ _).trans ha) zero_lt_one, inv_one]

lemma one_lt_inv (h₁ : 0 < a) (h₂ : a < 1) : 1 < a⁻¹ :=
by rwa [lt_inv (@zero_lt_one α _ _) h₁, inv_one]

lemma inv_le_one (ha : 1 ≤ a) : a⁻¹ ≤ 1 :=
by rwa [inv_le ((@zero_lt_one α _ _).trans_le ha) zero_lt_one, inv_one]

lemma one_le_inv (h₁ : 0 < a) (h₂ : a ≤ 1) : 1 ≤ a⁻¹ :=
by rwa [le_inv (@zero_lt_one α _ _) h₁, inv_one]

lemma inv_lt_one_iff_of_pos (h₀ : 0 < a) : a⁻¹ < 1 ↔ 1 < a :=
⟨λ h₁, inv_inv a ▸ one_lt_inv (inv_pos.2 h₀) h₁, inv_lt_one⟩

lemma inv_lt_one_iff : a⁻¹ < 1 ↔ a ≤ 0 ∨ 1 < a :=
begin
  cases le_or_lt a 0 with ha ha,
  { simp [ha, (inv_nonpos.2 ha).trans_lt zero_lt_one] },
  { simp only [ha.not_le, false_or, inv_lt_one_iff_of_pos ha] }
end

lemma one_lt_inv_iff : 1 < a⁻¹ ↔ 0 < a ∧ a < 1 :=
⟨λ h, ⟨inv_pos.1 (zero_lt_one.trans h), inv_inv a ▸ inv_lt_one h⟩, and_imp.2 one_lt_inv⟩

lemma inv_le_one_iff : a⁻¹ ≤ 1 ↔ a ≤ 0 ∨ 1 ≤ a :=
begin
  rcases em (a = 1) with (rfl|ha),
  { simp [le_rfl] },
  { simp only [ne.le_iff_lt (ne.symm ha), ne.le_iff_lt (mt inv_eq_one.1 ha), inv_lt_one_iff] }
end

lemma one_le_inv_iff : 1 ≤ a⁻¹ ↔ 0 < a ∧ a ≤ 1 :=
⟨λ h, ⟨inv_pos.1 (zero_lt_one.trans_le h), inv_inv a ▸ inv_le_one h⟩, and_imp.2 one_le_inv⟩

/-!
### Relating two divisions.
-/

@[mono] lemma div_le_div_of_le (hc : 0 ≤ c) (h : a ≤ b) : a / c ≤ b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_le_mul_of_nonneg_right h (one_div_nonneg.2 hc)
end

-- Not a `mono` lemma b/c `div_le_div` is strictly more general
lemma div_le_div_of_le_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c :=
begin
  rw [div_eq_mul_inv, div_eq_mul_inv],
  exact mul_le_mul_of_nonneg_left ((inv_le_inv (hc.trans_le h) hc).mpr h) ha
end

lemma div_le_div_of_le_of_nonneg (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c :=
div_le_div_of_le hc hab

lemma div_lt_div_of_lt (hc : 0 < c) (h : a < b) : a / c < b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_lt_mul_of_pos_right h (one_div_pos.2 hc)
end

lemma div_le_div_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b :=
⟨le_imp_le_of_lt_imp_lt $ div_lt_div_of_lt hc, div_le_div_of_le $ hc.le⟩

lemma div_lt_div_right (hc : 0 < c) : a / c < b / c ↔ a < b :=
lt_iff_lt_of_le_iff_le $ div_le_div_right hc

lemma div_lt_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b :=
by simp only [div_eq_mul_inv, mul_lt_mul_left ha, inv_lt_inv hb hc]

lemma div_le_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b ≤ a / c ↔ c ≤ b :=
le_iff_le_iff_lt_iff_lt.2 (div_lt_div_left ha hc hb)

lemma div_lt_div_iff (b0 : 0 < b) (d0 : 0 < d) :
  a / b < c / d ↔ a * d < c * b :=
by rw [lt_div_iff d0, div_mul_eq_mul_div, div_lt_iff b0]

lemma div_le_div_iff (b0 : 0 < b) (d0 : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b :=
by rw [le_div_iff d0, div_mul_eq_mul_div, div_le_iff b0]

@[mono] lemma div_le_div (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hbd : d ≤ b) : a / b ≤ c / d :=
by { rw div_le_div_iff (hd.trans_le hbd) hd, exact mul_le_mul hac hbd hd.le hc }

lemma div_lt_div (hac : a < c) (hbd : d ≤ b) (c0 : 0 ≤ c) (d0 : 0 < d) :
  a / b < c / d :=
(div_lt_div_iff (d0.trans_le hbd) d0).2 (mul_lt_mul hac hbd d0 c0)

lemma div_lt_div' (hac : a ≤ c) (hbd : d < b) (c0 : 0 < c) (d0 : 0 < d) :
  a / b < c / d :=
(div_lt_div_iff (d0.trans hbd) d0).2 (mul_lt_mul' hac hbd d0.le c0)

lemma div_lt_div_of_lt_left (hc : 0 < c) (hb : 0 < b) (h : b < a) : c / a < c / b :=
(div_lt_div_left hc (hb.trans h) hb).mpr h

/-!
### Relating one division and involving `1`
-/

lemma div_le_self (ha : 0 ≤ a) (hb : 1 ≤ b) : a / b ≤ a :=
by simpa only [div_one] using div_le_div_of_le_left ha zero_lt_one hb

lemma div_lt_self (ha : 0 < a) (hb : 1 < b) : a / b < a :=
by simpa only [div_one] using div_lt_div_of_lt_left ha zero_lt_one hb

lemma le_div_self (ha : 0 ≤ a) (hb₀ : 0 < b) (hb₁ : b ≤ 1) : a ≤ a / b :=
by simpa only [div_one] using div_le_div_of_le_left ha hb₀ hb₁

lemma one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a :=
by rw [le_div_iff hb, one_mul]

lemma div_le_one (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b :=
by rw [div_le_iff hb, one_mul]

lemma one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a :=
by rw [lt_div_iff hb, one_mul]

lemma div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b :=
by rw [div_lt_iff hb, one_mul]

lemma one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ b ↔ 1 / b ≤ a :=
by simpa using inv_le ha hb

lemma one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a :=
by simpa using inv_lt ha hb

lemma le_one_div (ha : 0 < a) (hb : 0 < b) : a ≤ 1 / b ↔ b ≤ 1 / a :=
by simpa using le_inv ha hb

lemma lt_one_div (ha : 0 < a) (hb : 0 < b) : a < 1 / b ↔ b < 1 / a :=
by simpa using lt_inv ha hb

/-!
### Relating two divisions, involving `1`
-/
lemma one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a :=
by simpa using inv_le_inv_of_le ha h

lemma one_div_lt_one_div_of_lt (ha : 0 < a) (h : a < b) : 1 / b < 1 / a :=
by rwa [lt_div_iff' ha, ← div_eq_mul_one_div, div_lt_one (ha.trans h)]

lemma le_of_one_div_le_one_div (ha : 0 < a) (h : 1 / a ≤ 1 / b) : b ≤ a :=
le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_lt ha) h

lemma lt_of_one_div_lt_one_div (ha : 0 < a) (h : 1 / a < 1 / b) : b < a :=
lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_le ha) h

/-- For the single implications with fewer assumptions, see `one_div_le_one_div_of_le` and
  `le_of_one_div_le_one_div` -/
lemma one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
div_le_div_left zero_lt_one ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
lemma one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
div_lt_div_left zero_lt_one ha hb

lemma one_lt_one_div (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a :=
by rwa [lt_one_div (@zero_lt_one α _ _) h1, one_div_one]

lemma one_le_one_div (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a :=
by rwa [le_one_div (@zero_lt_one α _ _) h1, one_div_one]

/-! ### Integer powers -/

lemma zpow_le_of_le (ha : 1 ≤ a) (h : m ≤ n) : a ^ m ≤ a ^ n :=
begin
  have ha₀ : 0 < a, from one_pos.trans_le ha,
  lift n - m to ℕ using sub_nonneg.2 h with k hk,
  calc a ^ m = a ^ m * 1 : (mul_one _).symm
  ... ≤ a ^ m * a ^ k : mul_le_mul_of_nonneg_left (one_le_pow_of_one_le ha _) (zpow_nonneg ha₀.le _)
  ... = a ^ n : by rw [← zpow_coe_nat, ← zpow_add₀ ha₀.ne', hk, add_sub_cancel'_right]
end

lemma zpow_le_one_of_nonpos (ha : 1 ≤ a) (hn : n ≤ 0) : a ^ n ≤ 1 :=
(zpow_le_of_le ha hn).trans_eq $ zpow_zero _

lemma one_le_zpow_of_nonneg (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n :=
(zpow_zero _).symm.trans_le $ zpow_le_of_le ha hn

protected lemma nat.zpow_pos_of_pos {a : ℕ} (h : 0 < a) (n : ℤ) : 0 < (a : α)^n :=
by { apply zpow_pos_of_pos, exact_mod_cast h }

lemma nat.zpow_ne_zero_of_pos {a : ℕ} (h : 0 < a) (n : ℤ) : (a : α)^n ≠ 0 :=
(nat.zpow_pos_of_pos h n).ne'

lemma one_lt_zpow (ha : 1 < a) : ∀ n : ℤ, 0 < n → 1 < a ^ n
| (n : ℕ) h := (zpow_coe_nat _ _).symm.subst (one_lt_pow ha $ int.coe_nat_ne_zero.mp h.ne')
| -[1+ n] h := ((int.neg_succ_not_pos _).mp h).elim

lemma zpow_strict_mono (hx : 1 < a) : strict_mono ((^) a : ℤ → α) :=
strict_mono_int_of_lt_succ $ λ n,
have xpos : 0 < a, from zero_lt_one.trans hx,
calc a ^ n < a ^ n * a : lt_mul_of_one_lt_right (zpow_pos_of_pos xpos _) hx
... = a ^ (n + 1) : (zpow_add_one₀ xpos.ne' _).symm

lemma zpow_strict_anti (h₀ : 0 < a) (h₁ : a < 1) : strict_anti ((^) a : ℤ → α) :=
strict_anti_int_of_succ_lt $ λ n,
calc a ^ (n + 1) = a ^ n * a : zpow_add_one₀ h₀.ne' _
... < a ^ n * 1 : (mul_lt_mul_left $ zpow_pos_of_pos h₀ _).2 h₁
... = a ^ n : mul_one _

@[simp] lemma zpow_lt_iff_lt (hx : 1 < a) : a ^ m < a ^ n ↔ m < n := (zpow_strict_mono hx).lt_iff_lt
@[simp] lemma zpow_le_iff_le (hx : 1 < a) : a ^ m ≤ a ^ n ↔ m ≤ n := (zpow_strict_mono hx).le_iff_le

@[simp] lemma div_pow_le (ha : 0 ≤ a) (hb : 1 ≤ b) (k : ℕ) : a/b^k ≤ a :=
div_le_self ha $ one_le_pow_of_one_le hb _

lemma zpow_injective (h₀ : 0 < a) (h₁ : a ≠ 1) : injective ((^) a : ℤ → α) :=
begin
  rcases h₁.lt_or_lt with H|H,
  { exact (zpow_strict_anti h₀ H).injective },
  { exact (zpow_strict_mono H).injective }
end

@[simp] lemma zpow_inj (h₀ : 0 < a) (h₁ : a ≠ 1) : a ^ m = a ^ n ↔ m = n :=
(zpow_injective h₀ h₁).eq_iff

lemma zpow_le_max_of_min_le {x : α} (hx : 1 ≤ x) {a b c : ℤ} (h : min a b ≤ c) :
  x ^ -c ≤ max (x ^ -a) (x ^ -b) :=
begin
  have : antitone (λ n : ℤ, x ^ -n) := λ m n h, zpow_le_of_le hx (neg_le_neg h),
  exact (this h).trans_eq this.map_min,
end

lemma zpow_le_max_iff_min_le {x : α} (hx : 1 < x) {a b c : ℤ} :
  x ^ -c ≤ max (x ^ -a) (x ^ -b) ↔ min a b ≤ c :=
by simp_rw [le_max_iff, min_le_iff, zpow_le_iff_le hx, neg_le_neg_iff]

/-!
### Results about halving.

The equalities also hold in semifields of characteristic `0`.
-/

/- TODO: Unify `add_halves` and `add_halves'` into a single lemma about
`division_semiring` + `char_zero` -/
lemma add_halves (a : α) : a / 2 + a / 2 = a :=
by rw [div_add_div_same, ← two_mul, mul_div_cancel_left a two_ne_zero]

-- TODO: Generalize to `division_semiring`
lemma add_self_div_two (a : α) : (a + a) / 2 = a :=
by rw [← mul_two, mul_div_cancel a two_ne_zero]

lemma half_pos (h : 0 < a) : 0 < a / 2 := div_pos h zero_lt_two

lemma one_half_pos : (0:α) < 1 / 2 := half_pos zero_lt_one

lemma div_two_lt_of_pos (h : 0 < a) : a / 2 < a :=
by { rw [div_lt_iff (@zero_lt_two α _ _)], exact lt_mul_of_one_lt_right h one_lt_two }

lemma half_lt_self : 0 < a → a / 2 < a := div_two_lt_of_pos

lemma half_le_self (ha_nonneg : 0 ≤ a) : a / 2 ≤ a :=
begin
  by_cases h0 : a = 0,
  { simp [h0], },
  { rw ← ne.def at h0,
    exact (half_lt_self (lt_of_le_of_ne ha_nonneg h0.symm)).le, },
end

lemma one_half_lt_one : (1 / 2 : α) < 1 := half_lt_self zero_lt_one

lemma two_inv_lt_one : (2⁻¹ : α) < 1 := (one_div _).symm.trans_lt one_half_lt_one

lemma left_lt_add_div_two : a < (a + b) / 2 ↔ a < b := by simp [lt_div_iff, mul_two]

lemma add_div_two_lt_right : (a + b) / 2 < b ↔ a < b := by simp [div_lt_iff, mul_two]

/-!
### Miscellaneous lemmas
-/

lemma mul_le_mul_of_mul_div_le (h : a * (b / c) ≤ d) (hc : 0 < c) : b * a ≤ d * c :=
begin
  rw [← mul_div_assoc] at h,
  rwa [mul_comm b, ← div_le_iff hc],
end

lemma div_mul_le_div_mul_of_div_le_div (h : a / b ≤ c / d) (he : 0 ≤ e) :
  a / (b * e) ≤ c / (d * e) :=
begin
  rw [div_mul_eq_div_mul_one_div, div_mul_eq_div_mul_one_div],
  exact mul_le_mul_of_nonneg_right h (one_div_nonneg.2 he)
end

lemma exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b * c < a :=
begin
  have : 0 < a / max (b + 1) 1, from div_pos h (lt_max_iff.2 (or.inr zero_lt_one)),
  refine ⟨a / max (b + 1) 1, this, _⟩,
  rw [← lt_div_iff this, div_div_cancel' h.ne'],
  exact lt_max_iff.2 (or.inl $ lt_add_one _)
end

lemma monotone.div_const {β : Type*} [preorder β] {f : β → α} (hf : monotone f)
  {c : α} (hc : 0 ≤ c) : monotone (λ x, (f x) / c) :=
begin
  haveI := @linear_order.decidable_le α _,
  simpa only [div_eq_mul_inv] using (monotone_mul_right_of_nonneg (inv_nonneg.2 hc)).comp hf
end

lemma strict_mono.div_const {β : Type*} [preorder β] {f : β → α} (hf : strict_mono f)
  {c : α} (hc : 0 < c) :
  strict_mono (λ x, (f x) / c) :=
by simpa only [div_eq_mul_inv] using hf.mul_const (inv_pos.2 hc)

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_field.to_densely_ordered : densely_ordered α :=
{ dense := λ a₁ a₂ h, ⟨(a₁ + a₂) / 2,
  calc a₁ = (a₁ + a₁) / 2 : (add_self_div_two a₁).symm
      ... < (a₁ + a₂) / 2 : div_lt_div_of_lt zero_lt_two (add_lt_add_left h _),
  calc (a₁ + a₂) / 2 < (a₂ + a₂) / 2 : div_lt_div_of_lt zero_lt_two (add_lt_add_right h _)
                 ... = a₂            : add_self_div_two a₂⟩ }

lemma min_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : min (a / c) (b / c) = (min a b) / c :=
eq.symm $ monotone.map_min (λ x y, div_le_div_of_le hc)

lemma max_div_div_right {c : α} (hc : 0 ≤ c) (a b : α) : max (a / c) (b / c) = (max a b) / c :=
eq.symm $ monotone.map_max (λ x y, div_le_div_of_le hc)

lemma one_div_strict_anti_on : strict_anti_on (λ x : α, 1 / x) (set.Ioi 0) :=
λ x x1 y y1 xy, (one_div_lt_one_div (set.mem_Ioi.mp y1) (set.mem_Ioi.mp x1)).mpr xy

lemma one_div_pow_le_one_div_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) :
  1 / a ^ n ≤ 1 / a ^ m :=
by refine (one_div_le_one_div _ _).mpr (pow_le_pow a1 mn);
  exact pow_pos (zero_lt_one.trans_le a1) _

lemma one_div_pow_lt_one_div_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) :
  1 / a ^ n < 1 / a ^ m :=
by refine (one_div_lt_one_div _ _).mpr (pow_lt_pow a1 mn);
  exact pow_pos (trans zero_lt_one a1) _

lemma one_div_pow_anti (a1 : 1 ≤ a) : antitone (λ n : ℕ, 1 / a ^ n) :=
λ m n, one_div_pow_le_one_div_pow_of_le a1

lemma one_div_pow_strict_anti (a1 : 1 < a) : strict_anti (λ n : ℕ, 1 / a ^ n) :=
λ m n, one_div_pow_lt_one_div_pow_of_lt a1

lemma inv_strict_anti_on : strict_anti_on (λ x : α, x⁻¹) (set.Ioi 0) :=
λ x hx y hy xy, (inv_lt_inv hy hx).2 xy

lemma inv_pow_le_inv_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) :
  (a ^ n)⁻¹ ≤ (a ^ m)⁻¹ :=
by convert one_div_pow_le_one_div_pow_of_le a1 mn; simp

lemma inv_pow_lt_inv_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) :
  (a ^ n)⁻¹ < (a ^ m)⁻¹ :=
by convert one_div_pow_lt_one_div_pow_of_lt a1 mn; simp

lemma inv_pow_anti (a1 : 1 ≤ a) : antitone (λ n : ℕ, (a ^ n)⁻¹) :=
λ m n, inv_pow_le_inv_pow_of_le a1

lemma inv_pow_strict_anti (a1 : 1 < a) : strict_anti (λ n : ℕ, (a ^ n)⁻¹) :=
λ m n, inv_pow_lt_inv_pow_of_lt a1

/-! ### Results about `is_lub` and `is_glb` -/

lemma is_glb.mul_left {s : set α} (ha : 0 ≤ a) (hs : is_glb s b) :
  is_glb ((λ b, a * b) '' s) (a * b) :=
begin
  rcases lt_or_eq_of_le ha with ha | rfl,
  { exact (order_iso.mul_left₀ _ ha).is_glb_image'.2 hs, },
  { simp_rw zero_mul,
    rw hs.nonempty.image_const,
    exact is_glb_singleton },
end

lemma is_glb.mul_right {s : set α} (ha : 0 ≤ a) (hs : is_glb s b) :
  is_glb ((λ b, b * a) '' s) (b * a) :=
by simpa [mul_comm] using hs.mul_left ha

end linear_ordered_semifield

section
variables [linear_ordered_field α] {a b c d : α} {n : ℤ}

/-! ### Lemmas about pos, nonneg, nonpos, neg -/

lemma div_pos_iff : 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by simp [division_def, mul_pos_iff]
lemma div_neg_iff : a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by simp [division_def, mul_neg_iff]

lemma div_nonneg_iff : 0 ≤ a / b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
by simp [division_def, mul_nonneg_iff]

lemma div_nonpos_iff : a / b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b :=
by simp [division_def, mul_nonpos_iff]

lemma div_nonneg_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b :=
div_nonneg_iff.2 $ or.inr ⟨ha, hb⟩

lemma div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b :=
div_pos_iff.2 $ or.inr ⟨ha, hb⟩

lemma div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
div_neg_iff.2 $ or.inr ⟨ha, hb⟩

lemma div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
div_neg_iff.2 $ or.inl ⟨ha, hb⟩

lemma zpow_bit0_nonneg (a : α) (n : ℤ) : 0 ≤ a ^ bit0 n :=
(mul_self_nonneg _).trans_eq $ (zpow_bit0 _ _).symm

lemma zpow_two_nonneg (a : α) : 0 ≤ a ^ (2 : ℤ) := zpow_bit0_nonneg _ _

lemma zpow_bit0_pos (h : a ≠ 0) (n : ℤ) : 0 < a ^ bit0 n :=
(zpow_bit0_nonneg a n).lt_of_ne (zpow_ne_zero _ h).symm

lemma zpow_two_pos_of_ne_zero (h : a ≠ 0) : 0 < a ^ (2 : ℤ) := zpow_bit0_pos h _

@[simp] lemma zpow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
⟨λ h, not_le.1 $ λ h', not_le.2 h $ zpow_nonneg h' _,
 λ h, by rw [bit1, zpow_add_one₀ h.ne]; exact mul_neg_of_pos_of_neg (zpow_bit0_pos h.ne _) h⟩

@[simp] lemma zpow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
le_iff_le_iff_lt_iff_lt.2 zpow_bit1_neg_iff

@[simp] lemma zpow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 :=
by rw [le_iff_lt_or_eq, le_iff_lt_or_eq, zpow_bit1_neg_iff, zpow_eq_zero_iff (int.bit1_ne_zero n)]

@[simp] lemma zpow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
lt_iff_lt_of_le_iff_le zpow_bit1_nonpos_iff

/-! ### Relating one division with another term -/

lemma div_le_iff_of_neg (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b :=
⟨λ h, div_mul_cancel b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le,
  λ h, calc
    a = a * c * (1 / c) : mul_mul_div a (ne_of_lt hc)
  ... ≥ b * (1 / c)     : mul_le_mul_of_nonpos_right h (one_div_neg.2 hc).le
  ... = b / c           : (div_eq_mul_one_div b c).symm⟩

lemma div_le_iff_of_neg' (hc : c < 0) : b / c ≤ a ↔ c * a ≤ b :=
by rw [mul_comm, div_le_iff_of_neg hc]

lemma le_div_iff_of_neg (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c :=
by rw [← neg_neg c, mul_neg, div_neg, le_neg,
    div_le_iff (neg_pos.2 hc), neg_mul]

lemma le_div_iff_of_neg' (hc : c < 0) : a ≤ b / c ↔ b ≤ c * a :=
by rw [mul_comm, le_div_iff_of_neg hc]

lemma div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b :=
lt_iff_lt_of_le_iff_le $ le_div_iff_of_neg hc

lemma div_lt_iff_of_neg' (hc : c < 0) : b / c < a ↔ c * a < b :=
by rw [mul_comm, div_lt_iff_of_neg hc]

lemma lt_div_iff_of_neg (hc : c < 0) : a < b / c ↔ b < a * c :=
lt_iff_lt_of_le_iff_le $ div_le_iff_of_neg hc

lemma lt_div_iff_of_neg' (hc : c < 0) : a < b / c ↔ b < c * a :=
by rw [mul_comm, lt_div_iff_of_neg hc]

/-! ### Bi-implications of inequalities using inversions -/

lemma inv_le_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by rw [← one_div, div_le_iff_of_neg ha, ← div_eq_inv_mul, div_le_iff_of_neg hb, one_mul]

lemma inv_le_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by rw [← inv_le_inv_of_neg hb (inv_lt_zero.2 ha), inv_inv]

lemma le_inv_of_neg (ha : a < 0) (hb : b < 0) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by rw [← inv_le_inv_of_neg (inv_lt_zero.2 hb) ha, inv_inv]

lemma inv_lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b⁻¹ ↔ b < a :=
lt_iff_lt_of_le_iff_le (inv_le_inv_of_neg hb ha)

lemma inv_lt_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a :=
lt_iff_lt_of_le_iff_le (le_inv_of_neg hb ha)

lemma lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a⁻¹ :=
lt_iff_lt_of_le_iff_le (inv_le_of_neg hb ha)

/-! ### Relating two divisions -/

lemma div_le_div_of_nonpos_of_le (hc : c ≤ 0) (h : b ≤ a) : a / c ≤ b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_le_mul_of_nonpos_right h (one_div_nonpos.2 hc)
end

lemma div_lt_div_of_neg_of_lt (hc : c < 0) (h : b < a) : a / c < b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_lt_mul_of_neg_right h (one_div_neg.2 hc)
end

lemma div_le_div_right_of_neg (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a :=
⟨le_imp_le_of_lt_imp_lt $ div_lt_div_of_neg_of_lt hc, div_le_div_of_nonpos_of_le $ hc.le⟩

lemma div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a :=
lt_iff_lt_of_le_iff_le $ div_le_div_right_of_neg hc

/-! ### Relating one division and involving `1` -/

lemma one_le_div_of_neg (hb : b < 0) : 1 ≤ a / b ↔ a ≤ b :=
by rw [le_div_iff_of_neg hb, one_mul]

lemma div_le_one_of_neg (hb : b < 0) : a / b ≤ 1 ↔ b ≤ a :=
by rw [div_le_iff_of_neg hb, one_mul]

lemma one_lt_div_of_neg (hb : b < 0) : 1 < a / b ↔ a < b :=
by rw [lt_div_iff_of_neg hb, one_mul]

lemma div_lt_one_of_neg (hb : b < 0) : a / b < 1 ↔ b < a :=
by rw [div_lt_iff_of_neg hb, one_mul]

lemma one_div_le_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ b ↔ 1 / b ≤ a :=
by simpa using inv_le_of_neg ha hb

lemma one_div_lt_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < b ↔ 1 / b < a :=
by simpa using inv_lt_of_neg ha hb

lemma le_one_div_of_neg (ha : a < 0) (hb : b < 0) : a ≤ 1 / b ↔ b ≤ 1 / a :=
by simpa using le_inv_of_neg ha hb

lemma lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : a < 1 / b ↔ b < 1 / a :=
by simpa using lt_inv_of_neg ha hb

lemma one_lt_div_iff : 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b :=
begin
  rcases lt_trichotomy b 0 with (hb|rfl|hb),
  { simp [hb, hb.not_lt, one_lt_div_of_neg] },
  { simp [lt_irrefl, zero_le_one] },
  { simp [hb, hb.not_lt, one_lt_div] }
end

lemma one_le_div_iff : 1 ≤ a / b ↔ 0 < b ∧ b ≤ a ∨ b < 0 ∧ a ≤ b :=
begin
  rcases lt_trichotomy b 0 with (hb|rfl|hb),
  { simp [hb, hb.not_lt, one_le_div_of_neg] },
  { simp [lt_irrefl, zero_lt_one.not_le, zero_lt_one] },
  { simp [hb, hb.not_lt, one_le_div] }
end

lemma div_lt_one_iff : a / b < 1 ↔ 0 < b ∧ a < b ∨ b = 0 ∨ b < 0 ∧ b < a :=
begin
  rcases lt_trichotomy b 0 with (hb|rfl|hb),
  { simp [hb, hb.not_lt, hb.ne, div_lt_one_of_neg] },
  { simp [zero_lt_one], },
  { simp [hb, hb.not_lt, div_lt_one, hb.ne.symm] }
end

lemma div_le_one_iff : a / b ≤ 1 ↔ 0 < b ∧ a ≤ b ∨ b = 0 ∨ b < 0 ∧ b ≤ a :=
begin
  rcases lt_trichotomy b 0 with (hb|rfl|hb),
  { simp [hb, hb.not_lt, hb.ne, div_le_one_of_neg] },
  { simp [zero_le_one], },
  { simp [hb, hb.not_lt, div_le_one, hb.ne.symm] }
end

/-! ### Relating two divisions, involving `1` -/

lemma one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a :=
by rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]

lemma one_div_lt_one_div_of_neg_of_lt (hb : b < 0) (h : a < b) : 1 / b < 1 / a :=
by rwa [div_lt_iff_of_neg' hb, ← div_eq_mul_one_div, div_lt_one_of_neg (h.trans hb)]

lemma le_of_neg_of_one_div_le_one_div (hb : b < 0) (h : 1 / a ≤ 1 / b) : b ≤ a :=
le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_neg_of_lt hb) h

lemma lt_of_neg_of_one_div_lt_one_div (hb : b < 0) (h : 1 / a < 1 / b) : b < a :=
lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_neg_of_le hb) h

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_neg_of_lt` and
  `lt_of_one_div_lt_one_div` -/
lemma one_div_le_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ 1 / b ↔ b ≤ a :=
by simpa [one_div] using inv_le_inv_of_neg ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
lemma one_div_lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < 1 / b ↔ b < a :=
lt_iff_lt_of_le_iff_le (one_div_le_one_div_of_neg hb ha)

lemma one_div_lt_neg_one (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
suffices 1 / a < 1 / -1, by rwa one_div_neg_one_eq_neg_one at this,
one_div_lt_one_div_of_neg_of_lt h1 h2

lemma one_div_le_neg_one (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 :=
suffices 1 / a ≤ 1 / -1, by rwa one_div_neg_one_eq_neg_one at this,
one_div_le_one_div_of_neg_of_le h1 h2

/-! ### Results about halving -/

lemma sub_self_div_two (a : α) : a - a / 2 = a / 2 :=
suffices a / 2 + a / 2 - a / 2 = a / 2, by rwa add_halves at this,
by rw [add_sub_cancel]

lemma div_two_sub_self (a : α) : a / 2 - a = - (a / 2) :=
suffices a / 2 - (a / 2 + a / 2) = - (a / 2), by rwa add_halves at this,
by rw [sub_add_eq_sub_sub, sub_self, zero_sub]

lemma add_sub_div_two_lt (h : a < b) : a + (b - a) / 2 < b :=
begin
  rwa [← div_sub_div_same, sub_eq_add_neg, add_comm (b/2), ← add_assoc, ← sub_eq_add_neg,
    ← lt_sub_iff_add_lt, sub_self_div_two, sub_self_div_two, div_lt_div_right (@zero_lt_two α _ _)]
end

/--  An inequality involving `2`. -/
lemma sub_one_div_inv_le_two (a2 : 2 ≤ a) : (1 - 1 / a)⁻¹ ≤ 2 :=
begin
  -- Take inverses on both sides to obtain `2⁻¹ ≤ 1 - 1 / a`
  refine (inv_le_inv_of_le (inv_pos.2 $ zero_lt_two' α) _).trans_eq (inv_inv (2 : α)),
  -- move `1 / a` to the left and `1 - 1 / 2 = 1 / 2` to the right to obtain `1 / a ≤ ⅟ 2`
  refine (le_sub_iff_add_le.2 (_ : _ + 2⁻¹ = _ ).le).trans ((sub_le_sub_iff_left 1).2 _),
  { -- show 2⁻¹ + 2⁻¹ = 1
    exact (two_mul _).symm.trans (mul_inv_cancel two_ne_zero) },
  { -- take inverses on both sides and use the assumption `2 ≤ a`.
    exact (one_div a).le.trans (inv_le_inv_of_le zero_lt_two a2) }
end

/-! ### Results about `is_lub` and `is_glb` -/

-- TODO: Generalize to `linear_ordered_semifield`
lemma is_lub.mul_left {s : set α} (ha : 0 ≤ a) (hs : is_lub s b) :
  is_lub ((λ b, a * b) '' s) (a * b) :=
begin
  rcases lt_or_eq_of_le ha with ha | rfl,
  { exact (order_iso.mul_left₀ _ ha).is_lub_image'.2 hs, },
  { simp_rw zero_mul,
    rw hs.nonempty.image_const,
    exact is_lub_singleton },
end

-- TODO: Generalize to `linear_ordered_semifield`
lemma is_lub.mul_right {s : set α} (ha : 0 ≤ a) (hs : is_lub s b) :
  is_lub ((λ b, b * a) '' s) (b * a) :=
by simpa [mul_comm] using hs.mul_left ha

/-! ### Miscellaneous lemmmas -/

lemma mul_sub_mul_div_mul_neg_iff (hc : c ≠ 0) (hd : d ≠ 0) :
  (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d :=
by rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_lt_zero]

lemma mul_sub_mul_div_mul_nonpos_iff (hc : c ≠ 0) (hd : d ≠ 0) :
  (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d :=
by rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_nonpos]

alias mul_sub_mul_div_mul_neg_iff ↔ div_lt_div_of_mul_sub_mul_div_neg mul_sub_mul_div_mul_neg
alias mul_sub_mul_div_mul_nonpos_iff ↔
  div_le_div_of_mul_sub_mul_div_nonpos mul_sub_mul_div_mul_nonpos

lemma exists_add_lt_and_pos_of_lt (h : b < a) : ∃ c, b + c < a ∧ 0 < c :=
⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) zero_lt_two⟩

lemma le_of_forall_sub_le (h : ∀ ε > 0, b - ε ≤ a) : b ≤ a :=
begin
  contrapose! h,
  simpa only [and_comm ((0 : α) < _), lt_sub_iff_add_lt, gt_iff_lt]
    using exists_add_lt_and_pos_of_lt h,
end

lemma mul_self_inj_of_nonneg (a0 : 0 ≤ a) (b0 : 0 ≤ b) : a * a = b * b ↔ a = b :=
mul_self_eq_mul_self_iff.trans $ or_iff_left_of_imp $
  λ h, by { subst a, have : b = 0 := le_antisymm (neg_nonneg.1 a0) b0, rw [this, neg_zero] }

lemma min_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : min (a / c) (b / c) = (max a b) / c :=
eq.symm $ antitone.map_max $ λ x y, div_le_div_of_nonpos_of_le hc

lemma max_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) : max (a / c) (b / c) = (min a b) / c :=
eq.symm $ antitone.map_min $ λ x y, div_le_div_of_nonpos_of_le hc

lemma abs_inv (a : α) : |a⁻¹| = (|a|)⁻¹ := map_inv₀ (abs_hom : α →*₀ α) a
lemma abs_div (a b : α) : |a / b| = |a| / |b| := map_div₀ (abs_hom : α →*₀ α) a b
lemma abs_one_div (a : α) : |1 / a| = 1 / |a| := by rw [abs_div, abs_one]

lemma pow_minus_two_nonneg : 0 ≤ a^(-2 : ℤ) :=
begin
  simp only [inv_nonneg, zpow_neg],
  change 0 ≤ a ^ ((2 : ℕ) : ℤ),
  rw zpow_coe_nat,
  apply sq_nonneg,
end

/-- Bernoulli's inequality reformulated to estimate `(n : α)`. -/
lemma nat.cast_le_pow_sub_div_sub (H : 1 < a)  (n : ℕ) : (n : α) ≤ (a ^ n - 1) / (a - 1) :=
(le_div_iff (sub_pos.2 H)).2 $ le_sub_left_of_add_le $
  one_add_mul_sub_le_pow ((neg_le_self zero_le_one).trans H.le) _

/-- For any `a > 1` and a natural `n` we have `n ≤ a ^ n / (a - 1)`. See also
`nat.cast_le_pow_sub_div_sub` for a stronger inequality with `a ^ n - 1` in the numerator. -/
theorem nat.cast_le_pow_div_sub (H : 1 < a) (n : ℕ) : (n : α) ≤ a ^ n / (a - 1) :=
(n.cast_le_pow_sub_div_sub H).trans $ div_le_div_of_le (sub_nonneg.2 H.le)
  (sub_le_self _ zero_le_one)

end

section canonically_linear_ordered_semifield
variables [canonically_linear_ordered_semifield α] [has_sub α] [has_ordered_sub α]

lemma tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]

end canonically_linear_ordered_semifield
