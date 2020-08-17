/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import algebra.ordered_ring
import algebra.field
/-!
  ### Linear ordered fields
  A linear ordered field is a field equipped with a linear order such that
  * addition respects the order: `a ≤ b → c + a ≤ c + b`;
  * multiplication of positives is positive: `0 < a → 0 < b → 0 < a * b`;
  * `0 < 1`.

  ### Main Definitions
  * `linear_ordered_field`: the class of linear ordered fields.
  * `discrete_linear_ordered_field`: the class of linear ordered fields where the inequality is
    decidable.
-/

set_option default_priority 100 -- see Note [default priority]
set_option old_structure_cmd true

variable {α : Type*}

/-- A linear ordered field is a field with a linear order respecting the operations. -/
@[protect_proj] class linear_ordered_field (α : Type*) extends linear_ordered_comm_ring α, field α

section linear_ordered_field
variables [linear_ordered_field α] {a b c d e : α}

/-!
### Lemmas about pos, nonneg, nonpos, neg
-/

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ 0 < a :=
suffices ∀ a : α, 0 < a → 0 < a⁻¹,
from ⟨λ h, inv_inv' a ▸ this _ h, this a⟩,
assume a ha, flip lt_of_mul_lt_mul_left ha.le $ by simp [ne_of_gt ha, zero_lt_one]

@[simp] lemma inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a :=
by simp only [le_iff_eq_or_lt, inv_pos, zero_eq_inv]

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
mul_pos ha (inv_pos.2 hb)

lemma div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b :=
mul_pos_of_neg_of_neg ha (inv_lt_zero.2 hb)

lemma div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
mul_neg_of_neg_of_pos ha (inv_pos.2 hb)

lemma div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
mul_neg_of_pos_of_neg ha (inv_lt_zero.2 hb)

lemma div_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
mul_nonneg ha (inv_nonneg.2 hb)

lemma div_nonneg_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b :=
mul_nonneg_of_nonpos_of_nonpos ha (inv_nonpos.2 hb)

lemma div_nonpos_of_nonpos_of_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a / b ≤ 0 :=
mul_nonpos_of_nonpos_of_nonneg ha (inv_nonneg.2 hb)

lemma div_nonpos_of_nonneg_of_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a / b ≤ 0 :=
mul_nonpos_of_nonneg_of_nonpos ha (inv_nonpos.2 hb)

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

lemma div_le_iff_of_neg (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b :=
⟨λ h, div_mul_cancel b (ne_of_lt hc) ▸ mul_le_mul_of_nonpos_right h hc.le,
  λ h, calc
    a = a * c * (1 / c) : mul_mul_div a (ne_of_lt hc)
  ... ≥ b * (1 / c)     : mul_le_mul_of_nonpos_right h (one_div_neg.2 hc).le
  ... = b / c           : (div_eq_mul_one_div b c).symm⟩

lemma div_le_iff_of_neg' (hc : c < 0) : b / c ≤ a ↔ c * a ≤ b :=
by rw [mul_comm, div_le_iff_of_neg hc]

lemma le_div_iff_of_neg (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c :=
by rw [← neg_neg c, mul_neg_eq_neg_mul_symm, div_neg, le_neg,
    div_le_iff (neg_pos.2 hc), neg_mul_eq_neg_mul_symm]

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

/-- One direction of `div_le_iff` where `b` is allowed to be `0` (but `c` must be nonnegative) -/
lemma div_le_iff_of_nonneg_of_le (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ c * b) : a / b ≤ c :=
by { rcases eq_or_lt_of_le hb with rfl|hb', simp [hc], rwa [div_le_iff hb'] }

/-!
### Bi-implications of inequalities using inversions
-/

lemma inv_le_inv_of_le (ha : 0 < a) (h : a ≤ b) : b⁻¹ ≤ a⁻¹ :=
by rwa [← one_div a, le_div_iff' ha, ← div_eq_mul_inv, div_le_iff (ha.trans_le h), one_mul]

/-- See `inv_le_inv_of_le` for the implication from right-to-left with one fewer assumption. -/
lemma inv_le_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by rw [← one_div, div_le_iff ha, ← div_eq_inv_mul, le_div_iff hb, one_mul]

lemma inv_le (ha : 0 < a) (hb : 0 < b) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by rw [← inv_le_inv hb (inv_pos.2 ha), inv_inv']

lemma le_inv (ha : 0 < a) (hb : 0 < b) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by rw [← inv_le_inv (inv_pos.2 hb) ha, inv_inv']

lemma inv_lt_inv (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a :=
lt_iff_lt_of_le_iff_le (inv_le_inv hb ha)

lemma inv_lt (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b ↔ b⁻¹ < a :=
lt_iff_lt_of_le_iff_le (le_inv hb ha)

lemma lt_inv (ha : 0 < a) (hb : 0 < b) : a < b⁻¹ ↔ b < a⁻¹ :=
lt_iff_lt_of_le_iff_le (inv_le hb ha)

lemma inv_le_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by rw [← one_div, div_le_iff_of_neg ha, ← div_eq_inv_mul, div_le_iff_of_neg hb, one_mul]

lemma inv_le_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by rw [← inv_le_inv_of_neg hb (inv_lt_zero.2 ha), inv_inv']

lemma le_inv_of_neg (ha : a < 0) (hb : b < 0) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by rw [← inv_le_inv_of_neg (inv_lt_zero.2 hb) ha, inv_inv']

lemma inv_lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b⁻¹ ↔ b < a :=
lt_iff_lt_of_le_iff_le (inv_le_inv_of_neg hb ha)

lemma inv_lt_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a :=
lt_iff_lt_of_le_iff_le (le_inv_of_neg hb ha)

lemma lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a⁻¹ :=
lt_iff_lt_of_le_iff_le (inv_le_of_neg hb ha)

lemma inv_lt_one (ha : 1 < a) : a⁻¹ < 1 :=
by rwa [inv_lt ((@zero_lt_one α _).trans ha) zero_lt_one, inv_one]

lemma one_lt_inv (h₁ : 0 < a) (h₂ : a < 1) : 1 < a⁻¹ :=
by rwa [lt_inv (@zero_lt_one α _) h₁, inv_one]

lemma inv_le_one (ha : 1 ≤ a) : a⁻¹ ≤ 1 :=
by rwa [inv_le ((@zero_lt_one α _).trans_le ha) zero_lt_one, inv_one]

lemma one_le_inv (h₁ : 0 < a) (h₂ : a ≤ 1) : 1 ≤ a⁻¹ :=
by rwa [le_inv (@zero_lt_one α _) h₁, inv_one]

/-!
### Relating two divisions.
-/

lemma div_le_div_of_le (hc : 0 ≤ c) (h : a ≤ b) : a / c ≤ b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_le_mul_of_nonneg_right h (one_div_nonneg.2 hc)
end

lemma div_le_div_of_le_left (ha : 0 ≤ a) (hc : 0 < c) (h : c ≤ b) : a / b ≤ a / c :=
begin
  rw [div_eq_mul_inv, div_eq_mul_inv],
  exact mul_le_mul_of_nonneg_left ((inv_le_inv (hc.trans_le h) hc).mpr h) ha
end

lemma div_le_div_of_le_of_nonneg (hab : a ≤ b) (hc : 0 ≤ c) : a / c ≤ b / c :=
mul_le_mul_of_nonneg_right hab (inv_nonneg.2 hc)

lemma div_le_div_of_nonpos_of_le (hc : c ≤ 0) (h : b ≤ a) : a / c ≤ b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_le_mul_of_nonpos_right h (one_div_nonpos.2 hc)
end

lemma div_lt_div_of_lt (hc : 0 < c) (h : a < b) : a / c < b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_lt_mul_of_pos_right h (one_div_pos.2 hc)
end

lemma div_lt_div_of_neg_of_lt (hc : c < 0) (h : b < a) : a / c < b / c :=
begin
  rw [div_eq_mul_one_div a c, div_eq_mul_one_div b c],
  exact mul_lt_mul_of_neg_right h (one_div_neg.2 hc)
end

lemma div_le_div_right (hc : 0 < c) : a / c ≤ b / c ↔ a ≤ b :=
⟨le_imp_le_of_lt_imp_lt $ div_lt_div_of_lt hc, div_le_div_of_le $ hc.le⟩

lemma div_le_div_right_of_neg (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a :=
⟨le_imp_le_of_lt_imp_lt $ div_lt_div_of_neg_of_lt hc, div_le_div_of_nonpos_of_le $ hc.le⟩

lemma div_lt_div_right (hc : 0 < c) : a / c < b / c ↔ a < b :=
lt_iff_lt_of_le_iff_le $ div_le_div_right hc

lemma div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a :=
lt_iff_lt_of_le_iff_le $ div_le_div_right_of_neg hc

lemma div_lt_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b < a / c ↔ c < b :=
(mul_lt_mul_left ha).trans (inv_lt_inv hb hc)

lemma div_le_div_left (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b ≤ a / c ↔ c ≤ b :=
le_iff_le_iff_lt_iff_lt.2 (div_lt_div_left ha hc hb)

lemma div_lt_div_iff (b0 : 0 < b) (d0 : 0 < d) :
  a / b < c / d ↔ a * d < c * b :=
by rw [lt_div_iff d0, div_mul_eq_mul_div, div_lt_iff b0]

lemma div_le_div_iff (b0 : 0 < b) (d0 : 0 < d) : a / b ≤ c / d ↔ a * d ≤ c * b :=
by rw [le_div_iff d0, div_mul_eq_mul_div, div_le_iff b0]

lemma div_le_div (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hbd : d ≤ b) : a / b ≤ c / d :=
by { rw div_le_div_iff (hd.trans_le hbd) hd, exact mul_le_mul hac hbd hd.le hc }

lemma div_lt_div (hac : a < c) (hbd : d ≤ b) (c0 : 0 ≤ c) (d0 : 0 < d) :
  a / b < c / d :=
(div_lt_div_iff (d0.trans_le hbd) d0).2 (mul_lt_mul hac hbd d0 c0)

lemma div_lt_div' (hac : a ≤ c) (hbd : d < b) (c0 : 0 < c) (d0 : 0 < d) :
  a / b < c / d :=
(div_lt_div_iff (d0.trans hbd) d0).2 (mul_lt_mul' hac hbd d0.le c0)

lemma div_lt_div_of_lt_left (hb : 0 < b) (h : b < a) (hc : 0 < c) : c / a < c / b :=
(div_lt_div_left hc (hb.trans h) hb).mpr h

/-!
### Relating one division and involving `1`
-/

lemma one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a :=
by rw [le_div_iff hb, one_mul]

lemma div_le_one (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b :=
by rw [div_le_iff hb, one_mul]

lemma one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a :=
by rw [lt_div_iff hb, one_mul]

lemma div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b :=
by rw [div_lt_iff hb, one_mul]

lemma one_le_div_of_neg (hb : b < 0) : 1 ≤ a / b ↔ a ≤ b :=
by rw [le_div_iff_of_neg hb, one_mul]

lemma div_le_one_of_neg (hb : b < 0) : a / b ≤ 1 ↔ b ≤ a :=
by rw [div_le_iff_of_neg hb, one_mul]

lemma one_lt_div_of_neg (hb : b < 0) : 1 < a / b ↔ a < b :=
by rw [lt_div_iff_of_neg hb, one_mul]

lemma div_lt_one_of_neg (hb : b < 0) : a / b < 1 ↔ b < a :=
by rw [div_lt_iff_of_neg hb, one_mul]

lemma one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ b ↔ 1 / b ≤ a :=
by simpa using inv_le ha hb

lemma one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a :=
by simpa using inv_lt ha hb

lemma le_one_div (ha : 0 < a) (hb : 0 < b) : a ≤ 1 / b ↔ b ≤ 1 / a :=
by simpa using le_inv ha hb

lemma lt_one_div (ha : 0 < a) (hb : 0 < b) : a < 1 / b ↔ b < 1 / a :=
by simpa using lt_inv ha hb

lemma one_div_le_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ b ↔ 1 / b ≤ a :=
by simpa using inv_le_of_neg ha hb

lemma one_div_lt_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < b ↔ 1 / b < a :=
by simpa using inv_lt_of_neg ha hb

lemma le_one_div_of_neg (ha : a < 0) (hb : b < 0) : a ≤ 1 / b ↔ b ≤ 1 / a :=
by simpa using le_inv_of_neg ha hb

lemma lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : a < 1 / b ↔ b < 1 / a :=
by simpa using lt_inv_of_neg ha hb

/-!
### Relating two divisions, involving `1`
-/
lemma one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a :=
by simpa using inv_le_inv_of_le ha h

lemma one_div_lt_one_div_of_lt (ha : 0 < a) (h : a < b) : 1 / b < 1 / a :=
by rwa [lt_div_iff' ha, ← div_eq_mul_one_div, div_lt_one (ha.trans h)]

lemma one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a :=
by rwa [div_le_iff_of_neg' hb, ← div_eq_mul_one_div, div_le_one_of_neg (h.trans_lt hb)]

lemma one_div_lt_one_div_of_neg_of_lt (hb : b < 0) (h : a < b) : 1 / b < 1 / a :=
by rwa [div_lt_iff_of_neg' hb, ← div_eq_mul_one_div, div_lt_one_of_neg (h.trans hb)]

lemma le_of_one_div_le_one_div (ha : 0 < a) (h : 1 / a ≤ 1 / b) : b ≤ a :=
le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_lt ha) h

lemma lt_of_one_div_lt_one_div (ha : 0 < a) (h : 1 / a < 1 / b) : b < a :=
lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_le ha) h

lemma le_of_neg_of_one_div_le_one_div (hb : b < 0) (h : 1 / a ≤ 1 / b) : b ≤ a :=
le_imp_le_of_lt_imp_lt (one_div_lt_one_div_of_neg_of_lt hb) h

lemma lt_of_neg_of_one_div_lt_one_div (hb : b < 0) (h : 1 / a < 1 / b) : b < a :=
lt_imp_lt_of_le_imp_le (one_div_le_one_div_of_neg_of_le hb) h

/-- For the single implications with fewer assumptions, see `one_div_le_one_div_of_le` and
  `le_of_one_div_le_one_div` -/
lemma one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
div_le_div_left zero_lt_one ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
lemma one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
div_lt_div_left zero_lt_one ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_neg_of_lt` and
  `lt_of_one_div_lt_one_div` -/
lemma one_div_le_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ 1 / b ↔ b ≤ a :=
by simpa [one_div] using inv_le_inv_of_neg ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
lemma one_div_lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < 1 / b ↔ b < a :=
lt_iff_lt_of_le_iff_le (one_div_le_one_div_of_neg hb ha)

lemma one_lt_one_div (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a :=
by rwa [lt_one_div (@zero_lt_one α _) h1, one_div_one]

lemma one_le_one_div (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a :=
by rwa [le_one_div (@zero_lt_one α _) h1, one_div_one]

lemma one_div_lt_neg_one (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 :=
suffices 1 / a < 1 / -1, by rwa one_div_neg_one_eq_neg_one at this,
one_div_lt_one_div_of_neg_of_lt h1 h2

lemma one_div_le_neg_one (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 :=
suffices 1 / a ≤ 1 / -1, by rwa one_div_neg_one_eq_neg_one at this,
one_div_le_one_div_of_neg_of_le h1 h2

/-!
### Results about halving.

The equalities also hold in fields of characteristic `0`. -/
lemma add_halves (a : α) : a / 2 + a / 2 = a :=
by rw [div_add_div_same, ← two_mul, mul_div_cancel_left a two_ne_zero]

lemma sub_self_div_two (a : α) : a - a / 2 = a / 2 :=
suffices a / 2 + a / 2 - a / 2 = a / 2, by rwa add_halves at this,
by rw [add_sub_cancel]

lemma div_two_sub_self (a : α) : a / 2 - a = - (a / 2) :=
suffices a / 2 - (a / 2 + a / 2) = - (a / 2), by rwa add_halves at this,
by rw [sub_add_eq_sub_sub, sub_self, zero_sub]

lemma add_self_div_two (a : α) : (a + a) / 2 = a :=
by rw [← mul_two, mul_div_cancel a two_ne_zero]

lemma half_pos (h : 0 < a) : 0 < a / 2 := div_pos h two_pos

lemma one_half_pos : (0:α) < 1 / 2 := half_pos zero_lt_one

lemma div_two_lt_of_pos (h : 0 < a) : a / 2 < a :=
by { rw [div_lt_iff (@two_pos α _)], exact lt_mul_of_one_lt_right h one_lt_two }

lemma half_lt_self : 0 < a → a / 2 < a := div_two_lt_of_pos

lemma one_half_lt_one : (1 / 2 : α) < 1 := half_lt_self zero_lt_one

lemma add_sub_div_two_lt (h : a < b) : a + (b - a) / 2 < b :=
begin
  rwa [← div_sub_div_same, sub_eq_add_neg, add_comm (b/2), ← add_assoc, ← sub_eq_add_neg,
    ← lt_sub_iff_add_lt, sub_self_div_two, sub_self_div_two, div_lt_div_right (@two_pos α _)]
end


/-!
### Miscellaneous lemmas
-/

lemma mul_sub_mul_div_mul_neg_iff (hc : c ≠ 0) (hd : d ≠ 0) :
  (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d :=
by rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_lt_zero]

alias mul_sub_mul_div_mul_neg_iff ↔ div_lt_div_of_mul_sub_mul_div_neg mul_sub_mul_div_mul_neg

lemma mul_sub_mul_div_mul_nonpos_iff (hc : c ≠ 0) (hd : d ≠ 0) :
      (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d :=
by rw [mul_comm b c, ← div_sub_div _ _ hc hd, sub_nonpos]

alias mul_sub_mul_div_mul_nonpos_iff ↔
  div_le_div_of_mul_sub_mul_div_nonpos mul_sub_mul_div_mul_nonpos

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

lemma exists_add_lt_and_pos_of_lt (h : b < a) : ∃ c : α, b + c < a ∧ 0 < c :=
⟨(a - b) / 2, add_sub_div_two_lt h, div_pos (sub_pos_of_lt h) two_pos⟩

lemma le_of_forall_sub_le (h : ∀ ε > 0, b - ε ≤ a) : b ≤ a :=
begin
  contrapose! h,
  simpa only [and_comm ((0 : α) < _), lt_sub_iff_add_lt, gt_iff_lt]
    using exists_add_lt_and_pos_of_lt h,
end

lemma monotone.div_const {β : Type*} [preorder β] {f : β → α} (hf : monotone f)
  {c : α} (hc : 0 ≤ c) : monotone (λ x, (f x) / c) :=
hf.mul_const (inv_nonneg.2 hc)

lemma strict_mono.div_const {β : Type*} [preorder β] {f : β → α} (hf : strict_mono f)
  {c : α} (hc : 0 < c) :
  strict_mono (λ x, (f x) / c) :=
hf.mul_const (inv_pos.2 hc)

instance linear_ordered_field.to_densely_ordered : densely_ordered α :=
{ dense := λ a₁ a₂ h, ⟨(a₁ + a₂) / 2,
  calc a₁ = (a₁ + a₁) / 2 : (add_self_div_two a₁).symm
      ... < (a₁ + a₂) / 2 : div_lt_div_of_lt two_pos (add_lt_add_left h _),
  calc (a₁ + a₂) / 2 < (a₂ + a₂) / 2 : div_lt_div_of_lt two_pos (add_lt_add_right h _)
                 ... = a₂            : add_self_div_two a₂⟩ }

instance linear_ordered_field.to_no_top_order : no_top_order α :=
{ no_top := λ a, ⟨a + 1, lt_add_of_le_of_pos (le_refl a) zero_lt_one ⟩ }

instance linear_ordered_field.to_no_bot_order : no_bot_order α :=
{ no_bot := λ a, ⟨a + -1, add_lt_of_le_of_neg (le_refl _) neg_one_lt_zero ⟩ }

lemma mul_self_inj_of_nonneg (a0 : 0 ≤ a) (b0 : 0 ≤ b) : a * a = b * b ↔ a = b :=
mul_self_eq_mul_self_iff.trans $ or_iff_left_of_imp $
  λ h, by { subst a, have : b = 0 := le_antisymm (neg_nonneg.1 a0) b0, rw [this, neg_zero] }

end linear_ordered_field

/-- A discrete linear ordered field is a field with a decidable linear order respecting the
  operations. -/
@[protect_proj] class discrete_linear_ordered_field (α : Type*)
  extends linear_ordered_field α, decidable_linear_ordered_comm_ring α

section discrete_linear_ordered_field
variables [discrete_linear_ordered_field α]

lemma abs_div (a b : α) : abs (a / b) = abs a / abs b :=
decidable.by_cases
  (assume h : b = 0, by rw [h, abs_zero, div_zero, div_zero, abs_zero])
  (assume h : b ≠ 0,
   have h₁ : abs b ≠ 0, from mt eq_zero_of_abs_eq_zero h,
   eq_div_of_mul_eq h₁ (show abs (a / b) * abs b = abs a, by rw [← abs_mul, div_mul_cancel _ h]))

lemma abs_one_div (a : α) : abs (1 / a) = 1 / abs a :=
by rw [abs_div, abs_of_nonneg (zero_le_one : 1 ≥ (0 : α))]

lemma abs_inv (a : α) : abs a⁻¹ = (abs a)⁻¹ :=
have h : abs (1 / a) = 1 / abs a,
  by { rw [abs_div, abs_of_nonneg], exact zero_le_one },
by simp * at *

end discrete_linear_ordered_field
