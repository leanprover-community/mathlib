/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set algebra.group
open set

universe u
variables {α : Type u}

section
variables [discrete_field α] {a b c : α}

lemma inv_sub_inv_eq (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) :=
have a * b ≠ 0, by simp [mul_eq_zero_iff_eq_zero_or_eq_zero, ha, hb],
calc (a⁻¹ - b⁻¹) = ((a⁻¹ - b⁻¹) * (a * b)) / (a * b) : by rwa [mul_div_cancel]
  ... = _ :
  begin
    simp [mul_add, add_mul, hb],
    rw [mul_comm a, mul_assoc, mul_comm a⁻¹, mul_inv_cancel ha],
    simp
  end

end

section
variables [linear_ordered_field α] {a b c : α}

lemma le_div_iff_mul_le_of_pos (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b :=
⟨mul_le_of_le_div hc, le_div_of_mul_le hc⟩

lemma div_le_iff_le_mul_of_pos (hb : 0 < b) : a / b ≤ c ↔ a ≤ c * b :=
⟨le_mul_of_div_le hb, by rw [mul_comm]; exact div_le_of_le_mul hb⟩

lemma lt_div_iff (h : 0 < c) : a < b / c ↔ a * c < b :=
⟨mul_lt_of_lt_div h, lt_div_of_mul_lt h⟩

lemma ivl_translate : (λx, x + c) '' {r:α | a ≤ r ∧ r ≤ b } = {r:α | a + c ≤ r ∧ r ≤ b + c} :=
calc (λx, x + c) '' {r | a ≤ r ∧ r ≤ b } = (λx, x - c) ⁻¹' {r | a ≤ r ∧ r ≤ b } :
    congr_fun (image_eq_preimage_of_inverse _ _
      (assume a, add_sub_cancel a c) (assume b, sub_add_cancel b c)) _
  ... = {r | a + c ≤ r ∧ r ≤ b + c} :
    set.ext $ by simp [-sub_eq_add_neg, le_sub_iff_add_le, sub_le_iff_le_add]

lemma ivl_stretch (hc : 0 < c) : (λx, x * c) '' {r | a ≤ r ∧ r ≤ b } = {r | a * c ≤ r ∧ r ≤ b * c} :=
calc (λx, x * c) '' {r | a ≤ r ∧ r ≤ b } = (λx, x / c) ⁻¹' {r | a ≤ r ∧ r ≤ b } :
    congr_fun (image_eq_preimage_of_inverse _ _
      (assume a, mul_div_cancel _ $ ne_of_gt hc) (assume b, div_mul_cancel _ $ ne_of_gt hc)) _
  ... = {r | a * c ≤ r ∧ r ≤ b * c} :
    set.ext $ by simp [le_div_iff_mul_le_of_pos, div_le_iff_le_mul_of_pos, hc]

instance linear_ordered_field.to_densely_ordered [linear_ordered_field α] : densely_ordered α :=
{ dense := assume a₁ a₂ h, ⟨(a₁ + a₂) / 2,
  calc a₁ = (a₁ + a₁) / 2 : (add_self_div_two a₁).symm
    ... < (a₁ + a₂) / 2 : div_lt_div_of_lt_of_pos (add_lt_add_left h _) two_pos,
  calc (a₁ + a₂) / 2 < (a₂ + a₂) / 2 : div_lt_div_of_lt_of_pos (add_lt_add_right h _) two_pos
    ... = a₂ : add_self_div_two a₂⟩ }

instance linear_ordered_field.to_no_top_order [linear_ordered_field α] : no_top_order α :=
{ no_top := assume a, ⟨a + 1, lt_add_of_le_of_pos (le_refl a) zero_lt_one ⟩ }

instance linear_ordered_field.to_no_bot_order [linear_ordered_field α] : no_bot_order α :=
{ no_bot := assume a, ⟨a + -1,
    add_lt_of_le_of_neg (le_refl _) (neg_lt_of_neg_lt $ by simp [zero_lt_one]) ⟩ }

end

section
variables [discrete_linear_ordered_field α] (a b c: α) 

lemma abs_inv : abs a⁻¹ = (abs a)⁻¹ :=
have h : abs (1 / a) = 1 / abs a,
  begin rw [abs_div, abs_of_nonneg], exact zero_le_one end,
by simp [*] at *

lemma inv_neg : (-a)⁻¹ = -(a⁻¹) :=
if h : a = 0
then by simp [h, inv_zero]
else by rwa [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

end
