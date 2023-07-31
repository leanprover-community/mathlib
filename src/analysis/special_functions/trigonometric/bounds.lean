/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.special_functions.trigonometric.arctan_deriv

/-!
# Polynomial bounds for trigonometric functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main statements

This file contains upper and lower bounds for real trigonometric functions in terms
of polynomials. See `trigonometric.basic` for more elementary inequalities, establishing
the ranges of these functions, and their monotonicity in suitable intervals.

Here we prove the following:

* `sin_lt`: for `x > 0` we have `sin x < x`.
* `sin_gt_sub_cube`: For `0 < x ≤ 1` we have `x - x ^ 3 / 4 < sin x`.
* `lt_tan`: for `0 < x < π/2` we have `x < tan x`.
* `cos_le_one_div_sqrt_sq_add_one` and `cos_lt_one_div_sqrt_sq_add_one`: for
  `-3 * π / 2 ≤ x ≤ 3 * π / 2`, we have `cos x ≤ 1 / sqrt (x ^ 2 + 1)`, with strict inequality if
  `x ≠ 0`. (This bound is not quite optimal, but not far off)

## Tags

sin, cos, tan, angle
-/

noncomputable theory
open set

namespace real
open_locale real

/-- For 0 < x, we have sin x < x. -/
lemma sin_lt {x : ℝ} (h : 0 < x) : sin x < x :=
begin
  cases lt_or_le 1 x with h' h',
  { exact (sin_le_one x).trans_lt h' },
  have hx : |x| = x := abs_of_nonneg h.le,
  have := le_of_abs_le (sin_bound $ show |x| ≤ 1, by rwa [hx]),
  rw [sub_le_iff_le_add', hx] at this,
  apply this.trans_lt,
  rw [sub_add, sub_lt_self_iff, sub_pos, div_eq_mul_inv (x ^ 3)],
  refine mul_lt_mul' _ (by norm_num) (by norm_num) (pow_pos h 3),
  apply pow_le_pow_of_le_one h.le h',
  norm_num
end

/-- For 0 < x ≤ 1 we have x - x ^ 3 / 4 < sin x.

This is also true for x > 1, but it's nontrivial for x just above 1. This inequality is not
tight; the tighter inequality is sin x > x - x ^ 3 / 6 for all x > 0, but this inequality has
a simpler proof. -/
lemma sin_gt_sub_cube {x : ℝ} (h : 0 < x) (h' : x ≤ 1) : x - x ^ 3 / 4 < sin x :=
begin
  have hx : |x| = x := abs_of_nonneg h.le,
  have := neg_le_of_abs_le (sin_bound $ show |x| ≤ 1, by rwa [hx]),
  rw [le_sub_iff_add_le, hx] at this,
  refine lt_of_lt_of_le _ this,
  have : x ^ 3 / 4 - x ^ 3 / 6 = x ^ 3 * 12⁻¹ := by norm_num [div_eq_mul_inv, ← mul_sub],
  rw [add_comm, sub_add, sub_neg_eq_add, sub_lt_sub_iff_left, ←lt_sub_iff_add_lt', this],
  refine mul_lt_mul' _ (by norm_num) (by norm_num) (pow_pos h 3),
  apply pow_le_pow_of_le_one h.le h',
  norm_num
end


/-- The derivative of `tan x - x` is `1/(cos x)^2 - 1` away from the zeroes of cos. -/
lemma deriv_tan_sub_id (x : ℝ) (h : cos x ≠ 0) :
    deriv (λ y : ℝ, tan y - y) x = 1 / cos x ^ 2 - 1 :=
has_deriv_at.deriv $ by simpa using (has_deriv_at_tan h).add (has_deriv_at_id x).neg

/-- For all `0 < x < π/2` we have `x < tan x`.

This is proved by checking that the function `tan x - x` vanishes
at zero and has non-negative derivative. -/
theorem lt_tan {x : ℝ} (h1 : 0 < x) (h2 : x < π / 2) : x < tan x :=
begin
  let U := Ico 0 (π / 2),

  have intU : interior U = Ioo 0 (π / 2) := interior_Ico,

  have half_pi_pos : 0 < π / 2 := div_pos pi_pos two_pos,

  have cos_pos : ∀ {y : ℝ}, y ∈ U → 0 < cos y,
  { intros y hy,
    exact cos_pos_of_mem_Ioo (Ico_subset_Ioo_left (neg_lt_zero.mpr half_pi_pos) hy) },

  have sin_pos : ∀ {y : ℝ}, y ∈ interior U → 0 < sin y,
  { intros y hy,
    rw intU at hy,
    exact sin_pos_of_mem_Ioo (Ioo_subset_Ioo_right (div_le_self pi_pos.le one_le_two) hy) },

  have tan_cts_U : continuous_on tan U,
  { apply continuous_on.mono continuous_on_tan,
    intros z hz,
    simp only [mem_set_of_eq],
    exact (cos_pos hz).ne' },

  have tan_minus_id_cts : continuous_on (λ y : ℝ, tan y - y) U :=
    tan_cts_U.sub continuous_on_id,

  have deriv_pos : ∀ y : ℝ, y ∈ interior U → 0 < deriv (λ y' : ℝ, tan y' - y') y,
  { intros y hy,
    have := cos_pos (interior_subset hy),
    simp only [deriv_tan_sub_id y this.ne', one_div, gt_iff_lt, sub_pos],
    have bd2 : cos y ^ 2 < 1,
    { apply lt_of_le_of_ne y.cos_sq_le_one,
      rw cos_sq',
      simpa only [ne.def, sub_eq_self, pow_eq_zero_iff, nat.succ_pos']
        using (sin_pos hy).ne' },
    rwa [lt_inv, inv_one],
    { exact zero_lt_one },
    simpa only [sq, mul_self_pos] using this.ne' },

  have mono := convex.strict_mono_on_of_deriv_pos (convex_Ico 0 (π / 2)) tan_minus_id_cts deriv_pos,
  have zero_in_U : (0 : ℝ) ∈ U,
  { rwa left_mem_Ico },
  have x_in_U : x ∈ U := ⟨h1.le, h2⟩,
  simpa only [tan_zero, sub_zero, sub_pos] using mono zero_in_U x_in_U h1
end

lemma le_tan {x : ℝ} (h1 : 0 ≤ x) (h2 : x < π / 2) : x ≤ tan x :=
begin
  rcases eq_or_lt_of_le h1 with rfl | h1',
  { rw tan_zero },
  { exact le_of_lt (lt_tan h1' h2) }
end

lemma cos_lt_one_div_sqrt_sq_add_one {x : ℝ}
  (hx1 : -(3 * π / 2) ≤ x) (hx2 : x ≤ 3 * π / 2) (hx3 : x ≠ 0) :
  cos x < 1 / sqrt (x ^ 2 + 1) :=
begin
  suffices : ∀ {y : ℝ} (hy1 : 0 < y) (hy2 : y ≤ 3 * π / 2), cos y < 1 / sqrt (y ^ 2 + 1),
  { rcases lt_or_lt_iff_ne.mpr hx3.symm,
    { exact this h hx2 },
    { convert this (by linarith : 0 < -x) (by linarith) using 1,
      { rw cos_neg }, { rw neg_sq } } },
  intros y hy1 hy2,
  have hy3 : 0 < y ^ 2 + 1, by linarith [sq_nonneg y],
  rcases lt_or_le y (π / 2) with hy2' | hy1',
  { -- Main case : `0 < y < π / 2`
    have hy4 : 0 < cos y := cos_pos_of_mem_Ioo ⟨by linarith, hy2'⟩,
    rw [←abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith, hy2'.le⟩),
      ←abs_of_nonneg (one_div_nonneg.mpr (sqrt_nonneg _)),  ←sq_lt_sq, div_pow, one_pow,
      sq_sqrt hy3.le, lt_one_div (pow_pos hy4 _) hy3, ←inv_one_add_tan_sq hy4.ne', one_div, inv_inv,
      add_comm, add_lt_add_iff_left, sq_lt_sq, abs_of_pos hy1,
      abs_of_nonneg (tan_nonneg_of_nonneg_of_le_pi_div_two hy1.le hy2'.le)],
    exact real.lt_tan hy1 hy2' },
  { -- Easy case : `π / 2 ≤ y ≤ 3 * π / 2`
    refine lt_of_le_of_lt _ (one_div_pos.mpr $ sqrt_pos_of_pos hy3),
    exact cos_nonpos_of_pi_div_two_le_of_le hy1' (by linarith [pi_pos]) }
end

lemma cos_le_one_div_sqrt_sq_add_one {x : ℝ} (hx1 : -(3 * π / 2) ≤ x) (hx2 : x ≤ 3 * π / 2) :
  cos x ≤ 1 / sqrt (x ^ 2 + 1) :=
begin
  rcases eq_or_ne x 0 with rfl | hx3,
  { simp },
  { exact (cos_lt_one_div_sqrt_sq_add_one hx1 hx2 hx3).le }
end

end real
