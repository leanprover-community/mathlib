/-
Copyright (c) 2021 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
import analysis.special_functions.integrals

/-! # The Wallis formula for Pi

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file establishes the Wallis product for `π` (`real.tendsto_prod_pi_div_two`). Our proof is
largely about analyzing the behaviour of the sequence `∫_{0}^{π} x, sin x ^ n` as `n → ∞`.
See: https://en.wikipedia.org/wiki/Wallis_product

The proof can be broken down into two pieces. The first step (carried out in
`analysis.special_functions.integrals`) is to use repeated integration by parts to obtain an
explicit formula for this integral, which is rational if `n` is odd and a rational multiple of `π`
if `n` is even.

The second step, carried out here, is to estimate the ratio
`∫_{0}^{π} x, sin x ^ (2 * k + 1) / ∫_{0}^{π} x, sin x ^ (2 * k)` and prove that
it converges to one using the squeeze theorem. The final product for `π` is obtained after some
algebraic manipulation.

## Main statements

* `real.wallis.W`: the product of the first `k` terms in Wallis' formula for `π`.
* `real.wallis.W_eq_integral_sin_pow_div_integral_sin_pow`: express `W n` as a ratio of integrals.
* `real.wallis.W_le` and `real.wallis.le_W`: upper and lower bounds for `W n`.
* `real.tendsto_prod_pi_div_two`: the Wallis product formula.
 -/

open_locale real topology big_operators nat
open filter finset interval_integral

namespace real

namespace wallis

/-- The product of the first `k` terms in Wallis' formula for `π`. -/
noncomputable def W (k : ℕ) : ℝ :=
∏ i in range k, (2 * i + 2) / (2 * i + 1) * ((2 * i + 2) / (2 * i + 3))

lemma W_succ (k : ℕ) :
  W (k + 1) = W k * ((2 * k + 2) / (2 * k + 1) * ((2 * k + 2) / (2 * k + 3))) :=
prod_range_succ _ _

lemma W_pos (k : ℕ) : 0 < W k :=
begin
  induction k with k hk,
  { unfold W, simp },
  { rw W_succ,
    refine mul_pos hk (mul_pos (div_pos _ _) (div_pos _ _));
    positivity }
end

lemma W_eq_factorial_ratio (n : ℕ) :
  W n = (2 ^ (4 * n) * n! ^ 4) / ((2 * n)!^ 2 * (2 * n + 1)) :=
begin
  induction n with n IH,
  { simp only [W, prod_range_zero, nat.factorial_zero, mul_zero, pow_zero, algebra_map.coe_one,
      one_pow, mul_one, algebra_map.coe_zero, zero_add, div_self, ne.def, one_ne_zero,
      not_false_iff] },
  { unfold W at ⊢ IH,
    rw [prod_range_succ, IH, _root_.div_mul_div_comm, _root_.div_mul_div_comm],
    refine (div_eq_div_iff _ _).mpr _,
    any_goals { exact ne_of_gt (by positivity) },
    simp_rw [nat.mul_succ, nat.factorial_succ, pow_succ],
    push_cast,
    ring_nf }
end

lemma W_eq_integral_sin_pow_div_integral_sin_pow (k : ℕ) :
  (π/2)⁻¹ * W k = (∫_{0}^{π} x, sin x ^ (2 * k + 1)) / ∫_{0}^{π} x, sin x ^ (2 * k) :=
begin
  rw [integral_sin_pow_even, integral_sin_pow_odd, mul_div_mul_comm, ←prod_div_distrib, inv_div],
  simp_rw [div_div_div_comm, div_div_eq_mul_div, mul_div_assoc],
  refl,
end

lemma W_le (k : ℕ) : W k ≤ π / 2 :=
begin
  rw [←div_le_one pi_div_two_pos, div_eq_inv_mul],
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, div_le_one (integral_sin_pow_pos _)],
  apply integral_sin_pow_succ_le,
end

lemma le_W (k : ℕ) : ((2:ℝ) * k + 1) / (2 * k + 2) * (π / 2) ≤ W k :=
begin
  rw [←le_div_iff pi_div_two_pos, div_eq_inv_mul (W k) _],
  rw [W_eq_integral_sin_pow_div_integral_sin_pow, le_div_iff (integral_sin_pow_pos _)],
  convert integral_sin_pow_succ_le (2 * k + 1),
  rw integral_sin_pow (2 * k),
  simp only [sin_zero, zero_pow', ne.def, nat.succ_ne_zero, not_false_iff, zero_mul, sin_pi,
    tsub_zero, nat.cast_mul, nat.cast_bit0, algebra_map.coe_one, zero_div, zero_add],
end

lemma tendsto_W_nhds_pi_div_two : tendsto W at_top (𝓝 $ π / 2) :=
begin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le _ tendsto_const_nhds le_W W_le,
  have : 𝓝 (π / 2) = 𝓝 ((1 - 0) * (π / 2)), by rw [sub_zero, one_mul], rw this,
  refine tendsto.mul _ tendsto_const_nhds,
  have h : ∀ (n:ℕ), ((2:ℝ) * n + 1) / (2 * n + 2) = 1 - 1 / (2 * n + 2),
  { intro n,
    rw [sub_div' _ _ _ (ne_of_gt (add_pos_of_nonneg_of_pos
      (mul_nonneg ((two_pos : 0 < (2:ℝ)).le) (nat.cast_nonneg _)) two_pos)), one_mul],
    congr' 1, ring },
  simp_rw h,
  refine (tendsto_const_nhds.div_at_top _).const_sub _,
  refine tendsto.at_top_add _ tendsto_const_nhds,
  exact tendsto_coe_nat_at_top_at_top.const_mul_at_top two_pos
end

end wallis

end real

/-- Wallis' product formula for `π / 2`. -/
theorem real.tendsto_prod_pi_div_two :
  tendsto
  (λ k, ∏ i in range k, (((2:ℝ) * i + 2) / (2 * i + 1)) * ((2 * i + 2) / (2 * i + 3)))
  at_top (𝓝 (π/2)) :=
real.wallis.tendsto_W_nhds_pi_div_two
