/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.analytic.basic
import analysis.specific_limits
import data.complex.is_R_or_C

open filter is_R_or_C continuous_multilinear_map normed_field
open_locale nat topological_space

section move_me

lemma coe_factorial_add_eq_zero {α : Type*} [ring α] {n : ℕ} (h : (n! : α) = 0) :
  ∀ i, ((n+i)! : α) = 0
| 0 := by simpa using h
| (i+1) := by rw [← add_assoc, nat.factorial_succ, nat.cast_mul,
                  coe_factorial_add_eq_zero i, mul_zero]

end move_me

section norm_nat_tendsto

end norm_nat_tendsto

section exp

-- Old approach : any field...

--variables {𝕂 𝔸 : Type*} [normed_field 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]
--
--lemma summable_pow_div_fact (x : 𝔸) : summable (λ n : ℕ, (1/n! : 𝕂) • x^n) :=
--begin
--  by_cases h : ∃ n : ℕ, (1/n! : 𝕂) • x^n = 0,
--  { rcases h with ⟨n, hn⟩,
--    refine summable_of_norm_bounded_eventually 0 summable_zero _,
--    rw [nat.cofinite_eq_at_top, eventually_at_top],
--    refine ⟨n, λ i hi, _⟩,
--    rw [pi.zero_apply, norm_le_zero_iff],
--    rcases nat.exists_eq_add_of_le hi with ⟨j, rfl⟩,
--    rcases smul_eq_zero.mp hn with h | h,
--    { simp [coe_factorial_add_eq_zero (eq_zero_of_one_div_eq_zero h)] },
--    { simp [pow_add, h] } },
--  { push_neg at h,
--    refine summable_of_ratio_test_tendsto_lt_one zero_lt_one
--      (eventually_of_forall $ h) _,
--    suffices : ∀ n : ℕ, ∥x∥ / ∥((n+1) : 𝕂)∥ =
--      ∥(1 / ((n+1)! : 𝕂)) • x^(n+1)∥ / ∥(1/(n! : 𝕂)) • x^n∥,
--    { refine tendsto.congr this _, },
--     }
--end

--lemma real.summable_inv_factorial : summable (λ n : ℕ, 1 / (n! : ℝ)) :=
--begin
--  have : ∀ n, (n! : ℝ) ≠ 0 := λ n, nat.cast_ne_zero.mpr n.factorial_ne_zero,
--  refine summable_of_ratio_test_tendsto_lt_one zero_lt_one (eventually_of_forall $
--    λ n, div_ne_zero one_ne_zero (this n)) _,
--  suffices : ∀ n : ℕ, ∥1 /((n+1)! : ℝ)∥ / ∥1 / (n! : ℝ)∥ = 1 / ((n+1 : ℕ) : ℝ),
--  { conv {congr, funext, rw [this] },
--    exact tendsto_one_div_add_at_top_nhds_0_nat },
--  intro n,
--  calc ∥1 / ((n + 1)! : ℝ)∥ / ∥1 / (n! : ℝ)∥
--      = ((n.succ)⁻¹ * n!⁻¹) * n! :
--        by rw [ nat.factorial_succ, nat.cast_mul, norm_div, norm_div, norm_one, norm_mul,
--                real.norm_coe_nat, real.norm_coe_nat, div_eq_mul_inv, div_eq_mul_inv,
--                div_eq_mul_inv, mul_inv', mul_inv', inv_inv', inv_one, one_mul, one_mul ]
--  ... = (n.succ : ℝ)⁻¹ * ((n!)⁻¹ * (n!)) : by linarith --faster than ac_refl !
--  ... =1 / (((n+1) : ℕ) : ℝ) :
--        by rw [inv_mul_cancel (this n), mul_one, inv_eq_one_div]
--end
--

lemma real.summable_pow_div_factorial (x : ℝ) : summable (λ n : ℕ, x^n / n!) :=
begin
  by_cases h : x = 0,
  { refine summable_of_norm_bounded_eventually 0 summable_zero _,
    filter_upwards [eventually_cofinite_ne 0],
    intros n hn,
    rw [h, zero_pow' n hn, zero_div, norm_zero],
    exact le_refl _ },
  { refine summable_of_ratio_test_tendsto_lt_one zero_lt_one (eventually_of_forall $
      λ n, div_ne_zero (pow_ne_zero n h) (nat.cast_ne_zero.mpr n.factorial_ne_zero)) _,
    suffices : ∀ n : ℕ, ∥x^(n+1) / (n+1)!∥ / ∥x^n / n!∥ = ∥x∥ / ∥((n+1 : ℕ) : ℝ)∥,
    { conv {congr, funext, rw [this, real.norm_coe_nat] },
      exact (tendsto_const_div_at_top_nhds_0_nat _).comp (tendsto_add_at_top_nat 1) },
    intro n,
    calc ∥x^(n+1) / (n+1)!∥ / ∥x^n / n!∥
        = (∥x∥^n * ∥x∥) * (∥(n! : ℝ)∥⁻¹ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * ((∥x∥^n)⁻¹ * ∥(n! : ℝ)∥) :
          by rw [ normed_field.norm_div, normed_field.norm_div,
                  normed_field.norm_pow, normed_field.norm_pow, pow_add, pow_one,
                  div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv', inv_inv',
                  nat.factorial_succ, nat.cast_mul, normed_field.norm_mul, mul_inv_rev' ]
    ... = (∥x∥ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * (∥x∥^n * (∥x∥^n)⁻¹) * (∥(n! : ℝ)∥ * ∥(n! : ℝ)∥⁻¹) :
          by linarith --faster than ac_refl !
    ... = (∥x∥ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * 1 * 1 :
          by  rw [mul_inv_cancel (pow_ne_zero _ $ λ h', h $ norm_eq_zero.mp h'), mul_inv_cancel
                    (λ h', n.factorial_ne_zero $ nat.cast_eq_zero.mp $ norm_eq_zero.mp h')];
              apply_instance
    ... = ∥x∥ / ∥((n+1 : ℕ) : ℝ)∥ : by rw [mul_one, mul_one, ← div_eq_mul_inv] }
end

variables (𝕂 𝔸 : Type*) [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

def exp_series : formal_multilinear_series 𝕂 𝔸 𝔸 :=
  λ n, (1/n! : 𝕂) • continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸

variables {𝔸}

noncomputable def exp (x : 𝔸) : 𝔸 := (exp_series 𝕂 𝔸).sum x

variables {𝕂}

lemma exp_series_radius_eq_top : (exp_series 𝕂 𝔸).radius = ⊤ :=
begin
  refine (exp_series 𝕂 𝔸).radius_eq_top_of_summable_norm (λ r, _),
  refine summable_of_norm_bounded_eventually _ (r : ℝ).summable_pow_div_factorial _,
  filter_upwards [eventually_cofinite_ne 0],
  intros n hn,
  rw [norm_mul, norm_norm (exp_series 𝕂 𝔸 n), exp_series, norm_smul, norm_div, norm_one, norm_pow,
      nnreal.norm_eq, norm_eq_abs, abs_cast_nat, mul_comm, ←mul_assoc, ←mul_div_assoc, mul_one],
  have : ∥continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸∥ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (nat.pos_of_ne_zero hn),
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n!.cast_nonneg) this
end

lemma exp_series_has_sum_exp (x : 𝔸) : has_sum (λ n, exp_series 𝕂 𝔸 n (λ _, x)) (exp 𝕂 x) :=
begin
  refine formal_multilinear_series.has_sum (exp_series 𝕂 𝔸) _,
end

lemma goal (x : 𝔸) : exp 𝕂 x = ∑' (n : ℕ), (1 / n! : 𝕂) • x^n :=
begin

end

end exp
