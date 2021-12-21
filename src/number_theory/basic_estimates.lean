/-
Copyright (c) 2021 Thomas Bloom, Alex Kontorovich, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Bloom, Alex Kontorovich, Bhavik Mehta
-/

import analysis.special_functions.integrals
import analysis.special_functions.pow
import number_theory.arithmetic_function

noncomputable theory

open_locale big_operators
open real set

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ 1 ≤ n ≤ x, a(n).
-/
-- BM: Formally I wrote this as the sum over the naturals in the closed interval `[1, ⌊x⌋]`.
-- The version in the notes uses sums from 1, mathlib typically uses sums from zero - hopefully
-- this difference shouldn't cause serious issues
def summatory {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) : M :=
∑ n in finset.Icc 1 ⌊x⌋₊, a n

lemma summatory_nat {M : Type*} [add_comm_monoid M] (a : ℕ → M) (n : ℕ) :
  summatory a n = ∑ i in finset.Icc 1 n, a i :=
by simp only [summatory, nat.floor_coe]

lemma summatory_eq_floor {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) :
  summatory a x = summatory a ⌊x⌋₊ :=
by rw [summatory, summatory, nat.floor_coe]

lemma summatory_eq_of_lt_one {M : Type*} [add_comm_monoid M] (a : ℕ → M) {x : ℝ} (hx : x < 1) :
  summatory a x = 0 :=
begin
  rw [summatory, finset.Icc_eq_empty_of_lt, finset.sum_empty],
  rwa [nat.floor_lt' one_ne_zero, nat.cast_one],
end

@[simp] lemma summatory_zero {M : Type*} [add_comm_monoid M] (a : ℕ → M) : summatory a 0 = 0 :=
summatory_eq_of_lt_one _ zero_lt_one

lemma summatory_succ_sub {M : Type*} [add_comm_group M] (a : ℕ → M) (n : ℕ) :
  a (n + 1) = summatory a (n + 1) - summatory a n :=
begin
  rw [←nat.cast_add_one, summatory_nat, summatory_nat, ←nat.Ico_succ_right,
    finset.sum_Ico_succ_top, nat.Ico_succ_right, add_sub_cancel'],
  simp,
end

lemma summatory_eq_sub {M : Type*} [add_comm_group M] (a : ℕ → M) :
  ∀ n, n ≠ 0 → a n = summatory a n - summatory a (n - 1)
| 0 h := (h rfl).elim
| (n+1) _ := by simpa using summatory_succ_sub a n

-- lemma integral_add_adjacent_intervals (hab : interval_integrable f μ a b)
--   (hbc : interval_integrable f μ b c) :
--   ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ :=
-- by rw [← add_neg_eq_zero, ← integral_symm, integral_add_adjacent_intervals_cancel hab hbc]

-- lemma sum_integral_adjacent_intervals {a : ℕ → α} {n : ℕ}

/-- A version of partial summation where the upper bound is a natural number, useful to prove the
general case. -/
theorem partial_summation_nat (a : ℕ → ℂ) (f f' : ℝ → ℂ) {N : ℕ}
  (hf : ∀ x, has_deriv_at f (f' x) x)
  (hf' : ∀ x, continuous_at f' x) :
  ∑ n in finset.Icc 1 N, a n * f n =
    summatory a N * f N - ∫ t in 1..N, summatory a t * f' t :=
begin
  rw ←nat.Ico_succ_right,
  induction N,
  { sorry },
  rw [finset.sum_Ico_succ_top nat.succ_pos', N_ih, add_comm, nat.succ_eq_add_one,
    summatory_succ_sub a, sub_mul, sub_add_eq_add_sub, eq_sub_iff_add_eq],
    rw add_sub_assoc,
    rw add_assoc,
    rw nat.cast_add_one,
    rw add_right_eq_self,
    rw sub_add_eq_add_sub,
    rw sub_eq_zero,
    rw add_comm,
    rw ←add_sub_assoc,
    rw ←sub_add_eq_add_sub,
    rw ←eq_sub_iff_add_eq,
    rw interval_integral.integral_interval_sub_left,
    rw interval_integral.integral_of_le,
    rw [measure_theory.measure.restrict_congr_set measure_theory.Ioo_ae_eq_Ioc.symm],


  -- induction N,
  -- { simp only [zero_sub, summatory_zero, finset.sum_empty, nat.cast_zero, zero_mul, nat.lt_one_iff,
  --     zero_eq_neg, finset.Icc_eq_empty_of_lt],
  --   simp only [interval_integral.integral_of_ge, zero_le_one, neg_eq_zero],
  --   rw [measure_theory.measure.restrict_congr_set measure_theory.Ioo_ae_eq_Ioc.symm,
  --     measure_theory.set_integral_congr, measure_theory.integral_zero],
  --   { exact measurable_set_Ioo },
  --   rintro x ⟨-, hx⟩,
  --   dsimp,
  --   rw [mul_eq_zero_of_left],
  --   rw [summatory_eq_of_lt_one _ hx],
  --   apply_instance },
  -- rw ←nat.Ico_succ_right,
  -- rw finset.sum_Ico_succ_top,
  -- rw nat.Ico_succ_right,
  -- rw N_ih,


end

-- BM: I think this can be made stronger by taking a weaker assumption on `f`, maybe something like
-- the derivative is integrable on intervals contained in [1,x]?
-- (and then probably have a corollary where it's enough for the derivative to be integrable on
-- [1, +inf) for convenience's sake)
-- I also think this might be necessary to make this change in order to apply this lemma to things
-- like `f(x) = 1/x`, since that's not cont diff at 0.
theorem partial_summation (a : ℕ → ℂ) (f : ℝ → ℂ) {x : ℝ} (hf : continuous (deriv f)) :
  ∑ n in finset.Icc 1 ⌊x⌋₊, a n * f n =
    summatory a x * f x - ∫ t in 1..x, summatory a t * deriv f t :=
sorry

-- BM: A definition of the Euler-Mascheroni constant
-- Maybe a different form is a better definition, and in any case it would be nice to show the
-- different definitions are equivalent.
-- This version uses an integral over an infinite interval, which in mathlib is *not* defined
-- as the limit of integrals over finite intervals, but there is a result saying they are equal:
-- see measure_theory.integral.integral_eq_improper: `interval_integral_tendsto_integral_Ioi`
def euler_mascheroni : ℝ := 1 - ∫ t in Ioi 1, int.fract t / t^2

-- vinogradov notation to state things more nicely
-- probably this should be generalised to not be just for ℝ, but I think this works for now
def vinogradov (f : ℝ → ℝ) (g : ℝ → ℝ) : Prop := asymptotics.is_O f g filter.at_top

infix ` ≪ `:50 := vinogradov
-- BM: might want to localise this notation
-- in the measure_theory locale it's used for absolute continuity of measures

lemma harmonic_series_vinogradov :
  (λ x, summatory (λ i, 1 / i) x - log x - euler_mascheroni) ≪ (λ x, 1 / x) :=
sorry

lemma summatory_log :
  (λ x, summatory (λ i, log i) x - x * log x) ≪ log :=
sorry

namespace nat.arithmetic_function
open_locale arithmetic_function

lemma pow_zero_eq_zeta :
  pow 0 = ζ :=
begin
  ext i,
  simp,
end

lemma sigma_zero_eq_zeta_mul_zeta :
  σ 0 = ζ * ζ :=
by rw [←zeta_mul_pow_eq_sigma, pow_zero_eq_zeta]

lemma sigma_zero_apply_eq_sum_divisors {i : ℕ} :
  σ 0 i = ∑ d in i.divisors, 1 :=
begin
  rw [sigma_apply, finset.sum_congr rfl],
  intros x hx,
  apply pow_zero,
end

lemma sigma_zero_apply_eq_card_divisors {i : ℕ} :
  σ 0 i = i.divisors.card :=
 by rw [sigma_zero_apply_eq_sum_divisors, finset.card_eq_sum_ones]

-- BM: Bounds like these make me tempted to define a relation
-- `equal_up_to p f g` to express that `f - g ≪ p` (probably stated `f - g = O(p)`) and show that
-- (for fixed p) this is an equivalence relation, and that it is increasing in `p`
-- Perhaps this would make it easier to express the sorts of calculations that are common in ANT,
-- especially ones like
-- f₁ = f₂ + O(p)
--    = f₃ + O(p)
--    = f₄ + O(p)
-- since this is essentially using transitivity of `equal_up_to p` three times
lemma hyperbola :
  (λ x, summatory (λ i, σ 0 i) x - x * log x - (2 * euler_mascheroni - 1) * x) ≪ sqrt :=
sorry

-- BM: This might need a lower bound on `n`, maybe just `1 ≤ n` is good enough?
lemma divisor_bound :
  ∃ (g : ℝ → ℝ), g ≪ (λ i, 1 / log (log i)) ∧
    ∀ (n : ℕ), (σ 0 n : ℝ) ≤ n ^ g n :=
sorry

-- BM: Might also need a lower bound on `n`?
lemma weak_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  ∃ C, 0 < C ∧ ∀ n, (σ 0 n : ℝ) ≤ C * (n : ℝ)^ε :=
sorry

lemma big_O_divisor_bound (ε : ℝ) (hε : 0 < ε) :
  asymptotics.is_O (λ n, (σ 0 n : ℝ)) (λ n, (n : ℝ)^ε) filter.at_top :=
sorry

-- BM: I have this defined in another branch, coming to mathlib soon
def von_mangoldt : nat.arithmetic_function ℝ := sorry
localized "notation `Λ` := von_mangoldt" in arithmetic_function

-- BM: this is equivalent to `is_O (λ x, x) (summatory Λ) at_top` (ie the same thing in Landau
-- notation) but the proof gives an explicit bound? So we can show something like
-- `is_O_with c (λ x, x) (summatory Λ) at_top`, with a nice constant `c` (I think the proof I have
-- gives something like c = log 2?)
-- Similarly there's a "for sufficiently large x" hidden in here, we could try to remove that too?
-- Then the statement would be something like
-- lemma explicit_chebyshev_lower (x : ℕ) (hx : x₀ ≤ x) :
--    x ≤ log 2 * summatory Λ x :=
-- which could be helpful
lemma chebyshev_lower :
  (λ x, x) ≪ summatory Λ :=
sorry

-- BM: As above, with c = 2 log 2?
lemma chebyshev_upper :
  summatory Λ ≪ (λ x, x) :=
sorry

/--
Given a function `a : ℕ → M` from the naturals into an additive commutative monoid, this expresses
∑ 1 ≤ p ≤ x, a(p) where `p` is prime.
-/
def prime_summatory {M : Type*} [add_comm_monoid M] (a : ℕ → M) (x : ℝ) : M :=
  ∑ n in (finset.Icc 1 ⌊x⌋₊).filter nat.prime, a n
-- BM: equivalently could say it's `summatory (λ n, if (a n).prime then a n else 0) x`

lemma log_reciprocal :
  (λ x, prime_summatory (λ p, log p / p) x - log x) ≪ (λ _, 1) :=
sorry

lemma prime_counting_asymptotic :
  (λ x, prime_summatory (λ _, 1) x - summatory Λ x / log x) ≪ (λ x, x / (log x)^2) :=
sorry

lemma prime_reciprocal : ∃ b,
  (λ x, prime_summatory (λ p, 1 / p) x - log (log x) - b) ≪ (λ x, 1 / log x) :=
sorry

-- BM: I expect there's a nicer way of stating this but this should be good enough for now
lemma mertens_third :
  ∃ c, (λ x, ∏ p in (finset.Icc 1 ⌊x⌋₊), (1 - 1/p)⁻¹ - c * log x) ≪ (λ _, 1) :=
sorry

end nat.arithmetic_function
