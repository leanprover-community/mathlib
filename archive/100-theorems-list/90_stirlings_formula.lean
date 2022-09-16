/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn
-/
import analysis.p_series
import analysis.special_functions.log.basic
import analysis.special_functions.pow
import algebra.big_operators.basic
import algebra.big_operators.intervals
import data.finset.sum
import data.fintype.basic
import data.real.basic
import data.real.pi.wallis
import order.filter
import order.filter.basic
import order.bounded_order
import topology.instances.real
import topology.instances.ennreal

/-!
# Stirling's formula

This file proves Theorem 90 from the [100 Theorem List] <https://www.cs.ru.nl/~freek/100/>.
It states that $n!$ grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.


## Proof outline

The proof follows: <https://proofwiki.org/wiki/Stirling%27s_Formula>.

### Part 1
We consider the fraction sequence $a_n$ of fractions $n!$ over $\sqrt{2n}(\frac{n}{e})^n$ and
proves that this sequence converges against a real, positve number $a$. For this the two main
ingredients are
 - taking the logarithm of the sequence and
 - use the series expansion of $\log(1 + x)$.
-/


open_locale big_operators -- notation ∑ for finite sums
open_locale classical real topological_space nnreal ennreal filter big_operators
open  finset filter nat real

namespace stirling

/-- The sum of inverse squares converges. -/
lemma summable_inverse_squares :
summable (λ (k : ℕ), (1 : ℝ) / ((k.succ))^(2)) :=
begin
  have g := (summable_nat_add_iff 1).mpr (real.summable_one_div_nat_rpow.mpr one_lt_two),
  norm_cast at *,
  exact g,
end

/-!
 ### Part 1
 https://proofwiki.org/wiki/Stirling%27s_Formula#Part_1
-/

/--
Define `stirling_seq n` as $\frac{n!}{\sqrt{2n}/(\frac{n}{e})^n$.
Stirling's formula states that this sequence has limit $\sqrt(π)$.
-/
noncomputable def stirling_seq (n : ℕ) : ℝ :=
(n.factorial : ℝ) / ((sqrt(2 * n) * ((n / (exp 1))) ^ n))

/-- The function `log(1 + x) - log(1 - x)` has a power series expansion with k-th term
`2 * x^(2 * k + 1) / (2 * k + 1)`, valid for `|x| < 1`. -/
lemma log_sum_plus_minus (x : ℝ) (hx : |x| < 1) : has_sum (λ k : ℕ,
  (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (x ^ (2 * k + 1))) (log (1 + x) - log(1 - x)) :=
begin
 have h₁, from has_sum_pow_div_log_of_abs_lt_1 hx,
  have h₂, from has_sum_pow_div_log_of_abs_lt_1 (eq.trans_lt (abs_neg x) hx),
  replace h₂ := (has_sum_mul_left_iff  (λ h : ( -1 = (0:ℝ)), one_ne_zero $ neg_eq_zero.mp h)).mp h₂,
  rw [neg_one_mul, neg_neg, sub_neg_eq_add 1 x] at h₂,
  have h₃, from has_sum.add h₂ h₁,
  rw [tactic.ring.add_neg_eq_sub] at h₃,
  let term := (λ n :ℕ, ((-1) * ((-x) ^ (n + 1) / ((n : ℝ) + 1)) + (x ^ (n + 1) / ((n : ℝ) + 1)))),
  let two_mul := (λ (n : ℕ), (2 * n)),
  rw ←function.injective.has_sum_iff (mul_right_injective two_pos) _ at h₃,
  { suffices h_term_eq_goal :
    (term ∘ two_mul) = (λ k : ℕ, 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k  + 1)),
    by {rw h_term_eq_goal at h₃, exact h₃},
    apply funext,
    intro n,
    rw [function.comp_app],
    dsimp only [two_mul, term],
    rw odd.neg_pow (⟨n, rfl⟩ : odd (2 * n + 1)) x,
    rw [neg_one_mul, neg_div, neg_neg, cast_mul, cast_two],
    ring },
  { intros m hm,
    rw [range_two_mul, set.mem_set_of_eq] at hm,
    rw [even.neg_pow (even_succ.mpr hm), succ_eq_add_one, neg_one_mul, neg_add_self] },
end

/--
For any positive real number `a`, we have the identity
`log((a + 1) / a) = log(1 + 1 / (2*a + 1)) - log(1 - 1/(2*a + 1))`.
-/
lemma log_succ_div_eq_log_sub (a : ℝ) (h : 0 < a) :
  log ((a + 1) / a) = log (1 + 1 / (2 * a + 1)) - log (1 - 1 / (2 * a + 1)) :=
begin
  have h₀: (2 : ℝ) * a + 1 ≠ 0, by { linarith, },
  have h₁: a ≠ 0 := ne_of_gt h,
  rw ← log_div,
  suffices g, from congr_arg log g,
  all_goals { field_simp, },
  all_goals { linarith, },
end

/--
For any positive real number `a`, the expression `log((a + 1) / a)` has the series expansion
$\sum_{k=0}^{\infty}\frac{2}{2k+1}(\frac{1}{2a+1})^{2k+1}$.
-/
lemma power_series_log_succ_div (a : ℝ) (h : 0 < a) : has_sum (λ (k : ℕ),
  (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * ((1 / (2 * (a : ℝ) + 1)) ^ (2 * k + 1)))
  (log ((a + 1) / a)) :=
 begin
  have h₁ : |1 / (2 * a + 1)| < 1, by --in library??
  { rw [abs_of_pos, div_lt_one],
    any_goals {linarith}, /- can not use brackets for single goal, bc of any_goals -/
    {refine div_pos one_pos _, linarith, }, },
  rw log_succ_div_eq_log_sub a (h),
  exact log_sum_plus_minus (1 / (2 * a + 1)) h₁,
 end

/--
`log_stirling_seq n` is log of `stirling_seq n`.
-/
noncomputable def log_stirling_seq (n : ℕ) : ℝ := log (stirling_seq n)

/--
We have the expression
`log_stirling_seq (n + 1) = log(n + 1)! - 1 / 2 * log(2 * n) - n * log ((n + 1) / e)`.
-/
lemma log_stirling_seq_formula (n : ℕ): log_stirling_seq n.succ = (log (n.succ.factorial : ℝ)) -
  1 / (2 : ℝ) * (log (2 * (n.succ : ℝ))) - (n.succ : ℝ) * log ((n.succ : ℝ) / (exp 1)) :=
begin
  have h3, from sqrt_ne_zero'.mpr (mul_pos two_pos $ cast_pos.mpr (succ_pos n)),
  have h4 : 0 ≠ ((n.succ : ℝ) / exp 1) ^ n.succ, from
    ne_of_lt (pow_pos (div_pos (cast_pos.mpr n.succ_pos ) (exp_pos 1)) n.succ),
  rw [log_stirling_seq, stirling_seq, log_div, log_mul, sqrt_eq_rpow, log_rpow, log_pow],
  { linarith },
  { exact (zero_lt_mul_left zero_lt_two).mpr (cast_lt.mpr n.succ_pos),},
  { exact h3, },
  { exact h4.symm, },
  { exact cast_ne_zero.mpr n.succ.factorial_ne_zero, },
  { apply (mul_ne_zero h3 h4.symm), },
end

/--
The sequence `log_stirling_seq (m + 1) - log_stirling_seq (m + 2)` has the series expansion
   `∑ 1 / (2 * (k + 1) + 1) * (1 / 2 * (m + 1) + 1)^(2 * (k + 1))`
-/
lemma log_stirling_seq_diff_has_sum (m : ℕ) :
  has_sum (λ (k : ℕ), (1 : ℝ) / (2 * k.succ + 1) * ((1 / (2 * m.succ + 1)) ^ 2) ^ (k.succ))
  ((log_stirling_seq m.succ) - (log_stirling_seq m.succ.succ)) :=
begin
  change
    has_sum ((λ (b : ℕ), 1 / (2 * (b : ℝ) + 1) * ((1 / (2 * (m.succ : ℝ) + 1)) ^ 2) ^ b) ∘ succ) _,
  rw has_sum_nat_add_iff 1,
  convert (power_series_log_succ_div m.succ (cast_pos.mpr (succ_pos m))).mul_left
    ((m.succ : ℝ) + 1 / (2 : ℝ)),
  { ext k,
    rw [← pow_mul, pow_add],
    have : 2 * (k : ℝ) + 1     ≠ 0, by {norm_cast, exact succ_ne_zero (2*k)},
    have : 2 * (m.succ :ℝ) + 1 ≠ 0, by {norm_cast, exact succ_ne_zero (2*m.succ)},
    field_simp,
    ring },
  { have h_reorder : ∀ {a b c d e f : ℝ}, a - 1 / (2 : ℝ) * b - c - (d - 1 / (2 : ℝ) * e - f) =
      (a - d) - 1 / (2 : ℝ) * (b - e) - (c - f),
    by {intros, ring_nf},
    rw [log_stirling_seq_formula, log_stirling_seq_formula, h_reorder],
    repeat {rw [log_div, factorial_succ]},
    push_cast,
    repeat {rw log_mul},
    rw log_exp,
    ring_nf,
    all_goals {norm_cast},
    all_goals {try {refine mul_ne_zero _ _}, try {exact succ_ne_zero _}},
    any_goals {exact factorial_ne_zero m},
    any_goals {exact exp_ne_zero 1},
    simp },
  { apply_instance }
end

/-- The sequence `log_stirling_seq ∘ succ` is monotone decreasing -/
lemma log_stirling_seq'_antitone : antitone (log_stirling_seq ∘ succ) :=
begin
  apply antitone_nat_of_succ_le,
  intro n,
  refine sub_nonneg.mp _,
  rw ← succ_eq_add_one,
  refine has_sum.nonneg _ (log_stirling_seq_diff_has_sum n),
  norm_num,
  simp only [one_div],
  intro m,
  refine mul_nonneg _ _,
  all_goals {refine inv_nonneg.mpr _, norm_cast, exact (zero_le _)},
end

/--
We have the bound  `log_stirling_seq n - log_stirling_seq (n+1) ≤ 1/(2n+1)^2* 1/(1-(1/2n+1)^2)`.
-/
lemma log_stirling_seq_diff_le_geo_sum : ∀ (n : ℕ),
  log_stirling_seq n.succ - log_stirling_seq n.succ.succ ≤
  (1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2) :=
begin
  intro n,
  have h_nonneg : 0 ≤ ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2),
  by { rw [cast_succ, one_div, inv_pow, inv_nonneg], norm_cast, exact zero_le', },
  have g : has_sum (λ (k : ℕ), ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ)
    ((1 / (2 * n.succ + 1)) ^ 2 / (1 - (1 / (2 * n.succ + 1)) ^ 2)) :=
  begin
    have h_pow_succ := λ (k : ℕ),
      symm (pow_succ ((1 / (2 * ((n : ℝ) + 1) + 1)) ^ 2) k),
    have hlt : ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) < 1, by
    { simp only [cast_succ, one_div, inv_pow],
      refine inv_lt_one _,
      norm_cast,
      simp only [nat.one_lt_pow_iff, ne.def, zero_eq_bit0, nat.one_ne_zero, not_false_iff,
        lt_add_iff_pos_left, canonically_ordered_comm_semiring.mul_pos, succ_pos', and_self], },
    exact (has_sum_geometric_of_lt_1 h_nonneg hlt).mul_left ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2)
  end,
  have hab :
    ∀ (k : ℕ), (1 / (2 * (k.succ : ℝ) + 1)) * ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ ≤
    ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ :=
  begin
    intro k,
    have h_zero_le : 0 ≤ ((1 / (2 * (n.succ : ℝ) + 1)) ^ 2) ^ k.succ := pow_nonneg h_nonneg _,
    have h_left : 1 / (2 * (k.succ : ℝ) + 1) ≤ 1, by
    { simp only [cast_succ, one_div],
      refine inv_le_one _,
      norm_cast,
      exact (le_add_iff_nonneg_left 1).mpr zero_le', },
    exact mul_le_of_le_one_left h_zero_le h_left,
  end,
  exact has_sum_le hab (log_stirling_seq_diff_has_sum n) g,
end

/--
We have the bound  `log_stirling_seq n - log_stirling_seq (n+1)` ≤ 1/(4 n^2)
-/
lemma log_stirling_seq_sub_log_stirling_seq_succ (n : ℕ) :
  log_stirling_seq n.succ - log_stirling_seq n.succ.succ ≤ 1 / (4 * n.succ ^ 2) :=
begin
  have h₁ : 0 < 4 * ((n:ℝ) + 1)^2 := by nlinarith [@cast_nonneg ℝ _ n],
  have h₃ : 0 < (2 * ((n:ℝ) + 1) + 1) ^ 2 := by nlinarith [@cast_nonneg ℝ _ n ],
  have h₂ : 0 < 1 - (1 / (2 * ((n:ℝ) + 1) + 1)) ^ 2,
  { rw ← mul_lt_mul_right h₃,
    have H : 0 < (2 * ((n:ℝ) + 1) + 1) ^ 2 - 1 := by nlinarith [@cast_nonneg ℝ _ n ],
    convert H using 1; field_simp [h₃.ne'] },
  refine le_trans (log_stirling_seq_diff_le_geo_sum n) _,
  push_cast at *,
  rw div_le_div_iff h₂ h₁,
  field_simp [h₃.ne'],
  rw div_le_div_right h₃,
  ring_nf,
  norm_cast,
  linarith,
end

/-- For any `n`, we have `log_stirling_seq 1 - log_stirling_seq n ≤ 1/4 * ∑' 1/k^2`  -/
lemma log_stirling_seq_bounded_aux : ∃ (c : ℝ), ∀ (n : ℕ),
log_stirling_seq 1 - log_stirling_seq n.succ ≤ c :=
begin
  let d := ∑' k : ℕ, (1 : ℝ) / (k.succ)^2,
  use (1/4 * d : ℝ),
  let log_stirling_seq' : (ℕ → ℝ) := λ (k : ℕ), log_stirling_seq k.succ,
  intro n,
  calc
  log_stirling_seq 1 - log_stirling_seq n.succ = log_stirling_seq' 0 - log_stirling_seq' n : rfl
    ... = ∑ k in range n, (log_stirling_seq' k - log_stirling_seq' (k + 1)) :
    by rw ← (sum_range_sub' log_stirling_seq' n)
    ... ≤ ∑ k in range n, (1/4) * (1 / (k.succ)^2) :
    begin
      apply sum_le_sum,
      intros k hk,
      convert log_stirling_seq_sub_log_stirling_seq_succ k using 1,
      field_simp,
    end
    ... = 1 / 4 * ∑ k in range n, 1 / k.succ ^ 2 : by rw mul_sum
    ... ≤ 1 / 4 * d :
    begin
      refine (mul_le_mul_left _).mpr _, { exact one_div_pos.mpr four_pos, },
      refine sum_le_tsum (range n) (λ k _, _) summable_inverse_squares,
      apply le_of_lt,
      rw one_div_pos,
      rw sq_pos_iff,
      exact nonzero_of_invertible ↑(succ k)
    end
end

/-- The sequence `log_stirling_seq` is bounded below for `n ≥ 1`. -/
lemma log_stirling_seq_bounded_by_constant : ∃ c, ∀ (n : ℕ), c ≤ log_stirling_seq n.succ :=
begin
  obtain ⟨d, h⟩ := log_stirling_seq_bounded_aux,
  use log_stirling_seq 1 - d,
  intro n,
  exact sub_le.mp (h n),
end

/-- The sequence `stirling_seq` is positive for `n > 0`  -/
lemma stirling_seq'_pos (n : ℕ): 0 < stirling_seq n.succ :=
begin
  apply_rules [cast_pos.mpr, factorial_pos, exp_pos, pow_pos, div_pos, mul_pos, real.sqrt_pos.mpr,
    two_pos, succ_pos];
  apply_instance
end

/--
The sequence `stirling_seq` has a positive lower bound (in fact, `exp (3/4 - 1/2 * log 2)`)
-/
lemma stirling_seq'_bounded_by_pos_constant :
  ∃ a, 0 < a ∧ ∀ n : ℕ, a ≤ stirling_seq n.succ :=
begin
  cases log_stirling_seq_bounded_by_constant with c h,
  refine ⟨ exp c, exp_pos _, λ n, _⟩,
  rw ← le_log_iff_exp_le (stirling_seq'_pos n),
  exact h n,
end

/-- The sequence `stirling_seq ∘ succ` is monotone decreasing -/
lemma stirling_seq'_antitone : antitone (stirling_seq ∘ succ) :=
λ n m h, (log_le_log (stirling_seq'_pos m) (stirling_seq'_pos n)).mp (log_stirling_seq'_antitone h)

/-- The limit `a` of the sequence `stirling_seq` satisfies `0 < a` -/
lemma stirling_seq_has_pos_limit_a :
  ∃ (a : ℝ), 0 < a ∧ tendsto (λ (n : ℕ), stirling_seq n) at_top (𝓝 a) :=
begin
  obtain ⟨x, x_pos, hx⟩ := stirling_seq'_bounded_by_pos_constant,
  have hx' : x ∈ lower_bounds (set.range (stirling_seq ∘ succ)) := by simpa [lower_bounds] using hx,
  refine ⟨_, lt_of_lt_of_le x_pos (le_cInf (set.range_nonempty _) hx'), _⟩,
  rw ←filter.tendsto_add_at_top_iff_nat 1,
  exact tendsto_at_top_cinfi stirling_seq'_antitone ⟨x, hx'⟩,
end

end stirling
