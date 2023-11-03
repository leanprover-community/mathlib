/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import probability.ident_distrib
import measure_theory.integral.interval_integral
import analysis.specific_limits.floor_pow
import analysis.p_series
import analysis.asymptotics.specific_asymptotics

/-!
# The strong law of large numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove the strong law of large numbers, in `probability_theory.strong_law_ae`:
If `X n` is a sequence of independent identically distributed integrable real-valued random
variables, then `∑ i in range n, X i / n` converges almost surely to `𝔼[X 0]`.
We give here the strong version, due to Etemadi, that only requires pairwise independence.

This file also contains the Lᵖ version of the strong law of large numbers provided by
`probability_theory.strong_law_Lp` which shows `∑ i in range n, X i / n` converges in Lᵖ to
`𝔼[X 0]` provided `X n` is independent identically distributed and is Lᵖ.

## Implementation

We follow the proof by Etemadi
[Etemadi, *An elementary proof of the strong law of large numbers*][etemadi_strong_law],
which goes as follows.

It suffices to prove the result for nonnegative `X`, as one can prove the general result by
splitting a general `X` into its positive part and negative part.
Consider `Xₙ` a sequence of nonnegative integrable identically distributed pairwise independent
random variables. Let `Yₙ` be the truncation of `Xₙ` up to `n`. We claim that
* Almost surely, `Xₙ = Yₙ` for all but finitely many indices. Indeed, `∑ ℙ (Xₙ ≠ Yₙ)` is bounded by
  `1 + 𝔼[X]` (see `sum_prob_mem_Ioc_le` and `tsum_prob_mem_Ioi_lt_top`).
* Let `c > 1`. Along the sequence `n = c ^ k`, then `(∑_{i=0}^{n-1} Yᵢ - 𝔼[Yᵢ])/n` converges almost
  surely to `0`. This follows from a variance control, as
```
  ∑_k ℙ (|∑_{i=0}^{c^k - 1} Yᵢ - 𝔼[Yᵢ]| > c^k ε)
    ≤ ∑_k (c^k ε)^{-2} ∑_{i=0}^{c^k - 1} Var[Yᵢ]    (by Markov inequality)
    ≤ ∑_i (C/i^2) Var[Yᵢ]                           (as ∑_{c^k > i} 1/(c^k)^2 ≤ C/i^2)
    ≤ ∑_i (C/i^2) 𝔼[Yᵢ^2]
    ≤ 2C 𝔼[X^2]                                     (see `sum_variance_truncation_le`)
```
* As `𝔼[Yᵢ]` converges to `𝔼[X]`, it follows from the two previous items and Cesaro that, along
  the sequence `n = c^k`, one has `(∑_{i=0}^{n-1} Xᵢ) / n → 𝔼[X]` almost surely.
* To generalize it to all indices, we use the fact that `∑_{i=0}^{n-1} Xᵢ` is nondecreasing and
  that, if `c` is close enough to `1`, the gap between `c^k` and `c^(k+1)` is small.
-/

noncomputable theory

open measure_theory filter finset asymptotics
open set (indicator)

open_locale topology big_operators measure_theory probability_theory ennreal nnreal

namespace probability_theory

/-! ### Prerequisites on truncations -/

section truncation

variables {α : Type*}

/-- Truncating a real-valued function to the interval `(-A, A]`. -/
def truncation (f : α → ℝ) (A : ℝ) :=
(indicator (set.Ioc (-A) A) id) ∘ f

variables {m : measurable_space α} {μ : measure α} {f : α → ℝ}

lemma _root_.measure_theory.ae_strongly_measurable.truncation
  (hf : ae_strongly_measurable f μ) {A : ℝ} :
  ae_strongly_measurable (truncation f A) μ :=
begin
  apply ae_strongly_measurable.comp_ae_measurable _ hf.ae_measurable,
  exact (strongly_measurable_id.indicator measurable_set_Ioc).ae_strongly_measurable,
end

lemma abs_truncation_le_bound (f : α → ℝ) (A : ℝ) (x : α) :
  |truncation f A x| ≤ |A| :=
begin
  simp only [truncation, set.indicator, set.mem_Icc, id.def, function.comp_app],
  split_ifs,
  { exact abs_le_abs h.2 (neg_le.2 h.1.le) },
  { simp [abs_nonneg] }
end

@[simp] lemma truncation_zero (f : α → ℝ) :
  truncation f 0 = 0 :=
by simp [truncation]

lemma abs_truncation_le_abs_self (f : α → ℝ) (A : ℝ) (x : α) :
  |truncation f A x| ≤ |f x| :=
begin
  simp only [truncation, indicator, set.mem_Icc, id.def, function.comp_app],
  split_ifs,
  { exact le_rfl },
  { simp [abs_nonneg] },
end

lemma truncation_eq_self {f : α → ℝ} {A : ℝ} {x : α} (h : |f x| < A) :
  truncation f A x = f x :=
begin
  simp only [truncation, indicator, set.mem_Icc, id.def, function.comp_app, ite_eq_left_iff],
  assume H,
  apply H.elim,
  simp [(abs_lt.1 h).1, (abs_lt.1 h).2.le],
end

lemma truncation_eq_of_nonneg {f : α → ℝ} {A : ℝ} (h : ∀ x, 0 ≤ f x) :
  truncation f A = (indicator (set.Ioc 0 A) id) ∘ f :=
begin
  ext x,
  rcases (h x).lt_or_eq with hx|hx,
  { simp only [truncation, indicator, hx, set.mem_Ioc, id.def, function.comp_app, true_and],
    by_cases h'x : f x ≤ A,
    { have : - A < f x, by linarith [h x],
      simp only [this, true_and] },
    { simp only [h'x, and_false] } },
  { simp only [truncation, indicator, hx, id.def, function.comp_app, if_t_t]},
end

lemma truncation_nonneg {f : α → ℝ} (A : ℝ) {x : α} (h : 0 ≤ f x) : 0 ≤ truncation f A x :=
set.indicator_apply_nonneg $ λ _, h

lemma _root_.measure_theory.ae_strongly_measurable.mem_ℒp_truncation [is_finite_measure μ]
  (hf : ae_strongly_measurable f μ) {A : ℝ} {p : ℝ≥0∞} :
  mem_ℒp (truncation f A) p μ :=
mem_ℒp.of_bound hf.truncation (|A|) (eventually_of_forall (λ x, abs_truncation_le_bound _ _ _))

lemma _root_.measure_theory.ae_strongly_measurable.integrable_truncation [is_finite_measure μ]
  (hf : ae_strongly_measurable f μ) {A : ℝ} :
  integrable (truncation f A) μ :=
by { rw ← mem_ℒp_one_iff_integrable, exact hf.mem_ℒp_truncation }

lemma moment_truncation_eq_interval_integral (hf : ae_strongly_measurable f μ) {A : ℝ}
  (hA : 0 ≤ A) {n : ℕ} (hn : n ≠ 0) :
  ∫ x, (truncation f A x) ^ n ∂μ = ∫_{(-A)}^{A} y, y ^ n ∂(measure.map f μ) :=
begin
  have M : measurable_set (set.Ioc (-A) A) := measurable_set_Ioc,
  change ∫ x, (λ z, (indicator (set.Ioc (-A) A) id z) ^ n) (f x) ∂μ = _,
  rw [← integral_map hf.ae_measurable, interval_integral.integral_of_le, ← integral_indicator M],
  { simp only [indicator, zero_pow' _ hn, id.def, ite_pow] },
  { linarith },
  { exact ((measurable_id.indicator M).pow_const n).ae_strongly_measurable }
end

lemma moment_truncation_eq_interval_integral_of_nonneg (hf : ae_strongly_measurable f μ) {A : ℝ}
  {n : ℕ} (hn : n ≠ 0) (h'f : 0 ≤ f) :
  ∫ x, (truncation f A x) ^ n ∂μ = ∫_{0}^{A} y, y ^ n ∂(measure.map f μ) :=
begin
  have M : measurable_set (set.Ioc 0 A) := measurable_set_Ioc,
  have M' : measurable_set (set.Ioc A 0) := measurable_set_Ioc,
  rw truncation_eq_of_nonneg h'f,
  change ∫ x, (λ z, (indicator (set.Ioc 0 A) id z) ^ n) (f x) ∂μ = _,
  rcases le_or_lt 0 A with hA | hA,
  { rw [← integral_map hf.ae_measurable, interval_integral.integral_of_le hA,
        ← integral_indicator M],
    { simp only [indicator, zero_pow' _ hn, id.def, ite_pow] },
    { exact ((measurable_id.indicator M).pow_const n).ae_strongly_measurable } },
  { rw [← integral_map hf.ae_measurable, interval_integral.integral_of_ge hA.le,
        ← integral_indicator M'],
    { simp only [set.Ioc_eq_empty_of_le hA.le, zero_pow' _ hn, set.indicator_empty, integral_zero,
        zero_eq_neg],
      apply integral_eq_zero_of_ae,
      have : ∀ᵐ x ∂(measure.map f μ), (0 : ℝ) ≤ x :=
        (ae_map_iff hf.ae_measurable measurable_set_Ici).2 (eventually_of_forall h'f),
      filter_upwards [this] with x hx,
      simp only [indicator, set.mem_Ioc, pi.zero_apply, ite_eq_right_iff, and_imp],
      assume h'x h''x,
      have : x = 0, by linarith,
      simp [this, zero_pow' _ hn] },
    { exact ((measurable_id.indicator M).pow_const n).ae_strongly_measurable } }
end

lemma integral_truncation_eq_interval_integral (hf : ae_strongly_measurable f μ) {A : ℝ}
  (hA : 0 ≤ A) :
  ∫ x, truncation f A x ∂μ = ∫_{(-A)}^{A} y, y ∂(measure.map f μ) :=
by simpa using moment_truncation_eq_interval_integral hf hA one_ne_zero

lemma integral_truncation_eq_interval_integral_of_nonneg (hf : ae_strongly_measurable f μ) {A : ℝ}
  (h'f : 0 ≤ f) :
  ∫ x, truncation f A x ∂μ = ∫_{0}^{A} y, y ∂(measure.map f μ) :=
by simpa using moment_truncation_eq_interval_integral_of_nonneg hf one_ne_zero h'f

lemma integral_truncation_le_integral_of_nonneg
  (hf : integrable f μ) (h'f : 0 ≤ f) {A : ℝ} :
  ∫ x, truncation f A x ∂μ ≤ ∫ x, f x ∂μ :=
begin
  apply integral_mono_of_nonneg (eventually_of_forall (λ x, _)) hf (eventually_of_forall (λ x, _)),
  { exact truncation_nonneg _ (h'f x) },
  { calc truncation f A x ≤ |truncation f A x| : le_abs_self _
                      ... ≤ |f x|              : abs_truncation_le_abs_self _ _ _
                      ... = f x                : abs_of_nonneg (h'f x) }
end

/-- If a function is integrable, then the integral of its truncated versions converges to the
integral of the whole function. -/
lemma tendsto_integral_truncation {f : α → ℝ} (hf : integrable f μ) :
  tendsto (λ A, ∫ x, truncation f A x ∂μ) at_top (𝓝 (∫ x, f x ∂μ)) :=
begin
  refine tendsto_integral_filter_of_dominated_convergence (λ x, abs (f x)) _ _ _ _,
  { exact eventually_of_forall (λ A, hf.ae_strongly_measurable.truncation) },
  { apply eventually_of_forall (λ A, _),
    apply eventually_of_forall (λ x, _),
    rw real.norm_eq_abs,
    exact abs_truncation_le_abs_self _ _ _ },
  { apply hf.abs },
  { apply eventually_of_forall (λ x, _),
    apply tendsto_const_nhds.congr' _,
    filter_upwards [Ioi_mem_at_top (abs (f x))] with A hA,
    exact (truncation_eq_self hA).symm },
end

lemma ident_distrib.truncation {β : Type*} [measurable_space β] {ν : measure β}
  {f : α → ℝ} {g : β → ℝ} (h : ident_distrib f g μ ν) {A : ℝ} :
  ident_distrib (truncation f A) (truncation g A) μ ν :=
h.comp (measurable_id.indicator measurable_set_Ioc)

end truncation

section strong_law_ae

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

section moment_estimates

lemma sum_prob_mem_Ioc_le
  {X : Ω → ℝ} (hint : integrable X) (hnonneg : 0 ≤ X) {K : ℕ} {N : ℕ} (hKN : K ≤ N) :
  ∑ j in range K, ℙ {ω | X ω ∈ set.Ioc (j : ℝ) N} ≤ ennreal.of_real (𝔼[X] + 1) :=
begin
  let ρ : measure ℝ := measure.map X ℙ,
  haveI : is_probability_measure ρ := is_probability_measure_map hint.ae_measurable,
  have A : ∑ j in range K, ∫_{j}^{N} x, (1 : ℝ) ∂ρ ≤ 𝔼[X] + 1, from calc
  ∑ j in range K, ∫_{j}^{N} x, (1 : ℝ) ∂ρ
      = ∑ j in range K, ∑ i in Ico j N, ∫_{i}^{(i+1 : ℕ)} x, (1 : ℝ) ∂ρ :
    begin
      apply sum_congr rfl (λ j hj, _),
      rw interval_integral.sum_integral_adjacent_intervals_Ico ((mem_range.1 hj).le.trans hKN),
      assume k hk,
      exact continuous_const.interval_integrable _ _,
    end
  ... = ∑ i in range N, ∑ j in range (min (i+1) K), ∫_{i}^{(i+1 : ℕ)} x, (1 : ℝ) ∂ρ :
    begin
      simp_rw [sum_sigma'],
      refine sum_bij' (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ (λ a ha, rfl)
        (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ _ _,
      { rintros ⟨i, j⟩ hij,
        simp only [mem_sigma, mem_range, mem_Ico] at hij,
        simp only [hij, nat.lt_succ_iff.2 hij.2.1, mem_sigma, mem_range, lt_min_iff, and_self] },
      { rintros ⟨i, j⟩ hij,
        simp only [mem_sigma, mem_range, lt_min_iff] at hij,
        simp only [hij, nat.lt_succ_iff.1 hij.2.1, mem_sigma, mem_range, mem_Ico, and_self] },
      { rintros ⟨i, j⟩ hij, refl },
      { rintros ⟨i, j⟩ hij, refl },
    end
  ... ≤ ∑ i in range N, (i + 1) * ∫_{i}^{(i+1 : ℕ)} x, (1 : ℝ) ∂ρ :
    begin
      apply sum_le_sum (λ i hi, _),
      simp only [nat.cast_add, nat.cast_one, sum_const, card_range, nsmul_eq_mul, nat.cast_min],
      refine mul_le_mul_of_nonneg_right (min_le_left _ _) _,
      apply interval_integral.integral_nonneg,
      { simp only [le_add_iff_nonneg_right, zero_le_one] },
      { simp only [zero_le_one, implies_true_iff], }
    end
  ... ≤ ∑ i in range N, ∫_{i}^{(i+1 : ℕ)} x, (x + 1) ∂ρ :
    begin
      apply sum_le_sum (λ i hi, _),
      have I : (i : ℝ) ≤ (i + 1 : ℕ),
        by simp only [nat.cast_add, nat.cast_one, le_add_iff_nonneg_right, zero_le_one],
      simp_rw [interval_integral.integral_of_le I, ← integral_mul_left],
      apply set_integral_mono_on,
      { exact continuous_const.integrable_on_Ioc },
      { exact (continuous_id.add continuous_const).integrable_on_Ioc },
      { exact measurable_set_Ioc },
      { assume x hx,
        simp only [nat.cast_add, nat.cast_one, set.mem_Ioc] at hx,
        simp [hx.1.le] }
    end
  ... = ∫_{0}^{N} x, x + 1 ∂ρ :
    begin
      rw interval_integral.sum_integral_adjacent_intervals (λ k hk, _),
      { norm_cast },
      { exact (continuous_id.add continuous_const).interval_integrable _ _ }
    end
  ... = ∫_{0}^{N} x, x ∂ρ + ∫_{0}^{N} x, 1 ∂ρ :
    begin
      rw interval_integral.integral_add,
      { exact continuous_id.interval_integrable _ _ },
      { exact continuous_const.interval_integrable _ _ },
    end
  ... = 𝔼[truncation X N] + ∫_{0}^{N} x, 1 ∂ρ :
    by rw integral_truncation_eq_interval_integral_of_nonneg hint.1 hnonneg
  ... ≤ 𝔼[X] + ∫_{0}^{N} x, 1 ∂ρ :
    add_le_add_right (integral_truncation_le_integral_of_nonneg hint hnonneg) _
  ... ≤ 𝔼[X] + 1 :
    begin
      refine add_le_add le_rfl _,
      rw interval_integral.integral_of_le (nat.cast_nonneg _),
      simp only [integral_const, measure.restrict_apply', measurable_set_Ioc, set.univ_inter,
        algebra.id.smul_eq_mul, mul_one],
      rw ← ennreal.one_to_real,
      exact ennreal.to_real_mono ennreal.one_ne_top prob_le_one,
    end,
  have B : ∀ a b, ℙ {ω | X ω ∈ set.Ioc a b} = ennreal.of_real (∫ x in set.Ioc a b, (1 : ℝ) ∂ρ),
  { assume a b,
    rw [of_real_set_integral_one ρ _,
        measure.map_apply_of_ae_measurable hint.ae_measurable measurable_set_Ioc],
    refl },
  calc ∑ j in range K, ℙ {ω | X ω ∈ set.Ioc (j : ℝ) N}
      = ∑ j in range K, ennreal.of_real (∫ x in set.Ioc (j : ℝ) N, (1 : ℝ) ∂ρ) :
    by simp_rw B
  ... = ennreal.of_real (∑ j in range K, ∫ x in set.Ioc (j : ℝ) N, (1 : ℝ) ∂ρ) :
    begin
      rw ennreal.of_real_sum_of_nonneg,
      simp only [integral_const, algebra.id.smul_eq_mul, mul_one, ennreal.to_real_nonneg,
        implies_true_iff],
    end
  ... = ennreal.of_real (∑ j in range K, ∫_{j}^{N} x, (1 : ℝ) ∂ρ) :
    begin
      congr' 1,
      refine sum_congr rfl (λ j hj, _),
      rw interval_integral.integral_of_le (nat.cast_le.2 ((mem_range.1 hj).le.trans hKN)),
    end
  ... ≤ ennreal.of_real (𝔼[X] + 1) : ennreal.of_real_le_of_real A
end

lemma tsum_prob_mem_Ioi_lt_top
  {X : Ω → ℝ} (hint : integrable X) (hnonneg : 0 ≤ X) :
  ∑' (j : ℕ), ℙ {ω | X ω ∈ set.Ioi (j : ℝ)} < ∞ :=
begin
  suffices : ∀ (K : ℕ), ∑ j in range K, ℙ {ω | X ω ∈ set.Ioi (j : ℝ)} ≤ ennreal.of_real (𝔼[X] + 1),
    from (le_of_tendsto_of_tendsto (ennreal.tendsto_nat_tsum _) tendsto_const_nhds
      (eventually_of_forall this)).trans_lt ennreal.of_real_lt_top,
  assume K,
  have A : tendsto (λ (N : ℕ), ∑ j in range K, ℙ {ω | X ω ∈ set.Ioc (j : ℝ) N})
    at_top (𝓝 (∑ j in range K, ℙ {ω | X ω ∈ set.Ioi (j : ℝ)})),
  { refine tendsto_finset_sum _ (λ i hi, _),
    have : {ω | X ω ∈ set.Ioi (i : ℝ)} = ⋃ (N : ℕ), {ω | X ω ∈ set.Ioc (i : ℝ) N},
    { apply set.subset.antisymm _ _,
      { assume ω hω,
        obtain ⟨N, hN⟩ : ∃ (N : ℕ), X ω ≤ N := exists_nat_ge (X ω),
        exact set.mem_Union.2 ⟨N, hω, hN⟩ },
      { simp only [set.mem_Ioc, set.mem_Ioi, set.Union_subset_iff, set.set_of_subset_set_of,
          implies_true_iff] {contextual := tt} } },
    rw this,
    apply tendsto_measure_Union,
    assume m n hmn x hx,
    exact ⟨hx.1, hx.2.trans (nat.cast_le.2 hmn)⟩ },
  apply le_of_tendsto_of_tendsto A tendsto_const_nhds,
  filter_upwards [Ici_mem_at_top K] with N hN,
  exact sum_prob_mem_Ioc_le hint hnonneg hN
end

lemma sum_variance_truncation_le
  {X : Ω → ℝ} (hint : integrable X) (hnonneg : 0 ≤ X) (K : ℕ) :
  ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * 𝔼[(truncation X j) ^ 2] ≤ 2 * 𝔼[X] :=
begin
  set Y := λ (n : ℕ), truncation X n,
  let ρ : measure ℝ := measure.map X ℙ,
  have Y2 : ∀ n, 𝔼[Y n ^ 2] = ∫_{0}^{n} x, x ^ 2 ∂ρ,
  { assume n,
    change 𝔼[λ x, (Y n x)^2] = _,
    rw [moment_truncation_eq_interval_integral_of_nonneg hint.1 two_ne_zero hnonneg] },
  calc ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * 𝔼[Y j ^ 2]
      = ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * ∫_{0}^{j} x, x ^ 2 ∂ρ :
    by simp_rw [Y2]
  ... = ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * ∑ k in range j, ∫_{k}^{(k+1 : ℕ)} x, x ^ 2 ∂ρ :
    begin
      congr' 1 with j,
      congr' 1,
      rw interval_integral.sum_integral_adjacent_intervals,
      { norm_cast },
      assume k hk,
      exact (continuous_id.pow _).interval_integrable _ _,
    end
  ... = ∑ k in range K, (∑ j in Ioo k K, ((j : ℝ) ^ 2) ⁻¹) * ∫_{k}^{(k+1 : ℕ)} x, x ^ 2 ∂ρ :
    begin
      simp_rw [mul_sum, sum_mul, sum_sigma'],
      refine sum_bij' (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ (λ a ha, rfl)
        (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ _ _,
      { rintros ⟨i, j⟩ hij,
        simp only [mem_sigma, mem_range, mem_filter] at hij,
        simp [hij, mem_sigma, mem_range, and_self, hij.2.trans hij.1], },
      { rintros ⟨i, j⟩ hij,
        simp only [mem_sigma, mem_range, mem_Ioo] at hij,
        simp only [hij, mem_sigma, mem_range, and_self], },
      { rintros ⟨i, j⟩ hij, refl },
      { rintros ⟨i, j⟩ hij, refl },
    end
  ... ≤ ∑ k in range K, (2/ (k+1)) * ∫_{k}^{(k+1 : ℕ)} x, x ^ 2 ∂ρ :
    begin
      apply sum_le_sum (λ k hk, _),
      refine mul_le_mul_of_nonneg_right (sum_Ioo_inv_sq_le _ _) _,
      refine interval_integral.integral_nonneg_of_forall _ (λ u, sq_nonneg _),
      simp only [nat.cast_add, nat.cast_one, le_add_iff_nonneg_right, zero_le_one],
    end
  ... ≤ ∑ k in range K, ∫_{k}^{(k+1 : ℕ)} x, 2 * x ∂ρ :
    begin
      apply sum_le_sum (λ k hk, _),
      have Ik : (k : ℝ) ≤ (k + 1 : ℕ), by simp,
      rw [← interval_integral.integral_const_mul, interval_integral.integral_of_le Ik,
        interval_integral.integral_of_le Ik],
      refine set_integral_mono_on _ _ measurable_set_Ioc (λ x hx, _),
      { apply continuous.integrable_on_Ioc,
        exact continuous_const.mul (continuous_pow 2) },
      { apply continuous.integrable_on_Ioc,
        exact continuous_const.mul continuous_id' },
      { calc 2 / (↑k + 1) * x ^ 2 = (x / (k+1)) * (2 * x) : by ring_exp
        ... ≤ 1 * (2 * x) :
          mul_le_mul_of_nonneg_right begin
            apply_mod_cast (div_le_one _).2 hx.2,
            simp only [nat.cast_add, nat.cast_one],
            linarith only [show (0 : ℝ) ≤ k, from  nat.cast_nonneg k],
          end (mul_nonneg zero_le_two ((nat.cast_nonneg k).trans hx.1.le))
        ... = 2 * x : by rw one_mul }
    end
  ... = 2 * ∫_{0}^{K} x, x ∂ρ :
    begin
      rw interval_integral.sum_integral_adjacent_intervals (λ k hk, _),
      swap, { exact (continuous_const.mul continuous_id').interval_integrable _ _ },
      rw interval_integral.integral_const_mul,
      norm_cast
    end
  ... ≤ 2 * 𝔼[X] :
    mul_le_mul_of_nonneg_left begin
      rw ← integral_truncation_eq_interval_integral_of_nonneg hint.1 hnonneg,
      exact integral_truncation_le_integral_of_nonneg hint hnonneg,
    end zero_le_two
end

end moment_estimates

section strong_law_nonneg

/- This paragraph proves the strong law of large numbers (almost sure version, assuming only
pairwise independence) for nonnegative random variables, following Etemadi's proof. -/

variables (X : ℕ → Ω → ℝ) (hint : integrable (X 0))
  (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
  (hident : ∀ i, ident_distrib (X i) (X 0))
  (hnonneg : ∀ i ω, 0 ≤ X i ω)

include X hint hindep hident hnonneg

/- The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers (with respect to
the truncated expectation) along the sequence `c^n`, for any `c > 1`, up to a given `ε > 0`.
This follows from a variance control. -/
lemma strong_law_aux1 {c : ℝ} (c_one : 1 < c) {ε : ℝ} (εpos : 0 < ε) :
  ∀ᵐ ω, ∀ᶠ (n : ℕ) in at_top,
    |∑ i in range ⌊c^n⌋₊, truncation (X i) i ω - 𝔼[∑ i in range ⌊c^n⌋₊, truncation (X i) i]|
      < ε * ⌊c^n⌋₊ :=
begin
  /- Let `S n = ∑ i in range n, Y i` where `Y i = truncation (X i) i`. We should show that
  `|S k - 𝔼[S k]| / k ≤ ε` along the sequence of powers of `c`. For this, we apply Borel-Cantelli:
  it suffices to show that the converse probabilites are summable. From Chebyshev inequality, this
  will follow from a variance control `∑' Var[S (c^i)] / (c^i)^2 < ∞`. This is checked in `I2` using
  pairwise independence to expand the variance of the sum as the sum of the variances, and then
  a straightforward but tedious computation (essentially boiling down to the fact that the sum of
  `1/(c ^ i)^2` beyong a threshold `j` is comparable to `1/j^2`).
  Note that we have written `c^i` in the above proof sketch, but rigorously one should put integer
  parts everywhere, making things more painful. We write `u i = ⌊c^i⌋₊` for brevity. -/
  have c_pos : 0 < c := zero_lt_one.trans c_one,
  let ρ : measure ℝ := measure.map (X 0) ℙ,
  have hX : ∀ i, ae_strongly_measurable (X i) ℙ :=
    λ i, (hident i).symm.ae_strongly_measurable_snd hint.1,
  have A : ∀ i, strongly_measurable (indicator (set.Ioc (-i : ℝ) i) id) :=
    λ i, strongly_measurable_id.indicator measurable_set_Ioc,
  set Y := λ (n : ℕ), truncation (X n) n with hY,
  set S := λ n, ∑ i in range n, Y i with hS,
  let u : ℕ → ℕ := λ n, ⌊c ^ n⌋₊,
  have u_mono : monotone u := λ i j hij, nat.floor_mono (pow_le_pow c_one.le hij),
  have I1 : ∀ K, ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * Var[Y j] ≤ 2 * 𝔼[X 0],
  { assume K,
    calc ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * Var[Y j] ≤
      ∑ j in range K, ((j : ℝ) ^ 2) ⁻¹ * 𝔼[(truncation (X 0) j)^2] :
      begin
        apply sum_le_sum (λ j hj, _),
        refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (sq_nonneg _)),
        rw (hident j).truncation.variance_eq,
        exact variance_le_expectation_sq (hX 0).truncation,
      end
      ... ≤ 2 * 𝔼[X 0] : sum_variance_truncation_le hint (hnonneg 0) K },
  let C := (c ^ 5 * (c - 1) ⁻¹ ^ 3) * (2 * 𝔼[X 0]),
  have I2 : ∀ N, ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * Var[S (u i)] ≤ C,
  { assume N,
    calc
    ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * Var[S (u i)]
        = ∑ i in range N, ((u i : ℝ) ^ 2) ⁻¹ * (∑ j in range (u i), Var[Y j]) :
      begin
        congr' 1 with i,
        congr' 1,
        rw [hS, indep_fun.variance_sum],
        { assume j hj,
          exact (hident j).ae_strongly_measurable_fst.mem_ℒp_truncation },
        { assume k hk l hl hkl,
          exact (hindep hkl).comp (A k).measurable (A l).measurable }
      end
    ... = ∑ j in range (u (N - 1)),
            (∑ i in (range N).filter (λ i, j < u i), ((u i : ℝ) ^ 2) ⁻¹) * Var[Y j] :
      begin
        simp_rw [mul_sum, sum_mul, sum_sigma'],
        refine sum_bij' (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ (λ a ha, rfl)
          (λ (p : (Σ (i : ℕ), ℕ)) hp, (⟨p.2, p.1⟩ : (Σ (i : ℕ), ℕ))) _ _ _,
        { rintros ⟨i, j⟩ hij,
          simp only [mem_sigma, mem_range] at hij,
          simp only [hij.1, hij.2, mem_sigma, mem_range, mem_filter, and_true],
          exact hij.2.trans_le (u_mono (nat.le_pred_of_lt hij.1)) },
        { rintros ⟨i, j⟩ hij,
          simp only [mem_sigma, mem_range, mem_filter] at hij,
          simp only [hij.2.1, hij.2.2, mem_sigma, mem_range, and_self] },
        { rintros ⟨i, j⟩ hij, refl },
        { rintros ⟨i, j⟩ hij, refl },
      end
    ... ≤ ∑ j in range (u (N - 1)), (c ^ 5 * (c - 1) ⁻¹ ^ 3 / j ^ 2) * Var[Y j] :
      begin
        apply sum_le_sum (λ j hj, _),
        rcases @eq_zero_or_pos _ _ j with rfl|hj,
        { simp only [Y, nat.cast_zero, zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero,
            not_false_iff, div_zero, zero_mul],
          simp only [nat.cast_zero, truncation_zero, variance_zero, mul_zero] },
        apply mul_le_mul_of_nonneg_right _ (variance_nonneg _ _),
        convert sum_div_nat_floor_pow_sq_le_div_sq N (nat.cast_pos.2 hj) c_one,
        { simp only [nat.cast_lt] },
        { simp only [one_div] }
      end
    ... = (c ^ 5 * (c - 1) ⁻¹ ^ 3) * ∑ j in range (u (N - 1)), ((j : ℝ) ^ 2) ⁻¹ * Var[Y j] :
      by { simp_rw [mul_sum, div_eq_mul_inv], ring_nf }
    ... ≤ (c ^ 5 * (c - 1) ⁻¹ ^ 3) * (2 * 𝔼[X 0]) :
      begin
        apply mul_le_mul_of_nonneg_left (I1 _),
        apply mul_nonneg (pow_nonneg c_pos.le _),
        exact pow_nonneg (inv_nonneg.2 (sub_nonneg.2 c_one.le)) _
      end },
  have I3 : ∀ N, ∑ i in range N,
    ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|} ≤ ennreal.of_real (ε ⁻¹ ^ 2 * C),
  { assume N,
    calc ∑ i in range N, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|}
        ≤ ∑ i in range N, ennreal.of_real (Var[S (u i)] / (u i * ε) ^ 2) :
      begin
        refine sum_le_sum (λ i hi, _),
        apply meas_ge_le_variance_div_sq,
        { exact mem_ℒp_finset_sum' _
            (λ j hj, (hident j).ae_strongly_measurable_fst.mem_ℒp_truncation) },
        { apply mul_pos (nat.cast_pos.2 _) εpos,
          refine zero_lt_one.trans_le _,
          apply nat.le_floor,
          rw nat.cast_one,
          apply one_le_pow_of_one_le c_one.le }
      end
    ... = ennreal.of_real (∑ i in range N, Var[S (u i)] / (u i * ε) ^ 2) :
      begin
        rw ennreal.of_real_sum_of_nonneg (λ i hi, _),
        exact div_nonneg (variance_nonneg _ _) (sq_nonneg _),
      end
    ... ≤ ennreal.of_real (ε ⁻¹ ^ 2 * C) :
      begin
        apply ennreal.of_real_le_of_real,
        simp_rw [div_eq_inv_mul, ← inv_pow, mul_inv, mul_comm _ (ε⁻¹), mul_pow, mul_assoc,
          ← mul_sum],
        refine mul_le_mul_of_nonneg_left _ (sq_nonneg _),
        simp_rw [inv_pow],
        exact I2 N
      end },
  have I4 : ∑' i, ℙ {ω | (u i * ε : ℝ) ≤ |S (u i) ω - 𝔼[S (u i)]|} < ∞ :=
    (le_of_tendsto_of_tendsto' (ennreal.tendsto_nat_tsum _) tendsto_const_nhds I3).trans_lt
      ennreal.of_real_lt_top,
  filter_upwards [ae_eventually_not_mem I4.ne] with ω hω,
  simp_rw [not_le, mul_comm, S, sum_apply] at hω,
  exact hω,
end

/- The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers
(with respect to the truncated expectation) along the sequence
`c^n`, for any `c > 1`. This follows from `strong_law_aux1` by varying `ε`. -/
lemma strong_law_aux2 {c : ℝ} (c_one : 1 < c) :
  ∀ᵐ ω, (λ (n : ℕ), ∑ i in range ⌊c^n⌋₊, truncation (X i) i ω
    - 𝔼[∑ i in range ⌊c^n⌋₊, truncation (X i) i]) =o[at_top] (λ (n : ℕ), (⌊c^n⌋₊ : ℝ)) :=
begin
  obtain ⟨v, -, v_pos, v_lim⟩ :
    ∃ (v : ℕ → ℝ), strict_anti v ∧ (∀ (n : ℕ), 0 < v n) ∧ tendsto v at_top (𝓝 0) :=
      exists_seq_strict_anti_tendsto (0 : ℝ),
  have := λ i, strong_law_aux1 X hint hindep hident hnonneg c_one (v_pos i),
  filter_upwards [ae_all_iff.2 this] with ω hω,
  apply asymptotics.is_o_iff.2 (λ ε εpos, _),
  obtain ⟨i, hi⟩ : ∃ i, v i < ε := ((tendsto_order.1 v_lim).2 ε εpos).exists,
  filter_upwards [hω i] with n hn,
  simp only [real.norm_eq_abs, lattice_ordered_comm_group.abs_abs, nat.abs_cast],
  exact hn.le.trans (mul_le_mul_of_nonneg_right hi.le (nat.cast_nonneg _)),
end

omit hindep hnonneg
/-- The expectation of the truncated version of `Xᵢ` behaves asymptotically like the whole
expectation. This follows from convergence and Cesaro averaging. -/
lemma strong_law_aux3 :
  (λ n, 𝔼[∑ i in range n, truncation (X i) i] - n * 𝔼[X 0]) =o[at_top] (coe : ℕ → ℝ) :=
begin
  have A : tendsto (λ i, 𝔼[truncation (X i) i]) at_top (𝓝 (𝔼[X 0])),
  { convert (tendsto_integral_truncation hint).comp tendsto_coe_nat_at_top_at_top,
    ext i,
    exact (hident i).truncation.integral_eq },
  convert asymptotics.is_o_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 A),
  ext1 n,
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, sum_apply, sub_left_inj],
  rw integral_finset_sum _ (λ i hi, _),
  exact ((hident i).symm.integrable_snd hint).1.integrable_truncation,
end
include hindep hnonneg

/- The truncation of `Xᵢ` up to `i` satisfies the strong law of large numbers
(with respect to the original expectation) along the sequence
`c^n`, for any `c > 1`. This follows from the version from the truncated expectation, and the
fact that the truncated and the original expectations have the same asymptotic behavior. -/
lemma strong_law_aux4 {c : ℝ} (c_one : 1 < c) :
  ∀ᵐ ω, (λ (n : ℕ), ∑ i in range ⌊c^n⌋₊, truncation (X i) i ω - ⌊c^n⌋₊ * 𝔼[X 0]) =o[at_top]
    (λ (n : ℕ), (⌊c^n⌋₊ : ℝ)) :=
begin
  filter_upwards [strong_law_aux2 X hint hindep hident hnonneg c_one] with ω hω,
  have A : tendsto (λ (n : ℕ), ⌊c ^ n⌋₊) at_top at_top :=
    tendsto_nat_floor_at_top.comp (tendsto_pow_at_top_at_top_of_one_lt c_one),
  convert hω.add ((strong_law_aux3 X hint hident).comp_tendsto A),
  ext1 n,
  simp,
end

omit hindep
/-- The truncated and non-truncated versions of `Xᵢ` have the same asymptotic behavior, as they
almost surely coincide at all but finitely many steps. This follows from a probability computation
and Borel-Cantelli. -/
lemma strong_law_aux5 :
  ∀ᵐ ω, (λ (n : ℕ), ∑ i in range n, truncation (X i) i ω - ∑ i in range n, X i ω) =o[at_top]
    (λ (n : ℕ), (n : ℝ)) :=
begin
  have A : ∑' (j : ℕ), ℙ {ω | X j ω ∈ set.Ioi (j : ℝ)} < ∞,
  { convert tsum_prob_mem_Ioi_lt_top hint (hnonneg 0),
    ext1 j,
    exact (hident j).measure_mem_eq measurable_set_Ioi },
  have B : ∀ᵐ ω, tendsto (λ (n : ℕ), truncation (X n) n ω - X n ω) at_top (𝓝 0),
  { filter_upwards [ae_eventually_not_mem A.ne] with ω hω,
    apply tendsto_const_nhds.congr' _,
    filter_upwards [hω, Ioi_mem_at_top 0] with n hn npos,
    simp only [truncation, indicator, set.mem_Ioc, id.def, function.comp_app],
    split_ifs,
    { exact (sub_self _).symm },
    { have : - (n : ℝ) < X n ω,
      { apply lt_of_lt_of_le _ (hnonneg n ω),
        simpa only [right.neg_neg_iff, nat.cast_pos] using npos },
      simp only [this, true_and, not_le] at h,
      exact (hn h).elim } },
  filter_upwards [B] with ω hω,
  convert is_o_sum_range_of_tendsto_zero hω,
  ext n,
  rw sum_sub_distrib,
end
include hindep

/- `Xᵢ` satisfies the strong law of large numbers along the sequence
`c^n`, for any `c > 1`. This follows from the version for the truncated `Xᵢ`, and the fact that
`Xᵢ` and its truncated version have the same asymptotic behavior. -/
lemma strong_law_aux6 {c : ℝ} (c_one : 1 < c) :
  ∀ᵐ ω, tendsto (λ (n : ℕ), (∑ i in range ⌊c^n⌋₊, X i ω) / ⌊c^n⌋₊) at_top (𝓝 (𝔼[X 0])) :=
begin
   have H : ∀ (n : ℕ), (0 : ℝ) < ⌊c ^ n⌋₊,
  { assume n,
    refine zero_lt_one.trans_le _,
    simp only [nat.one_le_cast, nat.one_le_floor_iff, one_le_pow_of_one_le c_one.le n] },
  filter_upwards [strong_law_aux4 X hint hindep hident hnonneg c_one,
    strong_law_aux5 X hint hident hnonneg] with ω hω h'ω,
  rw [← tendsto_sub_nhds_zero_iff, ← asymptotics.is_o_one_iff ℝ],
  have L : (λ n : ℕ, ∑ i in range ⌊c^n⌋₊, X i ω - ⌊c^n⌋₊ * 𝔼[X 0]) =o[at_top] (λ n, (⌊c^n⌋₊ : ℝ)),
  { have A : tendsto (λ (n : ℕ), ⌊c ^ n⌋₊) at_top at_top :=
      tendsto_nat_floor_at_top.comp (tendsto_pow_at_top_at_top_of_one_lt c_one),
    convert hω.sub (h'ω.comp_tendsto A),
    ext1 n,
    simp only [sub_sub_sub_cancel_left] },
  convert L.mul_is_O (is_O_refl (λ (n : ℕ), (⌊c ^ n⌋₊ : ℝ) ⁻¹) at_top);
  { ext1 n,
    field_simp [(H n).ne'] },
end

/-- `Xᵢ` satisfies the strong law of large numbers along all integers. This follows from the
corresponding fact along the sequences `c^n`, and the fact that any integer can be sandwiched
between `c^n` and `c^(n+1)` with comparably small error if `c` is close enough to `1`
(which is formalized in `tendsto_div_of_monotone_of_tendsto_div_floor_pow`). -/
lemma strong_law_aux7 :
  ∀ᵐ ω, tendsto (λ (n : ℕ), (∑ i in range n, X i ω) / n) at_top (𝓝 (𝔼[X 0])) :=
begin
  obtain ⟨c, -, cone, clim⟩ :
    ∃ (c : ℕ → ℝ), strict_anti c ∧ (∀ (n : ℕ), 1 < c n) ∧ tendsto c at_top (𝓝 1) :=
      exists_seq_strict_anti_tendsto (1 : ℝ),
  have : ∀ k, ∀ᵐ ω, tendsto (λ (n : ℕ), (∑ i in range ⌊c k ^ n⌋₊, X i ω) / ⌊c k ^ n⌋₊)
    at_top (𝓝 (𝔼[X 0])) := λ k, strong_law_aux6 X hint hindep hident hnonneg (cone k),
  filter_upwards [ae_all_iff.2 this] with ω hω,
  apply tendsto_div_of_monotone_of_tendsto_div_floor_pow _ _ _ c cone clim _,
  { assume m n hmn,
    exact sum_le_sum_of_subset_of_nonneg (range_mono hmn) (λ i hi h'i, hnonneg i ω) },
  { exact hω }
end

end strong_law_nonneg

/-- *Strong law of large numbers*, almost sure version: if `X n` is a sequence of independent
identically distributed integrable real-valued random variables, then `∑ i in range n, X i / n`
converges almost surely to `𝔼[X 0]`. We give here the strong version, due to Etemadi, that only
requires pairwise independence. -/
theorem strong_law_ae
  (X : ℕ → Ω → ℝ) (hint : integrable (X 0))
  (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
  (hident : ∀ i, ident_distrib (X i) (X 0)) :
  ∀ᵐ ω, tendsto (λ (n : ℕ), (∑ i in range n, X i ω) / n) at_top (𝓝 (𝔼[X 0])) :=
begin
  let pos : ℝ → ℝ := (λ x, max x 0),
  let neg : ℝ → ℝ := (λ x, max (-x) 0),
  have posm : measurable pos := measurable_id'.max measurable_const,
  have negm : measurable neg := measurable_id'.neg.max measurable_const,
  have A : ∀ᵐ ω, tendsto (λ (n : ℕ), (∑ i in range n, (pos ∘ (X i)) ω) / n)
    at_top (𝓝 (𝔼[pos ∘ (X 0)])) :=
      strong_law_aux7 _ hint.pos_part (λ i j hij, (hindep hij).comp posm posm)
        (λ i, (hident i).comp posm) (λ i ω, le_max_right _ _),
  have B : ∀ᵐ ω, tendsto (λ (n : ℕ), (∑ i in range n, (neg ∘ (X i)) ω) / n)
    at_top (𝓝 (𝔼[neg ∘ (X 0)])) :=
      strong_law_aux7 _ hint.neg_part (λ i j hij, (hindep hij).comp negm negm)
        (λ i, (hident i).comp negm) (λ i ω, le_max_right _ _),
  filter_upwards [A, B] with ω hωpos hωneg,
  convert hωpos.sub hωneg,
  { simp only [← sub_div, ← sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self] },
  { simp only [←integral_sub hint.pos_part hint.neg_part, max_zero_sub_max_neg_zero_eq_self] }
end

end strong_law_ae

section strong_law_Lp

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

/-- *Strong law of large numbers*, Lᵖ version: if `X n` is a sequence of independent
identically distributed real-valued random variables in Lᵖ, then `∑ i in range n, X i / n`
converges in Lᵖ to `𝔼[X 0]`. -/
theorem strong_law_Lp
  {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
  (X : ℕ → Ω → ℝ) (hℒp : mem_ℒp (X 0) p)
  (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
  (hident : ∀ i, ident_distrib (X i) (X 0)) :
  tendsto (λ n, snorm (λ ω, (∑ i in range n, X i ω) / n - 𝔼[X 0]) p ℙ) at_top (𝓝 0) :=
begin
  have hmeas : ∀ i, ae_strongly_measurable (X i) ℙ :=
    λ i, (hident i).ae_strongly_measurable_iff.2 hℒp.1,
  have hint : integrable (X 0) ℙ := hℒp.integrable hp,
  have havg : ∀ n, ae_strongly_measurable (λ ω, (∑ i in range n, X i ω) / n) ℙ,
  { intro n,
    simp_rw div_eq_mul_inv,
    exact ae_strongly_measurable.mul_const (ae_strongly_measurable_sum _  (λ i _, hmeas i)) _ },
  refine tendsto_Lp_of_tendsto_in_measure _ hp hp' havg (mem_ℒp_const _) _
    (tendsto_in_measure_of_tendsto_ae havg (strong_law_ae _ hint hindep hident)),
  rw (_ : (λ n ω, (∑ i in range n, X i ω) / ↑n) = λ n, (∑ i in range n, X i) / ↑n),
  { exact (uniform_integrable_average hp $
      mem_ℒp.uniform_integrable_of_ident_distrib hp hp' hℒp hident).2.1 },
  { ext n ω,
    simp only [pi.coe_nat, pi.div_apply, sum_apply] }
end

end strong_law_Lp

end probability_theory
