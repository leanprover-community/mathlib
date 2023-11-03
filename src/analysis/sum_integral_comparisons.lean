/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
import measure_theory.integral.interval_integral
import data.set.function
import analysis.special_functions.integrals

/-!
# Comparing sums and integrals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

It is often the case that error terms in analysis can be computed by comparing
an infinite sum to the improper integral of an antitone function. This file will eventually enable
that.

At the moment it contains four lemmas in this direction: `antitone_on.integral_le_sum`,
`antitone_on.sum_le_integral` and versions for monotone functions, which can all be paired
with a `filter.tendsto` to estimate some errors.

`TODO`: Add more lemmas to the API to directly address limiting issues

## Main Results

* `antitone_on.integral_le_sum`: The integral of an antitone function is at most the sum of its
  values at integer steps aligning with the left-hand side of the interval
* `antitone_on.sum_le_integral`: The sum of an antitone function along integer steps aligning with
  the right-hand side of the interval is at most the integral of the function along that interval
* `monotone_on.integral_le_sum`: The integral of a monotone function is at most the sum of its
  values at integer steps aligning with the right-hand side of the interval
* `monotone_on.sum_le_integral`: The sum of a monotone function along integer steps aligning with
  the left-hand side of the interval is at most the integral of the function along that interval

## Tags

analysis, comparison, asymptotics
-/

open set measure_theory.measure_space
open_locale big_operators

variables {x₀ : ℝ} {a b : ℕ} {f : ℝ → ℝ}

lemma antitone_on.integral_le_sum (hf : antitone_on f (Icc x₀ (x₀ + a))) :
  ∫_{x₀}^{(x₀ + a)} x, f x ≤ ∑ i in finset.range a, f (x₀ + i) :=
begin
  have hint : ∀ (k : ℕ), k < a → interval_integrable f volume (x₀+k) (x₀ + (k + 1 : ℕ)),
  { assume k hk,
    refine (hf.mono _).interval_integrable,
    rw uIcc_of_le,
    { apply Icc_subset_Icc,
      { simp only [le_add_iff_nonneg_right, nat.cast_nonneg] },
      { simp only [add_le_add_iff_left, nat.cast_le, nat.succ_le_of_lt hk] } },
    { simp only [add_le_add_iff_left, nat.cast_le, nat.le_succ] } },
  calc
  ∫_{x₀}^{(x₀ + a)} x, f x = ∑ i in finset.range a, ∫_{(x₀+i)}^{(x₀+(i+1 : ℕ))} x, f x :
    begin
      convert (interval_integral.sum_integral_adjacent_intervals hint).symm,
      simp only [nat.cast_zero, add_zero],
    end
  ... ≤ ∑ i in finset.range a, ∫_{(x₀+i)}^{(x₀+(i+1 : ℕ))} x, f (x₀ + i) :
    begin
      apply finset.sum_le_sum (λ i hi, _),
      have ia : i < a := finset.mem_range.1 hi,
      refine interval_integral.integral_mono_on (by simp) (hint _ ia) (by simp) (λ x hx, _),
      apply hf _ _ hx.1,
      { simp only [ia.le, mem_Icc, le_add_iff_nonneg_right, nat.cast_nonneg, add_le_add_iff_left,
          nat.cast_le, and_self] },
      { refine mem_Icc.2 ⟨le_trans (by simp) hx.1, le_trans hx.2 _⟩,
        simp only [add_le_add_iff_left, nat.cast_le, nat.succ_le_of_lt ia] },
    end
  ... = ∑ i in finset.range a, f (x₀ + i) : by simp
end

lemma antitone_on.integral_le_sum_Ico (hab : a ≤ b) (hf : antitone_on f (set.Icc a b)) :
  ∫_{a}^{b} x, f x ≤ ∑ x in finset.Ico a b, f x :=
begin
  rw [(nat.sub_add_cancel hab).symm, nat.cast_add],
  conv { congr, congr, skip, skip, rw add_comm, skip, skip, congr, congr, rw ←zero_add a, },
  rw [← finset.sum_Ico_add, nat.Ico_zero_eq_range],
  conv { to_rhs, congr, skip, funext, rw nat.cast_add, },
  apply antitone_on.integral_le_sum,
  simp only [hf, hab, nat.cast_sub, add_sub_cancel'_right],
end

lemma antitone_on.sum_le_integral (hf : antitone_on f (Icc x₀ (x₀ + a))) :
  ∑ i in finset.range a, f (x₀ + (i + 1 : ℕ)) ≤ ∫_{x₀}^{(x₀ + a)} x, f x :=
begin
  have hint : ∀ (k : ℕ), k < a → interval_integrable f volume (x₀+k) (x₀ + (k + 1 : ℕ)),
  { assume k hk,
    refine (hf.mono _).interval_integrable,
    rw uIcc_of_le,
    { apply Icc_subset_Icc,
      { simp only [le_add_iff_nonneg_right, nat.cast_nonneg] },
      { simp only [add_le_add_iff_left, nat.cast_le, nat.succ_le_of_lt hk] } },
    { simp only [add_le_add_iff_left, nat.cast_le, nat.le_succ] } },
  calc ∑ i in finset.range a, f (x₀ + (i + 1 : ℕ))
      = ∑ i in finset.range a, ∫_{(x₀+i)}^{(x₀+(i+1:ℕ))} x, f (x₀ + (i + 1 : ℕ)) : by simp
  ... ≤ ∑ i in finset.range a, ∫_{(x₀+i)}^{(x₀+(i+1:ℕ))} x, f x :
    begin
      apply finset.sum_le_sum (λ i hi, _),
      have ia : i + 1 ≤ a := finset.mem_range.1 hi,
      refine interval_integral.integral_mono_on (by simp) (by simp) (hint _ ia) (λ x hx, _),
      apply hf _ _ hx.2,
      { refine mem_Icc.2 ⟨le_trans ((le_add_iff_nonneg_right _).2 (nat.cast_nonneg _)) hx.1,
          le_trans hx.2 _⟩,
        simp only [nat.cast_le, add_le_add_iff_left, ia] },
      { refine mem_Icc.2 ⟨(le_add_iff_nonneg_right _).2 (nat.cast_nonneg _), _⟩,
        simp only [add_le_add_iff_left, nat.cast_le, ia] },
    end
  ... = ∫_{x₀}^{(x₀ + a)} x, f x :
    begin
      convert interval_integral.sum_integral_adjacent_intervals hint,
      simp only [nat.cast_zero, add_zero],
    end
end

lemma antitone_on.sum_le_integral_Ico (hab : a ≤ b) (hf : antitone_on f (set.Icc a b)) :
  ∑ i in finset.Ico a b, f (i + 1 : ℕ) ≤ ∫_{a}^{b} x, f x :=
begin
  rw [(nat.sub_add_cancel hab).symm, nat.cast_add],
  conv { congr, congr, congr, rw ← zero_add a, skip, skip, skip, rw add_comm, },
  rw [← finset.sum_Ico_add, nat.Ico_zero_eq_range],
  conv { to_lhs, congr, congr, skip, funext, rw [add_assoc, nat.cast_add], },
  apply antitone_on.sum_le_integral,
  simp only [hf, hab, nat.cast_sub, add_sub_cancel'_right],
end

lemma monotone_on.sum_le_integral (hf : monotone_on f (Icc x₀ (x₀ + a))) :
  ∑ i in finset.range a, f (x₀ + i) ≤ ∫_{x₀}^{(x₀ + a)} x, f x :=
begin
  rw [← neg_le_neg_iff, ← finset.sum_neg_distrib, ← interval_integral.integral_neg],
  exact hf.neg.integral_le_sum,
end

lemma monotone_on.sum_le_integral_Ico (hab : a ≤ b) (hf : monotone_on f (set.Icc a b)) :
  ∑ x in finset.Ico a b, f x ≤ ∫_{a}^{b} x, f x :=
begin
  rw [← neg_le_neg_iff, ← finset.sum_neg_distrib, ← interval_integral.integral_neg],
  exact hf.neg.integral_le_sum_Ico hab,
end

lemma monotone_on.integral_le_sum (hf : monotone_on f (Icc x₀ (x₀ + a))) :
  ∫_{x₀}^{(x₀ + a)} x, f x ≤ ∑ i in finset.range a, f (x₀ + (i + 1 : ℕ)) :=
begin
  rw [← neg_le_neg_iff, ← finset.sum_neg_distrib, ← interval_integral.integral_neg],
  exact hf.neg.sum_le_integral,
end

lemma monotone_on.integral_le_sum_Ico (hab : a ≤ b) (hf : monotone_on f (set.Icc a b)) :
  ∫_{a}^{b} x, f x ≤ ∑ i in finset.Ico a b, f (i + 1 : ℕ) :=
begin
  rw [← neg_le_neg_iff, ← finset.sum_neg_distrib, ← interval_integral.integral_neg],
  exact hf.neg.sum_le_integral_Ico hab,
end
