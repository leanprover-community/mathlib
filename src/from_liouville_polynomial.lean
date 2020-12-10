/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.polynomial.basic
--import data.polynomial.derivative
--import data.polynomial.ring_division
import data.set.intervals.infinite
--import topology.instances.real
import topology.algebra.polynomial
import analysis.calculus.mean_value

/-!
This file contains the some lemmas about real polynomials and their derivatives
-/

open polynomial real set finset nat

/-- I could not find a good home for these last two results
The following result does not require the assumption that `f` be non-zero, as
`0.roots` is defined to be `∅`.
-/
lemma roots_discrete (f : polynomial ℝ) : discrete_topology {a : ℝ // a ∈ f.roots.to_finset} :=
discrete_of_t1_of_finite

lemma polynomial_eval_zero_discrete {f : polynomial ℝ} (hf : f ≠ 0) :
  discrete_topology {a : ℝ // f.eval a = 0} :=
begin
  rw polynomial.eval_zero_eq_roots hf,
  convert roots_discrete f;
  { simp_rw [multiset.mem_to_finset] },
end


lemma exists_forall_ge_of_polynomial_eval (α : ℝ) (f : polynomial ℝ)
  (h_f_deg : 0 < f.nat_degree) :
  ∃ M : ℝ, 0 < M ∧ ∀ (y : ℝ), abs (y - α) ≤ 1 → abs (eval y f) ≤ M :=
begin

  have h_f_nonzero : f ≠ 0 := ne_zero_of_degree_gt (nat_degree_pos_iff_degree_pos.mp h_f_deg),
  obtain ⟨x_max, ⟨h_x_max_range, hM⟩⟩ := is_compact.exists_forall_ge (@compact_Icc (α-1) (α+1))
    begin rw set.nonempty, use α, rw set.mem_Icc, split; linarith end
    (continuous_abs.comp f.continuous_eval).continuous_on,
  replace hM : ∀ (y : ℝ), y ∈ Icc (α - 1) (α + 1) →
    abs (eval y f) ≤ abs (eval x_max f),
    { simpa only [function.comp_app abs] },
  set M := abs (f.eval x_max),
  use M,
  split,
  { apply lt_of_le_of_ne (abs_nonneg _),
    intro hM0, change 0 = M at hM0, rw hM0.symm at hM,
    { refine h_f_nonzero (f.eq_zero_of_infinite_is_root _),
      refine infinite_mono (λ y hy, _) (Icc.infinite (show α - 1 < α + 1, by linarith)),
      simp only [mem_set_of_eq, is_root.def],
      exact abs_nonpos_iff.1 (hM y hy) }},
  intros y hy,
  have hy' : y ∈ Icc (α - 1) (α + 1),
  { apply mem_Icc.mpr,
    have h1 := le_abs_self (y - α),
    have h2 := neg_le_abs_self (y - α),
    split; linarith },
  exact hM y hy'
end

lemma non_root_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0) :
  ∃ B : ℝ, 0 < B ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  set f_roots := f.roots.to_finset.erase α,
  set distances := insert (1 : ℝ) (f_roots.image (λ x, abs (α - x))),
  have h_nonempty : distances.nonempty := ⟨1, finset.mem_insert_self _ _⟩,
  set B := distances.min' h_nonempty with hB,
  have h_allpos : ∀ x : ℝ, x ∈ distances → 0 < x,
  { intros x hx, rw [finset.mem_insert, finset.mem_image] at hx,
    rcases hx with rfl | ⟨α₀, ⟨h, rfl⟩⟩,
    { exact zero_lt_one },
    { rw [finset.mem_erase] at h,
      rw [abs_pos, sub_ne_zero], exact h.1.symm }},
  use [B, (h_allpos B (distances.min'_mem h_nonempty))],
  intros x hx hxα,
  have hab₂ : x ∉ f.roots.to_finset,
  { intro h,
    have h₁ : x ∈ f_roots, { rw [finset.mem_erase], exact ⟨hxα, h⟩ },
    have h₂ : abs (α - x) ∈ distances,
    { rw [finset.mem_insert, finset.mem_image], right, exact ⟨x, ⟨h₁, rfl⟩⟩ },
    have h₃ := finset.min'_le distances (abs (α - x)) h₂,
    erw ←hB at h₃, linarith only [lt_of_lt_of_le hx h₃] },
  rwa [multiset.mem_to_finset, mem_roots h_f_nonzero, is_root.def] at hab₂
end

lemma non_root_small_interval_of_polynomial (α : ℝ) (f : polynomial ℝ) (h_f_nonzero : f ≠ 0)
  (M : ℝ) (hM : 0 < M) :
  ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1
  ∧ ∀ x (hr : abs (α - x) < B) (hn : x ≠ α), f.eval x ≠ 0 :=
begin
  obtain ⟨B0, ⟨h_B0_pos, h_B0_root⟩⟩ := non_root_interval_of_polynomial α f h_f_nonzero,
  have h1M : 0 < 1 / M := one_div_pos.mpr hM,
  obtain ⟨B1, ⟨hB11, hB12, hB13⟩⟩ : ∃ B1 : ℝ, 0 < B1 ∧ B1 ≤ 1 / M ∧ B1 ≤ B0,
  { cases le_or_gt (1 / M) B0,
    { use 1 / M, tauto },
    { exact ⟨B0, h_B0_pos, le_of_lt h, le_refl B0⟩ }},
  obtain ⟨B, ⟨hB1, hB2, hB3, hB4⟩⟩ : ∃ B : ℝ, 0 < B ∧ B ≤ 1 / M ∧ B ≤ 1 ∧ B ≤ B0,
  { cases le_or_gt 1 B1,
    { use 1, split, norm_num, split, linarith, split, norm_num, linarith },
    { use B1, exact ⟨hB11, ⟨hB12, ⟨le_of_lt h, hB13⟩⟩⟩ }},
  refine ⟨B, hB1, hB2, hB3, λ (x : ℝ) (hx : abs (α - x) < B), h_B0_root x _ ⟩,
  linarith
end

lemma exists_deriv_eq_slope_of_polynomial_root (α : ℝ) (f : polynomial ℝ) (h_α_root : f.eval α = 0)
  (x : ℝ) (h : f.eval x ≠ 0) :
  ∃ x₀, α - x = - ((f.eval x) / (f.derivative.eval x₀))
    ∧ f.derivative.eval x₀ ≠ 0
    ∧ abs (α - x₀) < abs (α - x)
    ∧ abs (x - x₀) < abs (α - x) :=
begin
  have h₀ : x ≠ α, { intro h₁, rw ← h₁ at h_α_root, rw h_α_root at h, tauto },
  rcases ne_iff_lt_or_gt.1 h₀ with h_α_gt | h_α_lt,
  { -- When `x < α`
    have h_cont : continuous_on (λ x, f.eval x) (Icc x α) := f.continuous_eval.continuous_on,
    have h_diff : differentiable_on ℝ (λ x, f.eval x) (Ioo x α) :=
      differentiable.differentiable_on f.differentiable,
    rcases (exists_deriv_eq_slope (λ x, f.eval x) h_α_gt h_cont h_diff) with ⟨x₀, x₀_range, hx₀⟩,
    rw polynomial.deriv at hx₀,
    change eval x₀ f.derivative = (eval α f - eval x f) / (α - x) at hx₀,
    rw [h_α_root, zero_sub] at hx₀,
    replace hx₀ := hx₀.symm,
    have h_Df_nonzero : f.derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ hc, h
      begin
      rwa [hc, neg_div, neg_eq_zero, div_eq_iff (show α - x ≠ 0, by linarith), zero_mul] at hx₀ end,
    use x₀,
    split,
    { symmetry, rw ← neg_div, rw div_eq_iff at hx₀ ⊢, rwa mul_comm,
      exact h_Df_nonzero,
      rw sub_ne_zero, exact h₀.symm },
    apply and.intro h_Df_nonzero,
    rw mem_Ioo at x₀_range,
    rw [abs_of_pos (sub_pos.mpr h_α_gt), abs_of_pos (sub_pos.mpr x₀_range.2),
      abs_of_neg (sub_lt_zero.mpr x₀_range.1)],
    split; linarith },
  { -- When `α < x`
    have h_cont : continuous_on (λ x, f.eval x) (Icc α x) := f.continuous_eval.continuous_on,
    have h_diff : differentiable_on ℝ (λ x, f.eval x) (Ioo α x):=
      differentiable.differentiable_on f.differentiable,
    rcases (exists_deriv_eq_slope (λ x, f.eval x) h_α_lt h_cont h_diff) with ⟨x₀, x₀_range, hx₀⟩,
    rw polynomial.deriv at hx₀,
    change eval x₀ f.derivative = (eval x f - eval α f) / (x - α) at hx₀,
    rw [h_α_root, sub_zero] at hx₀,
    replace hx₀ := hx₀.symm,
    have h_Df_nonzero : f.derivative.eval x₀ ≠ 0 := hx₀.symm ▸ λ hc, h
      begin rwa [hc, div_eq_iff (show x - α ≠ 0, by linarith), zero_mul] at hx₀ end,
    use x₀,
    split,
    { symmetry, rw ← neg_div, rw div_eq_iff at hx₀ ⊢,
      {rw hx₀, ring },
      { exact h_Df_nonzero },
      { rwa sub_ne_zero }},
    apply and.intro h_Df_nonzero,
    rw mem_Ioo at x₀_range,
    rw [abs_of_neg (sub_lt_zero.mpr x₀_range.1), abs_of_neg (sub_lt_zero.mpr h_α_lt),
      abs_of_pos (sub_pos.mpr x₀_range.2)],
    split; linarith }
end
