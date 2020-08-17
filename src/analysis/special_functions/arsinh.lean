/-
Copyright (c) 2020 James Arthur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Chris Hughes, Shing Tak Lam.
-/
import analysis.special_functions.trigonometric

open real
noncomputable theory

/-!
# Inverse of the sinh function

In this file we prove that sinh is bijective and hence has an
inverse, arsinh.

## Main Results

- `sinh_injective`: The proof that `sinh` is injective
- `sinh_surjective`: The proof that `sinh` is surjective
- `sinh_bijective`: The proof `sinh` is bijective
- `arsinh`: The inverse function of `sinh`

## Tags

arsinh, arcsinh, argsinh, asinh, sinh injective, sinh bijective, sinh surjective
-/


/-- `arsinh` is defined using a logarithm, `arsinh x = log (x + sqrt(1 + x^2))` -/
def arsinh (x : ℝ) := log (x + sqrt(1 + x^2))

/-- `sinh` is injective, `∀ a b, sinh a = sinh b → a = b` -/
lemma sinh_injective : function.injective sinh := sinh_strict_mono.injective

private lemma aux_lemma (x : ℝ) : 1 / (x + sqrt (1 + x^2)) = -x + sqrt (1 + x^2) :=
begin
  refine (eq_one_div_of_mul_eq_one _).symm,
  have : 0 ≤ 1 + x ^ 2 := add_nonneg zero_le_one (pow_two_nonneg x),
  rw [add_comm, ← sub_eq_neg_add, ← mul_self_sub_mul_self,
      mul_self_sqrt this, pow_two, add_sub_cancel]
end

private lemma b_lt_sqrt_b_sq_add_one (b : ℝ) : b < sqrt (b^2 + 1) :=
begin
  by_cases hb : 0 ≤ b,
  conv { to_lhs, rw ← sqrt_sqr hb },
  rw sqrt_lt,
  linarith,
  apply pow_two_nonneg,
  have F : 0 ≤ b^2 := by apply pow_two_nonneg,
  { linarith },
  rw not_le at hb,
  apply lt_of_lt_of_le hb,
  apply sqrt_nonneg,
end

/-- `arsinh` is the right inverse of `sinh`-/
lemma arsinh_sinh (x : ℝ) : sinh (arsinh x) = x :=
begin
  rw sinh_eq,
  unfold arsinh,
  rw [←log_inv, exp_log, exp_log],
  { rw [← one_mul ((x + sqrt (1 + x ^ 2))⁻¹), ←division_def, aux_lemma],
    ring },
  { rw [← one_mul ((x + sqrt (1 + x ^ 2))⁻¹), ←division_def, aux_lemma],
    ring,
    rw [neg_add_eq_sub, sub_pos],
    have H : x^2 < sqrt (x ^ 2 + 1)^2,
    { rw sqr_sqrt,
      linarith,
      have F : 0 ≤ x^2 := by apply pow_two_nonneg,
      linarith },
    exact b_lt_sqrt_b_sq_add_one x,
  },
  { have H := b_lt_sqrt_b_sq_add_one (-x),
    rw [neg_square, add_comm (x^2)] at H,
    linarith },
end

/-- `sinh` is surjective, `∀ b, ∃ a, sinh a = b`. In this case, we use `a = arsinh b` -/
lemma sinh_surjective : function.surjective sinh := function.left_inverse.surjective arsinh_sinh

/-- `sinh` is bijective, both injective and surjective-/
lemma sinh_bijective : function.bijective sinh :=
⟨sinh_injective, sinh_surjective⟩

/-- A rearrangment and `sqrt` of `real.cosh_sq_sub_sinh_sq` -/
lemma sqrt_one_add_sinh_sq (x : ℝ): sqrt (1 + sinh x ^ 2) = cosh x :=
begin
  have H := real.cosh_sq_sub_sinh_sq x,
  have G : cosh x ^ 2 - sinh x ^ 2 + sinh x ^ 2 = 1 + sinh x ^ 2 := by rw H,
  rw sub_add_cancel at G,
  rw [←G, sqrt_sqr],
  exact le_of_lt (cosh_pos x),
end

/-- `arsinh` is the left inverse of `sinh` -/
lemma sinh_arsinh (x : ℝ) : arsinh (sinh x) = x :=
begin
  unfold arsinh,
  rw sinh_eq,
  apply exp_injective,
  rw exp_log,
  { rw [← sinh_eq, sqrt_one_add_sinh_sq, cosh_eq, sinh_eq],
    ring },
  { rw [← sinh_eq, sqrt_one_add_sinh_sq, cosh_eq, sinh_eq],
    ring,
    exact exp_pos x },
end
