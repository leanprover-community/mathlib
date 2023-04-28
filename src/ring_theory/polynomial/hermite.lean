/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/

import data.polynomial.derivative
import data.nat.parity
import analysis.special_functions.exp
import analysis.special_functions.exp_deriv

/-!
# Hermite polynomials

This file defines `polynomial.hermite n`, the nth probabilist's Hermite polynomial.

## Main definitions

* `polynomial.hermite n`: the `n`th probabilist's Hermite polynomial,
  defined recursively as a `polynomial ℤ`
* `gaussian`: the real Gaussian function

## Results

* `polynomial.coeff_hermite_of_odd_add`: for `n`,`k` where `n+k` is odd, `(hermite n).coeff k` is
  zero.
* `polynomial.monic_hermite`: for all `n`, `hermite n` is monic.
* `polynomial.hermite_eq_gauss`: the recursive polynomial definition is equivalent to the
  definition of the Hermite polynomial as the polynomial factor occurring in the `n`-th derivative
  of a gaussian. That is, for all `n` and `x`,

## Implementation details

We proceed by defining an auxiliary function `polynomial.hermite_gauss n` directly in terms of the
`n`th derivative of a gaussian function. We show that it satisfies the same recurrence relation as
the polynomial definition of `hermite n`, and hence that the two definitions are equivalent. This
definition is not intended to be used outside of this file.

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

noncomputable theory
open polynomial

namespace polynomial

/-- the nth probabilist's Hermite polynomial -/
noncomputable def hermite : ℕ → polynomial ℤ
| 0     := 1
| (n+1) := X * (hermite n) - (hermite n).derivative

@[simp] lemma hermite_succ (n : ℕ) : hermite (n+1) = X * (hermite n) - (hermite n).derivative :=
by rw hermite

lemma hermite_eq_iterate (n : ℕ) : hermite n = ((λ p, X*p - p.derivative)^[n] 1) :=
begin
  induction n with n ih,
  { refl },
  { rw [function.iterate_succ_apply', ← ih, hermite_succ] }
end

@[simp] lemma hermite_zero : hermite 0 = C 1 := rfl

@[simp] lemma hermite_one : hermite 1 = X :=
begin
  rw [hermite_succ, hermite_zero],
  simp only [map_one, mul_one, derivative_one, sub_zero]
end

/-! ### Lemmas about `polynomial.coeff` -/

section coeff

lemma coeff_hermite_succ_zero (n : ℕ) :
  coeff (hermite (n + 1)) 0 = -(coeff (hermite n) 1) := by simp [coeff_derivative]

lemma coeff_hermite_succ_succ (n k : ℕ) :
  coeff (hermite (n + 1)) (k + 1) = coeff (hermite n) k - (k + 2) * (coeff (hermite n) (k + 2)) :=
begin
  rw [hermite_succ, coeff_sub, coeff_X_mul, coeff_derivative, mul_comm],
  norm_cast
end

lemma coeff_hermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (hermite n) k = 0 :=
begin
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hnk,
  clear hnk,
  induction n with n ih generalizing k,
  { apply coeff_C },
  { have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring,
    rw [nat.succ_eq_add_one, coeff_hermite_succ_succ, add_right_comm, this, ih k, ih (k + 2),
      mul_zero, sub_zero] }
end

@[simp] lemma coeff_hermite_self (n : ℕ) : coeff (hermite n) n = 1 :=
begin
  induction n with n ih,
  { apply coeff_C },
  { rw [coeff_hermite_succ_succ, ih, coeff_hermite_of_lt, mul_zero, sub_zero],
    simp }
end

@[simp] lemma degree_hermite (n : ℕ) : (hermite n).degree = n :=
begin
  rw degree_eq_of_le_of_coeff_ne_zero,
  simp_rw [degree_le_iff_coeff_zero, with_bot.coe_lt_coe],
  { intro m,
    exact coeff_hermite_of_lt },
  { simp [coeff_hermite_self n] }
end

@[simp] lemma nat_degree_hermite {n : ℕ} : (hermite n).nat_degree = n :=
nat_degree_eq_of_degree_eq_some (degree_hermite n)

@[simp] lemma leading_coeff_hermite (n : ℕ) : (hermite n).leading_coeff = 1 :=
begin
  rw [← coeff_nat_degree, nat_degree_hermite, coeff_hermite_self],
end

lemma hermite_monic (n : ℕ) : (hermite n).monic := leading_coeff_hermite n

lemma coeff_hermite_of_odd_add {n k : ℕ} (hnk : odd (n + k)) : coeff (hermite n) k = 0 :=
begin
  induction n with n ih generalizing k,
  { rw zero_add at hnk,
    exact coeff_hermite_of_lt hnk.pos },
  { cases k,
    { rw nat.succ_add_eq_succ_add at hnk,
      rw [coeff_hermite_succ_zero, ih hnk, neg_zero] },
    { rw [coeff_hermite_succ_succ, ih, ih, mul_zero, sub_zero],
      { rwa [nat.succ_add_eq_succ_add] at hnk },
      { rw (by rw [nat.succ_add, nat.add_succ] : n.succ + k.succ = n + k + 2) at hnk,
        exact (nat.odd_add.mp hnk).mpr even_two }}}
end

end coeff
end polynomial

/-! ### Lemmas about `polynomial.hermite_gauss` -/

section gaussian

/-- The real Gaussian function -/
def gaussian : ℝ → ℝ := λ x, real.exp (-(x^2 / 2))

lemma inv_gaussian_eq : gaussian⁻¹ = λ x, real.exp (x^2 / 2) :=
by { ext, simp [gaussian, real.exp_neg] }

lemma inv_gaussian_mul_gaussian (x : ℝ) : gaussian⁻¹ x * gaussian x = 1 :=
by rw [inv_gaussian_eq, gaussian, ← real.exp_add, add_neg_self, real.exp_zero]

lemma deriv_gaussian (x : ℝ) : deriv gaussian x = -x * gaussian x :=
by simp [gaussian, mul_comm]

lemma deriv_inv_gaussian (x : ℝ) : deriv gaussian⁻¹ x = x * gaussian⁻¹ x :=
by simp [inv_gaussian_eq, mul_comm]

lemma cont_diff_gaussian : cont_diff ℝ ⊤ gaussian :=
((cont_diff_id.pow 2).div_const 2).neg.exp

lemma cont_diff.iterated_deriv :
∀ (n : ℕ) (f : ℝ → ℝ) (hf : cont_diff ℝ ⊤ f), cont_diff ℝ ⊤ (deriv^[n] f)
| 0     f hf := hf
| (n+1) f hf := cont_diff.iterated_deriv n (deriv f) (cont_diff_top_iff_deriv.mp hf).2

/-- The Gaussian form of `hermite n` -/
def hermite_gauss (n : ℕ) : ℝ → ℝ :=
λ x, (-1)^n * (gaussian⁻¹ x) * (deriv^[n] gaussian x)

lemma hermite_gauss_def (n : ℕ) :
hermite_gauss n = λ x, (-1)^n * (gaussian⁻¹ x) * (deriv^[n] gaussian x) := rfl

lemma hermite_gauss_succ (n : ℕ) : hermite_gauss (n+1)
= id * (hermite_gauss n) - deriv (hermite_gauss n):=
begin
  ext,
  simp only [hermite_gauss, function.iterate_succ', function.comp_app,
             id.def, pi.mul_apply, pi.sub_apply, pow_succ],
  rw [deriv_mul, deriv_const_mul, deriv_inv_gaussian],
  ring,
  { simp [inv_gaussian_eq] },
  { simp [inv_gaussian_eq] },
  { apply (cont_diff_top_iff_deriv.mp (cont_diff.iterated_deriv _ _ cont_diff_gaussian)).1 }
end

namespace polynomial

lemma hermite_eq_gauss (n : ℕ) :
(λ x, eval x (map (algebra_map ℤ ℝ) (hermite n))) =
λ x, (-1)^n * (gaussian⁻¹ x) * (deriv^[n] gaussian x) :=
begin
  induction n with n ih,
  { simp [-pi.inv_apply, inv_gaussian_mul_gaussian] },
  { rw [← hermite_gauss_def, hermite_gauss_succ, hermite_succ, hermite_gauss_def, ← ih],
    ext,
    simp },
end

lemma hermite_eq_gauss_apply :
  ∀ (n : ℕ) (x : ℝ), eval x (map (algebra_map ℤ ℝ) (hermite n)) =
    (-1)^n * (gaussian⁻¹ x) * (deriv^[n] gaussian x) :=
λ n x, congr_fun (hermite_eq_gauss n) x

end polynomial
end gaussian
