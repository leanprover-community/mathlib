/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import ring_theory.power_series
import data.nat.parity

/-!
# Definition of well-known power series

In this file we define the following power series:

* `power_series.inv_units_sub`: given `u : units R`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

* `power_series.sin`, `power_series.cos`, `power_series.exp` : power series for sin, cosine, and
  exponential functions.
-/

namespace power_series

section ring

variables {R S : Type*} [ring R] [ring S]

/-- The power series for `1 / (u - x)`. -/
def inv_units_sub (u : units R) : power_series R := mk $ λ n, 1 /ₚ u ^ (n + 1)

@[simp] lemma coeff_inv_units_sub (u : units R) (n : ℕ) :
  coeff R n (inv_units_sub u) = 1 /ₚ u ^ (n + 1) :=
coeff_mk _ _

@[simp] lemma constant_coeff_inv_units_sub (u : units R) :
  constant_coeff R (inv_units_sub u) = 1 /ₚ u :=
by rw [← coeff_zero_eq_constant_coeff_apply, coeff_inv_units_sub, zero_add, pow_one]

@[simp] lemma inv_units_sub_mul_X (u : units R) :
  inv_units_sub u * X = inv_units_sub u * C R u - 1 :=
begin
  ext (_|n),
  { simp },
  { simp [n.succ_ne_zero, pow_succ] }
end

@[simp] lemma inv_units_sub_mul_sub (u : units R) : inv_units_sub u * (C R u - X) = 1 :=
by simp [mul_sub, sub_sub_cancel]

lemma map_inv_units_sub (f : R →+* S) (u : units R) :
  map f (inv_units_sub u) = inv_units_sub (units.map (f : R →* S) u) :=
by { ext, simp [← monoid_hom.map_pow] }

end ring

section field

variables (k k' : Type*) [field k] [field k']

open_locale nat

/-- Power series for the exponential function at zero. -/
def exp : power_series k := mk $ λ n, 1 / n!

/-- Power series for the sine function at zero. -/
def sin : power_series k :=
mk $ λ n, if even n then 0 else (-1) ^ (n / 2) / n!

/-- Power series for the cosine function at zero. -/
def cos : power_series k :=
mk $ λ n, if even n then (-1) ^ (n / 2) / n! else 0

variables {k k'} (n : ℕ) (f : k →+* k')

@[simp] lemma coeff_exp : coeff k n (exp k) = 1 / n! := coeff_mk _ _

@[simp] lemma map_exp : map f (exp k) = exp k' := by { ext, simp [f.map_inv] }

@[simp] lemma map_sin : map f (sin k) = sin k' := by { ext, simp [sin, apply_ite f, f.map_div] }

@[simp] lemma map_cos : map f (cos k) = cos k' := by { ext, simp [cos, apply_ite f, f.map_div] }

end field

end power_series
