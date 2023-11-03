/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.integral.interval_integral
import measure_theory.integral.average

/-!
# Integral average over an interval

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we introduce notation `⨍_{a}^{b} x, f x` for the average `⨍ x in Ι a b, f x` of `f`
over the interval `Ι a b = set.Ioc (min a b) (max a b)` w.r.t. the Lebesgue measure, then prove
formulas for this average:

* `interval_average_eq`: `⨍_{a}^{b} x, f x = (b - a)⁻¹ • ∫_{a}^{b} x, f x`;
* `interval_average_eq_div`: `⨍_{a}^{b} x, f x = (∫_{a}^{b} x, f x) / (b - a)`.

We also prove that `⨍_{a}^{b} x, f x = ⨍_{b}^{a} x, f x`, see `interval_average_symm`.

## Notation

`⨍_{a}^{b} x, f x`: average of `f` over the interval `Ι a b` w.r.t. the Lebesgue measure.

-/

open measure_theory set topological_space
open_locale interval

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

notation `⨍_{` a `}^{` b `}` binders `, `
  r:(scoped:60 f, average (measure.restrict volume (Ι a b)) f) := r

lemma interval_average_symm (f : ℝ → E) (a b : ℝ) : ⨍_{a}^{b} x, f x = ⨍_{b}^{a} x, f x :=
by rw [set_average_eq, set_average_eq, uIoc_swap]

lemma interval_average_eq (f : ℝ → E) (a b : ℝ) : ⨍_{a}^{b} x, f x = (b - a)⁻¹ • ∫_{a}^{b} x, f x :=
begin
  cases le_or_lt a b with h h,
  { rw [set_average_eq, uIoc_of_le h, real.volume_Ioc, interval_integral.integral_of_le h,
      ennreal.to_real_of_real (sub_nonneg.2 h)] },
  { rw [set_average_eq, uIoc_of_lt h, real.volume_Ioc, interval_integral.integral_of_ge h.le,
     ennreal.to_real_of_real (sub_nonneg.2 h.le), smul_neg, ← neg_smul, ← inv_neg, neg_sub] }
end

lemma interval_average_eq_div (f : ℝ → ℝ) (a b : ℝ) :
  ⨍_{a}^{b} x, f x = (∫_{a}^{b} x, f x) / (b - a) :=
by rw [interval_average_eq, smul_eq_mul, div_eq_inv_mul]
