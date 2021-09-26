/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.nat.choose.basic
import data.nat.factorial.cast

/-!
# Cast of binomial coefficients

This file allows calculating the binomial coefficient `a.choose b` as an element of a division ring
of characteristic `0`.
-/

open nat
open_locale nat

variables (K : Type*) [division_ring K] [char_zero K]

lemma cast_choose {a b : ℕ} (h : a ≤ b) :
  (b.choose a : K) = b! / (a! * (b - a)!) :=
begin
  have : ∀ {n : ℕ}, (n! : K) ≠ 0 := λ n, nat.cast_ne_zero.2 (factorial_ne_zero _),
  rw eq_div_iff_mul_eq (mul_ne_zero this this),
  rw_mod_cast [← mul_assoc, choose_mul_factorial_mul_factorial h],
end

lemma cast_add_choose {a b : ℕ} :
  ((a + b).choose a : K) = (a + b)! / (a! * b!) :=
by rw [cast_choose K (le_add_right le_rfl), nat.add_sub_cancel_left]

lemma cast_choose' (a b : ℕ) :
  (a.choose b : K) = (pochhammer K b).eval (a - (b - 1) : ℕ) / b.factorial :=
by rw [eq_div_iff_mul_eq (nat.cast_ne_zero.2 b.factorial_ne_zero : (b.factorial : K) ≠ 0),
  ←nat.cast_mul, mul_comm, ←nat.desc_factorial_eq_factorial_mul_choose, ←cast_desc_factorial]

lemma cast_choose_two (a : ℕ) :
  (a.choose 2 : K) = a * (a - 1) / 2 :=
begin
  rw [cast_choose', factorial_two, cast_two],
  cases a,
  { rw [nat.zero_sub, cast_zero, pochhammer_ne_zero_eval_zero _ (two_ne_zero), zero_mul] },
  { rw [succ_sub_succ, nat.sub_zero, cast_succ, add_sub_cancel, pochhammer_succ_right,
      pochhammer_one, polynomial.X_mul, polynomial.eval_mul_X, polynomial.eval_add,
      polynomial.eval_X, cast_one, polynomial.eval_one] }
end
