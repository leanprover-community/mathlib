/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import tactic
import data.nat.modeq

/-!
# IMO 1964 Q1

(a) Find all positive integers $n$ for which $2^n-1$ is divisible by $7$.

(b) Prove that there is no positive integer $n$ for which $2^n+1$ is divisible by $7$.

We define a predicate for the solutions in (a), and prove that it is the set of positive
integers which are a multiple of 3.
-/

/-!
## Intermediate lemmas
-/

open nat.modeq

lemma two_pow_three_mul_mod_seven (m : ℕ) : 2 ^ (3 * m) ≡ 1 [MOD 7] :=
begin
  rw pow_mul,
  have h : 8 ≡ 1 [MOD 7] := modeq_of_dvd (by {use -1, norm_num }),
  convert modeq_pow _ h,
  simp,
end

lemma two_pow_three_mul_add_one_mod_seven (m : ℕ) : 2 ^ (3 * m + 1) ≡ 2 [MOD 7] :=
begin
  rw pow_add,
  exact modeq_mul (two_pow_three_mul_mod_seven m) (show 2 ^ 1 ≡ 2 [MOD 7], by refl),
end

lemma two_pow_three_mul_add_two_mod_seven (m : ℕ) : 2 ^ (3 * m + 2) ≡ 4 [MOD 7] :=
begin
  rw pow_add,
  exact modeq_mul (two_pow_three_mul_mod_seven m) (show 2 ^ 2 ≡ 4 [MOD 7], by refl),
end

/-!
## The question
-/

def problem_predicate (n : ℕ) : Prop := 7 ∣ 2 ^ n - 1

lemma aux (n : ℕ) : problem_predicate n ↔ 2 ^ n ≡ 1 [MOD 7] :=
begin
  rw nat.modeq.comm,
  apply (modeq_iff_dvd' _).symm,
  apply nat.one_le_pow'
end

theorem imo1964_q1a (n : ℕ) (hn : 0 < n) : problem_predicate n ↔ 3 ∣ n :=
begin
  rw aux,
  split,
  { intro h,
    let t := n % 3,
    rw [(show n = t + 3 * (n / 3), from (nat.mod_add_div n 3).symm), add_comm] at h,
    have ht : t < 3 := nat.mod_lt _ dec_trivial,
    interval_cases t with hr; rw hr at h,
    { exact nat.dvd_of_mod_eq_zero hr },
    { exfalso,
      have nonsense := (two_pow_three_mul_add_one_mod_seven _).symm.trans h,
      rw modeq_iff_dvd at nonsense,
      norm_num at nonsense },
    { exfalso,
      have nonsense := (two_pow_three_mul_add_two_mod_seven _).symm.trans h,
      rw modeq_iff_dvd at nonsense,
      norm_num at nonsense } },
  { rintro ⟨m, rfl⟩,
    apply two_pow_three_mul_mod_seven }
end

theorem imo1964_q1b (n : ℕ) : ¬ (7 ∣ 2 ^ n + 1) :=
begin
  let t := n % 3,
  rw [← modeq_zero_iff, (show n = t + 3 * (n / 3), from (nat.mod_add_div n 3).symm), add_comm],
  have ht : t < 3 := nat.mod_lt _ dec_trivial,
  interval_cases t with hr; rw hr,
  { rw zero_add,
    intro h,
    have := h.symm.trans (modeq_add (nat.modeq.refl _) (two_pow_three_mul_mod_seven _)),
    rw modeq_iff_dvd at this,
    norm_num at this },
  { rw add_comm _ (3 * _),
    intro h,
    have := h.symm.trans (modeq_add (nat.modeq.refl _) (two_pow_three_mul_add_one_mod_seven _)),
    rw modeq_iff_dvd at this,
    norm_num at this },
  { rw add_comm _ (3 * _),
    intro h,
    have := h.symm.trans (modeq_add (nat.modeq.refl _) (two_pow_three_mul_add_two_mod_seven _)),
    rw modeq_iff_dvd at this,
    norm_num at this },
end
