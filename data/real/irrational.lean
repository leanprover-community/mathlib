/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne.

Irrationality of real numbers.
-/
import data.real.basic data.nat.prime

open rat real

def irrational (x : ℝ) := ¬ ∃ q : ℚ, x = q

theorem irr_sqrt_two : irrational (sqrt 2)
| ⟨⟨n, d, h, c⟩, e⟩ := begin
  simp [num_denom', mk_eq_div] at e,
  have := mul_self_sqrt (le_of_lt two_pos),
  have d0 : (0:ℝ) < d := nat.cast_pos.2 h,
  rw [e, div_mul_div, div_eq_iff_mul_eq (ne_of_gt $ mul_pos d0 d0),
    ← int.cast_mul, ← int.nat_abs_mul_self] at this,
  generalize_hyp : n.nat_abs = k at c this,
  have E : 2 * (d * d) = k * k := (@nat.cast_inj ℝ _ _ _ _ _).1 (by simpa),
  have ke : 2 ∣ k,
  { refine (or_self _).1 (nat.prime_two.dvd_mul.1 _),
    rw ← E, apply dvd_mul_right },
  have de : 2 ∣ d,
  { have := mul_dvd_mul ke ke,
    refine (or_self _).1 (nat.prime_two.dvd_mul.1 _),
    rwa [← E, nat.mul_dvd_mul_iff_left (nat.succ_pos 1)] at this },
  exact nat.not_coprime_of_dvd_of_dvd (nat.lt_succ_self _) ke de c
end

variables {q : ℚ} {x : ℝ}

theorem irr_rat_add_of_irr : irrational x → irrational (q + x) :=
mt $ λ ⟨a, h⟩, ⟨-q + a, by rw [rat.cast_add, ← h, rat.cast_neg, neg_add_cancel_left]⟩

@[simp] theorem irr_add_rat_iff_irr : irrational (x + q) ↔ irrational x :=
⟨by simpa only [cast_neg, add_comm, add_neg_cancel_right] using @irr_rat_add_of_irr (-q) (x+q),
by rw add_comm; exact irr_rat_add_of_irr⟩

@[simp] theorem irr_rat_add_iff_irr : irrational (q + x) ↔ irrational x :=
by rw [add_comm, irr_add_rat_iff_irr]

theorem irr_mul_rat_iff_irr (Hqn0 : q ≠ 0) : irrational (x * ↑q) ↔ irrational x :=
⟨mt $ λ ⟨r, hr⟩, ⟨r * q, hr.symm ▸ (rat.cast_mul _ _).symm⟩,
mt $ λ ⟨r, hr⟩, ⟨r / q, by rw [cast_div, ← hr, mul_div_cancel]; rwa cast_ne_zero⟩⟩

theorem irr_of_irr_mul_self (Hix : irrational (x * x)) : irrational x :=
λ ⟨p, e⟩, Hix ⟨p * p, by rw [e, cast_mul]⟩

theorem irr_of_sqrt_padic_val_odd (m : ℤ) (Hnpl : m > 0) 
                                  (Hpn : ∃ p : ℕ, nat.prime p ∧ (padic_val p m) % 2 = 1) : 
        irrational (sqrt (↑m)) 
| ⟨⟨n, d, h, c⟩, e⟩ := begin
  cases Hpn with p Hpp, cases Hpp with Hp Hpv,
  simp [num_denom', mk_eq_div] at e,
  have Hnpl' : 0 < (m : ℝ) := int.cast_pos.2 Hnpl,
  have Hd0 : (0:ℝ) < d := nat.cast_pos.2 h,
  have := mul_self_sqrt (le_of_lt Hnpl'),
  rw [e, div_mul_div, div_eq_iff_mul_eq (ne_of_gt (mul_pos Hd0 Hd0)), ←int.cast_mul, ←int.cast_of_nat, ←int.cast_mul, ←int.cast_mul m (int.of_nat d * int.of_nat d), 
      int.cast_inj] at this,
  have d0' : int.of_nat d ≠ 0, rw [←int.coe_nat_eq, int.coe_nat_ne_zero], apply ne_of_gt h,
  have n0 : n ≠ 0, intro y0, rw [y0, int.cast_zero, zero_div, sqrt_eq_zero'] at e, revert e, apply not_le_of_gt Hnpl',
  have HPV : padic_val p (m * (int.of_nat d * int.of_nat d)) = padic_val p (n * n), rw this,
  rw [←padic_val.mul Hp (ne_of_gt Hnpl) (mul_ne_zero d0' d0'), ←padic_val.mul Hp d0' d0', ←padic_val.mul Hp n0 n0, ←mul_two, ←mul_two] at HPV,
  have HPV' : (padic_val p m + padic_val p (int.of_nat d) * 2) % 2 = (padic_val p n * 2) % 2, rw HPV,
  rw [nat.mul_mod_left, nat.add_mul_mod_self_right, Hpv] at HPV',
  revert HPV', exact dec_trivial,
end
