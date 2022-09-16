/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann
-/
import algebra.order.floor
import tactic.field_simp

/-!
# Floor Function for Rational Numbers

## Summary

We define the `floor` function and the `floor_ring` instance on `ℚ`. Some technical lemmas relating
`floor` to integer division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/

open int

namespace rat
variables {α : Type*} [linear_ordered_field α] [floor_ring α]

/-- `floor q` is the largest integer `z` such that `z ≤ q` -/
protected def floor : ℚ → ℤ
| ⟨n, d, h, c⟩ := n / d

protected theorem le_floor {z : ℤ} : ∀ {r : ℚ}, z ≤ rat.floor r ↔ (z : ℚ) ≤ r
| ⟨n, d, h, c⟩ := begin
  simp [rat.floor],
  rw [num_denom'],
  have h' := int.coe_nat_lt.2 h,
  conv { to_rhs,
    rw [coe_int_eq_mk, rat.le_def zero_lt_one h', mul_one] },
  exact int.le_div_iff_mul_le h'
end

instance : floor_ring ℚ :=
floor_ring.of_floor ℚ rat.floor $ λ a z, rat.le_floor.symm

protected lemma floor_def {q : ℚ} : ⌊q⌋ = q.num / q.denom := by { cases q, refl }

lemma floor_int_div_nat_eq_div {n : ℤ} {d : ℕ} : ⌊(↑n : ℚ) / (↑d : ℚ)⌋ = n / (↑d : ℤ) :=
begin
  rw [rat.floor_def],
  obtain rfl | hd := @eq_zero_or_pos _ _ d,
  { simp },
  set q := (n : ℚ) / d with q_eq,
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : ∃ c, n = c * q.num ∧ (d : ℤ) = c * q.denom, by
  { rw q_eq,
    exact_mod_cast @rat.exists_eq_mul_div_num_and_eq_mul_div_denom n d (by exact_mod_cast hd.ne') },
  rw [n_eq_c_mul_num, d_eq_c_mul_denom],
  refine (int.mul_div_mul_of_pos _ _ $ pos_of_mul_pos_left _ $ int.coe_nat_nonneg q.denom).symm,
  rwa [←d_eq_c_mul_denom, int.coe_nat_pos],
end

@[simp, norm_cast] lemma floor_cast (x : ℚ) : ⌊(x : α)⌋ = ⌊x⌋ :=
floor_eq_iff.2 (by exact_mod_cast floor_eq_iff.1 (eq.refl ⌊x⌋))

@[simp, norm_cast] lemma ceil_cast (x : ℚ) : ⌈(x : α)⌉ = ⌈x⌉ :=
by rw [←neg_inj, ←floor_neg, ←floor_neg, ← rat.cast_neg, rat.floor_cast]

@[simp, norm_cast] lemma round_cast (x : ℚ) : round (x : α) = round x :=
have ((x + 1 / 2 : ℚ) : α) = x + 1 / 2, by simp,
by rw [round_eq, round_eq, ← this, floor_cast]

@[simp, norm_cast] lemma cast_fract (x : ℚ) : (↑(fract x) : α) = fract x :=
by simp only [fract, cast_sub, cast_coe_int, floor_cast]

end rat


lemma int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} : n % d = n - d * ⌊(n : ℚ) / d⌋ :=
by rw [(eq_sub_of_add_eq $ int.mod_add_div n d), rat.floor_int_div_nat_eq_div]

lemma nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : ℕ} (n_coprime_d : n.coprime d) :
  ((n : ℤ) - d * ⌊(n : ℚ)/ d⌋).nat_abs.coprime d :=
begin
  have : (n : ℤ) % d = n - d * ⌊(n : ℚ)/ d⌋, from int.mod_nat_eq_sub_mul_floor_rat_div,
  rw ←this,
  have : d.coprime n, from n_coprime_d.symm,
  rwa [nat.coprime, nat.gcd_rec] at this
end


namespace rat

lemma num_lt_succ_floor_mul_denom (q : ℚ) : q.num < (⌊q⌋ + 1) * q.denom :=
begin
  suffices : (q.num : ℚ) < (⌊q⌋ + 1) * q.denom, by exact_mod_cast this,
  suffices : (q.num : ℚ) < (q - fract q + 1) * q.denom, by
  { have : (⌊q⌋ : ℚ) = q - fract q, from (eq_sub_of_add_eq $ floor_add_fract q),
    rwa this },
  suffices : (q.num : ℚ) < q.num + (1 - fract q) * q.denom, by
  { have : (q - fract q + 1) * q.denom = q.num + (1 - fract q) * q.denom, calc
      (q - fract q + 1) * q.denom = (q + (1 - fract q)) * q.denom            : by ring
                              ... = q * q.denom + (1 - fract q) * q.denom    : by rw add_mul
                              ... = q.num + (1 - fract q) * q.denom : by simp,
    rwa this },
  suffices : 0 < (1 - fract q) * q.denom, by { rw ←sub_lt_iff_lt_add', simpa },
  have : 0 < 1 - fract q, by
  { have : fract q < 1, from fract_lt_one q,
    have : 0 + fract q < 1, by simp [this],
    rwa lt_sub_iff_add_lt },
  exact mul_pos this (by exact_mod_cast q.pos)
end

lemma fract_inv_num_lt_num_of_pos {q : ℚ} (q_pos : 0 < q): (fract q⁻¹).num < q.num :=
begin
  -- we know that the numerator must be positive
  have q_num_pos : 0 < q.num, from rat.num_pos_iff_pos.elim_right q_pos,
  -- we will work with the absolute value of the numerator, which is equal to the numerator
  have q_num_abs_eq_q_num : (q.num.nat_abs : ℤ) = q.num, from
    (int.nat_abs_of_nonneg q_num_pos.le),
  set q_inv := (q.denom : ℚ) / q.num with q_inv_def,
  have q_inv_eq : q⁻¹ = q_inv, from rat.inv_def',
  suffices : (q_inv - ⌊q_inv⌋).num < q.num, by rwa q_inv_eq,
  suffices : ((q.denom - q.num * ⌊q_inv⌋ : ℚ) / q.num).num < q.num, by
    field_simp [this, (ne_of_gt q_num_pos)],
  suffices : (q.denom : ℤ) - q.num * ⌊q_inv⌋ < q.num, by
  { -- use that `q.num` and `q.denom` are coprime to show that the numerator stays unreduced
    have : ((q.denom - q.num * ⌊q_inv⌋ : ℚ) / q.num).num = q.denom - q.num * ⌊q_inv⌋, by
    { suffices : ((q.denom : ℤ) - q.num * ⌊q_inv⌋).nat_abs.coprime q.num.nat_abs, by
        exact_mod_cast (rat.num_div_eq_of_coprime q_num_pos this),
      have : (q.num.nat_abs : ℚ) = (q.num : ℚ), by exact_mod_cast q_num_abs_eq_q_num,
      have tmp := nat.coprime_sub_mul_floor_rat_div_of_coprime q.cop.symm,
      simpa only [this, q_num_abs_eq_q_num] using tmp },
    rwa this },
  -- to show the claim, start with the following inequality
  have q_inv_num_denom_ineq : q⁻¹.num - ⌊q⁻¹⌋ * q⁻¹.denom < q⁻¹.denom, by
  { have : q⁻¹.num < (⌊q⁻¹⌋ + 1) * q⁻¹.denom, from rat.num_lt_succ_floor_mul_denom q⁻¹,
    have : q⁻¹.num < ⌊q⁻¹⌋ * q⁻¹.denom + q⁻¹.denom, by rwa [right_distrib, one_mul] at this,
    rwa [←sub_lt_iff_lt_add'] at this },
  -- use that `q.num` and `q.denom` are coprime to show that q_inv is the unreduced reciprocal
  -- of `q`
  have : q_inv.num = q.denom ∧ q_inv.denom = q.num.nat_abs, by
  { have coprime_q_denom_q_num : q.denom.coprime q.num.nat_abs, from q.cop.symm,
    have : int.nat_abs q.denom = q.denom, by simp,
    rw ←this at coprime_q_denom_q_num,
    rw q_inv_def,
    split,
    { exact_mod_cast (rat.num_div_eq_of_coprime q_num_pos coprime_q_denom_q_num) },
    { suffices : (((q.denom : ℚ) / q.num).denom : ℤ) = q.num.nat_abs, by exact_mod_cast this,
      rw q_num_abs_eq_q_num,
      exact_mod_cast (rat.denom_div_eq_of_coprime q_num_pos coprime_q_denom_q_num) } },
  rwa [q_inv_eq, this.left, this.right, q_num_abs_eq_q_num, mul_comm] at q_inv_num_denom_ineq
end

namespace norm_num
open tactic

/-- A norm_num extension for `int.floor`, `int.ceil`, and `int.fract`. -/
@[norm_num] meta def eval_floor_ceil : expr → tactic (expr × expr)
| e@`(@int.floor %%R %%inst_1 %%inst_2 %%x) := do
  q ← x.to_rat,
  let z := int.floor q,
  let ze := `(z),
  t ← to_expr ``(%%e = %%ze),
  ((), p) ← tactic.solve_aux t (do
    tactic.mk_mapp `int.floor_eq_iff [some R, some inst_1, some inst_2] >>= tactic.rewrite_target,
    tactic.interactive.norm_num [] (interactive.loc.ns [none])),
  p ← instantiate_mvars p,
  pure (ze, p)
| e@`(@int.ceil %%R %%inst_1 %%inst_2 %%x) := do
  q ← x.to_rat,
  let z := int.ceil q,
  let ze := `(z),
  t ← to_expr ``(%%e = %%ze),
  ((), p) ← tactic.solve_aux t (do
    tactic.mk_mapp `int.ceil_eq_iff [some R, some inst_1, some inst_2] >>= tactic.rewrite_target,
    `[norm_num]),
  p ← instantiate_mvars p,
  pure (ze, p)
| e@`(@int.fract %%R %%inst_1 %%inst_2 %%x) := do
  q ← x.to_rat,
  ic ← mk_instance_cache R,
  let q' := int.fract q,
  (ic, q'e) ← ic.of_rat q',
  let z := int.floor q,
  let ze := `(z),
  t ← to_expr ``(%%e = %%q'e),
  ((), p) ← tactic.solve_aux t (do
    `[rw int.fract_eq_iff; norm_num],
    tactic.refine ``(⟨%%ze, _⟩),
    `[norm_num]),
  p ← instantiate_mvars p,
  pure (q'e, p)
| _ := failed

end norm_num
end rat
