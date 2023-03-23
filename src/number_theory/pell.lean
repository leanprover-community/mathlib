/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/

import tactic.qify
import data.zmod.basic
import number_theory.diophantine_approximation
import number_theory.zsqrtd.basic

/-!
# Pell's Equation

We prove the following

**Theorem.** Let $d$ be a positive integer that is not a square. Then the equation
$x^2 - d y^2 = 1$ has a nontrivial (i.e., with $y \ne 0$) solution in integers.

See `pell.exists_of_not_is_square`.

This is the beginning of a development that aims at providing all of the essential theory
of Pell's Equation for general $d$ (as opposed to the contents of `number_theory.pell_matiyasevic`,
which is specific to the case $d = a^2 - 1$ for some $a > 1$).

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
   (Section 17.5)][IrelandRosen1990]

## Tags

Pell's equation

## TODO

* Provide the structure theory of the solution set to Pell's equation
  and furthermore also for `x ^ 2 - d * y ^ 2 = -1` and further generalizations.
* Connect solutions to the continued fraction expansion of `√d`.
-/

namespace pell

/-!
### Group structure of the solution set

We define a structure of a commutative multiplicative group with distributive negation
on the set of all solutions to the Pell equation `x^2 - d*y^2 = 1`.

The type of such solutions is `pell.solution₁ d`. It corresponds to a pair of integers `x` and `y`
and a proof that `(x, y)` is indeed a solution.

The multiplication is given by `(x, y) * (x', y') = (x*y' + d*y*y', x*y' + y*x')`.
This is obtained by mapping `(x, y)` to `x + y*√d` and multiplying the results.
In fact, we define `pell.solution₁ d` to be `↥(unitary (ℤ√d))` and transport
the "commutative group with distributive negation" structure from `↥(unitary (ℤ√d))`.

We then set up an API for `pell.solution₁ d`.
-/

open zsqrtd

/-- An element of `ℤ√d` has norm one (i.e., `a.re^2 - d*a.im^2 = 1`) if and only if
it is contained in the submonoid of unitary elements.

TODO: merge this result with `pell.is_pell_iff_mem_unitary`. -/
lemma is_pell_solution_iff_mem_unitary {d : ℤ} {a : ℤ√d} :
  a.re ^ 2 - d * a.im ^ 2 = 1 ↔ a ∈ unitary ℤ√d :=
by rw [← norm_eq_one_iff_mem_unitary, norm_def, sq, sq, ← mul_assoc]

-- We use `solution₁ d` to allow for a more general structure `solution d m` that
-- encodes solutions to `x^2 - d*y^2 = m` to be added later.

/-- `pell.solution₁ d` is the type of solutions to the Pell equation `x^2 - d*y^2 = 1`.
We define this in terms of elements of `ℤ√d` of norm one.
-/
@[derive [comm_group, has_distrib_neg, inhabited]]
def solution₁ (d : ℤ) : Type := ↥(unitary ℤ√d)

namespace solution₁

variables {d : ℤ}

instance : has_coe (solution₁ d) ℤ√d := { coe := subtype.val }

/-- The `x` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def x (a : solution₁ d) : ℤ := (a : ℤ√d).re

/-- The `y` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def y (a : solution₁ d) : ℤ := (a : ℤ√d).im

/-- The proof that `a` is a solution to the Pell equation `x^2 - d*y^2 = 1` -/
lemma prop (a : solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1 :=
is_pell_solution_iff_mem_unitary.mpr a.property

/-- An alternative form of the equation, suitable for rewriting `x^2`. -/
lemma prop_x (a : solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2 := by {rw ← a.prop, ring}

/-- An alternative form of the equation, suitable for rewriting `d * y^2`. -/
lemma prop_y (a : solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1 := by {rw ← a.prop, ring}

/-- Two solutions are equal if their `x` and `y` components are equal. -/
@[ext]
lemma ext {a b : solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
subtype.ext $ ext.mpr ⟨hx, hy⟩

/-- Construct a solution from `x`, `y` and a proof that the equation is satisfied. -/
def mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : solution₁ d :=
{ val := ⟨x, y⟩,
  property := is_pell_solution_iff_mem_unitary.mp prop }

@[simp]
lemma x_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).x = x := rfl

@[simp]
lemma y_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).y = y := rfl

@[simp]
lemma coe_mk  (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (↑(mk x y prop) : ℤ√d) = ⟨x,y⟩ :=
zsqrtd.ext.mpr ⟨x_mk x y prop, y_mk x y prop⟩

@[simp]
lemma x_one : (1 : solution₁ d).x = 1 := rfl

@[simp]
lemma y_one : (1 : solution₁ d).y = 0 := rfl

@[simp]
lemma x_mul (a b : solution₁ d) : (a * b).x = a.x * b.x + d * (a.y * b.y) :=
by {rw ← mul_assoc, refl}

@[simp]
lemma y_mul (a b : solution₁ d) : (a * b).y = a.x * b.y + a.y * b.x := rfl

@[simp]
lemma x_inv (a : solution₁ d) : a⁻¹.x = a.x := rfl

@[simp]
lemma y_inv (a : solution₁ d) : a⁻¹.y = -a.y := rfl

@[simp]
lemma x_neg (a : solution₁ d) : (-a).x = -a.x := rfl

@[simp]
lemma y_neg (a : solution₁ d) : (-a).y = -a.y := rfl

/-- A solution has `x ≠ 0`. -/
lemma x_ne_zero (h₀ : 0 < d) (a : solution₁ d) : a.x ≠ 0 :=
begin
  intro hx,
  have h : 0 ≤ d * a.y ^ 2 := mul_nonneg h₀.le (sq_nonneg _),
  rw [a.prop_y, hx, sq, zero_mul, zero_sub] at h,
  exact not_le.mpr (neg_one_lt_zero : (-1 : ℤ) < 0) h,
end

/-- A solution with `x > 1` must have `y ≠ 0`. -/
lemma y_ne_zero_of_one_lt_x {a : solution₁ d} (ha : 1 < a.x) : a.y ≠ 0 :=
begin
  intro hy,
  have prop := a.prop,
  rw [hy, sq (0 : ℤ), zero_mul, mul_zero, sub_zero] at prop,
  exact lt_irrefl _ (((one_lt_sq_iff $ zero_le_one.trans ha.le).mpr ha).trans_eq prop),
end

/-- A solution with `x = 1` is trivial. -/
lemma eq_one_of_x_eq_one (h₀ : 0 < d) {a : solution₁ d} (ha : a.x = 1) : a = 1 :=
begin
  have prop := a.prop_y,
  rw [ha, one_pow, sub_self, mul_eq_zero, or_iff_right h₀.ne', sq_eq_zero_iff] at prop,
  exact ext ha prop,
end

/-- A solution is `1` or `-1` if and only if `y = 0`. -/
lemma eq_one_or_neg_one_iff_y_eq_zero {a : solution₁ d} : a = 1 ∨ a = -1 ↔ a.y = 0 :=
begin
  refine ⟨λ H, H.elim (λ h, by simp [h]) (λ h, by simp [h]), λ H, _⟩,
  have prop := a.prop,
  rw [H, sq (0 : ℤ), mul_zero, mul_zero, sub_zero, sq_eq_one_iff] at prop,
  exact prop.imp (λ h, ext h H) (λ h, ext h H),
end

/-- The set of solutions with `x > 0` is closed under multiplication. -/
lemma x_mul_pos_of_x_pos (h₀ : 0 < d) {a b : solution₁ d} (ha : 0 < a.x) (hb : 0 < b.x) :
  0 < (a * b).x :=
begin
  simp only [x_mul],
  refine neg_lt_iff_pos_add'.mp (abs_lt.mp _).1,
  rw [← abs_of_pos ha, ← abs_of_pos hb, ← abs_mul, ← sq_lt_sq, mul_pow a.x, a.prop_x, b.prop_x,
      ← sub_pos],
  ring_nf,
  positivity,
end

/-- The set of solutions with `x` and `y` positive is closed under multiplication. -/
lemma y_mul_pos_of_x_pos_of_y_pos {a b : solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y)
  (hbx : 0 < b.x) (hby : 0 < b.y) :
  0 < (a * b).y :=
begin
  simp only [y_mul],
  positivity,
end

/-- If `(x, y)` is a solution with `x` and `y` positive, then all its powers with positive
natural exponents have positive `x` and `y`. -/
lemma x_npow_pos_of_x_pos_of_y_pos (h₀ : 0 < d) {a : solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y)
  (n : ℕ) :
  0 < (a ^ n.succ).x ∧ 0 < (a ^ n.succ).y :=
begin
  induction n with n ih,
  { simp only [hax, hay, pow_one, and_self], },
  { rw [pow_succ],
    exact ⟨x_mul_pos_of_x_pos h₀ hax ih.1, y_mul_pos_of_x_pos_of_y_pos hax hay ih.1 ih.2⟩, }
end

/-- If `(x, y)` is a solution with `x` positive, then all its powers have positive `x`. -/
lemma x_zpow_pos_of_x_pos_of_y_pos (h₀ : 0 < d) {a : solution₁ d} (hax : 0 < a.x)
  (n : ℤ) :
  0 < (a ^ n).x :=
begin
  have H : ∀ m : ℤ, 0 < m → 0 < (a ^ m).x,
  { change ∀ m : ℤ, 1 ≤ m → _,
    refine λ m, int.le_induction (by simp only [hax, zpow_one]) (λ m hm ih, _) m,
    rw zpow_add_one,
    exact x_mul_pos_of_x_pos h₀ ih hax, },
  rcases lt_trichotomy 0 n with hpos | rfl | hneg,
  { exact H n hpos, },
  { simp only [zpow_zero, x_one, zero_lt_one], },
  { rw [← neg_neg n, zpow_neg, x_inv],
    exact H (-n) (lt_neg.mp hneg), }
end

/-- If `(x, y)` is a solution with `x` and `y` positive, then the `y` component of its powers
have the same sign as the exponent. -/
lemma sign_y_zpow_eq_sign_of_x_pos_of_y_pos (h₀ : 0 < d) {a : solution₁ d} (hax : 0 < a.x)
  (hay : 0 < a.y) (n : ℤ) :
  (a ^ n).y.sign = n.sign :=
begin
  have H : ∀ m : ℤ, 0 < m → 0 < (a ^ m).y,
  { change ∀ m : ℤ, 1 ≤ m → _,
    refine λ m, int.le_induction (by simp only [hay, zpow_one]) (λ m hm ih, _) m,
    rw zpow_add_one,
    exact y_mul_pos_of_x_pos_of_y_pos (x_zpow_pos_of_x_pos_of_y_pos h₀ hax m) ih hax hay, },
  rcases lt_trichotomy 0 n with hpos | rfl | hneg,
  { rw [(int.sign_eq_one_iff_pos n).mpr hpos, int.sign_eq_one_iff_pos],
    exact H n hpos, },
  { rw [int.sign_zero, int.sign_eq_zero_iff_zero, zpow_zero, y_one], },
  { rw [(int.sign_eq_neg_one_iff_neg n).mpr hneg, int.sign_eq_neg_one_iff_neg, ← neg_neg n,
        zpow_neg, y_inv, neg_lt, neg_zero],
    exact H (-n) (lt_neg.mp hneg), }
end

/-- If `a` is any solution, then one of `a`, `a⁻¹`, `-a`, `-a⁻¹` has
positive `x` and nonnegative `y`. -/
lemma exists_pos_variant (h₀ : 0 < d) (a : solution₁ d) :
  ∃ b : solution₁ d, 0 < b.x ∧ 0 ≤ b.y ∧ a ∈ ({b, b⁻¹, -b, -b⁻¹} : set (solution₁ d)) :=
begin
  refine ⟨mk (|a.x|) (|a.y|) (by simp [a.prop]), abs_pos.mpr (a.x_ne_zero h₀), abs_nonneg a.y, _⟩,
  cases le_or_lt 0 a.x with hax hax; cases le_or_lt 0 a.y with hay hay,
  { exact or.inl (ext (abs_of_nonneg hax).symm (abs_of_nonneg hay).symm), },
  { exact or.inr (or.inl $ ext (by simp [abs_of_nonneg hax]) (by simp [abs_of_neg hay])), },
  { exact or.inr (or.inr $ or.inr $ ext (by simp [abs_of_neg hax])
                                        (by simp [abs_of_nonneg hay])), },
  { exact or.inr (or.inr $ or.inl $ ext (by simp [abs_of_neg hax]) (by simp [abs_of_neg hay])),}
end

end solution₁

section existence

/-!
### Existence of nontrivial solutions
-/

variables {d : ℤ}

open set real

/-- If `d` is a positive integer that is not a square, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem exists_of_not_is_square (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 :=
begin
  let ξ : ℝ := sqrt d,
  have hξ : irrational ξ,
  { refine irrational_nrt_of_notint_nrt 2 d (sq_sqrt $ int.cast_nonneg.mpr h₀.le) _ two_pos,
    rintro ⟨x, hx⟩,
    refine hd ⟨x, @int.cast_injective ℝ _ _ d (x * x) _⟩,
    rw [← sq_sqrt $ int.cast_nonneg.mpr h₀.le, int.cast_mul, ← hx, sq], },
  obtain ⟨M, hM₁⟩ := exists_int_gt (2 * |ξ| + 1),
  have hM : {q : ℚ | |q.1 ^ 2 - d * q.2 ^ 2| < M}.infinite,
  { refine infinite.mono (λ q h, _) (infinite_rat_abs_sub_lt_one_div_denom_sq_of_irrational hξ),
    have h0 : 0 < (q.2 : ℝ) ^ 2 := pow_pos (nat.cast_pos.mpr q.pos) 2,
    have h1 : (q.num : ℝ) / (q.denom : ℝ) = q := by exact_mod_cast q.num_div_denom,
    rw [mem_set_of, abs_sub_comm, ← @int.cast_lt ℝ, ← div_lt_div_right (abs_pos_of_pos h0)],
    push_cast,
    rw [← abs_div, abs_sq, sub_div, mul_div_cancel _ h0.ne',
        ← div_pow, h1, ← sq_sqrt (int.cast_pos.mpr h₀).le, sq_sub_sq, abs_mul, ← mul_one_div],
    refine mul_lt_mul'' (((abs_add ξ q).trans _).trans_lt hM₁) h (abs_nonneg _) (abs_nonneg _),
    rw [two_mul, add_assoc, add_le_add_iff_left, ← sub_le_iff_le_add'],
    rw [mem_set_of, abs_sub_comm] at h,
    refine (abs_sub_abs_le_abs_sub (q : ℝ) ξ).trans (h.le.trans _),
    rw [div_le_one h0, one_le_sq_iff_one_le_abs, nat.abs_cast, nat.one_le_cast],
    exact q.pos, },
  obtain ⟨m, hm⟩ : ∃ m : ℤ, {q : ℚ | q.1 ^ 2 - d * q.2 ^ 2 = m}.infinite,
  { contrapose! hM,
    simp only [not_infinite] at hM ⊢,
    refine (congr_arg _ (ext (λ x, _))).mp (finite.bUnion (finite_Ioo (-M) M) (λ m _, hM m)),
    simp only [abs_lt, mem_set_of_eq, mem_Ioo, mem_Union, exists_prop, exists_eq_right'], },
  have hm₀ : m ≠ 0,
  { rintro rfl,
    obtain ⟨q, hq⟩ := hm.nonempty,
    rw [mem_set_of, sub_eq_zero, mul_comm] at hq,
    obtain ⟨a, ha⟩ := (int.pow_dvd_pow_iff two_pos).mp ⟨d, hq⟩,
    rw [ha, mul_pow, mul_right_inj' (pow_pos (int.coe_nat_pos.mpr q.pos) 2).ne'] at hq,
    exact hd ⟨a, sq a ▸ hq.symm⟩, },
  haveI := ne_zero_iff.mpr (int.nat_abs_ne_zero.mpr hm₀),
  let f : ℚ → (zmod m.nat_abs) × (zmod m.nat_abs) := λ q, (q.1, q.2),
  obtain ⟨q₁, h₁ : q₁.1 ^ 2 - d * q₁.2 ^ 2 = m, q₂, h₂ : q₂.1 ^ 2 - d * q₂.2 ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_maps_to (maps_to_univ f _) finite_univ,
  obtain ⟨hq1 : (q₁.1 : zmod m.nat_abs) = q₂.1, hq2 : (q₁.2 : zmod m.nat_abs) = q₂.2⟩ :=
    prod.ext_iff.mp hqf,
  have hd₁ : m ∣ q₁.1 * q₂.1 - d * (q₁.2 * q₂.2),
  { rw [← int.nat_abs_dvd, ← zmod.int_coe_zmod_eq_zero_iff_dvd],
    push_cast,
    rw [hq1, hq2, ← sq, ← sq],
    norm_cast,
    rw [zmod.int_coe_zmod_eq_zero_iff_dvd, int.nat_abs_dvd, nat.cast_pow, ← h₂], },
  have hd₂ : m ∣ q₁.1 * q₂.2 - q₂.1 * q₁.2,
  { rw [← int.nat_abs_dvd, ← zmod.int_coe_eq_int_coe_iff_dvd_sub],
    push_cast,
    rw [hq1, hq2], },
  replace hm₀ : (m : ℚ) ≠ 0 := int.cast_ne_zero.mpr hm₀,
  refine ⟨(q₁.1 * q₂.1 - d * (q₁.2 * q₂.2)) / m, (q₁.1 * q₂.2 - q₂.1 * q₁.2) / m, _, _⟩,
  { qify [hd₁, hd₂],
    field_simp [hm₀],
    norm_cast,
    conv_rhs {congr, rw sq, congr, rw ← h₁, skip, rw ← h₂},
    push_cast,
    ring, },
  { qify [hd₂],
    refine div_ne_zero_iff.mpr ⟨_, hm₀⟩,
    exact_mod_cast mt sub_eq_zero.mp (mt rat.eq_iff_mul_eq_mul.mpr hne), },
end

/-- If `d` is a positive integer, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1` if and only if `d` is not a square. -/
theorem exists_iff_not_is_square (h₀ : 0 < d) :
  (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0) ↔ ¬ is_square d :=
begin
  refine ⟨_, exists_of_not_is_square h₀⟩,
  rintros ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩,
  rw [← sq, ← mul_pow, sq_sub_sq] at hxy,
  simpa [mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using int.eq_of_mul_eq_one hxy,
end

namespace solution₁

/-- If `d` is a positive integer that is not a square, then there exists a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem exists_nontrivial_of_not_is_square (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃ a : solution₁ d, a ≠ 1 ∧ a ≠ -1 :=
begin
  obtain ⟨x, y, prop, hy⟩ := exists_of_not_is_square h₀ hd,
  refine ⟨mk x y prop, λ H, _, λ H, _⟩; apply_fun solution₁.y at H; simpa [hy] using H,
end

/-- If `d` is a positive integer that is not a square, then there exists a solution
to the Pell equation `x^2 - d*y^2 = 1` with `x > 1` and `y > 0`. -/
lemma exists_pos_of_not_is_square (h₀ : 0 < d) (hd : ¬ is_square d) :
  ∃ a : solution₁ d, 1 < a.x ∧ 0 < a.y :=
begin
  obtain ⟨a, ha₁, ha₂⟩ := exists_nontrivial_of_not_is_square h₀ hd,
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_pos_variant h₀ a,
  refine ⟨b, lt_iff_le_and_ne.mpr ⟨hb₁, λ hf, _⟩, lt_iff_le_and_ne.mpr ⟨hb₂, λ hf, _⟩⟩,
  { have := eq_one_of_x_eq_one h₀ hf.symm,
    rw [eq_one_of_x_eq_one h₀ hf.symm, inv_one] at hb₃,
    simpa only [ha₁, ha₂, or_self, mem_insert_iff, mem_singleton_iff] using hb₃, },
  { cases eq_one_or_neg_one_iff_y_eq_zero.mpr hf.symm with h h; rw h at hb₃,
    { simpa only [ha₁, ha₂, inv_one, or_self, mem_insert_iff, mem_singleton_iff] using hb₃, },
    { simpa only [ha₁, ha₂, inv_neg', inv_one, neg_neg, or_self, mem_insert_iff, mem_singleton_iff]
        using hb₃, } }
end

end solution₁

end existence

end pell
