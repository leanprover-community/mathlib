/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.nat.prime
import data.rat.defs
import order.well_founded
import tactic.linarith
import tactic.wlog

/-!
# IMO 1988 Q6 and constant descent Vieta jumping

Question 6 of IMO1988 is somewhat (in)famous. Several expert problem solvers
could not tackle the question within the given time limit.
The problem lead to the introduction of a new proof technique,
so called “Vieta jumping”.

In this file we formalise constant descent Vieta jumping,
and apply this to prove Q6 of IMO1988.
To illustrate the technique, we also prove a similar result.
-/

-- open_locale classical

local attribute [instance] classical.prop_decidable
local attribute [simp] sq

/-- Constant descent Vieta jumping.

This proof technique allows one to prove an arbitrary proposition `claim`,
by running a descent argument on a hyperbola `H` in the first quadrant of the plane,
under the following conditions:

* `h₀`     : There exists an integral point `(x,y)` on the hyperbola `H`.
* `H_symm` : The hyperbola has a symmetry along the diagonal in the plane.
* `H_zero` : If an integral point `(x,0)` lies on the hyperbola `H`, then `claim` is true.
* `H_diag` : If an integral point `(x,x)` lies on the hyperbola `H`, then `claim` is true.
* `H_desc` : If `(x,y)` is an integral point on the hyperbola `H`,
with `x < y` then there exists a “smaller” point on `H`: a point `(x',y')` with `x' < y' ≤ x`.

For reasons of usability, the hyperbola `H` is implemented as an arbitrary predicate.
(In question 6 of IMO1988, where this proof technique was first developped,
the predicate `claim` would be `∃ (d : ℕ), d ^ 2 = k` for some natural number `k`,
and the predicate `H` would be `λ a b, a * a + b * b = (a * b + 1) * k`.)

To ensure that the predicate `H` actually describes a hyperbola,
the user must provide arguments `B` and `C` that are used as coefficients for a quadratic equation.
Finally, `H_quad` is the proof obligation that the quadratic equation
  `(y:ℤ) * y - B x * y + C x = 0`
describes the same hyperbola as the predicate `H`.

For extra flexibility, one must provide a predicate `base` on the integral points in the plane.
In the descent step `H_desc` this will give the user the additional assumption that
the point `(x,y)` does not lie in this base locus.
The user must provide a proof that the proposition `claim` is true
if there exists an integral point `(x,y)` on the hyperbola `H` that lies in the base locus.
If such a base locus is not necessary, once can simply let it be `λ x y, false`.
-/
lemma constant_descent_vieta_jumping (x y : ℕ) {claim : Prop} {H : ℕ → ℕ → Prop}
  (h₀ : H x y) (B : ℕ → ℤ) (C : ℕ → ℤ) (base : ℕ → ℕ → Prop)
  (H_quad : ∀ {x y}, H x y ↔ (y:ℤ) * y - B x * y + C x = 0) (H_symm : ∀ {x y}, H x y ↔ H y x)
  (H_zero : ∀ {x}, H x 0 → claim) (H_diag : ∀ {x}, H x x → claim)
  (H_desc : ∀ {x y}, 0 < x → x < y → ¬base x y → H x y →
    ∀ y', y' * y' - B x * y' + C x = 0 → y' = B x - y → y' * y = C x → 0 ≤ y' ∧ y' ≤ x)
  (H_base : ∀ {x y}, H x y → base x y → claim) :
  claim :=
begin
  -- First of all, we may assume that x ≤ y.
  -- We justify this using H_symm.
  wlog hxy : x ≤ y, swap, { rw H_symm at h₀, solve_by_elim },
  -- In fact, we can easily deal with the case x = y.
  by_cases x_eq_y : x = y, {subst x_eq_y, exact H_diag h₀},
  -- Hence we may assume that x < y.
  replace hxy : x < y := lt_of_le_of_ne hxy x_eq_y, clear x_eq_y,
  -- Consider the upper branch of the hyperbola defined by H.
  let upper_branch : set (ℕ × ℕ) := {p | H p.1 p.2 ∧ p.1 < p.2},
  -- Note that the point p = (x,y) lies on the upper branch.
  let p : ℕ × ℕ := ⟨x,y⟩,
  have hp : p ∈ upper_branch := ⟨h₀, hxy⟩,
  -- We also consider the exceptional set of solutions (a,b) that satisfy
  -- a = 0 or a = b or B a = b or B a = b + a or that lie in the base locus.
  let exceptional : set (ℕ × ℕ) :=
  {p | H p.1 p.2 ∧ (base p.1 p.2 ∨ p.1 = 0 ∨ p.1 = p.2 ∨ B p.1 = p.2 ∨ B p.1 = p.2 + p.1) },
  -- Let S be the projection of the upper branch on to the y-axis
  -- after removing the exceptional locus.
  let S : set ℕ := prod.snd '' (upper_branch \ exceptional),
  -- The strategy is to show that the exceptional locus in nonempty
  -- by running a descent argument that starts with the given point p = (x,y).
  -- Our assumptions ensure that we can then prove the claim.
  suffices exc : exceptional.nonempty,
  { -- Suppose that there exists an element in the exceptional locus.
    simp [exceptional, -add_comm, set.nonempty] at exc,
    -- Let (a,b) be such an element, and consider all the possible cases.
    rcases exc with ⟨a, b, hH, hb⟩, rcases hb with _|rfl|rfl|hB|hB,
    -- The first three cases are rather easy to solve.
    { solve_by_elim },
    { rw H_symm at hH, solve_by_elim },
    { solve_by_elim },
    -- The final two cases are very similar.
    all_goals
    { -- Consider the quadratic equation that (a,b) satisfies.
      rw H_quad at hH,
      -- We find the other root of the equation, and Vieta's formulas.
      rcases Vieta_formula_quadratic hH with ⟨c, h_root, hV₁, hV₂⟩,
      -- By substitutions we find that b = 0 or b = a.
      simp [hB] at hV₁, subst hV₁,
      rw [← int.coe_nat_zero] at *,
      rw ← H_quad at h_root,
      -- And hence we are done by H_zero and H_diag.
      solve_by_elim } },
  -- To finish the main proof, we need to show that the exceptional locus is nonempty.
  -- So we assume that the exceptional locus is empty, and work towards deriving a contradiction.
  rw set.nonempty_iff_ne_empty,
  assume exceptional_empty,
  -- Observe that S is nonempty.
  have S_nonempty : S.nonempty,
  { -- It contains the image of p.
    use p.2,
    apply set.mem_image_of_mem,
    -- After all, we assumed that the exceptional locus is empty.
    rwa [exceptional_empty, set.diff_empty], },
  -- We are now set for an infinite descent argument.
  -- Let m be the smallest element of the nonempty set S.
  let  m     : ℕ                := well_founded.min     nat.lt_wf S S_nonempty,
  have m_mem : m ∈ S            := well_founded.min_mem nat.lt_wf S S_nonempty,
  have m_min : ∀ k ∈ S, ¬ k < m := λ k hk, well_founded.not_lt_min nat.lt_wf S S_nonempty hk,
  -- It suffices to show that there is point (a,b) with b ∈ S and b < m.
  rsuffices ⟨p', p'_mem, p'_small⟩ : ∃ p' : ℕ × ℕ, p'.2 ∈ S ∧ p'.2 < m,
  { solve_by_elim },
  -- Let (m_x, m_y) be a point on the upper branch that projects to m ∈ S
  -- and that does not lie in the exceptional locus.
  rcases m_mem with ⟨⟨mx, my⟩, ⟨⟨hHm, mx_lt_my⟩, h_base⟩, m_eq⟩,
  -- This means that m_y = m,
  -- and the conditions H(m_x, m_y) and m_x < m_y are satisfied.
  simp [exceptional, hHm] at mx_lt_my h_base m_eq,
  push_neg at h_base,
  -- Finally, it also means that (m_x, m_y) does not lie in the base locus,
  -- that m_x ≠ 0, m_x ≠ m_y, B(m_x) ≠ m_y, and B(m_x) ≠ m_x + m_y.
  rcases h_base with ⟨h_base, hmx, hm_diag, hm_B₁, hm_B₂⟩,
  replace hmx : 0 < mx := pos_iff_ne_zero.mpr hmx,
  -- Consider the quadratic equation that (m_x, m_y) satisfies.
  have h_quad := hHm, rw H_quad at h_quad,
  -- We find the other root of the equation, and Vieta's formulas.
  rcases Vieta_formula_quadratic h_quad with ⟨c, h_root, hV₁, hV₂⟩,
  -- No we rewrite Vietas formulas a bit, and apply the descent step.
  replace hV₁ : c = B mx - my := eq_sub_of_add_eq' hV₁,
  rw mul_comm at hV₂,
  have Hc := H_desc hmx mx_lt_my h_base hHm c h_root hV₁ hV₂,
  -- This means that we may assume that c ≥ 0 and c ≤ m_x.
  cases Hc with c_nonneg c_lt,
  -- In other words, c is a natural number.
  lift c to ℕ using c_nonneg,
  -- Recall that we are trying find a point (a,b) such that b ∈ S and b < m.
  -- We claim that p' = (c, m_x) does the job.
  let p' : ℕ × ℕ := ⟨c, mx⟩,
  use p',
  -- The second condition is rather easy to check, so we do that first.
  split, swap,
  { rwa m_eq at mx_lt_my },
  -- Now we need to show that p' projects onto S. In other words, that c ∈ S.
  -- We do that, by showing that it lies in the upper branch
  -- (which is sufficient, because we assumed that the exceptional locus is empty).
  apply set.mem_image_of_mem,
  rw [exceptional_empty, set.diff_empty],
  -- Now we are ready to prove that p' = (c, m_x) lies on the upper branch.
  -- We need to check two conditions: H(c, m_x) and c < m_x.
  split; dsimp only,
  { -- The first condition is not so hard. After all, c is the other root of the quadratic equation.
    rw [H_symm, H_quad],
    simpa using h_root, },
  { -- For the second condition, we note that it suffices to check that c ≠ m_x.
    suffices hc : c ≠ mx,
    { refine lt_of_le_of_ne _ hc,
      exact_mod_cast c_lt, },
    -- However, recall that B(m_x) ≠ m_x + m_y.
    -- If c = m_x, we can prove B(m_x) = m_x + m_y.
    contrapose! hm_B₂, subst c,
    simp [hV₁], }
    -- Hence p' = (c, m_x) lies on the upper branch, and we are done.
end

/--Question 6 of IMO1988. If a and b are two natural numbers
such that a*b+1 divides a^2 + b^2, show that their quotient is a perfect square.-/
lemma imo1988_q6 {a b : ℕ} (h : (a*b+1) ∣ a^2 + b^2) :
  ∃ d, d^2 = (a^2 + b^2)/(a*b + 1) :=
begin
  rcases h with ⟨k, hk⟩,
  rw [hk, nat.mul_div_cancel_left _ (nat.succ_pos (a*b))],
  simp only [sq] at hk,
  apply constant_descent_vieta_jumping a b hk (λ x, k * x) (λ x, x*x - k) (λ x y, false);
  clear hk a b,
  { -- We will now show that the fibers of the solution set are described by a quadratic equation.
    intros x y, dsimp only,
    rw [← int.coe_nat_inj', ← sub_eq_zero],
    apply eq_iff_eq_cancel_right.2,
    norm_cast,
    simp, ring, },
  { -- Show that the solution set is symmetric in a and b.
    intros x y, simp [add_comm (x*x), mul_comm x], },
  { -- Show that the claim is true if b = 0.
    suffices : ∀ a, a * a = k → ∃ d, d * d = k, by simpa,
    rintros x rfl, use x },
  { -- Show that the claim is true if a = b.
    intros x hx,
    suffices : k ≤ 1,
    { rw [nat.le_add_one_iff, le_zero_iff] at this,
      rcases this with rfl|rfl,
      { use 0, simp },
      { use 1, simp } },
    contrapose! hx with k_lt_one,
    apply ne_of_lt,
    calc x*x + x*x = x*x * 2       : by rw mul_two
               ... ≤ x*x * k       : nat.mul_le_mul_left (x*x) k_lt_one
               ... < (x*x + 1) * k : by linarith },
  { -- Show the descent step.
    intros x y hx x_lt_y hxky h z h_root hV₁ hV₀,
    split,
    { dsimp [-sub_eq_add_neg] at *,
      have hpos : z*z + x*x > 0,
      { apply add_pos_of_nonneg_of_pos,
        { apply mul_self_nonneg },
        { apply mul_pos; exact_mod_cast hx }, },
      have hzx : z*z + x*x = (z * x + 1) * k,
      { rw [← sub_eq_zero, ← h_root],
        ring, },
      rw hzx at hpos,
      replace hpos : z * x + 1 > 0 := pos_of_mul_pos_left hpos (int.coe_zero_le k),
      replace hpos : z * x ≥ 0 := int.le_of_lt_add_one hpos,
      apply nonneg_of_mul_nonneg_left hpos (by exact_mod_cast hx), },
    { contrapose! hV₀ with x_lt_z,
      apply ne_of_gt,
      calc z * y > x*x     : by apply mul_lt_mul'; linarith
             ... ≥ x*x - k : sub_le_self _ (int.coe_zero_le k) }, },
  { -- There is no base case in this application of Vieta jumping.
    simp },
end

/-
The following example illustrates the use of constant descent Vieta jumping
in the presence of a non-trivial base case.
-/

example {a b : ℕ} (h : a*b ∣ a^2 + b^2 + 1) :
  3*a*b = a^2 + b^2 + 1 :=
begin
  rcases h with ⟨k, hk⟩,
  suffices : k = 3, { simp * at *, ring, },
  simp only [sq] at hk,
  apply constant_descent_vieta_jumping a b hk (λ x, k * x) (λ x, x*x + 1) (λ x y, x ≤ 1);
  clear hk a b,
  { -- We will now show that the fibers of the solution set are described by a quadratic equation.
    intros x y, dsimp only,
    rw [← int.coe_nat_inj', ← sub_eq_zero],
    apply eq_iff_eq_cancel_right.2,
    simp, ring, },
  { -- Show that the solution set is symmetric in a and b.
    cc },
  { -- Show that the claim is true if b = 0.
    simp },
  { -- Show that the claim is true if a = b.
    intros x hx,
    have x_sq_dvd : x*x ∣ x*x*k := dvd_mul_right (x*x) k,
    rw ← hx at x_sq_dvd,
    obtain ⟨y, hy⟩ : x * x ∣ 1 := by simpa only [nat.dvd_add_self_left, add_assoc] using x_sq_dvd,
    obtain ⟨rfl,rfl⟩ : x = 1 ∧ y = 1 := by simpa [nat.mul_eq_one_iff] using hy.symm,
    simpa using hx.symm, },
  { -- Show the descent step.
    intros x y x_lt_y hx h_base h z h_root hV₁ hV₀,
    split,
    { have zy_pos : z * y ≥ 0,
      { rw hV₀, exact_mod_cast (nat.zero_le _) },
      apply nonneg_of_mul_nonneg_left zy_pos,
      linarith },
    { contrapose! hV₀ with x_lt_z,
      apply ne_of_gt,
      push_neg at h_base,
      calc z * y > x * y       : by apply mul_lt_mul_of_pos_right; linarith
             ... ≥ x * (x + 1) : by apply mul_le_mul; linarith
             ... > x * x + 1   :
        begin
          rw [mul_add, mul_one],
          apply add_lt_add_left,
          assumption_mod_cast
        end, } },
  { -- Show the base case.
    intros x y h h_base,
    obtain rfl|rfl : x = 0 ∨ x = 1 := by rwa [nat.le_add_one_iff, le_zero_iff] at h_base,
    { simpa using h, },
    { simp only [mul_one, one_mul, add_comm, zero_add] at h,
      have y_dvd : y ∣ y * k := dvd_mul_right y k,
      rw [← h, ← add_assoc, nat.dvd_add_left (dvd_mul_left y y)] at y_dvd,
      obtain rfl|rfl := (nat.dvd_prime nat.prime_two).mp y_dvd; apply nat.eq_of_mul_eq_mul_left,
      exacts [zero_lt_one, h.symm, zero_lt_two, h.symm] } }
end
