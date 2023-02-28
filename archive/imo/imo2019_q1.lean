/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import tactic.linarith

/-!
# IMO 2019 Q1

Determine all functions `f : ℤ → ℤ` such that, for all integers `a` and `b`,
`f(2a) + 2f(b) = f(f(a+b))`.

The desired theorem is that either:
  -  `f = λ _, 0`
  -  `∃ c, f = λ x, 2 * x + c`

Note that there is a much more compact proof of this fact in Isabelle/HOL
  - http://downthetypehole.de/paste/4YbGgqb4
-/

theorem imo2019Q1 (f : ℤ → ℤ) :
  (∀ a b : ℤ, f (2 * a) + 2 * (f b) = f (f (a + b))) ↔
    (f = 0) ∨ ∃ c, f = λ x, 2 * x + c :=
begin
  split, swap,
  -- easy way: f(x)=0 and f(x)=2x+c work.
  { rintros (rfl|⟨c, rfl⟩); intros; simp only [pi.zero_apply]; ring },
  -- hard way.
  intro hf, -- functional equation
  -- Using `h` for `(0, b)` and `(-1, b + 1)`, we get `f (b + 1) = f b + m`
  obtain ⟨m, H⟩ : ∃ m, ∀ b, f (b + 1) = f b + m,
  { refine ⟨(f 0 - f (-2)) / 2, λ b, _⟩,
    refine sub_eq_iff_eq_add'.1 (int.eq_div_of_mul_eq_right two_ne_zero _),
    have h1 : f 0 + 2 * f b = f (f b) := by simpa using hf 0 b,
    have h2 : f (-2) + 2 * f (b + 1) = f (f b) := by simpa using hf (-1) (b + 1),
    linarith },
  -- Hence, `f` is an affine map, `f b = f 0 + m * b`
  obtain ⟨c, H⟩ : ∃ c, ∀ b, f b = c + m * b,
  { refine ⟨f 0, λ b, _⟩,
    induction b using int.induction_on with b ihb b ihb,
    { simp },
    { simp [H, ihb, mul_add, add_assoc] },
    { rw ← sub_eq_of_eq_add (H _),
      simp [ihb]; ring } },
  -- Now use `hf 0 0` and `hf 0 1` to show that `m ∈ {0, 2}`
  have H3 : 2 * c = m * c := by simpa [H, mul_add] using hf 0 0,
  obtain (rfl|rfl) : 2 = m ∨ m = 0 := by simpa [H, mul_add, H3] using hf 0 1,
  { right, use c, ext b, simp [H, add_comm] },
  { left, ext b, simpa [H, two_ne_zero] using H3 }
end
