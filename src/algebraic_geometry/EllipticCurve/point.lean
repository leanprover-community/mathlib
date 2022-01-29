/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import field_theory.galois

import algebraic_geometry.EllipticCurve

/-!
# The group of rational points on an elliptic curve over a field
-/

noncomputable theory
open_locale classical

variables {F : Type*} [field F]

notation K↑L := algebra_map K L
notation K`⟶[`F]L := (algebra.of_id K L).restrict_scalars F

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

section point

variables (E : EllipticCurve F) (K : Type*) [field K] [algebra F K]

/-- The group of `K`-rational points `E(K)` on an elliptic curve `E` over `F`, consisting of
    the point at infinity and the affine points satisfying a Weierstrass equation `w`. -/
inductive point
| zero
| some (x y : K) (w : y ^ 2 + (F↑K)E.a₁ * x * y + (F↑K)E.a₃ * y
                    = x ^ 3 + (F↑K)E.a₂ * x ^ 2 + (F↑K)E.a₄ * x + (F↑K)E.a₆)

notation E⟮K⟯ := point E K

end point

variables {E : EllipticCurve F}
variables {K : Type*} [field K] [algebra F K]
variables {L : Type*} [field L] [algebra F L] [algebra K L] [is_scalar_tower F K L]

open point

----------------------------------------------------------------------------------------------------
/-! ## Zero in `E(K)` -/

section zero

/-- `E(K)` has zero. -/
instance : has_zero E⟮K⟯ := ⟨zero⟩

/-- Zero in `E(K)` is zero. -/
@[simp] lemma zero_def : zero = (0 : E⟮K⟯) := rfl

/-- `E(K)` is inhabited. -/
instance : inhabited E⟮K⟯ := ⟨0⟩

end zero

----------------------------------------------------------------------------------------------------
/-! ## Negation in `E(K)` -/

section negation

variables {x y : K}
variables (w : y ^ 2 + (F↑K)E.a₁ * x * y + (F↑K)E.a₃ * y
             = x ^ 3 + (F↑K)E.a₂ * x ^ 2 + (F↑K)E.a₄ * x + (F↑K)E.a₆)

include w

/-- Negation of an affine point in `E(K)` is in `E(K)`. -/
lemma neg_weierstrass :
  (-y - (F↑K)E.a₁ * x - (F↑K)E.a₃) ^ 2 + (F↑K)E.a₁ * x * (-y - (F↑K)E.a₁ * x - (F↑K)E.a₃)
    + (F↑K)E.a₃ * (-y - (F↑K)E.a₁ * x - (F↑K)E.a₃)
    = x ^ 3 + (F↑K)E.a₂ * x ^ 2 + (F↑K)E.a₄ * x + (F↑K)E.a₆ :=
by { rw [← w], ring1 }

omit w

/-- Negation in `E(K)`. -/
def neg : E⟮K⟯ → E⟮K⟯
| 0            := 0
| (some x y w) := some x (-y - (F↑K)E.a₁ * x - (F↑K)E.a₃) $ neg_weierstrass w

/-- `E(K)` has negation. -/
instance : has_neg E⟮K⟯ := ⟨neg⟩

/-- Negation of zero in `E(K)` is zero. -/
@[simp] lemma neg_zero : -0 = (0 : E⟮K⟯) := rfl

/-- Negation of an affine point in `E(K)` is an affine point. -/
@[simp] lemma neg_some :
  -some x y w = some x (-y - (F↑K)E.a₁ * x - (F↑K)E.a₃) (neg_weierstrass w) :=
rfl

end negation

----------------------------------------------------------------------------------------------------
/-! ## Doubling in `E(K)` -/

section doubling

variables {x y l x' y' : K}
variables (w : y ^ 2 + (F↑K)E.a₁ * x * y + (F↑K)E.a₃ * y
             = x ^ 3 + (F↑K)E.a₂ * x ^ 2 + (F↑K)E.a₄ * x + (F↑K)E.a₆)

include w

/-- Doubling of an affine point in `E(K)` is in `E(K)`. -/
lemma dbl_weierstrass
  (y_ne : 2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃ ≠ 0)
  (l_def : l  = (3 * x ^ 2 + 2 * (F↑K)E.a₂ * x + (F↑K)E.a₄ - (F↑K)E.a₁ * y)
                * (2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃)⁻¹)
  (x_def : x' = l ^ 2 + (F↑K)E.a₁ * l - (F↑K)E.a₂ - 2 * x)
  (y_def : y' = -l * x' - (F↑K)E.a₁ * x' - y + l * x - (F↑K)E.a₃) :
  y' ^ 2 + (F↑K)E.a₁ * x' * y' + (F↑K)E.a₃ * y'
    = x' ^ 3 + (F↑K)E.a₂ * x' ^ 2 + (F↑K)E.a₄ * x' + (F↑K)E.a₆ :=
begin
  -- rewrite Weierstrass equation as w(x, y) = 0
  rw [← sub_eq_zero] at w,
  -- rewrite y
  have y_rw :
    y' ^ 2 + (F↑K)E.a₁ * x' * y' + (F↑K)E.a₃ * y'
      = x' ^ 2 * (l ^ 2 + (F↑K)E.a₁ * l)
      + x' * (-2 * x * l ^ 2 - (F↑K)E.a₁ * x * l + 2 * y * l + (F↑K)E.a₃ * l + (F↑K)E.a₁ * y)
      + (x ^ 2 * l ^ 2 - 2 * x * y * l - (F↑K)E.a₃ * x * l + y ^ 2 + (F↑K)E.a₃ * y) :=
  by { rw [y_def], ring1 },
  -- rewrite x
  have x_rw :
    x' ^ 2 * (l ^ 2 + (F↑K)E.a₁ * l)
      + x' * (-2 * x * l ^ 2 - (F↑K)E.a₁ * x * l + 2 * y * l + (F↑K)E.a₃ * l + (F↑K)E.a₁ * y)
      + (x ^ 2 * l ^ 2 - 2 * x * y * l - (F↑K)E.a₃ * x * l + y ^ 2 + (F↑K)E.a₃ * y)
      - (x' ^ 3 + (F↑K)E.a₂ * x' ^ 2 + (F↑K)E.a₄ * x' + (F↑K)E.a₆)
      = l * (l * (l * (2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃)
                  + (-3 * x ^ 2 + (F↑K)E.a₁ ^ 2 * x - 2 * (F↑K)E.a₂ * x + 3 * (F↑K)E.a₁ * y
                     + (F↑K)E.a₁ * (F↑K)E.a₃ - (F↑K)E.a₄))
             + (-6 * (F↑K)E.a₁ * x ^ 2 - 6 * x * y - 3 * (F↑K)E.a₁ * (F↑K)E.a₂ * x
                - 3 * (F↑K)E.a₃ * x + (F↑K)E.a₁ ^ 2 * y - 2 * (F↑K)E.a₂ * y - (F↑K)E.a₁ * (F↑K)E.a₄
                - (F↑K)E.a₂ * (F↑K)E.a₃))
        + (8 * x ^ 3 + 8 * (F↑K)E.a₂ * x ^ 2 - 2 * (F↑K)E.a₁ * x * y + y ^ 2 + 2 * (F↑K)E.a₂ ^ 2 * x
           + 2 * (F↑K)E.a₄ * x - (F↑K)E.a₁ * (F↑K)E.a₂ * y + (F↑K)E.a₃ * y + (F↑K)E.a₂ * (F↑K)E.a₄
           - (F↑K)E.a₆) :=
  by { rw [x_def], ring1 },
  -- rewrite l step 1
  have l_rw_1 :
    l * (2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃)
      + (-3 * x ^ 2 + (F↑K)E.a₁ ^ 2 * x - 2 * (F↑K)E.a₂ * x + 3 * (F↑K)E.a₁ * y
         + (F↑K)E.a₁ * (F↑K)E.a₃ - (F↑K)E.a₄)
      = (2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃) * (F↑K)E.a₁ :=
  by { rw [l_def, inv_mul_cancel_right₀ y_ne], ring1 },
  -- rewrite l step 2
  have l_rw_2 :
    l * ((2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃) * (F↑K)E.a₁)
      + (-6 * (F↑K)E.a₁ * x ^ 2 - 6 * x * y - 3 * (F↑K)E.a₁ * (F↑K)E.a₂ * x - 3 * (F↑K)E.a₃ * x
         + (F↑K)E.a₁ ^ 2 * y - 2 * (F↑K)E.a₂ * y - (F↑K)E.a₁ * (F↑K)E.a₄ - (F↑K)E.a₂ * (F↑K)E.a₃)
      = (2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃) * (-3 * x - (F↑K)E.a₂) :=
  by { rw [← mul_assoc l, l_def, inv_mul_cancel_right₀ y_ne], ring1 },
  -- rewrite l step 3
  have l_rw_3 :
    l * ((2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃) * (-3 * x - (F↑K)E.a₂))
      + (8 * x ^ 3 + 8 * (F↑K)E.a₂ * x ^ 2 - 2 * (F↑K)E.a₁ * x * y + y ^ 2 + 2 * (F↑K)E.a₂ ^ 2 * x
         + 2 * (F↑K)E.a₄ * x - (F↑K)E.a₁ * (F↑K)E.a₂ * y + (F↑K)E.a₃ * y + (F↑K)E.a₂ * (F↑K)E.a₄
         - (F↑K)E.a₆)
      = 0 :=
  by { rw [← mul_assoc l, l_def, inv_mul_cancel_right₀ y_ne, ← w], ring1 },
  -- rewrite Weierstrass equation as w'(x', y') = 0 and sequence steps
  rw [← sub_eq_zero, y_rw, x_rw, l_rw_1, l_rw_2, l_rw_3]
end

omit w

/-- Doubling in `E(K)`. -/
def dbl : E⟮K⟯ → E⟮K⟯
| 0            := 0
| (some x y w) :=
if y_ne : 2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃ ≠ 0 then
  let l  := (3 * x ^ 2 + 2 * (F↑K)E.a₂ * x + (F↑K)E.a₄ - (F↑K)E.a₁ * y)
            * (2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃)⁻¹,
      x' := l ^ 2 + (F↑K)E.a₁ * l - (F↑K)E.a₂ - 2 * x,
      y' := -l * x' - (F↑K)E.a₁ * x' - y + l * x - (F↑K)E.a₃
  in  some x' y' $ dbl_weierstrass w y_ne rfl rfl rfl
else
  0

/-- Doubling of zero in `E(K)` is zero. -/
@[simp] lemma dbl_zero : dbl 0 = (0 : E⟮K⟯) := rfl

/-- Doubling of an affine point `(x, y) ∈ E(K)` with `2y + a₁x + a₃ ≠ 0` is an affine point. -/
@[simp] lemma dbl_some_of_y_ne (y_ne : 2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃ ≠ 0) :
  dbl (some x y w)
    = let l  := (3 * x ^ 2 + 2 * (F↑K)E.a₂ * x + (F↑K)E.a₄ - (F↑K)E.a₁ * y)
                * (2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃)⁻¹,
          x' := l ^ 2 + (F↑K)E.a₁ * l - (F↑K)E.a₂ - 2 * x,
          y' := -l * x' - (F↑K)E.a₁ * x' - y + l * x - (F↑K)E.a₃
      in  some x' y' $ dbl_weierstrass w y_ne rfl rfl rfl :=
by rw [dbl, dif_pos y_ne]

/-- Doubling of an affine point `(x, y) ∈ E(K)` with `2y + a₁x + a₃ = 0` is zero. -/
@[simp] lemma dbl_some_of_y_eq (y_eq : 2 * y + (F↑K)E.a₁ * x + (F↑K)E.a₃ = 0) :
  dbl (some x y w) = 0 :=
by rw [dbl, dif_neg $ not_not.mpr y_eq]

end doubling

----------------------------------------------------------------------------------------------------
/-! ## Addition in `E(K)` -/

section addition

variables {x₁ y₁ x₂ y₂ l x₃ y₃ : K}
variables (w₁ : y₁ ^ 2 + (F↑K)E.a₁ * x₁ * y₁ + (F↑K)E.a₃ * y₁
              = x₁ ^ 3 + (F↑K)E.a₂ * x₁ ^ 2 + (F↑K)E.a₄ * x₁ + (F↑K)E.a₆)
variables (w₂ : y₂ ^ 2 + (F↑K)E.a₁ * x₂ * y₂ + (F↑K)E.a₃ * y₂
              = x₂ ^ 3 + (F↑K)E.a₂ * x₂ ^ 2 + (F↑K)E.a₄ * x₂ + (F↑K)E.a₆)

include w₁ w₂

/-- Addition of affine points in `E(K)` is in `E(K)`. -/
lemma add_weierstrass
  (x_ne : x₁ ≠ x₂)
  (l_def : l  = (y₁ - y₂) * (x₁ - x₂)⁻¹)
  (x_def : x₃ = l ^ 2 + (F↑K)E.a₁ * l - (F↑K)E.a₂ - x₁ - x₂)
  (y_def : y₃ = -l * x₃ - (F↑K)E.a₁ * x₃ - y₁ + l * x₁ - (F↑K)E.a₃) :
  y₃ ^ 2 + (F↑K)E.a₁ * x₃ * y₃ + (F↑K)E.a₃ * y₃
    = x₃ ^ 3 + (F↑K)E.a₂ * x₃ ^ 2 + (F↑K)E.a₄ * x₃ + (F↑K)E.a₆ :=
begin
  -- rewrite Weierstrass equations as w₁(x₁, y₁) = 0 and w₂(x₂, y₂) = 0
  rw [← sub_eq_zero] at w₁ w₂,
  -- rewrite y
  have y_rw :
    y₃ ^ 2 + (F↑K)E.a₁ * x₃ * y₃ + (F↑K)E.a₃ * y₃
      = x₃ ^ 2 * (l ^ 2 + (F↑K)E.a₁ * l)
      + x₃ * (-2 * x₁ * l ^ 2 - (F↑K)E.a₁ * x₁ * l + 2 * y₁ * l + (F↑K)E.a₃ * l + (F↑K)E.a₁ * y₁)
      + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (F↑K)E.a₃ * x₁ * l + y₁ ^ 2 + (F↑K)E.a₃ * y₁) :=
  by { rw [y_def], ring1 },
  -- rewrite x
  have x_rw :
    x₃ ^ 2 * (l ^ 2 + (F↑K)E.a₁ * l)
      + x₃ * (-2 * x₁ * l ^ 2 - (F↑K)E.a₁ * x₁ * l + 2 * y₁ * l + (F↑K)E.a₃ * l + (F↑K)E.a₁ * y₁)
      + (x₁ ^ 2 * l ^ 2 - 2 * x₁ * y₁ * l - (F↑K)E.a₃ * x₁ * l + y₁ ^ 2 + (F↑K)E.a₃ * y₁)
      - (x₃ ^ 3 + (F↑K)E.a₂ * x₃ ^ 2 + (F↑K)E.a₄ * x₃ + (F↑K)E.a₆)
      = l * (l * (l * (l * (x₁ - x₂) * (-1)
                       + (-(F↑K)E.a₁ * x₁ + 2 * (F↑K)E.a₁ * x₂ + 2 * y₁ + (F↑K)E.a₃))
                  + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + (F↑K)E.a₁ ^ 2 * x₂ - 2 * (F↑K)E.a₂ * x₂
                     + 3 * (F↑K)E.a₁ * y₁ + (F↑K)E.a₁ * (F↑K)E.a₃ - (F↑K)E.a₄))
             + (-(F↑K)E.a₁ * x₁ ^ 2 - 3 * (F↑K)E.a₁ * x₁ * x₂ - 4 * x₁ * y₁ - 2 * (F↑K)E.a₁ * x₂ ^ 2
                - 2 * x₂ * y₁ - (F↑K)E.a₁ * (F↑K)E.a₂ * x₁ - 2 * (F↑K)E.a₃ * x₁
                - 2 * (F↑K)E.a₁ * (F↑K)E.a₂ * x₂ - (F↑K)E.a₃ * x₂ + (F↑K)E.a₁ ^ 2 * y₁
                - 2 * (F↑K)E.a₂ * y₁ - (F↑K)E.a₁ * (F↑K)E.a₄ - (F↑K)E.a₂ * (F↑K)E.a₃))
        + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * (F↑K)E.a₂ * x₁ ^ 2
           + 4 * (F↑K)E.a₂ * x₁ * x₂ - (F↑K)E.a₁ * x₁ * y₁ + 2 * (F↑K)E.a₂ * x₂ ^ 2
           - (F↑K)E.a₁ * x₂ * y₁ + y₁ ^ 2 + (F↑K)E.a₂ ^ 2 * x₁ + (F↑K)E.a₄ * x₁ + (F↑K)E.a₂ ^ 2 * x₂
           + (F↑K)E.a₄ * x₂ - (F↑K)E.a₁ * (F↑K)E.a₂ * y₁ + (F↑K)E.a₃ * y₁ + (F↑K)E.a₂ * (F↑K)E.a₄
           - (F↑K)E.a₆) :=
  by { rw [x_def], ring1 },
  -- rewrite l auxiliary tactic
  have l_rw : ∀ a b c : K, l * a + b = c ↔ (y₁ - y₂) * a + (x₁ - x₂) * b + 0 = (x₁ - x₂) * c + 0 :=
  by { intros, rw [← mul_right_inj' $ sub_ne_zero.mpr x_ne, mul_add (x₁ - x₂),
                   ← mul_assoc (x₁ - x₂) l, mul_comm (x₁ - x₂) l, l_def,
                   inv_mul_cancel_right₀ $ sub_ne_zero.mpr x_ne, ← add_left_inj (0 : K)] },
  -- rewrite l step 1
  have l_rw_1 :
    l * (x₁ - x₂) * (-1) + (-(F↑K)E.a₁ * x₁ + 2 * (F↑K)E.a₁ * x₂ + 2 * y₁ + (F↑K)E.a₃)
      = -(F↑K)E.a₁ * x₁ + 2 * (F↑K)E.a₁ * x₂ + 2 * y₁ + (F↑K)E.a₃ - y₁ + y₂ :=
  by { rw [l_def, inv_mul_cancel_right₀ $ sub_ne_zero.mpr x_ne], ring1 },
  -- rewrite l step 2
  have l_rw_2 :
    l * (-(F↑K)E.a₁ * x₁ + 2 * (F↑K)E.a₁ * x₂ + 2 * y₁ + (F↑K)E.a₃ - y₁ + y₂)
      + (x₁ ^ 2 - 2 * x₁ * x₂ - 2 * x₂ ^ 2 + (F↑K)E.a₁ ^ 2 * x₂ - 2 * (F↑K)E.a₂ * x₂
         + 3 * (F↑K)E.a₁ * y₁ + (F↑K)E.a₁ * (F↑K)E.a₃ - (F↑K)E.a₄)
      = 2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + (F↑K)E.a₂ * x₁ + (F↑K)E.a₁ ^ 2 * x₂ + (F↑K)E.a₂ * x₂
      - 2 * (F↑K)E.a₂ * x₂ + (F↑K)E.a₁ * y₁ + (F↑K)E.a₁ * y₂ + (F↑K)E.a₁ * (F↑K)E.a₃ :=
  by { rw [l_rw], nth_rewrite_rhs 0 [← w₁], nth_rewrite_lhs 0 [← w₂], ring1 },
  -- rewrite l step 3
  have l_rw_3 :
    l * (2 * x₁ ^ 2 - x₁ * x₂ - x₂ ^ 2 + (F↑K)E.a₂ * x₁ + (F↑K)E.a₁ ^ 2 * x₂ + (F↑K)E.a₂ * x₂
         - 2 * (F↑K)E.a₂ * x₂ + (F↑K)E.a₁ * y₁ + (F↑K)E.a₁ * y₂ + (F↑K)E.a₁ * (F↑K)E.a₃)
      + (-(F↑K)E.a₁ * x₁ ^ 2 - 3 * (F↑K)E.a₁ * x₁ * x₂ - 4 * x₁ * y₁ - 2 * (F↑K)E.a₁ * x₂ ^ 2
         - 2 * x₂ * y₁ - (F↑K)E.a₁ * (F↑K)E.a₂ * x₁ - 2 * (F↑K)E.a₃ * x₁
         - 2 * (F↑K)E.a₁ * (F↑K)E.a₂ * x₂ - (F↑K)E.a₃ * x₂ + (F↑K)E.a₁ ^ 2 * y₁ - 2 * (F↑K)E.a₂ * y₁
         - (F↑K)E.a₁ * (F↑K)E.a₄ - (F↑K)E.a₂ * (F↑K)E.a₃)
      = -2 * (F↑K)E.a₁ * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - (F↑K)E.a₁ * x₂ ^ 2 - x₂ * y₁
        - x₂ * y₂ - 2 * (F↑K)E.a₃ * x₁ - (F↑K)E.a₁ * (F↑K)E.a₂ * x₂ - (F↑K)E.a₃ * x₂
        - (F↑K)E.a₂ * y₁ - (F↑K)E.a₂ * y₂ - (F↑K)E.a₂ * (F↑K)E.a₃ :=
  by { apply_fun ((*) ((F↑K)E.a₁)) at w₁ w₂, rw [mul_zero] at w₁ w₂, rw [l_rw],
       nth_rewrite_rhs 0 [← w₁], nth_rewrite_lhs 0 [← w₂], ring1 },
  -- rewrite l step 4
  have l_rw_4 :
    l * (-2 * (F↑K)E.a₁ * x₁ * x₂ - 2 * x₁ * y₁ - 2 * x₁ * y₂ - (F↑K)E.a₁ * x₂ ^ 2 - x₂ * y₁
         - x₂ * y₂ - 2 * (F↑K)E.a₃ * x₁ - (F↑K)E.a₁ * (F↑K)E.a₂ * x₂ - (F↑K)E.a₃ * x₂
         - (F↑K)E.a₂ * y₁ - (F↑K)E.a₂ * y₂ - (F↑K)E.a₂ * (F↑K)E.a₃)
      + (x₁ ^ 3 + 3 * x₁ ^ 2 * x₂ + 3 * x₁ * x₂ ^ 2 + x₂ ^ 3 + 2 * (F↑K)E.a₂ * x₁ ^ 2
         + 4 * (F↑K)E.a₂ * x₁ * x₂ - (F↑K)E.a₁ * x₁ * y₁ + 2 * (F↑K)E.a₂ * x₂ ^ 2
         - (F↑K)E.a₁ * x₂ * y₁ + y₁ ^ 2 + (F↑K)E.a₂ ^ 2 * x₁ + (F↑K)E.a₄ * x₁ + (F↑K)E.a₂ ^ 2 * x₂
         + (F↑K)E.a₄ * x₂ - (F↑K)E.a₁ * (F↑K)E.a₂ * y₁ + (F↑K)E.a₃ * y₁ + (F↑K)E.a₂ * (F↑K)E.a₄
         - (F↑K)E.a₆)
      = 0 :=
  by { apply_fun ((*) (x₁ + 2 * x₂ + (F↑K)E.a₂)) at w₁,
       apply_fun ((*) (2 * x₁ + x₂ + (F↑K)E.a₂)) at w₂, rw [mul_zero] at w₁ w₂, rw [l_rw],
       nth_rewrite_lhs 0 [← w₁], nth_rewrite_rhs 1 [← w₂], ring1 },
  -- rewrite Weierstrass equation as w₃(x₃, y₃) = 0 and sequence steps
  rw [← sub_eq_zero, y_rw, x_rw, l_rw_1, l_rw_2, l_rw_3, l_rw_4]
end

/-- For all affine points `(x₁, y₁), (x₂, y₂) ∈ E(K)`,
    if `x₁ = x₂` and `y₁ + y₂ + a₁x₂ + a₃ ≠ 0` then `2y₁ + a₁x₁ + a₃ ≠ 0`. -/
private lemma y_ne_of_y_ne (x_eq : x₁ = x₂) (y_ne : y₁ + y₂ + (F↑K)E.a₁ * x₂ + (F↑K)E.a₃ ≠ 0) :
  2 * y₁ + (F↑K)E.a₁ * x₁ + (F↑K)E.a₃ ≠ 0 :=
begin
  have y_rw : ∀ a₁ a₃ : K,
    y₁ ^ 2 + a₁ * x₁ * y₁ + a₃ * y₁ - (y₂ ^ 2 + a₁ * x₁ * y₂ + a₃ * y₂)
      = (y₁ - y₂) * (y₁ + y₂ + a₁ * x₁ + a₃) :=
  by { intros, ring1 },
  subst x_eq,
  rw [← w₂, ← sub_eq_zero, y_rw, mul_eq_zero, sub_eq_zero] at w₁,
  cases w₁,
  { subst w₁,
    simpa only [two_mul] },
  { contradiction }
end

omit w₁ w₂

/-- Addition in `E(K)`. -/
def add : E⟮K⟯ → E⟮K⟯ → E⟮K⟯
| 0               P               := P
| P               0               := P
| (some x₁ y₁ w₁) (some x₂ y₂ w₂) :=
if x_ne : x₁ ≠ x₂ then
  let l  := (y₁ - y₂) * (x₁ - x₂)⁻¹,
      x₃ := l ^ 2 + (F↑K)E.a₁ * l - (F↑K)E.a₂ - x₁ - x₂,
      y₃ := -l * x₃ - (F↑K)E.a₁ * x₃ - y₁ + l * x₁ - (F↑K)E.a₃
  in  some x₃ y₃ $ add_weierstrass w₁ w₂ x_ne rfl rfl rfl
else
  if y_ne : y₁ + y₂ + (F↑K)E.a₁ * x₂ + (F↑K)E.a₃ ≠ 0 then dbl $ some x₁ y₁ w₁ else 0

/-- `E(K)` has addition. -/
instance : has_add E⟮K⟯ := ⟨add⟩

/-- Addition of zero and `P ∈ E(K)` is `P`. -/
@[simp] lemma zero_add (P : E⟮K⟯) : 0 + P = P := by cases P; refl

/-- Addition of `P ∈ E(K)` and zero is `P`. -/
@[simp] lemma add_zero (P : E⟮K⟯) : P + 0 = P := by cases P; refl

/-- Addition of affine points `(x₁, y₁), (x₂, y₂) ∈ E(K)` with `x₁ ≠ x₂` is an affine point. -/
@[simp] lemma some_add_some_of_x_ne (x_ne : x₁ ≠ x₂) :
  some x₁ y₁ w₁ + some x₂ y₂ w₂
    = let l  := (y₁ - y₂) * (x₁ - x₂)⁻¹,
          x₃ := l ^ 2 + (F↑K)E.a₁ * l - (F↑K)E.a₂ - x₁ - x₂,
          y₃ := -l * x₃ - (F↑K)E.a₁ * x₃ - y₁ + l * x₁ - (F↑K)E.a₃
      in  some x₃ y₃ $ add_weierstrass w₁ w₂ x_ne rfl rfl rfl :=
by { unfold has_add.add, rw [add, dif_pos x_ne] }

/-- Addition of affine points `(x₁, y₁), (x₂, y₂) ∈ E(K)` with `x₁ = x₂`
    and `y₁ + y₂ + a₁x₂ + a₃ ≠ 0` is doubling of `(x₁, y₁)`. -/
@[simp] lemma some_add_some_of_y_ne (x_eq : x₁ = x₂)
  (y_ne : y₁ + y₂ + (F↑K)E.a₁ * x₂ + (F↑K)E.a₃ ≠ 0) :
  some x₁ y₁ w₁ + some x₂ y₂ w₂
    = let l  := (3 * x₁ ^ 2 + 2 * (F↑K)E.a₂ * x₁ + (F↑K)E.a₄ - (F↑K)E.a₁ * y₁)
                * (2 * y₁ + (F↑K)E.a₁ * x₁ + (F↑K)E.a₃)⁻¹,
          x' := l ^ 2 + (F↑K)E.a₁ * l - (F↑K)E.a₂ - 2 * x₁,
          y' := -l * x' - (F↑K)E.a₁ * x' - y₁ + l * x₁ - (F↑K)E.a₃
      in  some x' y' $ dbl_weierstrass w₁ (y_ne_of_y_ne w₁ w₂ x_eq y_ne) rfl rfl rfl :=
begin
  unfold has_add.add,
  rw [add, dif_neg $ not_not.mpr x_eq, if_pos y_ne, dbl, dif_pos $ y_ne_of_y_ne w₁ w₂ x_eq y_ne]
end

/-- Addition of affine points `(x₁, y₁), (x₂, y₂) ∈ E(K)` with `x₁ = x₂`
    and `y₁ + y₂ + a₁x₂ + a₃ = 0` is zero. -/
@[simp] lemma some_add_some_of_y_eq (x_eq : x₁ = x₂)
  (y_eq : y₁ + y₂ + (F↑K)E.a₁ * x₂ + (F↑K)E.a₃ = 0) : some x₁ y₁ w₁ + some x₂ y₂ w₂ = 0 :=
by { unfold has_add.add, rw [add, dif_neg $ not_not.mpr x_eq, if_neg $ not_not.mpr y_eq] }

end addition

----------------------------------------------------------------------------------------------------
/-! ## Axioms in `E(K)` -/

section add_comm_group

/-- Left negation in `E(K)`. -/
@[simp] lemma add_left_neg (P : E⟮K⟯) : -P + P = 0 :=
by { cases P, { refl }, { rw [neg_some, some_add_some_of_y_eq]; ring1 } }

/-- Commutativity in `E(K)`. -/
lemma add_comm (P Q : E⟮K⟯) : P + Q = Q + P :=
begin
  rcases ⟨P, Q⟩ with ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  any_goals { refl },
  { sorry }
end

/-- Associativity in `E(K)`. -/
lemma add_assoc (P Q R : E⟮K⟯) : (P + Q) + R = P + (Q + R) :=
begin
  rcases ⟨P, Q, R⟩ with ⟨⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩,
  any_goals { refl },
  { rw [zero_def, zero_add, zero_add] },
  { rw [zero_def, add_zero, add_zero] },
  { sorry }
end

/-- `E(K)` is an additive commutative group. -/
instance : add_comm_group E⟮K⟯ :=
{ zero         := 0,
  neg          := neg,
  add          := add,
  zero_add     := zero_add,
  add_zero     := add_zero,
  add_left_neg := add_left_neg,
  add_comm     := add_comm,
  add_assoc    := add_assoc }

end add_comm_group

----------------------------------------------------------------------------------------------------
/-! ## Functoriality of `K ↦ E(K)` -/

section functoriality

variables (φ : K →ₐ[F] L)

/-- Set function `E(K) → E(L)`. -/
def point_hom.to_fun : E⟮K⟯ → E⟮L⟯
| 0            := 0
| (some x y w) := some (φ x) (φ y)
begin
  apply_fun φ at w,
  simp only [alg_hom.map_add, alg_hom.map_mul, alg_hom.map_pow, alg_hom.commutes] at w,
  exact w
end

/-- `E(K) → E(L)` respects zero. -/
lemma point_hom.map_zero : point_hom.to_fun φ 0 = (0 : E⟮L⟯) := rfl

/-- `E(K) → E(L)` respects addition. -/
lemma point_hom.map_add (P Q : E⟮K⟯) :
  point_hom.to_fun φ (P + Q) = point_hom.to_fun φ P + point_hom.to_fun φ Q :=
begin
  rcases ⟨P, Q⟩ with ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  any_goals { refl },
  { sorry }
end

/-- Group homomorphism `E(K) → E(L)`. -/
def point_hom : E⟮K⟯ →+ E⟮L⟯ := ⟨point_hom.to_fun φ, point_hom.map_zero φ, point_hom.map_add φ⟩

/-- `K ↦ E(K)` respects identity. -/
lemma point_hom.id (P : E⟮K⟯) : point_hom (K⟶[F]K) P = P := by cases P; refl

/-- `K ↦ E(K)` respects composition. -/
lemma point_hom.comp {M : Type*} [field M] [algebra F M] [algebra K M] [algebra L M]
  [is_scalar_tower F L M] [is_scalar_tower F K M] (P : E⟮K⟯) :
  point_hom (L⟶[F]M) (point_hom (K⟶[F]L) P) = point_hom ((L⟶[F]M).comp (K⟶[F]L)) P :=
by cases P; refl

/-- `E(K) → E(L)` is injective. -/
lemma point_hom.injective : function.injective $ @point_hom _ _ E _ _ _ _ _ _ _ _ φ :=
begin
  intros P Q hPQ,
  rcases ⟨P, Q⟩ with ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  any_goals { contradiction },
  { refl },
  { injection hPQ with hx hy,
    simp only,
    exact ⟨φ.to_ring_hom.injective hx, φ.to_ring_hom.injective hy⟩ }
end

/-- Canonical inclusion map `E(K) ↪ E(L)`. -/
def ιₚ : E⟮K⟯ →+ E⟮L⟯ := point_hom $ K⟶[F]L

end functoriality

----------------------------------------------------------------------------------------------------
/-! ## Galois module structure of `E(L)` -/

section galois

variables (σ τ : L ≃ₐ[K] L)

/-- The Galois action `Gal(L/K) ↷ E(L)`. -/
def point_gal : E⟮L⟯ → E⟮L⟯
| 0            := 0
| (some x y w) := some (σ • x) (σ • y)
begin
  apply_fun ((•) $ σ.restrict_scalars F) at w,
  simp only [smul_add, smul_mul', smul_pow'] at w,
  simp only [alg_equiv.smul_def, alg_equiv.commutes] at w,
  exact w
end

/-- `Gal(L/K) ↷ E(L)` is a scalar action. -/
instance : has_scalar (L ≃ₐ[K] L) E⟮L⟯ := ⟨point_gal⟩

/-- `Gal(L/K) ↷ E(L)` respects scalar one. -/
lemma point_gal.one_smul (P : E⟮L⟯) : (1 : L ≃ₐ[K] L) • P = P :=
by { cases P, { refl }, { simp only [has_scalar.smul, point_gal], exact ⟨rfl, rfl⟩ } }

/-- `Gal(L/K) ↷ E(L)` respects scalar multiplication. -/
lemma point_gal.mul_smul (P : E⟮L⟯) : (σ * τ) • P = σ • τ • P :=
by { cases P, { refl }, { simp only [has_scalar.smul, point_gal], exact ⟨rfl, rfl⟩ } }

/-- `Gal(L/K) ↷ E(L)` is a multiplicative action. -/
instance : mul_action (L ≃ₐ[K] L) E⟮L⟯ := ⟨point_gal.one_smul, point_gal.mul_smul⟩

/-- `Gal(L/K) ↷ E(L)` respects scaling on addition. -/
lemma point_gal.smul_add (P Q : E⟮L⟯) : σ • (P + Q) = σ • P + σ • Q :=
begin
  rcases ⟨P, Q⟩ with ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  any_goals { refl },
  { sorry }
end

/-- `Gal(L/K) ↷ E(L)` respects scaling on zero. -/
lemma point_gal.smul_zero : σ • 0 = (0 : E⟮L⟯) := rfl

/-- `Gal(L/K) ↷ E(L)` is a distributive multiplicative action. -/
instance : distrib_mul_action (L ≃ₐ[K] L) E⟮L⟯ := ⟨point_gal.smul_add, point_gal.smul_zero⟩

local notation E⟮L⟯^K := mul_action.fixed_points (L ≃ₐ[K] L) E⟮L⟯

/-- Zero is in `E(L)ᴷ`. -/
lemma point_gal.fixed.zero_mem : (0 : E⟮L⟯) ∈ E⟮L⟯^K := λ σ, rfl

/-- Addition is closed in `E(L)ᴷ`. -/
lemma point_gal.fixed.add_mem (P Q : E⟮L⟯) : P ∈ (E⟮L⟯^K) → Q ∈ (E⟮L⟯^K) → P + Q ∈ E⟮L⟯^K :=
λ hP hQ σ, by rw [smul_add, hP, hQ]

/-- Negation is closed in `E(L)ᴷ`. -/
lemma point_gal.fixed.neg_mem (P : E⟮L⟯) : P ∈ (E⟮L⟯^K) → -P ∈ E⟮L⟯^K :=
λ hP σ, by simpa only [neg_inj, smul_neg] using hP σ

/-- The Galois invariant subgroup `E(L)ᴷ` of `E(L)` fixed by `Gal(L/K)`. -/
def point_gal.fixed : add_subgroup E⟮L⟯ :=
⟨E⟮L⟯^K, point_gal.fixed.zero_mem, point_gal.fixed.add_mem, point_gal.fixed.neg_mem⟩

notation E⟮L`⟯^`K := @point_gal.fixed _ _ E K _ _ L _ _ _ _

variables [finite_dimensional K L] [is_galois K L]

/-- `E(L)ᴷ = ιₚ(E(K))`. -/
lemma point_gal.fixed.eq : (E⟮L⟯^K) = (ιₚ : E⟮K⟯ →+ E⟮L⟯).range :=
begin
  ext P,
  split,
  { intro hP,
    cases P with x y w,
    { apply add_subgroup.zero_mem },
    { change ∀ σ : L ≃ₐ[K] L, σ • some x y w = some x y w at hP,
      simp only [has_scalar.smul, point_gal, forall_and_distrib] at hP,
      have hx : x ∈ intermediate_field.fixed_field (⊤ : subgroup (L ≃ₐ[K] L)) := λ σ, hP.left σ,
      have hy : y ∈ intermediate_field.fixed_field (⊤ : subgroup (L ≃ₐ[K] L)) := λ σ, hP.right σ,
      rw [((@is_galois.tfae K _ L _ _ _).out 0 1).mp _inst_9, intermediate_field.mem_bot] at hx hy,
      change ∃ x' : K, (K⟶[F]L)x' = x at hx,
      change ∃ y' : K, (K⟶[F]L)y' = y at hy,
      rw [add_monoid_hom.mem_range],
      existsi [some hx.some hy.some _],
      { change some ((K⟶[F]L)hx.some) ((K⟶[F]L)hy.some) _ = some x y w,
        simp only [hx.some_spec, hy.some_spec],
        exact ⟨rfl, rfl⟩ },
      { apply_fun (K⟶[F]L) using (K⟶[F]L : K →+* L).injective,
        simp only [alg_hom.map_add, alg_hom.map_mul, alg_hom.map_pow, alg_hom.commutes],
        rw [hx.some_spec, hy.some_spec, w] } } },
  { intros hP σ,
    cases P with x y w,
    { refl },
    { rcases hP with ⟨_ | ⟨x', y', w'⟩, hQ⟩,
      { contradiction },
      { change some ((K↑L)x') ((K↑L) y') _ = some x y w at hQ,
        simp only at hQ,
        have hx : x ∈ set.range (K↑L) := exists.intro x' hQ.left,
        have hy : y ∈ set.range (K↑L) := exists.intro y' hQ.right,
        rw [← intermediate_field.mem_bot,
            ← ((@is_galois.tfae K _ L _ _ _).out 0 1).mp _inst_9] at hx hy,
        simp only [has_scalar.smul, point_gal],
        exact ⟨hx ⟨σ, subgroup.mem_top σ⟩, hy ⟨σ, subgroup.mem_top σ⟩⟩ } } }
end

/-- `Gal(L/K)` fixes `ιₚ(E(K))`. -/
lemma point_gal.fixed.smul (P : E⟮K⟯) : σ • ιₚ P = (ιₚ P : E⟮L⟯) :=
by { revert σ, change ιₚ P ∈ E⟮L⟯^K, rw [point_gal.fixed.eq], exact ⟨P, rfl⟩ }

end galois

----------------------------------------------------------------------------------------------------
/-! ## Isomorphism on `E(K)` induced by a linear change of variables -/

section change_of_variables

variables (u : Fˣ) (r s t : F)

/-- The function on `E(K)` induced by a linear change of variables
  `(x, y) ↦ (u²x + r, u³y + u²sx + t)` for some `u ∈ Rˣ` and some `r, s, t ∈ R`. -/
def cov.to_fun : (E.cov u r s t)⟮K⟯ → E⟮K⟯
| 0            := 0
| (some x y w) :=
some ((F↑K)u.val ^ 2 * x + (F↑K)r) ((F↑K)u.val ^ 3 * y + (F↑K)u.val ^ 2 * (F↑K)s * x + (F↑K)t)
begin
  have w_rw : ∀ a₁ a₂ a₃ a₄ a₆ v i : K,
    v ^ 6 * (y ^ 2 + i * a₁ * x * y + i ^ 3 * a₃ * y)
    - v ^ 6 * (x ^ 3 + i ^ 2 * a₂ * x ^ 2 + i ^ 4 * a₄ * x + i ^ 6 * a₆)
    = v ^ 6 * y ^ 2 + v ^ 5 * (v * i) * a₁ * x * y + v ^ 3 * (v * i) ^ 3 * a₃ * y - v ^ 6 * x ^ 3
      - v ^ 4 * (v * i) ^ 2 * a₂ * x ^ 2 - v ^ 2 * (v * i) ^ 4 * a₄ * x - (v * i) ^ 6 * a₆ :=
  by { intros, ring1 },
  apply_fun ((*) ((F↑K)u.val ^ 6)) at w,
  simp only [cov, algebra.id.map_eq_self] at w,
  simp only [map_neg, map_add, map_sub, map_mul, map_pow] at w,
  rw [← sub_eq_zero, w_rw, ← map_mul, u.val_inv] at w,
  simp only [map_one, map_bit0, map_bit1] at w,
  rw [← sub_eq_zero, ← w],
  ring1
end

/-- The inverse function on `E(K)` induced by a linear change of variables
  `(x, y) ↦ ((u⁻¹)²(x - r), (u⁻¹)³(y - sx + rs - t))` for some `u ∈ Rˣ` and some `r, s, t ∈ R`. -/
def cov.inv_fun : E⟮K⟯ → (E.cov u r s t)⟮K⟯
| 0            := 0
| (some x y w) :=
some ((F↑K)u.inv ^ 2 * (x - (F↑K)r)) ((F↑K)u.inv ^ 3 * (y - (F↑K)s * x + (F↑K)r * (F↑K)s - (F↑K)t))
begin
  apply_fun ((*) ((F↑K)u.inv ^ 6)) at w,
  rw [← sub_eq_zero] at w,
  simp only [cov, algebra.id.map_eq_self],
  simp only [map_neg, map_add, map_sub, map_mul, map_pow],
  simp only [map_one, map_bit0, map_bit1],
  rw [← sub_eq_zero, ← w],
  ring1
end

/-- `(x, y) ↦ ((u⁻¹)²(x - r), (u⁻¹)³(y - sx + rs - t))` is a left inverse of
  `(x, y) ↦ (u²x + r, u³y + u²sx + t)` on `E(K)`. -/
lemma cov.left_inv (P : (E.cov u r s t)⟮K⟯) : cov.inv_fun u r s t (cov.to_fun u r s t P) = P :=
begin
  cases P with x y,
  { refl },
  { have x_rw : ∀ r v i : K, i ^ 2 * (v ^ 2 * x + r - r) = (i * v) ^ 2 * x := by { intros, ring1 },
    have y_rw : ∀ r s t v i : K,
      i ^ 3 * (v ^ 3 * y + v ^ 2 * s * x + t - s * (v ^ 2 * x + r) + r * s - t) = (i * v) ^ 3 * y :=
    by { intros, ring1 },
    simp only [cov.to_fun, cov.inv_fun],
    rw [x_rw, y_rw, ← map_mul, u.inv_val],
    simp only [one_mul, one_pow, map_one],
    exact ⟨rfl, rfl⟩ }
end

/-- `(x, y) ↦ ((u⁻¹)²(x - r), (u⁻¹)³(y - sx + rs - t))` is a right inverse of
  `(x, y) ↦ (u²x + r, u³y + u²sx + t)` on `E(K)`. -/
lemma cov.right_inv (P : E⟮K⟯) : cov.to_fun u r s t (cov.inv_fun u r s t P) = P :=
begin
  cases P with x y,
  { refl },
  { have x_rw : ∀ r v i : K, v ^ 2 * (i ^ 2 * (x - r)) + r = (v * i) ^ 2 * (x - r) + r :=
    by { intros, ring1 },
    have y_rw : ∀ r s t v i : K,
      v ^ 3 * (i ^ 3 * (y - s * x + r * s - t)) + v ^ 2 * s * (i ^ 2 * (x - r)) + t
      = (v * i) ^ 3 * y + ((v * i) ^ 2 - (v * i) ^ 3) * (s * x - r * s) + (1 - (v * i) ^ 3) * t :=
    by { intros, ring1 },
    simp only [cov.to_fun, cov.inv_fun],
    rw [x_rw, y_rw, ← map_mul, u.val_inv],
    simp only [sub_self, sub_add_cancel, add_monoid.add_zero, zero_mul, one_mul, one_pow, map_one],
    exact ⟨rfl, rfl⟩ }
end

/-- `(x, y) ↦ (u²x + r, u³y + u²sx + t)` is a group homomorphism on `E(K)`. -/
lemma cov.map_add (P Q : (E.cov u r s t)⟮K⟯) :
  cov.to_fun u r s t (P + Q) = cov.to_fun u r s t P + cov.to_fun u r s t Q :=
begin
  rcases ⟨P, Q⟩ with ⟨⟨_ | _⟩, ⟨_ | _⟩⟩,
  any_goals { refl },
  { sorry }
end

/-- `(x, y) ↦ (u²x + r, u³y + u²sx + t)` is a group isomorphism on `E(K)`. -/
def cov.equiv_add : (E.cov u r s t)⟮K⟯ ≃+ E⟮K⟯ :=
{ to_fun    := cov.to_fun u r s t,
  inv_fun   := cov.inv_fun u r s t,
  left_inv  := cov.left_inv u r s t,
  right_inv := cov.right_inv u r s t,
  map_add'  := cov.map_add u r s t }

/-- Completing a square is a group isomorphism on `E(K)`. -/
def covₘ.equiv_add [invertible (2 : F)] : E.covₘ⟮K⟯ ≃+ E⟮K⟯ :=
cov.equiv_add 1 0 (-⅟2 * E.a₁) (-⅟2 * E.a₃)

end change_of_variables

----------------------------------------------------------------------------------------------------

end EllipticCurve
