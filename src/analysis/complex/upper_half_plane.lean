/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/

import linear_algebra.special_linear_group
import analysis.complex.basic
import group_theory.group_action.defs
import linear_algebra.general_linear_group


/-!
# The upper half plane and its automorphisms

This file defines `upper_half_plane` to be the upper half plane in `ℂ`.

We furthermore equip it with the structure of an `GL_pos 2 ℝ` action by
fractional linear transformations.

We define the notation `ℍ` for the upper half plane available in the locale
`upper_half_plane` so as not to conflict with the quaternions.
-/

noncomputable theory

open matrix matrix.special_linear_group

open_locale classical big_operators matrix_groups

local attribute [instance] fintype.card_fin_even

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

/-- The open upper half plane -/
@[derive [topological_space, λ α, has_coe α ℂ]]
def upper_half_plane := {point : ℂ // 0 < point.im}

localized "notation `ℍ` := upper_half_plane" in upper_half_plane

namespace upper_half_plane

instance : inhabited ℍ := ⟨⟨complex.I, by simp⟩⟩

/-- Imaginary part -/
def im (z : ℍ) := (z : ℂ).im

/-- Real part -/
def re (z : ℍ) := (z : ℂ).re

@[simp] lemma coe_im (z : ℍ) : (z : ℂ).im = z.im := rfl

@[simp] lemma coe_re (z : ℍ) : (z : ℂ).re = z.re := rfl

lemma im_pos (z : ℍ) : 0 < z.im := z.2

lemma im_ne_zero (z : ℍ) : z.im ≠ 0 := z.im_pos.ne'

lemma ne_zero (z : ℍ) : (z : ℂ) ≠ 0 :=
mt (congr_arg complex.im) z.im_ne_zero

lemma norm_sq_pos (z : ℍ) : 0 < complex.norm_sq (z : ℂ) :=
by { rw complex.norm_sq_pos, exact z.ne_zero }

lemma norm_sq_ne_zero (z : ℍ) : complex.norm_sq (z : ℂ) ≠ 0 := (norm_sq_pos z).ne'

/-- Numerator of the formula for a fractional linear transformation -/
@[simp] def num (g : GL_pos (fin 2) ℝ) (z : ℍ) : ℂ := (↑ₘg 0 0 : ℝ) * z + (↑ₘg 0 1 : ℝ)

/-- Denominator of the formula for a fractional linear transformation -/
@[simp] def denom (g :  GL_pos (fin 2) ℝ) (z : ℍ) : ℂ := (↑ₘg 1 0 : ℝ) * z + (↑ₘg 1 1 : ℝ)

lemma linear_ne_zero (cd : fin 2 → ℝ) (z : ℍ) (h : cd ≠ 0) : (cd 0 : ℂ) * z + cd 1 ≠ 0 :=
begin
  contrapose! h,
  have : cd 0 = 0, -- we will need this twice
  { apply_fun complex.im at h,
    simpa only [z.im_ne_zero, complex.add_im, add_zero, coe_im, zero_mul, or_false,
      complex.of_real_im, complex.zero_im, complex.mul_im, mul_eq_zero] using h, },
  simp only [this, zero_mul, complex.of_real_zero, zero_add, complex.of_real_eq_zero] at h,
  ext i,
  fin_cases i; assumption,
end

lemma denom_ne_zero (g : GL_pos (fin 2) ℝ) (z : ℍ) : denom g z ≠ 0 :=
begin
  intro H,
  have DET:= (mem_GL_pos _).1 g.property,
  have hz:=z.property,
  simp only [subtype.val_eq_coe, general_linear_group.coe_det_apply] at DET,
  have H1 : (↑ₘg 1 0 : ℝ) = 0 ∨ z.im = 0, by simpa using congr_arg complex.im H,
  cases H1,
  {simp [H1, complex.of_real_zero, denom, coe_fn_eq_coe, zero_mul, zero_add,
    complex.of_real_eq_zero] at H,
  have:= matrix.det_fin_two g,
  simp  [coe_fn_coe_base', subtype.val_eq_coe, coe_im, general_linear_group.coe_fn_eq_coe] at *,
  rw this at DET,
  simp  [H, H1, mul_zero, sub_zero, lt_self_iff_false] at DET,
  exact DET,},
  change z.im > 0 at hz,
  linarith,
end

lemma norm_sq_denom_pos (g : GL_pos (fin 2) ℝ) (z : ℍ) : 0 < complex.norm_sq (denom g z) :=
complex.norm_sq_pos.mpr (denom_ne_zero g z)

lemma norm_sq_denom_ne_zero (g :  GL_pos (fin 2) ℝ) (z : ℍ) : complex.norm_sq (denom g z) ≠ 0 :=
ne_of_gt (norm_sq_denom_pos g z)

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smul_aux' (g :  GL_pos (fin 2) ℝ) (z : ℍ) : ℂ := num g z / denom g z

lemma smul_aux'_im (g :  GL_pos (fin 2) ℝ) (z : ℍ) :
  (smul_aux' g z).im = ((det ↑ₘg) * z.im) / (denom g z).norm_sq :=
begin
  rw [smul_aux', complex.div_im],
  set NsqBot := (denom g z).norm_sq,
  have : NsqBot ≠ 0,
  { simp only [denom_ne_zero g z, monoid_with_zero_hom.map_eq_zero, ne.def, not_false_iff], },
  field_simp [smul_aux'],
  ring_nf,
  have:= matrix.det_fin_two(g : GL (fin 2) ℝ),
  simp at this,
  rw this,
  ring,
  exact real.comm_ring,
end

/-- Fractional linear transformation,  also known as the Moebius transformation -/
def smul_aux (g :  GL_pos (fin 2) ℝ) (z : ℍ) : ℍ :=
  ⟨smul_aux' g z,
    by { rw smul_aux'_im,
    simp,
    have h1:= div_pos z.im_pos (complex.norm_sq_pos.mpr (denom_ne_zero g z)),
    have h2:=g.property,
    simp at *,
    have:= mul_pos h2 h1,
    convert this,
    simp [coe_fn_coe_base'],
    ring, }⟩

lemma denom_cocycle (x y : GL_pos (fin 2) ℝ) (z : ℍ) :
  denom (x * y) z = denom x (smul_aux y z) * denom y z :=
begin
  change _ = (_ * (_ / _) + _) * _,
  field_simp [denom_ne_zero, -denom, -num],
  simp [coe_fn_coe_base', matrix.mul, dot_product, fin.sum_univ_succ],
  ring
end

lemma mul_smul' (x y :  GL_pos (fin 2) ℝ) (z : ℍ) :
  smul_aux (x * y) z = smul_aux x (smul_aux y z) :=
begin
  ext1,
  change _ / _ = (_ * (_ / _) + _)  * _,
  rw denom_cocycle,
  field_simp [denom_ne_zero, -denom, -num],
  simp [coe_fn_coe_base',matrix.mul, dot_product, fin.sum_univ_succ],
  ring
end

/-- The action of ` GL_pos 2 ℝ` on the upper half-plane by fractional linear transformations. -/
instance : mul_action  (GL_pos (fin 2) ℝ) ℍ :=
{ smul := smul_aux,
  one_smul := λ z, by { ext1, change _ / _ = _,
   simp [coe_fn_coe_base']  },
  mul_smul := mul_smul' }

section modular_scalar_towers

variable (Γ : subgroup (special_linear_group (fin 2) ℤ))

instance SL_action {R : Type*} [comm_ring R] [algebra R ℝ] : mul_action SL(2, R) ℍ :=
 mul_action.comp_hom ℍ  (monoid_hom.comp (special_linear_group.to_GL_pos)
 (map (algebra_map R ℝ)) )

instance : has_coe SL(2,ℤ) (GL_pos (fin 2) ℝ) := ⟨λ g , ((g : SL(2, ℝ)) : (GL_pos (fin 2) ℝ))⟩

instance SL_on_GL_pos : has_scalar SL(2,ℤ) (GL_pos (fin 2) ℝ) := ⟨λ s g, s * g⟩

lemma SL_on_GL_pos_smul_apply (s : SL(2,ℤ)) (g : (GL_pos (fin 2) ℝ) ) (z : ℍ) :
  (s • g) • z = ( (s : GL_pos (fin 2) ℝ) * g) • z := rfl

instance SL_to_GL_tower : is_scalar_tower SL(2,ℤ) (GL_pos (fin 2) ℝ) ℍ :=
 {smul_assoc := by {intros s g z, rw SL_on_GL_pos_smul_apply, simp, apply mul_smul',},}

instance subgroup_GL_pos : has_scalar Γ (GL_pos (fin 2) ℝ) := ⟨λ s g, s * g⟩

lemma subgroup_on_GL_pos_smul_apply (s : Γ) (g : (GL_pos (fin 2) ℝ) ) (z : ℍ) :
  (s • g) • z = ( (s : GL_pos (fin 2) ℝ) * g) • z := rfl

instance subgroup_on_GL_pos : is_scalar_tower Γ (GL_pos (fin 2) ℝ) ℍ :=
 {smul_assoc :=
  by {intros s g z, rw subgroup_on_GL_pos_smul_apply, simp only [coe_coe], apply mul_smul',},}

instance subgroup_SL : has_scalar Γ SL(2,ℤ) :=⟨λ s g, s * g⟩

lemma subgroup_on_SL_apply (s : Γ) (g : SL(2,ℤ) ) (z : ℍ) :
  (s • g) • z = ( (s : SL(2, ℤ)) * g) • z := rfl

instance subgroup_to_SL_tower : is_scalar_tower Γ SL(2,ℤ) ℍ :=
 {smul_assoc := by {intros s g z, rw subgroup_on_SL_apply, apply upper_half_plane.SL_action.3,},}

end modular_scalar_towers

@[simp] lemma coe_smul (g : GL_pos (fin 2) ℝ) (z : ℍ) : ↑(g • z) = num g z / denom g z := rfl
@[simp] lemma re_smul (g : GL_pos (fin 2) ℝ) (z : ℍ) : (g • z).re = (num g z / denom g z).re := rfl

lemma im_smul (g : GL_pos (fin 2) ℝ) (z : ℍ) : (g • z).im = (num g z / denom g z).im := rfl

lemma im_smul_eq_div_norm_sq (g : GL_pos (fin 2) ℝ) (z : ℍ) :
  (g • z).im = (det ↑ₘg * z.im) / (complex.norm_sq (denom g z)) :=
smul_aux'_im g z

@[simp] lemma neg_smul (g :  GL_pos (fin 2) ℝ) (z : ℍ) : -g • z = g • z :=
begin
  ext1,
  change _ / _ = _ / _,
  field_simp [denom_ne_zero, -denom, -num],
  simp [coe_GL_pos_neg, coe_fn_coe_base'],
  ring_nf,
  end

variable (Γ : subgroup (special_linear_group (fin 2) ℤ))

@[simp]lemma sl_moeb (A: SL(2,ℤ)) (z : ℍ) : A • z = (A : (GL_pos (fin 2) ℝ)) • z := rfl
@[simp]lemma subgroup_moeb (A: Γ) (z : ℍ) : A • z = (A : (GL_pos (fin 2) ℝ)) • z := rfl
@[simp]lemma subgroup_to_sl_moeb (A: Γ) (z : ℍ) : A • z = (A : SL(2,ℤ)) • z := rfl

@[simp] lemma SL_neg_smul (g : SL(2,ℤ)) (z : ℍ) : -g • z = g • z :=
begin
simp [coe_GL_pos_neg],
end

end upper_half_plane
