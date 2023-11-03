/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import data.complex.basic
import measure_theory.integral.circle_integral
/-!
# Circle integral transform

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the circle integral transform of a function `f` with complex domain. This is
defined as $(2πi)^{-1}\frac{f(x)}{x-w}$ where `x` moves along a circle. We then prove some basic
facts about these functions.

These results are useful for proving that the uniform limit of a sequence of holomorphic functions
is holomorphic.

-/

open set measure_theory metric filter function
open_locale interval real

noncomputable theory

variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] (R : ℝ) (z w : ℂ)

namespace complex

/-- Given a function `f : ℂ → E`, `circle_transform R z w f` is the functions mapping `θ` to
`(2 * ↑π * I)⁻¹ • deriv (circle_map z R) θ • ((circle_map z R θ) - w)⁻¹ • f (circle_map z R θ)`.

If `f` is differentiable and `w` is in the interior of the ball, then the integral from `0` to
`2 * π` of this gives the value `f(w)`. -/
def circle_transform (f : ℂ → E) (θ : ℝ) : E :=
(2 * ↑π * I)⁻¹ • deriv (circle_map z R) θ • ((circle_map z R θ) - w)⁻¹ • f (circle_map z R θ)

/-- The derivative of `circle_transform` w.r.t `w`.-/
def circle_transform_deriv (f : ℂ → E) (θ : ℝ) : E :=
(2 * ↑π * I)⁻¹ • deriv (circle_map z R) θ • ((circle_map z R θ - w) ^ 2)⁻¹ • f (circle_map z R θ)

lemma circle_transform_deriv_periodic (f : ℂ → E) :
  periodic (circle_transform_deriv R z w f) (2 * π) :=
begin
  have := periodic_circle_map,
  simp_rw periodic at *,
  intro x,
  simp_rw [circle_transform_deriv, this],
  congr' 2,
  simp [this],
end

lemma circle_transform_deriv_eq (f : ℂ → E) :
  circle_transform_deriv R z w f =
  (λ θ, (circle_map z R θ - w)⁻¹ • (circle_transform R z w f θ)) :=
begin
  ext,
  simp_rw [circle_transform_deriv, circle_transform, ←mul_smul, ←mul_assoc],
  ring_nf,
  rw inv_pow,
  congr,
  ring,
end

lemma integral_circle_transform [complete_space E] (f : ℂ → E) :
  ∫_{0}^{2 * π} θ, circle_transform R z w f θ =
  (2 * ↑π * I)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z :=
begin
  simp_rw [circle_transform, circle_integral, deriv_circle_map, circle_map],
  simp,
end

lemma continuous_circle_transform {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
  (hf : continuous_on f $ sphere z R) (hw : w ∈ ball z R) :
  continuous (circle_transform R z w f) :=
begin
  apply_rules [continuous.smul, continuous_const],
  simp_rw deriv_circle_map,
  apply_rules [continuous.mul, (continuous_circle_map 0 R), continuous_const],
  { apply continuous_circle_map_inv hw },
  { apply continuous_on.comp_continuous hf (continuous_circle_map z R),
    exact (λ _, (circle_map_mem_sphere _ hR.le) _) },
end

lemma continuous_circle_transform_deriv {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
  (hf : continuous_on f (sphere z R)) (hw : w ∈ ball z R) :
  continuous (circle_transform_deriv R z w f) :=
begin
  rw circle_transform_deriv_eq,
  exact (continuous_circle_map_inv hw).smul (continuous_circle_transform hR hf hw),
end

/--A useful bound for circle integrals (with complex codomain)-/
def circle_transform_bounding_function (R : ℝ) (z : ℂ) (w : ℂ × ℝ) : ℂ :=
circle_transform_deriv R z w.1 (λ x, 1) w.2

lemma continuous_on_prod_circle_transform_function {R r : ℝ} (hr : r < R) {z : ℂ} :
  continuous_on (λ w : ℂ × ℝ, ((circle_map z R w.snd - w.fst)⁻¹) ^ 2) (closed_ball z r ×ˢ univ) :=
begin
  simp_rw ←one_div,
  apply_rules [continuous_on.pow, continuous_on.div, continuous_on_const],
  refine ((continuous_circle_map z R).continuous_on.comp continuous_on_snd (λ _, and.right)).sub
    (continuous_on_id.comp continuous_on_fst (λ _, and.left)),
  simp only [mem_prod, ne.def, and_imp, prod.forall],
  intros a b ha hb,
  have ha2 : a ∈ ball z R, by {simp at *, linarith,},
  exact (sub_ne_zero.2 (circle_map_ne_mem_ball ha2 b)),
end

lemma continuous_on_abs_circle_transform_bounding_function {R r : ℝ} (hr : r < R) (z : ℂ) :
  continuous_on (abs ∘ (λ t, circle_transform_bounding_function R z t)) (closed_ball z r ×ˢ univ) :=
begin
  have : continuous_on (circle_transform_bounding_function R z) (closed_ball z r ×ˢ (⊤ : set ℝ)),
  { apply_rules [continuous_on.smul, continuous_on_const],
    simp only [deriv_circle_map],
    have c := (continuous_circle_map 0 R).continuous_on,
    apply_rules [continuous_on.mul, c.comp continuous_on_snd (λ _, and.right), continuous_on_const],
    simp_rw ←inv_pow,
    apply continuous_on_prod_circle_transform_function hr, },
  refine continuous_abs.continuous_on.comp this _,
  show maps_to _ _ (⊤ : set ℂ),
  simp [maps_to],
end

lemma abs_circle_transform_bounding_function_le {R r : ℝ} (hr : r < R) (hr' : 0 ≤ r) (z : ℂ) :
  ∃ x : closed_ball z r ×ˢ [0, 2 * π],
  ∀ y : closed_ball z r ×ˢ [0, 2 * π],
  abs (circle_transform_bounding_function R z y) ≤ abs (circle_transform_bounding_function R z x) :=
begin
  have cts := continuous_on_abs_circle_transform_bounding_function hr z,
  have comp : is_compact (closed_ball z r ×ˢ [0, 2 * π]),
  { apply_rules [is_compact.prod, proper_space.is_compact_closed_ball z r, is_compact_uIcc], },
  have none : (closed_ball z r ×ˢ [0, 2 * π]).nonempty :=
    (nonempty_closed_ball.2 hr').prod nonempty_uIcc,
  have := is_compact.exists_forall_ge comp none (cts.mono
    (by { intro z, simp only [mem_prod, mem_closed_ball, mem_univ, and_true, and_imp], tauto })),
  simpa only [set_coe.forall, subtype.coe_mk, set_coe.exists],
end

/-- The derivative of a `circle_transform` is locally bounded. -/
lemma circle_transform_deriv_bound {R : ℝ} (hR : 0 < R) {z x : ℂ} {f : ℂ → ℂ}
  (hx : x ∈ ball z R) (hf : continuous_on f (sphere z R)) :
  ∃ (B ε : ℝ), 0 < ε ∧ ball x ε ⊆ ball z R ∧
  (∀ (t : ℝ) (y ∈ ball x ε), ‖circle_transform_deriv R z y f t‖ ≤ B) :=
begin
  obtain ⟨r, hr, hrx⟩ := exists_lt_mem_ball_of_mem_ball hx,
  obtain ⟨ε', hε', H⟩ := exists_ball_subset_ball hrx,
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, hab⟩ := abs_circle_transform_bounding_function_le hr
    (pos_of_mem_ball hrx).le z,
  let V : ℝ → (ℂ → ℂ) := λ θ w, circle_transform_deriv R z w (λ x, 1) θ,
  have funccomp : continuous_on (λ r , abs (f r)) (sphere z R),
  by { have cabs : continuous_on abs ⊤ := by apply continuous_abs.continuous_on,
    apply cabs.comp (hf), rw maps_to, tauto,},
  have sbou := is_compact.exists_forall_ge (is_compact_sphere z R)
    (normed_space.sphere_nonempty.2 hR.le) funccomp,
  obtain ⟨X, HX, HX2⟩ := sbou,
  refine ⟨abs (V b a) * abs (f X), ε' , hε', subset.trans H (ball_subset_ball hr.le), _ ⟩,
  intros y v hv,
  obtain ⟨y1, hy1, hfun⟩ := periodic.exists_mem_Ico₀
    (circle_transform_deriv_periodic R z v f) real.two_pi_pos y,
  have hy2: y1 ∈ [0, 2*π], by {convert (Ico_subset_Icc_self hy1),
    simp [uIcc_of_le real.two_pi_pos.le]},
  have := mul_le_mul (hab ⟨⟨v, y1⟩, ⟨ball_subset_closed_ball (H hv), hy2⟩⟩)
   (HX2 (circle_map z R y1) (circle_map_mem_sphere z hR.le y1))
   (complex.abs.nonneg _) (complex.abs.nonneg _),
  simp_rw hfun,
  simp only [circle_transform_bounding_function, circle_transform_deriv, V, norm_eq_abs,
    algebra.id.smul_eq_mul, deriv_circle_map, map_mul, abs_circle_map_zero, abs_I, mul_one,
    ←mul_assoc, mul_inv_rev, inv_I, abs_neg, abs_inv, abs_of_real, one_mul, abs_two, abs_pow,
    mem_ball, gt_iff_lt, subtype.coe_mk, set_coe.forall, mem_prod, mem_closed_ball, and_imp,
    prod.forall, normed_space.sphere_nonempty, mem_sphere_iff_norm] at *,
  exact this,
end

end complex
