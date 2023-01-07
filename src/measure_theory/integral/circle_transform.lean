/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import data.complex.basic
import measure_theory.integral.circle_integral
/-!
# Circle integral transform

In this file we define the circle integral transform of a function `f` with complex domain. This is
defined as $(2πi)^{-1}\frac{f(x)}{x-w}$ where `x` moves along a circle. We then prove some basic
facts about these functions.

These results are useful for proving that the uniform limit of a sequence of holomorphic functions
is holomorphic.

-/

open topological_space set measure_theory interval_integral metric filter function complex
open_locale interval real nnreal ennreal topological_space big_operators

noncomputable theory

variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] (R : ℝ) (z w : ℂ)

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
  ∫ (θ : ℝ) in 0..2 * π, circle_transform R z w f θ =
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
 continuous_on (λ (w : ℂ × ℝ), ((circle_map z R w.snd - w.fst)⁻¹) ^ 2)
  ((closed_ball z r) ×ˢ (⊤ : set ℝ)) :=
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
  continuous_on (abs ∘ (λ t, circle_transform_bounding_function R z t))
  ((closed_ball z r) ×ˢ (⊤ : set ℝ) : set $ ℂ × ℝ) :=
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
  ∃ (x : ((closed_ball z r) ×ˢ [0, 2 * π] : set $ ℂ × ℝ)),
  ∀ (y : ((closed_ball z r) ×ˢ [0, 2 * π] : set $ ℂ × ℝ)),
  abs (circle_transform_bounding_function R z y) ≤ abs (circle_transform_bounding_function R z x) :=
begin
  have cts := continuous_on_abs_circle_transform_bounding_function hr z,
  have comp : is_compact (((closed_ball z r) ×ˢ [0, 2 * π]) : set (ℂ × ℝ)),
  { apply_rules [is_compact.prod, proper_space.is_compact_closed_ball z r, is_compact_interval], },
  have none := (nonempty_closed_ball.2 hr').prod nonempty_interval,
  simpa using is_compact.exists_forall_ge comp none (cts.mono (by { intro z, simp, tauto })),
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
    simp [interval_of_le real.two_pi_pos.le]},
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

/--Cauchy integral form of a function at `z` in a disk of radius `R`-/
def circle_integral_form [complete_space E] (R : ℝ) (z : ℂ) (f : ℂ → E): (ℂ → E) :=
λ w, (2 * π * I : ℂ)⁻¹ • (∮ z in C(z, R), (z - w)⁻¹ • f z)

lemma circle_intgral_form_eq_int [complete_space E] (R : ℝ) (z : ℂ) (f : ℂ → E) :
  circle_integral_form R z f = λ w, ∫ (θ : ℝ) in 0..2 * π, (circle_transform R z w f) θ :=
by simp_rw [circle_transform, circle_integral_form, circle_integral,
  interval_integral.integral_smul]


lemma circle_transform_circle_int [complete_space E] (R : ℝ) (z w : ℂ) (f : ℂ → E) :
  ∫ (θ : ℝ) in 0..2 * π, circle_transform R z w f θ =
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z :=
begin
  simp_rw [circle_transform, circle_integral,deriv_circle_map, circle_map],
  simp only [real_smul, nsmul_eq_mul, nat.cast_bit0, nat.cast_one, one_div,
    interval_integral.integral_smul, zero_add],
end

lemma circle_transform_has_deriv_at (R : ℝ) (z : ℂ) (f : ℂ → ℂ) :
  ∀ (t : ℝ) y ∈ ball z R, has_deriv_at (λ y, (circle_transform R z y f) t)
  ((circle_transform_deriv R z y f) t) y :=
begin
  intros y x hx,
  simp only [circle_transform, circle_transform_deriv, algebra.id.smul_eq_mul,
   ←mul_assoc, deriv_circle_map],
  apply_rules [has_deriv_at.mul_const, has_deriv_at.const_mul],
  have H : has_deriv_at (λ (y_1 : ℂ), (circle_map z R y - y_1)) (-1 ) x,
   by {apply has_deriv_at.const_sub, apply has_deriv_at_id,},
  have hfin := has_deriv_at.inv H (sub_ne_zero.2 (circle_map_ne_mem_ball hx y)),
  simp only [one_div, neg_neg] at hfin,
  exact hfin,
end

lemma circle_transform_ae_measurable {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R)
  (z x : ℂ) (hx : x ∈ ball z R) (hf : continuous_on f (sphere z R)) :
  ∀ᶠ y in 𝓝 x, ae_measurable (( λ w, (λ θ, (circle_transform R z w f θ))) y)
  (volume.restrict (Ι 0 (2 * π))):=
begin
  rw filter.eventually_iff_exists_mem,
  obtain ⟨ε', He, HB⟩ := (exists_ball_subset_ball hx),
  refine  ⟨(ball x ε'), _⟩,
  simp only [metric.ball_mem_nhds x He, exists_true_left],
  intros y hy,
  exact continuous_on.ae_measurable ((continuous_circle_transform hR hf (HB hy))).continuous_on
    (measurable_set_interval_oc),
end

lemma circle_interval_integrable {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R)
  (z x : ℂ) (hx : x ∈ ball z R) (hf : continuous_on f (sphere z R)) :
  interval_integrable ((λ w, (λ θ, (circle_transform R z w f θ))) x) volume 0 (2 * π) :=
(continuous_on.interval_integrable) (continuous_circle_transform hR hf hx).continuous_on

lemma circle_transform_deriv_ae_measurable {R : ℝ} (hR : 0 < R)
  (z x : ℂ) (hx : x ∈ ball z R) (f : ℂ → ℂ) (hf : continuous_on f (sphere z R)) :
   ae_measurable (( λ w θ, (circle_transform_deriv R z w f θ)) x)
  (volume.restrict (Ι 0 (2 * π))) :=
continuous_on.ae_measurable ((continuous_circle_transform_deriv hR hf (hx))).continuous_on
    (measurable_set_interval_oc)

/--The `circle_integral_form` of a function, which is continuous on `sphere z R` is differentiable
on `ball z R`. -/
lemma circle_integral_form_differentiable_on {R : ℝ} {f : ℂ → ℂ} (hR : 0 < R) (z : ℂ)
  (hf : continuous_on f (sphere z R)) :
  differentiable_on ℂ (circle_integral_form R z f) (ball z R) :=
begin
  simp_rw [circle_integral_form, ←circle_transform_circle_int R z _ f,
    differentiable_on, differentiable_within_at],
  intros x hx,
  have h4R : 0 < (4⁻¹*R), by {apply left.mul_pos, rw inv_pos, linarith, apply hR,},
  set F : ℂ → ℝ → ℂ := λ w, (λ θ, (circle_transform R z w f θ)),
  set F' : ℂ → ℝ → ℂ := λ w, circle_transform_deriv R z w f,
  have hF_meas : ∀ᶠ y in 𝓝 x, ae_strongly_measurable (F y) (volume.restrict (Ι 0 (2 * π))),
  by {simp_rw [F, _root_.ae_strongly_measurable_iff_ae_measurable],
    exact circle_transform_ae_measurable hR z x hx hf},
  have hF_int : interval_integrable (F x) volume 0 (2 * π),
  by {simp_rw F,
    apply circle_interval_integrable hR z x hx hf},
  have hF'_meas : ae_strongly_measurable (F' x) (volume.restrict (Ι 0 (2 * π))),
  by {simp_rw [F', _root_.ae_strongly_measurable_iff_ae_measurable],
    exact circle_transform_deriv_ae_measurable hR z x hx f hf},
  have BOU := circle_transform_deriv_bound hR hx hf,
  obtain ⟨bound, ε, hε ,h_ball, h_boun⟩ := BOU,
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε , ∥F' y t∥ ≤ bound,
  by {apply eventually_of_forall,
    exact (λ _,(λ _, by {apply h_boun})) },
  have bound_integrable : interval_integrable (λ _, bound) volume 0 (2 * π),
  by {exact _root_.interval_integrable_const, },
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε,
  has_deriv_at (λ y, F y t) (F' y t) y,
  by {simp_rw [F, F', circle_transform, circle_transform_deriv],
    have := circle_transform_has_deriv_at R z f,
    apply eventually_of_forall,
    simp_rw [circle_transform, circle_transform_deriv] at this,
    intros y hy x hx,
    rw (interval_oc_of_le real.two_pi_pos.le) at hy,
    have hy2 : y ∈ [0, 2*π], by {convert (Ioc_subset_Icc_self hy),
      simp [interval_of_le real.two_pi_pos.le]},
    exact this y x (h_ball hx)},
  have := interval_integral.has_deriv_at_integral_of_dominated_loc_of_deriv_le hε hF_meas hF_int
    hF'_meas h_bound bound_integrable h_diff,
  simp only [F, has_deriv_at, has_deriv_at_filter, has_fderiv_within_at, mem_ball, zero_lt_mul_left,
    inv_pos, zero_lt_bit0, zero_lt_one, norm_eq_abs,
    interval_integral.interval_integrable_const] at *,
  exact ⟨continuous_linear_map.smul_right (1 : ℂ →L[ℂ] ℂ)
    (interval_integral (F' x) 0 (2 * π) volume), (has_fderiv_at_filter.mono this.2 inf_le_left)⟩,
end

/--The differece of the `circle_transform` of two functions `f,g` is the `circle_transform` of the
difference `f - g`. -/
lemma circle_transform_sub (R : ℝ) (f g : ℂ → ℂ) (z w : ℂ) (θ : ℝ) :
  ((circle_transform R z w f ) θ) - ((circle_transform R z w g) θ) =
  (circle_transform R z w (f - g) θ) :=
begin
  simp only [circle_transform, mul_inv_rev, inv_I, neg_mul, deriv_circle_map,
    algebra.id.smul_eq_mul, neg_sub_neg, pi.sub_apply],
  ring,
end

lemma circle_transform_of_bound_is_bound {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) (z w : ℂ) (r : ℝ)
  (h : ∀ (x : sphere z R), (complex.abs (f x) ≤ abs r)) (θ : ℝ) :
  complex.abs (circle_transform R z w f θ) ≤ complex.abs (circle_transform R z w (λ x, r) θ) :=
begin
  simp only [circle_transform, abs_of_real, mul_one, algebra.id.smul_eq_mul, abs_I, abs_two,
    ←mul_assoc, deriv_circle_map, abs_circle_map_zero, mul_inv_rev, inv_I, absolute_value.map_neg,
    absolute_value.map_mul, map_inv₀, one_mul],
  apply_rules [monotone_mul_left_of_nonneg, mul_nonneg, mul_nonneg],
  repeat {simp_rw inv_nonneg},
  swap,
  nlinarith,
  repeat {apply _root_.abs_nonneg},
  { simp only [map_nonneg] },
  { simp only [abs_of_real, set_coe.forall, subtype.coe_mk] at h,
    exact h _ (circle_map_mem_sphere z hR.le θ)},
end

/--The `circle_transform` of a function is integrable. -/
lemma circle_transform_integrable {R : ℝ} {F : ℂ → ℂ} (hR : 0 < R) (z : ℂ)
  (F_cts : continuous_on F (sphere z R)) (w : ball z R) :
  integrable (circle_transform R z w F) (volume.restrict (Ioc 0 (2*π))) :=
begin
  apply integrable_on.integrable,
  rw ←(interval_integrable_iff_integrable_Ioc_of_le real.two_pi_pos.le),
  apply continuous_on.interval_integrable ((continuous_circle_transform hR F_cts
    w.property).continuous_on),
  exact real.locally_finite_volume,
end

/--The (complex) absolute value of the `circle_transform` of a function is integrable. -/
lemma circle_transform_integrable_abs {R : ℝ} {F : ℂ → ℂ} (hR : 0 < R) (z : ℂ)
  (F_cts : continuous_on F (sphere z R)) (w : ball z R) :
  integrable (complex.abs ∘ (circle_transform R z w F)) (volume.restrict (Ioc 0 (2*π))) :=
⟨(circle_transform_integrable hR z F_cts w).ae_strongly_measurable.norm,
    (circle_transform_integrable hR z F_cts w).has_finite_integral.norm⟩

lemma abs_sub_add_cancel_bound (x : ℂ) (r : ℝ)
  (h : ∃ (b : ℂ), complex.abs (x - b) + complex.abs(b) ≤ r) : complex.abs(x) ≤ r :=
begin
  obtain ⟨b, hb⟩ := h,
  rw ←sub_add_cancel x b,
  exact le_trans (abs.add_le (x - b) b) hb,
end

/--The `circle_transform` of a unifom limit of functions `F n` tends to the `circle_transform` of
  the limit function `f`. -/
lemma circle_transform_of_unifom_limit {R : ℝ} {F : ℕ → ℂ → ℂ} (hR : 0 < R) (f : ℂ → ℂ) (z : ℂ)
  (hlim : tendsto_uniformly_on F f filter.at_top (sphere z R)) (w : ball z R) (y : ℝ) :
  tendsto (λ n, ((circle_transform R z w (F n))) y)
  at_top (𝓝 (((circle_transform R z w f )) y)) :=
begin
  rw metric.tendsto_uniformly_on_iff at hlim,
  simp only [metric.tendsto_nhds, dist_comm, circle_transform, one_div,
    algebra.id.smul_eq_mul, gt_iff_lt, mem_closed_ball, nat.cast_bit0, real_smul, ge_iff_le,
    nsmul_eq_mul, nat.cast_one, eventually_at_top] at *,
  intros ε hε,
  set r : ℂ := (2 * π * I : ℂ)⁻¹ * circle_map 0 R y * I * ((circle_map z R y - ↑w)⁻¹),
  have hr : 0 < ∥ r ∥,
  by {simp only [r, norm_eq_abs, abs_mul, abs_inv, abs_two, abs_of_real, abs_I, mul_one,
    abs_circle_map_zero],
  simp only [absolute_value.map_neg, absolute_value.map_mul, abs_I, map_inv₀, abs_of_real, abs_two,
    one_mul, abs_circle_map_zero, mul_one],
  apply left.mul_pos (left.mul_pos (inv_pos.2 (left.mul_pos (@two_pos ℝ _ _)
    (_root_.abs_pos.2 real.pi_ne_zero)))  (_root_.abs_pos_of_pos hR)) _,
  simp only [inv_pos, absolute_value.pos_iff],
  exact sub_ne_zero.2 (circle_map_ne_mem_ball w.2 y), },
  let e := (∥ r ∥)⁻¹ * (ε/2),
  have he : 0 < e, by {simp_rw e, apply mul_pos (inv_pos.2 hr) (div_pos hε two_pos) },
  obtain ⟨a, ha⟩ := (hlim e he),
  refine ⟨ a, (λ b hb, _)⟩,
  simp_rw [deriv_circle_map, dist_eq_norm, ← mul_sub] at *,
  have hg : ∥ (2 * π * I : ℂ)⁻¹ * (circle_map 0 R y * I *
    ((circle_map z R y - ↑w)⁻¹ * (f (circle_map z R y) - F b (circle_map z R y))))∥ =
    ∥ (2 * π * I : ℂ)⁻¹ * circle_map 0 R y * I * ((circle_map z R y - ↑w)⁻¹) ∥ *
    ∥ (f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I)))∥,
  by {simp only [circle_map, abs_of_real, abs_exp_of_real_mul_I, mul_one, abs_I, abs_two,
        norm_eq_abs, mul_inv_rev, inv_I, zero_add, one_mul, absolute_value.map_neg,
        absolute_value.map_mul, map_inv₀],
      ring,},
  simp_rw [hg, ←r],
  have hab := (ha b hb) (z + ↑R * exp (↑y * I)) (circle_map_mem_sphere z hR.le y),
  simp only [abs_of_real, abs_exp_of_real_mul_I, add_sub_cancel',
    mul_one, abs_mul, norm_eq_abs] at hab,
  apply lt_trans (mul_lt_mul_of_pos_left hab hr),
  simp_rw [e, div_eq_inv_mul, ← mul_assoc, mul_inv_cancel (ne_of_gt hr)],
  simp only [one_mul, mul_lt_iff_lt_one_left, inv_eq_one_div],
  linarith,
end

/--A uniform limit of functions on a `sphere` can be eventually bounded by an integrable
function.  -/
lemma circle_transform_of_uniform_exists_bounding_function {R : ℝ} {F : ℕ → ℂ → ℂ} (hR : 0 < R)
  (f : ℂ → ℂ) (z : ℂ) (w : ball z R) (F_cts : ∀ n, continuous_on (F n) (sphere z R))
  (hlim : tendsto_uniformly_on F f filter.at_top (sphere z R) ):
  ∃ (bound : ℝ → ℝ), ((∀ n, ∀ᵐ r ∂(volume.restrict (Ioc 0 (2*π))),
  ∥(circle_transform R z w (F n)) r∥ ≤ bound r)
  ∧ integrable bound (volume.restrict (Ioc 0 (2*π)))) :=
begin
  have f_cont : continuous_on f (sphere z R) ,
  by {apply tendsto_uniformly_on.continuous_on hlim,
      simp only [F_cts, eventually_at_top, implies_true_iff, exists_const],},
  simp only [metric.tendsto_uniformly_on_iff, gt_iff_lt, ge_iff_le, eventually_at_top] at hlim,
  obtain ⟨a, ha⟩ := (hlim 1 (zero_lt_one)),
  set bound : ℝ → ℝ := λ θ, (∑ i in finset.range (a+1),
    complex.abs ((circle_transform R z w (F i)) θ))
    + complex.abs ((circle_transform R z w (λ x, 1)) θ) +
    complex.abs ((circle_transform R z w f) θ),
  refine ⟨bound, (λ n, _), _⟩,
  rw [ae_restrict_iff'],
  apply eventually_of_forall,
  intros y hyl,
  by_cases (n ≤ a),
  simp_rw bound,
  have hnn : n ∈ finset.range(a + 1), by {simp only [finset.mem_range], linarith},
  have := finset.add_sum_erase (finset.range (a + 1))
  (λ i , complex.abs ((circle_transform R z w (F i)) y)) hnn,
  simp only [and_imp, mem_Ioc, finset.mem_range, mem_sphere_iff_norm, norm_eq_abs] at *,
  simp_rw [←this, add_assoc, le_add_iff_nonneg_right],
  apply add_nonneg,
  { apply finset.sum_nonneg,
    intros a b,
    apply absolute_value.nonneg},
  { apply add_nonneg,
    apply absolute_value.nonneg,
    apply absolute_value.nonneg},
  { apply abs_sub_add_cancel_bound ((circle_transform R z w (F n)) y) (bound y),
    refine ⟨circle_transform R z ↑w f y,_⟩,
    simp_rw [circle_transform_sub, bound],
    simp only [add_le_add_iff_right, finset.univ_eq_attach],
    have := circle_transform_of_bound_is_bound hR ((F n) - f) z w 1,
    have haan := ha n (not_le.1 h).le,
    simp only [of_real_one, abs_one, pi.sub_apply] at this,
    simp_rw dist_eq_norm at *,
    simp only [norm_eq_abs] at haan,
    have haf : ∀ (x : sphere z R), abs (F n x - f x) ≤ 1,
    by {intro x, rw absolute_value.map_sub, apply (haan x.1 x.property).le,},
    apply le_add_of_nonneg_of_le,
    apply finset.sum_nonneg,
    intros d dd,
    apply absolute_value.nonneg,
    simp only [absolute_value.map_one] at this,
    apply ((this haf) y)},
  { simp only [measurable_set_Ioc]},
  { simp_rw bound,
   apply_rules [integrable.add, integrable.add, integrable_finset_sum],
   refine (λ _ _, circle_transform_integrable_abs hR z (F_cts _) w),
   apply circle_transform_integrable_abs hR z continuous_const.continuous_on,
   apply circle_transform_integrable_abs hR z f_cont},
end

/--The integral of a uniform limit of functions `F n` tends to the integral of the limit function
`f`. -/
lemma circle_int_uniform_lim_eq_lim_of_int {R : ℝ} {F : ℕ → ℂ → ℂ} (hR : 0 < R) (f : ℂ → ℂ)
  (z : ℂ) (w : ball z R) (F_cts : ∀ n, continuous_on (F n) (sphere z R))
  (hlim : tendsto_uniformly_on F f filter.at_top (sphere z R)) :
  tendsto (λn, ∫ (θ : ℝ) in 0..2 * π, (circle_transform R z w (F n)) θ)
  at_top (𝓝 $ ∫ (θ : ℝ) in 0..2 * π, (circle_transform R z w f ) θ) :=
begin
  have F_measurable : ∀ n,
  ae_strongly_measurable (circle_transform R z w (F n)) (volume.restrict (Ioc 0 (2*π))),
  by {intro n, simp_rw _root_.ae_strongly_measurable_iff_ae_measurable,
    apply (circle_transform_integrable hR z (F_cts n) w).ae_measurable},
  have h_lim'' : ∀ (a : ℝ), tendsto (λ n, ((circle_transform R z w (F n))) a)
  at_top (𝓝 (((circle_transform R z w f)) a)),
  by {apply circle_transform_of_unifom_limit hR f z hlim},
  have h_lim' : ∀ᵐ a ∂(volume.restrict (Ioc 0 (2*π))),
  tendsto (λ n, ((circle_transform R z w (F n))) a)
  at_top (𝓝 (((circle_transform R z w f )) a)),
  by {simp only [h_lim'', eventually_true],},
  have hboundlem := circle_transform_of_uniform_exists_bounding_function hR f z w F_cts hlim,
  obtain ⟨bound, h_bound, bound_integrable⟩ := hboundlem,
  simp_rw integral_of_le (real.two_pi_pos.le),
  exact tendsto_integral_of_dominated_convergence bound F_measurable bound_integrable h_bound
    h_lim',
end

end complex
