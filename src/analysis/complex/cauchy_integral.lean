/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.measure.lebesgue.complex
import measure_theory.integral.divergence_theorem
import measure_theory.integral.circle_integral
import analysis.calculus.dslope
import analysis.analytic.basic
import analysis.complex.re_im_topology
import analysis.calculus.diff_cont_on_cl
import data.real.cardinality

/-!
# Cauchy integral formula

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove the Cauchy-Goursat theorem and the Cauchy integral formula for integrals over
circles. Most results are formulated for a function `f : ℂ → E` that takes values in a complex
Banach space with second countable topology.

## Main statements

In the following theorems, if the name ends with `off_countable`, then the actual theorem assumes
differentiability at all but countably many points of the set mentioned below.

* `complex.integral_boundary_rect_of_has_fderiv_within_at_real_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and *real* differentiable on its interior, then
  its integral over the boundary of this rectangle is equal to the integral of
  `I • f' (x + y * I) 1 - f' (x + y * I) I` over the rectangle, where `f' z w : E` is the derivative
  of `f` at `z` in the direction `w` and `I = complex.I` is the imaginary unit.

* `complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and is *complex* differentiable on its interior,
  then its integral over the boundary of this rectangle is equal to zero.

* `complex.circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`: If a
  function `f : ℂ → E` is continuous on a closed annulus `{z | r ≤ |z - c| ≤ R}` and is complex
  differentiable on its interior `{z | r < |z - c| < R}`, then the integrals of `(z - c)⁻¹ • f z`
  over the outer boundary and over the inner boundary are equal.

* `complex.circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto`,
  `complex.circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable`:
  If a function `f : ℂ → E` is continuous on a punctured closed disc `{z | |z - c| ≤ R ∧ z ≠ c}`, is
  complex differentiable on the corresponding punctured open disc, and tends to `y` as `z → c`,
  `z ≠ c`, then the integral of `(z - c)⁻¹ • f z` over the circle `|z - c| = R` is equal to
  `2πiy`. In particular, if `f` is continuous on the whole closed disc and is complex differentiable
  on the corresponding open disc, then this integral is equal to `2πif(c)`.

* `complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable`,
  `complex.two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable`
  **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
  complex differentiable on the corresponding open disc, then for any `w` in the corresponding open
  disc the integral of `(z - w)⁻¹ • f z` over the boundary of the disc is equal to `2πif(w)`.
  Two versions of the lemma put the multiplier `2πi` at the different sides of the equality.

* `complex.has_fpower_series_on_ball_of_differentiable_off_countable`: If `f : ℂ → E` is continuous
  on a closed disc of positive radius and is complex differentiable on the corresponding open disc,
  then it is analytic on the corresponding open disc, and the coefficients of the power series are
  given by Cauchy integral formulas.

* `differentiable_on.has_fpower_series_on_ball`: If `f : ℂ → E` is complex differentiable on a
  closed disc of positive radius, then it is analytic on the corresponding open disc, and the
  coefficients of the power series are given by Cauchy integral formulas.

* `differentiable_on.analytic_at`, `differentiable.analytic_at`: If `f : ℂ → E` is differentiable
  on a neighborhood of a point, then it is analytic at this point. In particular, if `f : ℂ → E`
  is differentiable on the whole `ℂ`, then it is analytic at every point `z : ℂ`.

* `differentiable.has_power_series_on_ball`: If `f : ℂ → E` is differentiable everywhere then the
  `cauchy_power_series f z R` is a formal power series representing `f` at `z` with infinite
  radius of convergence (this holds for any choice of `0 < R`).

## Implementation details

The proof of the Cauchy integral formula in this file is based on a very general version of the
divergence theorem, see `measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable`
(a version for functions defined on `fin (n + 1) → ℝ`),
`measure_theory.integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le`, and
`measure_theory.integral2_divergence_prod_of_has_fderiv_within_at_off_countable` (versions for
functions defined on `ℝ × ℝ`).

Usually, the divergence theorem is formulated for a $C^1$ smooth function. The theorems formulated
above deal with a function that is

* continuous on a closed box/rectangle;
* differentiable at all but countably many points of its interior;
* have divergence integrable over the closed box/rectangle.

First, we reformulate the theorem for a *real*-differentiable map `ℂ → E`, and relate the integral
of `f` over the boundary of a rectangle in `ℂ` to the integral of the derivative
$\frac{\partial f}{\partial \bar z}$ over the interior of this box. In particular, for a *complex*
differentiable function, the latter derivative is zero, hence the integral over the boundary of a
rectangle is zero. Thus we get the Cauchy-Goursat theorem for a rectangle in `ℂ`.

Next, we apply the this theorem to the function $F(z)=f(c+e^{z})$ on the rectangle
$[\ln r, \ln R]\times [0, 2\pi]$ to prove that
$$
  \oint_{|z-c|=r}\frac{f(z)\,dz}{z-c}=\oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}
$$
provided that `f` is continuous on the closed annulus `r ≤ |z - c| ≤ R` and is complex
differentiable on its interior `r < |z - c| < R` (possibly, at all but countably many points).

Here and below, we write $\frac{f(z)}{z-c}$ in the documentation while the actual lemmas use
`(z - c)⁻¹ • f z` because `f z` belongs to some Banach space over `ℂ` and `f z / (z - c)` is
undefined.

Taking the limit of this equality as `r` tends to `𝓝[>] 0`, we prove
$$
  \oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}=2\pi if(c)
$$
provided that `f` is continuous on the closed disc `|z - c| ≤ R` and is differentiable at all but
countably many points of its interior. This is the Cauchy integral formula for the center of a
circle. In particular, if we apply this function to `F z = (z - c) • f z`, then we get
$$
  \oint_{|z-c|=R} f(z)\,dz=0.
$$

In order to deduce the Cauchy integral formula for any point `w`, `|w - c| < R`, we consider the
slope function `g : ℂ → E` given by `g z = (z - w)⁻¹ • (f z - f w)` if `z ≠ w` and `g w = f' w`.
This function satisfies assumptions of the previous theorem, so we have
$$
  \oint_{|z-c|=R} \frac{f(z)\,dz}{z-w}=\oint_{|z-c|=R} \frac{f(w)\,dz}{z-w}=
  \left(\oint_{|z-c|=R} \frac{dz}{z-w}\right)f(w).
$$
The latter integral was computed in `circle_integral.integral_sub_inv_of_mem_ball` and is equal to
`2 * π * complex.I`.

There is one more step in the actual proof. Since we allow `f` to be non-differentiable on a
countable set `s`, we cannot immediately claim that `g` is continuous at `w` if `w ∈ s`. So, we use
the proof outlined in the previous paragraph for `w ∉ s` (see
`complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux`), then use continuity
of both sides of the formula and density of `sᶜ` to prove the formula for all points of the open
ball, see `complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable`.

Finally, we use the properties of the Cauchy integrals established elsewhere (see
`has_fpower_series_on_cauchy_integral`) and Cauchy integral formula to prove that the original
function is analytic on the open ball.

## Tags

Cauchy-Goursat theorem, Cauchy integral formula
-/

open topological_space set measure_theory interval_integral metric filter function
open_locale interval real nnreal ennreal topology big_operators

noncomputable theory

universes u

variables {E : Type u} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]

namespace complex

/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable at all but countably many points of the corresponding open
rectangle, and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the
integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
lemma integral_boundary_rect_of_has_fderiv_at_real_off_countable (f : ℂ → E)
  (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ) (s : set ℂ) (hs : s.countable)
  (Hc : continuous_on f ([z.re, w.re] ×ℂ [z.im, w.im]))
  (Hd : ∀ x ∈ (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)) \ s,
    has_fderiv_at f (f' x) x)
  (Hi : integrable_on (λ z, I • f' z 1 - f' z I) ([z.re, w.re] ×ℂ [z.im, w.im])) :
  (∫_{z.re}^{w.re} x, f (x + z.im * I)) - (∫_{z.re}^{w.re} x, f (x + w.im * I)) +
    (I • ∫_{z.im}^{w.im} y, f (re w + y * I)) - I • ∫_{z.im}^{w.im} y, f (re z + y * I) =
    ∫_{z.re}^{w.re} x, ∫_{z.im}^{w.im} y, I • f' (x + y * I) 1 - f' (x + y * I) I :=
begin
  set e : (ℝ × ℝ) ≃L[ℝ] ℂ := equiv_real_prod_clm.symm,
  have he : ∀ x y : ℝ, ↑x + ↑y * I = e (x, y), from λ x y, (mk_eq_add_mul_I x y).symm,
  have he₁ : e (1, 0) = 1 := rfl, have he₂ : e (0, 1) = I := rfl,
  simp only [he] at *,
  set F : (ℝ × ℝ) → E := f ∘ e,
  set F' : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] E := λ p, (f' (e p)).comp (e : (ℝ × ℝ) →L[ℝ] ℂ),
  have hF' : ∀ p : ℝ × ℝ, (-(I • F' p)) (1, 0) + F' p (0, 1) = -(I • f' (e p) 1 - f' (e p) I),
  { rintro ⟨x, y⟩,
    simp only [continuous_linear_map.neg_apply, continuous_linear_map.smul_apply, F',
      continuous_linear_map.comp_apply, continuous_linear_equiv.coe_coe, he₁, he₂,
      neg_add_eq_sub, neg_sub], },
  set R : set (ℝ × ℝ) := [z.re, w.re] ×ˢ [w.im, z.im],
  set t : set (ℝ × ℝ) := e ⁻¹' s,
  rw [uIcc_comm z.im] at Hc Hi, rw [min_comm z.im, max_comm z.im] at Hd,
  have hR : e ⁻¹' ([z.re, w.re] ×ℂ [w.im, z.im]) = R := rfl,
  have htc : continuous_on F R, from Hc.comp e.continuous_on hR.ge,
  have htd : ∀ p ∈ Ioo (min z.re w.re) (max z.re w.re) ×ˢ Ioo (min w.im z.im) (max w.im z.im) \ t,
    has_fderiv_at F (F' p) p := λ p hp, (Hd (e p) hp).comp p e.has_fderiv_at,
  simp_rw [← interval_integral.integral_smul, interval_integral.integral_symm w.im z.im,
    ← interval_integral.integral_neg, ← hF'],
  refine (integral2_divergence_prod_of_has_fderiv_within_at_off_countable
      (λ p, -(I • F p)) F (λ p, - (I • F' p)) F' z.re w.im w.re z.im t (hs.preimage e.injective)
      (htc.const_smul _).neg htc (λ p hp, ((htd p hp).const_smul I).neg) htd _).symm,
  rw [← (volume_preserving_equiv_real_prod.symm _).integrable_on_comp_preimage
    (measurable_equiv.measurable_embedding _)] at Hi,
  simpa only [hF'] using Hi.neg
end

/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable on the corresponding open rectangle, and
$\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the integral of `f` over
the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
lemma integral_boundary_rect_of_continuous_on_of_has_fderiv_at_real (f : ℂ → E)
  (f' : ℂ → ℂ →L[ℝ] E) (z w : ℂ)
  (Hc : continuous_on f ([z.re, w.re] ×ℂ [z.im, w.im]))
  (Hd : ∀ x ∈ (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)),
    has_fderiv_at f (f' x) x)
  (Hi : integrable_on (λ z, I • f' z 1 - f' z I) ([z.re, w.re] ×ℂ [z.im, w.im])) :
  (∫_{z.re}^{w.re} x, f (x + z.im * I)) - (∫_{z.re}^{w.re} x, f (x + w.im * I)) +
    (I • ∫_{z.im}^{w.im} y, f (re w + y * I)) - I • ∫_{z.im}^{w.im} y, f (re z + y * I) =
    ∫_{z.re}^{w.re} x, ∫_{z.im}^{w.im} y, I • f' (x + y * I) 1 - f' (x + y * I) I :=
integral_boundary_rect_of_has_fderiv_at_real_off_countable f f' z w ∅ countable_empty Hc
  (λ x hx, Hd x hx.1) Hi

/-- Suppose that a function `f : ℂ → E` is *real* differentiable on a closed rectangle with opposite
corners at `z w : ℂ` and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then
the integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
lemma integral_boundary_rect_of_differentiable_on_real (f : ℂ → E) (z w : ℂ)
  (Hd : differentiable_on ℝ f ([z.re, w.re] ×ℂ [z.im, w.im]))
  (Hi : integrable_on (λ z, I • fderiv ℝ f z 1 - fderiv ℝ f z I) ([z.re, w.re] ×ℂ [z.im, w.im])) :
  (∫_{z.re}^{w.re} x, f (x + z.im * I)) - (∫_{z.re}^{w.re} x, f (x + w.im * I)) +
    (I • ∫_{z.im}^{w.im} y, f (re w + y * I)) - I • ∫_{z.im}^{w.im} y, f (re z + y * I) =
    ∫_{z.re}^{w.re} x, ∫_{z.im}^{w.im} y,
      I • fderiv ℝ f (x + y * I) 1 - fderiv ℝ f (x + y * I) I :=
integral_boundary_rect_of_has_fderiv_at_real_off_countable f (fderiv ℝ f) z w ∅ countable_empty
  Hd.continuous_on
  (λ x hx, Hd.has_fderiv_at $ by simpa only [← mem_interior_iff_mem_nhds,
    interior_re_prod_im, uIcc, interior_Icc] using hx.1) Hi

/-- **Cauchy-Goursat theorem** for a rectangle: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuous on a closed
rectangle and is complex differentiable at all but countably many points of the corresponding open
rectangle, then its integral over the boundary of the rectangle equals zero. -/
lemma integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : ℂ → E)
  (z w : ℂ) (s : set ℂ) (hs : s.countable) (Hc : continuous_on f ([z.re, w.re] ×ℂ [z.im, w.im]))
  (Hd : ∀ x ∈ (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)) \ s,
    differentiable_at ℂ f x) :
  (∫_{z.re}^{w.re} x, f (x + z.im * I)) - (∫_{z.re}^{w.re} x, f (x + w.im * I)) +
    (I • ∫_{z.im}^{w.im} y, f (re w + y * I)) -
      I • ∫_{z.im}^{w.im} y, f (re z + y * I) = 0 :=
by refine (integral_boundary_rect_of_has_fderiv_at_real_off_countable f
  (λ z, (fderiv ℂ f z).restrict_scalars ℝ) z w s hs Hc
  (λ x hx, (Hd x hx).has_fderiv_at.restrict_scalars ℝ) _).trans _;
    simp [← continuous_linear_map.map_smul]

/-- **Cauchy-Goursat theorem for a rectangle**: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuous on a closed
rectangle and is complex differentiable on the corresponding open rectangle, then its integral over
the boundary of the rectangle equals zero. -/
lemma integral_boundary_rect_eq_zero_of_continuous_on_of_differentiable_on (f : ℂ → E) (z w : ℂ)
  (Hc : continuous_on f ([z.re, w.re] ×ℂ [z.im, w.im]))
  (Hd : differentiable_on ℂ f
    (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im))) :
  (∫_{z.re}^{w.re} x, f (x + z.im * I)) - (∫_{z.re}^{w.re} x, f (x + w.im * I)) +
    (I • ∫_{z.im}^{w.im} y, f (re w + y * I)) -
      I • ∫_{z.im}^{w.im} y, f (re z + y * I) = 0 :=
integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ countable_empty
  Hc $ λ x hx, Hd.differentiable_at $ (is_open_Ioo.re_prod_im is_open_Ioo).mem_nhds hx.1

/-- **Cauchy-Goursat theorem** for a rectangle: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is complex differentiable on a
closed rectangle, then its integral over the boundary of the rectangle equals zero. -/
lemma integral_boundary_rect_eq_zero_of_differentiable_on (f : ℂ → E) (z w : ℂ)
  (H : differentiable_on ℂ f ([z.re, w.re] ×ℂ [z.im, w.im])) :
  (∫_{z.re}^{w.re} x, f (x + z.im * I)) - (∫_{z.re}^{w.re} x, f (x + w.im * I)) +
    (I • ∫_{z.im}^{w.im} y, f (re w + y * I)) -
      I • ∫_{z.im}^{w.im} y, f (re z + y * I) = 0 :=
integral_boundary_rect_eq_zero_of_continuous_on_of_differentiable_on f z w H.continuous_on $
  H.mono $
    inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

/-- If `f : ℂ → E` is continuous the closed annulus `r ≤ ‖z - c‖ ≤ R`, `0 < r ≤ R`, and is complex
differentiable at all but countably many points of its interior, then the integrals of
`f z / (z - c)` (formally, `(z - c)⁻¹ • f z`) over the circles `‖z - c‖ = r` and `‖z - c‖ = R` are
equal to each other. -/
lemma circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
  {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : set ℂ} (hs : s.countable)
  (hc : continuous_on f (closed_ball c R \ ball c r))
  (hd : ∀ z ∈ ball c R \ closed_ball c r \ s, differentiable_at ℂ f z) :
  ∮ z in C(c, R), (z - c)⁻¹ • f z = ∮ z in C(c, r), (z - c)⁻¹ • f z :=
begin
  /- We apply the previous lemma to `λ z, f (c + exp z)` on the rectangle
  `[log r, log R] × [0, 2 * π]`. -/
  set A := closed_ball c R \ ball c r,
  obtain ⟨a, rfl⟩ : ∃ a, real.exp a = r, from ⟨real.log r, real.exp_log h0⟩,
  obtain ⟨b, rfl⟩ : ∃ b, real.exp b = R, from ⟨real.log R, real.exp_log (h0.trans_le hle)⟩,
  rw [real.exp_le_exp] at hle,
  -- Unfold definition of `circle_integral` and cancel some terms.
  suffices : ∫_{0}^{2 * π} θ, I • f (circle_map c (real.exp b) θ) =
    ∫_{0}^{2 * π} θ, I • f (circle_map c (real.exp a) θ),
    by simpa only [circle_integral, add_sub_cancel', of_real_exp, ← exp_add, smul_smul,
      ← div_eq_mul_inv, mul_div_cancel_left _ (circle_map_ne_center (real.exp_pos _).ne'),
      circle_map_sub_center, deriv_circle_map],
  set R := [a, b] ×ℂ [0, 2 * π],
  set g : ℂ → ℂ := (+) c ∘ exp,
  have hdg : differentiable ℂ g := differentiable_exp.const_add _,
  replace hs : (g ⁻¹' s).countable := (hs.preimage (add_right_injective c)).preimage_cexp,
  have h_maps : maps_to g R A,
  { rintro z ⟨h, -⟩, simpa [dist_eq, g, abs_exp, hle] using h.symm },
  replace hc : continuous_on (f ∘ g) R, from hc.comp hdg.continuous.continuous_on h_maps,
  replace hd : ∀ z ∈ (Ioo (min a b) (max a b) ×ℂ Ioo (min 0 (2 * π)) (max 0 (2 * π))) \ g ⁻¹' s,
    differentiable_at ℂ (f ∘ g) z,
  { refine λ z hz, (hd (g z) ⟨_, hz.2⟩).comp z (hdg _),
    simpa [g, dist_eq, abs_exp, hle, and.comm] using hz.1.1 },
  simpa [g, circle_map, exp_periodic _, sub_eq_zero, ← exp_add]
    using integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩
      _ hs hc hd
end

/-- **Cauchy-Goursat theorem** for an annulus. If `f : ℂ → E` is continuous on the closed annulus
`r ≤ ‖z - c‖ ≤ R`, `0 < r ≤ R`, and is complex differentiable at all but countably many points of
its interior, then the integrals of `f` over the circles `‖z - c‖ = r` and `‖z - c‖ = R` are equal
to each other. -/
lemma circle_integral_eq_of_differentiable_on_annulus_off_countable
  {c : ℂ} {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : set ℂ} (hs : s.countable)
  (hc : continuous_on f (closed_ball c R \ ball c r))
  (hd : ∀ z ∈ ball c R \ closed_ball c r \ s, differentiable_at ℂ f z) :
  ∮ z in C(c, R), f z = ∮ z in C(c, r), f z :=
calc ∮ z in C(c, R), f z = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :
  (circle_integral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
... = ∮ z in C(c, r), (z - c)⁻¹ • (z - c) • f z :
  circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable h0 hle hs
    ((continuous_on_id.sub continuous_on_const).smul hc)
    (λ z hz, (differentiable_at_id.sub_const _).smul (hd z hz))
... = ∮ z in C(c, r), f z : circle_integral.integral_sub_inv_smul_sub_smul _ _ _ _

/-- **Cauchy integral formula** for the value at the center of a disc. If `f` is continuous on a
punctured closed disc of radius `R`, is differentiable at all but countably many points of the
interior of this disc, and has a limit `y` at the center of the disc, then the integral
$\oint_{‖z-c‖=R} \frac{f(z)}{z-c}\,dz$ is equal to $2πiy`. -/
lemma circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
  {c : ℂ} {R : ℝ} (h0 : 0 < R) {f : ℂ → E} {y : E} {s : set ℂ} (hs : s.countable)
  (hc : continuous_on f (closed_ball c R \ {c}))
  (hd : ∀ z ∈ ball c R \ {c} \ s, differentiable_at ℂ f z) (hy : tendsto f (𝓝[{c}ᶜ] c) (𝓝 y)) :
  ∮ z in C(c, R), (z - c)⁻¹ • f z = (2 * π * I : ℂ) • y :=
begin
  rw [← sub_eq_zero, ← norm_le_zero_iff],
  refine le_of_forall_le_of_dense (λ ε ε0, _),
  obtain ⟨δ, δ0, hδ⟩ :
    ∃ δ > (0 : ℝ), ∀ z ∈ closed_ball c δ \ {c}, dist (f z) y < ε / (2 * π),
    from ((nhds_within_has_basis nhds_basis_closed_ball _).tendsto_iff nhds_basis_ball).1 hy _
      (div_pos ε0 real.two_pi_pos),
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩,
  have hsub : closed_ball c R \ ball c r ⊆ closed_ball c R \ {c},
    from diff_subset_diff_right (singleton_subset_iff.2 $ mem_ball_self hr0),
  have hsub' : ball c R \ closed_ball c r ⊆ ball c R \ {c},
    from diff_subset_diff_right (singleton_subset_iff.2 $ mem_closed_ball_self hr0.le),
  have hzne : ∀ z ∈ sphere c r, z ≠ c,
    from λ z hz, ne_of_mem_of_not_mem hz (λ h, hr0.ne' $ dist_self c ▸ eq.symm h),
  /- The integral `∮ z in C(c, r), f z / (z - c)` does not depend on `0 < r ≤ R` and tends to
  `2πIy` as `r → 0`. -/
  calc ‖(∮ z in C(c, R), (z - c)⁻¹ • f z) - (2 * ↑π * I) • y‖
      = ‖(∮ z in C(c, r), (z - c)⁻¹ • f z) - ∮ z in C(c, r), (z - c)⁻¹ • y‖ :
    begin
      congr' 2,
      { exact circle_integral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
          hr0 hrR hs (hc.mono hsub) (λ z hz, hd z ⟨hsub' hz.1, hz.2⟩) },
      { simp [hr0.ne'] }
    end
  ... = ‖∮ z in C(c, r), (z - c)⁻¹ • (f z - y)‖ :
    begin
      simp only [smul_sub],
      have hc' : continuous_on (λ z, (z - c)⁻¹) (sphere c r),
        from (continuous_on_id.sub continuous_on_const).inv₀ (λ z hz, sub_ne_zero.2 $ hzne _ hz),
      rw circle_integral.integral_sub; refine (hc'.smul _).circle_integrable hr0.le,
      { exact hc.mono (subset_inter (sphere_subset_closed_ball.trans $
          closed_ball_subset_closed_ball hrR) hzne) },
      { exact continuous_on_const }
    end
  ... ≤ 2 * π * r * (r⁻¹ * (ε / (2 * π))) :
    begin
      refine circle_integral.norm_integral_le_of_norm_le_const hr0.le (λ z hz, _),
      specialize hzne z hz,
      rw [mem_sphere, dist_eq_norm] at hz,
      rw [norm_smul, norm_inv, hz, ← dist_eq_norm],
      refine mul_le_mul_of_nonneg_left (hδ _ ⟨_, hzne⟩).le (inv_nonneg.2 hr0.le),
      rwa [mem_closed_ball_iff_norm, hz]
    end
  ... = ε : by { field_simp [hr0.ne', real.two_pi_pos.ne'], ac_refl }
end

/-- **Cauchy integral formula** for the value at the center of a disc. If `f : ℂ → E` is continuous
on a closed disc of radius `R` and is complex differentiable at all but countably many points of its
interior, then the integral $\oint_{|z-c|=R} \frac{f(z)}{z-c}\,dz$ is equal to $2πiy`. -/
lemma circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 < R)
  {f : ℂ → E} {c : ℂ} {s : set ℂ} (hs : s.countable)
  (hc : continuous_on f (closed_ball c R)) (hd : ∀ z ∈ ball c R \ s, differentiable_at ℂ f z) :
  ∮ z in C(c, R), (z - c)⁻¹ • f z = (2 * π * I : ℂ) • f c :=
circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs
  (hc.mono $ diff_subset _ _) (λ z hz, hd z ⟨hz.1.1, hz.2⟩)
  (hc.continuous_at $ closed_ball_mem_nhds _ h0).continuous_within_at

/-- **Cauchy-Goursat theorem** for a disk: if `f : ℂ → E` is continuous on a closed disk
`{z | ‖z - c‖ ≤ R}` and is complex differentiable at all but countably many points of its interior,
then the integral $\oint_{|z-c|=R}f(z)\,dz$ equals zero. -/
lemma circle_integral_eq_zero_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
  {c : ℂ} {s : set ℂ} (hs : s.countable) (hc : continuous_on f (closed_ball c R))
  (hd : ∀ z ∈ ball c R \ s, differentiable_at ℂ f z) :
  ∮ z in C(c, R), f z = 0 :=
begin
  rcases h0.eq_or_lt with rfl|h0, { apply circle_integral.integral_radius_zero },
  calc ∮ z in C(c, R), f z = ∮ z in C(c, R), (z - c)⁻¹ • (z - c) • f z :
    (circle_integral.integral_sub_inv_smul_sub_smul _ _ _ _).symm
  ... = (2 * ↑π * I : ℂ) • (c - c) • f c :
    circle_integral_sub_center_inv_smul_of_differentiable_on_off_countable h0 hs
      ((continuous_on_id.sub continuous_on_const).smul hc)
      (λ z hz, (differentiable_at_id.sub_const _).smul (hd z hz))
  ... = 0 : by rw [sub_self, zero_smul, smul_zero]
end

/-- An auxiliary lemma for
`complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable`. This lemma assumes
`w ∉ s` while the main lemma drops this assumption. -/
lemma circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux {R : ℝ} {c w : ℂ}
  {f : ℂ → E} {s : set ℂ} (hs : s.countable) (hw : w ∈ ball c R \ s)
  (hc : continuous_on f (closed_ball c R)) (hd : ∀ x ∈ ball c R \ s, differentiable_at ℂ f x) :
  ∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I : ℂ) • f w :=
begin
  have hR : 0 < R := dist_nonneg.trans_lt hw.1,
  set F : ℂ → E := dslope f w,
  have hws : (insert w s).countable := hs.insert w,
  have hnhds : closed_ball c R ∈ 𝓝 w, from closed_ball_mem_nhds_of_mem hw.1,
  have hcF : continuous_on F (closed_ball c R),
    from (continuous_on_dslope $ closed_ball_mem_nhds_of_mem hw.1).2 ⟨hc, hd _ hw⟩,
  have hdF : ∀ z ∈ ball (c : ℂ) R \ (insert w s), differentiable_at ℂ F z,
    from λ z hz, (differentiable_at_dslope_of_ne
      (ne_of_mem_of_not_mem (mem_insert _ _) hz.2).symm).2
      (hd _ (diff_subset_diff_right (subset_insert _ _) hz)),
  have HI := circle_integral_eq_zero_of_differentiable_on_off_countable hR.le hws hcF hdF,
  have hne : ∀ z ∈ sphere c R, z ≠ w, from λ z hz, ne_of_mem_of_not_mem hz (ne_of_lt hw.1),
  have hFeq : eq_on F (λ z, (z - w)⁻¹ • f z - (z - w)⁻¹ • f w) (sphere c R),
  { intros z hz,
    calc F z = (z - w)⁻¹ • (f z - f w) : update_noteq (hne z hz) _ _
    ... = (z - w)⁻¹ • f z - (z - w)⁻¹ • f w : smul_sub _ _ _ },
  have hc' : continuous_on (λ z, (z - w)⁻¹) (sphere c R),
    from (continuous_on_id.sub continuous_on_const).inv₀ (λ z hz, sub_ne_zero.2 $ hne z hz),
  rw [← circle_integral.integral_sub_inv_of_mem_ball hw.1, ← circle_integral.integral_smul_const,
    ← sub_eq_zero, ← circle_integral.integral_sub, ← circle_integral.integral_congr hR.le hFeq, HI],
  exacts [(hc'.smul (hc.mono sphere_subset_closed_ball)).circle_integrable hR.le,
    (hc'.smul continuous_on_const).circle_integrable hR.le]
end

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$.
-/
lemma two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable
  {R : ℝ} {c w : ℂ} {f : ℂ → E} {s : set ℂ} (hs : s.countable) (hw : w ∈ ball c R)
  (hc : continuous_on f (closed_ball c R)) (hd : ∀ x ∈ ball c R \ s, differentiable_at ℂ f x) :
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z = f w :=
begin
  have hR : 0 < R := dist_nonneg.trans_lt hw,
  suffices : w ∈ closure (ball c R \ s),
  { lift R to ℝ≥0 using hR.le,
    have A : continuous_at (λ w, (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w,
    { have := has_fpower_series_on_cauchy_integral
      ((hc.mono sphere_subset_closed_ball).circle_integrable R.coe_nonneg) hR,
      refine this.continuous_on.continuous_at (emetric.is_open_ball.mem_nhds _),
      rwa metric.emetric_ball_nnreal },
    have B : continuous_at f w, from hc.continuous_at (closed_ball_mem_nhds_of_mem hw),
    refine tendsto_nhds_unique_of_frequently_eq A B ((mem_closure_iff_frequently.1 this).mono _),
    intros z hz,
    rw [circle_integral_sub_inv_smul_of_differentiable_on_off_countable_aux hs hz hc hd,
      inv_smul_smul₀],
    simp [real.pi_ne_zero, I_ne_zero] },
  refine mem_closure_iff_nhds.2 (λ t ht, _),
  -- TODO: generalize to any vector space over `ℝ`
  set g : ℝ → ℂ := λ x, w + x,
  have : tendsto g (𝓝 0) (𝓝 w),
    from (continuous_const.add continuous_of_real).tendsto' 0 w (add_zero _),
  rcases mem_nhds_iff_exists_Ioo_subset.1 (this $ inter_mem ht $ is_open_ball.mem_nhds hw)
    with ⟨l, u, hlu₀, hlu_sub⟩,
  obtain ⟨x, hx⟩ : (Ioo l u \ g ⁻¹' s).nonempty,
  { refine nonempty_diff.2 (λ hsub, _),
    have : (Ioo l u).countable,
      from (hs.preimage ((add_right_injective w).comp of_real_injective)).mono hsub,
    rw [← cardinal.le_aleph_0_iff_set_countable,
      cardinal.mk_Ioo_real (hlu₀.1.trans hlu₀.2)] at this,
    exact this.not_lt cardinal.aleph_0_lt_continuum },
  exact ⟨g x, (hlu_sub hx.1).1, (hlu_sub hx.1).2, hx.2⟩
end

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$.
-/
lemma circle_integral_sub_inv_smul_of_differentiable_on_off_countable
  {R : ℝ} {c w : ℂ} {f : ℂ → E} {s : set ℂ} (hs : s.countable) (hw : w ∈ ball c R)
  (hc : continuous_on f (closed_ball c R)) (hd : ∀ x ∈ ball c R \ s, differentiable_at ℂ f x) :
  ∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I : ℂ) • f w :=
by { rw [← two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable
  hs hw hc hd, smul_inv_smul₀], simp [real.pi_ne_zero, I_ne_zero] }

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on an open disc and is
continuous on its closure, then for any `w` in this open ball we have
$\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$. -/
lemma _root_.diff_cont_on_cl.circle_integral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
  (h : diff_cont_on_cl ℂ f (ball c R)) (hw : w ∈ ball c R) :
  ∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I : ℂ) • f w :=
circle_integral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw
  h.continuous_on_ball $ λ x hx, h.differentiable_at is_open_ball hx.1

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on an open disc and is
continuous on its closure, then for any `w` in this open ball we have
$\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$. -/
lemma _root_.diff_cont_on_cl.two_pi_I_inv_smul_circle_integral_sub_inv_smul {R : ℝ} {c w : ℂ}
  {f : ℂ → E} (hf : diff_cont_on_cl ℂ f (ball c R)) (hw : w ∈ ball c R) :
  (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z = f w :=
begin
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (nonempty_of_mem hw).ne_empty),
  refine two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty hw _ _,
  { simpa only [closure_ball c hR.ne.symm] using hf.continuous_on },
  { simpa only [diff_empty] using λ z hz, hf.differentiable_at is_open_ball hz }
end

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on a closed disc of radius
`R`, then for any `w` in its interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$. -/
lemma _root_.differentiable_on.circle_integral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
  (hd : differentiable_on ℂ f (closed_ball c R)) (hw : w ∈ ball c R)  :
  ∮ z in C(c, R), (z - w)⁻¹ • f z = (2 * π * I : ℂ) • f w :=
(hd.mono closure_ball_subset_closed_ball).diff_cont_on_cl.circle_integral_sub_inv_smul hw

/-- **Cauchy integral formula**: if `f : ℂ → ℂ` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}\frac{f(z)}{z-w}dz=2\pi i\,f(w)$.
-/
lemma circle_integral_div_sub_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {s : set ℂ}
  (hs : s.countable) (hw : w ∈ ball c R) {f : ℂ → ℂ} (hc : continuous_on f (closed_ball c R))
  (hd : ∀ z ∈ ball c R \ s, differentiable_at ℂ f z) :
  ∮ z in C(c, R), f z / (z - w) = 2 * π * I * f w :=
by simpa only [smul_eq_mul, div_eq_inv_mul]
  using circle_integral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd

/-- If `f : ℂ → E` is continuous on a closed ball of positive radius and is differentiable at all
but countably many points of the corresponding open ball, then it is analytic on the open ball with
coefficients of the power series given by Cauchy integral formulas. -/
lemma has_fpower_series_on_ball_of_differentiable_off_countable {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
  {s : set ℂ} (hs : s.countable) (hc : continuous_on f (closed_ball c R))
  (hd : ∀ z ∈ ball c R \ s, differentiable_at ℂ f z) (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f c R) c R :=
{ r_le := le_radius_cauchy_power_series _ _ _,
  r_pos := ennreal.coe_pos.2 hR,
  has_sum := λ w hw,
    begin
      have hw' : c + w ∈ ball c R,
        by simpa only [add_mem_ball_iff_norm, ← coe_nnnorm, mem_emetric_ball_zero_iff,
          nnreal.coe_lt_coe, ennreal.coe_lt_coe] using hw,
      rw ← two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable hs
        hw' hc hd,
      exact (has_fpower_series_on_cauchy_integral
        ((hc.mono sphere_subset_closed_ball).circle_integrable R.2) hR).has_sum hw
    end }

/-- If `f : ℂ → E` is complex differentiable on an open disc of positive radius and is continuous
on its closure, then it is analytic on the open disc with coefficients of the power series given by
Cauchy integral formulas. -/
lemma _root_.diff_cont_on_cl.has_fpower_series_on_ball {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
  (hf : diff_cont_on_cl ℂ f (ball c R)) (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f c R) c R :=
has_fpower_series_on_ball_of_differentiable_off_countable countable_empty hf.continuous_on_ball
  (λ z hz, hf.differentiable_at is_open_ball hz.1) hR

/-- If `f : ℂ → E` is complex differentiable on a closed disc of positive radius, then it is
analytic on the corresponding open disc, and the coefficients of the power series are given by
Cauchy integral formulas. See also
`complex.has_fpower_series_on_ball_of_differentiable_off_countable` for a version of this lemma with
weaker assumptions. -/
protected lemma _root_.differentiable_on.has_fpower_series_on_ball {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
  (hd : differentiable_on ℂ f (closed_ball c R)) (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f c R) c R :=
(hd.mono closure_ball_subset_closed_ball).diff_cont_on_cl.has_fpower_series_on_ball hR

/-- If `f : ℂ → E` is complex differentiable on some set `s`, then it is analytic at any point `z`
such that `s ∈ 𝓝 z` (equivalently, `z ∈ interior s`). -/
protected lemma _root_.differentiable_on.analytic_at {s : set ℂ} {f : ℂ → E} {z : ℂ}
  (hd : differentiable_on ℂ f s) (hz : s ∈ 𝓝 z) : analytic_at ℂ f z :=
begin
  rcases nhds_basis_closed_ball.mem_iff.1 hz with ⟨R, hR0, hRs⟩,
  lift R to ℝ≥0 using hR0.le,
  exact ((hd.mono hRs).has_fpower_series_on_ball hR0).analytic_at
end

lemma _root_.differentiable_on.analytic_on {s : set ℂ} {f : ℂ → E} (hd : differentiable_on ℂ f s)
  (hs : is_open s) : analytic_on ℂ f s :=
λ z hz, hd.analytic_at (hs.mem_nhds hz)

/-- A complex differentiable function `f : ℂ → E` is analytic at every point. -/
protected lemma _root_.differentiable.analytic_at {f : ℂ → E} (hf : differentiable ℂ f) (z : ℂ) :
  analytic_at ℂ f z :=
hf.differentiable_on.analytic_at univ_mem

/-- When `f : ℂ → E` is differentiable, the `cauchy_power_series f z R` represents `f` as a power
series centered at `z` in the entirety of `ℂ`, regardless of `R : ℝ≥0`, with  `0 < R`. -/
protected lemma _root_.differentiable.has_fpower_series_on_ball {f : ℂ → E}
  (h : differentiable ℂ f) (z : ℂ) {R : ℝ≥0} (hR : 0 < R) :
  has_fpower_series_on_ball f (cauchy_power_series f z R) z ∞ :=
(h.differentiable_on.has_fpower_series_on_ball hR).r_eq_top_of_exists $ λ r hr,
  ⟨_, h.differentiable_on.has_fpower_series_on_ball hr⟩

end complex
