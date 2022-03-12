/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.complex.abs_max
import analysis.complex.removable_singularity

/-!
# Schwarz lemma

In this file we prove several versions of the Schwarz lemma.

* `complex.abs_deriv_le_div_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk with center `c` and
  a positive radius `R₁` to an open disk with center `f c` and radius `R₂`, then the absolute value
  of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`;

* `complex.dist_le_div_mul_dist_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk with center `c`
  and radius `R₁` to an open disk with center `f c` and radius `R₂`, then for any `z` in the former
  disk we have ``dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`;

* `complex.abs_deriv_le_one_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk of positive radius
  to itself and the center of this disk to itself, then the absolute value of the derivative of `f`
  at the center of this disk is at most `1`;

* `complex.dist_le_dist_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk to itself and the center
  `c` of this disk to itself, then for any point `z` of this disk we have `dist (f z) c ≤ dist z c`;

* `complex.abs_le_abs_of_maps_to_ball`: if `f : ℂ → ℂ` sends an open disk with center `0` to itself,
  the for any point `z` of this disk we have `abs (f z) ≤ abs z`.

## TODO

* Prove that these inequalities are strict unless `f` is an affine map.

* Prove that any diffeomorphism of the unit disk to itself is a Möbius map.

## Tags

Schwarz lemma
-/

open metric set function filter
open_locale topological_space

namespace complex

variables {R R₁ R₂ : ℝ} {f : ℂ → ℂ} {c z : ℂ}

/-- An auxiliary lemma used to simultaneously prove the Schwarz lemma for the derivative at the
center and for the distance to the center. -/
lemma abs_dslope_le_div_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
  abs (dslope f c z) ≤ R₂ / R₁ :=
begin
  have hR₁ : 0 < R₁, from nonempty_ball.1 ⟨z, hz⟩,
  suffices : ∀ᶠ r in 𝓝[<] R₁, abs (dslope f c z) ≤ R₂ / r,
  { refine ge_of_tendsto _ this,
    exact (tendsto_const_nhds.div tendsto_id hR₁.ne').mono_left nhds_within_le_nhds },
  rw mem_ball at hz,
  filter_upwards [Ioo_mem_nhds_within_Iio ⟨hz, le_rfl⟩] with r hr,
  have hr₀ : 0 < r, from dist_nonneg.trans_lt hr.1,
  replace hd : differentiable_on ℂ (dslope f c) (closed_ball c r),
    from ((differentiable_on_dslope $ ball_mem_nhds _ hR₁).mpr hd).mono (closed_ball_subset_ball hr.2),
  refine norm_le_of_forall_mem_frontier_norm_le (is_compact_closed_ball c r)
    hd.continuous_on (hd.mono interior_subset) _ hr.1.le,
  rw frontier_closed_ball',
  intros z hz,
  have hz' : z ≠ c, by { rintro rfl, simpa [hr₀.ne] using hz },
  rw [dslope_of_ne _ hz', slope_def_field, norm_div,
    (mem_sphere_iff_norm _ _ _).1 hz, div_le_div_right hr₀, ← dist_eq_norm],
  rw mem_sphere at hz,
  exact le_of_lt (h_maps (mem_ball.2 (by { rw hz, exact hr.2 })))
end

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk with center `c` and a positive radius
`R₁` to an open disk with center `f c` and radius `R₂`, then the absolute value of the derivative of
`f` at `c` is at most the ratio `R₂ / R₁`. -/
lemma abs_deriv_le_div_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (h₀ : 0 < R₁) :
  abs (deriv f c) ≤ R₂ / R₁ :=
by simpa only [dslope_same] using abs_dslope_le_div_of_maps_to_ball hd h_maps (mem_ball_self h₀)

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk with center `c` and radius `R₁` to an
open disk with center `f c` and radius `R₂`, then for any `z` in the former disk we have
`dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`. -/
lemma dist_le_div_mul_dist_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R₁))
  (h_maps : maps_to f (ball c R₁) (ball (f c) R₂)) (hz : z ∈ ball c R₁) :
  dist (f z) (f c) ≤ (R₂ / R₁) * dist z c :=
begin
  rcases eq_or_ne z c with rfl|hne, { simp only [dist_self, mul_zero] },
  simpa only [dslope_of_ne _ hne, slope_def_field, abs_div, ← dist_eq, div_le_iff (dist_pos.2 hne)]
    using abs_dslope_le_div_of_maps_to_ball hd h_maps hz
end

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk of positive radius to itself and the
center of this disk to itself, then the absolute value of the derivative of `f` at the center of
this disk is at most `1`. -/
lemma abs_deriv_le_one_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R))
  (h_maps : maps_to f (ball c R) (ball c R)) (hc : f c = c) (h₀ : 0 < R) :
  abs (deriv f c) ≤ 1 :=
(abs_deriv_le_div_of_maps_to_ball hd (by rwa hc) h₀).trans_eq (div_self h₀.ne')

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk to itself and the center `c` of this
disk to itself, then for any point `z` of this disk we have `dist (f z) c ≤ dist z c`. -/
lemma dist_le_dist_of_maps_to_ball (hd : differentiable_on ℂ f (ball c R))
  (h_maps : maps_to f (ball c R) (ball c R)) (hc : f c = c) (hz : z ∈ ball c R) :
  dist (f z) c ≤ dist z c :=
have hR : 0 < R, from nonempty_ball.1 ⟨z, hz⟩,
by simpa only [hc, div_self hR.ne', one_mul]
  using dist_le_div_mul_dist_of_maps_to_ball hd (by rwa hc) hz

/-- The **Schwarz Lemma**: if `f : ℂ → ℂ` sends an open disk with center `0` to itself, the for any
point `z` of this disk we have `abs (f z) ≤ abs z`. -/
lemma abs_le_abs_of_maps_to_ball (hd : differentiable_on ℂ f (ball 0 R))
  (h_maps : maps_to f (ball 0 R) (ball 0 R)) (h₀ : f 0 = 0) (hz : abs z < R) :
  abs (f z) ≤ abs z :=
begin
  replace hz : z ∈ ball (0 : ℂ) R, from mem_ball_zero_iff.2 hz,
  simpa only [dist_zero_right] using dist_le_dist_of_maps_to_ball hd h_maps h₀ hz
end

end complex
