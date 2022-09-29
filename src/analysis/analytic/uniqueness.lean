/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.analytic.linear
import analysis.analytic.composition
import analysis.normed_space.completion

/-!
# Uniqueness principle for analytic functions

We show that two analytic functions which coincide around a point coincide on whole connected sets,
in `analytic_on.eq_on_of_preconnected_of_eventually_eq`.
-/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

open set
open_locale topological_space ennreal

/-- If a preconnected set `s` intersects an open set `u`, and limit points of `u` inside `s` are
contained in `u`, then the whole set `s` is contained in `u`. -/
lemma is_preconnected.subset_of_closure_inter_subset {α : Type*} [topological_space α]
  {s u : set α} (hs : is_preconnected s) (hu : is_open u) (h'u : (s ∩ u).nonempty)
  (h : closure u ∩ s ⊆ u) : s ⊆ u :=
begin
  have A : s ⊆ u ∪ (closure u)ᶜ,
  { assume x hx,
    by_cases xu : x ∈ u,
    { exact or.inl xu },
    { right,
      assume h'x,
      exact xu (h (mem_inter h'x hx)) } },
  apply hs.subset_left_of_subset_union hu is_closed_closure.is_open_compl _ A h'u,
  exact disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure),
end

namespace analytic_on

/-- If an analytic function vanishes around a point, then it is uniformly zero along
a connected set. Superseded by `eq_on_zero_of_preconnected_of_locally_zero` which does not assume
completeness of the target space. -/
theorem eq_on_zero_of_preconnected_of_eventually_eq_zero_aux [complete_space F]
  {f : E → F} {U : set E} (hf : analytic_on 𝕜 f U) (hU : is_preconnected U) {w : E}
  (hw : w ∈ U) (hfw : f =ᶠ[𝓝 w] 0) : eq_on f 0 U :=
begin
  /- Let `u` be the set of points around which `f` vanishes. It is clearly open. We have to show
  that its limit points in `U` still belong to it, from which the inclusion `U ⊆ u` will follow
  by connectedness.
  Take a limit point `x`, then a ball `B (x, r)` on which it has a power series expansion, and
  then `y ∈ B (x, r/2) ∩ u`. Then `f` has a power series expansion on `B (y, r/2)` as it is
  contained in `B (x, r)`. All the coefficients in this series expansion vanish, as `f` is zero on a
  neighborhood of `y`. Therefore, `f` is zero on `B (y, r/2)`. As this ball contains `x`, it follows
  that `f` vanishes on a neighborhood of `x`, proving the claim. -/
  let u := {x | f =ᶠ[𝓝 x] 0},
  have main : closure u ∩ U ⊆ u,
  { rintros x ⟨xu, xU⟩,
    rcases hf x xU with ⟨p, r, hp⟩,
    obtain ⟨y, yu, hxy⟩ : ∃ y ∈ u, edist x y < r / 2,
      from emetric.mem_closure_iff.1 xu (r / 2) (ennreal.half_pos hp.r_pos.ne'),
    let q := p.change_origin (y - x),
    have has_series : has_fpower_series_on_ball f q y (r / 2),
    { have A : (∥y - x∥₊ : ℝ≥0∞) < r / 2, by rwa [edist_comm, edist_eq_coe_nnnorm_sub] at hxy,
      have := hp.change_origin (A.trans_le ennreal.half_le_self),
      simp only [add_sub_cancel'_right] at this,
      apply this.mono (ennreal.half_pos hp.r_pos.ne'),
      apply ennreal.le_sub_of_add_le_left ennreal.coe_ne_top,
      apply (add_le_add (A.le) (le_refl (r / 2))).trans (le_of_eq _),
      exact ennreal.add_halves _ },
    have M : emetric.ball y (r / 2) ∈ 𝓝 x, from emetric.is_open_ball.mem_nhds hxy,
    filter_upwards [M] with z hz,
    have A : has_sum (λ (n : ℕ), q n (λ (i : fin n), z - y)) (f z) := has_series.has_sum_sub hz,
    have B : has_sum (λ (n : ℕ), q n (λ (i : fin n), z - y)) (0),
    { have : has_fpower_series_at 0 q y, from has_series.has_fpower_series_at.congr yu,
      convert has_sum_zero,
      ext n,
      exact this.apply_eq_zero n _ },
    exact has_sum.unique A B },
  have Uu : U ⊆ u, from
    hU.subset_of_closure_inter_subset is_open_set_of_eventually_nhds ⟨w, hw, hfw⟩ main,
  assume z hz,
  simpa using mem_of_mem_nhds (Uu hz),
end

/-- The *identity principle* for analytic functions: If an analytic function vanishes in a whole
neighborhood of a point `z₀`, then it is uniformly zero along a connected set. For a one-dimensional
version assuming only that the function vanishes at some points arbitrarily close to `z₀`, see
`eq_on_zero_of_preconnected_of_frequently_eq_zero`. -/
theorem eq_on_zero_of_preconnected_of_eventually_eq_zero
  {f : E → F} {U : set E} (hf : analytic_on 𝕜 f U) (hU : is_preconnected U) {w : E}
  (hw : w ∈ U) (hfw : f =ᶠ[𝓝 w] 0) :
  eq_on f 0 U :=
begin
  let F' := uniform_space.completion F,
  set e : F →L[𝕜] F' := uniform_space.completion.to_complL,
  have : analytic_on 𝕜 (e ∘ f) U := λ x hx, (e.analytic_at _).comp (hf x hx),
  have A : eq_on (e ∘ f) 0 U,
  { apply eq_on_zero_of_preconnected_of_eventually_eq_zero_aux this hU hw,
    filter_upwards [hfw] with x hx,
    simp only [hx, function.comp_app, pi.zero_apply, map_zero] },
  assume z hz,
  have : e (f z) = e 0, by simpa only using A hz,
  exact uniform_space.completion.coe_injective F this,
end

/-- The *identity principle* for analytic functions: If two analytic function coincide in a whole
neighborhood of a point `z₀`, then they coincide globally along a connected set.
For a one-dimensional version assuming only that the functions coincide at some points
arbitrarily close to `z₀`, see `eq_on_of_preconnected_of_frequently_eq`. -/
theorem eq_on_of_preconnected_of_eventually_eq
  {f g : E → F} {U : set E} (hf : analytic_on 𝕜 f U) (hg : analytic_on 𝕜 g U)
  (hU : is_preconnected U) {w : E} (hw : w ∈ U) (hfg : f =ᶠ[𝓝 w] g) :
  eq_on f g U :=
begin
  have hfg' : (f - g) =ᶠ[𝓝 w] 0 := hfg.mono (λ z h, by simp [h]),
  simpa [sub_eq_zero] using
    λ z hz, (hf.sub hg).eq_on_zero_of_preconnected_of_eventually_eq_zero hU hw hfg' hz,
end

end analytic_on
