/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.special_functions.log.deriv
import measure_theory.integral.fund_thm_calculus

/-!
# Non integrable functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the derivative of a function that tends to infinity is not interval
integrable, see `interval_integral.not_integrable_has_deriv_at_of_tendsto_norm_at_top_filter` and
`interval_integral.not_integrable_has_deriv_at_of_tendsto_norm_at_top_punctured`.  Then we apply the
latter lemma to prove that the function `λ x, x⁻¹` is integrable on `a..b` if and only if `a = b` or
`0 ∉ [a, b]`.

## Main results

* `not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured`: if `f` tends to infinity
  along `𝓝[≠] c` and `f' = O(g)` along the same filter, then `g` is not interval integrable on any
  nontrivial integral `a..b`, `c ∈ [a, b]`.

* `not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_filter`: a version of
  `not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured` that works for one-sided
  neighborhoods;

* `not_interval_integrable_of_sub_inv_is_O_punctured`: if `1 / (x - c) = O(f)` as `x → c`, `x ≠ c`,
  then `f` is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`;

* `interval_integrable_sub_inv_iff`, `interval_integrable_inv_iff`: integrability conditions for
  `(x - c)⁻¹` and `x⁻¹`.

## Tags

integrable function
-/

open_locale measure_theory topology interval nnreal ennreal
open measure_theory topological_space set filter asymptotics interval_integral

variables {E F : Type*} [normed_add_comm_group E] [normed_space ℝ E] [second_countable_topology E]
[complete_space E] [normed_add_comm_group F]

/-- If `f` is eventually differentiable along a nontrivial filter `l : filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` along `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any interval `a..b` such that
`[a, b] ∈ l`. -/
lemma not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_filter {f : ℝ → E} {g : ℝ → F}
  {a b : ℝ} (l : filter ℝ) [ne_bot l] [tendsto_Ixx_class Icc l l] (hl : [a, b] ∈ l)
  (hd : ∀ᶠ x in l, differentiable_at ℝ f x) (hf : tendsto (λ x, ‖f x‖) l at_top)
  (hfg : deriv f =O[l] g) :
  ¬interval_integrable g volume a b :=
begin
  intro hgi,
  obtain ⟨C, hC₀, s, hsl, hsub, hfd, hg⟩ : ∃ (C : ℝ) (hC₀ : 0 ≤ C) (s ∈ l),
    (∀ (x ∈ s) (y ∈ s), [x, y] ⊆ [a, b]) ∧
    (∀ (x ∈ s) (y ∈ s) (z ∈ [x, y]), differentiable_at ℝ f z) ∧
    (∀ (x ∈ s) (y ∈ s) (z ∈ [x, y]), ‖deriv f z‖ ≤ C * ‖g z‖),
  { rcases hfg.exists_nonneg with ⟨C, C₀, hC⟩,
    have h : ∀ᶠ x : ℝ × ℝ in l.prod l, ∀ y ∈ [x.1, x.2], (differentiable_at ℝ f y ∧
      ‖deriv f y‖ ≤ C * ‖g y‖) ∧ y ∈ [a, b],
      from (tendsto_fst.uIcc tendsto_snd).eventually ((hd.and hC.bound).and hl).small_sets,
    rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩,
    simp only [prod_subset_iff, mem_set_of_eq] at hs,
    exact ⟨C, C₀, s, hsl, λ x hx y hy z hz, (hs x hx y hy z hz).2,
      λ x hx y hy z hz, (hs x hx y hy z hz).1.1, λ x hx y hy z hz, (hs x hx y hy z hz).1.2⟩ },
  replace hgi : interval_integrable (λ x, C * ‖g x‖) volume a b, by convert hgi.norm.smul C,
  obtain ⟨c, hc, d, hd, hlt⟩ : ∃ (c ∈ s) (d ∈ s), ‖f c‖ + ∫ y in Ι a b, C * ‖g y‖ < ‖f d‖,
  { rcases filter.nonempty_of_mem hsl with ⟨c, hc⟩,
    have : ∀ᶠ x in l, ‖f c‖ + ∫ y in Ι a b, C * ‖g y‖ < ‖f x‖,
      from hf.eventually (eventually_gt_at_top _),
    exact ⟨c, hc, (this.and hsl).exists.imp (λ d hd, ⟨hd.2, hd.1⟩)⟩ },
  specialize hsub c hc d hd, specialize hfd c hc d hd,
  replace hg : ∀ x ∈ Ι c d, ‖deriv f x‖ ≤ C * ‖g x‖, from λ z hz, hg c hc d hd z ⟨hz.1.le, hz.2⟩,
  have hg_ae : ∀ᵐ x ∂(volume.restrict (Ι c d)), ‖deriv f x‖ ≤ C * ‖g x‖,
    from (ae_restrict_mem measurable_set_uIoc).mono hg,
  have hsub' : Ι c d ⊆ Ι a b,
    from uIoc_subset_uIoc_of_uIcc_subset_uIcc hsub,
  have hfi : interval_integrable (deriv f) volume c d,
    from (hgi.mono_set hsub).mono_fun' (ae_strongly_measurable_deriv _ _) hg_ae,
  refine hlt.not_le (sub_le_iff_le_add'.1 _),
  calc ‖f d‖ - ‖f c‖ ≤ ‖f d - f c‖ : norm_sub_norm_le _ _
  ... = ‖∫_{c}^{d} x, deriv f x‖ : congr_arg _ (integral_deriv_eq_sub hfd hfi).symm
  ... = ‖∫ x in Ι c d, deriv f x‖ : norm_integral_eq_norm_integral_Ioc _
  ... ≤ ∫ x in Ι c d, ‖deriv f x‖ : norm_integral_le_integral_norm _
  ... ≤ ∫ x in Ι c d, C * ‖g x‖ :
    set_integral_mono_on hfi.norm.def (hgi.def.mono_set hsub') measurable_set_uIoc hg
  ... ≤ ∫ x in Ι a b, C * ‖g x‖ :
    set_integral_mono_set hgi.def (ae_of_all _ $ λ x, mul_nonneg hC₀ (norm_nonneg _))
      hsub'.eventually_le
end

/-- If `a ≠ b`, `c ∈ [a, b]`, `f` is differentiable in the neighborhood of `c` within
`[a, b] \ {c}`, `‖f x‖ → ∞` as `x → c` within `[a, b] \ {c}`, and `f' = O(g)` along
`𝓝[[a, b] \ {c}] c`, where `f'` is the derivative of `f`, then `g` is not interval integrable on
`a..b`. -/
lemma not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_within_diff_singleton
  {f : ℝ → E} {g : ℝ → F} {a b c : ℝ} (hne : a ≠ b) (hc : c ∈ [a, b])
  (h_deriv : ∀ᶠ x in 𝓝[[a, b] \ {c}] c, differentiable_at ℝ f x)
  (h_infty : tendsto (λ x, ‖f x‖) (𝓝[[a, b] \ {c}] c) at_top)
  (hg : deriv f =O[𝓝[[a, b] \ {c}] c] g) :
  ¬interval_integrable g volume a b :=
begin
  obtain ⟨l, hl, hl', hle, hmem⟩ : ∃ l : filter ℝ, tendsto_Ixx_class Icc l l ∧ l.ne_bot ∧
    l ≤ 𝓝 c ∧ [a, b] \ {c} ∈ l,
  { cases (min_lt_max.2 hne).lt_or_lt c with hlt hlt,
    { refine ⟨𝓝[<] c, infer_instance, infer_instance, inf_le_left, _⟩,
      rw ← Iic_diff_right,
      exact diff_mem_nhds_within_diff (Icc_mem_nhds_within_Iic ⟨hlt, hc.2⟩) _ },
    { refine ⟨𝓝[>] c, infer_instance, infer_instance, inf_le_left, _⟩,
      rw ← Ici_diff_left,
      exact diff_mem_nhds_within_diff (Icc_mem_nhds_within_Ici ⟨hc.1, hlt⟩) _ } },
  resetI,
  have : l ≤ 𝓝[[a, b] \ {c}] c, from le_inf hle (le_principal_iff.2 hmem),
  exact not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_filter l
    (mem_of_superset hmem (diff_subset _ _))
    (h_deriv.filter_mono this) (h_infty.mono_left this) (hg.mono this),
end

/-- If `f` is differentiable in a punctured neighborhood of `c`, `‖f x‖ → ∞` as `x → c` (more
formally, along the filter `𝓝[≠] c`), and `f' = O(g)` along `𝓝[≠] c`, where `f'` is the derivative
of `f`, then `g` is not interval integrable on any nontrivial interval `a..b` such that
`c ∈ [a, b]`. -/
lemma not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured {f : ℝ → E} {g : ℝ → F}
  {a b c : ℝ} (h_deriv : ∀ᶠ x in 𝓝[≠] c, differentiable_at ℝ f x)
  (h_infty : tendsto (λ x, ‖f x‖) (𝓝[≠] c) at_top) (hg : deriv f =O[𝓝[≠] c] g)
  (hne : a ≠ b) (hc : c ∈ [a, b]) :
  ¬interval_integrable g volume a b :=
have 𝓝[[a, b] \ {c}] c ≤ 𝓝[≠] c, from nhds_within_mono _ (inter_subset_right _ _),
not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_within_diff_singleton hne hc
  (h_deriv.filter_mono this) (h_infty.mono_left this) (hg.mono this)

/-- If `f` grows in the punctured neighborhood of `c : ℝ` at least as fast as `1 / (x - c)`,
then it is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`. -/
lemma not_interval_integrable_of_sub_inv_is_O_punctured {f : ℝ → F} {a b c : ℝ}
  (hf : (λ x, (x - c)⁻¹) =O[𝓝[≠] c] f) (hne : a ≠ b) (hc : c ∈ [a, b]) :
  ¬interval_integrable f volume a b :=
begin
  have A : ∀ᶠ x in 𝓝[≠] c, has_deriv_at (λ x, real.log (x - c)) (x - c)⁻¹ x,
  { filter_upwards [self_mem_nhds_within] with x hx,
    simpa using ((has_deriv_at_id x).sub_const c).log (sub_ne_zero.2 hx) },
  have B : tendsto (λ x, ‖real.log (x - c)‖) (𝓝[≠] c) at_top,
  { refine tendsto_abs_at_bot_at_top.comp (real.tendsto_log_nhds_within_zero.comp _),
    rw ← sub_self c,
    exact ((has_deriv_at_id c).sub_const c).tendsto_punctured_nhds one_ne_zero },
  exact not_interval_integrable_of_tendsto_norm_at_top_of_deriv_is_O_punctured
    (A.mono (λ x hx, hx.differentiable_at)) B
    (hf.congr' (A.mono $ λ x hx, hx.deriv.symm) eventually_eq.rfl) hne hc
end

/-- The function `λ x, (x - c)⁻¹` is integrable on `a..b` if and only if `a = b` or `c ∉ [a, b]`. -/
@[simp] lemma interval_integrable_sub_inv_iff {a b c : ℝ} :
  interval_integrable (λ x, (x - c)⁻¹) volume a b ↔ a = b ∨ c ∉ [a, b] :=
begin
  split,
  { refine λ h, or_iff_not_imp_left.2 (λ hne hc, _),
    exact not_interval_integrable_of_sub_inv_is_O_punctured (is_O_refl _ _) hne hc h },
  { rintro (rfl|h₀),
    { exact interval_integrable.refl },
    refine ((continuous_sub_right c).continuous_on.inv₀ _).interval_integrable,
    exact λ x hx, sub_ne_zero.2 $ ne_of_mem_of_not_mem hx h₀ }
end

/-- The function `λ x, x⁻¹` is integrable on `a..b` if and only if `a = b` or `0 ∉ [a, b]`. -/
@[simp] lemma interval_integrable_inv_iff {a b : ℝ} :
  interval_integrable (λ x, x⁻¹) volume a b ↔ a = b ∨ (0 : ℝ) ∉ [a, b] :=
by simp only [← interval_integrable_sub_inv_iff, sub_zero]
