/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import measure_theory.function.ess_sup
import measure_theory.integral.mean_inequalities
import topology.continuous_function.compact
import topology.metric_space.metrizable
import measure_theory.function.simple_func_dense

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be strongly measurable if `f` is the sequential limit of simple functions.
It is said to be finitely strongly measurable with respect to a measure `μ` if the supports
of those simple functions have finite measure.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.
If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

## Main definitions

* `strongly_measurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`.
* `fin_strongly_measurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → simple_func α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.
* `ae_fin_strongly_measurable f μ`: `f` is almost everywhere equal to a `fin_strongly_measurable`
  function.

* `ae_fin_strongly_measurable.sigma_finite_set`: a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.

## Main statements

* `ae_fin_strongly_measurable.exists_set_sigma_finite`: there exists a measurable set `t` such that
  `f =ᵐ[μ.restrict tᶜ] 0` and `μ.restrict t` is sigma-finite.
* `mem_ℒp.ae_fin_strongly_measurable`: if `mem_ℒp f p μ` with `0 < p < ∞`, then
  `ae_fin_strongly_measurable f μ`.
* `Lp.fin_strongly_measurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.

-/

open measure_theory filter topological_space function
open_locale ennreal topological_space measure_theory

variables {α β γ : Type*}
namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

section definitions
variable [topological_space β]

/-- A function is `strongly_measurable` if it is the limit of simple functions. -/
def strongly_measurable [measurable_space α] (f : α → β) : Prop :=
∃ fs : ℕ → α →ₛ β, ∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x))

/-- A function is `fin_strongly_measurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def fin_strongly_measurable [has_zero β] {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ (∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x)))

/-- A function is `ae_strongly_measurable` with respect to a measure `μ` if it is almost everywhere
equal to the limit of a sequence of simple functions. -/
def ae_strongly_measurable {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ g, strongly_measurable g ∧ f =ᵐ[μ] g

/-- A function is `ae_fin_strongly_measurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def ae_fin_strongly_measurable [has_zero β] {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ g, fin_strongly_measurable g μ ∧ f =ᵐ[μ] g

end definitions

/-! ## Strongly measurable functions -/

lemma strongly_measurable.ae_strongly_measurable {α β} {m0 : measurable_space α}
  [topological_space β] {f : α → β} {μ : measure α} (hf : strongly_measurable f) :
  ae_strongly_measurable f μ :=
⟨f, hf, eventually_eq.refl _ _⟩

lemma subsingleton.strongly_measurable {α β} [measurable_space α] [topological_space β]
  [subsingleton β] (f : α → β) :
  strongly_measurable f :=
begin
  let f_sf : α →ₛ β := ⟨f, λ x, _,
    set.subsingleton.finite set.subsingleton_of_subsingleton⟩,
  { exact ⟨λ n, f_sf, λ x, tendsto_const_nhds⟩, },
  { have h_univ : f ⁻¹' {x} = set.univ, by { ext1 y, simp, },
    rw h_univ,
    exact measurable_set.univ, },
end

lemma simple_func.strongly_measurable {α β} {m : measurable_space α} [topological_space β]
  (f : α →ₛ β) :
  strongly_measurable f :=
⟨λ _, f, λ x, tendsto_const_nhds⟩

lemma strongly_measurable_const {α β} {m : measurable_space α} [topological_space β] {b : β} :
  strongly_measurable (λ a : α, b) :=
⟨λ n, simple_func.const α b, λ a, tendsto_const_nhds⟩

lemma strongly_measurable_zero {α β} {m : measurable_space α} [topological_space β] [has_zero β] :
  strongly_measurable (0 : α → β) :=
@strongly_measurable_const _ _ _ _ 0

namespace strongly_measurable

variables {f g : α → β}

section basic_properties_in_any_topological_space
variables [topological_space β]

/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`.
That property is given by `strongly_measurable.tendsto_approx`. -/
protected noncomputable
def approx {m : measurable_space α} (hf : strongly_measurable f) : ℕ → α →ₛ β :=
hf.some

protected lemma tendsto_approx {m : measurable_space α} (hf : strongly_measurable f) :
  ∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x)) :=
hf.some_spec

end basic_properties_in_any_topological_space

lemma fin_strongly_measurable_of_set_sigma_finite [topological_space β] [has_zero β]
  {m : measurable_space α} {μ : measure α} (hf_meas : strongly_measurable f) {t : set α}
  (ht : measurable_set t) (hft_zero : ∀ x ∈ tᶜ, f x = 0) (htμ : sigma_finite (μ.restrict t)) :
  fin_strongly_measurable f μ :=
begin
  haveI : sigma_finite (μ.restrict t) := htμ,
  let S := spanning_sets (μ.restrict t),
  have hS_meas : ∀ n, measurable_set (S n), from measurable_spanning_sets (μ.restrict t),
  let f_approx := hf_meas.approx,
  let fs := λ n, simple_func.restrict (f_approx n) (S n ∩ t),
  have h_fs_t_compl : ∀ n, ∀ x ∉ t, fs n x = 0,
  { intros n x hxt,
    rw simple_func.restrict_apply _ ((hS_meas n).inter ht),
    refine set.indicator_of_not_mem _ _,
    simp [hxt], },
  refine ⟨fs, _, λ x, _⟩,
  { simp_rw simple_func.support_eq,
    refine λ n, (measure_bUnion_finset_le _ _).trans_lt _,
    refine ennreal.sum_lt_top_iff.mpr (λ y hy, _),
    rw simple_func.restrict_preimage_singleton _ ((hS_meas n).inter ht),
    swap, { rw finset.mem_filter at hy, exact hy.2, },
    refine (measure_mono (set.inter_subset_left _ _)).trans_lt _,
    have h_lt_top := measure_spanning_sets_lt_top (μ.restrict t) n,
    rwa measure.restrict_apply' ht at h_lt_top, },
  { by_cases hxt : x ∈ t,
    swap, { rw [funext (λ n, h_fs_t_compl n x hxt), hft_zero x hxt], exact tendsto_const_nhds, },
    have h : tendsto (λ n, (f_approx n) x) at_top (𝓝 (f x)), from hf_meas.tendsto_approx x,
    obtain ⟨n₁, hn₁⟩ : ∃ n, ∀ m, n ≤ m → fs m x = f_approx m x,
    { obtain ⟨n, hn⟩ : ∃ n, ∀ m, n ≤ m → x ∈ S m ∩ t,
      { suffices : ∃ n, ∀ m, n ≤ m → x ∈ S m,
        { obtain ⟨n, hn⟩ := this,
          exact ⟨n, λ m hnm, set.mem_inter (hn m hnm) hxt⟩, },
        suffices : ∃ n, x ∈ S n,
        { rcases this with ⟨n, hn⟩,
          exact ⟨n, λ m hnm, monotone_spanning_sets (μ.restrict t) hnm hn⟩, },
        rw [← set.mem_Union, Union_spanning_sets (μ.restrict t)],
        trivial, },
      refine ⟨n, λ m hnm, _⟩,
      simp_rw [fs, simple_func.restrict_apply _ ((hS_meas m).inter ht),
        set.indicator_of_mem (hn m hnm)], },
    rw tendsto_at_top' at h ⊢,
    intros s hs,
    obtain ⟨n₂, hn₂⟩ := h s hs,
    refine ⟨max n₁ n₂, λ m hm, _⟩,
    rw hn₁ m ((le_max_left _ _).trans hm.le),
    exact hn₂ m ((le_max_right _ _).trans hm.le), },
end

/-- If the measure is sigma-finite, all strongly measurable functions are
  `fin_strongly_measurable`. -/
protected lemma fin_strongly_measurable [topological_space β] [has_zero β] {m0 : measurable_space α}
  (hf : strongly_measurable f) (μ : measure α) [sigma_finite μ] :
  fin_strongly_measurable f μ :=
hf.fin_strongly_measurable_of_set_sigma_finite measurable_set.univ (by simp)
  (by rwa measure.restrict_univ)

/-- A strongly measurable function is measurable. -/
protected lemma measurable [measurable_space α] [topological_space β] [metrizable_space β]
  [measurable_space β] [borel_space β] (hf : strongly_measurable f) :
  measurable f :=
measurable_of_tendsto_metrizable (λ n, (hf.approx n).measurable)
  (tendsto_pi_nhds.mpr hf.tendsto_approx)

lemma _root_.continuous.comp_strongly_measurable
  {m : measurable_space α} [topological_space β] [topological_space γ] {g : β → γ} {f : α → β}
  (hg : continuous g) (hf : strongly_measurable f) : strongly_measurable (λ x, g (f x)) :=
⟨λ n, simple_func.map g (hf.approx n), λ x, (hg.tendsto _).comp (hf.tendsto_approx x)⟩

section arithmetic
variables [measurable_space α] [topological_space β]

@[to_additive]
protected lemma mul [has_mul β] [has_continuous_mul β]
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f * g) :=
⟨λ n, hf.approx n * hg.approx n, λ x, (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive]
protected lemma inv [group β] [topological_group β] (hf : strongly_measurable f) :
  strongly_measurable f⁻¹ :=
⟨λ n, (hf.approx n)⁻¹, λ x, (hf.tendsto_approx x).inv⟩

@[to_additive]
protected lemma div [has_div β] [has_continuous_div β]
  (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (f / g) :=
⟨λ n, hf.approx n / hg.approx n, λ x, (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩

protected lemma const_smul {𝕜} [topological_space 𝕜] [has_scalar 𝕜 β] [has_continuous_smul 𝕜 β]
  (hf : strongly_measurable f) (c : 𝕜) :
  strongly_measurable (c • f) :=
⟨λ n, c • (hf.approx n), λ x, (hf.tendsto_approx x).const_smul c⟩

end arithmetic

protected lemma mono {m m' : measurable_space α} [topological_space β]
  (hf : @strongly_measurable α β _ m' f) (h_mono : m' ≤ m) :
  @strongly_measurable α β _ m f :=
begin
  let f_approx : ℕ → @simple_func α m β := λ n,
  { to_fun := hf.approx n,
    measurable_set_fiber' := λ x, h_mono _ (simple_func.measurable_set_fiber' _ x),
    finite_range' := simple_func.finite_range (hf.approx n) },
  exact ⟨f_approx, hf.tendsto_approx⟩,
end

protected lemma prod_mk {m : measurable_space α} [topological_space β] [topological_space γ]
  {f : α → β} {g : α → γ} (hf : strongly_measurable f) (hg : strongly_measurable g) :
  strongly_measurable (λ x, (f x, g x)) :=
begin
  refine ⟨λ n, simple_func.pair (hf.approx n) (hg.approx n), λ x, _⟩,
  rw nhds_prod_eq,
  exact tendsto.prod_mk (hf.tendsto_approx x) (hg.tendsto_approx x),
end

section order
variables [measurable_space α] [topological_space β]

open filter
open_locale filter

protected lemma sup [has_sup β] [has_continuous_sup β] (hf : strongly_measurable f)
  (hg : strongly_measurable g) :
  strongly_measurable (f ⊔ g) :=
⟨λ n, hf.approx n ⊔ hg.approx n, λ x, (hf.tendsto_approx x).sup_right_nhds (hg.tendsto_approx x)⟩

protected lemma inf [has_inf β] [has_continuous_inf β] (hf : strongly_measurable f)
  (hg : strongly_measurable g) :
  strongly_measurable (f ⊓ g) :=
⟨λ n, hf.approx n ⊓ hg.approx n, λ x, (hf.tendsto_approx x).inf_right_nhds (hg.tendsto_approx x)⟩

end order

section second_countable_strongly_measurable

variables [measurable_space α] [measurable_space β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
lemma _root_.measurable.strongly_measurable [topological_space β] [metrizable_space β]
  [second_countable_topology β] [opens_measurable_space β] (hf : measurable f) :
  strongly_measurable f :=
begin
  letI := metrizable_space_metric β,
  rcases is_empty_or_nonempty β; resetI,
  { exact subsingleton.strongly_measurable f, },
  { inhabit β,
    exact ⟨simple_func.approx_on f hf set.univ default (set.mem_univ _),
      λ x, simple_func.tendsto_approx_on hf (set.mem_univ _) (by simp)⟩, },
end

/-- A continuous function to a second countable space is strongly measurable. -/
lemma _root_.continuous.strongly_measurable [topological_space α] [opens_measurable_space α]
  {β : Type*} [topological_space β] [metrizable_space β] [second_countable_topology β]
  {f : α → β} (hf : continuous f) :
  strongly_measurable f :=
begin
  letI : measurable_space β := borel β,
  haveI : borel_space β := ⟨rfl⟩,
  exact hf.measurable.strongly_measurable,
end

lemma strongly_measurable_id [topological_space α] [metrizable_space α] [opens_measurable_space α]
  [second_countable_topology α] :
  strongly_measurable (id : α → α) :=
measurable_id.strongly_measurable

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
lemma strongly_measurable_iff_measurable [metric_space β] [borel_space β]
  [second_countable_topology β] :
  strongly_measurable f ↔ measurable f :=
⟨λ h, h.measurable, λ h, measurable.strongly_measurable h⟩

end second_countable_strongly_measurable

end strongly_measurable

/-! ## Finitely strongly measurable functions -/

lemma fin_strongly_measurable_zero {α β} {m : measurable_space α} {μ : measure α} [has_zero β]
  [topological_space β] :
  fin_strongly_measurable (0 : α → β) μ :=
⟨0, by simp only [pi.zero_apply, simple_func.coe_zero, support_zero', measure_empty,
    with_top.zero_lt_top, forall_const],
  λ n, tendsto_const_nhds⟩

namespace fin_strongly_measurable

variables {m0 : measurable_space α} {μ : measure α} {f g : α → β}

lemma ae_fin_strongly_measurable [has_zero β] [topological_space β]
  (hf : fin_strongly_measurable f μ) :
  ae_fin_strongly_measurable f μ :=
⟨f, hf, ae_eq_refl f⟩

section sequence
variables [has_zero β] [topological_space β] (hf : fin_strongly_measurable f μ)

/-- A sequence of simple functions such that `∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x))`
and `∀ n, μ (support (hf.approx n)) < ∞`. These properties are given by
`fin_strongly_measurable.tendsto_approx` and `fin_strongly_measurable.fin_support_approx`. -/
protected noncomputable def approx : ℕ → α →ₛ β := hf.some

protected lemma fin_support_approx : ∀ n, μ (support (hf.approx n)) < ∞ := hf.some_spec.1

protected lemma tendsto_approx : ∀ x, tendsto (λ n, hf.approx n x) at_top (𝓝 (f x)) :=
hf.some_spec.2

end sequence

protected lemma strongly_measurable [has_zero β] [topological_space β]
  (hf : fin_strongly_measurable f μ) :
  strongly_measurable f :=
⟨hf.approx, hf.tendsto_approx⟩

lemma exists_set_sigma_finite [has_zero β] [topological_space β] [t2_space β]
  (hf : fin_strongly_measurable f μ) :
  ∃ t, measurable_set t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ sigma_finite (μ.restrict t) :=
begin
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩,
  let T := λ n, support (fs n),
  have hT_meas : ∀ n, measurable_set (T n), from λ n, simple_func.measurable_set_support (fs n),
  let t := ⋃ n, T n,
  refine ⟨t, measurable_set.Union hT_meas, _, _⟩,
  { have h_fs_zero : ∀ n, ∀ x ∈ tᶜ, fs n x = 0,
    { intros n x hxt,
      rw [set.mem_compl_iff, set.mem_Union, not_exists] at hxt,
      simpa using (hxt n), },
    refine λ x hxt, tendsto_nhds_unique (h_approx x) _,
    rw funext (λ n, h_fs_zero n x hxt),
    exact tendsto_const_nhds, },
  { refine ⟨⟨⟨λ n, tᶜ ∪ T n, λ n, trivial, λ n, _, _⟩⟩⟩,
    { rw [measure.restrict_apply' (measurable_set.Union hT_meas), set.union_inter_distrib_right,
        set.compl_inter_self t, set.empty_union],
      exact (measure_mono (set.inter_subset_left _ _)).trans_lt (hT_lt_top n), },
    { rw ← set.union_Union tᶜ T,
      exact set.compl_union_self _ } }
end

/-- A finitely strongly measurable function is measurable. -/
protected lemma measurable [has_zero β] [topological_space β] [metrizable_space β]
  [measurable_space β] [borel_space β] (hf : fin_strongly_measurable f μ) :
  measurable f :=
hf.strongly_measurable.measurable

section arithmetic
variables [topological_space β]

protected lemma mul [monoid_with_zero β] [has_continuous_mul β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f * g) μ :=
begin
  refine ⟨λ n, hf.approx n * hg.approx n, _, λ x, (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩,
  intro n,
  apply (measure_mono _).trans_lt (hf.fin_support_approx n),
  apply support_mul_subset_left,
end

protected lemma add [add_monoid β] [has_continuous_add β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f + g) μ :=
⟨λ n, hf.approx n + hg.approx n,
  λ n, (measure_mono (function.support_add _ _)).trans_lt ((measure_union_le _ _).trans_lt
    (ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
  λ x, (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

protected lemma neg [add_group β] [topological_add_group β] (hf : fin_strongly_measurable f μ) :
  fin_strongly_measurable (-f) μ :=
begin
  refine ⟨λ n, -hf.approx n, λ n, _, λ x, (hf.tendsto_approx x).neg⟩,
  suffices : μ (function.support (λ x, - (hf.approx n) x)) < ∞, by convert this,
  rw function.support_neg (hf.approx n),
  exact hf.fin_support_approx n,
end

protected lemma sub [add_group β] [has_continuous_sub β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f - g) μ :=
⟨λ n, hf.approx n - hg.approx n,
  λ n, (measure_mono (function.support_sub _ _)).trans_lt ((measure_union_le _ _).trans_lt
    (ennreal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
  λ x, (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

protected lemma const_smul {𝕜} [topological_space 𝕜] [add_monoid β] [monoid 𝕜]
  [distrib_mul_action 𝕜 β] [has_continuous_smul 𝕜 β]
  (hf : fin_strongly_measurable f μ) (c : 𝕜) :
  fin_strongly_measurable (c • f) μ :=
begin
  refine ⟨λ n, c • (hf.approx n), λ n, _, λ x, (hf.tendsto_approx x).const_smul c⟩,
  rw simple_func.coe_smul,
  refine (measure_mono (support_smul_subset_right c _)).trans_lt (hf.fin_support_approx n),
end

end arithmetic

section order
variables [topological_space β] [has_zero β]

protected lemma sup [semilattice_sup β] [has_continuous_sup β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f ⊔ g) μ :=
begin
  refine ⟨λ n, hf.approx n ⊔ hg.approx n, λ n, _,
    λ x, (hf.tendsto_approx x).sup_right_nhds (hg.tendsto_approx x)⟩,
  refine (measure_mono (support_sup _ _)).trans_lt _,
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩,
end

protected lemma inf [semilattice_inf β] [has_continuous_inf β]
  (hf : fin_strongly_measurable f μ) (hg : fin_strongly_measurable g μ) :
  fin_strongly_measurable (f ⊓ g) μ :=
begin
  refine ⟨λ n, hf.approx n ⊓ hg.approx n, λ n, _,
    λ x, (hf.tendsto_approx x).inf_right_nhds (hg.tendsto_approx x)⟩,
  refine (measure_mono (support_inf _ _)).trans_lt _,
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩,
end

end order

end fin_strongly_measurable

lemma fin_strongly_measurable_iff_strongly_measurable_and_exists_set_sigma_finite {α β} {f : α → β}
  [topological_space β] [t2_space β] [has_zero β] {m : measurable_space α} {μ : measure α} :
  fin_strongly_measurable f μ ↔ (strongly_measurable f
    ∧ (∃ t, measurable_set t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ sigma_finite (μ.restrict t))) :=
⟨λ hf, ⟨hf.strongly_measurable, hf.exists_set_sigma_finite⟩,
  λ hf, hf.1.fin_strongly_measurable_of_set_sigma_finite hf.2.some_spec.1 hf.2.some_spec.2.1
    hf.2.some_spec.2.2⟩

lemma ae_fin_strongly_measurable_zero {α β} {m : measurable_space α} (μ : measure α) [has_zero β]
  [topological_space β] :
  ae_fin_strongly_measurable (0 : α → β) μ :=
⟨0, fin_strongly_measurable_zero, eventually_eq.rfl⟩

/-! ### Almost everywhere strongly measurable functions -/

lemma ae_strongly_measurable_const {α β} {m : measurable_space α} {μ : measure α}
  [topological_space β] {b : β} :
  ae_strongly_measurable (λ a : α, b) μ :=
strongly_measurable_const.ae_strongly_measurable

lemma ae_strongly_measurable_zero {α β} {m : measurable_space α} {μ : measure α}
  [topological_space β] [has_zero β] :
  ae_strongly_measurable (0 : α → β) μ :=
strongly_measurable_zero.ae_strongly_measurable

namespace ae_strongly_measurable

variables {m : measurable_space α} {μ : measure α} [topological_space β] [topological_space γ]
  {f g : α → β}

section mk

/-- A `strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : ae_strongly_measurable f μ) : α → β := hf.some

lemma strongly_measurable_mk (hf : ae_strongly_measurable f μ) :
  strongly_measurable (hf.mk f) :=
hf.some_spec.1

lemma measurable_mk [metrizable_space β] [measurable_space β] [borel_space β]
  (hf : ae_strongly_measurable f μ) :
  measurable (hf.mk f) :=
hf.strongly_measurable_mk.measurable

lemma ae_eq_mk (hf : ae_strongly_measurable f μ) : f =ᵐ[μ] hf.mk f :=
hf.some_spec.2

protected lemma ae_measurable {β} [measurable_space β] [topological_space β] [metrizable_space β]
  [borel_space β] {f : α → β} (hf : ae_strongly_measurable f μ) :
  ae_measurable f μ :=
⟨hf.mk f, hf.strongly_measurable_mk.measurable, hf.ae_eq_mk⟩

end mk

lemma congr (hf : ae_strongly_measurable f μ) (h : f =ᵐ[μ] g) : ae_strongly_measurable g μ :=
⟨hf.mk f, hf.strongly_measurable_mk, h.symm.trans hf.ae_eq_mk⟩

lemma _root_.ae_strongly_measurable_congr (h : f =ᵐ[μ] g) :
  ae_strongly_measurable f μ ↔ ae_strongly_measurable g μ :=
⟨λ hf, hf.congr h, λ hg, hg.congr h.symm⟩

lemma mono_measure {ν : measure α} (hf : ae_strongly_measurable f μ) (h : ν ≤ μ) :
  ae_strongly_measurable f ν :=
⟨hf.mk f, hf.strongly_measurable_mk, eventually.filter_mono (ae_mono h) hf.ae_eq_mk⟩

protected lemma mono' {ν : measure α} (h : ae_strongly_measurable f μ) (h' : ν ≪ μ) :
  ae_strongly_measurable f ν :=
⟨h.mk f, h.strongly_measurable_mk, h' h.ae_eq_mk⟩

/-- The composition of a continuous function and an ae strongly measurable function is ae strongly
measurable. -/
lemma _root_.continuous.comp_ae_strongly_measurable {g : β → γ} {f : α → β}
  (hg : continuous g) (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (λ x, g (f x)) μ :=
⟨_, hg.comp_strongly_measurable hf.strongly_measurable_mk, eventually_eq.fun_comp hf.ae_eq_mk g⟩

/-- A continuous function to a second countable space is strongly measurable. -/
lemma _root_.continuous.ae_strongly_measurable [topological_space α] [opens_measurable_space α]
  [metrizable_space β] [second_countable_topology β]  (hf : continuous f) :
  ae_strongly_measurable f μ :=
hf.strongly_measurable.ae_strongly_measurable

section arithmetic

@[to_additive]
protected lemma mul [monoid β] [has_continuous_mul β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f * g) μ :=
⟨hf.mk f * hg.mk g, hf.strongly_measurable_mk.mul hg.strongly_measurable_mk,
  hf.ae_eq_mk.mul hg.ae_eq_mk⟩

@[to_additive]
protected lemma inv [group β] [topological_group β] (hf : ae_strongly_measurable f μ) :
  ae_strongly_measurable (f⁻¹) μ :=
⟨(hf.mk f)⁻¹, hf.strongly_measurable_mk.inv, hf.ae_eq_mk.inv⟩

@[to_additive]
protected lemma div [group β] [topological_group β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f / g) μ :=
⟨hf.mk f / hg.mk g, hf.strongly_measurable_mk.div hg.strongly_measurable_mk,
  hf.ae_eq_mk.div hg.ae_eq_mk⟩

protected lemma const_smul {𝕜} [topological_space 𝕜] [has_scalar 𝕜 β] [has_continuous_smul 𝕜 β]
  (hf : ae_strongly_measurable f μ) (c : 𝕜) :
  ae_strongly_measurable (c • f) μ :=
⟨c • hf.mk f, hf.strongly_measurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

end arithmetic

section order

protected lemma sup [semilattice_sup β] [has_continuous_sup β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f ⊔ g) μ :=
⟨hf.mk f ⊔ hg.mk g, hf.strongly_measurable_mk.sup hg.strongly_measurable_mk,
  hf.ae_eq_mk.sup hg.ae_eq_mk⟩

protected lemma inf [semilattice_inf β] [has_continuous_inf β]
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (f ⊓ g) μ :=
⟨hf.mk f ⊓ hg.mk g, hf.strongly_measurable_mk.inf hg.strongly_measurable_mk,
  hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end order

protected lemma prod_mk {f : α → β} {g : α → γ}
  (hf : ae_strongly_measurable f μ) (hg : ae_strongly_measurable g μ) :
  ae_strongly_measurable (λ x, (f x, g x)) μ :=
⟨λ x, (hf.mk f x, hg.mk g x), hf.strongly_measurable_mk.prod_mk hg.strongly_measurable_mk,
  hf.ae_eq_mk.prod_mk hg.ae_eq_mk⟩

section second_countable_ae_strongly_measurable

variables [measurable_space β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
lemma _root_.ae_measurable.ae_strongly_measurable [metrizable_space β]
  [opens_measurable_space β] [second_countable_topology β] (hf : ae_measurable f μ) :
  ae_strongly_measurable f μ :=
⟨hf.mk f, hf.measurable_mk.strongly_measurable, hf.ae_eq_mk⟩

lemma ae_strongly_measurable_id {α : Type*} [topological_space α] [metrizable_space α]
  {m : measurable_space α} [opens_measurable_space α] [second_countable_topology α]
  {μ : measure α} :
  ae_strongly_measurable (id : α → α) μ :=
ae_measurable_id.ae_strongly_measurable

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
lemma ae_strongly_measurable_iff_ae_measurable [metrizable_space β] [borel_space β]
  [second_countable_topology β] :
  ae_strongly_measurable f μ ↔ ae_measurable f μ :=
⟨λ h, h.ae_measurable, λ h, h.ae_strongly_measurable⟩

end second_countable_ae_strongly_measurable

end ae_strongly_measurable

/-! ### Almost everywhere finitely strongly measurable functions -/

namespace ae_fin_strongly_measurable

variables {m : measurable_space α} {μ : measure α} [topological_space β]
  {f g : α → β}

section mk
variables [has_zero β]

/-- A `fin_strongly_measurable` function such that `f =ᵐ[μ] hf.mk f`. See lemmas
`fin_strongly_measurable_mk` and `ae_eq_mk`. -/
protected noncomputable def mk (f : α → β) (hf : ae_fin_strongly_measurable f μ) : α → β := hf.some

lemma fin_strongly_measurable_mk (hf : ae_fin_strongly_measurable f μ) :
  fin_strongly_measurable (hf.mk f) μ :=
hf.some_spec.1

lemma ae_eq_mk (hf : ae_fin_strongly_measurable f μ) : f =ᵐ[μ] hf.mk f :=
hf.some_spec.2

protected lemma ae_measurable {β} [has_zero β] [measurable_space β] [topological_space β]
  [metrizable_space β] [borel_space β]
  {f : α → β} (hf : ae_fin_strongly_measurable f μ) :
  ae_measurable f μ :=
⟨hf.mk f, hf.fin_strongly_measurable_mk.measurable, hf.ae_eq_mk⟩

end mk

section arithmetic

protected lemma mul [monoid_with_zero β] [has_continuous_mul β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f * g) μ :=
⟨hf.mk f * hg.mk g, hf.fin_strongly_measurable_mk.mul hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.mul hg.ae_eq_mk⟩

protected lemma add [add_monoid β] [has_continuous_add β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f + g) μ :=
⟨hf.mk f + hg.mk g, hf.fin_strongly_measurable_mk.add hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.add hg.ae_eq_mk⟩

protected lemma neg [add_group β] [topological_add_group β] (hf : ae_fin_strongly_measurable f μ) :
  ae_fin_strongly_measurable (-f) μ :=
⟨-hf.mk f, hf.fin_strongly_measurable_mk.neg, hf.ae_eq_mk.neg⟩

protected lemma sub [add_group β] [has_continuous_sub β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f - g) μ :=
⟨hf.mk f - hg.mk g, hf.fin_strongly_measurable_mk.sub hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.sub hg.ae_eq_mk⟩

protected lemma const_smul {𝕜} [topological_space 𝕜] [add_monoid β] [monoid 𝕜]
  [distrib_mul_action 𝕜 β] [has_continuous_smul 𝕜 β]
  (hf : ae_fin_strongly_measurable f μ) (c : 𝕜) :
  ae_fin_strongly_measurable (c • f) μ :=
⟨c • hf.mk f, hf.fin_strongly_measurable_mk.const_smul c, hf.ae_eq_mk.const_smul c⟩

end arithmetic

section order
variables [has_zero β]

protected lemma sup [semilattice_sup β] [has_continuous_sup β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f ⊔ g) μ :=
⟨hf.mk f ⊔ hg.mk g, hf.fin_strongly_measurable_mk.sup hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.sup hg.ae_eq_mk⟩

protected lemma inf [semilattice_inf β] [has_continuous_inf β]
  (hf : ae_fin_strongly_measurable f μ) (hg : ae_fin_strongly_measurable g μ) :
  ae_fin_strongly_measurable (f ⊓ g) μ :=
⟨hf.mk f ⊓ hg.mk g, hf.fin_strongly_measurable_mk.inf hg.fin_strongly_measurable_mk,
  hf.ae_eq_mk.inf hg.ae_eq_mk⟩

end order

variables [has_zero β] [t2_space β]

lemma exists_set_sigma_finite (hf : ae_fin_strongly_measurable f μ) :
  ∃ t, measurable_set t ∧ f =ᵐ[μ.restrict tᶜ] 0 ∧ sigma_finite (μ.restrict t) :=
begin
  rcases hf with ⟨g, hg, hfg⟩,
  obtain ⟨t, ht, hgt_zero, htμ⟩ := hg.exists_set_sigma_finite,
  refine ⟨t, ht, _, htμ⟩,
  refine eventually_eq.trans (ae_restrict_of_ae hfg) _,
  rw [eventually_eq, ae_restrict_iff' ht.compl],
  exact eventually_of_forall hgt_zero,
end

/-- A measurable set `t` such that `f =ᵐ[μ.restrict tᶜ] 0` and `sigma_finite (μ.restrict t)`. -/
def sigma_finite_set (hf : ae_fin_strongly_measurable f μ) : set α :=
hf.exists_set_sigma_finite.some

protected lemma measurable_set (hf : ae_fin_strongly_measurable f μ) :
  measurable_set hf.sigma_finite_set :=
hf.exists_set_sigma_finite.some_spec.1

lemma ae_eq_zero_compl (hf : ae_fin_strongly_measurable f μ) :
  f =ᵐ[μ.restrict hf.sigma_finite_setᶜ] 0 :=
hf.exists_set_sigma_finite.some_spec.2.1

instance sigma_finite_restrict (hf : ae_fin_strongly_measurable f μ) :
  sigma_finite (μ.restrict hf.sigma_finite_set) :=
hf.exists_set_sigma_finite.some_spec.2.2

end ae_fin_strongly_measurable

end measure_theory
