/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.simple_func_dense

/-!
# Strongly measurable functions

A function `f` is said to be strongly measurable with respect to a measure `μ` if `f` is the
sequential limit of simple functions whose support has finite measure.

Functions in `Lp` for `0 < p < ∞` are strongly measurable.
If the measure is sigma-finite, measurable and strongly measurable are equivalent.

The main property of strongly measurable functions is `strongly_measurable.exists_set_sigma_finite`:
there exists a measurable set `t` such that `f` is supported on `t` and `μ.restrict t` is
sigma-finite. As a consequence, we can prove some results for those functions as if the measure was
sigma-finite.

## Main definitions

* `strongly_measurable f μ`: `f : α → γ` is the limit of a sequence `fs : ℕ → simple_func α γ`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.
* `strongly_measurable.sigma_finite_set`: a measurable set `t` such that `∀ x ∈ tᶜ, f x = 0` and
  `μ.restrict t` is sigma-finite.

## Main statements

* `strongly_measurable.exists_set_sigma_finite`: if a function `f` is strongly measurable with
  respect to a measure `μ`, then there exists a measurable set `t` such that `∀ x ∈ tᶜ, f x = 0`
  and `sigma_finite (μ.restrict t)`.
* `mem_ℒp.ae_strongly_measurable`: if `mem_ℒp f p μ` with `0 < p < ∞`, then
  `∃ g, strongly_measurable g μ ∧ f =ᵐ[μ] g`.
* `Lp.strongly_measurable`: for `0 < p < ∞`, `Lp` functions are strongly measurable.
* `stongly_measurable.measurable`: a stongly measurable function is measurable.
* `measurable.strongly_measurable`: if a measure is sigma-finite, then all measurable functions are
  strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.

-/

open measure_theory filter topological_space function
open_locale ennreal topological_space measure_theory

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

section definitions
variables {α β : Type*} [topological_space β]

/-- A function is `strongly_measurable` if it is the limit of simple functions. -/
def strongly_measurable [measurable_space α] (f : α → β) : Prop :=
∃ fs : ℕ → α →ₛ β, ∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x))

/-- A function is `ae_strongly_measurable` if it is the almost everywhere limit of simple
  functions. -/
def ae_strongly_measurable {m0 : measurable_space α} (f : α → β) (μ : measure α) : Prop :=
∃ g, strongly_measurable g ∧ f =ᵐ[μ] g

/-- A function is `fin_strongly_measurable` with respect to a measure if it is the limit of simple
  functions with support with finite measure. -/
def fin_strongly_measurable [has_zero β] {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ fs : ℕ → α →ₛ β, (∀ n, μ (support (fs n)) < ∞) ∧ (∀ x, tendsto (λ n, fs n x) at_top (𝓝 (f x)))

/-- A function is `ae_fin_strongly_measurable` with respect to a measure if it is almost everywhere
equal to the limit of a sequence of simple functions with support with finite measure. -/
def ae_fin_strongly_measurable [has_zero β] {m0 : measurable_space α} (f : α → β) (μ : measure α) :
  Prop :=
∃ g, fin_strongly_measurable g μ ∧ f =ᵐ[μ] g

end definitions

lemma simple_func.measurable_set_support {α H : Type*} [has_zero H] [measurable_space α]
  (f : α →ₛ H) :
  measurable_set (support f) :=
begin
  rw f.support_eq,
  exact finset.measurable_set_bUnion _ (λ y hy, simple_func.measurable_set_fiber _ _),
end

lemma simple_func.measure_support_lt_top_of_mem_ℒp {α H : Type*} [measurable_space H]
  [normed_group H] {m : measurable_space α} {μ : measure α} {p : ℝ≥0∞}
  (f : α →ₛ H) (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  μ (support f) < ∞ :=
begin
  rw simple_func.support_eq,
  refine (measure_bUnion_finset_le _ _).trans_lt (ennreal.sum_lt_top_iff.mpr (λ y hy, _)),
  refine f.measure_preimage_lt_top_of_mem_ℒp (pos_iff_ne_zero.mpr hp_ne_zero) hp_ne_top hf _ _,
  sorry,
  --classical,
  --exact (finset.mem_filter.mp hy).2,
end

namespace strongly_measurable

lemma ae_strongly_measurable {α β : Type*} {m : measurable_space α} [topological_space β]
  {f : α → β} (hf : strongly_measurable f) (μ : measure α) :
  ae_strongly_measurable f μ :=
⟨f, hf, ae_eq_refl f⟩

variables {α β : Type*} {f : α → β}

protected noncomputable
def seq [measurable_space α] [topological_space β] (hf : strongly_measurable f) : ℕ → α →ₛ β :=
hf.some

protected lemma tendsto_seq [measurable_space α] [topological_space β]
  (hf : strongly_measurable f) :
  ∀ x, tendsto (λ n, hf.seq n x) at_top (𝓝 (f x)) :=
hf.some_spec

lemma fin_strongly_measurable_of_exists_set_sigma_finite [topological_space β] [has_zero β]
  {m : measurable_space α} {μ : measure α} (hf_meas : strongly_measurable f)
  (hf : ∃ t, measurable_set t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ sigma_finite (μ.restrict t)) :
  fin_strongly_measurable f μ :=
begin
  obtain ⟨t, ht, hft_zero, htμ⟩ := hf,
  haveI : sigma_finite (μ.restrict t) := htμ,
  let S := spanning_sets (μ.restrict t),
  have hS_meas : ∀ n, measurable_set (S n), from measurable_spanning_sets (μ.restrict t),
  let f_approx := hf_meas.seq,
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
    swap, { sorry, },
    refine (measure_mono (set.inter_subset_left _ _)).trans_lt _,
    have h_lt_top := measure_spanning_sets_lt_top (μ.restrict t) n,
    rwa measure.restrict_apply' ht at h_lt_top, },
  { by_cases hxt : x ∈ t,
    swap, { rw [funext (λ n, h_fs_t_compl n x hxt), hft_zero x hxt], exact tendsto_const_nhds, },
    have h : tendsto (λ n, (f_approx n) x) at_top (𝓝 (f x)), from hf_meas.tendsto_seq x,
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
lemma fin_strongly_measurable [topological_space β] [has_zero β] {m0 : measurable_space α}
  (hf : strongly_measurable f) (μ : measure α) [sigma_finite μ] :
  fin_strongly_measurable f μ :=
hf.fin_strongly_measurable_of_exists_set_sigma_finite
  ⟨set.univ, measurable_set.univ, by simp, by rwa measure.restrict_univ⟩

/-- A strongly measurable function is measurable. -/
lemma measurable [measurable_space α] [metric_space β] [measurable_space β] [borel_space β]
  (hf : strongly_measurable f) :
  measurable f :=
measurable_of_tendsto_metric (λ n, (hf.seq n).measurable) (tendsto_pi.mpr hf.tendsto_seq)

end strongly_measurable

/-- In a space with second countable topology, measurable implies strongly measurable.
  TODO: remove the `nonempty β` hypothesis? -/
lemma measurable.strongly_measurable {α β} [measurable_space α] [emetric_space β]
  [measurable_space β] [opens_measurable_space β] [second_countable_topology β] [hβ : nonempty β]
  {f : α → β} (hf : measurable f) :
  strongly_measurable f :=
⟨simple_func.approx_on f hf set.univ hβ.some (set.mem_univ hβ.some),
  λ x, simple_func.tendsto_approx_on hf (set.mem_univ _) (by simp)⟩

/-- In a space with second countable topology, strongly measurable and measurable are equivalent. -/
lemma strongly_measurable_iff_measurable {α β} [measurable_space α] [metric_space β]
  [measurable_space β] [borel_space β] [second_countable_topology β] [hβ : nonempty β]
  {f : α → β} :
  strongly_measurable f ↔ measurable f :=
⟨λ h, h.measurable, λ h, measurable.strongly_measurable h⟩

namespace fin_strongly_measurable

variables {α β : Type*} [has_zero β] {m0 : measurable_space α} {μ : measure α} {f : α → β}

lemma ae_fin_strongly_measurable [topological_space β] (hf : fin_strongly_measurable f μ) :
  ae_fin_strongly_measurable f μ :=
⟨f, hf, ae_eq_refl f⟩

section sequence
variables [topological_space β] (hf : fin_strongly_measurable f μ)

protected noncomputable def seq : ℕ → α →ₛ β := hf.some

protected lemma fin_support : ∀ n, μ (support (hf.seq n)) < ∞ := hf.some_spec.1

protected lemma tendsto_seq : ∀ x, tendsto (λ n, hf.seq n x) at_top (𝓝 (f x)) := hf.some_spec.2

lemma strongly_measurable : strongly_measurable f := ⟨hf.seq, hf.tendsto_seq⟩

end sequence

lemma exists_set_sigma_finite [topological_space β] [t2_space β]
  (hf : fin_strongly_measurable f μ) :
  ∃ t, measurable_set t ∧ (∀ x ∈ tᶜ, f x = 0) ∧ sigma_finite (μ.restrict t) :=
begin
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩,
  let T := λ n, support (fs n),
  have hT_meas : ∀ n, measurable_set (T n), from λ n, simple_func.measurable_set_support _,
  let t := ⋃ n, T n,
  refine ⟨t, measurable_set.Union hT_meas, _, _⟩,
  { have h_fs_zero : ∀ n, ∀ x ∈ tᶜ, fs n x = 0,
    { intros n x hxt,
      rw [set.mem_compl_iff, set.mem_Union, not_exists] at hxt,
      simpa using (hxt n), },
    refine λ x hxt, tendsto_nhds_unique (h_approx x) _,
    rw funext (λ n, h_fs_zero n x hxt),
    exact tendsto_const_nhds, },
  { refine measure.finite_spanning_sets_in.sigma_finite _ _,
    { exact set.range (λ n, tᶜ ∪ T n), },
    { refine ⟨λ n, tᶜ ∪ T n, λ n, set.mem_range_self _, λ n, _, _⟩,
      { rw [measure.restrict_apply' (measurable_set.Union hT_meas), set.union_inter_distrib_right,
          set.compl_inter_self t, set.empty_union],
        exact (measure_mono (set.inter_subset_left _ _)).trans_lt (hT_lt_top n), },
      rw ← set.union_Union tᶜ T,
      exact set.compl_union_self _, },
    { intros s hs,
      rw set.mem_range at hs,
      cases hs with n hsn,
      rw ← hsn,
      exact (measurable_set.compl (measurable_set.Union hT_meas)).union (hT_meas n), }, },
end

/-- A strongly measurable function is measurable. -/
protected lemma measurable [metric_space β] [measurable_space β] [borel_space β]
  (hf : fin_strongly_measurable f μ) :
  measurable f :=
measurable_of_tendsto_metric (λ n, (hf.some n).measurable) (tendsto_pi.mpr hf.some_spec.2)

end fin_strongly_measurable

namespace ae_fin_strongly_measurable

variables {α β : Type*} {m : measurable_space α} {μ : measure α} [has_zero β] [topological_space β]
  [t2_space β] {f : α → β}

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

lemma sigma_finite_restrict (hf : ae_fin_strongly_measurable f μ) :
  sigma_finite (μ.restrict hf.sigma_finite_set) :=
hf.exists_set_sigma_finite.some_spec.2.2

end ae_fin_strongly_measurable


variables {α G : Type*} {p : ℝ≥0∞} {m m0 : measurable_space α} {μ : measure α}
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  {f : α → G}

/-- In a space with second countable topology and a sigma-finite measure, `fin_strongly_measurable`
  and `measurable` are equivalent. -/
lemma fin_strongly_measurable_iff_measurable {m0 : measurable_space α} (μ : measure α)
  [sigma_finite μ] :
  fin_strongly_measurable f μ ↔ measurable f :=
⟨λ h, h.measurable, λ h, (measurable.strongly_measurable h).fin_strongly_measurable μ⟩

/-- In a space with second countable topology and a sigma-finite measure,
  `ae_fin_strongly_measurable` and `ae_measurable` are equivalent. -/
lemma ae_fin_strongly_measurable_iff_ae_measurable {m0 : measurable_space α} (μ : measure α)
  [sigma_finite μ] :
  ae_fin_strongly_measurable f μ ↔ ae_measurable f μ :=
by simp_rw [ae_fin_strongly_measurable, ae_measurable, fin_strongly_measurable_iff_measurable]

lemma mem_ℒp.fin_strongly_measurable_of_measurable (hf : mem_ℒp f p μ) (hf_meas : measurable f)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  fin_strongly_measurable f μ :=
begin
  let fs := simple_func.approx_on f hf_meas set.univ 0 (set.mem_univ _),
  refine ⟨fs, _, _⟩,
  { have h_fs_Lp : ∀ n, mem_ℒp (fs n) p μ, from simple_func.mem_ℒp_approx_on_univ hf_meas hf,
    exact λ n, (fs n).measure_support_lt_top_of_mem_ℒp (h_fs_Lp n) hp_ne_zero hp_ne_top, },
  { exact λ x, simple_func.tendsto_approx_on hf_meas (set.mem_univ 0) (by simp), },
end

lemma mem_ℒp.ae_fin_strongly_measurable (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) :
  ae_fin_strongly_measurable f μ :=
⟨hf.ae_measurable.mk f,
  ((mem_ℒp_congr_ae hf.ae_measurable.ae_eq_mk).mp hf).fin_strongly_measurable_of_measurable
    hf.ae_measurable.measurable_mk hp_ne_zero hp_ne_top,
  hf.ae_measurable.ae_eq_mk⟩

lemma integrable.ae_fin_strongly_measurable (hf : integrable f μ) :
  ae_fin_strongly_measurable f μ :=
(mem_ℒp_one_iff_integrable.mpr hf).ae_fin_strongly_measurable one_ne_zero ennreal.coe_ne_top

lemma Lp.fin_strongly_measurable (f : Lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  fin_strongly_measurable f μ :=
(Lp.mem_ℒp f).fin_strongly_measurable_of_measurable (Lp.measurable f) hp_ne_zero hp_ne_top

end measure_theory
