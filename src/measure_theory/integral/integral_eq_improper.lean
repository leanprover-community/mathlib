/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Bhavik Mehta
-/
import analysis.special_functions.pow.deriv
import measure_theory.integral.fund_thm_calculus
import order.filter.at_top_bot
import measure_theory.function.jacobian
import measure_theory.measure.haar.normed_space

/-!
# Links between an integral and its "improper" version

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In its current state, mathlib only knows how to talk about definite ("proper") integrals,
in the sense that it treats integrals over `[x, +∞)` the same as it treats integrals over
`[y, z]`. For example, the integral over `[1, +∞)` is **not** defined to be the limit of
the integral over `[1, x]` as `x` tends to `+∞`, which is known as an **improper integral**.

Indeed, the "proper" definition is stronger than the "improper" one. The usual counterexample
is `x ↦ sin(x)/x`, which has an improper integral over `[1, +∞)` but no definite integral.

Although definite integrals have better properties, they are hardly usable when it comes to
computing integrals on unbounded sets, which is much easier using limits. Thus, in this file,
we prove various ways of studying the proper integral by studying the improper one.

## Definitions

The main definition of this file is `measure_theory.ae_cover`. It is a rather technical
definition whose sole purpose is generalizing and factoring proofs. Given an index type `ι`, a
countably generated filter `l` over `ι`, and an `ι`-indexed family `φ` of subsets of a measurable
space `α` equipped with a measure `μ`, one should think of a hypothesis `hφ : ae_cover μ l φ` as
a sufficient condition for being able to interpret `∫ x, f x ∂μ` (if it exists) as the limit
of `∫ x in φ i, f x ∂μ` as `i` tends to `l`.

When using this definition with a measure restricted to a set `s`, which happens fairly often,
one should not try too hard to use a `ae_cover` of subsets of `s`, as it often makes proofs
more complicated than necessary. See for example the proof of
`measure_theory.integrable_on_Iic_of_interval_integral_norm_tendsto` where we use `(λ x, Ioi x)`
as an `ae_cover` w.r.t. `μ.restrict (Iic b)`, instead of using `(λ x, Ioc x b)`.

## Main statements

- `measure_theory.ae_cover.lintegral_tendsto_of_countably_generated` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, and if `f` is a measurable `ennreal`-valued function,
  then `∫⁻ x in φ n, f x ∂μ` tends to `∫⁻ x, f x ∂μ` as `n` tends to `l`
- `measure_theory.ae_cover.integrable_of_integral_norm_tendsto` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, if `f` is measurable and integrable on each `φ n`,
  and if `∫ x in φ n, ‖f x‖ ∂μ` tends to some `I : ℝ` as n tends to `l`, then `f` is integrable
- `measure_theory.ae_cover.integral_tendsto_of_countably_generated` : if `φ` is a `ae_cover μ l`,
  where `l` is a countably generated filter, and if `f` is measurable and integrable (globally),
  then `∫ x in φ n, f x ∂μ` tends to `∫ x, f x ∂μ` as `n` tends to `+∞`.

We then specialize these lemmas to various use cases involving intervals, which are frequent
in analysis. In particular,
- `measure_theory.integral_Ioi_of_has_deriv_at_of_tendsto` is a version of FTC-2 on the interval
  `(a, +∞)`, giving the formula `∫ x in (a, +∞), g' x = l - g a` if `g'` is integrable and
  `g` tends to `l` at `+∞`.
- `measure_theory.integral_Ioi_of_has_deriv_at_of_nonneg` gives the same result assuming that
  `g'` is nonnegative instead of integrable. Its automatic integrability in this context is proved
  in `measure_theory.integrable_on_Ioi_deriv_of_nonneg`.
- `measure_theory.integral_comp_smul_deriv_Ioi` is a version of the change of variables formula
  on semi-infinite intervals.
-/

open measure_theory filter set topological_space
open_locale ennreal nnreal topology

namespace measure_theory

section ae_cover

variables {α ι : Type*} [measurable_space α] (μ : measure α) (l : filter ι)

/-- A sequence `φ` of subsets of `α` is a `ae_cover` w.r.t. a measure `μ` and a filter `l`
    if almost every point (w.r.t. `μ`) of `α` eventually belongs to `φ n` (w.r.t. `l`), and if
    each `φ n` is measurable.
    This definition is a technical way to avoid duplicating a lot of proofs.
    It should be thought of as a sufficient condition for being able to interpret
    `∫ x, f x ∂μ` (if it exists) as the limit of `∫ x in φ n, f x ∂μ` as `n` tends to `l`.

    See for example `measure_theory.ae_cover.lintegral_tendsto_of_countably_generated`,
    `measure_theory.ae_cover.integrable_of_integral_norm_tendsto` and
    `measure_theory.ae_cover.integral_tendsto_of_countably_generated`. -/
structure ae_cover (φ : ι → set α) : Prop :=
(ae_eventually_mem : ∀ᵐ x ∂μ, ∀ᶠ i in l, x ∈ φ i)
(measurable : ∀ i, measurable_set $ φ i)

variables {μ} {l}

section preorder_α

variables [preorder α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α}
  (ha : tendsto a l at_bot) (hb : tendsto b l at_top)

lemma ae_cover_Icc :
  ae_cover μ l (λ i, Icc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mp $
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Icc }

lemma ae_cover_Ici :
  ae_cover μ l (λ i, Ici $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mono $
    λ i hai, hai ),
  measurable := λ i, measurable_set_Ici }

lemma ae_cover_Iic :
  ae_cover μ l (λ i, Iic $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi, hbi ),
  measurable := λ i, measurable_set_Iic }

end preorder_α

section linear_order_α

variables [linear_order α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α}
  (ha : tendsto a l at_bot) (hb : tendsto b l at_top)

lemma ae_cover_Ioo [no_min_order α] [no_max_order α] :
  ae_cover μ l (λ i, Ioo (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mp $
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ioo }

lemma ae_cover_Ioc [no_min_order α] : ae_cover μ l (λ i, Ioc (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mp $
    (hb.eventually $ eventually_ge_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ioc }

lemma ae_cover_Ico [no_max_order α] : ae_cover μ l (λ i, Ico (a i) (b i)) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_le_at_bot x).mp $
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi hai, ⟨hai, hbi⟩ ),
  measurable := λ i, measurable_set_Ico }

lemma ae_cover_Ioi [no_min_order α] :
  ae_cover μ l (λ i, Ioi $ a i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (ha.eventually $ eventually_lt_at_bot x).mono $
    λ i hai, hai ),
  measurable := λ i, measurable_set_Ioi }

lemma ae_cover_Iio [no_max_order α] :
  ae_cover μ l (λ i, Iio $ b i) :=
{ ae_eventually_mem := ae_of_all μ (λ x,
    (hb.eventually $ eventually_gt_at_top x).mono $
    λ i hbi, hbi ),
  measurable := λ i, measurable_set_Iio }

end linear_order_α

section finite_intervals

variables [linear_order α] [topological_space α] [order_closed_topology α]
  [opens_measurable_space α] {a b : ι → α} {A B : α}
  (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B))

lemma ae_cover_Ioo_of_Icc :
  ae_cover (μ.restrict $ Ioo A B) l (λ i, Icc (a i) (b i)) :=
{ ae_eventually_mem := (ae_restrict_iff' measurable_set_Ioo).mpr (
    ae_of_all μ (λ x hx,
    (ha.eventually $ eventually_le_nhds hx.left).mp $
    (hb.eventually $ eventually_ge_nhds hx.right).mono $
    λ i hbi hai, ⟨hai, hbi⟩)),
  measurable := λ i, measurable_set_Icc, }

lemma ae_cover_Ioo_of_Ico :
  ae_cover (μ.restrict $ Ioo A B) l (λ i, Ico (a i) (b i)) :=
{ ae_eventually_mem := (ae_restrict_iff' measurable_set_Ioo).mpr (
    ae_of_all μ (λ x hx,
    (ha.eventually $ eventually_le_nhds hx.left).mp $
    (hb.eventually $ eventually_gt_nhds hx.right).mono $
    λ i hbi hai, ⟨hai, hbi⟩)),
  measurable := λ i, measurable_set_Ico, }

lemma ae_cover_Ioo_of_Ioc :
  ae_cover (μ.restrict $ Ioo A B) l (λ i, Ioc (a i) (b i)) :=
{ ae_eventually_mem := (ae_restrict_iff' measurable_set_Ioo).mpr (
    ae_of_all μ (λ x hx,
    (ha.eventually $ eventually_lt_nhds hx.left).mp $
    (hb.eventually $ eventually_ge_nhds hx.right).mono $
    λ i hbi hai, ⟨hai, hbi⟩)),
  measurable := λ i, measurable_set_Ioc, }

lemma ae_cover_Ioo_of_Ioo :
  ae_cover (μ.restrict $ Ioo A B) l (λ i, Ioo (a i) (b i)) :=
{ ae_eventually_mem := (ae_restrict_iff' measurable_set_Ioo).mpr (
    ae_of_all μ (λ x hx,
    (ha.eventually $ eventually_lt_nhds hx.left).mp $
    (hb.eventually $ eventually_gt_nhds hx.right).mono $
    λ i hbi hai, ⟨hai, hbi⟩)),
  measurable := λ i, measurable_set_Ioo, }

variables [has_no_atoms μ]

lemma ae_cover_Ioc_of_Icc (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Ioc A B) l (λ i, Icc (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ae_cover_Ioo_of_Icc ha hb]

lemma ae_cover_Ioc_of_Ico (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Ioc A B) l (λ i, Ico (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ae_cover_Ioo_of_Ico ha hb]

lemma ae_cover_Ioc_of_Ioc (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Ioc A B) l (λ i, Ioc (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ae_cover_Ioo_of_Ioc ha hb]

lemma ae_cover_Ioc_of_Ioo (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Ioc A B) l (λ i, Ioo (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, ae_cover_Ioo_of_Ioo ha hb]

lemma ae_cover_Ico_of_Icc (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Ico A B) l (λ i, Icc (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Ico.symm, ae_cover_Ioo_of_Icc ha hb]

lemma ae_cover_Ico_of_Ico (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Ico A B) l (λ i, Ico (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Ico.symm, ae_cover_Ioo_of_Ico ha hb]

lemma ae_cover_Ico_of_Ioc (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Ico A B) l (λ i, Ioc (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Ico.symm, ae_cover_Ioo_of_Ioc ha hb]

lemma ae_cover_Ico_of_Ioo (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Ico A B) l (λ i, Ioo (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Ico.symm, ae_cover_Ioo_of_Ioo ha hb]

lemma ae_cover_Icc_of_Icc (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Icc A B) l (λ i, Icc (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Icc.symm, ae_cover_Ioo_of_Icc ha hb]

lemma ae_cover_Icc_of_Ico (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Icc A B) l (λ i, Ico (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Icc.symm, ae_cover_Ioo_of_Ico ha hb]

lemma ae_cover_Icc_of_Ioc (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Icc A B) l (λ i, Ioc (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Icc.symm, ae_cover_Ioo_of_Ioc ha hb]

lemma ae_cover_Icc_of_Ioo (ha : tendsto a l (𝓝 A)) (hb : tendsto b l (𝓝 B)) :
  ae_cover (μ.restrict $ Icc A B) l (λ i, Ioo (a i) (b i)) :=
by simp [measure.restrict_congr_set Ioo_ae_eq_Icc.symm, ae_cover_Ioo_of_Ioo ha hb]

end finite_intervals

lemma ae_cover.restrict {φ : ι → set α} (hφ : ae_cover μ l φ) {s : set α} :
  ae_cover (μ.restrict s) l φ :=
{ ae_eventually_mem := ae_restrict_of_ae hφ.ae_eventually_mem,
  measurable := hφ.measurable }

lemma ae_cover_restrict_of_ae_imp {s : set α} {φ : ι → set α}
  (hs : measurable_set s) (ae_eventually_mem : ∀ᵐ x ∂μ, x ∈ s → ∀ᶠ n in l, x ∈ φ n)
  (measurable : ∀ n, measurable_set $ φ n) :
  ae_cover (μ.restrict s) l φ :=
{ ae_eventually_mem := by rwa ae_restrict_iff' hs,
  measurable := measurable }

lemma ae_cover.inter_restrict {φ : ι → set α} (hφ : ae_cover μ l φ)
  {s : set α} (hs : measurable_set s) :
  ae_cover (μ.restrict s) l (λ i, φ i ∩ s) :=
ae_cover_restrict_of_ae_imp hs
  (hφ.ae_eventually_mem.mono (λ x hx hxs, hx.mono $ λ i hi, ⟨hi, hxs⟩))
  (λ i, (hφ.measurable i).inter hs)

lemma ae_cover.ae_tendsto_indicator {β : Type*} [has_zero β] [topological_space β]
  (f : α → β) {φ : ι → set α} (hφ : ae_cover μ l φ) :
  ∀ᵐ x ∂μ, tendsto (λ i, (φ i).indicator f x) l (𝓝 $ f x) :=
hφ.ae_eventually_mem.mono (λ x hx, tendsto_const_nhds.congr' $
  hx.mono $ λ n hn, (indicator_of_mem hn _).symm)

lemma ae_cover.ae_measurable {β : Type*} [measurable_space β] [l.is_countably_generated] [l.ne_bot]
  {f : α → β} {φ : ι → set α} (hφ : ae_cover μ l φ)
  (hfm : ∀ i, ae_measurable f (μ.restrict $ φ i)) : ae_measurable f μ :=
begin
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto,
  have := ae_measurable_Union_iff.mpr (λ (n : ℕ), hfm (u n)),
  rwa measure.restrict_eq_self_of_ae_mem at this,
  filter_upwards [hφ.ae_eventually_mem] with x hx using
    let ⟨i, hi⟩ := (hu.eventually hx).exists in mem_Union.mpr ⟨i, hi⟩
end

lemma ae_cover.ae_strongly_measurable {β : Type*} [topological_space β] [pseudo_metrizable_space β]
  [l.is_countably_generated] [l.ne_bot]
  {f : α → β} {φ : ι → set α} (hφ : ae_cover μ l φ)
  (hfm : ∀ i, ae_strongly_measurable f (μ.restrict $ φ i)) : ae_strongly_measurable f μ :=
begin
  obtain ⟨u, hu⟩ := l.exists_seq_tendsto,
  have := ae_strongly_measurable_Union_iff.mpr (λ (n : ℕ), hfm (u n)),
  rwa measure.restrict_eq_self_of_ae_mem at this,
  filter_upwards [hφ.ae_eventually_mem] with x hx using
    let ⟨i, hi⟩ := (hu.eventually hx).exists in mem_Union.mpr ⟨i, hi⟩
end


end ae_cover

lemma ae_cover.comp_tendsto {α ι ι' : Type*} [measurable_space α] {μ : measure α} {l : filter ι}
  {l' : filter ι'} {φ : ι → set α} (hφ : ae_cover μ l φ)
  {u : ι' → ι} (hu : tendsto u l' l) :
  ae_cover μ l' (φ ∘ u) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono (λ x hx, hu.eventually hx),
  measurable := λ i, hφ.measurable (u i) }

section ae_cover_Union_Inter_countable

variables {α ι : Type*} [countable ι]
  [measurable_space α] {μ : measure α}

lemma ae_cover.bUnion_Iic_ae_cover [preorder ι] {φ : ι → set α} (hφ : ae_cover μ at_top φ) :
  ae_cover μ at_top (λ (n : ι), ⋃ k (h : k ∈ Iic n), φ k) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono
    (λ x h, h.mono (λ i hi, mem_bUnion right_mem_Iic hi)),
  measurable := λ i, measurable_set.bUnion (to_countable _) (λ n _, hφ.measurable n) }

lemma ae_cover.bInter_Ici_ae_cover [semilattice_sup ι] [nonempty ι] {φ : ι → set α}
  (hφ : ae_cover μ at_top φ) : ae_cover μ at_top (λ (n : ι), ⋂ k (h : k ∈ Ici n), φ k) :=
{ ae_eventually_mem := hφ.ae_eventually_mem.mono
    begin
      intros x h,
      rw eventually_at_top at *,
      rcases h with ⟨i, hi⟩,
      use i,
      intros j hj,
      exact mem_bInter (λ k hk, hi k (le_trans hj hk)),
    end,
  measurable := λ i, measurable_set.bInter (to_countable _) (λ n _, hφ.measurable n) }

end ae_cover_Union_Inter_countable

section lintegral

variables {α ι : Type*} [measurable_space α] {μ : measure α} {l : filter ι}

private lemma lintegral_tendsto_of_monotone_of_nat {φ : ℕ → set α}
  (hφ : ae_cover μ at_top φ) (hmono : monotone φ) {f : α → ℝ≥0∞} (hfm : ae_measurable f μ) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
let F := λ n, (φ n).indicator f in
have key₁ : ∀ n, ae_measurable (F n) μ, from λ n, hfm.indicator (hφ.measurable n),
have key₂ : ∀ᵐ (x : α) ∂μ, monotone (λ n, F n x), from ae_of_all _
  (λ x i j hij, indicator_le_indicator_of_subset (hmono hij) (λ x, zero_le $ f x) x),
have key₃ : ∀ᵐ (x : α) ∂μ, tendsto (λ n, F n x) at_top (𝓝 (f x)), from hφ.ae_tendsto_indicator f,
(lintegral_tendsto_of_tendsto_of_monotone key₁ key₂ key₃).congr
  (λ n, lintegral_indicator f (hφ.measurable n))

lemma ae_cover.lintegral_tendsto_of_nat {φ : ℕ → set α} (hφ : ae_cover μ at_top φ)
  {f : α → ℝ≥0∞} (hfm : ae_measurable f μ) :
  tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) at_top (𝓝 $ ∫⁻ x, f x ∂μ) :=
begin
  have lim₁ := lintegral_tendsto_of_monotone_of_nat (hφ.bInter_Ici_ae_cover)
    (λ i j hij, bInter_subset_bInter_left (Ici_subset_Ici.mpr hij)) hfm,
  have lim₂ := lintegral_tendsto_of_monotone_of_nat (hφ.bUnion_Iic_ae_cover)
    (λ i j hij, bUnion_subset_bUnion_left (Iic_subset_Iic.mpr hij)) hfm,
  have le₁ := λ n, lintegral_mono_set (bInter_subset_of_mem left_mem_Ici),
  have le₂ := λ n, lintegral_mono_set (subset_bUnion_of_mem right_mem_Iic),
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le lim₁ lim₂ le₁ le₂
end

lemma ae_cover.lintegral_tendsto_of_countably_generated [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → ℝ≥0∞}
  (hfm : ae_measurable f μ) : tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) l (𝓝 $ ∫⁻ x, f x ∂μ) :=
tendsto_of_seq_tendsto (λ u hu, (hφ.comp_tendsto hu).lintegral_tendsto_of_nat hfm)

lemma ae_cover.lintegral_eq_of_tendsto [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → ℝ≥0∞} (I : ℝ≥0∞)
  (hfm : ae_measurable f μ) (htendsto : tendsto (λ i, ∫⁻ x in φ i, f x ∂μ) l (𝓝 I)) :
  ∫⁻ x, f x ∂μ = I :=
tendsto_nhds_unique (hφ.lintegral_tendsto_of_countably_generated hfm) htendsto

lemma ae_cover.supr_lintegral_eq_of_countably_generated [nonempty ι] [l.ne_bot]
  [l.is_countably_generated] {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → ℝ≥0∞}
  (hfm : ae_measurable f μ) : (⨆ (i : ι), ∫⁻ x in φ i, f x ∂μ) = ∫⁻ x, f x ∂μ :=
begin
  have := hφ.lintegral_tendsto_of_countably_generated hfm,
  refine csupr_eq_of_forall_le_of_forall_lt_exists_gt
    (λ i, lintegral_mono' measure.restrict_le_self le_rfl) (λ w hw, _),
  rcases exists_between hw with ⟨m, hm₁, hm₂⟩,
  rcases (eventually_ge_of_tendsto_gt hm₂ this).exists with ⟨i, hi⟩,
  exact ⟨i, lt_of_lt_of_le hm₁ hi⟩,
end

end lintegral

section integrable

variables {α ι E : Type*} [measurable_space α] {μ : measure α} {l : filter ι}
  [normed_add_comm_group E]

lemma ae_cover.integrable_of_lintegral_nnnorm_bounded [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → E} (I : ℝ) (hfm : ae_strongly_measurable f μ)
  (hbounded : ∀ᶠ i in l, ∫⁻ x in φ i, ‖f x‖₊ ∂μ ≤ ennreal.of_real I) :
  integrable f μ :=
begin
  refine ⟨hfm, (le_of_tendsto _ hbounded).trans_lt ennreal.of_real_lt_top⟩,
  exact hφ.lintegral_tendsto_of_countably_generated hfm.ennnorm
end

lemma ae_cover.integrable_of_lintegral_nnnorm_tendsto [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → E} (I : ℝ)
  (hfm : ae_strongly_measurable f μ)
  (htendsto : tendsto (λ i, ∫⁻ x in φ i, ‖f x‖₊ ∂μ) l (𝓝 $ ennreal.of_real I)) :
  integrable f μ :=
begin
  refine hφ.integrable_of_lintegral_nnnorm_bounded (max 1 (I + 1)) hfm _,
  refine htendsto.eventually (ge_mem_nhds _),
  refine (ennreal.of_real_lt_of_real_iff (lt_max_of_lt_left zero_lt_one)).2 _,
  exact lt_max_of_lt_right (lt_add_one I),
end

lemma ae_cover.integrable_of_lintegral_nnnorm_bounded' [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → E} (I : ℝ≥0) (hfm : ae_strongly_measurable f μ)
  (hbounded : ∀ᶠ i in l, ∫⁻ x in φ i, ‖f x‖₊ ∂μ ≤ I) :
  integrable f μ :=
hφ.integrable_of_lintegral_nnnorm_bounded I hfm
  (by simpa only [ennreal.of_real_coe_nnreal] using hbounded)

lemma ae_cover.integrable_of_lintegral_nnnorm_tendsto' [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → E} (I : ℝ≥0)
  (hfm : ae_strongly_measurable f μ)
  (htendsto : tendsto (λ i, ∫⁻ x in φ i, ‖f x‖₊ ∂μ) l (𝓝 I)) :
  integrable f μ :=
hφ.integrable_of_lintegral_nnnorm_tendsto I hfm
  (by simpa only [ennreal.of_real_coe_nnreal] using htendsto)

lemma ae_cover.integrable_of_integral_norm_bounded [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → E}
  (I : ℝ) (hfi : ∀ i, integrable_on f (φ i) μ)
  (hbounded : ∀ᶠ i in l, ∫ x in φ i, ‖f x‖ ∂μ ≤ I) :
  integrable f μ :=
begin
  have hfm : ae_strongly_measurable f μ :=
    hφ.ae_strongly_measurable (λ i, (hfi i).ae_strongly_measurable),
  refine hφ.integrable_of_lintegral_nnnorm_bounded I hfm _,
  conv at hbounded in (integral _ _)
  { rw integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (λ x, @norm_nonneg E _ (f x)))
    hfm.norm.restrict },
  conv at hbounded in (ennreal.of_real _) { dsimp, rw ← coe_nnnorm, rw ennreal.of_real_coe_nnreal },
  refine hbounded.mono (λ i hi, _),
  rw ←ennreal.of_real_to_real (ne_top_of_lt (hfi i).2),
  apply ennreal.of_real_le_of_real hi,
end

lemma ae_cover.integrable_of_integral_norm_tendsto [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → E}
  (I : ℝ) (hfi : ∀ i, integrable_on f (φ i) μ)
  (htendsto : tendsto (λ i, ∫ x in φ i, ‖f x‖ ∂μ) l (𝓝 I)) :
  integrable f μ :=
let ⟨I', hI'⟩ := htendsto.is_bounded_under_le in hφ.integrable_of_integral_norm_bounded I' hfi hI'

lemma ae_cover.integrable_of_integral_bounded_of_nonneg_ae [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → ℝ} (I : ℝ)
  (hfi : ∀ i, integrable_on f (φ i) μ) (hnng : ∀ᵐ x ∂μ, 0 ≤ f x)
  (hbounded : ∀ᶠ i in l, ∫ x in φ i, f x ∂μ ≤ I) :
  integrable f μ :=
hφ.integrable_of_integral_norm_bounded I hfi $ hbounded.mono $ λ i hi,
  (integral_congr_ae $ ae_restrict_of_ae $ hnng.mono $ λ x, real.norm_of_nonneg).le.trans hi

lemma ae_cover.integrable_of_integral_tendsto_of_nonneg_ae [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → ℝ} (I : ℝ)
  (hfi : ∀ i, integrable_on f (φ i) μ) (hnng : ∀ᵐ x ∂μ, 0 ≤ f x)
  (htendsto : tendsto (λ i, ∫ x in φ i, f x ∂μ) l (𝓝 I)) :
  integrable f μ :=
let ⟨I', hI'⟩ := htendsto.is_bounded_under_le in
  hφ.integrable_of_integral_bounded_of_nonneg_ae I' hfi hnng hI'

end integrable

section integral

variables {α ι E : Type*} [measurable_space α] {μ : measure α} {l : filter ι}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

lemma ae_cover.integral_tendsto_of_countably_generated [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → E} (hfi : integrable f μ) :
  tendsto (λ i, ∫ x in φ i, f x ∂μ) l (𝓝 $ ∫ x, f x ∂μ) :=
suffices h : tendsto (λ i, ∫ (x : α), (φ i).indicator f x ∂μ) l (𝓝 (∫ (x : α), f x ∂μ)),
by { convert h, ext n, rw integral_indicator (hφ.measurable n) },
tendsto_integral_filter_of_dominated_convergence (λ x, ‖f x‖)
  (eventually_of_forall $ λ i, hfi.ae_strongly_measurable.indicator $ hφ.measurable i)
  (eventually_of_forall $ λ i, ae_of_all _ $ λ x, norm_indicator_le_norm_self _ _)
  hfi.norm (hφ.ae_tendsto_indicator f)

/-- Slight reformulation of
    `measure_theory.ae_cover.integral_tendsto_of_countably_generated`. -/
lemma ae_cover.integral_eq_of_tendsto [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → E}
  (I : E) (hfi : integrable f μ)
  (h : tendsto (λ n, ∫ x in φ n, f x ∂μ) l (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
tendsto_nhds_unique (hφ.integral_tendsto_of_countably_generated hfi) h

lemma ae_cover.integral_eq_of_tendsto_of_nonneg_ae [l.ne_bot] [l.is_countably_generated]
  {φ : ι → set α} (hφ : ae_cover μ l φ) {f : α → ℝ} (I : ℝ)
  (hnng : 0 ≤ᵐ[μ] f) (hfi : ∀ n, integrable_on f (φ n) μ)
  (htendsto : tendsto (λ n, ∫ x in φ n, f x ∂μ) l (𝓝 I)) :
  ∫ x, f x ∂μ = I :=
have hfi' : integrable f μ,
  from hφ.integrable_of_integral_tendsto_of_nonneg_ae I hfi hnng htendsto,
hφ.integral_eq_of_tendsto I hfi' htendsto

end integral

section integrable_of_interval_integral

variables {ι E : Type*} {μ : measure ℝ}
          {l : filter ι} [filter.ne_bot l] [is_countably_generated l]
          [normed_add_comm_group E]
          {a b : ι → ℝ} {f : ℝ → E}

lemma integrable_of_interval_integral_norm_bounded
  (I : ℝ) (hfi : ∀ i, integrable_on f (Ioc (a i) (b i)) μ)
  (ha : tendsto a l at_bot) (hb : tendsto b l at_top)
  (h : ∀ᶠ i in l, ∫_{a i}^{b i} x, ‖f x‖ ∂μ ≤ I) :
  integrable f μ :=
begin
  have hφ : ae_cover μ l _ := ae_cover_Ioc ha hb,
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp _),
  filter_upwards [ha.eventually (eventually_le_at_bot 0), hb.eventually (eventually_ge_at_top 0)]
    with i hai hbi ht,
  rwa ←interval_integral.integral_of_le (hai.trans hbi)
end

/-- If `f` is integrable on intervals `Ioc (a i) (b i)`,
where `a i` tends to -∞ and `b i` tends to ∞, and
`∫_{a i}^{b i} x, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (-∞, ∞) -/
lemma integrable_of_interval_integral_norm_tendsto
  (I : ℝ) (hfi : ∀ i, integrable_on f (Ioc (a i) (b i)) μ)
  (ha : tendsto a l at_bot) (hb : tendsto b l at_top)
  (h : tendsto (λ i, ∫_{a i}^{b i} x, ‖f x‖ ∂μ) l (𝓝 I)) :
  integrable f μ :=
let ⟨I', hI'⟩ := h.is_bounded_under_le in
  integrable_of_interval_integral_norm_bounded I' hfi ha hb hI'

lemma integrable_on_Iic_of_interval_integral_norm_bounded (I b : ℝ)
  (hfi : ∀ i, integrable_on f (Ioc (a i) b) μ) (ha : tendsto a l at_bot)
  (h : ∀ᶠ i in l, (∫_{a i}^{b} x, ‖f x‖ ∂μ) ≤ I) :
  integrable_on f (Iic b) μ :=
begin
  have hφ : ae_cover (μ.restrict $ Iic b) l _ := ae_cover_Ioi ha,
  have hfi : ∀ i, integrable_on f (Ioi (a i)) (μ.restrict $ Iic b),
  { intro i,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i)],
    exact hfi i },
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp _),
  filter_upwards [ha.eventually (eventually_le_at_bot b)] with i hai,
  rw [interval_integral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)],
  exact id
end

/-- If `f` is integrable on intervals `Ioc (a i) b`,
where `a i` tends to -∞, and
`∫_{a i}^{b} x, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (-∞, b) -/
lemma integrable_on_Iic_of_interval_integral_norm_tendsto (I b : ℝ)
  (hfi : ∀ i, integrable_on f (Ioc (a i) b) μ) (ha : tendsto a l at_bot)
  (h : tendsto (λ i, ∫_{a i}^{b} x, ‖f x‖ ∂μ) l (𝓝 I)) :
  integrable_on f (Iic b) μ :=
let ⟨I', hI'⟩ := h.is_bounded_under_le in
  integrable_on_Iic_of_interval_integral_norm_bounded I' b hfi ha hI'

lemma integrable_on_Ioi_of_interval_integral_norm_bounded (I a : ℝ)
  (hfi : ∀ i, integrable_on f (Ioc a (b i)) μ) (hb : tendsto b l at_top)
  (h : ∀ᶠ i in l, (∫_{a}^{b i} x, ‖f x‖ ∂μ) ≤ I) :
  integrable_on f (Ioi a) μ :=
begin
  have hφ : ae_cover (μ.restrict $ Ioi a) l _ := ae_cover_Iic hb,
  have hfi : ∀ i, integrable_on f (Iic (b i)) (μ.restrict $ Ioi a),
  { intro i,
    rw [integrable_on, measure.restrict_restrict (hφ.measurable i), inter_comm],
    exact hfi i },
  refine hφ.integrable_of_integral_norm_bounded I hfi (h.mp _),
  filter_upwards [hb.eventually (eventually_ge_at_top a)] with i hbi,
  rw [interval_integral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i),
      inter_comm],
  exact id
end

/-- If `f` is integrable on intervals `Ioc a (b i)`,
where `b i` tends to ∞, and
`∫_{a}^{b i} x, ‖f x‖ ∂μ` converges to `I : ℝ` along a filter `l`,
then `f` is integrable on the interval (a, ∞) -/
lemma integrable_on_Ioi_of_interval_integral_norm_tendsto (I a : ℝ)
  (hfi : ∀ i, integrable_on f (Ioc a (b i)) μ) (hb : tendsto b l at_top)
  (h : tendsto (λ i, ∫_{a}^{b i} x, ‖f x‖ ∂μ) l (𝓝 $ I)) :
  integrable_on f (Ioi a) μ :=
let ⟨I', hI'⟩ := h.is_bounded_under_le in
  integrable_on_Ioi_of_interval_integral_norm_bounded I' a hfi hb hI'

lemma integrable_on_Ioc_of_interval_integral_norm_bounded {I a₀ b₀ : ℝ}
  (hfi : ∀ i, integrable_on f $ Ioc (a i) (b i))
  (ha : tendsto a l $ 𝓝 a₀) (hb : tendsto b l $ 𝓝 b₀)
  (h : ∀ᶠ i in l, (∫ x in Ioc (a i) (b i), ‖f x‖) ≤ I) : integrable_on f (Ioc a₀ b₀) :=
begin
  refine (ae_cover_Ioc_of_Ioc ha hb).integrable_of_integral_norm_bounded I
    (λ i, (hfi i).restrict measurable_set_Ioc) (eventually.mono h _),
  intros i hi, simp only [measure.restrict_restrict measurable_set_Ioc],
  refine le_trans (set_integral_mono_set (hfi i).norm _ _) hi,
  { apply ae_of_all, simp only [pi.zero_apply, norm_nonneg, forall_const] },
  { apply ae_of_all, intros c hc, exact hc.1 },
end

lemma integrable_on_Ioc_of_interval_integral_norm_bounded_left {I a₀ b : ℝ}
  (hfi : ∀ i, integrable_on f $ Ioc (a i) b) (ha : tendsto a l $ 𝓝 a₀)
  (h : ∀ᶠ i in l, (∫ x in Ioc (a i) b, ‖f x‖) ≤ I) : integrable_on f (Ioc a₀ b) :=
integrable_on_Ioc_of_interval_integral_norm_bounded hfi ha tendsto_const_nhds h

lemma integrable_on_Ioc_of_interval_integral_norm_bounded_right {I a b₀ : ℝ}
  (hfi : ∀ i, integrable_on f $ Ioc a (b i)) (hb : tendsto b l $ 𝓝 b₀)
  (h : ∀ᶠ i in l, (∫ x in Ioc a (b i), ‖f x‖ ) ≤ I) : integrable_on f (Ioc a b₀) :=
integrable_on_Ioc_of_interval_integral_norm_bounded hfi tendsto_const_nhds hb h

end integrable_of_interval_integral

section integral_of_interval_integral

variables {ι E : Type*} {μ : measure ℝ}
          {l : filter ι} [is_countably_generated l]
          [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
          {a b : ι → ℝ} {f : ℝ → E}

lemma interval_integral_tendsto_integral
  (hfi : integrable f μ) (ha : tendsto a l at_bot) (hb : tendsto b l at_top) :
  tendsto (λ i, ∫_{a i}^{b i} x, f x ∂μ) l (𝓝 $ ∫ x, f x ∂μ) :=
begin
  let φ := λ i, Ioc (a i) (b i),
  have hφ : ae_cover μ l φ := ae_cover_Ioc ha hb,
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' _,
  filter_upwards [ha.eventually (eventually_le_at_bot 0), hb.eventually (eventually_ge_at_top 0)]
    with i hai hbi,
  exact (interval_integral.integral_of_le (hai.trans hbi)).symm
end

lemma interval_integral_tendsto_integral_Iic (b : ℝ)
  (hfi : integrable_on f (Iic b) μ) (ha : tendsto a l at_bot) :
  tendsto (λ i, ∫_{a i}^{b} x, f x ∂μ) l (𝓝 $ ∫ x in Iic b, f x ∂μ) :=
begin
  let φ := λ i, Ioi (a i),
  have hφ : ae_cover (μ.restrict $ Iic b) l φ := ae_cover_Ioi ha,
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' _,
  filter_upwards [ha.eventually (eventually_le_at_bot $ b)] with i hai,
  rw [interval_integral.integral_of_le hai, measure.restrict_restrict (hφ.measurable i)],
  refl,
end

lemma interval_integral_tendsto_integral_Ioi (a : ℝ)
  (hfi : integrable_on f (Ioi a) μ) (hb : tendsto b l at_top) :
  tendsto (λ i, ∫_{a}^{b i} x, f x ∂μ) l (𝓝 $ ∫ x in Ioi a, f x ∂μ) :=
begin
  let φ := λ i, Iic (b i),
  have hφ : ae_cover (μ.restrict $ Ioi a) l φ := ae_cover_Iic hb,
  refine (hφ.integral_tendsto_of_countably_generated hfi).congr' _,
  filter_upwards [hb.eventually (eventually_ge_at_top $ a)] with i hbi,
  rw [interval_integral.integral_of_le hbi, measure.restrict_restrict (hφ.measurable i),
      inter_comm],
  refl,
end

end integral_of_interval_integral

open real
open_locale interval

section Ioi_FTC

variables {E : Type*} {f f' : ℝ → E} {g g' : ℝ → ℝ} {a b l : ℝ} {m : E}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(a, +∞)`.
When a function has a limit at infinity `m`, and its derivative is integrable, then the
integral of the derivative on `(a, +∞)` is `m - f a`. Version assuming differentiability
on `(a, +∞)` and continuity on `[a, +∞)`.-/
lemma integral_Ioi_of_has_deriv_at_of_tendsto (hcont : continuous_on f (Ici a))
  (hderiv : ∀ x ∈ Ioi a, has_deriv_at f (f' x) x)
  (f'int : integrable_on f' (Ioi a)) (hf : tendsto f at_top (𝓝 m)) :
  ∫ x in Ioi a, f' x = m - f a :=
begin
  refine tendsto_nhds_unique (interval_integral_tendsto_integral_Ioi a f'int tendsto_id) _,
  apply tendsto.congr' _ (hf.sub_const _),
  filter_upwards [Ioi_mem_at_top a] with x hx,
  have h'x : a ≤ id x := le_of_lt hx,
  symmetry,
  apply interval_integral.integral_eq_sub_of_has_deriv_at_of_le h'x
    (hcont.mono Icc_subset_Ici_self) (λ y hy, hderiv y hy.1),
  rw interval_integrable_iff_integrable_Ioc_of_le h'x,
  exact f'int.mono (λ y hy, hy.1) le_rfl,
end

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(a, +∞)`.
When a function has a limit at infinity `m`, and its derivative is integrable, then the
integral of the derivative on `(a, +∞)` is `m - f a`. Version assuming differentiability
on `[a, +∞)`. -/
lemma integral_Ioi_of_has_deriv_at_of_tendsto'
  (hderiv : ∀ x ∈ Ici a, has_deriv_at f (f' x) x)
  (f'int : integrable_on f' (Ioi a)) (hf : tendsto f at_top (𝓝 m)) :
  ∫ x in Ioi a, f' x = m - f a :=
begin
  apply integral_Ioi_of_has_deriv_at_of_tendsto _ (λ x hx, hderiv x (le_of_lt hx)) f'int hf,
  assume x hx,
  exact (hderiv x hx).continuous_at.continuous_within_at,
end

/-- When a function has a limit at infinity, and its derivative is nonnegative, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `(a, +∞)` and continuity on `[a, +∞)`. -/
lemma integrable_on_Ioi_deriv_of_nonneg (hcont : continuous_on g (Ici a))
  (hderiv : ∀ x ∈ Ioi a, has_deriv_at g (g' x) x)
  (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x) (hg : tendsto g at_top (𝓝 l)) :
  integrable_on g' (Ioi a) :=
begin
  apply integrable_on_Ioi_of_interval_integral_norm_tendsto (l - g a) a (λ x, _) tendsto_id, swap,
  { exact interval_integral.integrable_on_deriv_of_nonneg (hcont.mono Icc_subset_Ici_self)
      (λ y hy, hderiv y hy.1) (λ y hy, g'pos y hy.1) },
  apply tendsto.congr' _ (hg.sub_const _),
  filter_upwards [Ioi_mem_at_top a] with x hx,
  have h'x : a ≤ id x := le_of_lt hx,
  calc g x - g a = ∫_{a}^{id x} y, g' y :
    begin
      symmetry,
      apply interval_integral.integral_eq_sub_of_has_deriv_at_of_le h'x
        (hcont.mono Icc_subset_Ici_self) (λ y hy, hderiv y hy.1),
      rw interval_integrable_iff_integrable_Ioc_of_le h'x,
      exact interval_integral.integrable_on_deriv_of_nonneg (hcont.mono Icc_subset_Ici_self)
        (λ y hy, hderiv y hy.1) (λ y hy, g'pos y hy.1)
    end
  ... = ∫_{a}^{id x} y, ‖g' y‖ :
    begin
      simp_rw interval_integral.integral_of_le h'x,
      refine set_integral_congr (measurable_set_Ioc) (λ y hy, _),
      dsimp,
      rw abs_of_nonneg,
      exact g'pos _ hy.1,
    end
end

/-- When a function has a limit at infinity, and its derivative is nonnegative, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `[a, +∞)`. -/
lemma integrable_on_Ioi_deriv_of_nonneg'
  (hderiv : ∀ x ∈ Ici a, has_deriv_at g (g' x) x)
  (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x) (hg : tendsto g at_top (𝓝 l)) :
  integrable_on g' (Ioi a) :=
begin
  apply integrable_on_Ioi_deriv_of_nonneg _ (λ x hx, hderiv x (le_of_lt hx)) g'pos hg,
  assume x hx,
  exact (hderiv x hx).continuous_at.continuous_within_at,
end

/-- When a function has a limit at infinity `l`, and its derivative is nonnegative, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg`). Version assuming differentiability on `(a, +∞)` and
continuity on `[a, +∞)`. -/
lemma integral_Ioi_of_has_deriv_at_of_nonneg (hcont : continuous_on g (Ici a))
  (hderiv : ∀ x ∈ Ioi a, has_deriv_at g (g' x) x)
  (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x) (hg : tendsto g at_top (𝓝 l)) :
  ∫ x in Ioi a, g' x = l - g a :=
integral_Ioi_of_has_deriv_at_of_tendsto hcont hderiv
  (integrable_on_Ioi_deriv_of_nonneg hcont hderiv g'pos hg) hg

/-- When a function has a limit at infinity `l`, and its derivative is nonnegative, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg'`). Version assuming differentiability on `[a, +∞)`. -/
lemma integral_Ioi_of_has_deriv_at_of_nonneg'
  (hderiv : ∀ x ∈ Ici a, has_deriv_at g (g' x) x)
  (g'pos : ∀ x ∈ Ioi a, 0 ≤ g' x) (hg : tendsto g at_top (𝓝 l)) :
  ∫ x in Ioi a, g' x = l - g a :=
integral_Ioi_of_has_deriv_at_of_tendsto' hderiv
  (integrable_on_Ioi_deriv_of_nonneg' hderiv g'pos hg) hg

/-- When a function has a limit at infinity, and its derivative is nonpositive, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `(a, +∞)` and continuity on `[a, +∞)`. -/
lemma integrable_on_Ioi_deriv_of_nonpos (hcont : continuous_on g (Ici a))
  (hderiv : ∀ x ∈ Ioi a, has_deriv_at g (g' x) x)
  (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) (hg : tendsto g at_top (𝓝 l)) :
  integrable_on g' (Ioi a) :=
begin
  apply integrable_neg_iff.1,
  exact integrable_on_Ioi_deriv_of_nonneg hcont.neg (λ x hx, (hderiv x hx).neg)
    (λ x hx, neg_nonneg_of_nonpos (g'neg x hx)) hg.neg,
end

/-- When a function has a limit at infinity, and its derivative is nonpositive, then the derivative
is automatically integrable on `(a, +∞)`. Version assuming differentiability
on `[a, +∞)`. -/
lemma integrable_on_Ioi_deriv_of_nonpos'
  (hderiv : ∀ x ∈ Ici a, has_deriv_at g (g' x) x)
  (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) (hg : tendsto g at_top (𝓝 l)) :
  integrable_on g' (Ioi a) :=
begin
  apply integrable_on_Ioi_deriv_of_nonpos _ (λ x hx, hderiv x (le_of_lt hx)) g'neg hg,
  assume x hx,
  exact (hderiv x hx).continuous_at.continuous_within_at,
end

/-- When a function has a limit at infinity `l`, and its derivative is nonpositive, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg`). Version assuming differentiability on `(a, +∞)` and
continuity on `[a, +∞)`. -/
lemma integral_Ioi_of_has_deriv_at_of_nonpos (hcont : continuous_on g (Ici a))
  (hderiv : ∀ x ∈ Ioi a, has_deriv_at g (g' x) x)
  (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) (hg : tendsto g at_top (𝓝 l)) :
  ∫ x in Ioi a, g' x = l - g a :=
integral_Ioi_of_has_deriv_at_of_tendsto hcont hderiv
  (integrable_on_Ioi_deriv_of_nonpos hcont hderiv g'neg hg) hg

/-- When a function has a limit at infinity `l`, and its derivative is nonpositive, then the
integral of the derivative on `(a, +∞)` is `l - g a` (and the derivative is integrable, see
`integrable_on_Ioi_deriv_of_nonneg'`). Version assuming differentiability on `[a, +∞)`. -/
lemma integral_Ioi_of_has_deriv_at_of_nonpos'
  (hderiv : ∀ x ∈ Ici a, has_deriv_at g (g' x) x)
  (g'neg : ∀ x ∈ Ioi a, g' x ≤ 0) (hg : tendsto g at_top (𝓝 l)) :
  ∫ x in Ioi a, g' x = l - g a :=
integral_Ioi_of_has_deriv_at_of_tendsto' hderiv
  (integrable_on_Ioi_deriv_of_nonpos' hderiv g'neg hg) hg

end Ioi_FTC

section Ioi_change_variables

open real
open_locale interval

variables {E : Type*} {f : ℝ → E}
  [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

/-- Change-of-variables formula for `Ioi` integrals of vector-valued functions, proved by taking
limits from the result for finite intervals. -/
lemma integral_comp_smul_deriv_Ioi {f f' : ℝ → ℝ} {g : ℝ → E} {a : ℝ}
  (hf : continuous_on f $ Ici a)
  (hft : tendsto f at_top at_top)
  (hff' : ∀ x ∈ Ioi a, has_deriv_within_at f (f' x) (Ioi x) x)
  (hg_cont : continuous_on g $ f '' Ioi a)
  (hg1 : integrable_on g $ f '' Ici a)
  (hg2 : integrable_on (λ x, f' x • (g ∘ f) x) (Ici a)) :
  ∫ x in Ioi a, f' x • (g ∘ f) x = ∫ u in Ioi (f a), g u :=
begin
  have eq : ∀ b : ℝ, a < b → ∫_{a}^{b} x, f' x • (g ∘ f) x = ∫_{f a}^{f b} u, g u,
  { intros b hb,
    have i1 : Ioo (min a b) (max a b) ⊆ Ioi a,
    { rw min_eq_left hb.le, exact Ioo_subset_Ioi_self },
    have i2 : [a, b] ⊆ Ici a,
    { rw uIcc_of_le hb.le, exact Icc_subset_Ici_self },
    refine interval_integral.integral_comp_smul_deriv''' (hf.mono i2)
      (λ x hx, hff' x $ mem_of_mem_of_subset hx i1) (hg_cont.mono $ image_subset _ _)
      (hg1.mono_set $ image_subset _ _) (hg2.mono_set i2),
    { rw min_eq_left hb.le, exact Ioo_subset_Ioi_self },
    { rw uIcc_of_le hb.le, exact Icc_subset_Ici_self } },
  rw integrable_on_Ici_iff_integrable_on_Ioi at hg2,
  have t2 := interval_integral_tendsto_integral_Ioi _ hg2 tendsto_id,
  have : Ioi (f a) ⊆ f '' Ici a := (Ioi_subset_Ici_self.trans $
    is_preconnected.intermediate_value_Ici is_preconnected_Ici left_mem_Ici
    (le_principal_iff.mpr $ Ici_mem_at_top _) hf hft),
  have t1 := (interval_integral_tendsto_integral_Ioi _ (hg1.mono_set this) tendsto_id).comp hft,
  exact tendsto_nhds_unique (tendsto.congr' (eventually_eq_of_mem (Ioi_mem_at_top a) eq) t2) t1,
end

/-- Change-of-variables formula for `Ioi` integrals of scalar-valued functions -/
lemma integral_comp_mul_deriv_Ioi {f f' : ℝ → ℝ} {g : ℝ → ℝ} {a : ℝ}
  (hf : continuous_on f $ Ici a)
  (hft : tendsto f at_top at_top)
  (hff' : ∀ x ∈ Ioi a, has_deriv_within_at f (f' x) (Ioi x) x)
  (hg_cont : continuous_on g $ f '' Ioi a)
  (hg1 : integrable_on g $ f '' Ici a)
  (hg2 : integrable_on (λ x, (g ∘ f) x * f' x) (Ici a)) :
  ∫ x in Ioi a, (g ∘ f) x * f' x = ∫ u in Ioi (f a), g u :=
begin
  have hg2' : integrable_on (λ x, f' x • (g ∘ f) x) (Ici a) := by simpa [mul_comm] using hg2,
  simpa [mul_comm] using integral_comp_smul_deriv_Ioi hf hft hff' hg_cont hg1 hg2',
end

/-- Substitution `y = x ^ p` in integrals over `Ioi 0` -/
lemma integral_comp_rpow_Ioi (g : ℝ → E) {p : ℝ} (hp : p ≠ 0) :
  ∫ x in Ioi 0, (|p| * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi 0, g y :=
begin
  let S := Ioi (0 : ℝ),
  have a1 : ∀ x:ℝ, x ∈ S → has_deriv_within_at (λ (t:ℝ), t ^ p) (p * x ^ (p - 1)) S x :=
    λ x hx, (has_deriv_at_rpow_const (or.inl (mem_Ioi.mp hx).ne')).has_deriv_within_at,
  have a2 : inj_on (λ x:ℝ, x ^ p) S,
  { rcases lt_or_gt_of_ne hp,
    { apply strict_anti_on.inj_on,
      intros x hx y hy hxy,
      rw [←inv_lt_inv (rpow_pos_of_pos hx p) (rpow_pos_of_pos hy p),
      ←rpow_neg (le_of_lt hx), ←rpow_neg (le_of_lt hy)],
      exact rpow_lt_rpow (le_of_lt hx) hxy (neg_pos.mpr h), },
    exact strict_mono_on.inj_on (λ x hx y hy hxy, rpow_lt_rpow (mem_Ioi.mp hx).le hxy h),},
  have a3 : (λ (t : ℝ), t ^ p) '' S = S,
  { ext1, rw mem_image, split,
    { rintro ⟨y, hy, rfl⟩, exact rpow_pos_of_pos hy p },
    { intro hx, refine ⟨x ^ (1 / p), rpow_pos_of_pos hx _, _⟩,
      rw [←rpow_mul (le_of_lt hx), one_div_mul_cancel hp, rpow_one], } },
  have := integral_image_eq_integral_abs_deriv_smul measurable_set_Ioi a1 a2 g,
  rw a3 at this, rw this,
  refine set_integral_congr measurable_set_Ioi _,
  intros x hx, dsimp only,
  rw [abs_mul, abs_of_nonneg (rpow_nonneg_of_nonneg (le_of_lt hx) _)],
end

lemma integral_comp_rpow_Ioi_of_pos {g : ℝ → E} {p : ℝ} (hp : 0 < p) :
  ∫ x in Ioi 0, (p * x ^ (p - 1)) • g (x ^ p) = ∫ y in Ioi 0, g y :=
begin
  convert integral_comp_rpow_Ioi g hp.ne',
  funext, congr, rw abs_of_nonneg hp.le,
end

lemma integral_comp_mul_left_Ioi (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
  ∫ x in Ioi a, g (b * x) = |b⁻¹| • ∫ x in Ioi (b * a), g x :=
begin
  have : ∀ c : ℝ, measurable_set (Ioi c) := λ c, measurable_set_Ioi,
  rw [←integral_indicator (this a), ←integral_indicator (this $ b * a)],
  convert measure.integral_comp_mul_left _ b,
  ext1 x,
  rw [←indicator_comp_right, preimage_const_mul_Ioi _ hb, mul_div_cancel_left _ hb.ne'],
end

lemma integral_comp_mul_right_Ioi (g : ℝ → E) (a : ℝ) {b : ℝ} (hb : 0 < b) :
  ∫ x in Ioi a, g (x * b) = |b⁻¹| • ∫ x in Ioi (a * b), g x :=
by simpa only [mul_comm] using integral_comp_mul_left_Ioi g a hb

end Ioi_change_variables

section Ioi_integrability

open real
open_locale interval

variables {E : Type*} [normed_add_comm_group E]

/-- The substitution `y = x ^ p` in integrals over `Ioi 0` preserves integrability. -/
lemma integrable_on_Ioi_comp_rpow_iff [normed_space ℝ E] (f : ℝ → E) {p : ℝ} (hp : p ≠ 0) :
  integrable_on (λ x, (|p| * x ^ (p - 1)) • f (x ^ p)) (Ioi 0) ↔ integrable_on f (Ioi 0) :=
begin
  let S := Ioi (0 : ℝ),
  have a1 : ∀ x:ℝ, x ∈ S → has_deriv_within_at (λ (t:ℝ), t ^ p) (p * x ^ (p - 1)) S x :=
    λ x hx, (has_deriv_at_rpow_const (or.inl (mem_Ioi.mp hx).ne')).has_deriv_within_at,
  have a2 : inj_on (λ x:ℝ, x ^ p) S,
  { rcases lt_or_gt_of_ne hp,
    { apply strict_anti_on.inj_on,
      intros x hx y hy hxy,
      rw [←inv_lt_inv (rpow_pos_of_pos hx p) (rpow_pos_of_pos hy p),
      ←rpow_neg (le_of_lt hx), ←rpow_neg (le_of_lt hy)],
      exact rpow_lt_rpow (le_of_lt hx) hxy (neg_pos.mpr h), },
    exact strict_mono_on.inj_on (λ x hx y hy hxy, rpow_lt_rpow (mem_Ioi.mp hx).le hxy h) },
  have a3 : (λ (t : ℝ), t ^ p) '' S = S,
  { ext1, rw mem_image, split,
    { rintro ⟨y, hy, rfl⟩, exact rpow_pos_of_pos hy p },
    { intro hx, refine ⟨x ^ (1 / p), rpow_pos_of_pos hx _, _⟩,
      rw [←rpow_mul (le_of_lt hx), one_div_mul_cancel hp, rpow_one], } },
  have := integrable_on_image_iff_integrable_on_abs_deriv_smul measurable_set_Ioi a1 a2 f,
  rw a3 at this,
  rw this,
  refine integrable_on_congr_fun (λ x hx, _) measurable_set_Ioi,
  simp_rw [abs_mul, abs_of_nonneg (rpow_nonneg_of_nonneg (le_of_lt hx) _)],
end

/-- The substitution `y = x ^ p` in integrals over `Ioi 0` preserves integrability (version
without `|p|` factor) -/
lemma integrable_on_Ioi_comp_rpow_iff' [normed_space ℝ E] (f : ℝ → E) {p : ℝ} (hp : p ≠ 0) :
  integrable_on (λ x, x ^ (p - 1) • f (x ^ p)) (Ioi 0) ↔ integrable_on f (Ioi 0) :=
by simpa only [←integrable_on_Ioi_comp_rpow_iff f hp, mul_smul]
  using (integrable_smul_iff (abs_pos.mpr hp).ne' _).symm

lemma integrable_on_Ioi_comp_mul_left_iff (f : ℝ → E) (c : ℝ) {a : ℝ} (ha : 0 < a) :
  integrable_on (λ x, f (a * x)) (Ioi c) ↔ integrable_on f (Ioi $ a * c) :=
begin
  rw [←integrable_indicator_iff (measurable_set_Ioi : measurable_set $ Ioi c)],
  rw [←integrable_indicator_iff (measurable_set_Ioi : measurable_set $ Ioi $ a * c)],
  convert integrable_comp_mul_left_iff ((Ioi (a * c)).indicator f) ha.ne' using 2,
  ext1 x,
  rw [←indicator_comp_right, preimage_const_mul_Ioi _ ha, mul_comm a c, mul_div_cancel _ ha.ne'],
end

lemma integrable_on_Ioi_comp_mul_right_iff (f : ℝ → E) (c : ℝ) {a : ℝ} (ha : 0 < a) :
  integrable_on (λ x, f (x * a)) (Ioi c) ↔ integrable_on f (Ioi $ c * a) :=
by simpa only [mul_comm, mul_zero] using integrable_on_Ioi_comp_mul_left_iff f c ha

end Ioi_integrability

end measure_theory
