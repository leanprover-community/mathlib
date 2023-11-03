/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
import data.set.intervals.disjoint
import measure_theory.integral.set_integral
import measure_theory.measure.lebesgue.basic

/-!
# Integral over an interval

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `∫_{a}^{b} x, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b` and
`-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `interval_integrable f μ a b` as
`integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `set.uIoc a b = set.Ioc (min a b) (max a b)`.

Similarly, we define `∫_{a}^{b} x, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `set.uIoc a b = set.Ioc (min a b) (max a b)` instead of one of the other
three possible intervals with the same endpoints for two reasons:

* this way `∫_{a}^{b} x, f x ∂μ + ∫_{b}^{c} x, f x ∂μ = ∫_{a}^{c} x, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `set.Ioo` and `set.Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫_{a}^{b} x, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.

## Tags

integral
-/

noncomputable theory
open topological_space (second_countable_topology)
open measure_theory set classical filter function

open_locale classical topology filter ennreal big_operators interval nnreal

variables {ι 𝕜 E F A : Type*} [normed_add_comm_group E]

/-!
### Integrability on an interval
-/

/-- A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered
interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these
intervals is always empty, so this property is equivalent to `f` being integrable on
`(min a b, max a b]`. -/
def interval_integrable (f : ℝ → E) (μ : measure ℝ) (a b : ℝ) : Prop :=
integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ

section

variables {f : ℝ → E} {a b : ℝ} {μ : measure ℝ}

/-- A function is interval integrable with respect to a given measure `μ` on `a..b` if and
  only if it is integrable on `uIoc a b` with respect to `μ`. This is an equivalent
  definition of `interval_integrable`. -/
lemma interval_integrable_iff : interval_integrable f μ a b ↔ integrable_on f (Ι a b) μ :=
by rw [uIoc_eq_union, integrable_on_union, interval_integrable]

/-- If a function is interval integrable with respect to a given measure `μ` on `a..b` then
  it is integrable on `uIoc a b` with respect to `μ`. -/
lemma interval_integrable.def (h : interval_integrable f μ a b) : integrable_on f (Ι a b) μ :=
interval_integrable_iff.mp h

lemma interval_integrable_iff_integrable_Ioc_of_le (hab : a ≤ b) :
  interval_integrable f μ a b ↔ integrable_on f (Ioc a b) μ :=
by rw [interval_integrable_iff, uIoc_of_le hab]

lemma interval_integrable_iff' [has_no_atoms μ] :
  interval_integrable f μ a b ↔ integrable_on f (uIcc a b) μ :=
by rw [interval_integrable_iff, ←Icc_min_max, uIoc, integrable_on_Icc_iff_integrable_on_Ioc]

lemma interval_integrable_iff_integrable_Icc_of_le
  {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) {μ : measure ℝ} [has_no_atoms μ] :
  interval_integrable f μ a b ↔ integrable_on f (Icc a b) μ :=
by rw [interval_integrable_iff_integrable_Ioc_of_le hab, integrable_on_Icc_iff_integrable_on_Ioc]

/-- If a function is integrable with respect to a given measure `μ` then it is interval integrable
  with respect to `μ` on `uIcc a b`. -/
lemma measure_theory.integrable.interval_integrable (hf : integrable f μ) :
  interval_integrable f μ a b :=
⟨hf.integrable_on, hf.integrable_on⟩

lemma measure_theory.integrable_on.interval_integrable (hf : integrable_on f [a, b] μ) :
  interval_integrable f μ a b :=
⟨measure_theory.integrable_on.mono_set hf (Ioc_subset_Icc_self.trans Icc_subset_uIcc),
 measure_theory.integrable_on.mono_set hf (Ioc_subset_Icc_self.trans Icc_subset_uIcc')⟩

lemma interval_integrable_const_iff {c : E} :
  interval_integrable (λ _, c) μ a b ↔ c = 0 ∨ μ (Ι a b) < ∞ :=
by simp only [interval_integrable_iff, integrable_on_const]

@[simp] lemma interval_integrable_const [is_locally_finite_measure μ] {c : E} :
  interval_integrable (λ _, c) μ a b :=
interval_integrable_const_iff.2 $ or.inr measure_Ioc_lt_top

end

namespace interval_integrable

section

variables {f : ℝ → E} {a b c d : ℝ} {μ ν : measure ℝ}

@[symm] lemma symm (h : interval_integrable f μ a b) : interval_integrable f μ b a :=
h.symm

@[refl] lemma refl : interval_integrable f μ a a :=
by split; simp

@[trans] lemma trans {a b c : ℝ} (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) : interval_integrable f μ a c :=
⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
  (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

lemma trans_iterate_Ico {a : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
  (hint : ∀ k ∈ Ico m n, interval_integrable f μ (a k) (a $ k+1)) :
  interval_integrable f μ (a m) (a n) :=
begin
  revert hint,
  refine nat.le_induction _ _ n hmn,
  { simp },
  { assume p hp IH h,
    exact (IH (λ k hk, h k (Ico_subset_Ico_right p.le_succ hk))).trans (h p (by simp [hp])) }
end

lemma trans_iterate {a : ℕ → ℝ} {n : ℕ} (hint : ∀ k < n, interval_integrable f μ (a k) (a $ k+1)) :
  interval_integrable f μ (a 0) (a n) :=
trans_iterate_Ico bot_le (λ k hk, hint k hk.2)

lemma neg (h : interval_integrable f μ a b) : interval_integrable (-f) μ a b :=
⟨h.1.neg, h.2.neg⟩

lemma norm (h : interval_integrable f μ a b) :
  interval_integrable (λ x, ‖f x‖) μ a b  :=
⟨h.1.norm, h.2.norm⟩

lemma interval_integrable_norm_iff {f : ℝ → E} {μ : measure ℝ} {a b : ℝ}
  (hf : ae_strongly_measurable f (μ.restrict (Ι a b))) :
  interval_integrable (λ t, ‖f t‖) μ a b ↔ interval_integrable f μ a b :=
by { simp_rw [interval_integrable_iff, integrable_on], exact integrable_norm_iff hf }

lemma abs {f : ℝ → ℝ} (h : interval_integrable f μ a b) :
  interval_integrable (λ x, |f x|) μ a b  :=
h.norm

lemma mono (hf : interval_integrable f ν a b) (h1 : [c, d] ⊆ [a, b]) (h2 : μ ≤ ν) :
  interval_integrable f μ c d :=
interval_integrable_iff.mpr $ hf.def.mono
  (uIoc_subset_uIoc_of_uIcc_subset_uIcc h1) h2

lemma mono_measure (hf : interval_integrable f ν a b) (h : μ ≤ ν) :
  interval_integrable f μ a b :=
hf.mono rfl.subset h

lemma mono_set (hf : interval_integrable f μ a b) (h : [c, d] ⊆ [a, b]) :
  interval_integrable f μ c d :=
hf.mono h rfl.le

lemma mono_set_ae (hf : interval_integrable f μ a b) (h : Ι c d ≤ᵐ[μ] Ι a b) :
  interval_integrable f μ c d :=
interval_integrable_iff.mpr $ hf.def.mono_set_ae h

lemma mono_set' (hf : interval_integrable f μ a b) (hsub : Ι c d ⊆ Ι a b) :
  interval_integrable f μ c d :=
hf.mono_set_ae $ eventually_of_forall hsub

lemma mono_fun [normed_add_comm_group F] {g : ℝ → F}
  (hf : interval_integrable f μ a b) (hgm : ae_strongly_measurable g (μ.restrict (Ι a b)))
  (hle : (λ x, ‖g x‖) ≤ᵐ[μ.restrict (Ι a b)] (λ x, ‖f x‖)) : interval_integrable g μ a b :=
interval_integrable_iff.2 $ hf.def.integrable.mono hgm hle

lemma mono_fun' {g : ℝ → ℝ} (hg : interval_integrable g μ a b)
  (hfm : ae_strongly_measurable f (μ.restrict (Ι a b)))
  (hle : (λ x, ‖f x‖) ≤ᵐ[μ.restrict (Ι a b)] g) : interval_integrable f μ a b :=
interval_integrable_iff.2 $ hg.def.integrable.mono' hfm hle

protected lemma ae_strongly_measurable (h : interval_integrable f μ a b) :
  ae_strongly_measurable f (μ.restrict (Ioc a b)):=
h.1.ae_strongly_measurable

protected lemma ae_strongly_measurable' (h : interval_integrable f μ a b) :
  ae_strongly_measurable f (μ.restrict (Ioc b a)):=
h.2.ae_strongly_measurable

end

variables [normed_ring A] {f g : ℝ → E} {a b : ℝ} {μ : measure ℝ}

lemma smul [normed_field 𝕜] [normed_space 𝕜 E]
  {f : ℝ → E} {a b : ℝ} {μ : measure ℝ} (h : interval_integrable f μ a b) (r : 𝕜) :
  interval_integrable (r • f) μ a b :=
⟨h.1.smul r, h.2.smul r⟩

@[simp] lemma add (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) :
  interval_integrable (λ x, f x + g x) μ a b :=
⟨hf.1.add hg.1, hf.2.add hg.2⟩

@[simp] lemma sub (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) :
  interval_integrable (λ x, f x - g x) μ a b :=
⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

lemma sum (s : finset ι) {f : ι → ℝ → E} (h : ∀ i ∈ s, interval_integrable (f i) μ a b) :
  interval_integrable (∑ i in s, f i) μ a b :=
⟨integrable_finset_sum' s (λ i hi, (h i hi).1), integrable_finset_sum' s (λ i hi, (h i hi).2)⟩

lemma mul_continuous_on {f g : ℝ → A}
  (hf : interval_integrable f μ a b) (hg : continuous_on g [a, b]) :
  interval_integrable (λ x, f x * g x) μ a b :=
begin
  rw interval_integrable_iff at hf ⊢,
  exact hf.mul_continuous_on_of_subset hg measurable_set_Ioc is_compact_uIcc Ioc_subset_Icc_self
end

lemma continuous_on_mul {f g : ℝ → A}
  (hf : interval_integrable f μ a b) (hg : continuous_on g [a, b]) :
  interval_integrable (λ x, g x * f x) μ a b :=
begin
  rw interval_integrable_iff at hf ⊢,
  exact hf.continuous_on_mul_of_subset hg is_compact_uIcc measurable_set_Ioc Ioc_subset_Icc_self
end

@[simp]
lemma const_mul {f : ℝ → A}
  (hf : interval_integrable f μ a b) (c : A) : interval_integrable (λ x, c * f x) μ a b :=
hf.continuous_on_mul continuous_on_const

@[simp]
lemma mul_const {f : ℝ → A}
  (hf : interval_integrable f μ a b) (c : A) : interval_integrable (λ x, f x * c) μ a b :=
hf.mul_continuous_on continuous_on_const

@[simp]
lemma div_const {𝕜 : Type*} {f : ℝ → 𝕜} [normed_field 𝕜]
  (h : interval_integrable f μ a b) (c : 𝕜) :
  interval_integrable (λ x, f x / c) μ a b :=
by simpa only [div_eq_mul_inv] using mul_const h c⁻¹

lemma comp_mul_left (hf : interval_integrable f volume a b) (c : ℝ) :
  interval_integrable (λ x, f (c * x)) volume (a / c) (b / c) :=
begin
  rcases eq_or_ne c 0 with hc|hc, { rw hc, simp },
  rw interval_integrable_iff' at hf ⊢,
  have A : measurable_embedding (λ x, x * c⁻¹) :=
    (homeomorph.mul_right₀ _ (inv_ne_zero hc)).closed_embedding.measurable_embedding,
  rw [←real.smul_map_volume_mul_right (inv_ne_zero hc), integrable_on, measure.restrict_smul,
    integrable_smul_measure (by simpa : ennreal.of_real (|c⁻¹|) ≠ 0) ennreal.of_real_ne_top,
    ←integrable_on, measurable_embedding.integrable_on_map_iff A],
  convert hf using 1,
  { ext, simp only [comp_app], congr' 1, field_simp, ring },
  { rw preimage_mul_const_uIcc (inv_ne_zero hc), field_simp [hc] },
end

lemma comp_mul_right (hf : interval_integrable f volume a b) (c : ℝ) :
  interval_integrable (λ x, f (x * c)) volume (a / c) (b / c) :=
by simpa only [mul_comm] using comp_mul_left hf c

lemma comp_add_right (hf : interval_integrable f volume a b) (c : ℝ) :
  interval_integrable (λ x, f (x + c)) volume (a - c) (b - c) :=
begin
  wlog h : a ≤ b,
  { exact interval_integrable.symm (this hf.symm _ (le_of_not_le h)) },
  rw interval_integrable_iff' at hf ⊢,
  have A : measurable_embedding (λ x, x + c) :=
    (homeomorph.add_right c).closed_embedding.measurable_embedding,
  have Am : measure.map (λ x, x + c) volume = volume,
  { exact is_add_left_invariant.is_add_right_invariant.map_add_right_eq_self _ },
  rw ←Am at hf,
  convert (measurable_embedding.integrable_on_map_iff A).mp hf,
  rw preimage_add_const_uIcc,
end

lemma comp_add_left (hf : interval_integrable f volume a b) (c : ℝ) :
  interval_integrable (λ x, f (c + x)) volume (a - c) (b - c) :=
by simpa only [add_comm] using interval_integrable.comp_add_right hf c

lemma comp_sub_right (hf : interval_integrable f volume a b) (c : ℝ) :
  interval_integrable (λ x, f (x - c)) volume (a + c) (b + c) :=
by simpa only [sub_neg_eq_add] using interval_integrable.comp_add_right hf (-c)

lemma iff_comp_neg  :
  interval_integrable f volume a b ↔ interval_integrable (λ x, f (-x)) volume (-a) (-b) :=
begin
  split, all_goals { intro hf, convert comp_mul_left hf (-1), simp, field_simp, field_simp },
end

lemma comp_sub_left (hf : interval_integrable f volume a b) (c : ℝ) :
  interval_integrable (λ x, f (c - x)) volume (c - a) (c - b) :=
by simpa only [neg_sub, ←sub_eq_add_neg] using iff_comp_neg.mp (hf.comp_add_left c)

end interval_integrable

section

variables {μ : measure ℝ} [is_locally_finite_measure μ]

lemma continuous_on.interval_integrable {u : ℝ → E} {a b : ℝ}
  (hu : continuous_on u (uIcc a b)) : interval_integrable u μ a b :=
(continuous_on.integrable_on_Icc hu).interval_integrable

lemma continuous_on.interval_integrable_of_Icc {u : ℝ → E} {a b : ℝ} (h : a ≤ b)
  (hu : continuous_on u (Icc a b)) : interval_integrable u μ a b :=
continuous_on.interval_integrable ((uIcc_of_le h).symm ▸ hu)

/-- A continuous function on `ℝ` is `interval_integrable` with respect to any locally finite measure
`ν` on ℝ. -/
lemma continuous.interval_integrable {u : ℝ → E} (hu : continuous u) (a b : ℝ) :
  interval_integrable u μ a b :=
hu.continuous_on.interval_integrable

end

section

variables {μ : measure ℝ} [is_locally_finite_measure μ] [conditionally_complete_linear_order E]
  [order_topology E] [second_countable_topology E]

lemma monotone_on.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : monotone_on u (uIcc a b)) :
  interval_integrable u μ a b :=
begin
  rw interval_integrable_iff,
  exact (hu.integrable_on_is_compact is_compact_uIcc).mono_set Ioc_subset_Icc_self,
end

lemma antitone_on.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : antitone_on u (uIcc a b)) :
  interval_integrable u μ a b :=
hu.dual_right.interval_integrable

lemma monotone.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : monotone u) :
  interval_integrable u μ a b :=
(hu.monotone_on _).interval_integrable

lemma antitone.interval_integrable {u : ℝ → E} {a b : ℝ} (hu : antitone u) :
  interval_integrable u μ a b :=
(hu.antitone_on _).interval_integrable

end

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l' ⊓ μ.ae`. Then `f` is interval integrable on
`u..v` provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter ℝ` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
lemma filter.tendsto.eventually_interval_integrable_ae {f : ℝ → E} {μ : measure ℝ}
  {l l' : filter ℝ}  (hfm : strongly_measurable_at_filter f l' μ)
  [tendsto_Ixx_class Ioc l l'] [is_measurably_generated l']
  (hμ : μ.finite_at_filter l') {c : E} (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  {u v : ι → ℝ} {lt : filter ι} (hu : tendsto u lt l) (hv : tendsto v lt l) :
  ∀ᶠ t in lt, interval_integrable f μ (u t) (v t) :=
have _ := (hf.integrable_at_filter_ae hfm hμ).eventually,
((hu.Ioc hv).eventually this).and $ (hv.Ioc hu).eventually this

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : ℝ → E` has a finite limit at `l`. Then `f` is interval integrable on `u..v`
provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter ℝ` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
lemma filter.tendsto.eventually_interval_integrable {f : ℝ → E} {μ : measure ℝ}
  {l l' : filter ℝ} (hfm : strongly_measurable_at_filter f l' μ)
  [tendsto_Ixx_class Ioc l l'] [is_measurably_generated l']
  (hμ : μ.finite_at_filter l') {c : E} (hf : tendsto f l' (𝓝 c))
  {u v : ι → ℝ} {lt : filter ι} (hu : tendsto u lt l) (hv : tendsto v lt l) :
  ∀ᶠ t in lt, interval_integrable f μ (u t) (v t) :=
(hf.mono_left inf_le_left).eventually_interval_integrable_ae hfm hμ hu hv

/-!
### Interval integral: definition and basic properties

In this section we define `∫_{a}^{b} x, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`
and prove some basic properties.
-/

variables [complete_space E] [normed_space ℝ E]

/-- The interval integral `∫_{a}^{b} x, f x ∂μ` is defined
as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`. -/
def interval_integral (f : ℝ → E) (a b : ℝ) (μ : measure ℝ) : E :=
∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ

notation `∫_{` a `}^{` b `}` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := interval_integral r a b μ
notation `∫_{` a `}^{` b `}` binders `, ` r:(scoped:60 f, interval_integral f a b volume) := r

namespace interval_integral

section basic

variables {a b : ℝ} {f g : ℝ → E} {μ : measure ℝ}

@[simp] lemma integral_zero : ∫_{a}^{b} x, (0 : E) ∂μ = 0 :=
by simp [interval_integral]

lemma integral_of_le (h : a ≤ b) : ∫_{a}^{b} x, f x ∂μ = ∫ x in Ioc a b, f x ∂μ :=
by simp [interval_integral, h]

@[simp] lemma integral_same : ∫_{a}^{a} x, f x ∂μ = 0 :=
sub_self _

lemma integral_symm (a b) : ∫_{b}^{a} x, f x ∂μ = -∫_{a}^{b} x, f x ∂μ :=
by simp only [interval_integral, neg_sub]

lemma integral_of_ge (h : b ≤ a) : ∫_{a}^{b} x, f x ∂μ = -∫ x in Ioc b a, f x ∂μ :=
by simp only [integral_symm b, integral_of_le h]

lemma interval_integral_eq_integral_uIoc (f : ℝ → E) (a b : ℝ) (μ : measure ℝ) :
  ∫_{a}^{b} x, f x ∂μ = (if a ≤ b then 1 else -1 : ℝ) • ∫ x in Ι a b, f x ∂μ :=
begin
  split_ifs with h,
  { simp only [integral_of_le h, uIoc_of_le h, one_smul] },
  { simp only [integral_of_ge (not_le.1 h).le, uIoc_of_lt (not_le.1 h), neg_one_smul] }
end

lemma norm_interval_integral_eq (f : ℝ → E) (a b : ℝ) (μ : measure ℝ) :
  ‖∫_{a}^{b} x, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ :=
begin
  simp_rw [interval_integral_eq_integral_uIoc, norm_smul],
  split_ifs; simp only [norm_neg, norm_one, one_mul],
end

lemma abs_interval_integral_eq (f : ℝ → ℝ) (a b : ℝ) (μ : measure ℝ) :
  |∫_{a}^{b} x, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
norm_interval_integral_eq f a b μ

lemma integral_cases (f : ℝ → E) (a b) :
  ∫_{a}^{b} x, f x ∂μ ∈ ({∫ x in Ι a b, f x ∂μ, -∫ x in Ι a b, f x ∂μ} : set E) :=
by { rw interval_integral_eq_integral_uIoc, split_ifs; simp }

lemma integral_undef (h : ¬ interval_integrable f μ a b) :
  ∫_{a}^{b} x, f x ∂μ = 0 :=
by cases le_total a b with hab hab;
  simp only [integral_of_le, integral_of_ge, hab, neg_eq_zero];
    refine integral_undef (not_imp_not.mpr _ h);
      simpa only [hab, Ioc_eq_empty_of_le, integrable_on_empty, not_true, false_or, or_false]
        using not_and_distrib.mp h

lemma interval_integrable_of_integral_ne_zero {a b : ℝ}
  {f : ℝ → E} {μ : measure ℝ} (h : ∫_{a}^{b} x, f x ∂μ ≠ 0) :
  interval_integrable f μ a b :=
by { contrapose! h, exact interval_integral.integral_undef h }

lemma integral_non_ae_strongly_measurable
  (hf : ¬ ae_strongly_measurable f (μ.restrict (Ι a b))) :
  ∫_{a}^{b} x, f x ∂μ = 0 :=
by rw [interval_integral_eq_integral_uIoc, integral_non_ae_strongly_measurable hf, smul_zero]

lemma integral_non_ae_strongly_measurable_of_le (h : a ≤ b)
  (hf : ¬ ae_strongly_measurable f (μ.restrict (Ioc a b))) :
  ∫_{a}^{b} x, f x ∂μ = 0 :=
integral_non_ae_strongly_measurable $ by rwa [uIoc_of_le h]

lemma norm_integral_min_max (f : ℝ → E) :
  ‖∫_{min a b}^{max a b} x, f x ∂μ‖ = ‖∫_{a}^{b} x, f x ∂μ‖ :=
by cases le_total a b; simp [*, integral_symm a b]

lemma norm_integral_eq_norm_integral_Ioc (f : ℝ → E) :
  ‖∫_{a}^{b} x, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ :=
by rw [← norm_integral_min_max, integral_of_le min_le_max, uIoc]

lemma abs_integral_eq_abs_integral_uIoc (f : ℝ → ℝ) :
  |∫_{a}^{b} x, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
norm_integral_eq_norm_integral_Ioc f

lemma norm_integral_le_integral_norm_Ioc :
  ‖∫_{a}^{b} x, f x ∂μ‖ ≤ ∫ x in Ι a b, ‖f x‖ ∂μ :=
calc ‖∫_{a}^{b} x, f x ∂μ‖ = ‖∫ x in Ι a b, f x ∂μ‖ :
  norm_integral_eq_norm_integral_Ioc f
... ≤ ∫ x in Ι a b, ‖f x‖ ∂μ :
  norm_integral_le_integral_norm f

lemma norm_integral_le_abs_integral_norm : ‖∫_{a}^{b} x, f x ∂μ‖ ≤ |∫_{a}^{b} x, ‖f x‖ ∂μ| :=
begin
  simp only [← real.norm_eq_abs, norm_integral_eq_norm_integral_Ioc],
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)
end

lemma norm_integral_le_integral_norm (h : a ≤ b) :
  ‖∫_{a}^{b} x, f x ∂μ‖ ≤ ∫_{a}^{b} x, ‖f x‖ ∂μ :=
norm_integral_le_integral_norm_Ioc.trans_eq $ by rw [uIoc_of_le h, integral_of_le h]

lemma norm_integral_le_of_norm_le {g : ℝ → ℝ}
  (h : ∀ᵐ t ∂(μ.restrict $ Ι a b), ‖f t‖ ≤ g t)
  (hbound : interval_integrable g μ a b) :
  ‖∫_{a}^{b} t, f t ∂μ‖ ≤ |∫_{a}^{b} t, g t ∂μ| :=
by simp_rw [norm_interval_integral_eq, abs_interval_integral_eq,
  abs_eq_self.mpr (integral_nonneg_of_ae $ h.mono $ λ t ht, (norm_nonneg _).trans ht),
  norm_integral_le_of_norm_le hbound.def h]

lemma norm_integral_le_of_norm_le_const_ae {a b C : ℝ} {f : ℝ → E}
  (h : ∀ᵐ x, x ∈ Ι a b → ‖f x‖ ≤ C) :
  ‖∫_{a}^{b} x, f x‖ ≤ C * |b - a| :=
begin
  rw [norm_integral_eq_norm_integral_Ioc],
  convert norm_set_integral_le_of_norm_le_const_ae'' _ measurable_set_Ioc h,
  { rw [real.volume_Ioc, max_sub_min_eq_abs, ennreal.to_real_of_real (abs_nonneg _)] },
  { simp only [real.volume_Ioc, ennreal.of_real_lt_top] },
end

lemma norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E}
  (h : ∀ x ∈ Ι a b, ‖f x‖ ≤ C) :
  ‖∫_{a}^{b} x, f x‖ ≤ C * |b - a| :=
norm_integral_le_of_norm_le_const_ae $ eventually_of_forall h

@[simp] lemma integral_add (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) :
  ∫_{a}^{b} x, f x + g x ∂μ = ∫_{a}^{b} x, f x ∂μ + ∫_{a}^{b} x, g x ∂μ :=
by simp only [interval_integral_eq_integral_uIoc, integral_add hf.def hg.def, smul_add]

lemma integral_finset_sum {ι} {s : finset ι} {f : ι → ℝ → E}
  (h : ∀ i ∈ s, interval_integrable (f i) μ a b) :
  ∫_{a}^{b} x, ∑ i in s, f i x ∂μ = ∑ i in s, ∫_{a}^{b} x, f i x ∂μ :=
by simp only [interval_integral_eq_integral_uIoc,
  integral_finset_sum s (λ i hi, (h i hi).def), finset.smul_sum]

@[simp] lemma integral_neg : ∫_{a}^{b} x, -f x ∂μ = -∫_{a}^{b} x, f x ∂μ :=
by { simp only [interval_integral, integral_neg], abel }

@[simp] lemma integral_sub (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) :
  ∫_{a}^{b} x, f x - g x ∂μ = ∫_{a}^{b} x, f x ∂μ - ∫_{a}^{b} x, g x ∂μ :=
by simpa only [sub_eq_add_neg] using (integral_add hf hg.neg).trans (congr_arg _ integral_neg)

@[simp] lemma integral_smul {𝕜 : Type*} [nontrivially_normed_field 𝕜] [normed_space 𝕜 E]
  [smul_comm_class ℝ 𝕜 E]
  (r : 𝕜) (f : ℝ → E) : ∫_{a}^{b} x, r • f x ∂μ = r • ∫_{a}^{b} x, f x ∂μ :=
by simp only [interval_integral, integral_smul, smul_sub]

@[simp] lemma integral_smul_const {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E] (f : ℝ → 𝕜) (c : E) :
  ∫_{a}^{b} x, f x • c ∂μ = (∫_{a}^{b} x, f x ∂μ) • c :=
by simp only [interval_integral_eq_integral_uIoc, integral_smul_const, smul_assoc]

@[simp] lemma integral_const_mul {𝕜 : Type*} [is_R_or_C 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
  ∫_{a}^{b} x, r * f x ∂μ = r * ∫_{a}^{b} x, f x ∂μ :=
integral_smul r f

@[simp] lemma integral_mul_const {𝕜 : Type*} [is_R_or_C 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
  ∫_{a}^{b} x, f x * r ∂μ = ∫_{a}^{b} x, f x ∂μ * r :=
by simpa only [mul_comm r] using integral_const_mul r f

@[simp] lemma integral_div {𝕜 : Type*} [is_R_or_C 𝕜] (r : 𝕜) (f : ℝ → 𝕜) :
  ∫_{a}^{b} x, f x / r ∂μ = ∫_{a}^{b} x, f x ∂μ / r :=
by simpa only [div_eq_mul_inv] using integral_mul_const r⁻¹ f

lemma integral_const' (c : E) :
  ∫_{a}^{b} x, c ∂μ = ((μ $ Ioc a b).to_real - (μ $ Ioc b a).to_real) • c :=
by simp only [interval_integral, set_integral_const, sub_smul]

@[simp] lemma integral_const (c : E) : ∫_{a}^{b} x, c = (b - a) • c :=
by simp only [integral_const', real.volume_Ioc, ennreal.to_real_of_real', ← neg_sub b,
  max_zero_sub_eq_self]

lemma integral_smul_measure (c : ℝ≥0∞) :
  ∫_{a}^{b} x, f x ∂(c • μ) = c.to_real • ∫_{a}^{b} x, f x ∂μ :=
by simp only [interval_integral, measure.restrict_smul, integral_smul_measure, smul_sub]

end basic

lemma integral_of_real {a b : ℝ} {μ : measure ℝ} {f : ℝ → ℝ} :
  ∫_{a}^{b} x, (f x : ℂ) ∂μ = ↑(∫_{a}^{b} x, f x ∂μ) :=
by simp only [interval_integral, integral_of_real, complex.of_real_sub]

section continuous_linear_map

variables {a b : ℝ} {μ : measure ℝ} {f : ℝ → E}
variables [is_R_or_C 𝕜] [normed_space 𝕜 E] [normed_add_comm_group F] [normed_space 𝕜 F]

open continuous_linear_map

lemma _root_.continuous_linear_map.interval_integral_apply {a b : ℝ} {φ : ℝ → F →L[𝕜] E}
  (hφ : interval_integrable φ μ a b) (v : F) :
  (∫_{a}^{b} x, φ x ∂μ) v = ∫_{a}^{b} x, φ x v ∂μ :=
by simp_rw [interval_integral_eq_integral_uIoc, ← integral_apply hφ.def v, coe_smul',
  pi.smul_apply]

variables [normed_space ℝ F] [complete_space F]

lemma _root_.continuous_linear_map.interval_integral_comp_comm
  (L : E →L[𝕜] F) (hf : interval_integrable f μ a b) :
  ∫_{a}^{b} x, L (f x) ∂μ = L (∫_{a}^{b} x, f x ∂μ) :=
by simp_rw [interval_integral, L.integral_comp_comm hf.1, L.integral_comp_comm hf.2, L.map_sub]

end continuous_linear_map
section comp

variables {a b c d : ℝ} (f : ℝ → E)

@[simp] lemma integral_comp_mul_right (hc : c ≠ 0) :
  ∫_{a}^{b} x, f (x * c) = c⁻¹ • ∫_{a*c}^{b*c} x, f x :=
begin
  have A : measurable_embedding (λ x, x * c) :=
    (homeomorph.mul_right₀ c hc).closed_embedding.measurable_embedding,
  conv_rhs { rw [← real.smul_map_volume_mul_right hc] },
  simp_rw [integral_smul_measure, interval_integral, A.set_integral_map,
          ennreal.to_real_of_real (abs_nonneg c)],
  cases hc.lt_or_lt,
  { simp [h, mul_div_cancel, hc, abs_of_neg, measure.restrict_congr_set Ico_ae_eq_Ioc] },
  { simp [h, mul_div_cancel, hc, abs_of_pos] }
end

@[simp] lemma smul_integral_comp_mul_right (c) :
  c • ∫_{a}^{b} x, f (x * c) = ∫_{a*c}^{b*c} x, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_mul_left (hc : c ≠ 0) :
  ∫_{a}^{b} x, f (c * x) = c⁻¹ • ∫_{c*a}^{c*b} x, f x :=
by simpa only [mul_comm c] using integral_comp_mul_right f hc

@[simp] lemma smul_integral_comp_mul_left (c) :
  c • ∫_{a}^{b} x, f (c * x) = ∫_{c*a}^{c*b} x, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_div (hc : c ≠ 0) :
  ∫_{a}^{b} x, f (x / c) = c • ∫_{a/c}^{b/c} x, f x :=
by simpa only [inv_inv] using integral_comp_mul_right f (inv_ne_zero hc)

@[simp] lemma inv_smul_integral_comp_div (c) :
  c⁻¹ • ∫_{a}^{b} x, f (x / c) = ∫_{a/c}^{b/c} x, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_add_right (d) :
  ∫_{a}^{b} x, f (x + d) = ∫_{a+d}^{b+d} x, f x :=
have A : measurable_embedding (λ x, x + d) :=
  (homeomorph.add_right d).closed_embedding.measurable_embedding,
calc  ∫_{a}^{b} x, f (x + d)
    = ∫_{a+d}^{b+d} x, f x ∂(measure.map (λ x, x + d) volume)
                           : by simp [interval_integral, A.set_integral_map]
... = ∫_{a+d}^{b+d} x, f x : by rw [map_add_right_eq_self]

@[simp] lemma integral_comp_add_left (d) :
  ∫_{a}^{b} x, f (d + x) = ∫_{d+a}^{d+b} x, f x :=
by simpa only [add_comm] using integral_comp_add_right f d

@[simp] lemma integral_comp_mul_add (hc : c ≠ 0) (d) :
  ∫_{a}^{b} x, f (c * x + d) = c⁻¹ • ∫_{c*a+d}^{c*b+d} x, f x :=
by rw [← integral_comp_add_right, ← integral_comp_mul_left _ hc]

@[simp] lemma smul_integral_comp_mul_add (c d) :
  c • ∫_{a}^{b} x, f (c * x + d) = ∫_{c*a+d}^{c*b+d} x, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_add_mul (hc : c ≠ 0) (d) :
  ∫_{a}^{b} x, f (d + c * x) = c⁻¹ • ∫_{d+c*a}^{d+c*b} x, f x :=
by rw [← integral_comp_add_left, ← integral_comp_mul_left _ hc]

@[simp] lemma smul_integral_comp_add_mul (c d) :
  c • ∫_{a}^{b} x, f (d + c * x) = ∫_{d+c*a}^{d+c*b} x, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_div_add (hc : c ≠ 0) (d) :
  ∫_{a}^{b} x, f (x / c + d) = c • ∫_{a/c+d}^{b/c+d} x, f x :=
by simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_add f (inv_ne_zero hc) d

@[simp] lemma inv_smul_integral_comp_div_add (c d) :
  c⁻¹ • ∫_{a}^{b} x, f (x / c + d) = ∫_{a/c+d}^{b/c+d} x, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_add_div (hc : c ≠ 0) (d) :
  ∫_{a}^{b} x, f (d + x / c) = c • ∫_{d+a/c}^{d+b/c} x, f x :=
by simpa only [div_eq_inv_mul, inv_inv] using integral_comp_add_mul f (inv_ne_zero hc) d

@[simp] lemma inv_smul_integral_comp_add_div (c d) :
  c⁻¹ • ∫_{a}^{b} x, f (d + x / c) = ∫_{d+a/c}^{d+b/c} x, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_mul_sub (hc : c ≠ 0) (d) :
  ∫_{a}^{b} x, f (c * x - d) = c⁻¹ • ∫_{c*a-d}^{c*b-d} x, f x :=
by simpa only [sub_eq_add_neg] using integral_comp_mul_add f hc (-d)

@[simp] lemma smul_integral_comp_mul_sub (c d) :
  c • ∫_{a}^{b} x, f (c * x - d) = ∫_{c*a-d}^{c*b-d} x, f x  :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_sub_mul (hc : c ≠ 0) (d) :
  ∫_{a}^{b} x, f (d - c * x) = c⁻¹ • ∫_{d-c*b}^{d-c*a} x, f x :=
begin
  simp only [sub_eq_add_neg, neg_mul_eq_neg_mul],
  rw [integral_comp_add_mul f (neg_ne_zero.mpr hc) d, integral_symm],
  simp only [inv_neg, smul_neg, neg_neg, neg_smul],
end

@[simp] lemma smul_integral_comp_sub_mul (c d) :
  c • ∫_{a}^{b} x, f (d - c * x) = ∫_{d-c*b}^{d-c*a} x, f x  :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_div_sub (hc : c ≠ 0) (d) :
  ∫_{a}^{b} x, f (x / c - d) = c • ∫_{a/c-d}^{b/c-d} x, f x :=
by simpa only [div_eq_inv_mul, inv_inv] using integral_comp_mul_sub f (inv_ne_zero hc) d

@[simp] lemma inv_smul_integral_comp_div_sub (c d) :
  c⁻¹ • ∫_{a}^{b} x, f (x / c - d) = ∫_{a/c-d}^{b/c-d} x, f x  :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_sub_div (hc : c ≠ 0) (d) :
  ∫_{a}^{b} x, f (d - x / c) = c • ∫_{d-b/c}^{d-a/c} x, f x :=
by simpa only [div_eq_inv_mul, inv_inv] using integral_comp_sub_mul f (inv_ne_zero hc) d

@[simp] lemma inv_smul_integral_comp_sub_div (c d) :
  c⁻¹ • ∫_{a}^{b} x, f (d - x / c) = ∫_{d-b/c}^{d-a/c} x, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_sub_right (d) :
  ∫_{a}^{b} x, f (x - d) = ∫_{a-d}^{b-d} x, f x :=
by simpa only [sub_eq_add_neg] using integral_comp_add_right f (-d)

@[simp] lemma integral_comp_sub_left (d) :
  ∫_{a}^{b} x, f (d - x) = ∫_{d-b}^{d-a} x, f x :=
by simpa only [one_mul, one_smul, inv_one] using integral_comp_sub_mul f one_ne_zero d

@[simp] lemma integral_comp_neg : ∫_{a}^{b} x, f (-x) = ∫_{-b}^{-a} x, f x :=
by simpa only [zero_sub] using integral_comp_sub_left f 0

end comp

/-!
### Integral is an additive function of the interval

In this section we prove that `∫_{a}^{b} x, f x ∂μ + ∫_{b}^{c} x, f x ∂μ = ∫_{a}^{c} x, f x ∂μ`
as well as a few other identities trivially equivalent to this one. We also prove that
`∫_{a}^{b} x, f x ∂μ = ∫ x, f x ∂μ` provided that `support f ⊆ Ioc a b`.
-/

section order_closed_topology

variables {a b c d : ℝ} {f g : ℝ → E} {μ : measure ℝ}

/-- If two functions are equal in the relevant interval, their interval integrals are also equal. -/
lemma integral_congr {a b : ℝ} (h : eq_on f g [a, b]) :
  ∫_{a}^{b} x, f x ∂μ = ∫_{a}^{b} x, g x ∂μ :=
by cases le_total a b with hab hab; simpa [hab, integral_of_le, integral_of_ge]
  using set_integral_congr measurable_set_Ioc (h.mono Ioc_subset_Icc_self)

lemma integral_add_adjacent_intervals_cancel (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  ∫_{a}^{b} x, f x ∂μ + ∫_{b}^{c} x, f x ∂μ + ∫_{c}^{a} x, f x ∂μ = 0 :=
begin
  have hac := hab.trans hbc,
  simp only [interval_integral, sub_add_sub_comm, sub_eq_zero],
  iterate 4 { rw ← integral_union },
  { suffices : Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc b a ∪ Ioc c b ∪ Ioc a c, by rw this,
    rw [Ioc_union_Ioc_union_Ioc_cycle, union_right_comm, Ioc_union_Ioc_union_Ioc_cycle,
      min_left_comm, max_left_comm] },
  all_goals { simp [*, measurable_set.union, measurable_set_Ioc, Ioc_disjoint_Ioc_same,
    Ioc_disjoint_Ioc_same.symm, hab.1, hab.2, hbc.1, hbc.2, hac.1, hac.2] }
end

lemma integral_add_adjacent_intervals (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  ∫_{a}^{b} x, f x ∂μ + ∫_{b}^{c} x, f x ∂μ = ∫_{a}^{c} x, f x ∂μ :=
by rw [← add_neg_eq_zero, ← integral_symm, integral_add_adjacent_intervals_cancel hab hbc]

lemma sum_integral_adjacent_intervals_Ico {a : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n)
  (hint : ∀ k ∈ Ico m n, interval_integrable f μ (a k) (a $ k+1)) :
  ∑ (k : ℕ) in finset.Ico m n, ∫_{(a k)}^{(a $ k+1)} x, f x ∂μ = ∫_{(a m)}^{(a n)} x, f x ∂μ :=
begin
  revert hint,
  refine nat.le_induction _ _ n hmn,
  { simp },
  { assume p hmp IH h,
    rw [finset.sum_Ico_succ_top hmp, IH, integral_add_adjacent_intervals],
    { apply interval_integrable.trans_iterate_Ico hmp (λ k hk, h k _),
      exact (Ico_subset_Ico le_rfl (nat.le_succ _)) hk },
    { apply h,
      simp [hmp] },
    { assume k hk,
      exact h _ (Ico_subset_Ico_right p.le_succ hk) } }
end

lemma sum_integral_adjacent_intervals {a : ℕ → ℝ} {n : ℕ}
  (hint : ∀ k < n, interval_integrable f μ (a k) (a $ k+1)) :
  ∑ (k : ℕ) in finset.range n, ∫_{(a k)}^{(a $ k+1)} x, f x ∂μ = ∫_{(a 0)}^{(a n)} x, f x ∂μ :=
begin
  rw ← nat.Ico_zero_eq_range,
  exact sum_integral_adjacent_intervals_Ico (zero_le n) (λ k hk, hint k hk.2),
end

lemma integral_interval_sub_left (hab : interval_integrable f μ a b)
  (hac : interval_integrable f μ a c) :
  ∫_{a}^{b} x, f x ∂μ - ∫_{a}^{c} x, f x ∂μ = ∫_{c}^{b} x, f x ∂μ :=
sub_eq_of_eq_add' $ eq.symm $ integral_add_adjacent_intervals hac (hac.symm.trans hab)

lemma integral_interval_add_interval_comm (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫_{a}^{b} x, f x ∂μ + ∫_{c}^{d} x, f x ∂μ = ∫_{a}^{d} x, f x ∂μ + ∫_{c}^{b} x, f x ∂μ :=
by rw [← integral_add_adjacent_intervals hac hcd, add_assoc, add_left_comm,
  integral_add_adjacent_intervals hac (hac.symm.trans hab), add_comm]

lemma integral_interval_sub_interval_comm (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫_{a}^{b} x, f x ∂μ - ∫_{c}^{d} x, f x ∂μ = ∫_{a}^{c} x, f x ∂μ - ∫_{b}^{d} x, f x ∂μ :=
by simp only [sub_eq_add_neg, ← integral_symm,
  integral_interval_add_interval_comm hab hcd.symm (hac.trans hcd)]

lemma integral_interval_sub_interval_comm' (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫_{a}^{b} x, f x ∂μ - ∫_{c}^{d} x, f x ∂μ = ∫_{d}^{b} x, f x ∂μ - ∫_{c}^{a} x, f x ∂μ :=
by { rw [integral_interval_sub_interval_comm hab hcd hac, integral_symm b d, integral_symm a c,
  sub_neg_eq_add, sub_eq_neg_add], }

lemma integral_Iic_sub_Iic (ha : integrable_on f (Iic a) μ) (hb : integrable_on f (Iic b) μ) :
  ∫ x in Iic b, f x ∂μ - ∫ x in Iic a, f x ∂μ = ∫_{a}^{b} x, f x ∂μ :=
begin
  wlog hab : a ≤ b generalizing a b,
  { rw [integral_symm, ← this hb ha (le_of_not_le hab), neg_sub] },
  rw [sub_eq_iff_eq_add', integral_of_le hab, ← integral_union (Iic_disjoint_Ioc le_rfl),
    Iic_union_Ioc_eq_Iic hab],
  exacts [measurable_set_Ioc, ha, hb.mono_set (λ _, and.right)]
end

/-- If `μ` is a finite measure then `∫_{a}^{b} x, c ∂μ = (μ (Iic b) - μ (Iic a)) • c`. -/
lemma integral_const_of_cdf [is_finite_measure μ] (c : E) :
  ∫_{a}^{b} x, c ∂μ = ((μ (Iic b)).to_real - (μ (Iic a)).to_real) • c :=
begin
  simp only [sub_smul, ← set_integral_const],
  refine (integral_Iic_sub_Iic _ _).symm;
    simp only [integrable_on_const, measure_lt_top, or_true]
end

lemma integral_eq_integral_of_support_subset {a b} (h : support f ⊆ Ioc a b) :
  ∫_{a}^{b} x, f x ∂μ = ∫ x, f x ∂μ :=
begin
  cases le_total a b with hab hab,
  { rw [integral_of_le hab, ← integral_indicator measurable_set_Ioc, indicator_eq_self.2 h];
    apply_instance },
  { rw [Ioc_eq_empty hab.not_lt, subset_empty_iff, support_eq_empty_iff] at h,
    simp [h] }
end

lemma integral_congr_ae' (h : ∀ᵐ x ∂μ, x ∈ Ioc a b → f x = g x)
  (h' : ∀ᵐ x ∂μ, x ∈ Ioc b a → f x = g x) :
  ∫_{a}^{b} x, f x ∂μ = ∫_{a}^{b} x, g x ∂μ :=
by simp only [interval_integral, set_integral_congr_ae (measurable_set_Ioc) h,
              set_integral_congr_ae (measurable_set_Ioc) h']

lemma integral_congr_ae (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = g x) :
  ∫_{a}^{b} x, f x ∂μ = ∫_{a}^{b} x, g x ∂μ :=
integral_congr_ae' (ae_uIoc_iff.mp h).1 (ae_uIoc_iff.mp h).2

lemma integral_zero_ae (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = 0) :
  ∫_{a}^{b} x, f x ∂μ = 0 :=
calc ∫_{a}^{b} x, f x ∂μ = ∫_{a}^{b} x, 0 ∂μ : integral_congr_ae h
                     ... = 0                 : integral_zero

lemma integral_indicator {a₁ a₂ a₃ : ℝ} (h : a₂ ∈ Icc a₁ a₃) :
  ∫_{a₁}^{a₃} x, indicator {x | x ≤ a₂} f x ∂ μ = ∫_{a₁}^{a₂} x, f x ∂ μ :=
begin
  have : {x | x ≤ a₂} ∩ Ioc a₁ a₃ = Ioc a₁ a₂, from Iic_inter_Ioc_of_le h.2,
  rw [integral_of_le h.1, integral_of_le (h.1.trans h.2),
      integral_indicator, measure.restrict_restrict, this],
  exact measurable_set_Iic,
  all_goals { apply measurable_set_Iic },
end

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
lemma tendsto_integral_filter_of_dominated_convergence {ι} {l : filter ι}
  [l.is_countably_generated] {F : ι → ℝ → E} (bound : ℝ → ℝ)
  (hF_meas : ∀ᶠ n in l, ae_strongly_measurable (F n) (μ.restrict (Ι a b)))
  (h_bound : ∀ᶠ n in l, ∀ᵐ x ∂μ, x ∈ Ι a b → ‖F n x‖ ≤ bound x)
  (bound_integrable : interval_integrable bound μ a b)
  (h_lim : ∀ᵐ x ∂μ, x ∈ Ι a b → tendsto (λ n, F n x) l (𝓝 (f x))) :
  tendsto (λn, ∫_{a}^{b} x, F n x ∂μ) l (𝓝 $ ∫_{a}^{b} x, f x ∂μ) :=
begin
  simp only [interval_integrable_iff, interval_integral_eq_integral_uIoc,
    ← ae_restrict_iff' measurable_set_uIoc] at *,
  exact tendsto_const_nhds.smul
    (tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_lim)
end

/-- Lebesgue dominated convergence theorem for series. -/
lemma has_sum_integral_of_dominated_convergence {ι} [countable ι]
  {F : ι → ℝ → E} (bound : ι → ℝ → ℝ)
  (hF_meas : ∀ n, ae_strongly_measurable (F n) (μ.restrict (Ι a b)))
  (h_bound : ∀ n, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F n t‖ ≤ bound n t)
  (bound_summable : ∀ᵐ t ∂μ, t ∈ Ι a b → summable (λ n, bound n t))
  (bound_integrable : interval_integrable (λ t, ∑' n, bound n t) μ a b)
  (h_lim : ∀ᵐ t ∂μ, t ∈ Ι a b → has_sum (λ n, F n t) (f t)) :
  has_sum (λn, ∫_{a}^{b} t, F n t ∂μ) (∫_{a}^{b} t, f t ∂μ) :=
begin
  simp only [interval_integrable_iff, interval_integral_eq_integral_uIoc,
    ← ae_restrict_iff' measurable_set_uIoc] at *,
  exact (has_sum_integral_of_dominated_convergence bound hF_meas h_bound bound_summable
    bound_integrable h_lim).const_smul _,
end

open topological_space

/-- Interval integrals commute with countable sums, when the supremum norms are summable (a
special case of the dominated convergence theorem). -/
lemma has_sum_interval_integral_of_summable_norm [countable ι] {f : ι → C(ℝ, E)}
  (hf_sum : summable (λ i : ι, ‖(f i).restrict (⟨uIcc a b, is_compact_uIcc⟩ : compacts ℝ)‖)) :
  has_sum (λ i : ι, ∫_{a}^{b} x, f i x) (∫_{a}^{b} x, (∑' i : ι, f i x)) :=
begin
  refine has_sum_integral_of_dominated_convergence
    (λ i (x : ℝ), ‖(f i).restrict ↑(⟨uIcc a b, is_compact_uIcc⟩ : compacts ℝ)‖)
    (λ i, (map_continuous $ f i).ae_strongly_measurable)
    (λ i, ae_of_all _ (λ x hx, ((f i).restrict ↑(⟨uIcc a b, is_compact_uIcc⟩ :
      compacts ℝ)).norm_coe_le_norm ⟨x, ⟨hx.1.le, hx.2⟩⟩))
    (ae_of_all _ (λ x hx, hf_sum))
    interval_integrable_const
    (ae_of_all _ (λ x hx, summable.has_sum _)),
  -- next line is slow, & doesn't work with "exact" in place of "apply" -- ?
  apply continuous_map.summable_apply (summable_of_summable_norm hf_sum) ⟨x, ⟨hx.1.le, hx.2⟩⟩,
end

lemma tsum_interval_integral_eq_of_summable_norm [countable ι] {f : ι → C(ℝ, E)}
  (hf_sum : summable (λ i : ι, ‖(f i).restrict (⟨uIcc a b, is_compact_uIcc⟩ : compacts ℝ)‖)) :
  ∑' (i : ι), ∫_{a}^{b} x, f i x = ∫_{a}^{b} x, (∑' i : ι, f i x) :=
(has_sum_interval_integral_of_summable_norm hf_sum).tsum_eq

variables {X : Type*} [topological_space X] [first_countable_topology X]

/-- Continuity of interval integral with respect to a parameter, at a point within a set.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀` within `s` and at `x₀`, and assume it is bounded by a function integrable
  on `[a, b]` independent of `x` in a neighborhood of `x₀` within `s`. If `(λ x, F x t)`
  is continuous at `x₀` within `s` for almost every `t` in `[a, b]`
  then the same holds for `(λ x, ∫_{a}^{b} t, F x t ∂μ) s x₀`. -/
lemma continuous_within_at_of_dominated_interval
  {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ} {s : set X}
  (hF_meas : ∀ᶠ x in 𝓝[s] x₀, ae_strongly_measurable (F x) (μ.restrict $ Ι a b))
  (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → continuous_within_at (λ x, F x t) s x₀) :
  continuous_within_at (λ x, ∫_{a}^{b} t, F x t ∂μ) s x₀ :=
tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter at a point.
  Given `F : X → ℝ → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀`, and assume it is bounded by a function integrable on
  `[a, b]` independent of `x` in a neighborhood of `x₀`. If `(λ x, F x t)`
  is continuous at `x₀` for almost every `t` in `[a, b]`
  then the same holds for `(λ x, ∫_{a}^{b} t, F x t ∂μ) s x₀`. -/
lemma continuous_at_of_dominated_interval
  {F : X → ℝ → E} {x₀ : X} {bound : ℝ → ℝ} {a b : ℝ}
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_strongly_measurable (F x) (μ.restrict $ Ι a b))
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → continuous_at (λ x, F x t) x₀) :
  continuous_at (λ x, ∫_{a}^{b} t, F x t ∂μ) x₀ :=
tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter.
  Given `F : X → ℝ → E`, assume each `F x` is ae-measurable on `[a, b]`,
  and assume it is bounded by a function integrable on `[a, b]` independent of `x`.
  If `(λ x, F x t)` is continuous for almost every `t` in `[a, b]`
  then the same holds for `(λ x, ∫_{a}^{b} t, F x t ∂μ) s x₀`. -/
lemma continuous_of_dominated_interval {F : X → ℝ → E} {bound : ℝ → ℝ} {a b : ℝ}
  (hF_meas : ∀ x, ae_strongly_measurable (F x) $ μ.restrict $ Ι a b)
  (h_bound : ∀ x, ∀ᵐ t ∂μ, t ∈ Ι a b → ‖F x t‖ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → continuous (λ x, F x t)) :
  continuous (λ x, ∫_{a}^{b} t, F x t ∂μ) :=
continuous_iff_continuous_at.mpr (λ x₀, continuous_at_of_dominated_interval
  (eventually_of_forall hF_meas) (eventually_of_forall h_bound) bound_integrable $ h_cont.mono $
  λ x himp hx, (himp hx).continuous_at)

end order_closed_topology

section continuous_primitive
open topological_space

variables {a b b₀ b₁ b₂ : ℝ} {μ : measure ℝ} {f g : ℝ → E}

lemma continuous_within_at_primitive (hb₀ : μ {b₀} = 0)
  (h_int : interval_integrable f μ (min a b₁) (max a b₂)) :
  continuous_within_at (λ b, ∫_{a}^{b} x, f x ∂ μ) (Icc b₁ b₂) b₀ :=
begin
  by_cases h₀ : b₀ ∈ Icc b₁ b₂,
  { have h₁₂ : b₁ ≤ b₂ := h₀.1.trans h₀.2,
    have min₁₂ : min b₁ b₂ = b₁ := min_eq_left h₁₂,
    have h_int' : ∀ {x}, x ∈ Icc b₁ b₂ → interval_integrable f μ b₁ x,
    { rintros x ⟨h₁, h₂⟩,
      apply h_int.mono_set,
      apply uIcc_subset_uIcc,
      { exact ⟨min_le_of_left_le (min_le_right a b₁),
                h₁.trans (h₂.trans $ le_max_of_le_right $ le_max_right _ _)⟩ },
      { exact ⟨min_le_of_left_le $ (min_le_right _ _).trans h₁,
                le_max_of_le_right $ h₂.trans $ le_max_right _ _⟩ } },
    have : ∀ b ∈ Icc b₁ b₂, ∫_{a}^{b} x, f x ∂μ = ∫_{a}^{b₁} x, f x ∂μ + ∫_{b₁}^{b} x, f x ∂μ,
    { rintros b ⟨h₁, h₂⟩,
      rw ← integral_add_adjacent_intervals _ (h_int' ⟨h₁, h₂⟩),
      apply h_int.mono_set,
      apply uIcc_subset_uIcc,
      { exact ⟨min_le_of_left_le (min_le_left a b₁), le_max_of_le_right (le_max_left _ _)⟩ },
      { exact ⟨min_le_of_left_le (min_le_right _ _),
                le_max_of_le_right (h₁.trans $ h₂.trans (le_max_right a b₂))⟩ } },
    apply continuous_within_at.congr _ this (this _ h₀), clear this,
    refine continuous_within_at_const.add _,
    have : (λ b, ∫_{b₁}^{b} x, f x ∂μ) =ᶠ[𝓝[Icc b₁ b₂] b₀]
            λ b, ∫_{b₁}^{b₂} x, indicator {x | x ≤ b} f x ∂ μ,
    { apply eventually_eq_of_mem self_mem_nhds_within,
      exact λ b b_in, (integral_indicator b_in).symm },

    apply continuous_within_at.congr_of_eventually_eq _ this (integral_indicator h₀).symm,
    have : interval_integrable (λ x, ‖f x‖) μ b₁ b₂,
      from interval_integrable.norm (h_int' $ right_mem_Icc.mpr h₁₂),
    refine continuous_within_at_of_dominated_interval _ _ this _ ; clear this,
    { apply eventually.mono (self_mem_nhds_within),
      intros x hx,
      erw [ae_strongly_measurable_indicator_iff, measure.restrict_restrict, Iic_inter_Ioc_of_le],
      { rw min₁₂,
        exact (h_int' hx).1.ae_strongly_measurable },
      { exact le_max_of_le_right hx.2 },
      exacts [measurable_set_Iic, measurable_set_Iic] },
    { refine eventually_of_forall (λ x, eventually_of_forall (λ t, _)),
      dsimp [indicator],
      split_ifs ; simp },
    { have : ∀ᵐ t ∂μ, t < b₀ ∨ b₀ < t,
      { apply eventually.mono (compl_mem_ae_iff.mpr hb₀),
        intros x hx,
        exact ne.lt_or_lt hx },
      apply this.mono,
      rintros x₀ (hx₀ | hx₀) -,
      { have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : ℝ | t ≤ x}.indicator f x₀ = f x₀,
        { apply mem_nhds_within_of_mem_nhds,
          apply eventually.mono (Ioi_mem_nhds hx₀),
          intros x hx,
          simp [hx.le] },
        apply continuous_within_at_const.congr_of_eventually_eq  this,
        simp [hx₀.le] },
      { have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : ℝ | t ≤ x}.indicator f x₀ = 0,
        { apply mem_nhds_within_of_mem_nhds,
          apply eventually.mono (Iio_mem_nhds hx₀),
          intros x hx,
          simp [hx] },
        apply continuous_within_at_const.congr_of_eventually_eq this,
        simp [hx₀] } } },
  { apply continuous_within_at_of_not_mem_closure,
    rwa [closure_Icc] }
end

lemma continuous_on_primitive [has_no_atoms μ] (h_int : integrable_on f (Icc a b) μ) :
  continuous_on (λ x, ∫ t in Ioc a x, f t ∂ μ) (Icc a b) :=
begin
  by_cases h : a ≤ b,
  { have : ∀ x ∈ Icc a b, ∫ t in Ioc a x, f t ∂μ = ∫_{a}^{x} t, f t ∂μ,
    { intros x x_in,
      simp_rw [← uIoc_of_le h, integral_of_le x_in.1] },
    rw continuous_on_congr this,
    intros x₀ hx₀,
    refine continuous_within_at_primitive (measure_singleton x₀) _,
    simp only [interval_integrable_iff_integrable_Ioc_of_le, min_eq_left, max_eq_right, h],
    exact h_int.mono Ioc_subset_Icc_self le_rfl },
  { rw Icc_eq_empty h,
    exact continuous_on_empty _ },
end

lemma continuous_on_primitive_Icc [has_no_atoms μ] (h_int : integrable_on f (Icc a b) μ) :
  continuous_on (λ x, ∫ t in Icc a x, f t ∂ μ) (Icc a b) :=
begin
  rw show (λ x, ∫ t in Icc a x, f t ∂μ) = λ x, ∫ t in Ioc a x, f t ∂μ,
    by { ext x, exact integral_Icc_eq_integral_Ioc },
  exact continuous_on_primitive h_int
end

/-- Note: this assumes that `f` is `interval_integrable`, in contrast to some other lemmas here. -/
lemma continuous_on_primitive_interval' [has_no_atoms μ]
  (h_int : interval_integrable f μ b₁ b₂) (ha : a ∈ [b₁, b₂]) :
  continuous_on (λ b, ∫_{a}^{b} x, f x ∂ μ) [b₁, b₂] :=
begin
  intros b₀ hb₀,
  refine continuous_within_at_primitive (measure_singleton _) _,
  rw [min_eq_right ha.1, max_eq_right ha.2],
  simpa [interval_integrable_iff, uIoc] using h_int,
end

lemma continuous_on_primitive_interval [has_no_atoms μ]
  (h_int : integrable_on f (uIcc a b) μ) :
  continuous_on (λ x, ∫_{a}^{x} t, f t ∂ μ) (uIcc a b) :=
continuous_on_primitive_interval' h_int.interval_integrable left_mem_uIcc

lemma continuous_on_primitive_interval_left [has_no_atoms μ]
  (h_int : integrable_on f (uIcc a b) μ) :
  continuous_on (λ x, ∫_{x}^{b} t, f t ∂ μ) (uIcc a b) :=
begin
  rw uIcc_comm a b at h_int ⊢,
  simp only [integral_symm b],
  exact (continuous_on_primitive_interval h_int).neg,
end

variables [has_no_atoms μ]

lemma continuous_primitive (h_int : ∀ a b, interval_integrable f μ a b) (a : ℝ) :
  continuous (λ b, ∫_{a}^{b} x, f x ∂ μ) :=
begin
  rw continuous_iff_continuous_at,
  intro b₀,
  cases exists_lt b₀ with b₁ hb₁,
  cases exists_gt b₀ with b₂ hb₂,
  apply continuous_within_at.continuous_at _ (Icc_mem_nhds hb₁ hb₂),
  exact continuous_within_at_primitive (measure_singleton b₀) (h_int _ _)
end

lemma _root_.measure_theory.integrable.continuous_primitive (h_int : integrable f μ) (a : ℝ) :
  continuous (λ b, ∫_{a}^{b} x, f x ∂ μ) :=
continuous_primitive (λ _ _, h_int.interval_integrable) a

end continuous_primitive

section

variables {f g : ℝ → ℝ} {a b : ℝ} {μ : measure ℝ}

lemma integral_eq_zero_iff_of_le_of_nonneg_ae (hab : a ≤ b)
  (hf : 0 ≤ᵐ[μ.restrict (Ioc a b)] f) (hfi : interval_integrable f μ a b) :
  ∫_{a}^{b} x, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b)] 0 :=
by rw [integral_of_le hab, integral_eq_zero_iff_of_nonneg_ae hf hfi.1]

lemma integral_eq_zero_iff_of_nonneg_ae
  (hf : 0 ≤ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] f) (hfi : interval_integrable f μ a b) :
  ∫_{a}^{b} x, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] 0 :=
begin
  cases le_total a b with hab hab;
    simp only [Ioc_eq_empty hab.not_lt, empty_union, union_empty] at hf ⊢,
  { exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi },
  { rw [integral_symm, neg_eq_zero, integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi.symm] }
end

/-- If `f` is nonnegative and integrable on the unordered interval `set.uIoc a b`, then its
integral over `a..b` is positive if and only if `a < b` and the measure of
`function.support f ∩ set.Ioc a b` is positive. -/
lemma integral_pos_iff_support_of_nonneg_ae'
  (hf : 0 ≤ᵐ[μ.restrict (Ι a b)] f) (hfi : interval_integrable f μ a b) :
  0 < ∫_{a}^{b} x, f x ∂μ ↔ a < b ∧ 0 < μ (support f ∩ Ioc a b) :=
begin
  cases lt_or_le a b with hab hba,
  { rw uIoc_of_le hab.le at hf,
    simp only [hab, true_and, integral_of_le hab.le,
      set_integral_pos_iff_support_of_nonneg_ae hf hfi.1] },
  { suffices : ∫_{a}^{b} x, f x ∂μ ≤ 0, by simp only [this.not_lt, hba.not_lt, false_and],
    rw [integral_of_ge hba, neg_nonpos],
    rw [uIoc_swap, uIoc_of_le hba] at hf,
    exact integral_nonneg_of_ae hf }
end

/-- If `f` is nonnegative a.e.-everywhere and it is integrable on the unordered interval
`set.uIoc a b`, then its integral over `a..b` is positive if and only if `a < b` and the
measure of `function.support f ∩ set.Ioc a b` is positive. -/
lemma integral_pos_iff_support_of_nonneg_ae (hf : 0 ≤ᵐ[μ] f) (hfi : interval_integrable f μ a b) :
  0 < ∫_{a}^{b} x, f x ∂μ ↔ a < b ∧ 0 < μ (support f ∩ Ioc a b) :=
integral_pos_iff_support_of_nonneg_ae' (ae_mono measure.restrict_le_self hf) hfi

/-- If `f : ℝ → ℝ` is integrable on `(a, b]` for real numbers `a < b`, and positive on the interior
of the interval, then its integral over `a..b` is strictly positive. -/
lemma interval_integral_pos_of_pos_on {f : ℝ → ℝ} {a b : ℝ}
  (hfi : interval_integrable f volume a b) (hpos : ∀ (x : ℝ), x ∈ Ioo a b → 0 < f x) (hab : a < b) :
  0 < ∫_{a}^{b} x, f x :=
begin
  have hsupp : Ioo a b ⊆ support f ∩ Ioc a b :=
    λ x hx, ⟨mem_support.mpr (hpos x hx).ne', Ioo_subset_Ioc_self hx⟩,
  have h₀ : 0 ≤ᵐ[volume.restrict (uIoc a b)] f,
  { rw [eventually_le, uIoc_of_le hab.le],
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc _,
    exact (ae_restrict_iff' measurable_set_Ioo).mpr (ae_of_all _ (λ x hx, (hpos x hx).le)) },
  rw integral_pos_iff_support_of_nonneg_ae' h₀ hfi,
  exact ⟨hab, ((measure.measure_Ioo_pos _).mpr hab).trans_le (measure_mono hsupp)⟩,
end

/-- If `f : ℝ → ℝ` is strictly positive everywhere, and integrable on `(a, b]` for real numbers
`a < b`, then its integral over `a..b` is strictly positive. (See `interval_integral_pos_of_pos_on`
for a version only assuming positivity of `f` on `(a, b)` rather than everywhere.) -/
lemma interval_integral_pos_of_pos {f : ℝ → ℝ} {a b : ℝ}
  (hfi : interval_integrable f measure_space.volume a b) (hpos : ∀ x, 0 < f x) (hab : a < b) :
  0 < ∫_{a}^{b} x, f x :=
interval_integral_pos_of_pos_on hfi (λ x hx, hpos x) hab

/-- If `f` and `g` are two functions that are interval integrable on `a..b`, `a ≤ b`,
`f x ≤ g x` for a.e. `x ∈ set.Ioc a b`, and `f x < g x` on a subset of `set.Ioc a b`
of nonzero measure, then `∫_{a}^{b} x, f x ∂μ < ∫_{a}^{b} x, g x ∂μ`. -/
lemma integral_lt_integral_of_ae_le_of_measure_set_of_lt_ne_zero (hab : a ≤ b)
  (hfi : interval_integrable f μ a b) (hgi : interval_integrable g μ a b)
  (hle : f ≤ᵐ[μ.restrict (Ioc a b)] g) (hlt : μ.restrict (Ioc a b) {x | f x < g x} ≠ 0) :
  ∫_{a}^{b} x, f x ∂μ < ∫_{a}^{b} x, g x ∂μ :=
begin
  rw [← sub_pos, ← integral_sub hgi hfi, integral_of_le hab,
    measure_theory.integral_pos_iff_support_of_nonneg_ae],
  { refine pos_iff_ne_zero.2 (mt (measure_mono_null _) hlt),
    exact λ x hx, (sub_pos.2 hx).ne' },
  exacts [hle.mono (λ x, sub_nonneg.2), hgi.1.sub hfi.1]
end

/-- If `f` and `g` are continuous on `[a, b]`, `a < b`, `f x ≤ g x` on this interval, and
`f c < g c` at some point `c ∈ [a, b]`, then `∫_{a}^{b} x, f x < ∫_{a}^{b} x, g x`. -/
lemma integral_lt_integral_of_continuous_on_of_le_of_exists_lt {f g : ℝ → ℝ} {a b : ℝ}
  (hab : a < b) (hfc : continuous_on f (Icc a b)) (hgc : continuous_on g (Icc a b))
  (hle : ∀ x ∈ Ioc a b, f x ≤ g x) (hlt : ∃ c ∈ Icc a b, f c < g c) :
  ∫_{a}^{b} x, f x < ∫_{a}^{b} x, g x :=
begin
  refine integral_lt_integral_of_ae_le_of_measure_set_of_lt_ne_zero hab.le
    (hfc.interval_integrable_of_Icc hab.le) (hgc.interval_integrable_of_Icc hab.le)
    ((ae_restrict_mem measurable_set_Ioc).mono hle) _,
  contrapose! hlt,
  have h_eq : f =ᵐ[volume.restrict (Ioc a b)] g,
  { simp only [← not_le, ← ae_iff] at hlt,
    exact eventually_le.antisymm ((ae_restrict_iff' measurable_set_Ioc).2 $
      eventually_of_forall hle) hlt },
  simp only [measure.restrict_congr_set Ioc_ae_eq_Icc] at h_eq,
  exact λ c hc, (measure.eq_on_Icc_of_ae_eq volume hab.ne h_eq hfc hgc hc).ge
end

lemma integral_nonneg_of_ae_restrict (hab : a ≤ b) (hf : 0 ≤ᵐ[μ.restrict (Icc a b)] f) :
  0 ≤ (∫_{a}^{b} u, f u ∂μ) :=
let H := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hf in
by simpa only [integral_of_le hab] using set_integral_nonneg_of_ae_restrict H

lemma integral_nonneg_of_ae (hab : a ≤ b) (hf : 0 ≤ᵐ[μ] f) :
  0 ≤ (∫_{a}^{b} u, f u ∂μ) :=
integral_nonneg_of_ae_restrict hab $ ae_restrict_of_ae hf

lemma integral_nonneg_of_forall (hab : a ≤ b) (hf : ∀ u, 0 ≤ f u) :
  0 ≤ (∫_{a}^{b} u, f u ∂μ) :=
integral_nonneg_of_ae hab $ eventually_of_forall hf

lemma integral_nonneg (hab : a ≤ b) (hf : ∀ u, u ∈ Icc a b → 0 ≤ f u) :
  0 ≤ (∫_{a}^{b} u, f u ∂μ) :=
integral_nonneg_of_ae_restrict hab $ (ae_restrict_iff' measurable_set_Icc).mpr $ ae_of_all μ hf

lemma abs_integral_le_integral_abs (hab : a ≤ b) :
  |∫_{a}^{b} x, f x ∂μ| ≤ ∫_{a}^{b} x, |f x| ∂μ :=
by simpa only [← real.norm_eq_abs] using norm_integral_le_integral_norm hab

section mono

variables (hab : a ≤ b) (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b)

include hab hf hg

lemma integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict (Icc a b)] g) :
  ∫_{a}^{b} u, f u ∂μ ≤ ∫_{a}^{b} u, g u ∂μ :=
let H := h.filter_mono $ ae_mono $ measure.restrict_mono Ioc_subset_Icc_self $ le_refl μ in
by simpa only [integral_of_le hab] using set_integral_mono_ae_restrict hf.1 hg.1 H

lemma integral_mono_ae (h : f ≤ᵐ[μ] g) :
  ∫_{a}^{b} u, f u ∂μ ≤ ∫_{a}^{b} u, g u ∂μ :=
by simpa only [integral_of_le hab] using set_integral_mono_ae hf.1 hg.1 h

lemma integral_mono_on (h : ∀ x ∈ Icc a b, f x ≤ g x) :
  ∫_{a}^{b} u, f u ∂μ ≤ ∫_{a}^{b} u, g u ∂μ :=
let H := λ x hx, h x $ Ioc_subset_Icc_self hx in
by simpa only [integral_of_le hab] using set_integral_mono_on hf.1 hg.1 measurable_set_Ioc H

lemma integral_mono (h : f ≤ g) :
  ∫_{a}^{b} u, f u ∂μ ≤ ∫_{a}^{b} u, g u ∂μ :=
integral_mono_ae hab hf hg $ ae_of_all _ h

omit hg hab

lemma integral_mono_interval {c d} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
  (hf : 0 ≤ᵐ[μ.restrict (Ioc c d)] f) (hfi : interval_integrable f μ c d):
  ∫_{a}^{b} x, f x ∂μ ≤ ∫_{c}^{d} x, f x ∂μ :=
begin
  rw [integral_of_le hab, integral_of_le (hca.trans (hab.trans hbd))],
  exact set_integral_mono_set hfi.1 hf (Ioc_subset_Ioc hca hbd).eventually_le
end

lemma abs_integral_mono_interval {c d } (h : Ι a b ⊆ Ι c d)
  (hf : 0 ≤ᵐ[μ.restrict (Ι c d)] f) (hfi : interval_integrable f μ c d) :
  |∫_{a}^{b} x, f x ∂μ| ≤ |∫_{c}^{d} x, f x ∂μ| :=
have hf' : 0 ≤ᵐ[μ.restrict (Ι a b)] f, from ae_mono (measure.restrict_mono h le_rfl) hf,
calc |∫_{a}^{b} x, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| : abs_integral_eq_abs_integral_uIoc f
... = ∫ x in Ι a b, f x ∂μ : abs_of_nonneg (measure_theory.integral_nonneg_of_ae hf')
... ≤ ∫ x in Ι c d, f x ∂μ : set_integral_mono_set hfi.def hf h.eventually_le
... ≤ |∫ x in Ι c d, f x ∂μ| : le_abs_self _
... = |∫_{c}^{d} x, f x ∂μ| : (abs_integral_eq_abs_integral_uIoc f).symm

end mono

end

section has_sum
variables {μ : measure ℝ} {f : ℝ → E}

lemma _root_.measure_theory.integrable.has_sum_interval_integral (hfi : integrable f μ) (y : ℝ) :
  has_sum (λ (n : ℤ), ∫_{(y + n)}^{(y + n + 1)} x, f x ∂μ) (∫ x, f x ∂μ) :=
begin
  simp_rw integral_of_le (le_add_of_nonneg_right zero_le_one),
  rw [←integral_univ, ←Union_Ioc_add_int_cast y],
  exact has_sum_integral_Union (λ i, measurable_set_Ioc) (pairwise_disjoint_Ioc_add_int_cast y)
    hfi.integrable_on,
end

lemma _root_.measure_theory.integrable.has_sum_interval_integral_comp_add_int
  (hfi : integrable f) :
  has_sum (λ (n : ℤ), ∫_{0}^{1} x, f (x + n)) (∫ x, f x) :=
begin
  convert hfi.has_sum_interval_integral 0 using 2,
  ext1 n,
  rw [integral_comp_add_right, zero_add, add_comm],
end

end has_sum

end interval_integral
