/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import measure_theory.ess_sup
import measure_theory.ae_eq_fun
import analysis.mean_inequalities

/-!
# ℒp space and Lp space

This file describes properties of almost everywhere measurable functions with finite seminorm,
denoted by `snorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`, `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for
`0 < p < ∞` and `ess_sup ∥f∥ μ` for `p=∞`.

The Prop-valued `mem_ℒp f p μ` states that a function `f : α → E` has finite seminorm.
The space `Lp α E p μ` is the subtype of elements of `α →ₘ[μ] E` (see ae_eq_fun) such that
`snorm f p μ` is finite. For `1 ≤ p`, `snorm` defines a norm and `Lp` is a metric space.

TODO: prove that Lp is complete.

## Main definitions

* `snorm' f p μ` : `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a  measurable
  space and `F` is a normed group.
* `snorm_ess_sup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `ess_sup ∥f∥ μ`.
* `snorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `snorm' f p μ`
  for `0 < p < ∞` and to `snorm_ess_sup f μ` for `p = ∞`.

* `mem_ℒp f p μ` : property that the function `f` is almost everywhere measurable and has finite
  p-seminorm for measure `μ` (`snorm f p μ < ∞`)
* `Lp E p μ` : elements of `α →ₘ[μ] E` (see ae_eq_fun) such that `snorm f p μ` is finite. Defined
  as an `add_subgroup` of `α →ₘ[μ] E`.

Lipschitz functions vanishing at zero act by composition on `Lp`. We define this action, and prove
that it is continuous. In particular,
* `continuous_linear_map.comp_Lp` defines the action on `Lp` of a continuous linear map.
* `Lp.pos_part` is the positive part of an `Lp` function.
* `Lp.neg_part` is the negative part of an `Lp` function.

## Implementation

Since `Lp` is defined as an `add_subgroup`, dot notation does not work. Use `Lp.measurable f` to
say that the coercion of `f` to a genuine function is measurable, instead of the non-working
`f.measurable`.

To prove that two `Lp` elements are equal, it suffices to show that their coercions to functions
coincide almost everywhere (this is registered as an `ext` rule). This can often be done using
`filter_upwards`. For instance, a proof from first principles that `f + (g + h) = (f + g) + h`
could read (in the `Lp` namespace)
```
example (f g h : Lp E p μ) : (f + g) + h = f + (g + h) :=
begin
  ext1,
  filter_upwards [coe_fn_add (f + g) h, coe_fn_add f g, coe_fn_add f (g + h), coe_fn_add g h],
  assume a ha1 ha2 ha3 ha4,
  simp only [ha1, ha2, ha3, ha4, add_assoc],
end
```
The lemma `coe_fn_add` states that the coercion of `f + g` coincides almost everywhere with the sum
of the coercions of `f` and `g`. All such lemmas use `coe_fn` in their name, to distinguish the
function coercion from the coercion to almost everywhere defined functions.
-/

noncomputable theory
open topological_space measure_theory
open_locale nnreal ennreal big_operators

lemma fact_one_le_one_ennreal : fact ((1 : ℝ≥0∞) ≤ 1) := le_refl _

lemma fact_one_le_two_ennreal : fact ((1 : ℝ≥0∞) ≤ 2) :=
ennreal.coe_le_coe.2 (show (1 : nnreal) ≤ 2, by norm_num)

lemma fact_one_le_top_ennreal : fact ((1 : ℝ≥0∞) ≤ ∞) := le_top

local attribute [instance] fact_one_le_one_ennreal fact_one_le_two_ennreal fact_one_le_top_ennreal

variables {α E F G : Type*} [measurable_space α] {p : ℝ≥0∞} {q : ℝ} {μ : measure α}
  [measurable_space E] [normed_group E]
  [normed_group F] [normed_group G]

open_locale ennreal

namespace measure_theory

section ℒp

/-!
### ℒp seminorm

We define the ℒp seminorm, denoted by `snorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `snorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `snorm_ess_sup f μ`).

We also define a predicate `mem_ℒp f p μ`, requesting that a function is almost everywhere
measurable and has finite `snorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `snorm'` and `snorm_ess_sup` when it makes sense,
deduce it for `snorm`, and translate it in terms of `mem_ℒp`.
-/

section ℒp_space_definition

/-- `(∫ ∥f a∥^q ∂μ) ^ (1/q)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
def snorm' (f : α → F) (q : ℝ) (μ : measure α) : ℝ≥0∞ := (∫⁻ a, (nnnorm (f a))^q ∂μ) ^ (1/q)

/-- seminorm for `ℒ∞`, equal to the essential supremum of `∥f∥`. -/
def snorm_ess_sup (f : α → F) (μ : measure α) := ess_sup (λ x, (nnnorm (f x) : ℝ≥0∞)) μ

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ∥f a∥^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`ess_sup ∥f∥ μ` for `p = ∞`. -/
def snorm (f : α → F) (p : ℝ≥0∞) (μ : measure α) : ℝ≥0∞ :=
if p = 0 then 0 else (if p = ∞ then snorm_ess_sup f μ else snorm' f (ennreal.to_real p) μ)

lemma snorm_eq_snorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F} :
  snorm f p μ = snorm' f (ennreal.to_real p) μ :=
by simp [snorm, hp_ne_zero, hp_ne_top]

@[simp] lemma snorm_exponent_top {f : α → F} : snorm f ∞ μ = snorm_ess_sup f μ := by simp [snorm]

/-- The property that `f:α→E` is ae_measurable and `(∫ ∥f a∥^p ∂μ)^(1/p)` is finite if `p < ∞`, or
`ess_sup f < ∞` if `p = ∞`. -/
def mem_ℒp (f : α → E) (p : ℝ≥0∞) (μ : measure α) : Prop :=
ae_measurable f μ ∧ snorm f p μ < ∞

lemma mem_ℒp.ae_measurable {f : α → E} {p : ℝ≥0∞} {μ : measure α} (h : mem_ℒp f p μ) :
  ae_measurable f μ := h.1

lemma lintegral_rpow_nnnorm_eq_rpow_snorm' {f : α → F} (hq0_lt : 0 < q) :
  ∫⁻ a, (nnnorm (f a)) ^ q ∂μ = (snorm' f q μ) ^ q :=
begin
  rw [snorm', ←ennreal.rpow_mul, one_div, inv_mul_cancel, ennreal.rpow_one],
  exact (ne_of_lt hq0_lt).symm,
end

end ℒp_space_definition

section top

lemma mem_ℒp.snorm_lt_top {f : α → E} (hfp : mem_ℒp f p μ) : snorm f p μ < ∞ := hfp.2

lemma mem_ℒp.snorm_ne_top {f : α → E} (hfp : mem_ℒp f p μ) : snorm f p μ ≠ ∞ := ne_of_lt (hfp.2)

lemma lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top {f : α → F} (hq0_lt : 0 < q)
  (hfq : snorm' f q μ < ∞) :
  ∫⁻ a, (nnnorm (f a)) ^ q ∂μ < ∞ :=
begin
  rw lintegral_rpow_nnnorm_eq_rpow_snorm' hq0_lt,
  exact ennreal.rpow_lt_top_of_nonneg (le_of_lt hq0_lt) (ne_of_lt hfq),
end

end top

section zero

@[simp] lemma snorm'_exponent_zero {f : α → F} : snorm' f 0 μ = 1 :=
by rw [snorm', div_zero, ennreal.rpow_zero]

@[simp] lemma snorm_exponent_zero {f : α → F} : snorm f 0 μ = 0 :=
by simp [snorm]

lemma mem_ℒp_zero_iff_ae_measurable {f : α → E} : mem_ℒp f 0 μ ↔ ae_measurable f μ :=
by simp [mem_ℒp, snorm_exponent_zero]

@[simp] lemma snorm'_zero (hp0_lt : 0 < q) : snorm' (0 : α → F) q μ = 0 :=
by simp [snorm', hp0_lt]

@[simp] lemma snorm'_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) : snorm' (0 : α → F) q μ = 0 :=
begin
  cases le_or_lt 0 q with hq0 hq_neg,
  { exact snorm'_zero (lt_of_le_of_ne hq0 hq0_ne.symm), },
  { simp [snorm', ennreal.rpow_eq_zero_iff, hμ, hq_neg], },
end

@[simp] lemma snorm_ess_sup_zero : snorm_ess_sup (0 : α → F) μ = 0 :=
begin
  simp_rw [snorm_ess_sup, pi.zero_apply, nnnorm_zero, ennreal.coe_zero, ←ennreal.bot_eq_zero],
  exact ess_sup_const_bot,
end

@[simp] lemma snorm_zero : snorm (0 : α → F) p μ = 0 :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simp only [h_top, snorm_exponent_top, snorm_ess_sup_zero], },
  rw ←ne.def at h0,
  simp [snorm_eq_snorm' h0 h_top,
    ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩],
end

lemma zero_mem_ℒp : mem_ℒp (0 : α → E) p μ :=
⟨measurable_zero.ae_measurable, by { rw snorm_zero, exact ennreal.coe_lt_top, } ⟩

lemma snorm'_measure_zero_of_pos {f : α → F} (hq_pos : 0 < q) : snorm' f q 0 = 0 :=
by simp [snorm', hq_pos]

lemma snorm'_measure_zero_of_exponent_zero {f : α → F} : snorm' f 0 0 = 1 := by simp [snorm']

lemma snorm'_measure_zero_of_neg {f : α → F} (hq_neg : q < 0) : snorm' f q 0 = ∞ :=
by simp [snorm', hq_neg]

@[simp] lemma snorm_ess_sup_measure_zero {f : α → F} : snorm_ess_sup f 0 = 0 :=
by simp [snorm_ess_sup]

@[simp] lemma snorm_measure_zero {f : α → F} : snorm f p 0 = 0 :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simp [h_top], },
  rw ←ne.def at h0,
  simp [snorm_eq_snorm' h0 h_top, snorm',
    ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩],
end

end zero

section const

lemma snorm'_const (c : F) (hq_pos : 0 < q) :
  snorm' (λ x : α , c) q μ = (nnnorm c : ℝ≥0∞) * (μ set.univ) ^ (1/q) :=
begin
  rw [snorm', lintegral_const, @ennreal.mul_rpow_of_nonneg _ _ (1/q) (by simp [hq_pos.le])],
  congr,
  rw ←ennreal.rpow_mul,
  suffices hq_cancel : q * (1/q) = 1, by rw [hq_cancel, ennreal.rpow_one],
  rw [one_div, mul_inv_cancel (ne_of_lt hq_pos).symm],
end

lemma snorm'_const' [finite_measure μ] (c : F) (hc_ne_zero : c ≠ 0) (hq_ne_zero : q ≠ 0) :
  snorm' (λ x : α , c) q μ = (nnnorm c : ℝ≥0∞) * (μ set.univ) ^ (1/q) :=
begin
  rw [snorm', lintegral_const, ennreal.mul_rpow_of_ne_top _ (measure_ne_top μ set.univ)],
  { congr,
    rw ←ennreal.rpow_mul,
    suffices hp_cancel : q * (1/q) = 1, by rw [hp_cancel, ennreal.rpow_one],
    rw [one_div, mul_inv_cancel hq_ne_zero], },
  { rw [ne.def, ennreal.rpow_eq_top_iff, auto.not_or_eq, auto.not_and_eq, auto.not_and_eq],
    split,
    { left,
      rwa [ennreal.coe_eq_zero, nnnorm_eq_zero], },
    { exact or.inl ennreal.coe_ne_top, }, },
end

lemma snorm_ess_sup_const (c : F) (hμ : μ ≠ 0) :
  snorm_ess_sup (λ x : α, c) μ = (nnnorm c : ℝ≥0∞) :=
by rw [snorm_ess_sup, ess_sup_const _ hμ]

lemma snorm'_const_of_probability_measure (c : F) (hq_pos : 0 < q) [probability_measure μ] :
  snorm' (λ x : α , c) q μ = (nnnorm c : ℝ≥0∞) :=
by simp [snorm'_const c hq_pos, measure_univ]

lemma snorm_const (c : F) (h0 : p ≠ 0) (hμ : μ ≠ 0) :
  snorm (λ x : α , c) p μ = (nnnorm c : ℝ≥0∞) * (μ set.univ) ^ (1/(ennreal.to_real p)) :=
begin
  by_cases h_top : p = ∞,
  { simp [h_top, snorm_ess_sup_const c hμ], },
  simp [snorm_eq_snorm' h0 h_top, snorm'_const,
    ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩],
end

lemma snorm_const' (c : F) (h0 : p ≠ 0) (h_top: p ≠ ∞) :
  snorm (λ x : α , c) p μ = (nnnorm c : ℝ≥0∞) * (μ set.univ) ^ (1/(ennreal.to_real p)) :=
begin
  simp [snorm_eq_snorm' h0 h_top, snorm'_const,
    ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩],
end

lemma mem_ℒp_const (c : E) [finite_measure μ] : mem_ℒp (λ a:α, c) p μ :=
begin
  refine ⟨measurable_const.ae_measurable, _⟩,
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases hμ : μ = 0,
  { simp [hμ], },
  rw snorm_const c h0 hμ,
  refine ennreal.mul_lt_top ennreal.coe_lt_top _,
  refine ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ set.univ),
  simp,
end

end const

lemma snorm'_mono_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ ∥g x∥) :
  snorm' f q μ ≤ snorm' g q μ :=
begin
  rw [snorm'],
  refine ennreal.rpow_le_rpow _ (one_div_nonneg.2 hq),
  refine lintegral_mono_ae (h.mono $ λ x hx, _),
  exact ennreal.rpow_le_rpow (ennreal.coe_le_coe.2 hx) hq
end

lemma snorm'_congr_norm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ∥f x∥ = ∥g x∥) :
  snorm' f q μ = snorm' g q μ :=
begin
  have : (λ x, (nnnorm (f x) ^ q : ℝ≥0∞)) =ᵐ[μ] (λ x, nnnorm (g x) ^ q),
    from hfg.mono (λ x hx, by { simp only [← coe_nnnorm, nnreal.coe_eq] at hx, simp [hx] }),
  simp only [snorm', lintegral_congr_ae this]
end

lemma snorm'_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm' f q μ = snorm' g q μ :=
snorm'_congr_norm_ae (hfg.fun_comp _)

lemma snorm_ess_sup_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) :
  snorm_ess_sup f μ = snorm_ess_sup g μ :=
ess_sup_congr_ae (hfg.fun_comp (coe ∘ nnnorm))

lemma snorm_mono_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ ∥g x∥) :
  snorm f p μ ≤ snorm g p μ :=
begin
  simp only [snorm],
  split_ifs,
  { exact le_rfl },
  { refine ess_sup_mono_ae (h.mono $ λ x hx, _),
    exact_mod_cast hx },
  { exact snorm'_mono_ae ennreal.to_real_nonneg h }
end

lemma snorm_congr_norm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ∥f x∥ = ∥g x∥) :
  snorm f p μ = snorm g p μ :=
le_antisymm (snorm_mono_ae $ filter.eventually_eq.le hfg)
  (snorm_mono_ae $ (filter.eventually_eq.symm hfg).le)

@[simp] lemma snorm_norm (f : α → F) : snorm (λ x, ∥f x∥) p μ = snorm f p μ :=
snorm_congr_norm_ae $ filter.eventually_of_forall $ λ x, norm_norm _

lemma snorm_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm f p μ = snorm g p μ :=
snorm_congr_norm_ae $ hfg.mono (λ x hx, hx ▸ rfl)

lemma mem_ℒp_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) : mem_ℒp f p μ ↔ mem_ℒp g p μ :=
by simp only [mem_ℒp, snorm_congr_ae hfg, ae_measurable_congr hfg]

lemma mem_ℒp.ae_eq {f g : α → E} (hfg : f =ᵐ[μ] g) (hf_Lp : mem_ℒp f p μ) : mem_ℒp g p μ :=
(mem_ℒp_congr_ae hfg).1 hf_Lp

lemma mem_ℒp.of_le [measurable_space F] {f : α → E} {g : α → F}
  (hg : mem_ℒp g p μ) (hf : ae_measurable f μ) (hfg : ∀ᵐ x ∂μ, ∥f x∥ ≤ ∥g x∥) : mem_ℒp f p μ :=
⟨hf, (snorm_mono_ae hfg).trans_lt hg.snorm_lt_top⟩

section opens_measurable_space
variable [opens_measurable_space E]

lemma mem_ℒp.norm {f : α → E} (h : mem_ℒp f p μ) : mem_ℒp (λ x, ∥f x∥) p μ :=
h.of_le h.ae_measurable.norm (filter.eventually_of_forall (λ x, by simp))

lemma snorm'_eq_zero_of_ae_zero {f : α → F} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0) :
  snorm' f q μ = 0 :=
by rw [snorm'_congr_ae hf_zero, snorm'_zero hq0_lt]

lemma snorm'_eq_zero_of_ae_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) {f : α → F} (hf_zero : f =ᵐ[μ] 0) :
  snorm' f q μ = 0 :=
by rw [snorm'_congr_ae hf_zero, snorm'_zero' hq0_ne hμ]

lemma ae_eq_zero_of_snorm'_eq_zero {f : α → E} (hq0 : 0 ≤ q) (hf : ae_measurable f μ)
  (h : snorm' f q μ = 0) : f =ᵐ[μ] 0 :=
begin
  rw [snorm', ennreal.rpow_eq_zero_iff] at h,
  cases h,
  { rw lintegral_eq_zero_iff' hf.nnnorm.ennreal_coe.ennreal_rpow_const at h,
    refine h.left.mono (λ x hx, _),
    rw [pi.zero_apply, ennreal.rpow_eq_zero_iff] at hx,
    cases hx,
    { cases hx with hx _,
      rwa [←ennreal.coe_zero, ennreal.coe_eq_coe, nnnorm_eq_zero] at hx, },
    { exact absurd hx.left ennreal.coe_ne_top, }, },
  { exfalso,
    rw [one_div, inv_lt_zero] at h,
    exact hq0.not_lt h.right },
end

lemma snorm'_eq_zero_iff (hq0_lt : 0 < q) {f : α → E} (hf : ae_measurable f μ) :
  snorm' f q μ = 0 ↔ f =ᵐ[μ] 0 :=
⟨ae_eq_zero_of_snorm'_eq_zero (le_of_lt hq0_lt) hf, snorm'_eq_zero_of_ae_zero hq0_lt⟩

lemma coe_nnnorm_ae_le_snorm_ess_sup (f : α → F) (μ : measure α) :
  ∀ᵐ x ∂μ, (nnnorm (f x) : ℝ≥0∞) ≤ snorm_ess_sup f μ :=
ennreal.ae_le_ess_sup (λ x, (nnnorm (f x) : ℝ≥0∞))

@[simp] lemma snorm_ess_sup_eq_zero_iff {f : α → F} : snorm_ess_sup f μ = 0 ↔ f =ᵐ[μ] 0 :=
by simp [filter.eventually_eq, snorm_ess_sup]

lemma snorm_eq_zero_iff {f : α → E} (hf : ae_measurable f μ) (h0 : p ≠ 0) :
  snorm f p μ = 0 ↔ f =ᵐ[μ] 0 :=
begin
  by_cases h_top : p = ∞,
  { rw [h_top, snorm_exponent_top, snorm_ess_sup_eq_zero_iff], },
  rw snorm_eq_snorm' h0 h_top,
  exact snorm'_eq_zero_iff
    (ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩) hf,
end

end opens_measurable_space

@[simp] lemma snorm'_neg {f : α → F} : snorm' (-f) q μ = snorm' f q μ := by simp [snorm']

@[simp] lemma snorm_neg {f : α → F} : snorm (-f) p μ = snorm f p μ :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simp [h_top, snorm_ess_sup], },
  simp [snorm_eq_snorm' h0 h_top],
end

section borel_space
variable [borel_space E]

lemma mem_ℒp.neg {f : α → E} (hf : mem_ℒp f p μ) : mem_ℒp (-f) p μ :=
⟨ae_measurable.neg hf.1, by simp [hf.right]⟩

lemma snorm'_le_snorm'_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q)
  {f : α → E} (hf : ae_measurable f μ) :
  snorm' f p μ ≤ snorm' f q μ * (μ set.univ) ^ (1/p - 1/q) :=
begin
  have hq0_lt : 0 < q, from lt_of_lt_of_le hp0_lt hpq,
  by_cases hpq_eq : p = q,
  { rw [hpq_eq, sub_self, ennreal.rpow_zero, mul_one],
    exact le_refl _, },
  have hpq : p < q, from lt_of_le_of_ne hpq hpq_eq,
  let g := λ a : α, (1 : ℝ≥0∞),
  have h_rw : ∫⁻ a, ↑(nnnorm (f a))^p ∂ μ = ∫⁻ a, (nnnorm (f a) * (g a))^p ∂ μ,
  from lintegral_congr (λ a, by simp),
  repeat {rw snorm'},
  rw h_rw,
  let r := p * q / (q - p),
  have hpqr : 1/p = 1/q + 1/r,
  { field_simp [(ne_of_lt hp0_lt).symm,
      (ne_of_lt hq0_lt).symm],
    ring, },
  calc (∫⁻ (a : α), (↑(nnnorm (f a)) * g a) ^ p ∂μ) ^ (1/p)
      ≤ (∫⁻ (a : α), ↑(nnnorm (f a)) ^ q ∂μ) ^ (1/q) * (∫⁻ (a : α), (g a) ^ r ∂μ) ^ (1/r) :
    ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.nnnorm.ennreal_coe
      ae_measurable_const
  ... = (∫⁻ (a : α), ↑(nnnorm (f a)) ^ q ∂μ) ^ (1/q) * μ set.univ ^ (1/p - 1/q) :
    by simp [hpqr],
end

lemma snorm'_le_snorm_ess_sup_mul_rpow_measure_univ (hq_pos : 0 < q) {f : α → F} :
  snorm' f q μ ≤ snorm_ess_sup f μ * (μ set.univ) ^ (1/q) :=
begin
  have h_le : ∫⁻ (a : α), ↑(nnnorm (f a)) ^ q ∂μ ≤ ∫⁻ (a : α), (snorm_ess_sup f μ) ^ q ∂μ,
  { refine lintegral_mono_ae _,
    have h_nnnorm_le_snorm_ess_sup := coe_nnnorm_ae_le_snorm_ess_sup f μ,
    refine h_nnnorm_le_snorm_ess_sup.mono (λ x hx, ennreal.rpow_le_rpow hx (le_of_lt hq_pos)), },
  rw [snorm', ←ennreal.rpow_one (snorm_ess_sup f μ)],
  nth_rewrite 1 ←mul_inv_cancel (ne_of_lt hq_pos).symm,
  rw [ennreal.rpow_mul, one_div,
    ←@ennreal.mul_rpow_of_nonneg _ _ q⁻¹ (by simp [hq_pos.le])],
  refine ennreal.rpow_le_rpow _ (by simp [hq_pos.le]),
  rwa lintegral_const at h_le,
end

lemma snorm'_le_snorm'_of_exponent_le {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q) (μ : measure α)
  [probability_measure μ] {f : α → E} (hf : ae_measurable f μ) :
  snorm' f p μ ≤ snorm' f q μ :=
begin
  have h_le_μ := snorm'_le_snorm'_mul_rpow_measure_univ hp0_lt hpq hf,
  rwa [measure_univ, ennreal.one_rpow, mul_one] at h_le_μ,
end

lemma snorm'_le_snorm_ess_sup (hq_pos : 0 < q) {f : α → F} [probability_measure μ] :
  snorm' f q μ ≤ snorm_ess_sup f μ :=
le_trans (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hq_pos) (le_of_eq (by simp [measure_univ]))

lemma snorm_le_snorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [probability_measure μ]
  {f : α → E} (hf : ae_measurable f μ) :
  snorm f p μ ≤ snorm f q μ :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  rw ←ne.def at hp0,
  by_cases hq_top : q = ∞,
  { by_cases hp_top : p = ∞,
    { rw [hq_top, hp_top],
      exact le_refl _, },
    { have hp_pos : 0 < p.to_real,
      from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
      rw [snorm_eq_snorm' hp0 hp_top, hq_top, snorm_exponent_top],
      refine le_trans (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hp_pos) (le_of_eq _),
      simp [measure_univ], }, },
  { have hp_top : p ≠ ∞,
    { by_contra hp_eq_top,
      push_neg at hp_eq_top,
      refine hq_top _,
      rwa [hp_eq_top, top_le_iff] at hpq, },
    have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
    have hq0 : q ≠ 0,
    { by_contra hq_eq_zero,
      push_neg at hq_eq_zero,
      have hp_eq_zero : p = 0, from le_antisymm (by rwa hq_eq_zero at hpq) (zero_le _),
      rw [hp_eq_zero, ennreal.zero_to_real] at hp_pos,
      exact (lt_irrefl _) hp_pos, },
    have hpq_real : p.to_real ≤ q.to_real, by rwa ennreal.to_real_le_to_real hp_top hq_top,
    rw [snorm_eq_snorm' hp0 hp_top, snorm_eq_snorm' hq0 hq_top],
    exact snorm'_le_snorm'_of_exponent_le hp_pos hpq_real _ hf, },
end

lemma snorm'_lt_top_of_snorm'_lt_top_of_exponent_le {p q : ℝ} [finite_measure μ] {f : α → E}
  (hf : ae_measurable f μ) (hfq_lt_top : snorm' f q μ < ∞) (hp_nonneg : 0 ≤ p) (hpq : p ≤ q) :
  snorm' f p μ < ∞ :=
begin
  cases le_or_lt p 0 with hp_nonpos hp_pos,
  { rw le_antisymm hp_nonpos hp_nonneg,
    simp, },
  have hq_pos : 0 < q, from lt_of_lt_of_le hp_pos hpq,
  calc snorm' f p μ
      ≤ snorm' f q μ * (μ set.univ) ^ (1/p - 1/q) :
    snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq hf
  ... < ∞ :
  begin
    rw ennreal.mul_lt_top_iff,
    refine or.inl ⟨hfq_lt_top, ennreal.rpow_lt_top_of_nonneg _ (measure_ne_top μ set.univ)⟩,
    rwa [le_sub, sub_zero, one_div, one_div, inv_le_inv hq_pos hp_pos],
  end
end

lemma mem_ℒp.mem_ℒp_of_exponent_le {p q : ℝ≥0∞} [finite_measure μ] {f : α → E}
  (hfq : mem_ℒp f q μ) (hpq : p ≤ q) :
  mem_ℒp f p μ :=
begin
  cases hfq with hfq_m hfq_lt_top,
  by_cases hp0 : p = 0,
  { rwa [hp0, mem_ℒp_zero_iff_ae_measurable], },
  rw ←ne.def at hp0,
  refine ⟨hfq_m, _⟩,
  by_cases hp_top : p = ∞,
  { have hq_top : q = ∞,
      by rwa [hp_top, top_le_iff] at hpq,
    rw [hp_top],
    rwa hq_top at hfq_lt_top, },
  have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
  by_cases hq_top : q = ∞,
  { rw snorm_eq_snorm' hp0 hp_top,
    rw [hq_top, snorm_exponent_top] at hfq_lt_top,
    refine lt_of_le_of_lt (snorm'_le_snorm_ess_sup_mul_rpow_measure_univ hp_pos) _,
    refine ennreal.mul_lt_top hfq_lt_top _,
    exact ennreal.rpow_lt_top_of_nonneg (by simp [le_of_lt hp_pos]) (measure_ne_top μ set.univ), },
  have hq0 : q ≠ 0,
  { by_contra hq_eq_zero,
    push_neg at hq_eq_zero,
    have hp_eq_zero : p = 0, from le_antisymm (by rwa hq_eq_zero at hpq) (zero_le _),
    rw [hp_eq_zero, ennreal.zero_to_real] at hp_pos,
    exact (lt_irrefl _) hp_pos, },
  have hpq_real : p.to_real ≤ q.to_real, by rwa ennreal.to_real_le_to_real hp_top hq_top,
  rw snorm_eq_snorm' hp0 hp_top,
  rw snorm_eq_snorm' hq0 hq_top at hfq_lt_top,
  exact snorm'_lt_top_of_snorm'_lt_top_of_exponent_le hfq_m hfq_lt_top (le_of_lt hp_pos) hpq_real,
end

lemma snorm'_add_le {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ) (hq1 : 1 ≤ q) :
  snorm' (f + g) q μ ≤ snorm' f q μ + snorm' g q μ :=
calc (∫⁻ a, ↑(nnnorm ((f + g) a)) ^ q ∂μ) ^ (1 / q)
    ≤ (∫⁻ a, (((λ a, (nnnorm (f a) : ℝ≥0∞))
        + (λ a, (nnnorm (g a) : ℝ≥0∞))) a) ^ q ∂μ) ^ (1 / q) :
begin
  refine @ennreal.rpow_le_rpow _ _ (1/q) _ (by simp [le_trans zero_le_one hq1]),
  refine lintegral_mono (λ a, ennreal.rpow_le_rpow _ (le_trans zero_le_one hq1)),
  simp [←ennreal.coe_add, nnnorm_add_le],
end
... ≤ snorm' f q μ + snorm' g q μ :
  ennreal.lintegral_Lp_add_le hf.nnnorm.ennreal_coe hg.nnnorm.ennreal_coe hq1

lemma snorm_ess_sup_add_le {f g : α → F} :
  snorm_ess_sup (f + g) μ ≤ snorm_ess_sup f μ + snorm_ess_sup g μ :=
begin
  refine le_trans (ess_sup_mono_ae (filter.eventually_of_forall (λ x, _)))
    (ennreal.ess_sup_add_le _ _),
  simp_rw [pi.add_apply, ←ennreal.coe_add, ennreal.coe_le_coe],
  exact nnnorm_add_le _ _,
end

lemma snorm_add_le {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ) (hp1 : 1 ≤ p) :
  snorm (f + g) p μ ≤ snorm f p μ + snorm g p μ :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  by_cases hp_top : p = ∞,
  { simp [hp_top, snorm_ess_sup_add_le], },
  have hp1_real : 1 ≤ p.to_real,
  by rwa [← ennreal.one_to_real, ennreal.to_real_le_to_real ennreal.one_ne_top hp_top],
  repeat { rw snorm_eq_snorm' hp0 hp_top, },
  exact snorm'_add_le hf hg hp1_real,
end

lemma snorm'_sum_le [second_countable_topology E] {ι} {f : ι → α → E} {s : finset ι}
  (hfs : ∀ i, i ∈ s → ae_measurable (f i) μ) (hq1 : 1 ≤ q) :
  snorm' (∑ i in s, f i) q μ ≤ ∑ i in s, snorm' (f i) q μ :=
finset.le_sum_of_subadditive_on_pred (λ (f : α → E), snorm' f q μ)
  (λ f, ae_measurable f μ) (snorm'_zero (zero_lt_one.trans_le hq1))
  (λ f g hf hg, snorm'_add_le hf hg hq1) (λ x y, ae_measurable.add) _ hfs

lemma snorm_sum_le [second_countable_topology E] {ι} {f : ι → α → E} {s : finset ι}
  (hfs : ∀ i, i ∈ s → ae_measurable (f i) μ) (hp1 : 1 ≤ p) :
  snorm (∑ i in s, f i) p μ ≤ ∑ i in s, snorm (f i) p μ :=
finset.le_sum_of_subadditive_on_pred (λ (f : α → E), snorm f p μ)
  (λ f, ae_measurable f μ) snorm_zero (λ f g hf hg, snorm_add_le hf hg hp1)
  (λ x y, ae_measurable.add) _ hfs

lemma snorm_add_lt_top_of_one_le {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ)
  (hq1 : 1 ≤ p) : snorm (f + g) p μ < ∞ :=
lt_of_le_of_lt (snorm_add_le hf.1 hg.1 hq1) (ennreal.add_lt_top.mpr ⟨hf.2, hg.2⟩)

lemma snorm'_add_lt_top_of_le_one {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ)
  (hf_snorm : snorm' f q μ < ∞) (hg_snorm : snorm' g q μ < ∞) (hq_pos : 0 < q) (hq1 : q ≤ 1) :
  snorm' (f + g) q μ < ∞ :=
calc (∫⁻ a, ↑(nnnorm ((f + g) a)) ^ q ∂μ) ^ (1 / q)
    ≤ (∫⁻ a, (((λ a, (nnnorm (f a) : ℝ≥0∞))
        + (λ a, (nnnorm (g a) : ℝ≥0∞))) a) ^ q ∂μ) ^ (1 / q) :
begin
  refine @ennreal.rpow_le_rpow _ _ (1/q) _ (by simp [hq_pos.le]),
  refine lintegral_mono (λ a, ennreal.rpow_le_rpow _ hq_pos.le),
  simp [←ennreal.coe_add, nnnorm_add_le],
end
... ≤ (∫⁻ a, (nnnorm (f a) : ℝ≥0∞) ^ q + (nnnorm (g a) : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) :
begin
  refine @ennreal.rpow_le_rpow _ _ (1/q) (lintegral_mono (λ a, _)) (by simp [hq_pos.le]),
  exact ennreal.rpow_add_le_add_rpow _ _ hq_pos hq1,
end
... < ∞ :
begin
  refine @ennreal.rpow_lt_top_of_nonneg _ (1/q) (by simp [hq_pos.le]) _,
  rw [lintegral_add' hf.nnnorm.ennreal_coe.ennreal_rpow_const
    hg.nnnorm.ennreal_coe.ennreal_rpow_const, ennreal.add_ne_top, ←lt_top_iff_ne_top,
    ←lt_top_iff_ne_top],
  exact ⟨lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hq_pos hf_snorm,
    lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top hq_pos hg_snorm⟩,
end

lemma snorm_add_lt_top {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  snorm (f + g) p μ < ∞ :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  rw ←ne.def at h0,
  cases le_total 1 p with hp1 hp1,
  { exact snorm_add_lt_top_of_one_le hf hg hp1, },
  have hp_top : p ≠ ∞, from (lt_of_le_of_lt hp1 ennreal.coe_lt_top).ne,
  have hp_pos : 0 < p.to_real,
  { rw [← ennreal.zero_to_real, @ennreal.to_real_lt_to_real 0 p ennreal.coe_ne_top hp_top],
    exact ((zero_le p).lt_of_ne h0.symm), },
  have hp1_real : p.to_real ≤ 1,
  { rwa [← ennreal.one_to_real, @ennreal.to_real_le_to_real p 1 hp_top ennreal.coe_ne_top], },
  rw snorm_eq_snorm' h0 hp_top,
  rw [mem_ℒp, snorm_eq_snorm' h0 hp_top] at hf hg,
  exact snorm'_add_lt_top_of_le_one hf.1 hg.1 hf.2 hg.2 hp_pos hp1_real,
end

section second_countable_topology
variable [second_countable_topology E]

lemma mem_ℒp.add {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) : mem_ℒp (f + g) p μ :=
⟨ae_measurable.add hf.1 hg.1, snorm_add_lt_top hf hg⟩

lemma mem_ℒp.sub {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) : mem_ℒp (f - g) p μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

end second_countable_topology

end borel_space

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F]

lemma snorm'_const_smul {f : α → F} (c : 𝕜) (hq0_lt : 0 < q) :
  snorm' (c • f) q μ = (nnnorm c : ℝ≥0∞) * snorm' f q μ :=
begin
  rw snorm',
  simp_rw [pi.smul_apply, nnnorm_smul, ennreal.coe_mul,
    ennreal.mul_rpow_of_nonneg _ _ (le_of_lt hq0_lt)],
  suffices h_integral : ∫⁻ a, ↑(nnnorm c) ^ q * ↑(nnnorm (f a)) ^ q ∂μ
    = (nnnorm c : ℝ≥0∞)^q * ∫⁻ a, (nnnorm (f a)) ^ q ∂μ,
  { apply_fun (λ x, x ^ (1/q)) at h_integral,
    rw [h_integral, @ennreal.mul_rpow_of_nonneg _ _ (1/q) (by simp [le_of_lt hq0_lt])],
    congr,
    simp_rw [←ennreal.rpow_mul, one_div, mul_inv_cancel (ne_of_lt hq0_lt).symm,
      ennreal.rpow_one], },
  rw lintegral_const_mul',
  rw ennreal.coe_rpow_of_nonneg _ hq0_lt.le,
  exact ennreal.coe_ne_top,
end

lemma snorm_ess_sup_const_smul {f : α → F} (c : 𝕜) :
  snorm_ess_sup (c • f) μ = (nnnorm c : ℝ≥0∞) * snorm_ess_sup f μ :=
by simp_rw [snorm_ess_sup,  pi.smul_apply, nnnorm_smul, ennreal.coe_mul, ennreal.ess_sup_const_mul]

lemma snorm_const_smul {f : α → F} (c : 𝕜) :
  snorm (c • f) p μ = (nnnorm c : ℝ≥0∞) * snorm f p μ :=
begin
  by_cases h0 : p = 0,
  { simp [h0], },
  by_cases h_top : p = ∞,
  { simp [h_top, snorm_ess_sup_const_smul], },
  repeat { rw snorm_eq_snorm' h0 h_top, },
  rw ←ne.def at h0,
  exact snorm'_const_smul c
    (ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) h0.symm, h_top⟩),
end

lemma mem_ℒp.const_smul [borel_space E] {f : α → E} (hf : mem_ℒp f p μ) (c : 𝕜) :
  mem_ℒp (c • f) p μ :=
⟨ae_measurable.const_smul hf.1 c,
  lt_of_le_of_lt (le_of_eq (snorm_const_smul c)) (ennreal.mul_lt_top ennreal.coe_lt_top hf.2)⟩

lemma mem_ℒp.const_mul [measurable_space 𝕜] [borel_space 𝕜]
  {f : α → 𝕜} (hf : mem_ℒp f p μ) (c : 𝕜) : mem_ℒp (λ x, c * f x) p μ :=
hf.const_smul c

lemma snorm'_smul_le_mul_snorm' [opens_measurable_space E] [measurable_space 𝕜]
  [opens_measurable_space 𝕜] {p q r : ℝ}
  {f : α → E} (hf : ae_measurable f μ) {φ : α → 𝕜} (hφ : ae_measurable φ μ)
  (hp0_lt : 0 < p) (hpq : p < q) (hpqr : 1/p = 1/q + 1/r) :
  snorm' (φ • f) p μ ≤ snorm' φ q μ * snorm' f r μ :=
begin
  simp_rw [snorm', pi.smul_apply', nnnorm_smul, ennreal.coe_mul],
  exact ennreal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hφ.nnnorm.ennreal_coe
    hf.nnnorm.ennreal_coe,
end

end normed_space

section monotonicity

lemma snorm_le_mul_snorm_aux_of_nonneg {f : α → F} {g : α → G} {c : ℝ}
  (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ c * ∥g x∥) (hc : 0 ≤ c) (p : ℝ≥0∞) :
  snorm f p μ ≤ (ennreal.of_real c) * snorm g p μ :=
begin
  lift c to ℝ≥0 using hc,
  rw [ennreal.of_real_coe_nnreal, ← c.nnnorm_eq, ← snorm_norm g, ← snorm_const_smul (c : ℝ)],
  swap, apply_instance,
  refine snorm_mono_ae _,
  simpa
end

lemma snorm_le_mul_snorm_aux_of_neg {f : α → F} {g : α → G} {c : ℝ}
  (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ c * ∥g x∥) (hc : c < 0) (p : ℝ≥0∞) :
  snorm f p μ = 0 ∧ snorm g p μ = 0 :=
begin
  suffices : f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0,
    by simp [snorm_congr_ae this.1, snorm_congr_ae this.2],
  refine ⟨h.mono $ λ x hx, _, h.mono $ λ x hx, _⟩,
  { refine norm_le_zero_iff.1 (hx.trans _),
    exact mul_nonpos_of_nonpos_of_nonneg hc.le (norm_nonneg _) },
  { refine norm_le_zero_iff.1 (nonpos_of_mul_nonneg_right _ hc),
    exact (norm_nonneg _).trans hx }
end

lemma snorm_le_mul_snorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
  (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ c * ∥g x∥) (p : ℝ≥0∞) :
  snorm f p μ ≤ (ennreal.of_real c) * snorm g p μ :=
begin
  cases le_or_lt 0 c with hc hc,
  { exact snorm_le_mul_snorm_aux_of_nonneg h hc p },
  { simp [snorm_le_mul_snorm_aux_of_neg h hc p] }
end

lemma mem_ℒp.of_le_mul [measurable_space F] {f : α → E} {g : α → F} {c : ℝ}
  (hg : mem_ℒp g p μ) (hf : ae_measurable f μ) (hfg : ∀ᵐ x ∂μ, ∥f x∥ ≤ c * ∥g x∥) :
  mem_ℒp f p μ :=
begin
  simp only [mem_ℒp, hf, true_and],
  apply lt_of_le_of_lt (snorm_le_mul_snorm_of_ae_le_mul hfg p),
  simp [lt_top_iff_ne_top, hg.snorm_ne_top],
end

end monotonicity

end ℒp

/-!
### Lp space

The space of equivalence classes of measurable functions for which `snorm f p μ < ∞`.
-/

@[simp] lemma snorm_ae_eq_fun {α E : Type*} [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E] {p : ℝ≥0∞} {f : α → E} (hf : ae_measurable f μ) :
  snorm (ae_eq_fun.mk f hf) p μ = snorm f p μ :=
snorm_congr_ae (ae_eq_fun.coe_fn_mk _ _)

lemma mem_ℒp.snorm_mk_lt_top {α E : Type*} [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E] {p : ℝ≥0∞} {f : α → E} (hfp : mem_ℒp f p μ) :
  snorm (ae_eq_fun.mk f hfp.1) p μ < ∞ :=
by simp [hfp.2]

/-- Lp space -/
def Lp {α} (E : Type*) [measurable_space α] [measurable_space E] [normed_group E]
  [borel_space E] [second_countable_topology E]
  (p : ℝ≥0∞) (μ : measure α) : add_subgroup (α →ₘ[μ] E) :=
{ carrier := {f | snorm f p μ < ∞},
  zero_mem' := by simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero],
  add_mem' := λ f g hf hg, by simp [snorm_congr_ae (ae_eq_fun.coe_fn_add _ _),
    snorm_add_lt_top ⟨f.ae_measurable, hf⟩ ⟨g.ae_measurable, hg⟩],
  neg_mem' := λ f hf,
    by rwa [set.mem_set_of_eq, snorm_congr_ae (ae_eq_fun.coe_fn_neg _), snorm_neg] }

notation α ` →₁[`:25 μ `] ` E := measure_theory.Lp E 1 μ

namespace mem_ℒp

variables [borel_space E] [second_countable_topology E]

/-- make an element of Lp from a function verifying `mem_ℒp` -/
def to_Lp (f : α → E) (h_mem_ℒp : mem_ℒp f p μ) : Lp E p μ :=
⟨ae_eq_fun.mk f h_mem_ℒp.1, h_mem_ℒp.snorm_mk_lt_top⟩

lemma coe_fn_to_Lp {f : α → E} (hf : mem_ℒp f p μ) : hf.to_Lp f =ᵐ[μ] f :=
ae_eq_fun.coe_fn_mk _ _

@[simp] lemma to_Lp_eq_to_Lp_iff {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  hf.to_Lp f = hg.to_Lp g ↔ f =ᵐ[μ] g :=
by simp [to_Lp]

@[simp] lemma to_Lp_zero (h : mem_ℒp (0 : α → E) p μ ) : h.to_Lp 0 = 0 := rfl

lemma to_Lp_add {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  (hf.add hg).to_Lp (f + g) = hf.to_Lp f + hg.to_Lp g := rfl

lemma to_Lp_neg {f : α → E} (hf : mem_ℒp f p μ) : hf.neg.to_Lp (-f) = - hf.to_Lp f := rfl

lemma to_Lp_sub {f g : α → E} (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  (hf.sub hg).to_Lp (f - g) = hf.to_Lp f - hg.to_Lp g :=
by { convert hf.to_Lp_add hg.neg, exact sub_eq_add_neg f g }

end mem_ℒp

namespace Lp

variables [borel_space E] [second_countable_topology E]

instance : has_coe_to_fun (Lp E p μ) := ⟨λ _, α → E, λ f, ((f : α →ₘ[μ] E) : α → E)⟩

@[ext] lemma ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g :=
begin
  cases f,
  cases g,
  simp only [subtype.mk_eq_mk],
  exact ae_eq_fun.ext h
end

lemma ext_iff {f g : Lp E p μ} : f = g ↔ f =ᵐ[μ] g :=
⟨λ h, by rw h, λ h, ext h⟩

lemma mem_Lp_iff_snorm_lt_top {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ snorm f p μ < ∞ := iff.refl _

lemma mem_Lp_iff_mem_ℒp {f : α →ₘ[μ] E} : f ∈ Lp E p μ ↔ mem_ℒp f p μ :=
by simp [mem_Lp_iff_snorm_lt_top, mem_ℒp, f.measurable.ae_measurable]

lemma antimono [finite_measure μ] {p q : ℝ≥0∞} (hpq : p ≤ q) : Lp E q μ ≤ Lp E p μ :=
λ f hf, (mem_ℒp.mem_ℒp_of_exponent_le ⟨f.ae_measurable, hf⟩ hpq).2

@[simp] lemma coe_fn_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) :
  ((⟨f, hf⟩ : Lp E p μ) : α → E) = f := rfl

@[simp] lemma coe_mk {f : α →ₘ[μ] E} (hf : snorm f p μ < ∞) :
  ((⟨f, hf⟩ : Lp E p μ) : α →ₘ[μ] E) = f := rfl

@[simp] lemma to_Lp_coe_fn (f : Lp E p μ) (hf : mem_ℒp f p μ) : hf.to_Lp f = f :=
by { cases f, simp [mem_ℒp.to_Lp] }

lemma snorm_lt_top (f : Lp E p μ) : snorm f p μ < ∞ := f.prop

lemma snorm_ne_top (f : Lp E p μ) : snorm f p μ ≠ ∞ := (snorm_lt_top f).ne

protected lemma measurable (f : Lp E p μ) : measurable f := f.val.measurable

protected lemma ae_measurable (f : Lp E p μ) : ae_measurable f μ := f.val.ae_measurable

protected lemma mem_ℒp (f : Lp E p μ) : mem_ℒp f p μ := ⟨Lp.ae_measurable f, f.prop⟩

variables (E p μ)
lemma coe_fn_zero : ⇑(0 : Lp E p μ) =ᵐ[μ] 0 := ae_eq_fun.coe_fn_zero
variables {E p μ}

lemma coe_fn_neg (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f := ae_eq_fun.coe_fn_neg _

lemma coe_fn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] f + g := ae_eq_fun.coe_fn_add _ _

lemma coe_fn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g := ae_eq_fun.coe_fn_sub _ _

lemma mem_Lp_const (α) [measurable_space α] (μ : measure α) (c : E) [finite_measure μ] :
  @ae_eq_fun.const α _ _ μ _ c ∈ Lp E p μ :=
(mem_ℒp_const c).snorm_mk_lt_top

instance : has_norm (Lp E p μ) := { norm := λ f, ennreal.to_real (snorm f p μ) }

instance : has_dist (Lp E p μ) := { dist := λ f g, ∥f - g∥}

instance : has_edist (Lp E p μ) := { edist := λ f g, ennreal.of_real (dist f g) }

lemma norm_def (f : Lp E p μ) : ∥f∥ = ennreal.to_real (snorm f p μ) := rfl

@[simp] lemma norm_to_Lp (f : α → E) (hf : mem_ℒp f p μ) :
  ∥hf.to_Lp f∥ = ennreal.to_real (snorm f p μ) :=
by rw [norm_def, snorm_congr_ae (mem_ℒp.coe_fn_to_Lp hf)]

lemma dist_def (f g : Lp E p μ) : dist f g = (snorm (f - g) p μ).to_real :=
begin
  simp_rw [dist, norm_def],
  congr' 1,
  apply snorm_congr_ae (coe_fn_sub _ _),
end

lemma edist_def (f g : Lp E p μ) : edist f g = snorm (f - g) p μ :=
begin
  simp_rw [edist, dist, norm_def, ennreal.of_real_to_real (snorm_ne_top _)],
  exact snorm_congr_ae (coe_fn_sub _ _)
end

@[simp] lemma edist_to_Lp_to_Lp (f g : α → E) (hf : mem_ℒp f p μ) (hg : mem_ℒp g p μ) :
  edist (hf.to_Lp f) (hg.to_Lp g) = snorm (f - g) p μ :=
by { rw edist_def, exact snorm_congr_ae (hf.coe_fn_to_Lp.sub hg.coe_fn_to_Lp) }

@[simp] lemma edist_to_Lp_zero (f : α → E) (hf : mem_ℒp f p μ) :
  edist (hf.to_Lp f) 0 = snorm f p μ :=
by { convert edist_to_Lp_to_Lp f 0 hf zero_mem_ℒp, simp }

@[simp] lemma norm_zero : ∥(0 : Lp E p μ)∥ = 0 :=
begin
  change (snorm ⇑(0 : α →ₘ[μ] E) p μ).to_real = 0,
  simp [snorm_congr_ae ae_eq_fun.coe_fn_zero, snorm_zero]
end

lemma norm_eq_zero_iff {f : Lp E p μ} (hp : 0 < p) : ∥f∥ = 0 ↔ f = 0 :=
begin
  refine ⟨λ hf, _, λ hf, by simp [hf]⟩,
  rw [norm_def, ennreal.to_real_eq_zero_iff] at hf,
  cases hf,
  { rw snorm_eq_zero_iff (Lp.ae_measurable f) hp.ne.symm at hf,
    exact subtype.eq (ae_eq_fun.ext (hf.trans ae_eq_fun.coe_fn_zero.symm)), },
  { exact absurd hf (snorm_ne_top f), },
end

lemma eq_zero_iff_ae_eq_zero {f : Lp E p μ} : f = 0 ↔ f =ᵐ[μ] 0 :=
begin
  split,
  { assume h,
    rw h,
    exact ae_eq_fun.coe_fn_const _ _ },
  { assume h,
    ext1,
    filter_upwards [h, ae_eq_fun.coe_fn_const α (0 : E)],
    assume a ha h'a,
    rw ha,
    exact h'a.symm }
end

@[simp] lemma norm_neg {f : Lp E p μ} : ∥-f∥ = ∥f∥ :=
by rw [norm_def, norm_def, snorm_congr_ae (coe_fn_neg _), snorm_neg]

lemma norm_le_mul_norm_of_ae_le_mul
  [second_countable_topology F] [measurable_space F] [borel_space F]
  {c : ℝ} {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ c * ∥g x∥) : ∥f∥ ≤ c * ∥g∥ :=
begin
  by_cases pzero : p = 0,
  { simp [pzero, norm_def] },
  cases le_or_lt 0 c with hc hc,
  { have := snorm_le_mul_snorm_aux_of_nonneg h hc p,
    rw [← ennreal.to_real_le_to_real, ennreal.to_real_mul, ennreal.to_real_of_real hc] at this,
    { exact this },
    { exact (Lp.mem_ℒp _).snorm_ne_top },
    { simp [(Lp.mem_ℒp _).snorm_ne_top] } },
  { have := snorm_le_mul_snorm_aux_of_neg h hc p,
    simp only [snorm_eq_zero_iff (Lp.ae_measurable _) pzero, ← eq_zero_iff_ae_eq_zero] at this,
    simp [this] }
end

lemma norm_le_norm_of_ae_le [second_countable_topology F] [measurable_space F] [borel_space F]
  {f : Lp E p μ} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ ∥g x∥) : ∥f∥ ≤ ∥g∥ :=
begin
  rw [norm_def, norm_def, ennreal.to_real_le_to_real (snorm_ne_top _) (snorm_ne_top _)],
  exact snorm_mono_ae h
end

lemma mem_Lp_of_ae_le_mul [second_countable_topology F] [measurable_space F] [borel_space F]
  {c : ℝ} {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ c * ∥g x∥) : f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_le_mul (Lp.mem_ℒp g) (ae_eq_fun.ae_measurable f) h

lemma mem_Lp_of_ae_le [second_countable_topology F] [measurable_space F] [borel_space F]
  {f : α →ₘ[μ] E} {g : Lp F p μ} (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ ∥g x∥) : f ∈ Lp E p μ :=
mem_Lp_iff_mem_ℒp.2 $ mem_ℒp.of_le (Lp.mem_ℒp g) (ae_eq_fun.ae_measurable f) h

instance [hp : fact (1 ≤ p)] : normed_group (Lp E p μ) :=
normed_group.of_core _
{ norm_eq_zero_iff := λ f, norm_eq_zero_iff (ennreal.zero_lt_one.trans_le hp),
  triangle := begin
    assume f g,
    simp only [norm_def],
    rw ← ennreal.to_real_add (snorm_ne_top f) (snorm_ne_top g),
    suffices h_snorm : snorm ⇑(f + g) p μ ≤ snorm ⇑f p μ + snorm ⇑g p μ,
    { rwa ennreal.to_real_le_to_real (snorm_ne_top (f + g)),
      exact ennreal.add_ne_top.mpr ⟨snorm_ne_top f, snorm_ne_top g⟩, },
    rw [snorm_congr_ae (coe_fn_add _ _)],
    exact snorm_add_le (Lp.ae_measurable f) (Lp.ae_measurable g) hp,
  end,
  norm_neg := by simp }

instance normed_group_L1 : normed_group (Lp E 1 μ) := by apply_instance
instance normed_group_L2 : normed_group (Lp E 2 μ) := by apply_instance
instance normed_group_Ltop : normed_group (Lp E ∞ μ) := by apply_instance

section normed_space

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma mem_Lp_const_smul (c : 𝕜) (f : Lp E p μ) : c • ↑f ∈ Lp E p μ :=
begin
  rw [mem_Lp_iff_snorm_lt_top, snorm_congr_ae (ae_eq_fun.coe_fn_smul _ _), snorm_const_smul,
    ennreal.mul_lt_top_iff],
  exact or.inl ⟨ennreal.coe_lt_top, f.prop⟩,
end

instance : has_scalar 𝕜 (Lp E p μ) := { smul := λ c f, ⟨c • ↑f, mem_Lp_const_smul c f⟩ }

lemma coe_fn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f) =ᵐ[μ] c • f := ae_eq_fun.coe_fn_smul _ _

instance : semimodule 𝕜 (Lp E p μ) :=
{ one_smul := λ _, subtype.eq (one_smul 𝕜 _),
  mul_smul := λ _ _ _, subtype.eq (mul_smul _ _ _),
  smul_add := λ _ _ _, subtype.eq (smul_add _ _ _),
  smul_zero := λ _, subtype.eq (smul_zero _),
  add_smul := λ _ _ _, subtype.eq (add_smul _ _ _),
  zero_smul := λ _, subtype.eq (zero_smul _ _) }

lemma norm_const_smul (c : 𝕜) (f : Lp E p μ) : ∥c • f∥ = ∥c∥ * ∥f∥ :=
by rw [norm_def, snorm_congr_ae (coe_fn_smul _ _), snorm_const_smul c,
  ennreal.to_real_mul, ennreal.coe_to_real, coe_nnnorm, norm_def]

instance [fact (1 ≤ p)] : normed_space 𝕜 (Lp E p μ) :=
{ norm_smul_le := λ _ _, by simp [norm_const_smul] }

instance normed_space_L1 : normed_space 𝕜 (Lp E 1 μ) := by apply_instance
instance normed_space_L2 : normed_space 𝕜 (Lp E 2 μ) := by apply_instance
instance normed_space_Ltop : normed_space 𝕜 (Lp E ∞ μ) := by apply_instance

end normed_space

end Lp

namespace mem_ℒp

variables
  [borel_space E] [second_countable_topology E]
  {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma to_Lp_const_smul {f : α → E} (c : 𝕜) (hf : mem_ℒp f p μ) :
  (hf.const_smul c).to_Lp (c • f) = c • hf.to_Lp f := rfl

end mem_ℒp

end measure_theory

open measure_theory

/-!
### Composition on `L^p`

We show that Lipschitz functions vanishing at zero act by composition on `L^p`, and specialize
this to the composition with continuous linear maps, and to the definition of the positive
part of an `L^p` function.
-/

section composition

variables [second_countable_topology E] [borel_space E]
  [second_countable_topology F] [measurable_space F] [borel_space F]
  {g : E → F} {c : nnreal}

namespace lipschitz_with

/-- When `g` is a Lipschitz function sending `0` to `0` and `f` is in `Lp`, then `g ∘ f` is well
defined as an element of `Lp`. -/
def comp_Lp (hg : lipschitz_with c g) (g0 : g 0 = 0) (f : Lp E p μ) : Lp F p μ :=
⟨ae_eq_fun.comp g hg.continuous.measurable (f : α →ₘ[μ] E),
begin
  suffices : ∀ᵐ x ∂μ, ∥ae_eq_fun.comp g hg.continuous.measurable (f : α →ₘ[μ] E) x∥ ≤ c * ∥f x∥,
    { exact Lp.mem_Lp_of_ae_le_mul this },
  filter_upwards [ae_eq_fun.coe_fn_comp g hg.continuous.measurable (f : α →ₘ[μ] E)],
  assume a ha,
  simp only [ha],
  rw [← dist_zero_right, ← dist_zero_right, ← g0],
  exact hg.dist_le_mul (f a) 0,
end⟩

lemma coe_fn_comp_Lp (hg : lipschitz_with c g) (g0 : g 0 = 0) (f : Lp E p μ) :
  hg.comp_Lp g0 f =ᵐ[μ] g ∘ f :=
ae_eq_fun.coe_fn_comp _ _ _

@[simp] lemma comp_Lp_zero (hg : lipschitz_with c g) (g0 : g 0 = 0) :
  hg.comp_Lp g0 (0 : Lp E p μ) = 0 :=
begin
  rw Lp.eq_zero_iff_ae_eq_zero,
  apply (coe_fn_comp_Lp _ _ _).trans,
  filter_upwards [Lp.coe_fn_zero E p μ],
  assume a ha,
  simp [ha, g0]
end

lemma norm_comp_Lp_sub_le (hg : lipschitz_with c g) (g0 : g 0 = 0) (f f' : Lp E p μ) :
  ∥hg.comp_Lp g0 f - hg.comp_Lp g0 f'∥ ≤ c * ∥f - f'∥ :=
begin
  apply Lp.norm_le_mul_norm_of_ae_le_mul,
  filter_upwards [hg.coe_fn_comp_Lp g0 f, hg.coe_fn_comp_Lp g0 f',
    Lp.coe_fn_sub (hg.comp_Lp g0 f) (hg.comp_Lp g0 f'), Lp.coe_fn_sub f f'],
  assume a ha1 ha2 ha3 ha4,
  simp [ha1, ha2, ha3, ha4, ← dist_eq_norm],
  exact hg.dist_le_mul (f a) (f' a)
end

lemma norm_comp_Lp_le (hg : lipschitz_with c g) (g0 : g 0 = 0) (f : Lp E p μ) :
  ∥hg.comp_Lp g0 f∥ ≤ c * ∥f∥ :=
by simpa using hg.norm_comp_Lp_sub_le g0 f 0

lemma lipschitz_with_comp_Lp [fact (1 ≤ p)] (hg : lipschitz_with c g) (g0 : g 0 = 0) :
  lipschitz_with c (hg.comp_Lp g0 : Lp E p μ → Lp F p μ) :=
lipschitz_with.of_dist_le_mul $ λ f g, by simp [dist_eq_norm, norm_comp_Lp_sub_le]

lemma continuous_comp_Lp [fact (1 ≤ p)] (hg : lipschitz_with c g) (g0 : g 0 = 0) :
  continuous (hg.comp_Lp g0 : Lp E p μ → Lp F p μ) :=
(lipschitz_with_comp_Lp hg g0).continuous

end lipschitz_with

namespace continuous_linear_map
variables [normed_space ℝ E] [normed_space ℝ F]

/-- Composing `f : Lp ` with `L : E →L[ℝ] F`. -/
def comp_Lp (L : E →L[ℝ] F) (f : Lp E p μ) : Lp F p μ :=
L.lipschitz.comp_Lp (map_zero L) f

lemma coe_fn_comp_Lp (L : E →L[ℝ] F) (f : Lp E p μ) :
  ∀ᵐ a ∂μ, (L.comp_Lp f) a = L (f a) :=
lipschitz_with.coe_fn_comp_Lp _ _ _

variables (μ p)
/-- Composing `f : Lp E p μ` with `L : E →L[ℝ] F`, seen as a `ℝ`-linear map on `Lp E p μ`. -/
def comp_Lpₗ (L : E →L[ℝ] F) : (Lp E p μ) →ₗ[ℝ] (Lp F p μ) :=
{ to_fun := λ f, L.comp_Lp f,
  map_add' := begin
    intros f g,
    ext1,
    filter_upwards [Lp.coe_fn_add f g, coe_fn_comp_Lp L (f + g), coe_fn_comp_Lp L f,
      coe_fn_comp_Lp L g, Lp.coe_fn_add (L.comp_Lp f) (L.comp_Lp g)],
    assume a ha1 ha2 ha3 ha4 ha5,
    simp only [ha1, ha2, ha3, ha4, ha5, map_add, pi.add_apply],
  end,
  map_smul' := begin
    intros c f,
    ext1,
    filter_upwards [Lp.coe_fn_smul c f, coe_fn_comp_Lp L (c • f), Lp.coe_fn_smul c (L.comp_Lp f),
      coe_fn_comp_Lp L f],
    assume a ha1 ha2 ha3 ha4,
    simp only [ha1, ha2, ha3, ha4, map_smul, pi.smul_apply],
  end }

variables {μ p}
lemma norm_comp_Lp_le (L : E →L[ℝ] F) (f : Lp E p μ)  : ∥L.comp_Lp f∥ ≤ ∥L∥ * ∥f∥ :=
lipschitz_with.norm_comp_Lp_le _ _ _

variables (μ p)

/-- Composing `f : Lp E p μ` with `L : E →L[ℝ] F`, seen as a continuous `ℝ`-linear map on
`Lp E p μ`. -/
def comp_LpL [fact (1 ≤ p)] (L : E →L[ℝ] F) : (Lp E p μ) →L[ℝ] (Lp F p μ) :=
linear_map.mk_continuous (L.comp_Lpₗ p μ) ∥L∥ L.norm_comp_Lp_le

lemma norm_compLpL_le [fact (1 ≤ p)] (L : E →L[ℝ] F) :
  ∥L.comp_LpL p μ∥ ≤ ∥L∥ :=
linear_map.mk_continuous_norm_le _ (norm_nonneg _) _

end continuous_linear_map

namespace measure_theory
namespace Lp
section pos_part

lemma lipschitz_with_pos_part : lipschitz_with 1 (λ (x : ℝ), max x 0) :=
lipschitz_with.of_dist_le_mul $ λ x y, by simp [dist, abs_max_sub_max_le_abs]

/-- Positive part of a function in `L^p`. -/
def pos_part (f : Lp ℝ p μ) : Lp ℝ p μ :=
lipschitz_with_pos_part.comp_Lp (max_eq_right (le_refl _)) f

/-- Negative part of a function in `L^p`. -/
def neg_part (f : Lp ℝ p μ) : Lp ℝ p μ := pos_part (-f)

@[norm_cast]
lemma coe_pos_part (f : Lp ℝ p μ) : (pos_part f : α →ₘ[μ] ℝ) = (f : α →ₘ[μ] ℝ).pos_part := rfl

lemma coe_fn_pos_part (f : Lp ℝ p μ) : ⇑(pos_part f) =ᵐ[μ] λ a, max (f a) 0 :=
ae_eq_fun.coe_fn_pos_part _

lemma coe_fn_neg_part_eq_max (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, neg_part f a = max (- f a) 0 :=
begin
  rw neg_part,
  filter_upwards [coe_fn_pos_part (-f), coe_fn_neg f],
  assume a h₁ h₂,
  rw [h₁, h₂, pi.neg_apply]
end

lemma coe_fn_neg_part (f : Lp ℝ p μ) : ∀ᵐ a ∂μ, neg_part f a = - min (f a) 0 :=
(coe_fn_neg_part_eq_max f).mono $ assume a h,
by rw [h, ← max_neg_neg, neg_zero]

lemma continuous_pos_part [fact (1 ≤ p)] : continuous (λf : Lp ℝ p μ, pos_part f) :=
lipschitz_with.continuous_comp_Lp _ _

lemma continuous_neg_part [fact (1 ≤ p)] : continuous (λf : Lp ℝ p μ, neg_part f) :=
have eq : (λf : Lp ℝ p μ, neg_part f) = (λf : Lp ℝ p μ, pos_part (-f)) := rfl,
by { rw eq, exact continuous_pos_part.comp continuous_neg }

end pos_part
end Lp
end measure_theory
end composition
