/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
import analysis.calculus.fderiv_measurable
import analysis.calculus.deriv.comp
import analysis.calculus.deriv.add
import analysis.calculus.deriv.slope
import analysis.calculus.deriv.mul
import analysis.normed_space.dual
import measure_theory.integral.interval_integral
import measure_theory.integral.vitali_caratheodory

/-!
# Fundamental Theorem of Calculus

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove various versions of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus)
for interval integrals in `ℝ`.

Recall that its first version states that the function `(u, v) ↦ ∫_{u}^{v} x, f x` has derivative
`(δu, δv) ↦ δv • f b - δu • f a` at `(a, b)` provided that `f` is continuous at `a` and `b`,
and its second version states that, if `f` has an integrable derivative on `[a, b]`, then
`∫_{a}^{b} x, f' x = f b - f a`.

## Main statements

### FTC-1 for Lebesgue measure

We prove several versions of FTC-1, all in the `interval_integral` namespace. Many of them follow
the naming scheme `integral_has(_strict?)_(f?)deriv(_within?)_at(_of_tendsto_ae?)(_right|_left?)`.
They formulate FTC in terms of `has(_strict?)_(f?)deriv(_within?)_at`.
Let us explain the meaning of each part of the name:

* `_strict` means that the theorem is about strict differentiability;
* `f` means that the theorem is about differentiability in both endpoints; incompatible with
  `_right|_left`;
* `_within` means that the theorem is about one-sided derivatives, see below for details;
* `_of_tendsto_ae` means that instead of continuity the theorem assumes that `f` has a finite limit
  almost surely as `x` tends to `a` and/or `b`;
* `_right` or `_left` mean that the theorem is about differentiability in the right (resp., left)
  endpoint.

We also reformulate these theorems in terms of `(f?)deriv(_within?)`. These theorems are named
`(f?)deriv(_within?)_integral(_of_tendsto_ae?)(_right|_left?)` with the same meaning of parts of the
name.

### One-sided derivatives

Theorem `integral_has_fderiv_within_at_of_tendsto_ae` states that `(u, v) ↦ ∫_{u}^{v} x, f x` has a
derivative `(δu, δv) ↦ δv • cb - δu • ca` within the set `s × t` at `(a, b)` provided that `f` tends
to `ca` (resp., `cb`) almost surely at `la` (resp., `lb`), where possible values of `s`, `t`, and
corresponding filters `la`, `lb` are given in the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |

We use a typeclass `FTC_filter` to make Lean automatically find `la`/`lb` based on `s`/`t`. This way
we can formulate one theorem instead of `16` (or `8` if we leave only non-trivial ones not covered
by `integral_has_deriv_within_at_of_tendsto_ae_(left|right)` and
`integral_has_fderiv_at_of_tendsto_ae`). Similarly,
`integral_has_deriv_within_at_of_tendsto_ae_right` works for both one-sided derivatives using the
same typeclass to find an appropriate filter.

### FTC for a locally finite measure

Before proving FTC for the Lebesgue measure, we prove a few statements that can be seen as FTC for
any measure. The most general of them,
`measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae`, states the following. Let `(la, la')`
be an `FTC_filter` pair of filters around `a` (i.e., `FTC_filter a la la'`) and let `(lb, lb')` be
an `FTC_filter` pair of filters around `b`. If `f` has finite limits `ca` and `cb` almost surely at
`la'` and `lb'`, respectively, then
`∫_{va}^{vb} x, f x ∂μ - ∫_{ua}^{ub} x, f x ∂μ = ∫_{ub}^{vb} x, cb ∂μ - ∫_{ua}^{va} x, ca ∂μ +
  o(‖∫_{ua}^{va} x, (1:ℝ) ∂μ‖ + ‖∫_{ub}^{vb} x, (1:ℝ) ∂μ‖)` as `ua` and `va` tend to `la` while
`ub` and `vb` tend to `lb`.

### FTC-2 and corollaries

We use FTC-1 to prove several versions of FTC-2 for the Lebesgue measure, using a similar naming
scheme as for the versions of FTC-1. They include:
* `interval_integral.integral_eq_sub_of_has_deriv_right_of_le` - most general version, for functions
  with a right derivative
* `interval_integral.integral_eq_sub_of_has_deriv_at'` - version for functions with a derivative on
  an open set
* `interval_integral.integral_deriv_eq_sub'` - version that is easiest to use when computing the
  integral of a specific function

We then derive additional integration techniques from FTC-2:
* `interval_integral.integral_mul_deriv_eq_deriv_mul` - integration by parts
* `interval_integral.integral_comp_mul_deriv''` - integration by substitution

Many applications of these theorems can be found in the file `analysis.special_functions.integrals`.

Note that the assumptions of FTC-2 are formulated in the form that `f'` is integrable. To use it in
a context with the stronger assumption that `f'` is continuous, one can use
`continuous_on.interval_integrable` or `continuous_on.integrable_on_Icc` or
`continuous_on.integrable_on_interval`.

### `FTC_filter` class

As explained above, many theorems in this file rely on the typeclass
`FTC_filter (a : ℝ) (l l' : filter ℝ)` to avoid code duplication. This typeclass combines four
assumptions:

- `pure a ≤ l`;
- `l' ≤ 𝓝 a`;
- `l'` has a basis of measurable sets;
- if `u n` and `v n` tend to `l`, then for any `s ∈ l'`, `Ioc (u n) (v n)` is eventually included
  in `s`.

This typeclass has the following “real” instances: `(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`,
`(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`.
Furthermore, we have the following instances that are equal to the previously mentioned instances:
`(a, 𝓝[{a}] a, ⊥)` and `(a, 𝓝[univ] a, 𝓝[univ] a)`.
While the difference between `Ici a` and `Ioi a` doesn't matter for theorems about Lebesgue measure,
it becomes important in the versions of FTC about any locally finite measure if this measure has an
atom at one of the endpoints.

### Combining one-sided and two-sided derivatives

There are some `FTC_filter` instances where the fact that it is one-sided or
two-sided depends on the point, namely `(x, 𝓝[Icc a b] x, 𝓝[Icc a b] x)`
(resp. `(x, 𝓝[[a, b]] x, 𝓝[[a, b]] x)`, where `[a, b] = set.uIcc a b`),
with `x ∈ Icc a b` (resp. `x ∈ [a, b]`).
This results in a two-sided derivatives for `x ∈ Ioo a b` and one-sided derivatives for
`x ∈ {a, b}`. Other instances could be added when needed (in that case, one also needs to add
instances for `filter.is_measurably_generated` and `filter.tendsto_Ixx_class`).

## Tags

integral, fundamental theorem of calculus, FTC-1, FTC-2, change of variables in integrals
-/

noncomputable theory
open topological_space (second_countable_topology)
open measure_theory set classical filter function

open_locale classical topology filter ennreal big_operators interval nnreal

variables {ι 𝕜 E F A : Type*} [normed_add_comm_group E]
  [complete_space E] [normed_space ℝ E]

namespace interval_integral

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integrals
w.r.t. any measure. Many theorems are formulated for one or two pairs of filters related by
`FTC_filter a l l'`. This typeclass has exactly four “real” instances: `(a, pure a, ⊥)`,
`(a, 𝓝[≥] a, 𝓝[>] a)`, `(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances
that are equal to the first and last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and
`(a, 𝓝[univ] a, 𝓝[univ] a)`.  We use this approach to avoid repeating arguments in many very similar
cases.  Lean can automatically find both `a` and `l'` based on `l`.

The most general theorem `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` can be seen
as a generalization of lemma `integral_has_strict_fderiv_at` below which states strict
differentiability of `∫_{u}^{v} x, f x` in `(u, v)` at `(a, b)` for a measurable function `f` that
is integrable on `a..b` and is continuous at `a` and `b`. The lemma is generalized in three
directions: first, `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` deals with any
locally finite measure `μ`; second, it works for one-sided limits/derivatives; third, it assumes
only that `f` has finite limits almost surely at `a` and `b`.

Namely, let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`FTC_filter`s around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f`
has finite limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.  Then
`∫_{va}^{vb} x, f x ∂μ - ∫_{ua}^{ub} x, f x ∂μ = ∫_{ub}^{vb} x, cb ∂μ - ∫_{ua}^{va} x, ca ∂μ +
  o(‖∫_{ua}^{va} x, (1:ℝ) ∂μ‖ + ‖∫_{ub}^{vb} x, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This theorem is formulated with integral of constants instead of measures in the right hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

In the next subsection we apply this theorem to prove various theorems about differentiability
of the integral w.r.t. Lebesgue measure. -/

/-- An auxiliary typeclass for the Fundamental theorem of calculus, part 1. It is used to formulate
theorems that work simultaneously for left and right one-sided derivatives of `∫_{u}^{v} x, f x`. -/
class FTC_filter (a : out_param ℝ) (outer : filter ℝ) (inner : out_param $ filter ℝ)
  extends tendsto_Ixx_class Ioc outer inner : Prop :=
(pure_le : pure a ≤ outer)
(le_nhds : inner ≤ 𝓝 a)
[meas_gen : is_measurably_generated inner]

/- The `dangerous_instance` linter doesn't take `out_param`s into account, so it thinks that
`FTC_filter.to_tendsto_Ixx_class` is dangerous. Disable this linter using `nolint`.
-/
attribute [nolint dangerous_instance] FTC_filter.to_tendsto_Ixx_class

namespace FTC_filter

instance pure (a : ℝ) : FTC_filter a (pure a) ⊥ :=
{ pure_le := le_rfl,
  le_nhds := bot_le }

instance nhds_within_singleton (a : ℝ) : FTC_filter a (𝓝[{a}] a) ⊥ :=
by { rw [nhds_within, principal_singleton, inf_eq_right.2 (pure_le_nhds a)], apply_instance }

lemma finite_at_inner {a : ℝ} (l : filter ℝ) {l'} [h : FTC_filter a l l']
  {μ : measure ℝ} [is_locally_finite_measure μ] :
  μ.finite_at_filter l' :=
(μ.finite_at_nhds a).filter_mono h.le_nhds

instance nhds (a : ℝ) : FTC_filter a (𝓝 a) (𝓝 a) :=
{ pure_le := pure_le_nhds a,
  le_nhds := le_rfl }

instance nhds_univ (a : ℝ) : FTC_filter a (𝓝[univ] a) (𝓝 a) :=
by { rw nhds_within_univ, apply_instance }

instance nhds_left (a : ℝ) : FTC_filter a (𝓝[≤] a) (𝓝[≤] a) :=
{ pure_le := pure_le_nhds_within right_mem_Iic,
  le_nhds := inf_le_left }

instance nhds_right (a : ℝ) : FTC_filter a (𝓝[≥] a) (𝓝[>] a) :=
{ pure_le := pure_le_nhds_within left_mem_Ici,
  le_nhds := inf_le_left }

instance nhds_Icc {x a b : ℝ} [h : fact (x ∈ Icc a b)] :
  FTC_filter x (𝓝[Icc a b] x) (𝓝[Icc a b] x) :=
{ pure_le := pure_le_nhds_within h.out,
  le_nhds := inf_le_left }

instance nhds_uIcc {x a b : ℝ} [h : fact (x ∈ [a, b])] :
  FTC_filter x (𝓝[[a, b]] x) (𝓝[[a, b]] x) :=
by { haveI : fact (x ∈ set.Icc (min a b) (max a b)) := h, exact FTC_filter.nhds_Icc }

end FTC_filter

open asymptotics

section

variables {f : ℝ → E} {a b : ℝ} {c ca cb : E} {l l' la la' lb lb' : filter ℝ} {lt : filter ι}
  {μ : measure ℝ} {u v ua va ub vb : ι → ℝ}

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, where `μ` is a measure
finite at `l'`, then `∫_{u}^{v} x, f x ∂μ = ∫_{u}^{v} x, c ∂μ + o(∫_{u}^{v} x, 1 ∂μ)` as both
`u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae` for a version assuming
`[FTC_filter a l l']` and `[is_locally_finite_measure μ]`. If `l` is one of `𝓝[≥] a`,
`𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae'
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : strongly_measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hl : μ.finite_at_filter l')
  (hu : tendsto u lt l) (hv : tendsto v lt l) :
  (λ t, ∫_{u t}^{v t} x, f x ∂μ - ∫_{u t}^{v t} x, c ∂μ) =o[lt] (λ t, ∫_{u t}^{v t} x, (1:ℝ) ∂μ) :=
begin
  have A := hf.integral_sub_linear_is_o_ae hfm hl (hu.Ioc hv),
  have B := hf.integral_sub_linear_is_o_ae hfm hl (hv.Ioc hu),
  simp only [integral_const'],
  convert (A.trans_le _).sub (B.trans_le _),
  { ext t,
    simp_rw [interval_integral, sub_smul],
    abel },
  all_goals { intro t, cases le_total (u t) (v t) with huv huv; simp [huv] }
end

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫_{u}^{v} x, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both
`u` and `v` tend to `l` so that `u ≤ v`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le` for a version assuming
`[FTC_filter a l l']` and `[is_locally_finite_measure μ]`. If `l` is one of `𝓝[≥] a`,
`𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : strongly_measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hl : μ.finite_at_filter l') (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
  (λ t, ∫_{u t}^{v t} x, f x ∂μ - (μ (Ioc (u t) (v t))).to_real • c) =o[lt]
    (λ t, (μ $ Ioc (u t) (v t)).to_real) :=
(measure_integral_sub_linear_is_o_of_tendsto_ae' hfm hf hl hu hv).congr'
  (huv.mono $ λ x hx, by simp [integral_const', hx])
  (huv.mono $ λ x hx, by simp [integral_const', hx])

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫_{u}^{v} x, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both
`u` and `v` tend to `l` so that `v ≤ u`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge` for a version assuming
`[FTC_filter a l l']` and `[is_locally_finite_measure μ]`. If `l` is one of `𝓝[≥] a`,
`𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : strongly_measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hl : μ.finite_at_filter l') (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
  (λ t, ∫_{u t}^{v t} x, f x ∂μ + (μ (Ioc (v t) (u t))).to_real • c) =o[lt]
    (λ t, (μ $ Ioc (v t) (u t)).to_real) :=
(measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' hfm hf hl hv hu huv).neg_left.congr_left $
  λ t, by simp [integral_symm (u t), add_comm]

section

variables [is_locally_finite_measure μ] [FTC_filter a l l']

include a

local attribute [instance] FTC_filter.meas_gen

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫_{u}^{v} x, f x ∂μ = ∫_{u}^{v} x, c ∂μ + o(∫_{u}^{v} x, 1 ∂μ)` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae'` for a version that also works, e.g., for
`l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae (hfm : strongly_measurable_at_filter f l' μ)
  (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c)) (hu : tendsto u lt l) (hv : tendsto v lt l) :
  (λ t, ∫_{u t}^{v t} x, f x ∂μ - ∫_{u t}^{v t} x, c ∂μ) =o[lt] (λ t, ∫_{u t}^{v t} x, (1:ℝ) ∂μ) :=
measure_integral_sub_linear_is_o_of_tendsto_ae' hfm hf (FTC_filter.finite_at_inner l) hu hv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫_{u}^{v} x, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'` for a version that also works,
e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_le
  (hfm : strongly_measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
  (λ t, ∫_{u t}^{v t} x, f x ∂μ - (μ (Ioc (u t) (v t))).to_real • c) =o[lt]
    (λ t, (μ $ Ioc (u t) (v t)).to_real) :=
measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' hfm hf (FTC_filter.finite_at_inner l)
  hu hv huv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫_{u}^{v} x, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'` for a version that also works,
e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge
  (hfm : strongly_measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
  (λ t, ∫_{u t}^{v t} x, f x ∂μ + (μ (Ioc (v t) (u t))).to_real • c) =o[lt]
    (λ t, (μ $ Ioc (v t) (u t)).to_real) :=
measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge' hfm hf (FTC_filter.finite_at_inner l)
  hu hv huv

end

local attribute [instance] FTC_filter.meas_gen

variables [FTC_filter a la la'] [FTC_filter b lb lb'] [is_locally_finite_measure μ]

/-- Fundamental theorem of calculus-1, strict derivative in both limits for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f` has finite
limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.
Then `∫_{va}^{vb} x, f x ∂μ - ∫_{ua}^{ub} x, f x ∂μ =
  ∫_{ub}^{vb} x, cb ∂μ - ∫_{ua}^{va} x, ca ∂μ +
    o(‖∫_{ua}^{va} x, (1:ℝ) ∂μ‖ + ‖∫_{ub}^{vb} x, (1:ℝ) ∂μ‖)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
-/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  (hab : interval_integrable f μ a b)
  (hmeas_a : strongly_measurable_at_filter f la' μ)
  (hmeas_b : strongly_measurable_at_filter f lb' μ)
  (ha_lim : tendsto f (la' ⊓ μ.ae) (𝓝 ca)) (hb_lim : tendsto f (lb' ⊓ μ.ae) (𝓝 cb))
  (hua : tendsto ua lt la) (hva : tendsto va lt la)
  (hub : tendsto ub lt lb) (hvb : tendsto vb lt lb) :
  (λ t, (∫_{va t}^{vb t} x, f x ∂μ) - (∫_{ua t}^{ub t} x, f x ∂μ) -
    (∫_{ub t}^{vb t} x, cb ∂μ - ∫_{ua t}^{va t} x, ca ∂μ)) =o[lt]
    (λ t, ‖∫_{ua t}^{va t} x, (1:ℝ) ∂μ‖ + ‖∫_{ub t}^{vb t} x, (1:ℝ) ∂μ‖) :=
begin
  refine
    ((measure_integral_sub_linear_is_o_of_tendsto_ae hmeas_a ha_lim hua hva).neg_left.add_add
    (measure_integral_sub_linear_is_o_of_tendsto_ae hmeas_b hb_lim hub hvb)).congr'
      _ eventually_eq.rfl,
  have A : ∀ᶠ t in lt, interval_integrable f μ (ua t) (va t) :=
    ha_lim.eventually_interval_integrable_ae hmeas_a (FTC_filter.finite_at_inner la) hua hva,
  have A' : ∀ᶠ t in lt, interval_integrable f μ a (ua t) :=
    ha_lim.eventually_interval_integrable_ae hmeas_a (FTC_filter.finite_at_inner la)
      (tendsto_const_pure.mono_right FTC_filter.pure_le) hua,
  have B : ∀ᶠ t in lt, interval_integrable f μ (ub t) (vb t) :=
    hb_lim.eventually_interval_integrable_ae hmeas_b (FTC_filter.finite_at_inner lb) hub hvb,
  have B' : ∀ᶠ t in lt, interval_integrable f μ b (ub t) :=
    hb_lim.eventually_interval_integrable_ae hmeas_b (FTC_filter.finite_at_inner lb)
      (tendsto_const_pure.mono_right FTC_filter.pure_le) hub,
  filter_upwards [A, A', B, B'] with _ ua_va a_ua ub_vb b_ub,
  rw [← integral_interval_sub_interval_comm'],
  { dsimp only [], abel, },
  exacts [ub_vb, ua_va, b_ub.symm.trans $ hab.symm.trans a_ua]
end

/-- Fundamental theorem of calculus-1, strict derivative in right endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(lb, lb')` be a pair of `FTC_filter`s
around `b`. Suppose that `f` has a finite limit `c` at `lb' ⊓ μ.ae`.

Then `∫_{a}^{v} x, f x ∂μ - ∫_{a}^{u} x, f x ∂μ = ∫_{u}^{v} x, c ∂μ + o(∫_{u}^{v} x, (1:ℝ) ∂μ)`
as `u` and `v` tend to `lb`.
-/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
  (hab : interval_integrable f μ a b) (hmeas : strongly_measurable_at_filter f lb' μ)
  (hf : tendsto f (lb' ⊓ μ.ae) (𝓝 c)) (hu : tendsto u lt lb) (hv : tendsto v lt lb) :
  (λ t, ∫_{a}^{v t} x, f x ∂μ - ∫_{a}^{u t} x, f x ∂μ - ∫_{u t}^{v t} x, c ∂μ) =o[lt]
    (λ t, ∫_{u t}^{v t} x, (1:ℝ) ∂μ) :=
by simpa using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  hab strongly_measurable_at_bot hmeas ((tendsto_bot : tendsto _ ⊥ (𝓝 0)).mono_left inf_le_left)
  hf (tendsto_const_pure : tendsto _ _ (pure a)) tendsto_const_pure hu hv

/-- Fundamental theorem of calculus-1, strict derivative in left endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`. Suppose that `f` has a finite limit `c` at `la' ⊓ μ.ae`.

Then `∫_{v}^{b} x, f x ∂μ - ∫_{u}^{b} x, f x ∂μ = -∫_{u}^{v} x, c ∂μ + o(∫_{u}^{v} x, (1:ℝ) ∂μ)`
as `u` and `v` tend to `la`.
-/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
  (hab : interval_integrable f μ a b) (hmeas : strongly_measurable_at_filter f la' μ)
  (hf : tendsto f (la' ⊓ μ.ae) (𝓝 c)) (hu : tendsto u lt la) (hv : tendsto v lt la) :
  (λ t, ∫_{v t}^{b} x, f x ∂μ - ∫_{u t}^{b} x, f x ∂μ + ∫_{u t}^{v t} x, c ∂μ) =o[lt]
    (λ t, ∫_{u t}^{v t} x, (1:ℝ) ∂μ) :=
by simpa using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  hab hmeas strongly_measurable_at_bot hf ((tendsto_bot : tendsto _ ⊥ (𝓝 0)).mono_left inf_le_left)
  hu hv (tendsto_const_pure : tendsto _ _ (pure b)) tendsto_const_pure

end

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫_{u}^{v} x, f x` is strictly differentiable in `(u, v)`
at `(a, b)` provided that `f` is integrable on `a..b` and is continuous at `a` and `b`.
-/

variables {f : ℝ → E} {c ca cb : E} {l l' la la' lb lb' : filter ℝ} {lt : filter ι}
  {a b z : ℝ} {u v ua ub va vb : ι → ℝ} [FTC_filter a la la'] [FTC_filter b lb lb']

/-!
#### Auxiliary `is_o` statements

In this section we prove several lemmas that can be interpreted as strict differentiability of
`(u, v) ↦ ∫_{u}^{v} x, f x ∂μ` in `u` and/or `v` at a filter. The statements use `is_o` because
we have no definition of `has_strict_(f)deriv_at_filter` in the library.
-/

/-- Fundamental theorem of calculus-1, local version. If `f` has a finite limit `c` almost surely at
`l'`, where `(l, l')` is an `FTC_filter` pair around `a`, then
`∫_{u}^{v} x, f x ∂μ = (v - u) • c + o (v - u)` as both `u` and `v` tend to `l`. -/
lemma integral_sub_linear_is_o_of_tendsto_ae [FTC_filter a l l']
  (hfm : strongly_measurable_at_filter f l') (hf : tendsto f (l' ⊓ volume.ae) (𝓝 c))
  {u v : ι → ℝ} (hu : tendsto u lt l) (hv : tendsto v lt l) :
  (λ t, (∫_{u t}^{v t} x, f x) - (v t - u t) • c) =o[lt] (v - u) :=
by simpa [integral_const] using measure_integral_sub_linear_is_o_of_tendsto_ae hfm hf hu hv

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair around
`a`, and `(lb, lb')` is an `FTC_filter` pair around `b`, and `f` has finite limits `ca` and `cb`
almost surely at `la'` and `lb'`, respectively, then
`(∫_{va}^{vb} x, f x) - ∫_{ua}^{ub} x, f x = (vb - ub) • cb - (va - ua) • ca +
  o(‖va - ua‖ + ‖vb - ub‖)` as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This lemma could've been formulated using `has_strict_fderiv_at_filter` if we had this
definition. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  (hab : interval_integrable f volume a b)
  (hmeas_a : strongly_measurable_at_filter f la') (hmeas_b : strongly_measurable_at_filter f lb')
  (ha_lim : tendsto f (la' ⊓ volume.ae) (𝓝 ca)) (hb_lim : tendsto f (lb' ⊓ volume.ae) (𝓝 cb))
  (hua : tendsto ua lt la) (hva : tendsto va lt la)
  (hub : tendsto ub lt lb) (hvb : tendsto vb lt lb) :
  (λ t, (∫_{va t}^{vb t} x, f x) - (∫_{ua t}^{ub t} x, f x) -
    ((vb t - ub t) • cb - (va t - ua t) • ca)) =o[lt] (λ t, ‖va t - ua t‖ + ‖vb t - ub t‖) :=
by simpa [integral_const]
  using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae hab hmeas_a hmeas_b
    ha_lim hb_lim hua hva hub hvb

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(lb, lb')` is an `FTC_filter` pair
around `b`, and `f` has a finite limit `c` almost surely at `lb'`, then
`(∫_{a}^{v} x, f x) - ∫_{a}^{u} x, f x = (v - u) • c + o(‖v - u‖)` as `u` and `v` tend to `lb`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
  (hab : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f lb')
  (hf : tendsto f (lb' ⊓ volume.ae) (𝓝 c)) (hu : tendsto u lt lb) (hv : tendsto v lt lb) :
  (λ t, (∫_{a}^{v t} x, f x) - (∫_{a}^{u t} x, f x) - (v t - u t) • c) =o[lt] (v - u) :=
by simpa only [integral_const, smul_eq_mul, mul_one] using
  measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hab hmeas hf hu hv

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair
around `a`, and `f` has a finite limit `c` almost surely at `la'`, then
`(∫_{v}^{b} x, f x) - ∫_{u}^{b} x, f x = -(v - u) • c + o(‖v - u‖)` as `u` and `v` tend to `la`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
  (hab : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f la')
  (hf : tendsto f (la' ⊓ volume.ae) (𝓝 c)) (hu : tendsto u lt la) (hv : tendsto v lt la) :
  (λ t, (∫_{v t}^{b} x, f x) - (∫_{u t}^{b} x, f x) + (v t - u t) • c) =o[lt] (v - u) :=
by simpa only [integral_const, smul_eq_mul, mul_one] using
  measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left hab hmeas hf hu hv

open continuous_linear_map (fst snd smul_right sub_apply smul_right_apply coe_fst' coe_snd' map_sub)

/-!
#### Strict differentiability

In this section we prove that for a measurable function `f` integrable on `a..b`,

* `integral_has_strict_fderiv_at_of_tendsto_ae`: the function `(u, v) ↦ ∫_{u}^{v} x, f x` has
  derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of strict differentiability
  provided that `f` tends to `ca` and `cb` almost surely as `x` tendsto to `a` and `b`,
  respectively;

* `integral_has_strict_fderiv_at`: the function `(u, v) ↦ ∫_{u}^{v} x, f x` has
  derivative `(u, v) ↦ v • f b - u • f a` at `(a, b)` in the sense of strict differentiability
  provided that `f` is continuous at `a` and `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_right`: the function `u ↦ ∫_{a}^{u} x, f x` has
  derivative `c` at `b` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `b`;

* `integral_has_strict_deriv_at_right`: the function `u ↦ ∫_{a}^{u} x, f x` has derivative `f b` at
  `b` in the sense of strict differentiability provided that `f` is continuous at `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_left`: the function `u ↦ ∫_{u}^{b} x, f x` has
  derivative `-c` at `a` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `a`;

* `integral_has_strict_deriv_at_left`: the function `u ↦ ∫_{u}^{b} x, f x` has derivative `-f a` at
  `a` in the sense of strict differentiability provided that `f` is continuous at `a`.
-/

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫_{u}^{v} x, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`
in the sense of strict differentiability. -/
lemma integral_has_strict_fderiv_at_of_tendsto_ae
  (hf : interval_integrable f volume a b)
  (hmeas_a : strongly_measurable_at_filter f (𝓝 a))
  (hmeas_b : strongly_measurable_at_filter f (𝓝 b))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 cb)) :
  has_strict_fderiv_at (λ p : ℝ × ℝ, ∫_{p.1}^{p.2} x, f x)
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) (a, b) :=
begin
  have := integral_sub_integral_sub_linear_is_o_of_tendsto_ae hf hmeas_a hmeas_b ha hb
    ((continuous_fst.comp continuous_snd).tendsto ((a, b), (a, b)))
    ((continuous_fst.comp continuous_fst).tendsto ((a, b), (a, b)))
    ((continuous_snd.comp continuous_snd).tendsto ((a, b), (a, b)))
    ((continuous_snd.comp continuous_fst).tendsto ((a, b), (a, b))),
  refine (this.congr_left _).trans_is_O _,
  { intro x, simp [sub_smul] },
  { exact is_O_fst_prod.norm_left.add is_O_snd_prod.norm_left }
end

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫_{u}^{v} x, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)` in the sense of strict differentiability. -/
lemma integral_has_strict_fderiv_at
  (hf : interval_integrable f volume a b)
  (hmeas_a : strongly_measurable_at_filter f (𝓝 a))
  (hmeas_b : strongly_measurable_at_filter f (𝓝 b))
  (ha : continuous_at f a) (hb : continuous_at f b) :
  has_strict_fderiv_at (λ p : ℝ × ℝ, ∫_{p.1}^{p.2} x, f x)
    ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (a, b) :=
integral_has_strict_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b
  (ha.mono_left inf_le_left) (hb.mono_left inf_le_left)

/-- **First Fundamental Theorem of Calculus**: if `f : ℝ → E` is integrable on `a..b` and `f x` has
a finite limit `c` almost surely at `b`, then `u ↦ ∫_{a}^{u} x, f x` has derivative `c` at `b` in
the sense of strict differentiability. -/
lemma integral_has_strict_deriv_at_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 b))
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) : has_strict_deriv_at (λ u, ∫_{a}^{u} x, f x) c b :=
integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hmeas hb continuous_at_snd
  continuous_at_fst

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫_{a}^{u} x, f x` has derivative `f b` at `b` in the sense of strict
differentiability. -/
lemma integral_has_strict_deriv_at_right
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 b))
  (hb : continuous_at f b) : has_strict_deriv_at (λ u, ∫_{a}^{u} x, f x) (f b) b :=
integral_has_strict_deriv_at_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫_{u}^{b} x, f x` has derivative `-c` at `a` in the sense
of strict differentiability. -/
lemma integral_has_strict_deriv_at_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 a))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 c)) : has_strict_deriv_at (λ u, ∫_{u}^{b} x, f x) (-c) a :=
by simpa only [← integral_symm]
  using (integral_has_strict_deriv_at_of_tendsto_ae_right hf.symm hmeas ha).neg

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫_{u}^{b} x, f x` has derivative `-f a` at `a` in the sense of strict
differentiability. -/
lemma integral_has_strict_deriv_at_left
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 a))
  (ha : continuous_at f a) : has_strict_deriv_at (λ u, ∫_{u}^{b} x, f x) (-f a) a :=
by simpa only [← integral_symm] using (integral_has_strict_deriv_at_right hf.symm hmeas ha).neg

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is continuous, then `u ↦ ∫_{a}^{u} x, f x`
has derivative `f b` at `b` in the sense of strict differentiability. -/
lemma _root_.continuous.integral_has_strict_deriv_at {f : ℝ → E} (hf : continuous f) (a b : ℝ) :
  has_strict_deriv_at (λ u, ∫_{a}^{u} x, f x) (f b) b :=
integral_has_strict_deriv_at_right (hf.interval_integrable _ _)
 (hf.strongly_measurable_at_filter _ _) hf.continuous_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is continuous, then the derivative
of `u ↦ ∫_{a}^{u} x, f x` at `b` is `f b`. -/
lemma _root_.continuous.deriv_integral (f : ℝ → E) (hf : continuous f) (a b : ℝ) :
  deriv (λ u, ∫_{a}^{u} x, f x) b = f b :=
(hf.integral_has_strict_deriv_at a b).has_deriv_at.deriv

/-!
#### Fréchet differentiability

In this subsection we restate results from the previous subsection in terms of `has_fderiv_at`,
`has_deriv_at`, `fderiv`, and `deriv`.
-/

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫_{u}^{v} x, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`. -/
lemma integral_has_fderiv_at_of_tendsto_ae (hf : interval_integrable f volume a b)
  (hmeas_a : strongly_measurable_at_filter f (𝓝 a))
  (hmeas_b : strongly_measurable_at_filter f (𝓝 b))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 cb)) :
  has_fderiv_at (λ p : ℝ × ℝ, ∫_{p.1}^{p.2} x, f x)
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) (a, b) :=
(integral_has_strict_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb).has_fderiv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫_{u}^{v} x, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)`. -/
lemma integral_has_fderiv_at (hf : interval_integrable f volume a b)
  (hmeas_a : strongly_measurable_at_filter f (𝓝 a))
  (hmeas_b : strongly_measurable_at_filter f (𝓝 b))
  (ha : continuous_at f a) (hb : continuous_at f b) :
  has_fderiv_at (λ p : ℝ × ℝ, ∫_{p.1}^{p.2} x, f x)
    ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (a, b) :=
(integral_has_strict_fderiv_at hf hmeas_a hmeas_b ha hb).has_fderiv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then `fderiv`
derivative of `(u, v) ↦ ∫_{u}^{v} x, f x` at `(a, b)` equals `(u, v) ↦ v • cb - u • ca`. -/
lemma fderiv_integral_of_tendsto_ae (hf : interval_integrable f volume a b)
  (hmeas_a : strongly_measurable_at_filter f (𝓝 a))
  (hmeas_b : strongly_measurable_at_filter f (𝓝 b))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 cb)) :
  fderiv ℝ (λ p : ℝ × ℝ, ∫_{p.1}^{p.2} x, f x) (a, b) =
    (snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca :=
(integral_has_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderiv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `fderiv` derivative of `(u, v) ↦ ∫_{u}^{v} x, f x` at `(a, b)` equals `(u, v) ↦
v • cb - u • ca`. -/
lemma fderiv_integral (hf : interval_integrable f volume a b)
  (hmeas_a : strongly_measurable_at_filter f (𝓝 a))
  (hmeas_b : strongly_measurable_at_filter f (𝓝 b))
  (ha : continuous_at f a) (hb : continuous_at f b) :
  fderiv ℝ (λ p : ℝ × ℝ, ∫_{p.1}^{p.2} x, f x) (a, b) =
    (snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a) :=
(integral_has_fderiv_at hf hmeas_a hmeas_b ha hb).fderiv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `b`, then `u ↦ ∫_{a}^{u} x, f x` has derivative `c` at `b`. -/
lemma integral_has_deriv_at_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 b))
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) : has_deriv_at (λ u, ∫_{a}^{u} x, f x) c b :=
(integral_has_strict_deriv_at_of_tendsto_ae_right hf hmeas hb).has_deriv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫_{a}^{u} x, f x` has derivative `f b` at `b`. -/
lemma integral_has_deriv_at_right
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 b))
  (hb : continuous_at f b) : has_deriv_at (λ u, ∫_{a}^{u} x, f x) (f b) b :=
(integral_has_strict_deriv_at_right hf hmeas hb).has_deriv_at

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `b`, then the derivative of `u ↦ ∫_{a}^{u} x, f x` at `b` equals `c`. -/
lemma deriv_integral_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 b))
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) : deriv (λ u, ∫_{a}^{u} x, f x) b = c :=
(integral_has_deriv_at_of_tendsto_ae_right hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then the derivative of `u ↦ ∫_{a}^{u} x, f x` at `b` equals `f b`. -/
lemma deriv_integral_right
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 b))
  (hb : continuous_at f b) :
  deriv (λ u, ∫_{a}^{u} x, f x) b = f b :=
(integral_has_deriv_at_right hf hmeas hb).deriv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫_{u}^{b} x, f x` has derivative `-c` at `a`. -/
lemma integral_has_deriv_at_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 a))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 c)) : has_deriv_at (λ u, ∫_{u}^{b} x, f x) (-c) a :=
(integral_has_strict_deriv_at_of_tendsto_ae_left hf hmeas ha).has_deriv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫_{u}^{b} x, f x` has derivative `-f a` at `a`. -/
lemma integral_has_deriv_at_left
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 a))
  (ha : continuous_at f a) :
  has_deriv_at (λ u, ∫_{u}^{b} x, f x) (-f a) a :=
(integral_has_strict_deriv_at_left hf hmeas ha).has_deriv_at

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `a`, then the derivative of `u ↦ ∫_{u}^{b} x, f x` at `a` equals `-c`. -/
lemma deriv_integral_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 a))
  (hb : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 c)) : deriv (λ u, ∫_{u}^{b} x, f x) a = -c :=
(integral_has_deriv_at_of_tendsto_ae_left hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then the derivative of `u ↦ ∫_{u}^{b} x, f x` at `a` equals `-f a`. -/
lemma deriv_integral_left
  (hf : interval_integrable f volume a b) (hmeas : strongly_measurable_at_filter f (𝓝 a))
  (hb : continuous_at f a) :
  deriv (λ u, ∫_{u}^{b} x, f x) a = -f a :=
(integral_has_deriv_at_left hf hmeas hb).deriv

/-!
#### One-sided derivatives
-/

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫_{u}^{v} x, f x`
has derivative `(u, v) ↦ v • cb - u • ca` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to `ca`
and `cb` almost surely at the filters `la` and `lb` from the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
lemma integral_has_fderiv_within_at_of_tendsto_ae
  (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) la] [FTC_filter b (𝓝[t] b) lb]
  (hmeas_a : strongly_measurable_at_filter f la) (hmeas_b : strongly_measurable_at_filter f lb)
  (ha : tendsto f (la ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (lb ⊓ volume.ae) (𝓝 cb)) :
  has_fderiv_within_at (λ p : ℝ × ℝ, ∫_{p.1}^{p.2} x, f x)
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) (s ×ˢ t) (a, b) :=
begin
  rw [has_fderiv_within_at, nhds_within_prod_eq],
  have := integral_sub_integral_sub_linear_is_o_of_tendsto_ae hf hmeas_a hmeas_b ha hb
    (tendsto_const_pure.mono_right FTC_filter.pure_le : tendsto _ _ (𝓝[s] a)) tendsto_fst
    (tendsto_const_pure.mono_right FTC_filter.pure_le : tendsto _ _ (𝓝[t] b)) tendsto_snd,
  refine (this.congr_left _).trans_is_O _,
  { intro x, simp [sub_smul] },
  { exact is_O_fst_prod.norm_left.add is_O_snd_prod.norm_left }
end

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫_{u}^{v} x, f x`
has derivative `(u, v) ↦ v • f b - u • f a` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to
`f a` and `f b` at the filters `la` and `lb` from the following table. In most cases this assumption
is definitionally equal `continuous_at f _` or `continuous_within_at f _ _`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
lemma integral_has_fderiv_within_at
  (hf : interval_integrable f volume a b)
  (hmeas_a : strongly_measurable_at_filter f la) (hmeas_b : strongly_measurable_at_filter f lb)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) la] [FTC_filter b (𝓝[t] b) lb]
  (ha : tendsto f la (𝓝 $ f a)) (hb : tendsto f lb (𝓝 $ f b)) :
  has_fderiv_within_at (λ p : ℝ × ℝ, ∫_{p.1}^{p.2} x, f x)
    ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (s ×ˢ t) (a, b) :=
integral_has_fderiv_within_at_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
  (hb.mono_left inf_le_left)

/-- An auxiliary tactic closing goals `unique_diff_within_at ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`. -/
meta def unique_diff_within_at_Ici_Iic_univ : tactic unit :=
`[apply_rules [unique_diff_on.unique_diff_within_at, unique_diff_on_Ici, unique_diff_on_Iic,
  left_mem_Ici, right_mem_Iic, unique_diff_within_at_univ]]

/-- Let `f` be a measurable function integrable on `a..b`. Choose `s ∈ {Iic a, Ici a, univ}`
and `t ∈ {Iic b, Ici b, univ}`. Suppose that `f` tends to `ca` and `cb` almost surely at the filters
`la` and `lb` from the table below. Then `fderiv_within ℝ (λ p, ∫_{p.1}^{p.2} x, f x) (s ×ˢ t)`
is equal to `(u, v) ↦ u • cb - v • ca`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
lemma fderiv_within_integral_of_tendsto_ae
  (hf : interval_integrable f volume a b)
  (hmeas_a : strongly_measurable_at_filter f la) (hmeas_b : strongly_measurable_at_filter f lb)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) la] [FTC_filter b (𝓝[t] b) lb]
  (ha : tendsto f (la ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (lb ⊓ volume.ae) (𝓝 cb))
  (hs : unique_diff_within_at ℝ s a . unique_diff_within_at_Ici_Iic_univ)
  (ht : unique_diff_within_at ℝ t b . unique_diff_within_at_Ici_Iic_univ) :
  fderiv_within ℝ (λ p : ℝ × ℝ, ∫_{p.1}^{p.2} x, f x) (s ×ˢ t) (a, b) =
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) :=
(integral_has_fderiv_within_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderiv_within $ hs.prod ht

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left,
then `u ↦ ∫_{a}^{u} x, f x` has right (resp., left) derivative `c` at `b`. -/
lemma integral_has_deriv_within_at_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)]
  (hmeas : strongly_measurable_at_filter f (𝓝[t] b)) (hb : tendsto f (𝓝[t] b ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫_{a}^{u} x, f x) c s b :=
integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hmeas hb
  (tendsto_const_pure.mono_right FTC_filter.pure_le) tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `b`, then `u ↦ ∫_{a}^{u} x, f x` has left (resp., right)
derivative `f b` at `b`. -/
lemma integral_has_deriv_within_at_right
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)]
  (hmeas : strongly_measurable_at_filter f (𝓝[t] b)) (hb : continuous_within_at f t b) :
  has_deriv_within_at (λ u, ∫_{a}^{u} x, f x) (f b) s b :=
integral_has_deriv_within_at_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫_{a}^{u} x, f x` at `b` equals `c`. -/
lemma deriv_within_integral_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)]
  (hmeas: strongly_measurable_at_filter f (𝓝[t] b)) (hb : tendsto f (𝓝[t] b ⊓ volume.ae) (𝓝 c))
  (hs : unique_diff_within_at ℝ s b . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫_{a}^{u} x, f x) s b = c :=
(integral_has_deriv_within_at_of_tendsto_ae_right hf hmeas hb).deriv_within hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `b`, then the right (resp., left) derivative of
`u ↦ ∫_{a}^{u} x, f x` at `b` equals `f b`. -/
lemma deriv_within_integral_right
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)]
  (hmeas : strongly_measurable_at_filter f (𝓝[t] b)) (hb : continuous_within_at f t b)
  (hs : unique_diff_within_at ℝ s b . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫_{a}^{u} x, f x) s b = f b :=
(integral_has_deriv_within_at_right hf hmeas hb).deriv_within hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left,
then `u ↦ ∫_{u}^{b} x, f x` has right (resp., left) derivative `-c` at `a`. -/
lemma integral_has_deriv_within_at_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)]
  (hmeas : strongly_measurable_at_filter f (𝓝[t] a))
  (ha : tendsto f (𝓝[t] a ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫_{u}^{b} x, f x) (-c) s a :=
by { simp only [integral_symm b],
  exact (integral_has_deriv_within_at_of_tendsto_ae_right hf.symm hmeas ha).neg }

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `a`, then `u ↦ ∫_{u}^{b} x, f x` has left (resp., right)
derivative `-f a` at `a`. -/
lemma integral_has_deriv_within_at_left
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)]
  (hmeas : strongly_measurable_at_filter f (𝓝[t] a)) (ha : continuous_within_at f t a) :
  has_deriv_within_at (λ u, ∫_{u}^{b} x, f x) (-f a) s a :=
integral_has_deriv_within_at_of_tendsto_ae_left hf hmeas (ha.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫_{u}^{b} x, f x` at `a` equals `-c`. -/
lemma deriv_within_integral_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)]
  (hmeas : strongly_measurable_at_filter f (𝓝[t] a)) (ha : tendsto f (𝓝[t] a ⊓ volume.ae) (𝓝 c))
  (hs : unique_diff_within_at ℝ s a . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫_{u}^{b} x, f x) s a = -c :=
(integral_has_deriv_within_at_of_tendsto_ae_left hf hmeas ha).deriv_within hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `a`, then the right (resp., left) derivative of
`u ↦ ∫_{u}^{b} x, f x` at `a` equals `-f a`. -/
lemma deriv_within_integral_left
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)]
  (hmeas : strongly_measurable_at_filter f (𝓝[t] a)) (ha : continuous_within_at f t a)
  (hs : unique_diff_within_at ℝ s a . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫_{u}^{b} x, f x) s a = -f a :=
(integral_has_deriv_within_at_left hf hmeas ha).deriv_within hs

/-- The integral of a continuous function is differentiable on a real set `s`. -/
theorem differentiable_on_integral_of_continuous {s : set ℝ}
  (hintg : ∀ x ∈ s, interval_integrable f volume a x) (hcont : continuous f) :
  differentiable_on ℝ (λ u, ∫_{a}^{u} x, f x) s :=
λ y hy, (integral_has_deriv_at_right (hintg y hy)
  hcont.ae_strongly_measurable.strongly_measurable_at_filter
    hcont.continuous_at) .differentiable_at.differentiable_within_at

/-!
### Fundamental theorem of calculus, part 2

This section contains theorems pertaining to FTC-2 for interval integrals, i.e., the assertion
that `∫_{a}^{b} x, f' x = f b - f a` under suitable assumptions.

The most classical version of this theorem assumes that `f'` is continuous. However, this is
unnecessarily strong: the result holds if `f'` is just integrable. We prove the strong version,
following [Rudin, *Real and Complex Analysis* (Theorem 7.21)][rudin2006real]. The proof is first
given for real-valued functions, and then deduced for functions with a general target space. For
a real-valued function `g`, it suffices to show that `g b - g a ≤ (∫_{a}^{b} x, g' x) + ε` for all
positive `ε`. To prove this, choose a lower-semicontinuous function `G'` with `g' < G'` and with
integral close to that of `g'` (its existence is guaranteed by the Vitali-Carathéodory theorem).
It satisfies `g t - g a ≤ ∫_{a}^{t} x, G' x` for all `t ∈ [a, b]`: this inequality holds at `a`,
and if it holds at `t` then it holds for `u` close to `t` on its right, as the left hand side
increases by `g u - g t ∼ (u -t) g' t`, while the right hand side increases by
`∫_{t}^{u} x, G' x` which is roughly at least `∫_{t}^{u} x, G' t = (u - t) G' t`, by lower
semicontinuity. As  `g' t < G' t`, this gives the conclusion. One can therefore push progressively
this inequality to the right until the point `b`, where it gives the desired conclusion.
-/

variables {g' g φ : ℝ → ℝ}

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫_{a}^{b} y, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫_{a}^{b} y, φ y` when `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `[a, b)`. -/
lemma sub_le_integral_of_has_deriv_right_of_le_Ico (hab : a ≤ b) (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ico a b, has_deriv_within_at g (g' x) (Ioi x) x)
  (φint : integrable_on φ (Icc a b)) (hφg : ∀ x ∈ Ico a b, g' x ≤ φ x) :
  g b - g a ≤ ∫_{a}^{b} y, φ y :=
begin
  refine le_of_forall_pos_le_add (λ ε εpos, _),
  -- Bound from above `g'` by a lower-semicontinuous function `G'`.
  rcases exists_lt_lower_semicontinuous_integral_lt φ φint εpos with
    ⟨G', f_lt_G', G'cont, G'int, G'lt_top, hG'⟩,
  -- we will show by "induction" that `g t - g a ≤ ∫_{a}^{t} u, G' u` for all `t ∈ [a, b]`.
  set s := {t | g t - g a ≤ ∫_{a}^{t} u, (G' u).to_real} ∩ Icc a b,
  -- the set `s` of points where this property holds is closed.
  have s_closed : is_closed s,
  { have : continuous_on (λ t, (g t - g a, ∫_{a}^{t} u, (G' u).to_real)) (Icc a b),
    { rw ← uIcc_of_le hab at G'int ⊢ hcont,
      exact (hcont.sub continuous_on_const).prod (continuous_on_primitive_interval G'int) },
    simp only [s, inter_comm],
    exact this.preimage_closed_of_closed is_closed_Icc order_closed_topology.is_closed_le' },
  have main : Icc a b ⊆ {t | g t - g a ≤ ∫_{a}^{t} u, (G' u).to_real },
  { -- to show that the set `s` is all `[a, b]`, it suffices to show that any point `t` in `s`
    -- with `t < b` admits another point in `s` slightly to its right
    -- (this is a sort of real induction).
    apply s_closed.Icc_subset_of_forall_exists_gt
      (by simp only [integral_same, mem_set_of_eq, sub_self]) (λ t ht v t_lt_v, _),
    obtain ⟨y, g'_lt_y', y_lt_G'⟩ : ∃ (y : ℝ), (g' t : ereal) < y ∧ (y : ereal) < G' t :=
      ereal.lt_iff_exists_real_btwn.1 ((ereal.coe_le_coe_iff.2 (hφg t ht.2)).trans_lt (f_lt_G' t)),
    -- bound from below the increase of `∫_{a}^{u} x, G' x` on the right of `t`, using the lower
    -- semicontinuity of `G'`.
    have I1 : ∀ᶠ u in 𝓝[>] t, (u - t) * y ≤ ∫_{t}^{u} w, (G' w).to_real,
    { have B : ∀ᶠ u in 𝓝 t, (y : ereal) < G' u :=
        G'cont.lower_semicontinuous_at _ _ y_lt_G',
      rcases mem_nhds_iff_exists_Ioo_subset.1 B with ⟨m, M, ⟨hm, hM⟩, H⟩,
      have : Ioo t (min M b) ∈ 𝓝[>] t := mem_nhds_within_Ioi_iff_exists_Ioo_subset.2
        ⟨min M b, by simp only [hM, ht.right.right, lt_min_iff, mem_Ioi, and_self], subset.refl _⟩,
      filter_upwards [this] with u hu,
      have I : Icc t u ⊆ Icc a b := Icc_subset_Icc ht.2.1 (hu.2.le.trans (min_le_right _ _)),
      calc (u - t) * y = ∫ v in Icc t u, y :
        by simp only [hu.left.le, measure_theory.integral_const, algebra.id.smul_eq_mul, sub_nonneg,
                      measurable_set.univ, real.volume_Icc, measure.restrict_apply, univ_inter,
                      ennreal.to_real_of_real]
      ... ≤ ∫_{t}^{u} w, (G' w).to_real :
      begin
        rw [interval_integral.integral_of_le hu.1.le, ← integral_Icc_eq_integral_Ioc],
        apply set_integral_mono_ae_restrict,
        { simp only [integrable_on_const, real.volume_Icc, ennreal.of_real_lt_top, or_true] },
        { exact integrable_on.mono_set G'int I },
        { have C1 : ∀ᵐ (x : ℝ) ∂volume.restrict (Icc t u), G' x < ∞ :=
            ae_mono (measure.restrict_mono I le_rfl) G'lt_top,
          have C2 : ∀ᵐ (x : ℝ) ∂volume.restrict (Icc t u), x ∈ Icc t u :=
            ae_restrict_mem measurable_set_Icc,
          filter_upwards [C1, C2] with x G'x hx,
          apply ereal.coe_le_coe_iff.1,
          have : x ∈ Ioo m M, by simp only [hm.trans_le hx.left,
            (hx.right.trans_lt hu.right).trans_le (min_le_left M b), mem_Ioo, and_self],
          convert le_of_lt (H this),
          exact ereal.coe_to_real G'x.ne (ne_bot_of_gt (f_lt_G' x)) }
      end },
    -- bound from above the increase of `g u - g a` on the right of `t`, using the derivative at `t`
    have I2 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ (u - t) * y,
    { have g'_lt_y : g' t < y := ereal.coe_lt_coe_iff.1 g'_lt_y',
      filter_upwards [(hderiv t ⟨ht.2.1, ht.2.2⟩).limsup_slope_le'
        (not_mem_Ioi.2 le_rfl) g'_lt_y, self_mem_nhds_within] with u hu t_lt_u,
      have := mul_le_mul_of_nonneg_left hu.le (sub_pos.2 t_lt_u).le,
      rwa [← smul_eq_mul, sub_smul_slope] at this },
    -- combine the previous two bounds to show that `g u - g a` increases less quickly than
    -- `∫_{a}^{u} x, G' x`.
    have I3 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ ∫_{t}^{u} w, (G' w).to_real,
    { filter_upwards [I1, I2] with u hu1 hu2 using hu2.trans hu1, },
    have I4 : ∀ᶠ u in 𝓝[>] t, u ∈ Ioc t (min v b),
    { refine mem_nhds_within_Ioi_iff_exists_Ioc_subset.2 ⟨min v b, _, subset.refl _⟩,
      simp only [lt_min_iff, mem_Ioi],
      exact ⟨t_lt_v, ht.2.2⟩ },
    -- choose a point `x` slightly to the right of `t` which satisfies the above bound
    rcases (I3.and I4).exists with ⟨x, hx, h'x⟩,
    -- we check that it belongs to `s`, essentially by construction
    refine ⟨x, _, Ioc_subset_Ioc le_rfl (min_le_left _ _) h'x⟩,
    calc g x - g a = (g t - g a) + (g x - g t) : by abel
    ... ≤ (∫_{a}^{t} w, (G' w).to_real) + ∫_{t}^{x} w, (G' w).to_real : add_le_add ht.1 hx
    ... = ∫_{a}^{x} w, (G' w).to_real :
    begin
      apply integral_add_adjacent_intervals,
      { rw interval_integrable_iff_integrable_Ioc_of_le ht.2.1,
        exact integrable_on.mono_set G'int
          (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.2.le)) },
      { rw interval_integrable_iff_integrable_Ioc_of_le h'x.1.le,
        apply integrable_on.mono_set G'int,
        refine Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.2.1 (h'x.2.trans (min_le_right _ _))) }
    end },
  -- now that we know that `s` contains `[a, b]`, we get the desired result by applying this to `b`.
  calc g b - g a ≤ ∫_{a}^{b} y, (G' y).to_real : main (right_mem_Icc.2 hab)
  ... ≤ (∫_{a}^{b} y, φ y) + ε :
    begin
      convert hG'.le;
      { rw interval_integral.integral_of_le hab,
        simp only [integral_Icc_eq_integral_Ioc', real.volume_singleton] },
    end
end

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫_{a}^{b} y, g' y` when `g'` is integrable.
Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`.
We give the slightly more general version that `g b - g a ≤ ∫_{a}^{b} y, φ y` when `g' ≤ φ` and
`φ` is integrable (even if `g'` is not known to be integrable).
Version assuming that `g` is differentiable on `(a, b)`. -/
lemma sub_le_integral_of_has_deriv_right_of_le (hab : a ≤ b)
  (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_within_at g (g' x) (Ioi x) x)
  (φint : integrable_on φ (Icc a b)) (hφg : ∀ x ∈ Ioo a b, g' x ≤ φ x) :
  g b - g a ≤ ∫_{a}^{b} y, φ y :=
begin
  -- This follows from the version on a closed-open interval (applied to `[t, b)` for `t` close to
  -- `a`) and a continuity argument.
  obtain rfl|a_lt_b := hab.eq_or_lt, { simp },
  set s := {t | g b - g t ≤ ∫_{t}^{b} u, φ u} ∩ Icc a b,
  have s_closed : is_closed s,
  { have : continuous_on (λ t, (g b - g t, ∫_{t}^{b} u, φ u)) (Icc a b),
    { rw ← uIcc_of_le hab at ⊢ hcont φint,
      exact (continuous_on_const.sub hcont).prod (continuous_on_primitive_interval_left φint) },
    simp only [s, inter_comm],
    exact this.preimage_closed_of_closed is_closed_Icc is_closed_le_prod, },
  have A : closure (Ioc a b) ⊆ s,
  { apply s_closed.closure_subset_iff.2,
    assume t ht,
    refine ⟨_, ⟨ht.1.le, ht.2⟩⟩,
    exact sub_le_integral_of_has_deriv_right_of_le_Ico ht.2
      (hcont.mono (Icc_subset_Icc ht.1.le le_rfl))
      (λ x hx, hderiv x ⟨ht.1.trans_le hx.1, hx.2⟩)
      (φint.mono_set (Icc_subset_Icc ht.1.le le_rfl))
      (λ x hx, hφg x ⟨ht.1.trans_le hx.1, hx.2⟩) },
  rw closure_Ioc a_lt_b.ne at A,
  exact (A (left_mem_Icc.2 hab)).1,
end

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`. -/
lemma integral_le_sub_of_has_deriv_right_of_le (hab : a ≤ b)
  (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_within_at g (g' x) (Ioi x) x)
  (φint : integrable_on φ (Icc a b)) (hφg : ∀ x ∈ Ioo a b, φ x ≤ g' x) :
  ∫_{a}^{b} y, φ y ≤ g b - g a :=
begin
  rw ← neg_le_neg_iff,
  convert sub_le_integral_of_has_deriv_right_of_le hab hcont.neg (λ x hx, (hderiv x hx).neg)
    φint.neg (λ x hx, neg_le_neg (hφg x hx)),
  { abel },
  { simp only [← integral_neg], refl },
end

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`: real version -/
lemma integral_eq_sub_of_has_deriv_right_of_le_real (hab : a ≤ b)
  (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_within_at g (g' x) (Ioi x) x)
  (g'int : integrable_on g' (Icc a b)) :
  ∫_{a}^{b} y, g' y = g b - g a :=
le_antisymm
  (integral_le_sub_of_has_deriv_right_of_le hab hcont hderiv g'int (λ x hx, le_rfl))
  (sub_le_integral_of_has_deriv_right_of_le hab hcont hderiv g'int (λ x hx, le_rfl))

variable {f' : ℝ → E}

/-- **Fundamental theorem of calculus-2**: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`)
  and has a right derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`,
  then `∫_{a}^{b} y, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_right_of_le (hab : a ≤ b) (hcont : continuous_on f (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_within_at f (f' x) (Ioi x) x)
  (f'int : interval_integrable f' volume a b) :
  ∫_{a}^{b} y, f' y = f b - f a :=
begin
  refine (normed_space.eq_iff_forall_dual_eq ℝ).2 (λ g, _),
  rw [← g.interval_integral_comp_comm f'int, g.map_sub],
  exact integral_eq_sub_of_has_deriv_right_of_le_real hab (g.continuous.comp_continuous_on hcont)
    (λ x hx, g.has_fderiv_at.comp_has_deriv_within_at x (hderiv x hx))
    (g.integrable_comp ((interval_integrable_iff_integrable_Icc_of_le hab).1 f'int))
end

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` and
  has a right derivative at `f' x` for all `x` in `[a, b)`, and `f'` is integrable on `[a, b]` then
  `∫_{a}^{b} y, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_right (hcont : continuous_on f (uIcc a b))
  (hderiv : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hint : interval_integrable f' volume a b) :
  ∫_{a}^{b} y, f' y = f b - f a :=
begin
  cases le_total a b with hab hab,
  { simp only [uIcc_of_le, min_eq_left, max_eq_right, hab] at hcont hderiv hint,
    apply integral_eq_sub_of_has_deriv_right_of_le hab hcont hderiv hint },
  { simp only [uIcc_of_ge, min_eq_right, max_eq_left, hab] at hcont hderiv,
    rw [integral_symm, integral_eq_sub_of_has_deriv_right_of_le hab hcont hderiv hint.symm,
        neg_sub] }
end

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`) and
  has a derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`, then
  `∫_{a}^{b} y, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_at_of_le (hab : a ≤ b)
  (hcont : continuous_on f (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hint : interval_integrable f' volume a b) :
  ∫_{a}^{b} y, f' y = f b - f a :=
integral_eq_sub_of_has_deriv_right_of_le hab hcont (λ x hx, (hderiv x hx).has_deriv_within_at) hint

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` has a derivative at `f' x` for all `x` in
  `[a, b]` and `f'` is integrable on `[a, b]`, then `∫_{a}^{b} y, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_at
  (hderiv : ∀ x ∈ uIcc a b, has_deriv_at f (f' x) x)
  (hint : interval_integrable f' volume a b) :
  ∫_{a}^{b} y, f' y = f b - f a :=
integral_eq_sub_of_has_deriv_right (has_deriv_at.continuous_on hderiv)
  (λ x hx, (hderiv _ (mem_Icc_of_Ioo hx)).has_deriv_within_at) hint

theorem integral_eq_sub_of_has_deriv_at_of_tendsto (hab : a < b) {fa fb}
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hint : interval_integrable f' volume a b)
  (ha : tendsto f (𝓝[>] a) (𝓝 fa)) (hb : tendsto f (𝓝[<] b) (𝓝 fb)) :
  ∫_{a}^{b} y, f' y = fb - fa :=
begin
  set F : ℝ → E := update (update f a fa) b fb,
  have Fderiv : ∀ x ∈ Ioo a b, has_deriv_at F (f' x) x,
  { refine λ x hx, (hderiv x hx).congr_of_eventually_eq _,
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with _ hy, simp only [F],
    rw [update_noteq hy.2.ne, update_noteq hy.1.ne'], },
  have hcont : continuous_on F (Icc a b),
  { rw [continuous_on_update_iff, continuous_on_update_iff, Icc_diff_right, Ico_diff_left],
    refine ⟨⟨λ z hz, (hderiv z hz).continuous_at.continuous_within_at, _⟩, _⟩,
    { exact λ _, ha.mono_left (nhds_within_mono _ Ioo_subset_Ioi_self) },
    { rintro -,
      refine (hb.congr' _).mono_left (nhds_within_mono _ Ico_subset_Iio_self),
      filter_upwards [Ioo_mem_nhds_within_Iio (right_mem_Ioc.2 hab)]
        with _ hz using (update_noteq hz.1.ne' _ _).symm } },
  simpa [F, hab.ne, hab.ne'] using integral_eq_sub_of_has_deriv_at_of_le hab.le hcont Fderiv hint
end

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x` in `[a, b]` and
  its derivative is integrable on `[a, b]`, then `∫_{a}^{b} y, deriv f y` equals `f b - f a`. -/
theorem integral_deriv_eq_sub (hderiv : ∀ x ∈ uIcc a b, differentiable_at ℝ f x)
  (hint : interval_integrable (deriv f) volume a b) :
  ∫_{a}^{b} y, deriv f y = f b - f a :=
integral_eq_sub_of_has_deriv_at (λ x hx, (hderiv x hx).has_deriv_at) hint

theorem integral_deriv_eq_sub' (f) (hderiv : deriv f = f')
  (hdiff : ∀ x ∈ uIcc a b, differentiable_at ℝ f x)
  (hcont : continuous_on f' (uIcc a b)) :
  ∫_{a}^{b} y, f' y = f b - f a :=
begin
  rw [← hderiv, integral_deriv_eq_sub hdiff],
  rw hderiv,
  exact hcont.interval_integrable
end

/-!
### Automatic integrability for nonnegative derivatives
-/

/-- When the right derivative of a function is nonnegative, then it is automatically integrable. -/
lemma integrable_on_deriv_right_of_nonneg  (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_within_at g (g' x) (Ioi x) x)
  (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) :
  integrable_on g' (Ioc a b) :=
begin
  by_cases hab : a < b, swap,
  { simp [Ioc_eq_empty hab] },
  rw integrable_on_Ioc_iff_integrable_on_Ioo,
  have meas_g' : ae_measurable g' (volume.restrict (Ioo a b)),
  { apply (ae_measurable_deriv_within_Ioi g _).congr,
    refine (ae_restrict_mem measurable_set_Ioo).mono (λ x hx, _),
    exact (hderiv x hx).deriv_within (unique_diff_within_at_Ioi _) },
  suffices H : ∫⁻ x in Ioo a b, ‖g' x‖₊ ≤ ennreal.of_real (g b - g a),
    from ⟨meas_g'.ae_strongly_measurable, H.trans_lt ennreal.of_real_lt_top⟩,
  by_contra' H,
  obtain ⟨f, fle, fint, hf⟩ :
    ∃ (f : simple_func ℝ ℝ≥0), (∀ x, f x ≤ ‖g' x‖₊) ∧ ∫⁻ (x : ℝ) in Ioo a b, f x < ∞
      ∧ ennreal.of_real (g b - g a) < ∫⁻ (x : ℝ) in Ioo a b, f x :=
    exists_lt_lintegral_simple_func_of_lt_lintegral H,
  let F : ℝ → ℝ := coe ∘ f,
  have intF : integrable_on F (Ioo a b),
  { refine ⟨f.measurable.coe_nnreal_real.ae_strongly_measurable, _⟩,
    simpa only [has_finite_integral, nnreal.nnnorm_eq] using fint },
  have A : ∫⁻ (x : ℝ) in Ioo a b, f x = ennreal.of_real (∫ x in Ioo a b, F x) :=
    lintegral_coe_eq_integral _ intF,
  rw A at hf,
  have B : ∫ (x : ℝ) in Ioo a b, F x ≤ g b - g a,
  { rw [← integral_Ioc_eq_integral_Ioo, ← interval_integral.integral_of_le hab.le],
    apply integral_le_sub_of_has_deriv_right_of_le hab.le hcont hderiv _ (λ x hx, _),
    { rwa integrable_on_Icc_iff_integrable_on_Ioo },
    { convert nnreal.coe_le_coe.2 (fle x),
      simp only [real.norm_of_nonneg (g'pos x hx), coe_nnnorm] } },
  exact lt_irrefl _ (hf.trans_le (ennreal.of_real_le_of_real B)),
end

/-- When the derivative of a function is nonnegative, then it is automatically integrable,
Ioc version. -/
lemma integrable_on_deriv_of_nonneg (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x)
  (g'pos : ∀ x ∈ Ioo a b, 0 ≤ g' x) :
  integrable_on g' (Ioc a b) :=
integrable_on_deriv_right_of_nonneg hcont (λ x hx, (hderiv x hx).has_deriv_within_at) g'pos

/-- When the derivative of a function is nonnegative, then it is automatically integrable,
interval version. -/
theorem interval_integrable_deriv_of_nonneg (hcont : continuous_on g (uIcc a b))
  (hderiv : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_at g (g' x) x)
  (hpos : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ g' x) :
  interval_integrable g' volume a b :=
begin
  cases le_total a b with hab hab,
  { simp only [uIcc_of_le, min_eq_left, max_eq_right, hab, interval_integrable,
      hab, Ioc_eq_empty_of_le, integrable_on_empty, and_true] at hcont hderiv hpos ⊢,
    exact integrable_on_deriv_of_nonneg hcont hderiv hpos, },
  { simp only [uIcc_of_ge, min_eq_right, max_eq_left, hab, interval_integrable,
      Ioc_eq_empty_of_le, integrable_on_empty, true_and] at hcont hderiv hpos ⊢,
    exact integrable_on_deriv_of_nonneg hcont hderiv hpos }
end

/-!
### Integration by parts
-/

section parts

variables [normed_ring A] [normed_algebra ℝ A] [complete_space A]

theorem integral_deriv_mul_eq_sub {u v u' v' : ℝ → A}
  (hu : ∀ x ∈ uIcc a b, has_deriv_at u (u' x) x)
  (hv : ∀ x ∈ uIcc a b, has_deriv_at v (v' x) x)
  (hu' : interval_integrable u' volume a b) (hv' : interval_integrable v' volume a b) :
  ∫_{a}^{b} x, u' x * v x + u x * v' x = u b * v b - u a * v a :=
integral_eq_sub_of_has_deriv_at (λ x hx, (hu x hx).mul (hv x hx)) $
  (hu'.mul_continuous_on (has_deriv_at.continuous_on hv)).add
    (hv'.continuous_on_mul ((has_deriv_at.continuous_on hu)))

theorem integral_mul_deriv_eq_deriv_mul {u v u' v' : ℝ → A}
  (hu : ∀ x ∈ uIcc a b, has_deriv_at u (u' x) x)
  (hv : ∀ x ∈ uIcc a b, has_deriv_at v (v' x) x)
  (hu' : interval_integrable u' volume a b) (hv' : interval_integrable v' volume a b) :
  ∫_{a}^{b} x, u x * v' x = u b * v b - u a * v a - ∫_{a}^{b} x, u' x * v x :=
begin
  rw [← integral_deriv_mul_eq_sub hu hv hu' hv', ← integral_sub],
  { exact integral_congr (λ x hx, by simp only [add_sub_cancel']) },
  { exact ((hu'.mul_continuous_on (has_deriv_at.continuous_on hv)).add
      (hv'.continuous_on_mul (has_deriv_at.continuous_on hu))) },
  { exact hu'.mul_continuous_on (has_deriv_at.continuous_on hv) },
end

end parts

/-!
### Integration by substitution / Change of variables
-/

section smul

/--
Change of variables, general form. If `f` is continuous on `[a, b]` and has
right-derivative `f'` in `(a, b)`, `g` is continuous on `f '' (a, b)` and integrable on
`f '' [a, b]`, and `f' x • (g ∘ f) x` is integrable on `[a, b]`,
then we can substitute `u = f x` to get `∫_{a}^{b} x, f' x • (g ∘ f) x = ∫_{f a}^{f b} u, g u`.
-/
theorem integral_comp_smul_deriv''' {f f' : ℝ → ℝ} {g : ℝ → E}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hg_cont : continuous_on g (f '' Ioo (min a b) (max a b)))
  (hg1 : integrable_on g (f '' [a, b]) )
  (hg2 : integrable_on (λ x, f'(x) • (g ∘ f) x) [a, b]) :
  ∫_{a}^{b} x, f' x • (g ∘ f) x = ∫_{f a}^{f b} u, g u :=
begin
  rw [hf.image_uIcc, ←interval_integrable_iff'] at hg1,
  have h_cont : continuous_on (λ u, ∫_{f a}^{f u} t, g t) [a, b],
  { refine (continuous_on_primitive_interval' hg1 _).comp hf _,
    { rw ← hf.image_uIcc, exact mem_image_of_mem f left_mem_uIcc },
    { rw ← hf.image_uIcc, exact maps_to_image _ _ } },
  have h_der : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at
    (λ u, ∫_{f a}^{f u} t, g t) (f' x • ((g ∘ f) x)) (Ioi x) x,
  { intros x hx,
    obtain ⟨c, hc⟩ := nonempty_Ioo.mpr hx.1,
    obtain ⟨d, hd⟩ := nonempty_Ioo.mpr hx.2,
    have cdsub : [c, d] ⊆ Ioo (min a b) (max a b),
    { rw uIcc_of_le (hc.2.trans hd.1).le, exact Icc_subset_Ioo hc.1 hd.2 },
    replace hg_cont := hg_cont.mono (image_subset f cdsub),
    let J := [Inf (f '' [c, d]), Sup (f '' [c, d])],
    have hJ : f '' [c, d] = J := (hf.mono (cdsub.trans Ioo_subset_Icc_self)).image_uIcc,
    rw hJ at hg_cont,
    have h2x : f x ∈ J, { rw ←hJ, exact mem_image_of_mem _ (mem_uIcc_of_le hc.2.le hd.1.le), },
    have h2g : interval_integrable g volume (f a) (f x),
    { refine hg1.mono_set _,
      rw ←hf.image_uIcc,
      exact hf.surj_on_uIcc left_mem_uIcc (Ioo_subset_Icc_self hx) },
    have h3g := hg_cont.strongly_measurable_at_filter_nhds_within measurable_set_Icc (f x),
    haveI : fact (f x ∈ J) := ⟨h2x⟩,
    have : has_deriv_within_at (λ u, ∫_{f a}^{u} x, g x) (g (f x)) J (f x) :=
      interval_integral.integral_has_deriv_within_at_right h2g h3g (hg_cont (f x) h2x),
    refine (this.scomp x ((hff' x hx).Ioo_of_Ioi hd.1) _).Ioi_of_Ioo hd.1,
    rw ←hJ,
    refine (maps_to_image _ _).mono _ subset.rfl,
    exact Ioo_subset_Icc_self.trans ((Icc_subset_Icc_left hc.2.le).trans Icc_subset_uIcc) },
  rw ←interval_integrable_iff' at hg2,
  simp_rw [integral_eq_sub_of_has_deriv_right h_cont h_der hg2, integral_same, sub_zero],
end

/--
Change of variables for continuous integrands. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫_{a}^{b} x, f' x • (g ∘ f) x = ∫_{f a}^{f b} u, g u`.
-/
theorem integral_comp_smul_deriv'' {f f' : ℝ → ℝ} {g : ℝ → E}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hf' : continuous_on f' [a, b])
  (hg : continuous_on g (f '' [a, b])) :
  ∫_{a}^{b} x, f' x • (g ∘ f) x = ∫_{f a}^{f b} u, g u :=
begin
  refine integral_comp_smul_deriv''' hf hff'
    (hg.mono $ image_subset _ Ioo_subset_Icc_self) _
    (hf'.smul (hg.comp hf $ subset_preimage_image f _)).integrable_on_Icc,
  rw hf.image_uIcc at hg ⊢,
  exact hg.integrable_on_Icc,
end

/--
Change of variables. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫_{a}^{b} x, f' x • (g ∘ f) x = ∫_{f a}^{f b} u, g u`.
Compared to `interval_integral.integral_comp_smul_deriv` we only require that `g` is continuous on
`f '' [a, b]`.
-/
theorem integral_comp_smul_deriv' {f f' : ℝ → ℝ} {g : ℝ → E}
  (h : ∀ x ∈ uIcc a b, has_deriv_at f (f' x) x)
  (h' : continuous_on f' (uIcc a b)) (hg : continuous_on g (f '' [a, b])) :
  ∫_{a}^{b} x, f' x • (g ∘ f) x = ∫_{f a}^{f b} x, g x :=
integral_comp_smul_deriv'' (λ x hx, (h x hx).continuous_at.continuous_within_at)
  (λ x hx, (h x $ Ioo_subset_Icc_self hx).has_deriv_within_at) h' hg

/--
Change of variables, most common version. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫_{a}^{b} x, f' x • (g ∘ f) x = ∫_{f a}^{f b} u, g u`.
-/
theorem integral_comp_smul_deriv {f f' : ℝ → ℝ} {g : ℝ → E}
  (h : ∀ x ∈ uIcc a b, has_deriv_at f (f' x) x)
  (h' : continuous_on f' (uIcc a b)) (hg : continuous g) :
  ∫_{a}^{b} x, f' x • (g ∘ f) x = ∫_{f a}^{f b} x, g x :=
integral_comp_smul_deriv' h h' hg.continuous_on

theorem integral_deriv_comp_smul_deriv' {f f' : ℝ → ℝ} {g g' : ℝ → E}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hf' : continuous_on f' [a, b])
  (hg : continuous_on g [f a, f b])
  (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), has_deriv_within_at g (g' x) (Ioi x) x)
  (hg' : continuous_on g' (f '' [a, b])) :
  ∫_{a}^{b} x, f' x • (g' ∘ f) x = (g ∘ f) b - (g ∘ f) a :=
begin
  rw [integral_comp_smul_deriv'' hf hff' hf' hg',
  integral_eq_sub_of_has_deriv_right hg hgg' (hg'.mono _).interval_integrable],
  exact intermediate_value_uIcc hf
end

theorem integral_deriv_comp_smul_deriv {f f' : ℝ → ℝ} {g g' : ℝ → E}
  (hf : ∀ x ∈ uIcc a b, has_deriv_at f (f' x) x)
  (hg : ∀ x ∈ uIcc a b, has_deriv_at g (g' (f x)) (f x))
  (hf' : continuous_on f' (uIcc a b)) (hg' : continuous g') :
  ∫_{a}^{b} x, f' x • (g' ∘ f) x = (g ∘ f) b - (g ∘ f) a :=
integral_eq_sub_of_has_deriv_at (λ x hx, (hg x hx).scomp x $ hf x hx)
  (hf'.smul (hg'.comp_continuous_on $ has_deriv_at.continuous_on hf)).interval_integrable

end smul
section mul

/--
Change of variables, general form for scalar functions. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, `g` is continuous on `f '' (a, b)` and integrable on
`f '' [a, b]`, and `(g ∘ f) x * f' x` is integrable on `[a, b]`, then we can substitute `u = f x`
to get `∫_{a}^{b} x, (g ∘ f) x * f' x = ∫_{f a}^{f b} u, g u`.
-/
theorem integral_comp_mul_deriv''' {a b : ℝ} {f f' : ℝ → ℝ} {g : ℝ → ℝ}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hg_cont : continuous_on g (f '' Ioo (min a b) (max a b)))
  (hg1 : integrable_on g (f '' [a, b]) )
  (hg2 : integrable_on (λ x, (g ∘ f) x * f' x) [a, b]) :
  ∫_{a}^{b} x, (g ∘ f) x * f' x = ∫_{f a}^{f b} u, g u :=
begin
  have hg2' : integrable_on (λ x, f' x • (g ∘ f) x) [a, b] := by simpa [mul_comm] using hg2,
  simpa [mul_comm] using integral_comp_smul_deriv''' hf hff' hg_cont hg1 hg2',
end

/--
Change of variables for continuous integrands. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫_{a}^{b} x, (g ∘ f) x * f' x = ∫_{f a}^{f b} u, g u`.
-/
theorem integral_comp_mul_deriv'' {f f' g : ℝ → ℝ}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hf' : continuous_on f' [a, b])
  (hg : continuous_on g (f '' [a, b])) :
  ∫_{a}^{b} x, (g ∘ f) x * f' x = ∫_{f a}^{f b} u, g u :=
by simpa [mul_comm] using integral_comp_smul_deriv'' hf hff' hf' hg

/--
Change of variables. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫_{a}^{b} x, (g ∘ f) x * f' x = ∫_{f a}^{f b} u, g u`.
Compared to `interval_integral.integral_comp_mul_deriv` we only require that `g` is continuous on
`f '' [a, b]`.
-/
theorem integral_comp_mul_deriv' {f f' g : ℝ → ℝ}
  (h : ∀ x ∈ uIcc a b, has_deriv_at f (f' x) x)
  (h' : continuous_on f' (uIcc a b)) (hg : continuous_on g (f '' [a, b])) :
  ∫_{a}^{b} x, (g ∘ f) x * f' x = ∫_{f a}^{f b} x, g x :=
by simpa [mul_comm] using integral_comp_smul_deriv' h h' hg

/--
Change of variables, most common version. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫_{a}^{b} x, (g ∘ f) x * f' x = ∫_{f a}^{f b} u, g u`.
-/
theorem integral_comp_mul_deriv {f f' g : ℝ → ℝ}
  (h : ∀ x ∈ uIcc a b, has_deriv_at f (f' x) x)
  (h' : continuous_on f' (uIcc a b)) (hg : continuous g) :
  ∫_{a}^{b} x, (g ∘ f) x * f' x = ∫_{f a}^{f b} x, g x :=
integral_comp_mul_deriv' h h' hg.continuous_on

theorem integral_deriv_comp_mul_deriv' {f f' g g' : ℝ → ℝ}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hf' : continuous_on f' [a, b])
  (hg : continuous_on g [f a, f b])
  (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), has_deriv_within_at g (g' x) (Ioi x) x)
  (hg' : continuous_on g' (f '' [a, b])) :
  ∫_{a}^{b} x, (g' ∘ f) x * f' x = (g ∘ f) b - (g ∘ f) a :=
by simpa [mul_comm] using integral_deriv_comp_smul_deriv' hf hff' hf' hg hgg' hg'

theorem integral_deriv_comp_mul_deriv {f f' g g' : ℝ → ℝ}
  (hf : ∀ x ∈ uIcc a b, has_deriv_at f (f' x) x)
  (hg : ∀ x ∈ uIcc a b, has_deriv_at g (g' (f x)) (f x))
  (hf' : continuous_on f' (uIcc a b)) (hg' : continuous g') :
  ∫_{a}^{b} x, (g' ∘ f) x * f' x = (g ∘ f) b - (g ∘ f) a :=
by simpa [mul_comm] using integral_deriv_comp_smul_deriv hf hg hf' hg'

end mul

end interval_integral
