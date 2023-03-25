/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.asymptotics.asymptotic_equivalent
import analysis.calculus.tangent_cone
import analysis.normed_space.bounded_linear_maps
import analysis.normed_space.units

/-!
# The Fréchet derivative

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `has_fderiv_within_at f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_within_at f f' x univ`

Finally,

  `has_strict_fderiv_at f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`is_bounded_bilinear_map.has_fderiv_at` twice: first for `has_fderiv_at`, then for
`has_strict_fderiv_at`.

## Main results

In addition to the definition and basic properties of the derivative, this file contains the
usual formulas (and existence assertions) for the derivative of
* constants
* the identity
* bounded linear maps
* bounded bilinear maps
* sum of two functions
* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
* multiplication of a function by a scalar function
* multiplication of two scalar functions
* composition of functions (the chain rule)
* inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : differentiable ℝ (λ x, sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : differentiable_at ℝ (λ x, exp x / (1 + sin x)) x :=
by simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `analysis.special_functions.trigonometric`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `deriv.lean`.

## Implementation details

The derivative is defined in terms of the `is_o` relation, but also
characterized in terms of the `tendsto` relation.

We also introduce predicates `differentiable_within_at 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `differentiable_at 𝕜 f x`,
`differentiable_on 𝕜 f s` and `differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderiv_within 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `unique_diff_within_at s x` and
`unique_diff_on s`, defined in `tangent_cone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(λ x, exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

Tests for this ability of the simplifier (with more examples) are provided in
`tests/differentiable.lean`.

## Tags

derivative, differentiable, Fréchet, calculus

-/

open filter asymptotics continuous_linear_map set metric
open_locale topology classical nnreal filter asymptotics ennreal

noncomputable theory


section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']

/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` converges along the filter `L`. This definition
is designed to be specialized for `L = 𝓝 x` (in `has_fderiv_at`), giving rise to the usual notion
of Fréchet derivative, and for `L = 𝓝[s] x` (in `has_fderiv_within_at`), giving rise to
the notion of Fréchet derivative along the set `s`. -/
def has_fderiv_at_filter (f : E → F) (f' : E →L[𝕜] F) (x : E) (L : filter E) :=
(λ x', f x' - f x - f' (x' - x)) =o[L] (λ x', x' - x)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` within a set `s` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x` inside `s`. -/
def has_fderiv_within_at (f : E → F) (f' : E →L[𝕜] F) (s : set E) (x : E) :=
has_fderiv_at_filter f f' x (𝓝[s] x)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x`. -/
def has_fderiv_at (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
has_fderiv_at_filter f f' x (𝓝 x)

/-- A function `f` has derivative `f'` at `a` in the sense of *strict differentiability*
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. This form of differentiability is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
def has_strict_fderiv_at (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
(λ p : E × E, f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x, x)] (λ p : E × E, p.1 - p.2)

variables (𝕜)

/-- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
def differentiable_within_at (f : E → F) (s : set E) (x : E) :=
∃f' : E →L[𝕜] F, has_fderiv_within_at f f' s x

/-- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
def differentiable_at (f : E → F) (x : E) :=
∃f' : E →L[𝕜] F, has_fderiv_at f f' x

/-- If `f` has a derivative at `x` within `s`, then `fderiv_within 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. -/
def fderiv_within (f : E → F) (s : set E) (x : E) : E →L[𝕜] F :=
if h : ∃f', has_fderiv_within_at f f' s x then classical.some h else 0

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
if h : ∃f', has_fderiv_at f f' x then classical.some h else 0

/-- `differentiable_on 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
def differentiable_on (f : E → F) (s : set E) :=
∀x ∈ s, differentiable_within_at 𝕜 f s x

/-- `differentiable 𝕜 f` means that `f` is differentiable at any point. -/
def differentiable (f : E → F) :=
∀x, differentiable_at 𝕜 f x

variables {𝕜}
variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[𝕜] F}
variables (e : E →L[𝕜] F)
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}

lemma fderiv_within_zero_of_not_differentiable_within_at
  (h : ¬ differentiable_within_at 𝕜 f s x) : fderiv_within 𝕜 f s x = 0 :=
have ¬ ∃ f', has_fderiv_within_at f f' s x, from h,
by simp [fderiv_within, this]

lemma fderiv_zero_of_not_differentiable_at (h : ¬ differentiable_at 𝕜 f x) : fderiv 𝕜 f x = 0 :=
have ¬ ∃ f', has_fderiv_at f f' x, from h,
by simp [fderiv, this]

section derivative_uniqueness
/- In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `unique_diff_within_at` and `unique_diff_on` indeed imply the
uniqueness of the derivative. -/

/-- If a function f has a derivative f' at x, a rescaled version of f around x converges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `c n` tends to infinity
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `f' v`. This lemma expresses
this fact, for functions having a derivative within a set. Its specific formulation is useful for
tangent cone related discussions. -/
theorem has_fderiv_within_at.lim (h : has_fderiv_within_at f f' s x) {α : Type*} (l : filter α)
  {c : α → 𝕜} {d : α → E} {v : E} (dtop : ∀ᶠ n in l, x + d n ∈ s)
  (clim : tendsto (λ n, ‖c n‖) l at_top)
  (cdlim : tendsto (λ n, c n • d n) l (𝓝 v)) :
  tendsto (λn, c n • (f (x + d n) - f x)) l (𝓝 (f' v)) :=
begin
  have tendsto_arg : tendsto (λ n, x + d n) l (𝓝[s] x),
  { conv in (𝓝[s] x) { rw ← add_zero x },
    rw [nhds_within, tendsto_inf],
    split,
    { apply tendsto_const_nhds.add (tangent_cone_at.lim_zero l clim cdlim) },
    { rwa tendsto_principal } },
  have : (λ y, f y - f x - f' (y - x)) =o[𝓝[s] x] (λ y, y - x) := h,
  have : (λ n, f (x + d n) - f x - f' ((x + d n) - x)) =o[l] (λ n, (x + d n)  - x) :=
    this.comp_tendsto tendsto_arg,
  have : (λ n, f (x + d n) - f x - f' (d n)) =o[l] d := by simpa only [add_sub_cancel'],
  have : (λ n, c n • (f (x + d n) - f x - f' (d n))) =o[l] (λ n, c n • d n) :=
    (is_O_refl c l).smul_is_o this,
  have : (λ n, c n • (f (x + d n) - f x - f' (d n))) =o[l] (λ n, (1:ℝ)) :=
    this.trans_is_O (cdlim.is_O_one ℝ),
  have L1 : tendsto (λn, c n • (f (x + d n) - f x - f' (d n))) l (𝓝 0) :=
    (is_o_one_iff ℝ).1 this,
  have L2 : tendsto (λn, f' (c n • d n)) l (𝓝 (f' v)) :=
    tendsto.comp f'.cont.continuous_at cdlim,
  have L3 : tendsto (λn, (c n • (f (x + d n) - f x - f' (d n)) +  f' (c n • d n)))
            l (𝓝 (0 + f' v)) :=
    L1.add L2,
  have : (λn, (c n • (f (x + d n) - f x - f' (d n)) +  f' (c n • d n)))
          = (λn, c n • (f (x + d n) - f x)),
    by { ext n, simp [smul_add, smul_sub] },
  rwa [this, zero_add] at L3
end

/-- If `f'` and `f₁'` are two derivatives of `f` within `s` at `x`, then they are equal on the
tangent cone to `s` at `x` -/
theorem has_fderiv_within_at.unique_on (hf : has_fderiv_within_at f f' s x)
  (hg : has_fderiv_within_at f f₁' s x) :
  eq_on f' f₁' (tangent_cone_at 𝕜 s x) :=
λ y ⟨c, d, dtop, clim, cdlim⟩,
  tendsto_nhds_unique (hf.lim at_top dtop clim cdlim) (hg.lim at_top dtop clim cdlim)

/-- `unique_diff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem unique_diff_within_at.eq (H : unique_diff_within_at 𝕜 s x)
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
continuous_linear_map.ext_on H.1 (hf.unique_on hg)

theorem unique_diff_on.eq (H : unique_diff_on 𝕜 s) (hx : x ∈ s)
  (h : has_fderiv_within_at f f' s x) (h₁ : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
(H x hx).eq h h₁

end derivative_uniqueness

section fderiv_properties
/-! ### Basic properties of the derivative -/

theorem has_fderiv_at_filter_iff_tendsto :
  has_fderiv_at_filter f f' x L ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) :=
have h : ∀ x', ‖x' - x‖ = 0 → ‖f x' - f x - f' (x' - x)‖ = 0, from λ x' hx',
  by { rw [sub_eq_zero.1 (norm_eq_zero.1 hx')], simp },
begin
  unfold has_fderiv_at_filter,
  rw [←is_o_norm_left, ←is_o_norm_right, is_o_iff_tendsto h],
  exact tendsto_congr (λ _, div_eq_inv_mul _ _),
end

theorem has_fderiv_within_at_iff_tendsto : has_fderiv_within_at f f' s x ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝[s] x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_tendsto : has_fderiv_at f f' x ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_is_o_nhds_zero : has_fderiv_at f f' x ↔
  (λ h : E, f (x + h) - f x - f' h) =o[𝓝 0] (λh, h) :=
begin
  rw [has_fderiv_at, has_fderiv_at_filter, ← map_add_left_nhds_zero x, is_o_map],
  simp [(∘)]
end

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
lemma has_fderiv_at.le_of_lip' {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : has_fderiv_at f f' x₀)
  {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) : ‖f'‖ ≤ C :=
begin
  refine le_of_forall_pos_le_add (λ ε ε0, op_norm_le_of_nhds_zero _ _),
  exact add_nonneg hC₀ ε0.le,
  rw [← map_add_left_nhds_zero x₀, eventually_map] at hlip,
  filter_upwards [is_o_iff.1 (has_fderiv_at_iff_is_o_nhds_zero.1 hf) ε0, hlip] with y hy hyC,
  rw add_sub_cancel' at hyC,
  calc ‖f' y‖ ≤ ‖f (x₀ + y) - f x₀‖ + ‖f (x₀ + y) - f x₀ - f' y‖ : norm_le_insert _ _
          ... ≤ C * ‖y‖ + ε * ‖y‖                                : add_le_add hyC hy
          ... = (C + ε) * ‖y‖                                    : (add_mul _ _ _).symm
end

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`. -/
lemma has_fderiv_at.le_of_lip {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : has_fderiv_at f f' x₀)
  {s : set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : lipschitz_on_with C f s) : ‖f'‖ ≤ C :=
begin
  refine hf.le_of_lip' C.coe_nonneg _,
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs),
end

theorem has_fderiv_at_filter.mono (h : has_fderiv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) :
  has_fderiv_at_filter f f' x L₁ :=
h.mono hst

theorem has_fderiv_within_at.mono_of_mem (h : has_fderiv_within_at f f' t x) (hst : t ∈ 𝓝[s] x) :
  has_fderiv_within_at f f' s x :=
h.mono $ nhds_within_le_iff.mpr hst

theorem has_fderiv_within_at.mono (h : has_fderiv_within_at f f' t x) (hst : s ⊆ t) :
  has_fderiv_within_at f f' s x :=
h.mono $ nhds_within_mono _ hst

theorem has_fderiv_at.has_fderiv_at_filter (h : has_fderiv_at f f' x) (hL : L ≤ 𝓝 x) :
  has_fderiv_at_filter f f' x L :=
h.mono hL

theorem has_fderiv_at.has_fderiv_within_at
  (h : has_fderiv_at f f' x) : has_fderiv_within_at f f' s x :=
h.has_fderiv_at_filter inf_le_left

lemma has_fderiv_within_at.differentiable_within_at (h : has_fderiv_within_at f f' s x) :
  differentiable_within_at 𝕜 f s x :=
⟨f', h⟩

lemma has_fderiv_at.differentiable_at (h : has_fderiv_at f f' x) : differentiable_at 𝕜 f x :=
⟨f', h⟩

@[simp] lemma has_fderiv_within_at_univ :
  has_fderiv_within_at f f' univ x ↔ has_fderiv_at f f' x :=
by { simp only [has_fderiv_within_at, nhds_within_univ], refl }

alias has_fderiv_within_at_univ ↔ has_fderiv_within_at.has_fderiv_at_of_univ _

lemma has_fderiv_within_at_insert {y : E} {g' : E →L[𝕜] F}  :
  has_fderiv_within_at g g' (insert y s) x ↔ has_fderiv_within_at g g' s x :=
begin
  rcases eq_or_ne x y with rfl|h,
  { simp_rw [has_fderiv_within_at, has_fderiv_at_filter],
    apply asymptotics.is_o_insert,
    simp only [sub_self, g'.map_zero] },
  refine ⟨λ h, h.mono $ subset_insert y s, λ hg, hg.mono_of_mem _⟩,
  simp_rw [nhds_within_insert_of_ne h, self_mem_nhds_within]
end

alias has_fderiv_within_at_insert ↔ has_fderiv_within_at.of_insert has_fderiv_within_at.insert'

lemma has_fderiv_within_at.insert {g' : E →L[𝕜] F} (h : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at g g' (insert x s) x :=
h.insert'

lemma has_strict_fderiv_at.is_O_sub (hf : has_strict_fderiv_at f f' x) :
  (λ p : E × E, f p.1 - f p.2) =O[𝓝 (x, x)] (λ p : E × E, p.1 - p.2) :=
hf.is_O.congr_of_sub.2 (f'.is_O_comp _ _)

lemma has_fderiv_at_filter.is_O_sub (h : has_fderiv_at_filter f f' x L) :
  (λ x', f x' - f x) =O[L] (λ x', x' - x) :=
h.is_O.congr_of_sub.2 (f'.is_O_sub _ _)

protected lemma has_strict_fderiv_at.has_fderiv_at (hf : has_strict_fderiv_at f f' x) :
  has_fderiv_at f f' x :=
begin
  rw [has_fderiv_at, has_fderiv_at_filter, is_o_iff],
  exact (λ c hc, tendsto_id.prod_mk_nhds tendsto_const_nhds (is_o_iff.1 hf hc))
end

protected lemma has_strict_fderiv_at.differentiable_at (hf : has_strict_fderiv_at f f' x) :
  differentiable_at 𝕜 f x :=
hf.has_fderiv_at.differentiable_at

/-- If `f` is strictly differentiable at `x` with derivative `f'` and `K > ‖f'‖₊`, then `f` is
`K`-Lipschitz in a neighborhood of `x`. -/
lemma has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt (hf : has_strict_fderiv_at f f' x)
  (K : ℝ≥0) (hK : ‖f'‖₊ < K) : ∃ s ∈ 𝓝 x, lipschitz_on_with K f s :=
begin
  have := hf.add_is_O_with (f'.is_O_with_comp _ _) hK,
  simp only [sub_add_cancel, is_O_with] at this,
  rcases exists_nhds_square this with ⟨U, Uo, xU, hU⟩,
  exact ⟨U, Uo.mem_nhds xU, lipschitz_on_with_iff_norm_sub_le.2 $
    λ x hx y hy, hU (mk_mem_prod hx hy)⟩
end

/-- If `f` is strictly differentiable at `x` with derivative `f'`, then `f` is Lipschitz in a
neighborhood of `x`. See also `has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt` for a
more precise statement. -/
lemma has_strict_fderiv_at.exists_lipschitz_on_with (hf : has_strict_fderiv_at f f' x) :
  ∃ K (s ∈ 𝓝 x), lipschitz_on_with K f s :=
(exists_gt _).imp hf.exists_lipschitz_on_with_of_nnnorm_lt

/-- Directional derivative agrees with `has_fderiv`. -/
lemma has_fderiv_at.lim (hf : has_fderiv_at f f' x) (v : E) {α : Type*} {c : α → 𝕜}
  {l : filter α} (hc : tendsto (λ n, ‖c n‖) l at_top) :
  tendsto (λ n, (c n) • (f (x + (c n)⁻¹ • v) - f x)) l (𝓝 (f' v)) :=
begin
  refine (has_fderiv_within_at_univ.2 hf).lim _ univ_mem hc _,
  assume U hU,
  refine (eventually_ne_of_tendsto_norm_at_top hc (0:𝕜)).mono (λ y hy, _),
  convert mem_of_mem_nhds hU,
  dsimp only,
  rw [← mul_smul, mul_inv_cancel hy, one_smul]
end

theorem has_fderiv_at.unique
  (h₀ : has_fderiv_at f f₀' x) (h₁ : has_fderiv_at f f₁' x) : f₀' = f₁' :=
begin
  rw ← has_fderiv_within_at_univ at h₀ h₁,
  exact unique_diff_within_at_univ.eq h₀ h₁
end

lemma has_fderiv_within_at_inter' (h : t ∈ 𝓝[s] x) :
  has_fderiv_within_at f f' (s ∩ t) x ↔ has_fderiv_within_at f f' s x :=
by simp [has_fderiv_within_at, nhds_within_restrict'' s h]

lemma has_fderiv_within_at_inter (h : t ∈ 𝓝 x) :
  has_fderiv_within_at f f' (s ∩ t) x ↔ has_fderiv_within_at f f' s x :=
by simp [has_fderiv_within_at, nhds_within_restrict' s h]

lemma has_fderiv_within_at.union (hs : has_fderiv_within_at f f' s x)
  (ht : has_fderiv_within_at f f' t x) :
  has_fderiv_within_at f f' (s ∪ t) x :=
begin
  simp only [has_fderiv_within_at, nhds_within_union],
  exact hs.sup ht,
end

lemma has_fderiv_within_at.nhds_within (h : has_fderiv_within_at f f' s x)
  (ht : s ∈ 𝓝[t] x) : has_fderiv_within_at f f' t x :=
(has_fderiv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))

lemma has_fderiv_within_at.has_fderiv_at (h : has_fderiv_within_at f f' s x) (hs : s ∈ 𝓝 x) :
  has_fderiv_at f f' x :=
by rwa [← univ_inter s, has_fderiv_within_at_inter hs, has_fderiv_within_at_univ] at h

lemma differentiable_within_at.differentiable_at
  (h : differentiable_within_at 𝕜 f s x) (hs : s ∈ 𝓝 x) : differentiable_at 𝕜 f x :=
h.imp (λ f' hf', hf'.has_fderiv_at hs)

lemma differentiable_within_at.has_fderiv_within_at (h : differentiable_within_at 𝕜 f s x) :
  has_fderiv_within_at f (fderiv_within 𝕜 f s x) s x :=
begin
  dunfold fderiv_within,
  dunfold differentiable_within_at at h,
  rw dif_pos h,
  exact classical.some_spec h
end

lemma differentiable_at.has_fderiv_at (h : differentiable_at 𝕜 f x) :
  has_fderiv_at f (fderiv 𝕜 f x) x :=
begin
  dunfold fderiv,
  dunfold differentiable_at at h,
  rw dif_pos h,
  exact classical.some_spec h
end

lemma differentiable_on.has_fderiv_at (h : differentiable_on 𝕜 f s) (hs : s ∈ 𝓝 x) :
  has_fderiv_at f (fderiv 𝕜 f x) x :=
((h x (mem_of_mem_nhds hs)).differentiable_at hs).has_fderiv_at

lemma differentiable_on.differentiable_at (h : differentiable_on 𝕜 f s) (hs : s ∈ 𝓝 x) :
  differentiable_at 𝕜 f x :=
(h.has_fderiv_at hs).differentiable_at

lemma differentiable_on.eventually_differentiable_at (h : differentiable_on 𝕜 f s) (hs : s ∈ 𝓝 x) :
  ∀ᶠ y in 𝓝 x, differentiable_at 𝕜 f y :=
(eventually_eventually_nhds.2 hs).mono $ λ y, h.differentiable_at

lemma has_fderiv_at.fderiv (h : has_fderiv_at f f' x) : fderiv 𝕜 f x = f' :=
by { ext, rw h.unique h.differentiable_at.has_fderiv_at }

lemma fderiv_eq {f' : E → E →L[𝕜] F} (h : ∀ x, has_fderiv_at f (f' x) x) : fderiv 𝕜 f = f' :=
funext $ λ x, (h x).fderiv

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
lemma fderiv_at.le_of_lip {f : E → F} {x₀ : E} (hf : differentiable_at 𝕜 f x₀)
  {s : set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : lipschitz_on_with C f s) : ‖fderiv 𝕜 f x₀‖ ≤ C :=
hf.has_fderiv_at.le_of_lip hs hlip

lemma has_fderiv_within_at.fderiv_within
  (h : has_fderiv_within_at f f' s x) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 f s x = f' :=
(hxs.eq h h.differentiable_within_at.has_fderiv_within_at).symm

/-- If `x` is not in the closure of `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
lemma has_fderiv_within_at_of_not_mem_closure (h : x ∉ closure s) :
  has_fderiv_within_at f f' s x :=
begin
  simp only [mem_closure_iff_nhds_within_ne_bot, ne_bot_iff, ne.def, not_not] at h,
  simp [has_fderiv_within_at, has_fderiv_at_filter, h, is_o, is_O_with],
end

lemma differentiable_within_at.mono (h : differentiable_within_at 𝕜 f t x) (st : s ⊆ t) :
  differentiable_within_at 𝕜 f s x :=
begin
  rcases h with ⟨f', hf'⟩,
  exact ⟨f', hf'.mono st⟩
end

lemma differentiable_within_at.mono_of_mem (h : differentiable_within_at 𝕜 f s x) {t : set E}
  (hst : s ∈ nhds_within x t) :
  differentiable_within_at 𝕜 f t x :=
(h.has_fderiv_within_at.mono_of_mem hst).differentiable_within_at

lemma differentiable_within_at_univ :
  differentiable_within_at 𝕜 f univ x ↔ differentiable_at 𝕜 f x :=
by simp only [differentiable_within_at, has_fderiv_within_at_univ, differentiable_at]

lemma differentiable_within_at_inter (ht : t ∈ 𝓝 x) :
  differentiable_within_at 𝕜 f (s ∩ t) x ↔ differentiable_within_at 𝕜 f s x :=
by simp only [differentiable_within_at, has_fderiv_within_at, has_fderiv_at_filter,
    nhds_within_restrict' s ht]

lemma differentiable_within_at_inter' (ht : t ∈ 𝓝[s] x) :
  differentiable_within_at 𝕜 f (s ∩ t) x ↔ differentiable_within_at 𝕜 f s x :=
by simp only [differentiable_within_at, has_fderiv_within_at, has_fderiv_at_filter,
    nhds_within_restrict'' s ht]

lemma differentiable_within_at.antimono (h : differentiable_within_at 𝕜 f s x) (hst : s ⊆ t)
  (hx : s ∈ 𝓝[t] x) :
  differentiable_within_at 𝕜 f t x :=
by rwa [← differentiable_within_at_inter' hx, inter_eq_self_of_subset_right hst]

lemma has_fderiv_within_at.antimono (h : has_fderiv_within_at f f' s x) (hst : s ⊆ t)
  (hs : unique_diff_within_at 𝕜 s x) (hx : s ∈ 𝓝[t] x) :
  has_fderiv_within_at f f' t x :=
begin
  have h' : has_fderiv_within_at f _ t x :=
    (h.differentiable_within_at.antimono hst hx).has_fderiv_within_at,
  rwa hs.eq h (h'.mono hst),
end

lemma differentiable_at.differentiable_within_at
  (h : differentiable_at 𝕜 f x) : differentiable_within_at 𝕜 f s x :=
(differentiable_within_at_univ.2 h).mono (subset_univ _)

lemma differentiable.differentiable_at (h : differentiable 𝕜 f) :
  differentiable_at 𝕜 f x :=
h x

lemma differentiable_at.fderiv_within
  (h : differentiable_at 𝕜 f x) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
h.has_fderiv_at.has_fderiv_within_at.fderiv_within hxs

lemma differentiable_on.mono (h : differentiable_on 𝕜 f t) (st : s ⊆ t) :
  differentiable_on 𝕜 f s :=
λ x hx, (h x (st hx)).mono st

lemma differentiable_on_univ :
  differentiable_on 𝕜 f univ ↔ differentiable 𝕜 f :=
by simp only [differentiable_on, differentiable, differentiable_within_at_univ, mem_univ,
  forall_true_left]

lemma differentiable.differentiable_on (h : differentiable 𝕜 f) : differentiable_on 𝕜 f s :=
(differentiable_on_univ.2 h).mono (subset_univ _)

lemma differentiable_on_of_locally_differentiable_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ differentiable_on 𝕜 f (s ∩ u)) : differentiable_on 𝕜 f s :=
begin
  assume x xs,
  rcases h x xs with ⟨t, t_open, xt, ht⟩,
  exact (differentiable_within_at_inter (is_open.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
end

lemma fderiv_within_subset (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  fderiv_within 𝕜 f s x = fderiv_within 𝕜 f t x :=
((differentiable_within_at.has_fderiv_within_at h).mono st).fderiv_within ht

lemma fderiv_within_subset' (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x) (hx : s ∈ 𝓝[t] x)
  (h : differentiable_within_at 𝕜 f s x) :
  fderiv_within 𝕜 f s x = fderiv_within 𝕜 f t x :=
fderiv_within_subset st ht (h.antimono st hx)

@[simp] lemma fderiv_within_univ : fderiv_within 𝕜 f univ = fderiv 𝕜 f :=
begin
  ext x : 1,
  by_cases h : differentiable_at 𝕜 f x,
  { apply has_fderiv_within_at.fderiv_within _ unique_diff_within_at_univ,
    rw has_fderiv_within_at_univ,
    apply h.has_fderiv_at },
  { have : ¬ differentiable_within_at 𝕜 f univ x,
    { rwa differentiable_within_at_univ },
    rw [fderiv_zero_of_not_differentiable_at h,
        fderiv_within_zero_of_not_differentiable_within_at this] }
end

lemma fderiv_within_inter (ht : t ∈ 𝓝 x) (hs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 f (s ∩ t) x = fderiv_within 𝕜 f s x :=
begin
  by_cases h : differentiable_within_at 𝕜 f (s ∩ t) x,
  { apply fderiv_within_subset (inter_subset_left _ _) _ ((differentiable_within_at_inter ht).1 h),
    apply hs.inter ht },
  { have : ¬ differentiable_within_at 𝕜 f s x,
    { rwa ←differentiable_within_at_inter ht },
    rw [fderiv_within_zero_of_not_differentiable_within_at h,
        fderiv_within_zero_of_not_differentiable_within_at this] }
end

lemma fderiv_within_of_mem_nhds (h : s ∈ 𝓝 x) :
  fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
begin
  have : s = univ ∩ s, by simp only [univ_inter],
  rw [this, ← fderiv_within_univ],
  exact fderiv_within_inter h (unique_diff_on_univ _ (mem_univ _))
end

lemma fderiv_within_of_open (hs : is_open s) (hx : x ∈ s) :
  fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
fderiv_within_of_mem_nhds (is_open.mem_nhds hs hx)

lemma fderiv_within_eq_fderiv (hs : unique_diff_within_at 𝕜 s x) (h : differentiable_at 𝕜 f x) :
  fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
begin
  rw ← fderiv_within_univ,
  exact fderiv_within_subset (subset_univ _) hs h.differentiable_within_at
end

lemma fderiv_mem_iff {f : E → F} {s : set (E →L[𝕜] F)} {x : E} :
  fderiv 𝕜 f x ∈ s ↔ (differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ s) ∨
    (¬differentiable_at 𝕜 f x ∧ (0 : E →L[𝕜] F) ∈ s) :=
by by_cases hx : differentiable_at 𝕜 f x; simp [fderiv_zero_of_not_differentiable_at, *]

lemma fderiv_within_mem_iff {f : E → F} {t : set E} {s : set (E →L[𝕜] F)} {x : E} :
  fderiv_within 𝕜 f t x ∈ s ↔ (differentiable_within_at 𝕜 f t x ∧ fderiv_within 𝕜 f t x ∈ s) ∨
    (¬differentiable_within_at 𝕜 f t x ∧ (0 : E →L[𝕜] F) ∈ s) :=
by by_cases hx : differentiable_within_at 𝕜 f t x;
  simp [fderiv_within_zero_of_not_differentiable_within_at, *]

lemma asymptotics.is_O.has_fderiv_within_at {s : set E} {x₀ : E} {n : ℕ}
  (h : f =O[𝓝[s] x₀] λ x, ‖x - x₀‖^n) (hx₀ : x₀ ∈ s) (hn : 1 < n) :
  has_fderiv_within_at f (0 : E →L[𝕜] F) s x₀ :=
by simp_rw [has_fderiv_within_at, has_fderiv_at_filter,
  h.eq_zero_of_norm_pow_within hx₀ $ zero_lt_one.trans hn, zero_apply, sub_zero,
  h.trans_is_o ((is_o_pow_sub_sub x₀ hn).mono nhds_within_le_nhds)]

lemma asymptotics.is_O.has_fderiv_at {x₀ : E} {n : ℕ}
  (h : f =O[𝓝 x₀] λ x, ‖x - x₀‖^n) (hn : 1 < n) :
  has_fderiv_at f (0 : E →L[𝕜] F) x₀ :=
begin
  rw [← nhds_within_univ] at h,
  exact (h.has_fderiv_within_at (mem_univ _) hn).has_fderiv_at_of_univ
end

lemma has_fderiv_within_at.is_O {f : E → F} {s : set E} {x₀ : E} {f' : E →L[𝕜] F}
  (h : has_fderiv_within_at f f' s x₀) :
  (λ x, f x - f x₀) =O[𝓝[s] x₀] λ x, x - x₀ :=
by simpa only [sub_add_cancel] using h.is_O.add (is_O_sub f' (𝓝[s] x₀) x₀)

lemma has_fderiv_at.is_O {f : E → F} {x₀ : E} {f' : E →L[𝕜] F} (h : has_fderiv_at f f' x₀) :
  (λ x, f x - f x₀) =O[𝓝 x₀] λ x, x - x₀ :=
by simpa only [sub_add_cancel] using h.is_O.add (is_O_sub f' (𝓝 x₀) x₀)

end fderiv_properties

section continuous
/-! ### Deducing continuity from differentiability -/

theorem has_fderiv_at_filter.tendsto_nhds
  (hL : L ≤ 𝓝 x) (h : has_fderiv_at_filter f f' x L) :
  tendsto f L (𝓝 (f x)) :=
begin
  have : tendsto (λ x', f x' - f x) L (𝓝 0),
  { refine h.is_O_sub.trans_tendsto (tendsto.mono_left _ hL),
    rw ← sub_self x, exact tendsto_id.sub tendsto_const_nhds },
  have := tendsto.add this tendsto_const_nhds,
  rw zero_add (f x) at this,
  exact this.congr (by simp only [sub_add_cancel, eq_self_iff_true, forall_const])
end

theorem has_fderiv_within_at.continuous_within_at
  (h : has_fderiv_within_at f f' s x) : continuous_within_at f s x :=
has_fderiv_at_filter.tendsto_nhds inf_le_left h

theorem has_fderiv_at.continuous_at (h : has_fderiv_at f f' x) :
  continuous_at f x :=
has_fderiv_at_filter.tendsto_nhds le_rfl h

lemma differentiable_within_at.continuous_within_at (h : differentiable_within_at 𝕜 f s x) :
  continuous_within_at f s x :=
let ⟨f', hf'⟩ := h in hf'.continuous_within_at

lemma differentiable_at.continuous_at (h : differentiable_at 𝕜 f x) : continuous_at f x :=
let ⟨f', hf'⟩ := h in hf'.continuous_at

lemma differentiable_on.continuous_on (h : differentiable_on 𝕜 f s) : continuous_on f s :=
λx hx, (h x hx).continuous_within_at

lemma differentiable.continuous (h : differentiable 𝕜 f) : continuous f :=
continuous_iff_continuous_at.2 $ λx, (h x).continuous_at

protected lemma has_strict_fderiv_at.continuous_at (hf : has_strict_fderiv_at f f' x) :
  continuous_at f x :=
hf.has_fderiv_at.continuous_at

lemma has_strict_fderiv_at.is_O_sub_rev {f' : E ≃L[𝕜] F}
  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) x) :
  (λ p : E × E, p.1 - p.2) =O[𝓝 (x, x)](λ p : E × E, f p.1 - f p.2) :=
((f'.is_O_comp_rev _ _).trans (hf.trans_is_O (f'.is_O_comp_rev _ _)).right_is_O_add).congr
(λ _, rfl) (λ _, sub_add_cancel _ _)

lemma has_fderiv_at_filter.is_O_sub_rev (hf : has_fderiv_at_filter f f' x L) {C}
  (hf' : antilipschitz_with C f') :
  (λ x', x' - x) =O[L] (λ x', f x' - f x) :=
have (λ x', x' - x) =O[L] (λ x', f' (x' - x)),
  from is_O_iff.2 ⟨C, eventually_of_forall $ λ x',
    add_monoid_hom_class.bound_of_antilipschitz f' hf' _⟩,
(this.trans (hf.trans_is_O this).right_is_O_add).congr (λ _, rfl) (λ _, sub_add_cancel _ _)

end continuous

section congr
/-! ### congr properties of the derivative -/

theorem filter.eventually_eq.has_strict_fderiv_at_iff
  (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
  has_strict_fderiv_at f₀ f₀' x ↔ has_strict_fderiv_at f₁ f₁' x :=
begin
  refine is_o_congr ((h.prod_mk_nhds h).mono _) (eventually_of_forall $ λ _, rfl),
  rintros p ⟨hp₁, hp₂⟩,
  simp only [*]
end

theorem has_strict_fderiv_at.congr_of_eventually_eq (h : has_strict_fderiv_at f f' x)
  (h₁ : f =ᶠ[𝓝 x] f₁) : has_strict_fderiv_at f₁ f' x :=
(h₁.has_strict_fderiv_at_iff (λ _, rfl)).1 h

theorem filter.eventually_eq.has_fderiv_at_filter_iff
  (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter f₀ f₀' x L ↔ has_fderiv_at_filter f₁ f₁' x L :=
is_o_congr (h₀.mono $ λ y hy, by simp only [hy, h₁, hx]) (eventually_of_forall $ λ _, rfl)

lemma has_fderiv_at_filter.congr_of_eventually_eq (h : has_fderiv_at_filter f f' x L)
  (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : has_fderiv_at_filter f₁ f' x L :=
(hL.has_fderiv_at_filter_iff hx $ λ _, rfl).2 h

theorem filter.eventually_eq.has_fderiv_at_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
  has_fderiv_at f₀ f' x ↔ has_fderiv_at f₁ f' x :=
h.has_fderiv_at_filter_iff h.eq_of_nhds (λ _, rfl)

theorem filter.eventually_eq.differentiable_at_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
  differentiable_at 𝕜 f₀ x ↔ differentiable_at 𝕜 f₁ x :=
exists_congr $ λ f', h.has_fderiv_at_iff

theorem filter.eventually_eq.has_fderiv_within_at_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
  has_fderiv_within_at f₀ f' s x ↔ has_fderiv_within_at f₁ f' s x :=
h.has_fderiv_at_filter_iff hx (λ _, rfl)

theorem filter.eventually_eq.has_fderiv_within_at_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
  has_fderiv_within_at f₀ f' s x ↔ has_fderiv_within_at f₁ f' s x :=
h.has_fderiv_within_at_iff (h.eq_of_nhds_within hx)

theorem filter.eventually_eq.differentiable_within_at_iff (h : f₀ =ᶠ[𝓝[s] x] f₁)
  (hx : f₀ x = f₁ x) :
  differentiable_within_at 𝕜 f₀ s x ↔ differentiable_within_at 𝕜 f₁ s x :=
exists_congr $ λ f', h.has_fderiv_within_at_iff hx

theorem filter.eventually_eq.differentiable_within_at_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁)
  (hx : x ∈ s) :
  differentiable_within_at 𝕜 f₀ s x ↔ differentiable_within_at 𝕜 f₁ s x :=
h.differentiable_within_at_iff (h.eq_of_nhds_within hx)

lemma has_fderiv_within_at.congr_mono (h : has_fderiv_within_at f f' s x) (ht : ∀x ∈ t, f₁ x = f x)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_fderiv_within_at f₁ f' t x :=
has_fderiv_at_filter.congr_of_eventually_eq (h.mono h₁) (filter.mem_inf_of_right ht) hx

lemma has_fderiv_within_at.congr (h : has_fderiv_within_at f f' s x) (hs : ∀x ∈ s, f₁ x = f x)
  (hx : f₁ x = f x) : has_fderiv_within_at f₁ f' s x :=
h.congr_mono hs hx (subset.refl _)

lemma has_fderiv_within_at.congr' (h : has_fderiv_within_at f f' s x) (hs : ∀x ∈ s, f₁ x = f x)
  (hx : x ∈ s) : has_fderiv_within_at f₁ f' s x :=
h.congr hs (hs x hx)

lemma has_fderiv_within_at.congr_of_eventually_eq (h : has_fderiv_within_at f f' s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : has_fderiv_within_at f₁ f' s x :=
has_fderiv_at_filter.congr_of_eventually_eq h h₁ hx

lemma has_fderiv_at.congr_of_eventually_eq (h : has_fderiv_at f f' x)
  (h₁ : f₁ =ᶠ[𝓝 x] f) : has_fderiv_at f₁ f' x :=
has_fderiv_at_filter.congr_of_eventually_eq h h₁ (mem_of_mem_nhds h₁ : _)

lemma differentiable_within_at.congr_mono (h : differentiable_within_at 𝕜 f s x)
  (ht : ∀x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : differentiable_within_at 𝕜 f₁ t x :=
(has_fderiv_within_at.congr_mono h.has_fderiv_within_at ht hx h₁).differentiable_within_at

lemma differentiable_within_at.congr (h : differentiable_within_at 𝕜 f s x)
  (ht : ∀x ∈ s, f₁ x = f x) (hx : f₁ x = f x) : differentiable_within_at 𝕜 f₁ s x :=
differentiable_within_at.congr_mono h ht hx (subset.refl _)

lemma differentiable_within_at.congr_of_eventually_eq
  (h : differentiable_within_at 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
  (hx : f₁ x = f x) : differentiable_within_at 𝕜 f₁ s x :=
(h.has_fderiv_within_at.congr_of_eventually_eq h₁ hx).differentiable_within_at

lemma differentiable_on.congr_mono (h : differentiable_on 𝕜 f s) (h' : ∀x ∈ t, f₁ x = f x)
  (h₁ : t ⊆ s) : differentiable_on 𝕜 f₁ t :=
λ x hx, (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

lemma differentiable_on.congr (h : differentiable_on 𝕜 f s) (h' : ∀x ∈ s, f₁ x = f x) :
  differentiable_on 𝕜 f₁ s :=
λ x hx, (h x hx).congr h' (h' x hx)

lemma differentiable_on_congr (h' : ∀x ∈ s, f₁ x = f x) :
  differentiable_on 𝕜 f₁ s ↔ differentiable_on 𝕜 f s :=
⟨λ h, differentiable_on.congr h (λy hy, (h' y hy).symm),
λ h, differentiable_on.congr h h'⟩

lemma differentiable_at.congr_of_eventually_eq (h : differentiable_at 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) :
  differentiable_at 𝕜 f₁ x :=
hL.differentiable_at_iff.2 h

lemma differentiable_within_at.fderiv_within_congr_mono (h : differentiable_within_at 𝕜 f s x)
  (hs : ∀x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : unique_diff_within_at 𝕜 t x) (h₁ : t ⊆ s) :
  fderiv_within 𝕜 f₁ t x = fderiv_within 𝕜 f s x :=
(has_fderiv_within_at.congr_mono h.has_fderiv_within_at hs hx h₁).fderiv_within hxt

lemma filter.eventually_eq.fderiv_within_eq (hs : unique_diff_within_at 𝕜 s x)
  (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
if h : differentiable_within_at 𝕜 f s x
then has_fderiv_within_at.fderiv_within (h.has_fderiv_within_at.congr_of_eventually_eq hL hx) hs
else
  have h' : ¬ differentiable_within_at 𝕜 f₁ s x,
  from mt (λ h, h.congr_of_eventually_eq (hL.mono $ λ x, eq.symm) hx.symm) h,
  by rw [fderiv_within_zero_of_not_differentiable_within_at h,
    fderiv_within_zero_of_not_differentiable_within_at h']

lemma filter.eventually_eq.fderiv_within_eq_nhds (hs : unique_diff_within_at 𝕜 s x)
  (hL : f₁ =ᶠ[𝓝 x] f) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
(show f₁ =ᶠ[𝓝[s] x] f, from nhds_within_le_nhds hL).fderiv_within_eq hs (mem_of_mem_nhds hL : _)

lemma fderiv_within_congr (hs : unique_diff_within_at 𝕜 s x)
  (hL : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
begin
  apply filter.eventually_eq.fderiv_within_eq hs _ hx,
  apply mem_of_superset self_mem_nhds_within,
  exact hL
end

lemma fderiv_within_congr' (hs : unique_diff_within_at 𝕜 s x)
  (hL : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
fderiv_within_congr hs hL (hL x hx)

lemma filter.eventually_eq.fderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) :
  fderiv 𝕜 f₁ x = fderiv 𝕜 f x :=
begin
  have A : f₁ x = f x := hL.eq_of_nhds,
  rw [← fderiv_within_univ, ← fderiv_within_univ],
  rw ← nhds_within_univ at hL,
  exact hL.fderiv_within_eq unique_diff_within_at_univ A
end

protected lemma filter.eventually_eq.fderiv (h : f₁ =ᶠ[𝓝 x] f) :
  fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
h.eventually_eq_nhds.mono $ λ x h, h.fderiv_eq

end congr

section id
/-! ### Derivative of the identity -/

theorem has_strict_fderiv_at_id (x : E) :
  has_strict_fderiv_at id (id 𝕜 E) x :=
(is_o_zero _ _).congr_left $ by simp

theorem has_fderiv_at_filter_id (x : E) (L : filter E) :
  has_fderiv_at_filter id (id 𝕜 E) x L :=
(is_o_zero _ _).congr_left $ by simp

theorem has_fderiv_within_at_id (x : E) (s : set E) :
  has_fderiv_within_at id (id 𝕜 E) s x :=
has_fderiv_at_filter_id _ _

theorem has_fderiv_at_id (x : E) : has_fderiv_at id (id 𝕜 E) x :=
has_fderiv_at_filter_id _ _

@[simp] lemma differentiable_at_id : differentiable_at 𝕜 id x :=
(has_fderiv_at_id x).differentiable_at

@[simp] lemma differentiable_at_id' : differentiable_at 𝕜 (λ x, x) x :=
(has_fderiv_at_id x).differentiable_at

lemma differentiable_within_at_id : differentiable_within_at 𝕜 id s x :=
differentiable_at_id.differentiable_within_at

@[simp] lemma differentiable_id : differentiable 𝕜 (id : E → E) :=
λx, differentiable_at_id

@[simp] lemma differentiable_id' : differentiable 𝕜 (λ (x : E), x) :=
λx, differentiable_at_id

lemma differentiable_on_id : differentiable_on 𝕜 id s :=
differentiable_id.differentiable_on

lemma fderiv_id : fderiv 𝕜 id x = id 𝕜 E :=
has_fderiv_at.fderiv (has_fderiv_at_id x)

@[simp] lemma fderiv_id' : fderiv 𝕜 (λ (x : E), x) x = continuous_linear_map.id 𝕜 E :=
fderiv_id

lemma fderiv_within_id (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 id s x = id 𝕜 E :=
begin
  rw differentiable_at.fderiv_within (differentiable_at_id) hxs,
  exact fderiv_id
end

lemma fderiv_within_id' (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λ (x : E), x) s x = continuous_linear_map.id 𝕜 E :=
fderiv_within_id hxs

end id

section const
/-! ### derivative of a constant function -/

theorem has_strict_fderiv_at_const (c : F) (x : E) :
  has_strict_fderiv_at (λ _, c) (0 : E →L[𝕜] F) x :=
(is_o_zero _ _).congr_left $ λ _, by simp only [zero_apply, sub_self]

theorem has_fderiv_at_filter_const (c : F) (x : E) (L : filter E) :
  has_fderiv_at_filter (λ x, c) (0 : E →L[𝕜] F) x L :=
(is_o_zero _ _).congr_left $ λ _, by simp only [zero_apply, sub_self]

theorem has_fderiv_within_at_const (c : F) (x : E) (s : set E) :
  has_fderiv_within_at (λ x, c) (0 : E →L[𝕜] F) s x :=
has_fderiv_at_filter_const _ _ _

theorem has_fderiv_at_const (c : F) (x : E) :
  has_fderiv_at (λ x, c) (0 : E →L[𝕜] F) x :=
has_fderiv_at_filter_const _ _ _

@[simp] lemma differentiable_at_const (c : F) : differentiable_at 𝕜 (λx, c) x :=
⟨0, has_fderiv_at_const c x⟩

lemma differentiable_within_at_const (c : F) : differentiable_within_at 𝕜 (λx, c) s x :=
differentiable_at.differentiable_within_at (differentiable_at_const _)

lemma fderiv_const_apply (c : F) : fderiv 𝕜 (λy, c) x = 0 :=
has_fderiv_at.fderiv (has_fderiv_at_const c x)

@[simp] lemma fderiv_const (c : F) : fderiv 𝕜 (λ (y : E), c) = 0 :=
by { ext m, rw fderiv_const_apply, refl }

lemma fderiv_within_const_apply (c : F) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λy, c) s x = 0 :=
begin
  rw differentiable_at.fderiv_within (differentiable_at_const _) hxs,
  exact fderiv_const_apply _
end

@[simp] lemma differentiable_const (c : F) : differentiable 𝕜 (λx : E, c) :=
λx, differentiable_at_const _

lemma differentiable_on_const (c : F) : differentiable_on 𝕜 (λx, c) s :=
(differentiable_const _).differentiable_on

lemma has_fderiv_within_at_singleton (f : E → F) (x : E) :
  has_fderiv_within_at f (0 : E →L[𝕜] F) {x} x :=
by simp only [has_fderiv_within_at, nhds_within_singleton, has_fderiv_at_filter, is_o_pure,
  continuous_linear_map.zero_apply, sub_self]

lemma has_fderiv_at_of_subsingleton [h : subsingleton E] (f : E → F) (x : E) :
  has_fderiv_at f (0 : E →L[𝕜] F) x :=
begin
  rw [← has_fderiv_within_at_univ, subsingleton_univ.eq_singleton_of_mem (mem_univ x)],
  exact has_fderiv_within_at_singleton f x
end

lemma differentiable_on_empty : differentiable_on 𝕜 f ∅ := λ x, false.elim

lemma differentiable_on_singleton : differentiable_on 𝕜 f {x} :=
forall_eq.2 (has_fderiv_within_at_singleton f x).differentiable_within_at

lemma set.subsingleton.differentiable_on (hs : s.subsingleton) : differentiable_on 𝕜 f s :=
hs.induction_on differentiable_on_empty (λ x, differentiable_on_singleton)

lemma has_fderiv_at_zero_of_eventually_const
  (c : F) (hf : f =ᶠ[𝓝 x] (λ y, c)) :
  has_fderiv_at f (0 : E →L[𝕜] F) x :=
(has_fderiv_at_const _ _).congr_of_eventually_eq hf

end const

section continuous_linear_map
/-!
### Continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `continuous_linear_map`, and denoted `E →L[𝕜] F`), and the unbundled version (with a
predicate `is_bounded_linear_map`). We give statements for both versions. -/

protected theorem continuous_linear_map.has_strict_fderiv_at {x : E} :
  has_strict_fderiv_at e e x :=
(is_o_zero _ _).congr_left $ λ x, by simp only [e.map_sub, sub_self]

protected lemma continuous_linear_map.has_fderiv_at_filter :
  has_fderiv_at_filter e e x L :=
(is_o_zero _ _).congr_left $ λ x, by simp only [e.map_sub, sub_self]

protected lemma continuous_linear_map.has_fderiv_within_at : has_fderiv_within_at e e s x :=
e.has_fderiv_at_filter

protected lemma continuous_linear_map.has_fderiv_at : has_fderiv_at e e x :=
e.has_fderiv_at_filter

@[simp] protected lemma continuous_linear_map.differentiable_at : differentiable_at 𝕜 e x :=
e.has_fderiv_at.differentiable_at

protected lemma continuous_linear_map.differentiable_within_at : differentiable_within_at 𝕜 e s x :=
e.differentiable_at.differentiable_within_at

@[simp] protected lemma continuous_linear_map.fderiv : fderiv 𝕜 e x = e :=
e.has_fderiv_at.fderiv

protected lemma continuous_linear_map.fderiv_within (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 e s x = e :=
begin
  rw differentiable_at.fderiv_within e.differentiable_at hxs,
  exact e.fderiv
end

@[simp] protected lemma continuous_linear_map.differentiable : differentiable 𝕜 e :=
λx, e.differentiable_at

protected lemma continuous_linear_map.differentiable_on : differentiable_on 𝕜 e s :=
e.differentiable.differentiable_on

lemma is_bounded_linear_map.has_fderiv_at_filter (h : is_bounded_linear_map 𝕜 f) :
  has_fderiv_at_filter f h.to_continuous_linear_map x L :=
h.to_continuous_linear_map.has_fderiv_at_filter

lemma is_bounded_linear_map.has_fderiv_within_at (h : is_bounded_linear_map 𝕜 f) :
  has_fderiv_within_at f h.to_continuous_linear_map s x :=
h.has_fderiv_at_filter

lemma is_bounded_linear_map.has_fderiv_at (h : is_bounded_linear_map 𝕜 f) :
  has_fderiv_at f h.to_continuous_linear_map x  :=
h.has_fderiv_at_filter

lemma is_bounded_linear_map.differentiable_at (h : is_bounded_linear_map 𝕜 f) :
  differentiable_at 𝕜 f x :=
h.has_fderiv_at.differentiable_at

lemma is_bounded_linear_map.differentiable_within_at (h : is_bounded_linear_map 𝕜 f) :
  differentiable_within_at 𝕜 f s x :=
h.differentiable_at.differentiable_within_at

lemma is_bounded_linear_map.fderiv (h : is_bounded_linear_map 𝕜 f) :
  fderiv 𝕜 f x = h.to_continuous_linear_map :=
has_fderiv_at.fderiv (h.has_fderiv_at)

lemma is_bounded_linear_map.fderiv_within (h : is_bounded_linear_map 𝕜 f)
  (hxs : unique_diff_within_at 𝕜 s x) : fderiv_within 𝕜 f s x = h.to_continuous_linear_map :=
begin
  rw differentiable_at.fderiv_within h.differentiable_at hxs,
  exact h.fderiv
end

lemma is_bounded_linear_map.differentiable (h : is_bounded_linear_map 𝕜 f) :
  differentiable 𝕜 f :=
λx, h.differentiable_at

lemma is_bounded_linear_map.differentiable_on (h : is_bounded_linear_map 𝕜 f) :
  differentiable_on 𝕜 f s :=
h.differentiable.differentiable_on

end continuous_linear_map

section composition
/-!
### Derivative of the composition of two functions

For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/

variable (x)

theorem has_fderiv_at_filter.comp {g : F → G} {g' : F →L[𝕜] G} {L' : filter F}
  (hg : has_fderiv_at_filter g g' (f x) L')
  (hf : has_fderiv_at_filter f f' x L) (hL : tendsto f L L') :
  has_fderiv_at_filter (g ∘ f) (g'.comp f') x L :=
let eq₁ := (g'.is_O_comp _ _).trans_is_o hf in
let eq₂ := (hg.comp_tendsto hL).trans_is_O hf.is_O_sub in
by { refine eq₂.triangle (eq₁.congr_left (λ x', _)), simp }

/- A readable version of the previous theorem,
   a general form of the chain rule. -/

example {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at_filter g g' (f x) (L.map f))
  (hf : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (g ∘ f) (g'.comp f') x L :=
begin
  unfold has_fderiv_at_filter at hg,
  have := calc (λ x', g (f x') - g (f x) - g' (f x' - f x)) =o[L] (λ x', f x' - f x) :
    hg.comp_tendsto le_rfl
  ... =O[L] (λ x', x' - x) : hf.is_O_sub,
  refine this.triangle _,
  calc (λ x' : E, g' (f x' - f x) - g'.comp f' (x' - x))
      =ᶠ[L] λ x', g' (f x' - f x - f' (x' - x)) : eventually_of_forall (λ x', by simp)
  ... =O[L] λ x', f x' - f x - f' (x' - x)      : g'.is_O_comp _ _
  ... =o[L] λ x', x' - x                        : hf
end

theorem has_fderiv_within_at.comp {g : F → G} {g' : F →L[𝕜] G} {t : set F}
  (hg : has_fderiv_within_at g g' t (f x)) (hf : has_fderiv_within_at f f' s x)
  (hst : maps_to f s t) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
hg.comp x hf $ hf.continuous_within_at.tendsto_nhds_within hst

theorem has_fderiv_at.comp_has_fderiv_within_at {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at g g' (f x)) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
hg.comp x hf hf.continuous_within_at

theorem has_fderiv_within_at.comp_of_mem {g : F → G} {g' : F →L[𝕜] G} {t : set F}
  (hg : has_fderiv_within_at g g' t (f x)) (hf : has_fderiv_within_at f f' s x)
  (hst : tendsto f (𝓝[s] x) (𝓝[t] f x)) :
  has_fderiv_within_at (g ∘ f) (g'.comp f') s x :=
has_fderiv_at_filter.comp x hg hf hst

/-- The chain rule. -/
theorem has_fderiv_at.comp {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_fderiv_at g g' (f x)) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (g ∘ f) (g'.comp f') x :=
hg.comp x hf hf.continuous_at

lemma differentiable_within_at.comp {g : F → G} {t : set F}
  (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (h : maps_to f s t) : differentiable_within_at 𝕜 (g ∘ f) s x :=
(hg.has_fderiv_within_at.comp x hf.has_fderiv_within_at h).differentiable_within_at

lemma differentiable_within_at.comp' {g : F → G} {t : set F}
  (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (g ∘ f) (s ∩ f⁻¹' t) x :=
hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

lemma differentiable_at.comp {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (g ∘ f) x :=
(hg.has_fderiv_at.comp x hf.has_fderiv_at).differentiable_at

lemma differentiable_at.comp_differentiable_within_at {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (g ∘ f) s x :=
hg.differentiable_within_at.comp x hf (maps_to_univ _ _)

lemma fderiv_within.comp {g : F → G} {t : set F}
  (hg : differentiable_within_at 𝕜 g t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (h : maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (g ∘ f) s x = (fderiv_within 𝕜 g t (f x)).comp (fderiv_within 𝕜 f s x) :=
(hg.has_fderiv_within_at.comp x (hf.has_fderiv_within_at) h).fderiv_within hxs

/-- A version of `fderiv_within.comp` that is useful to rewrite the composition of two derivatives
  into a single derivative. This version always applies, but creates a new side-goal `f x = y`. -/
lemma fderiv_within_fderiv_within {g : F → G} {f : E → F} {x : E} {y : F} {s : set E} {t : set F}
  (hg : differentiable_within_at 𝕜 g t y) (hf : differentiable_within_at 𝕜 f s x)
  (h : maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) (hy : f x = y) (v : E) :
  fderiv_within 𝕜 g t y (fderiv_within 𝕜 f s x v) = fderiv_within 𝕜 (g ∘ f) s x v :=
by { subst y, rw [fderiv_within.comp x hg hf h hxs], refl }

/-- Ternary version of `fderiv_within.comp`, with equality assumptions of basepoints added, in
  order to apply more easily as a rewrite from right-to-left. -/
lemma fderiv_within.comp₃ {g' : G → G'} {g : F → G} {t : set F} {u : set G} {y : F} {y' : G}
  (hg' : differentiable_within_at 𝕜 g' u y') (hg : differentiable_within_at 𝕜 g t y)
  (hf : differentiable_within_at 𝕜 f s x)
  (h2g : maps_to g t u) (h2f : maps_to f s t)
  (h3g : g y = y') (h3f : f x = y) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (g' ∘ g ∘ f) s x = (fderiv_within 𝕜 g' u y').comp
    ((fderiv_within 𝕜 g t y).comp (fderiv_within 𝕜 f s x)) :=
begin
  substs h3g h3f,
  exact (hg'.has_fderiv_within_at.comp x
    (hg.has_fderiv_within_at.comp x (hf.has_fderiv_within_at) h2f) $ h2g.comp h2f).fderiv_within hxs
end

lemma fderiv.comp {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_at 𝕜 f x) :
  fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
(hg.has_fderiv_at.comp x hf.has_fderiv_at).fderiv

lemma fderiv.comp_fderiv_within {g : F → G}
  (hg : differentiable_at 𝕜 g (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (g ∘ f) s x = (fderiv 𝕜 g (f x)).comp (fderiv_within 𝕜 f s x) :=
(hg.has_fderiv_at.comp_has_fderiv_within_at x hf.has_fderiv_within_at).fderiv_within hxs

lemma differentiable_on.comp {g : F → G} {t : set F}
  (hg : differentiable_on 𝕜 g t) (hf : differentiable_on 𝕜 f s) (st : maps_to f s t) :
  differentiable_on 𝕜 (g ∘ f) s :=
λx hx, differentiable_within_at.comp x (hg (f x) (st hx)) (hf x hx) st

lemma differentiable.comp {g : F → G} (hg : differentiable 𝕜 g) (hf : differentiable 𝕜 f) :
  differentiable 𝕜 (g ∘ f) :=
λx, differentiable_at.comp x (hg (f x)) (hf x)

lemma differentiable.comp_differentiable_on {g : F → G} (hg : differentiable 𝕜 g)
  (hf : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (g ∘ f) s :=
hg.differentiable_on.comp hf (maps_to_univ _ _)

/-- The chain rule for derivatives in the sense of strict differentiability. -/
protected lemma has_strict_fderiv_at.comp {g : F → G} {g' : F →L[𝕜] G}
  (hg : has_strict_fderiv_at g g' (f x)) (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, g (f x)) (g'.comp f') x :=
((hg.comp_tendsto (hf.continuous_at.prod_map' hf.continuous_at)).trans_is_O hf.is_O_sub).triangle $
  by simpa only [g'.map_sub, f'.coe_comp'] using (g'.is_O_comp _ _).trans_is_o hf

protected lemma differentiable.iterate {f : E → E} (hf : differentiable 𝕜 f) (n : ℕ) :
  differentiable 𝕜 (f^[n]) :=
nat.rec_on n differentiable_id (λ n ihn, ihn.comp hf)

protected lemma differentiable_on.iterate {f : E → E} (hf : differentiable_on 𝕜 f s)
  (hs : maps_to f s s) (n : ℕ) :
  differentiable_on 𝕜 (f^[n]) s :=
nat.rec_on n differentiable_on_id (λ n ihn, ihn.comp hf hs)

variable {x}

protected lemma has_fderiv_at_filter.iterate {f : E → E} {f' : E →L[𝕜] E}
  (hf : has_fderiv_at_filter f f' x L) (hL : tendsto f L L) (hx : f x = x) (n : ℕ) :
  has_fderiv_at_filter (f^[n]) (f'^n) x L :=
begin
  induction n with n ihn,
  { exact has_fderiv_at_filter_id x L },
  { rw [function.iterate_succ, pow_succ'],
    rw ← hx at ihn,
    exact ihn.comp x hf hL }
end

protected lemma has_fderiv_at.iterate {f : E → E} {f' : E →L[𝕜] E}
  (hf : has_fderiv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_fderiv_at (f^[n]) (f'^n) x :=
begin
  refine hf.iterate _ hx n,
  convert hf.continuous_at,
  exact hx.symm
end

protected lemma has_fderiv_within_at.iterate {f : E → E} {f' : E →L[𝕜] E}
  (hf : has_fderiv_within_at f f' s x) (hx : f x = x) (hs : maps_to f s s) (n : ℕ) :
  has_fderiv_within_at (f^[n]) (f'^n) s x :=
begin
  refine hf.iterate _ hx n,
  convert tendsto_inf.2 ⟨hf.continuous_within_at, _⟩,
  exacts [hx.symm, (tendsto_principal_principal.2 hs).mono_left inf_le_right]
end

protected lemma has_strict_fderiv_at.iterate {f : E → E} {f' : E →L[𝕜] E}
  (hf : has_strict_fderiv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_strict_fderiv_at (f^[n]) (f'^n) x :=
begin
  induction n with n ihn,
  { exact has_strict_fderiv_at_id x },
  { rw [function.iterate_succ, pow_succ'],
    rw ← hx at ihn,
    exact ihn.comp x hf }
end

protected lemma differentiable_at.iterate {f : E → E} (hf : differentiable_at 𝕜 f x)
  (hx : f x = x) (n : ℕ) :
  differentiable_at 𝕜 (f^[n]) x :=
(hf.has_fderiv_at.iterate hx n).differentiable_at

protected lemma differentiable_within_at.iterate {f : E → E} (hf : differentiable_within_at 𝕜 f s x)
  (hx : f x = x) (hs : maps_to f s s) (n : ℕ) :
  differentiable_within_at 𝕜 (f^[n]) s x :=
(hf.has_fderiv_within_at.iterate hx hs n).differentiable_within_at

end composition

section cartesian_product
/-! ### Derivative of the cartesian product of two functions -/

section prod
variables {f₂ : E → G} {f₂' : E →L[𝕜] G}

protected lemma has_strict_fderiv_at.prod
  (hf₁ : has_strict_fderiv_at f₁ f₁' x) (hf₂ : has_strict_fderiv_at f₂ f₂' x) :
  has_strict_fderiv_at (λx, (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
hf₁.prod_left hf₂

lemma has_fderiv_at_filter.prod
  (hf₁ : has_fderiv_at_filter f₁ f₁' x L) (hf₂ : has_fderiv_at_filter f₂ f₂' x L) :
  has_fderiv_at_filter (λx, (f₁ x, f₂ x)) (f₁'.prod f₂') x L :=
hf₁.prod_left hf₂

lemma has_fderiv_within_at.prod
  (hf₁ : has_fderiv_within_at f₁ f₁' s x) (hf₂ : has_fderiv_within_at f₂ f₂' s x) :
  has_fderiv_within_at (λx, (f₁ x, f₂ x)) (f₁'.prod f₂') s x :=
hf₁.prod hf₂

lemma has_fderiv_at.prod (hf₁ : has_fderiv_at f₁ f₁' x) (hf₂ : has_fderiv_at f₂ f₂' x) :
  has_fderiv_at (λx, (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
hf₁.prod hf₂

lemma has_fderiv_at_prod_mk_left (e₀ : E) (f₀ : F) :
  has_fderiv_at (λ e : E, (e, f₀)) (inl 𝕜 E F) e₀ :=
(has_fderiv_at_id e₀).prod (has_fderiv_at_const f₀ e₀)

lemma has_fderiv_at_prod_mk_right (e₀ : E) (f₀ : F) :
  has_fderiv_at (λ f : F, (e₀, f)) (inr 𝕜 E F) f₀ :=
(has_fderiv_at_const e₀ f₀).prod (has_fderiv_at_id f₀)

lemma differentiable_within_at.prod
  (hf₁ : differentiable_within_at 𝕜 f₁ s x) (hf₂ : differentiable_within_at 𝕜 f₂ s x) :
  differentiable_within_at 𝕜 (λx:E, (f₁ x, f₂ x)) s x :=
(hf₁.has_fderiv_within_at.prod hf₂.has_fderiv_within_at).differentiable_within_at

@[simp]
lemma differentiable_at.prod (hf₁ : differentiable_at 𝕜 f₁ x) (hf₂ : differentiable_at 𝕜 f₂ x) :
  differentiable_at 𝕜 (λx:E, (f₁ x, f₂ x)) x :=
(hf₁.has_fderiv_at.prod hf₂.has_fderiv_at).differentiable_at

lemma differentiable_on.prod (hf₁ : differentiable_on 𝕜 f₁ s) (hf₂ : differentiable_on 𝕜 f₂ s) :
  differentiable_on 𝕜 (λx:E, (f₁ x, f₂ x)) s :=
λx hx, differentiable_within_at.prod (hf₁ x hx) (hf₂ x hx)

@[simp]
lemma differentiable.prod (hf₁ : differentiable 𝕜 f₁) (hf₂ : differentiable 𝕜 f₂) :
  differentiable 𝕜 (λx:E, (f₁ x, f₂ x)) :=
λ x, differentiable_at.prod (hf₁ x) (hf₂ x)

lemma differentiable_at.fderiv_prod
  (hf₁ : differentiable_at 𝕜 f₁ x) (hf₂ : differentiable_at 𝕜 f₂ x) :
  fderiv 𝕜 (λx:E, (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).prod (fderiv 𝕜 f₂ x) :=
(hf₁.has_fderiv_at.prod hf₂.has_fderiv_at).fderiv

lemma differentiable_within_at.fderiv_within_prod
  (hf₁ : differentiable_within_at 𝕜 f₁ s x) (hf₂ : differentiable_within_at 𝕜 f₂ s x)
  (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx:E, (f₁ x, f₂ x)) s x =
    (fderiv_within 𝕜 f₁ s x).prod (fderiv_within 𝕜 f₂ s x) :=
(hf₁.has_fderiv_within_at.prod hf₂.has_fderiv_within_at).fderiv_within hxs

end prod

section fst

variables {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

lemma has_strict_fderiv_at_fst : has_strict_fderiv_at (@prod.fst E F) (fst 𝕜 E F) p :=
(fst 𝕜 E F).has_strict_fderiv_at

protected lemma has_strict_fderiv_at.fst (h : has_strict_fderiv_at f₂ f₂' x) :
  has_strict_fderiv_at (λ x, (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
has_strict_fderiv_at_fst.comp x h

lemma has_fderiv_at_filter_fst {L : filter (E × F)} :
  has_fderiv_at_filter (@prod.fst E F) (fst 𝕜 E F) p L :=
(fst 𝕜 E F).has_fderiv_at_filter

protected lemma has_fderiv_at_filter.fst (h : has_fderiv_at_filter f₂ f₂' x L) :
  has_fderiv_at_filter (λ x, (f₂ x).1) ((fst 𝕜 F G).comp f₂') x L :=
has_fderiv_at_filter_fst.comp x h tendsto_map

lemma has_fderiv_at_fst : has_fderiv_at (@prod.fst E F) (fst 𝕜 E F) p :=
has_fderiv_at_filter_fst

protected lemma has_fderiv_at.fst (h : has_fderiv_at f₂ f₂' x) :
  has_fderiv_at (λ x, (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
h.fst

lemma has_fderiv_within_at_fst {s : set (E × F)} :
  has_fderiv_within_at (@prod.fst E F) (fst 𝕜 E F) s p :=
has_fderiv_at_filter_fst

protected lemma has_fderiv_within_at.fst (h : has_fderiv_within_at f₂ f₂' s x) :
  has_fderiv_within_at (λ x, (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
h.fst

lemma differentiable_at_fst : differentiable_at 𝕜 prod.fst p :=
has_fderiv_at_fst.differentiable_at

@[simp] protected lemma differentiable_at.fst (h : differentiable_at 𝕜 f₂ x) :
  differentiable_at 𝕜 (λ x, (f₂ x).1) x :=
differentiable_at_fst.comp x h

lemma differentiable_fst : differentiable 𝕜 (prod.fst : E × F → E) :=
λ x, differentiable_at_fst

@[simp] protected lemma differentiable.fst (h : differentiable 𝕜 f₂) :
  differentiable 𝕜 (λ x, (f₂ x).1) :=
differentiable_fst.comp h

lemma differentiable_within_at_fst {s : set (E × F)} : differentiable_within_at 𝕜 prod.fst s p :=
differentiable_at_fst.differentiable_within_at

protected lemma differentiable_within_at.fst (h : differentiable_within_at 𝕜 f₂ s x) :
  differentiable_within_at 𝕜 (λ x, (f₂ x).1) s x :=
differentiable_at_fst.comp_differentiable_within_at x h

lemma differentiable_on_fst {s : set (E × F)} : differentiable_on 𝕜 prod.fst s :=
differentiable_fst.differentiable_on

protected lemma differentiable_on.fst (h : differentiable_on 𝕜 f₂ s) :
  differentiable_on 𝕜 (λ x, (f₂ x).1) s :=
differentiable_fst.comp_differentiable_on h

lemma fderiv_fst : fderiv 𝕜 prod.fst p = fst 𝕜 E F := has_fderiv_at_fst.fderiv

lemma fderiv.fst (h : differentiable_at 𝕜 f₂ x) :
  fderiv 𝕜 (λ x, (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
h.has_fderiv_at.fst.fderiv

lemma fderiv_within_fst {s : set (E × F)} (hs : unique_diff_within_at 𝕜 s p) :
  fderiv_within 𝕜 prod.fst s p = fst 𝕜 E F :=
has_fderiv_within_at_fst.fderiv_within hs

lemma fderiv_within.fst (hs : unique_diff_within_at 𝕜 s x) (h : differentiable_within_at 𝕜 f₂ s x) :
  fderiv_within 𝕜 (λ x, (f₂ x).1) s x = (fst 𝕜 F G).comp (fderiv_within 𝕜 f₂ s x) :=
h.has_fderiv_within_at.fst.fderiv_within hs

end fst

section snd

variables {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

lemma has_strict_fderiv_at_snd : has_strict_fderiv_at (@prod.snd E F) (snd 𝕜 E F) p :=
(snd 𝕜 E F).has_strict_fderiv_at

protected lemma has_strict_fderiv_at.snd (h : has_strict_fderiv_at f₂ f₂' x) :
  has_strict_fderiv_at (λ x, (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
has_strict_fderiv_at_snd.comp x h

lemma has_fderiv_at_filter_snd {L : filter (E × F)} :
  has_fderiv_at_filter (@prod.snd E F) (snd 𝕜 E F) p L :=
(snd 𝕜 E F).has_fderiv_at_filter

protected lemma has_fderiv_at_filter.snd (h : has_fderiv_at_filter f₂ f₂' x L) :
  has_fderiv_at_filter (λ x, (f₂ x).2) ((snd 𝕜 F G).comp f₂') x L :=
has_fderiv_at_filter_snd.comp x h tendsto_map

lemma has_fderiv_at_snd : has_fderiv_at (@prod.snd E F) (snd 𝕜 E F) p :=
has_fderiv_at_filter_snd

protected lemma has_fderiv_at.snd (h : has_fderiv_at f₂ f₂' x) :
  has_fderiv_at (λ x, (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
h.snd

lemma has_fderiv_within_at_snd {s : set (E × F)} :
  has_fderiv_within_at (@prod.snd E F) (snd 𝕜 E F) s p :=
has_fderiv_at_filter_snd

protected lemma has_fderiv_within_at.snd (h : has_fderiv_within_at f₂ f₂' s x) :
  has_fderiv_within_at (λ x, (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
h.snd

lemma differentiable_at_snd : differentiable_at 𝕜 prod.snd p :=
has_fderiv_at_snd.differentiable_at

@[simp] protected lemma differentiable_at.snd (h : differentiable_at 𝕜 f₂ x) :
  differentiable_at 𝕜 (λ x, (f₂ x).2) x :=
differentiable_at_snd.comp x h

lemma differentiable_snd : differentiable 𝕜 (prod.snd : E × F → F) :=
λ x, differentiable_at_snd

@[simp] protected lemma differentiable.snd (h : differentiable 𝕜 f₂) :
  differentiable 𝕜 (λ x, (f₂ x).2) :=
differentiable_snd.comp h

lemma differentiable_within_at_snd {s : set (E × F)} : differentiable_within_at 𝕜 prod.snd s p :=
differentiable_at_snd.differentiable_within_at

protected lemma differentiable_within_at.snd (h : differentiable_within_at 𝕜 f₂ s x) :
  differentiable_within_at 𝕜 (λ x, (f₂ x).2) s x :=
differentiable_at_snd.comp_differentiable_within_at x h

lemma differentiable_on_snd {s : set (E × F)} : differentiable_on 𝕜 prod.snd s :=
differentiable_snd.differentiable_on

protected lemma differentiable_on.snd (h : differentiable_on 𝕜 f₂ s) :
  differentiable_on 𝕜 (λ x, (f₂ x).2) s :=
differentiable_snd.comp_differentiable_on h

lemma fderiv_snd : fderiv 𝕜 prod.snd p = snd 𝕜 E F := has_fderiv_at_snd.fderiv

lemma fderiv.snd (h : differentiable_at 𝕜 f₂ x) :
  fderiv 𝕜 (λ x, (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
h.has_fderiv_at.snd.fderiv

lemma fderiv_within_snd {s : set (E × F)} (hs : unique_diff_within_at 𝕜 s p) :
  fderiv_within 𝕜 prod.snd s p = snd 𝕜 E F :=
has_fderiv_within_at_snd.fderiv_within hs

lemma fderiv_within.snd (hs : unique_diff_within_at 𝕜 s x) (h : differentiable_within_at 𝕜 f₂ s x) :
  fderiv_within 𝕜 (λ x, (f₂ x).2) s x = (snd 𝕜 F G).comp (fderiv_within 𝕜 f₂ s x) :=
h.has_fderiv_within_at.snd.fderiv_within hs

end snd

section prod_map

variables {f₂ : G → G'} {f₂' : G →L[𝕜] G'} {y : G} (p : E × G)

protected theorem has_strict_fderiv_at.prod_map (hf : has_strict_fderiv_at f f' p.1)
  (hf₂ : has_strict_fderiv_at f₂ f₂' p.2) :
  has_strict_fderiv_at (prod.map f f₂) (f'.prod_map f₂') p :=
(hf.comp p has_strict_fderiv_at_fst).prod (hf₂.comp p has_strict_fderiv_at_snd)

protected theorem has_fderiv_at.prod_map (hf : has_fderiv_at f f' p.1)
  (hf₂ : has_fderiv_at f₂ f₂' p.2) :
  has_fderiv_at (prod.map f f₂) (f'.prod_map f₂') p :=
(hf.comp p has_fderiv_at_fst).prod (hf₂.comp p has_fderiv_at_snd)

@[simp] protected theorem differentiable_at.prod_map (hf : differentiable_at 𝕜 f p.1)
  (hf₂ : differentiable_at 𝕜 f₂ p.2) :
  differentiable_at 𝕜 (λ p : E × G, (f p.1, f₂ p.2)) p :=
(hf.comp p differentiable_at_fst).prod (hf₂.comp p differentiable_at_snd)

end prod_map

end cartesian_product

section const_smul

variables {R : Type*} [semiring R] [module R F] [smul_comm_class 𝕜 R F]
  [has_continuous_const_smul R F]

/-! ### Derivative of a function multiplied by a constant -/
theorem has_strict_fderiv_at.const_smul (h : has_strict_fderiv_at f f' x) (c : R) :
  has_strict_fderiv_at (λ x, c • f x) (c • f') x :=
(c • (1 : F →L[𝕜] F)).has_strict_fderiv_at.comp x h

theorem has_fderiv_at_filter.const_smul (h : has_fderiv_at_filter f f' x L) (c : R) :
  has_fderiv_at_filter (λ x, c • f x) (c • f') x L :=
(c • (1 : F →L[𝕜] F)).has_fderiv_at_filter.comp x h tendsto_map

theorem has_fderiv_within_at.const_smul (h : has_fderiv_within_at f f' s x) (c : R) :
  has_fderiv_within_at (λ x, c • f x) (c • f') s x :=
h.const_smul c

theorem has_fderiv_at.const_smul (h : has_fderiv_at f f' x) (c : R) :
  has_fderiv_at (λ x, c • f x) (c • f') x :=
h.const_smul c

lemma differentiable_within_at.const_smul (h : differentiable_within_at 𝕜 f s x) (c : R) :
  differentiable_within_at 𝕜 (λy, c • f y) s x :=
(h.has_fderiv_within_at.const_smul c).differentiable_within_at

lemma differentiable_at.const_smul (h : differentiable_at 𝕜 f x) (c : R) :
  differentiable_at 𝕜 (λy, c • f y) x :=
(h.has_fderiv_at.const_smul c).differentiable_at

lemma differentiable_on.const_smul (h : differentiable_on 𝕜 f s) (c : R) :
  differentiable_on 𝕜 (λy, c • f y) s :=
λx hx, (h x hx).const_smul c

lemma differentiable.const_smul (h : differentiable 𝕜 f) (c : R) :
  differentiable 𝕜 (λy, c • f y) :=
λx, (h x).const_smul c

lemma fderiv_within_const_smul (hxs : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f s x) (c : R) :
  fderiv_within 𝕜 (λy, c • f y) s x = c • fderiv_within 𝕜 f s x :=
(h.has_fderiv_within_at.const_smul c).fderiv_within hxs

lemma fderiv_const_smul (h : differentiable_at 𝕜 f x) (c : R) :
  fderiv 𝕜 (λy, c • f y) x = c • fderiv 𝕜 f x :=
(h.has_fderiv_at.const_smul c).fderiv

end const_smul

section add

/-! ### Derivative of the sum of two functions -/

theorem has_strict_fderiv_at.add (hf : has_strict_fderiv_at f f' x)
  (hg : has_strict_fderiv_at g g' x) :
  has_strict_fderiv_at (λ y, f y + g y) (f' + g') x :=
(hf.add hg).congr_left $ λ y,
  by { simp only [linear_map.sub_apply, linear_map.add_apply, map_sub, map_add, add_apply], abel }

theorem has_fderiv_at_filter.add
  (hf : has_fderiv_at_filter f f' x L) (hg : has_fderiv_at_filter g g' x L) :
  has_fderiv_at_filter (λ y, f y + g y) (f' + g') x L :=
(hf.add hg).congr_left $ λ _,
  by { simp only [linear_map.sub_apply, linear_map.add_apply, map_sub, map_add, add_apply], abel }

theorem has_fderiv_within_at.add
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ y, f y + g y) (f' + g') s x :=
hf.add hg

theorem has_fderiv_at.add
  (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ x, f x + g x) (f' + g') x :=
hf.add hg

lemma differentiable_within_at.add
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  differentiable_within_at 𝕜 (λ y, f y + g y) s x :=
(hf.has_fderiv_within_at.add hg.has_fderiv_within_at).differentiable_within_at

@[simp] lemma differentiable_at.add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  differentiable_at 𝕜 (λ y, f y + g y) x :=
(hf.has_fderiv_at.add hg.has_fderiv_at).differentiable_at

lemma differentiable_on.add
  (hf : differentiable_on 𝕜 f s) (hg : differentiable_on 𝕜 g s) :
  differentiable_on 𝕜 (λy, f y + g y) s :=
λx hx, (hf x hx).add (hg x hx)

@[simp] lemma differentiable.add
  (hf : differentiable 𝕜 f) (hg : differentiable 𝕜 g) :
  differentiable 𝕜 (λy, f y + g y) :=
λx, (hf x).add (hg x)

lemma fderiv_within_add (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  fderiv_within 𝕜 (λy, f y + g y) s x = fderiv_within 𝕜 f s x + fderiv_within 𝕜 g s x :=
(hf.has_fderiv_within_at.add hg.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  fderiv 𝕜 (λy, f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
(hf.has_fderiv_at.add hg.has_fderiv_at).fderiv

theorem has_strict_fderiv_at.add_const (hf : has_strict_fderiv_at f f' x) (c : F) :
  has_strict_fderiv_at (λ y, f y + c) f' x :=
add_zero f' ▸ hf.add (has_strict_fderiv_at_const _ _)

theorem has_fderiv_at_filter.add_const
  (hf : has_fderiv_at_filter f f' x L) (c : F) :
  has_fderiv_at_filter (λ y, f y + c) f' x L :=
add_zero f' ▸ hf.add (has_fderiv_at_filter_const _ _ _)

theorem has_fderiv_within_at.add_const
  (hf : has_fderiv_within_at f f' s x) (c : F) :
  has_fderiv_within_at (λ y, f y + c) f' s x :=
hf.add_const c

theorem has_fderiv_at.add_const (hf : has_fderiv_at f f' x) (c : F):
  has_fderiv_at (λ x, f x + c) f' x :=
hf.add_const c

lemma differentiable_within_at.add_const
  (hf : differentiable_within_at 𝕜 f s x) (c : F) :
  differentiable_within_at 𝕜 (λ y, f y + c) s x :=
(hf.has_fderiv_within_at.add_const c).differentiable_within_at

@[simp] lemma differentiable_within_at_add_const_iff (c : F) :
  differentiable_within_at 𝕜 (λ y, f y + c) s x ↔ differentiable_within_at 𝕜 f s x :=
⟨λ h, by simpa using h.add_const (-c), λ h, h.add_const c⟩

lemma differentiable_at.add_const
  (hf : differentiable_at 𝕜 f x) (c : F) :
  differentiable_at 𝕜 (λ y, f y + c) x :=
(hf.has_fderiv_at.add_const c).differentiable_at

@[simp] lemma differentiable_at_add_const_iff (c : F) :
  differentiable_at 𝕜 (λ y, f y + c) x ↔ differentiable_at 𝕜 f x :=
⟨λ h, by simpa using h.add_const (-c), λ h, h.add_const c⟩

lemma differentiable_on.add_const
  (hf : differentiable_on 𝕜 f s) (c : F) :
  differentiable_on 𝕜 (λy, f y + c) s :=
λx hx, (hf x hx).add_const c

@[simp] lemma differentiable_on_add_const_iff (c : F) :
  differentiable_on 𝕜 (λ y, f y + c) s ↔ differentiable_on 𝕜 f s :=
⟨λ h, by simpa using h.add_const (-c), λ h, h.add_const c⟩

lemma differentiable.add_const
  (hf : differentiable 𝕜 f) (c : F) :
  differentiable 𝕜 (λy, f y + c) :=
λx, (hf x).add_const c

@[simp] lemma differentiable_add_const_iff (c : F) :
  differentiable 𝕜 (λ y, f y + c) ↔ differentiable 𝕜 f :=
⟨λ h, by simpa using h.add_const (-c), λ h, h.add_const c⟩

lemma fderiv_within_add_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  fderiv_within 𝕜 (λy, f y + c) s x = fderiv_within 𝕜 f s x :=
if hf : differentiable_within_at 𝕜 f s x
then (hf.has_fderiv_within_at.add_const c).fderiv_within hxs
else by { rw [fderiv_within_zero_of_not_differentiable_within_at hf,
  fderiv_within_zero_of_not_differentiable_within_at], simpa }

lemma fderiv_add_const (c : F) : fderiv 𝕜 (λy, f y + c) x = fderiv 𝕜 f x :=
by simp only [← fderiv_within_univ, fderiv_within_add_const unique_diff_within_at_univ]

theorem has_strict_fderiv_at.const_add (hf : has_strict_fderiv_at f f' x) (c : F) :
  has_strict_fderiv_at (λ y, c + f y) f' x :=
zero_add f' ▸ (has_strict_fderiv_at_const _ _).add hf

theorem has_fderiv_at_filter.const_add
  (hf : has_fderiv_at_filter f f' x L) (c : F) :
  has_fderiv_at_filter (λ y, c + f y) f' x L :=
zero_add f' ▸ (has_fderiv_at_filter_const _ _ _).add hf

theorem has_fderiv_within_at.const_add
  (hf : has_fderiv_within_at f f' s x) (c : F) :
  has_fderiv_within_at (λ y, c + f y) f' s x :=
hf.const_add c

theorem has_fderiv_at.const_add
  (hf : has_fderiv_at f f' x) (c : F):
  has_fderiv_at (λ x, c + f x) f' x :=
hf.const_add c

lemma differentiable_within_at.const_add
  (hf : differentiable_within_at 𝕜 f s x) (c : F) :
  differentiable_within_at 𝕜 (λ y, c + f y) s x :=
(hf.has_fderiv_within_at.const_add c).differentiable_within_at

@[simp] lemma differentiable_within_at_const_add_iff (c : F) :
  differentiable_within_at 𝕜 (λ y, c + f y) s x ↔ differentiable_within_at 𝕜 f s x :=
⟨λ h, by simpa using h.const_add (-c), λ h, h.const_add c⟩

lemma differentiable_at.const_add
  (hf : differentiable_at 𝕜 f x) (c : F) :
  differentiable_at 𝕜 (λ y, c + f y) x :=
(hf.has_fderiv_at.const_add c).differentiable_at

@[simp] lemma differentiable_at_const_add_iff (c : F) :
  differentiable_at 𝕜 (λ y, c + f y) x ↔ differentiable_at 𝕜 f x :=
⟨λ h, by simpa using h.const_add (-c), λ h, h.const_add c⟩

lemma differentiable_on.const_add (hf : differentiable_on 𝕜 f s) (c : F) :
  differentiable_on 𝕜 (λy, c + f y) s :=
λx hx, (hf x hx).const_add c

@[simp] lemma differentiable_on_const_add_iff (c : F) :
  differentiable_on 𝕜 (λ y, c + f y) s ↔ differentiable_on 𝕜 f s :=
⟨λ h, by simpa using h.const_add (-c), λ h, h.const_add c⟩

lemma differentiable.const_add (hf : differentiable 𝕜 f) (c : F) :
  differentiable 𝕜 (λy, c + f y) :=
λx, (hf x).const_add c

@[simp] lemma differentiable_const_add_iff (c : F) :
  differentiable 𝕜 (λ y, c + f y) ↔ differentiable 𝕜 f :=
⟨λ h, by simpa using h.const_add (-c), λ h, h.const_add c⟩

lemma fderiv_within_const_add (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  fderiv_within 𝕜 (λy, c + f y) s x = fderiv_within 𝕜 f s x :=
by simpa only [add_comm] using fderiv_within_add_const hxs c

lemma fderiv_const_add (c : F) : fderiv 𝕜 (λy, c + f y) x = fderiv 𝕜 f x :=
by simp only [add_comm c, fderiv_add_const]

end add

section sum
/-! ### Derivative of a finite sum of functions -/

open_locale big_operators

variables {ι : Type*} {u : finset ι} {A : ι → (E → F)} {A' : ι → (E →L[𝕜] F)}

theorem has_strict_fderiv_at.sum (h : ∀ i ∈ u, has_strict_fderiv_at (A i) (A' i) x) :
  has_strict_fderiv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
begin
  dsimp [has_strict_fderiv_at] at *,
  convert is_o.sum h,
  simp [finset.sum_sub_distrib, continuous_linear_map.sum_apply]
end

theorem has_fderiv_at_filter.sum (h : ∀ i ∈ u, has_fderiv_at_filter (A i) (A' i) x L) :
  has_fderiv_at_filter (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x L :=
begin
  dsimp [has_fderiv_at_filter] at *,
  convert is_o.sum h,
  simp [continuous_linear_map.sum_apply]
end

theorem has_fderiv_within_at.sum (h : ∀ i ∈ u, has_fderiv_within_at (A i) (A' i) s x) :
  has_fderiv_within_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) s x :=
has_fderiv_at_filter.sum h

theorem has_fderiv_at.sum (h : ∀ i ∈ u, has_fderiv_at (A i) (A' i) x) :
  has_fderiv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
has_fderiv_at_filter.sum h

theorem differentiable_within_at.sum (h : ∀ i ∈ u, differentiable_within_at 𝕜 (A i) s x) :
  differentiable_within_at 𝕜 (λ y, ∑ i in u, A i y) s x :=
has_fderiv_within_at.differentiable_within_at $ has_fderiv_within_at.sum $
λ i hi, (h i hi).has_fderiv_within_at

@[simp] theorem differentiable_at.sum (h : ∀ i ∈ u, differentiable_at 𝕜 (A i) x) :
  differentiable_at 𝕜 (λ y, ∑ i in u, A i y) x :=
has_fderiv_at.differentiable_at $ has_fderiv_at.sum $ λ i hi, (h i hi).has_fderiv_at

theorem differentiable_on.sum (h : ∀ i ∈ u, differentiable_on 𝕜 (A i) s) :
  differentiable_on 𝕜 (λ y, ∑ i in u, A i y) s :=
λ x hx, differentiable_within_at.sum $ λ i hi, h i hi x hx

@[simp] theorem differentiable.sum (h : ∀ i ∈ u, differentiable 𝕜 (A i)) :
  differentiable 𝕜 (λ y, ∑ i in u, A i y) :=
λ x, differentiable_at.sum $ λ i hi, h i hi x

theorem fderiv_within_sum (hxs : unique_diff_within_at 𝕜 s x)
  (h : ∀ i ∈ u, differentiable_within_at 𝕜 (A i) s x) :
  fderiv_within 𝕜 (λ y, ∑ i in u, A i y) s x = (∑ i in u, fderiv_within 𝕜 (A i) s x) :=
(has_fderiv_within_at.sum (λ i hi, (h i hi).has_fderiv_within_at)).fderiv_within hxs

theorem fderiv_sum (h : ∀ i ∈ u, differentiable_at 𝕜 (A i) x) :
  fderiv 𝕜 (λ y, ∑ i in u, A i y) x = (∑ i in u, fderiv 𝕜 (A i) x) :=
(has_fderiv_at.sum (λ i hi, (h i hi).has_fderiv_at)).fderiv

end sum

section pi

/-!
### Derivatives of functions `f : E → Π i, F' i`

In this section we formulate `has_*fderiv*_pi` theorems as `iff`s, and provide two versions of each
theorem:

* the version without `'` deals with `φ : Π i, E → F' i` and `φ' : Π i, E →L[𝕜] F' i`
  and is designed to deduce differentiability of `λ x i, φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `λ x, Φ x i` from
  differentiability of `Φ`.
-/

variables {ι : Type*} [fintype ι] {F' : ι → Type*} [Π i, normed_add_comm_group (F' i)]
  [Π i, normed_space 𝕜 (F' i)] {φ : Π i, E → F' i} {φ' : Π i, E →L[𝕜] F' i}
  {Φ : E → Π i, F' i} {Φ' : E →L[𝕜] Π i, F' i}

@[simp] lemma has_strict_fderiv_at_pi' :
  has_strict_fderiv_at Φ Φ' x ↔
    ∀ i, has_strict_fderiv_at (λ x, Φ x i) ((proj i).comp Φ') x :=
begin
  simp only [has_strict_fderiv_at, continuous_linear_map.coe_pi],
  exact is_o_pi
end

@[simp] lemma has_strict_fderiv_at_pi :
  has_strict_fderiv_at (λ x i, φ i x) (continuous_linear_map.pi φ') x ↔
    ∀ i, has_strict_fderiv_at (φ i) (φ' i) x :=
has_strict_fderiv_at_pi'

@[simp] lemma has_fderiv_at_filter_pi' :
  has_fderiv_at_filter Φ Φ' x L ↔
    ∀ i, has_fderiv_at_filter (λ x, Φ x i) ((proj i).comp Φ') x L :=
begin
  simp only [has_fderiv_at_filter, continuous_linear_map.coe_pi],
  exact is_o_pi
end

lemma has_fderiv_at_filter_pi :
  has_fderiv_at_filter (λ x i, φ i x) (continuous_linear_map.pi φ') x L ↔
    ∀ i, has_fderiv_at_filter (φ i) (φ' i) x L :=
has_fderiv_at_filter_pi'

@[simp] lemma has_fderiv_at_pi' :
  has_fderiv_at Φ Φ' x ↔
    ∀ i, has_fderiv_at (λ x, Φ x i) ((proj i).comp Φ') x :=
has_fderiv_at_filter_pi'

lemma has_fderiv_at_pi :
  has_fderiv_at (λ x i, φ i x) (continuous_linear_map.pi φ') x ↔
    ∀ i, has_fderiv_at (φ i) (φ' i) x :=
has_fderiv_at_filter_pi

@[simp] lemma has_fderiv_within_at_pi' :
  has_fderiv_within_at Φ Φ' s x ↔
    ∀ i, has_fderiv_within_at (λ x, Φ x i) ((proj i).comp Φ') s x :=
has_fderiv_at_filter_pi'

lemma has_fderiv_within_at_pi :
  has_fderiv_within_at (λ x i, φ i x) (continuous_linear_map.pi φ') s x ↔
    ∀ i, has_fderiv_within_at (φ i) (φ' i) s x :=
has_fderiv_at_filter_pi

@[simp] lemma differentiable_within_at_pi :
  differentiable_within_at 𝕜 Φ s x ↔
   ∀ i, differentiable_within_at 𝕜 (λ x, Φ x i) s x :=
⟨λ h i, (has_fderiv_within_at_pi'.1 h.has_fderiv_within_at i).differentiable_within_at,
  λ h, (has_fderiv_within_at_pi.2 (λ i, (h i).has_fderiv_within_at)).differentiable_within_at⟩

@[simp] lemma differentiable_at_pi :
  differentiable_at 𝕜 Φ x ↔ ∀ i, differentiable_at 𝕜 (λ x, Φ x i) x :=
⟨λ h i, (has_fderiv_at_pi'.1 h.has_fderiv_at i).differentiable_at,
  λ h, (has_fderiv_at_pi.2 (λ i, (h i).has_fderiv_at)).differentiable_at⟩

lemma differentiable_on_pi :
  differentiable_on 𝕜 Φ s ↔ ∀ i, differentiable_on 𝕜 (λ x, Φ x i) s :=
⟨λ h i x hx, differentiable_within_at_pi.1 (h x hx) i,
  λ h x hx, differentiable_within_at_pi.2 (λ i, h i x hx)⟩

lemma differentiable_pi :
  differentiable 𝕜 Φ ↔ ∀ i, differentiable 𝕜 (λ x, Φ x i) :=
⟨λ h i x, differentiable_at_pi.1 (h x) i, λ h x, differentiable_at_pi.2 (λ i, h i x)⟩

-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
lemma fderiv_within_pi (h : ∀ i, differentiable_within_at 𝕜 (φ i) s x)
  (hs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λ x i, φ i x) s x = pi (λ i, fderiv_within 𝕜 (φ i) s x) :=
(has_fderiv_within_at_pi.2 (λ i, (h i).has_fderiv_within_at)).fderiv_within hs

lemma fderiv_pi (h : ∀ i, differentiable_at 𝕜 (φ i) x) :
  fderiv 𝕜 (λ x i, φ i x) x = pi (λ i, fderiv 𝕜 (φ i) x) :=
(has_fderiv_at_pi.2 (λ i, (h i).has_fderiv_at)).fderiv

end pi

section neg
/-! ### Derivative of the negative of a function -/

theorem has_strict_fderiv_at.neg (h : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, -f x) (-f') x :=
(-1 : F →L[𝕜] F).has_strict_fderiv_at.comp x h

theorem has_fderiv_at_filter.neg (h : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter (λ x, -f x) (-f') x L :=
(-1 : F →L[𝕜] F).has_fderiv_at_filter.comp x h tendsto_map

theorem has_fderiv_within_at.neg (h : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, -f x) (-f') s x :=
h.neg

theorem has_fderiv_at.neg (h : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, -f x) (-f') x :=
h.neg

lemma differentiable_within_at.neg (h : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (λy, -f y) s x :=
h.has_fderiv_within_at.neg.differentiable_within_at

@[simp] lemma differentiable_within_at_neg_iff :
  differentiable_within_at 𝕜 (λy, -f y) s x ↔ differentiable_within_at 𝕜 f s x :=
⟨λ h, by simpa only [neg_neg] using h.neg, λ h, h.neg⟩

lemma differentiable_at.neg (h : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (λy, -f y) x :=
h.has_fderiv_at.neg.differentiable_at

@[simp] lemma differentiable_at_neg_iff :
  differentiable_at 𝕜 (λy, -f y) x ↔ differentiable_at 𝕜 f x :=
⟨λ h, by simpa only [neg_neg] using h.neg, λ h, h.neg⟩

lemma differentiable_on.neg (h : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (λy, -f y) s :=
λx hx, (h x hx).neg

@[simp] lemma differentiable_on_neg_iff :
  differentiable_on 𝕜 (λy, -f y) s ↔ differentiable_on 𝕜 f s :=
⟨λ h, by simpa only [neg_neg] using h.neg, λ h, h.neg⟩

lemma differentiable.neg (h : differentiable 𝕜 f) :
  differentiable 𝕜 (λy, -f y) :=
λx, (h x).neg

@[simp] lemma differentiable_neg_iff : differentiable 𝕜 (λy, -f y) ↔ differentiable 𝕜 f :=
⟨λ h, by simpa only [neg_neg] using h.neg, λ h, h.neg⟩

lemma fderiv_within_neg (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λy, -f y) s x = - fderiv_within 𝕜 f s x :=
if h : differentiable_within_at 𝕜 f s x
then h.has_fderiv_within_at.neg.fderiv_within hxs
else by { rw [fderiv_within_zero_of_not_differentiable_within_at h,
  fderiv_within_zero_of_not_differentiable_within_at, neg_zero], simpa }

@[simp] lemma fderiv_neg : fderiv 𝕜 (λy, -f y) x = - fderiv 𝕜 f x :=
by simp only [← fderiv_within_univ, fderiv_within_neg unique_diff_within_at_univ]

end neg

section sub
/-! ### Derivative of the difference of two functions -/

theorem has_strict_fderiv_at.sub
  (hf : has_strict_fderiv_at f f' x) (hg : has_strict_fderiv_at g g' x) :
  has_strict_fderiv_at (λ x, f x - g x) (f' - g') x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem has_fderiv_at_filter.sub
  (hf : has_fderiv_at_filter f f' x L) (hg : has_fderiv_at_filter g g' x L) :
  has_fderiv_at_filter (λ x, f x - g x) (f' - g') x L :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem has_fderiv_within_at.sub
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ x, f x - g x) (f' - g') s x :=
hf.sub hg

theorem has_fderiv_at.sub
  (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ x, f x - g x) (f' - g') x :=
hf.sub hg

lemma differentiable_within_at.sub
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  differentiable_within_at 𝕜 (λ y, f y - g y) s x :=
(hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).differentiable_within_at

@[simp] lemma differentiable_at.sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  differentiable_at 𝕜 (λ y, f y - g y) x :=
(hf.has_fderiv_at.sub hg.has_fderiv_at).differentiable_at

lemma differentiable_on.sub
  (hf : differentiable_on 𝕜 f s) (hg : differentiable_on 𝕜 g s) :
  differentiable_on 𝕜 (λy, f y - g y) s :=
λx hx, (hf x hx).sub (hg x hx)

@[simp] lemma differentiable.sub
  (hf : differentiable 𝕜 f) (hg : differentiable 𝕜 g) :
  differentiable 𝕜 (λy, f y - g y) :=
λx, (hf x).sub (hg x)

lemma fderiv_within_sub (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  fderiv_within 𝕜 (λy, f y - g y) s x = fderiv_within 𝕜 f s x - fderiv_within 𝕜 g s x :=
(hf.has_fderiv_within_at.sub hg.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  fderiv 𝕜 (λy, f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
(hf.has_fderiv_at.sub hg.has_fderiv_at).fderiv

theorem has_strict_fderiv_at.sub_const
  (hf : has_strict_fderiv_at f f' x) (c : F) :
  has_strict_fderiv_at (λ x, f x - c) f' x :=
by simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem has_fderiv_at_filter.sub_const
  (hf : has_fderiv_at_filter f f' x L) (c : F) :
  has_fderiv_at_filter (λ x, f x - c) f' x L :=
by simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem has_fderiv_within_at.sub_const
  (hf : has_fderiv_within_at f f' s x) (c : F) :
  has_fderiv_within_at (λ x, f x - c) f' s x :=
hf.sub_const c

theorem has_fderiv_at.sub_const
  (hf : has_fderiv_at f f' x) (c : F) :
  has_fderiv_at (λ x, f x - c) f' x :=
hf.sub_const c

lemma differentiable_within_at.sub_const
  (hf : differentiable_within_at 𝕜 f s x) (c : F) :
  differentiable_within_at 𝕜 (λ y, f y - c) s x :=
(hf.has_fderiv_within_at.sub_const c).differentiable_within_at

@[simp] lemma differentiable_within_at_sub_const_iff (c : F) :
  differentiable_within_at 𝕜 (λ y, f y - c) s x ↔ differentiable_within_at 𝕜 f s x :=
by simp only [sub_eq_add_neg, differentiable_within_at_add_const_iff]

lemma differentiable_at.sub_const (hf : differentiable_at 𝕜 f x) (c : F) :
  differentiable_at 𝕜 (λ y, f y - c) x :=
(hf.has_fderiv_at.sub_const c).differentiable_at

@[simp] lemma differentiable_at_sub_const_iff (c : F) :
  differentiable_at 𝕜 (λ y, f y - c) x ↔ differentiable_at 𝕜 f x :=
by simp only [sub_eq_add_neg, differentiable_at_add_const_iff]

lemma differentiable_on.sub_const (hf : differentiable_on 𝕜 f s) (c : F) :
  differentiable_on 𝕜 (λy, f y - c) s :=
λx hx, (hf x hx).sub_const c

@[simp] lemma differentiable_on_sub_const_iff (c : F) :
  differentiable_on 𝕜 (λ y, f y - c) s ↔ differentiable_on 𝕜 f s :=
by simp only [sub_eq_add_neg, differentiable_on_add_const_iff]

lemma differentiable.sub_const (hf : differentiable 𝕜 f) (c : F) :
  differentiable 𝕜 (λy, f y - c) :=
λx, (hf x).sub_const c

@[simp] lemma differentiable_sub_const_iff (c : F) :
  differentiable 𝕜 (λ y, f y - c) ↔ differentiable 𝕜 f :=
by simp only [sub_eq_add_neg, differentiable_add_const_iff]

lemma fderiv_within_sub_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  fderiv_within 𝕜 (λy, f y - c) s x = fderiv_within 𝕜 f s x :=
by simp only [sub_eq_add_neg, fderiv_within_add_const hxs]

lemma fderiv_sub_const (c : F) : fderiv 𝕜 (λy, f y - c) x = fderiv 𝕜 f x :=
by simp only [sub_eq_add_neg, fderiv_add_const]

theorem has_strict_fderiv_at.const_sub
  (hf : has_strict_fderiv_at f f' x) (c : F) :
  has_strict_fderiv_at (λ x, c - f x) (-f') x :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_fderiv_at_filter.const_sub
  (hf : has_fderiv_at_filter f f' x L) (c : F) :
  has_fderiv_at_filter (λ x, c - f x) (-f') x L :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_fderiv_within_at.const_sub
  (hf : has_fderiv_within_at f f' s x) (c : F) :
  has_fderiv_within_at (λ x, c - f x) (-f') s x :=
hf.const_sub c

theorem has_fderiv_at.const_sub
  (hf : has_fderiv_at f f' x) (c : F) :
  has_fderiv_at (λ x, c - f x) (-f') x :=
hf.const_sub c

lemma differentiable_within_at.const_sub
  (hf : differentiable_within_at 𝕜 f s x) (c : F) :
  differentiable_within_at 𝕜 (λ y, c - f y) s x :=
(hf.has_fderiv_within_at.const_sub c).differentiable_within_at

@[simp] lemma differentiable_within_at_const_sub_iff (c : F) :
  differentiable_within_at 𝕜 (λ y, c - f y) s x ↔ differentiable_within_at 𝕜 f s x :=
by simp [sub_eq_add_neg]

lemma differentiable_at.const_sub
  (hf : differentiable_at 𝕜 f x) (c : F) :
  differentiable_at 𝕜 (λ y, c - f y) x :=
(hf.has_fderiv_at.const_sub c).differentiable_at

@[simp] lemma differentiable_at_const_sub_iff (c : F) :
  differentiable_at 𝕜 (λ y, c - f y) x ↔ differentiable_at 𝕜 f x :=
by simp [sub_eq_add_neg]

lemma differentiable_on.const_sub (hf : differentiable_on 𝕜 f s) (c : F) :
  differentiable_on 𝕜 (λy, c - f y) s :=
λx hx, (hf x hx).const_sub c

@[simp] lemma differentiable_on_const_sub_iff (c : F) :
  differentiable_on 𝕜 (λ y, c - f y) s ↔ differentiable_on 𝕜 f s :=
by simp [sub_eq_add_neg]

lemma differentiable.const_sub (hf : differentiable 𝕜 f) (c : F) :
  differentiable 𝕜 (λy, c - f y) :=
λx, (hf x).const_sub c

@[simp] lemma differentiable_const_sub_iff (c : F) :
  differentiable 𝕜 (λ y, c - f y) ↔ differentiable 𝕜 f :=
by simp [sub_eq_add_neg]

lemma fderiv_within_const_sub (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  fderiv_within 𝕜 (λy, c - f y) s x = -fderiv_within 𝕜 f s x :=
by simp only [sub_eq_add_neg, fderiv_within_const_add, fderiv_within_neg, hxs]

lemma fderiv_const_sub (c : F) : fderiv 𝕜 (λy, c - f y) x = -fderiv 𝕜 f x :=
by simp only [← fderiv_within_univ, fderiv_within_const_sub unique_diff_within_at_univ]

end sub

section bilinear_map
/-! ### Derivative of a bounded bilinear map -/

variables {b : E × F → G} {u : set (E × F)}

open normed_field

lemma is_bounded_bilinear_map.has_strict_fderiv_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  has_strict_fderiv_at b (h.deriv p) p :=
begin
  rw has_strict_fderiv_at,
  set T := (E × F) × (E × F),
  have : (λ q : T, b (q.1 - q.2)) =o[𝓝 (p, p)] (λ q : T, ‖q.1 - q.2‖ * 1),
  { refine (h.is_O'.comp_tendsto le_top).trans_is_o _,
    simp only [(∘)],
    refine (is_O_refl (λ q : T, ‖q.1 - q.2‖) _).mul_is_o (is_o.norm_left $ (is_o_one_iff _).2 _),
    rw [← sub_self p],
    exact continuous_at_fst.sub continuous_at_snd },
  simp only [mul_one, is_o_norm_right] at this,
  refine (is_o.congr_of_sub _).1 this, clear this,
  convert_to (λ q : T, h.deriv (p - q.2) (q.1 - q.2)) =o[𝓝 (p, p)] (λ q : T, q.1 - q.2),
  { ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩, rcases p with ⟨x, y⟩,
    simp only [is_bounded_bilinear_map_deriv_coe, prod.mk_sub_mk, h.map_sub_left, h.map_sub_right],
    abel },
  have : (λ q : T, p - q.2) =o[𝓝 (p, p)] (λ q, (1:ℝ)),
    from (is_o_one_iff _).2 (sub_self p ▸ tendsto_const_nhds.sub continuous_at_snd),
  apply is_bounded_bilinear_map_apply.is_O_comp.trans_is_o,
  refine is_o.trans_is_O _ (is_O_const_mul_self 1 _ _).of_norm_right,
  refine is_o.mul_is_O _ (is_O_refl _ _),
  exact (((h.is_bounded_linear_map_deriv.is_O_id ⊤).comp_tendsto le_top : _).trans_is_o
    this).norm_left
end

lemma is_bounded_bilinear_map.has_fderiv_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  has_fderiv_at b (h.deriv p) p :=
(h.has_strict_fderiv_at p).has_fderiv_at

lemma is_bounded_bilinear_map.has_fderiv_within_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  has_fderiv_within_at b (h.deriv p) u p :=
(h.has_fderiv_at p).has_fderiv_within_at

lemma is_bounded_bilinear_map.differentiable_at (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  differentiable_at 𝕜 b p :=
(h.has_fderiv_at p).differentiable_at

lemma is_bounded_bilinear_map.differentiable_within_at (h : is_bounded_bilinear_map 𝕜 b)
  (p : E × F) :
  differentiable_within_at 𝕜 b u p :=
(h.differentiable_at p).differentiable_within_at

lemma is_bounded_bilinear_map.fderiv (h : is_bounded_bilinear_map 𝕜 b) (p : E × F) :
  fderiv 𝕜 b p = h.deriv p :=
has_fderiv_at.fderiv (h.has_fderiv_at p)

lemma is_bounded_bilinear_map.fderiv_within (h : is_bounded_bilinear_map 𝕜 b) (p : E × F)
  (hxs : unique_diff_within_at 𝕜 u p) : fderiv_within 𝕜 b u p = h.deriv p :=
begin
  rw differentiable_at.fderiv_within (h.differentiable_at p) hxs,
  exact h.fderiv p
end

lemma is_bounded_bilinear_map.differentiable (h : is_bounded_bilinear_map 𝕜 b) :
  differentiable 𝕜 b :=
λx, h.differentiable_at x

lemma is_bounded_bilinear_map.differentiable_on (h : is_bounded_bilinear_map 𝕜 b) :
  differentiable_on 𝕜 b u :=
h.differentiable.differentiable_on

variable (B : E →L[𝕜] F →L[𝕜] G)

lemma continuous_linear_map.has_fderiv_within_at_of_bilinear
  {f : G' → E} {g : G' → F} {f' : G' →L[𝕜] E} {g' : G' →L[𝕜] F} {x : G'} {s : set G'}
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ y, B (f y) (g y)) (B.precompR G' (f x) g' + B.precompL G' f' (g x)) s x :=
(B.is_bounded_bilinear_map.has_fderiv_at (f x, g x)).comp_has_fderiv_within_at x (hf.prod hg)

lemma continuous_linear_map.has_fderiv_at_of_bilinear
  {f : G' → E} {g : G' → F} {f' : G' →L[𝕜] E} {g' : G' →L[𝕜] F} {x : G'}
  (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ y, B (f y) (g y)) (B.precompR G' (f x) g' + B.precompL G' f' (g x)) x :=
(B.is_bounded_bilinear_map.has_fderiv_at (f x, g x)).comp x (hf.prod hg)

lemma continuous_linear_map.fderiv_within_of_bilinear
  {f : G' → E} {g : G' → F} {x : G'} {s : set G'}
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x)
  (hs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λ y, B (f y) (g y)) s x =
    (B.precompR G' (f x) (fderiv_within 𝕜 g s x) + B.precompL G' (fderiv_within 𝕜 f s x) (g x)) :=
(B.has_fderiv_within_at_of_bilinear hf.has_fderiv_within_at hg.has_fderiv_within_at).fderiv_within
  hs

lemma continuous_linear_map.fderiv_of_bilinear {f : G' → E} {g : G' → F} {x : G'}
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  fderiv 𝕜 (λ y, B (f y) (g y)) x =
    (B.precompR G' (f x) (fderiv 𝕜 g x) + B.precompL G' (fderiv 𝕜 f x) (g x)) :=
(B.has_fderiv_at_of_bilinear hf.has_fderiv_at hg.has_fderiv_at).fderiv

end bilinear_map

section clm_comp_apply
/-! ### Derivative of the pointwise composition/application of continuous linear maps -/

variables {H : Type*} [normed_add_comm_group H] [normed_space 𝕜 H] {c : E → G →L[𝕜] H}
  {c' : E →L[𝕜] G →L[𝕜] H} {d : E → F →L[𝕜] G} {d' : E →L[𝕜] F →L[𝕜] G} {u : E → G}
  {u' : E →L[𝕜] G}

lemma has_strict_fderiv_at.clm_comp (hc : has_strict_fderiv_at c c' x)
  (hd : has_strict_fderiv_at d d' x) : has_strict_fderiv_at (λ y, (c y).comp (d y))
  ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
(is_bounded_bilinear_map_comp.has_strict_fderiv_at (c x, d x)).comp x $ hc.prod hd

lemma has_fderiv_within_at.clm_comp (hc : has_fderiv_within_at c c' s x)
  (hd : has_fderiv_within_at d d' s x) : has_fderiv_within_at (λ y, (c y).comp (d y))
  ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') s x :=
(is_bounded_bilinear_map_comp.has_fderiv_at (c x, d x)).comp_has_fderiv_within_at x $ hc.prod hd

lemma has_fderiv_at.clm_comp (hc : has_fderiv_at c c' x)
  (hd : has_fderiv_at d d' x) : has_fderiv_at (λ y, (c y).comp (d y))
  ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
(is_bounded_bilinear_map_comp.has_fderiv_at (c x, d x)).comp x $ hc.prod hd

lemma differentiable_within_at.clm_comp
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  differentiable_within_at 𝕜 (λ y, (c y).comp (d y)) s x :=
(hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.clm_comp (hc : differentiable_at 𝕜 c x)
  (hd : differentiable_at 𝕜 d x) : differentiable_at 𝕜 (λ y, (c y).comp (d y)) x :=
(hc.has_fderiv_at.clm_comp hd.has_fderiv_at).differentiable_at

lemma differentiable_on.clm_comp (hc : differentiable_on 𝕜 c s) (hd : differentiable_on 𝕜 d s) :
  differentiable_on 𝕜 (λ y, (c y).comp (d y)) s :=
λx hx, (hc x hx).clm_comp (hd x hx)

lemma differentiable.clm_comp (hc : differentiable 𝕜 c) (hd : differentiable 𝕜 d) :
  differentiable 𝕜 (λ y, (c y).comp (d y)) :=
λx, (hc x).clm_comp (hd x)

lemma fderiv_within_clm_comp (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  fderiv_within 𝕜 (λ y, (c y).comp (d y)) s x =
    (compL 𝕜 F G H (c x)).comp (fderiv_within 𝕜 d s x) +
    ((compL 𝕜 F G H).flip (d x)).comp (fderiv_within 𝕜 c s x) :=
(hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_clm_comp (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  fderiv 𝕜 (λ y, (c y).comp (d y)) x =
    (compL 𝕜 F G H (c x)).comp (fderiv 𝕜 d x) +
    ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
(hc.has_fderiv_at.clm_comp hd.has_fderiv_at).fderiv

lemma has_strict_fderiv_at.clm_apply (hc : has_strict_fderiv_at c c' x)
  (hu : has_strict_fderiv_at u u' x) :
  has_strict_fderiv_at (λ y, (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
(is_bounded_bilinear_map_apply.has_strict_fderiv_at (c x, u x)).comp x (hc.prod hu)

lemma has_fderiv_within_at.clm_apply (hc : has_fderiv_within_at c c' s x)
  (hu : has_fderiv_within_at u u' s x) :
  has_fderiv_within_at (λ y, (c y) (u y)) ((c x).comp u' + c'.flip (u x)) s x :=
(is_bounded_bilinear_map_apply.has_fderiv_at (c x, u x)).comp_has_fderiv_within_at x (hc.prod hu)

lemma has_fderiv_at.clm_apply (hc : has_fderiv_at c c' x) (hu : has_fderiv_at u u' x) :
  has_fderiv_at (λ y, (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
(is_bounded_bilinear_map_apply.has_fderiv_at (c x, u x)).comp x (hc.prod hu)

lemma differentiable_within_at.clm_apply
  (hc : differentiable_within_at 𝕜 c s x) (hu : differentiable_within_at 𝕜 u s x) :
  differentiable_within_at 𝕜 (λ y, (c y) (u y)) s x :=
(hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.clm_apply (hc : differentiable_at 𝕜 c x)
  (hu : differentiable_at 𝕜 u x) : differentiable_at 𝕜 (λ y, (c y) (u y)) x :=
(hc.has_fderiv_at.clm_apply hu.has_fderiv_at).differentiable_at

lemma differentiable_on.clm_apply (hc : differentiable_on 𝕜 c s) (hu : differentiable_on 𝕜 u s) :
  differentiable_on 𝕜 (λ y, (c y) (u y)) s :=
λx hx, (hc x hx).clm_apply (hu x hx)

lemma differentiable.clm_apply (hc : differentiable 𝕜 c) (hu : differentiable 𝕜 u) :
  differentiable 𝕜 (λ y, (c y) (u y)) :=
λx, (hc x).clm_apply (hu x)

lemma fderiv_within_clm_apply (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hu : differentiable_within_at 𝕜 u s x) :
  fderiv_within 𝕜 (λ y, (c y) (u y)) s x =
    ((c x).comp (fderiv_within 𝕜 u s x) + (fderiv_within 𝕜 c s x).flip (u x)) :=
(hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_clm_apply (hc : differentiable_at 𝕜 c x) (hu : differentiable_at 𝕜 u x) :
  fderiv 𝕜 (λ y, (c y) (u y)) x = ((c x).comp (fderiv 𝕜 u x) + (fderiv 𝕜 c x).flip (u x)) :=
(hc.has_fderiv_at.clm_apply hu.has_fderiv_at).fderiv

end clm_comp_apply

section smul
/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `λ x, c x • f x` is differentiable as well. Lemmas in this section works for
function `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/

variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F]
variables {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'}

theorem has_strict_fderiv_at.smul (hc : has_strict_fderiv_at c c' x)
  (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ y, c y • f y) (c x • f' + c'.smul_right (f x)) x :=
(is_bounded_bilinear_map_smul.has_strict_fderiv_at (c x, f x)).comp x $
  hc.prod hf

theorem has_fderiv_within_at.smul
  (hc : has_fderiv_within_at c c' s x) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ y, c y • f y) (c x • f' + c'.smul_right (f x)) s x :=
(is_bounded_bilinear_map_smul.has_fderiv_at (c x, f x)).comp_has_fderiv_within_at x $
  hc.prod hf

theorem has_fderiv_at.smul (hc : has_fderiv_at c c' x) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ y, c y • f y) (c x • f' + c'.smul_right (f x)) x :=
(is_bounded_bilinear_map_smul.has_fderiv_at (c x, f x)).comp x $
  hc.prod hf

lemma differentiable_within_at.smul
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (λ y, c y • f y) s x :=
(hc.has_fderiv_within_at.smul hf.has_fderiv_within_at).differentiable_within_at

@[simp] lemma differentiable_at.smul (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (λ y, c y • f y) x :=
(hc.has_fderiv_at.smul hf.has_fderiv_at).differentiable_at

lemma differentiable_on.smul (hc : differentiable_on 𝕜 c s) (hf : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (λ y, c y • f y) s :=
λx hx, (hc x hx).smul (hf x hx)

@[simp] lemma differentiable.smul (hc : differentiable 𝕜 c) (hf : differentiable 𝕜 f) :
  differentiable 𝕜 (λ y, c y • f y) :=
λx, (hc x).smul (hf x)

lemma fderiv_within_smul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  fderiv_within 𝕜 (λ y, c y • f y) s x =
    c x • fderiv_within 𝕜 f s x + (fderiv_within 𝕜 c s x).smul_right (f x) :=
(hc.has_fderiv_within_at.smul hf.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_smul (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  fderiv 𝕜 (λ y, c y • f y) x =
    c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smul_right (f x) :=
(hc.has_fderiv_at.smul hf.has_fderiv_at).fderiv

theorem has_strict_fderiv_at.smul_const (hc : has_strict_fderiv_at c c' x) (f : F) :
  has_strict_fderiv_at (λ y, c y • f) (c'.smul_right f) x :=
by simpa only [smul_zero, zero_add] using hc.smul (has_strict_fderiv_at_const f x)

theorem has_fderiv_within_at.smul_const (hc : has_fderiv_within_at c c' s x) (f : F) :
  has_fderiv_within_at (λ y, c y • f) (c'.smul_right f) s x :=
by simpa only [smul_zero, zero_add] using hc.smul (has_fderiv_within_at_const f x s)

theorem has_fderiv_at.smul_const (hc : has_fderiv_at c c' x) (f : F) :
  has_fderiv_at (λ y, c y • f) (c'.smul_right f) x :=
by simpa only [smul_zero, zero_add] using hc.smul (has_fderiv_at_const f x)

lemma differentiable_within_at.smul_const
  (hc : differentiable_within_at 𝕜 c s x) (f : F) :
  differentiable_within_at 𝕜 (λ y, c y • f) s x :=
(hc.has_fderiv_within_at.smul_const f).differentiable_within_at

lemma differentiable_at.smul_const (hc : differentiable_at 𝕜 c x) (f : F) :
  differentiable_at 𝕜 (λ y, c y • f) x :=
(hc.has_fderiv_at.smul_const f).differentiable_at

lemma differentiable_on.smul_const (hc : differentiable_on 𝕜 c s) (f : F) :
  differentiable_on 𝕜 (λ y, c y • f) s :=
λx hx, (hc x hx).smul_const f

lemma differentiable.smul_const (hc : differentiable 𝕜 c) (f : F) :
  differentiable 𝕜 (λ y, c y • f) :=
λx, (hc x).smul_const f

lemma fderiv_within_smul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (f : F) :
  fderiv_within 𝕜 (λ y, c y • f) s x =
    (fderiv_within 𝕜 c s x).smul_right f :=
(hc.has_fderiv_within_at.smul_const f).fderiv_within hxs

lemma fderiv_smul_const (hc : differentiable_at 𝕜 c x) (f : F) :
  fderiv 𝕜 (λ y, c y • f) x = (fderiv 𝕜 c x).smul_right f :=
(hc.has_fderiv_at.smul_const f).fderiv

end smul

section mul
/-! ### Derivative of the product of two functions -/

variables {𝔸 𝔸' : Type*} [normed_ring 𝔸] [normed_comm_ring 𝔸'] [normed_algebra 𝕜 𝔸]
  [normed_algebra 𝕜 𝔸'] {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

theorem has_strict_fderiv_at.mul' {x : E} (ha : has_strict_fderiv_at a a' x)
  (hb : has_strict_fderiv_at b b' x) :
  has_strict_fderiv_at (λ y, a y * b y) (a x • b' + a'.smul_right (b x)) x :=
((continuous_linear_map.mul 𝕜 𝔸).is_bounded_bilinear_map.has_strict_fderiv_at (a x, b x)).comp x
  (ha.prod hb)

theorem has_strict_fderiv_at.mul
  (hc : has_strict_fderiv_at c c' x) (hd : has_strict_fderiv_at d d' x) :
  has_strict_fderiv_at (λ y, c y * d y) (c x • d' + d x • c') x :=
by { convert hc.mul' hd, ext z, apply mul_comm }

theorem has_fderiv_within_at.mul'
  (ha : has_fderiv_within_at a a' s x) (hb : has_fderiv_within_at b b' s x) :
  has_fderiv_within_at (λ y, a y * b y) (a x • b' + a'.smul_right (b x)) s x :=
((continuous_linear_map.mul 𝕜 𝔸).is_bounded_bilinear_map.has_fderiv_at
  (a x, b x)).comp_has_fderiv_within_at x (ha.prod hb)

theorem has_fderiv_within_at.mul
  (hc : has_fderiv_within_at c c' s x) (hd : has_fderiv_within_at d d' s x) :
  has_fderiv_within_at (λ y, c y * d y) (c x • d' + d x • c') s x :=
by { convert hc.mul' hd, ext z, apply mul_comm }

theorem has_fderiv_at.mul'
  (ha : has_fderiv_at a a' x) (hb : has_fderiv_at b b' x) :
  has_fderiv_at (λ y, a y * b y) (a x • b' + a'.smul_right (b x)) x :=
((continuous_linear_map.mul 𝕜 𝔸).is_bounded_bilinear_map.has_fderiv_at (a x, b x)).comp x
  (ha.prod hb)

theorem has_fderiv_at.mul (hc : has_fderiv_at c c' x) (hd : has_fderiv_at d d' x) :
  has_fderiv_at (λ y, c y * d y) (c x • d' + d x • c') x :=
by { convert hc.mul' hd, ext z, apply mul_comm }

lemma differentiable_within_at.mul
  (ha : differentiable_within_at 𝕜 a s x) (hb : differentiable_within_at 𝕜 b s x) :
  differentiable_within_at 𝕜 (λ y, a y * b y) s x :=
(ha.has_fderiv_within_at.mul' hb.has_fderiv_within_at).differentiable_within_at

@[simp] lemma differentiable_at.mul (ha : differentiable_at 𝕜 a x) (hb : differentiable_at 𝕜 b x) :
  differentiable_at 𝕜 (λ y, a y * b y) x :=
(ha.has_fderiv_at.mul' hb.has_fderiv_at).differentiable_at

lemma differentiable_on.mul (ha : differentiable_on 𝕜 a s) (hb : differentiable_on 𝕜 b s) :
  differentiable_on 𝕜 (λ y, a y * b y) s :=
λx hx, (ha x hx).mul (hb x hx)

@[simp] lemma differentiable.mul (ha : differentiable 𝕜 a) (hb : differentiable 𝕜 b) :
  differentiable 𝕜 (λ y, a y * b y) :=
λx, (ha x).mul (hb x)

lemma differentiable_within_at.pow (ha : differentiable_within_at 𝕜 a s x) :
  ∀ n : ℕ, differentiable_within_at 𝕜 (λ x, a x ^ n) s x
| 0 := by simp only [pow_zero, differentiable_within_at_const]
| (n + 1) := by simp only [pow_succ, differentiable_within_at.pow n, ha.mul]

@[simp] lemma differentiable_at.pow (ha : differentiable_at 𝕜 a x) (n : ℕ) :
  differentiable_at 𝕜 (λ x, a x ^ n) x :=
differentiable_within_at_univ.mp $ ha.differentiable_within_at.pow n

lemma differentiable_on.pow (ha : differentiable_on 𝕜 a s) (n : ℕ) :
  differentiable_on 𝕜 (λ x, a x ^ n) s :=
λ x h, (ha x h).pow n

@[simp] lemma differentiable.pow (ha : differentiable 𝕜 a) (n : ℕ) :
  differentiable 𝕜 (λ x, a x ^ n) :=
λx, (ha x).pow n

lemma fderiv_within_mul' (hxs : unique_diff_within_at 𝕜 s x)
  (ha : differentiable_within_at 𝕜 a s x) (hb : differentiable_within_at 𝕜 b s x) :
  fderiv_within 𝕜 (λ y, a y * b y) s x =
    a x • fderiv_within 𝕜 b s x + (fderiv_within 𝕜 a s x).smul_right (b x) :=
(ha.has_fderiv_within_at.mul' hb.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_within_mul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  fderiv_within 𝕜 (λ y, c y * d y) s x =
    c x • fderiv_within 𝕜 d s x + d x • fderiv_within 𝕜 c s x :=
(hc.has_fderiv_within_at.mul hd.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_mul' (ha : differentiable_at 𝕜 a x) (hb : differentiable_at 𝕜 b x) :
  fderiv 𝕜 (λ y, a y * b y) x =
    a x • fderiv 𝕜 b x + (fderiv 𝕜 a x).smul_right (b x) :=
(ha.has_fderiv_at.mul' hb.has_fderiv_at).fderiv

lemma fderiv_mul (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  fderiv 𝕜 (λ y, c y * d y) x =
    c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
(hc.has_fderiv_at.mul hd.has_fderiv_at).fderiv

theorem has_strict_fderiv_at.mul_const' (ha : has_strict_fderiv_at a a' x) (b : 𝔸) :
  has_strict_fderiv_at (λ y, a y * b) (a'.smul_right b) x :=
(((continuous_linear_map.mul 𝕜 𝔸).flip b).has_strict_fderiv_at).comp x ha

theorem has_strict_fderiv_at.mul_const (hc : has_strict_fderiv_at c c' x) (d : 𝔸') :
  has_strict_fderiv_at (λ y, c y * d) (d • c') x :=
by { convert hc.mul_const' d, ext z, apply mul_comm }

theorem has_fderiv_within_at.mul_const' (ha : has_fderiv_within_at a a' s x) (b : 𝔸) :
  has_fderiv_within_at (λ y, a y * b) (a'.smul_right b) s x :=
(((continuous_linear_map.mul 𝕜 𝔸).flip b).has_fderiv_at).comp_has_fderiv_within_at x ha

theorem has_fderiv_within_at.mul_const (hc : has_fderiv_within_at c c' s x) (d : 𝔸') :
  has_fderiv_within_at (λ y, c y * d) (d • c') s x :=
by { convert hc.mul_const' d, ext z, apply mul_comm }

theorem has_fderiv_at.mul_const' (ha : has_fderiv_at a a' x) (b : 𝔸) :
  has_fderiv_at (λ y, a y * b) (a'.smul_right b) x :=
(((continuous_linear_map.mul 𝕜 𝔸).flip b).has_fderiv_at).comp x ha

theorem has_fderiv_at.mul_const (hc : has_fderiv_at c c' x) (d : 𝔸') :
  has_fderiv_at (λ y, c y * d) (d • c') x :=
by { convert hc.mul_const' d, ext z, apply mul_comm }

lemma differentiable_within_at.mul_const
  (ha : differentiable_within_at 𝕜 a s x) (b : 𝔸) :
  differentiable_within_at 𝕜 (λ y, a y * b) s x :=
(ha.has_fderiv_within_at.mul_const' b).differentiable_within_at

lemma differentiable_at.mul_const (ha : differentiable_at 𝕜 a x) (b : 𝔸) :
  differentiable_at 𝕜 (λ y, a y * b) x :=
(ha.has_fderiv_at.mul_const' b).differentiable_at

lemma differentiable_on.mul_const (ha : differentiable_on 𝕜 a s) (b : 𝔸) :
  differentiable_on 𝕜 (λ y, a y * b) s :=
λx hx, (ha x hx).mul_const b

lemma differentiable.mul_const (ha : differentiable 𝕜 a) (b : 𝔸) :
  differentiable 𝕜 (λ y, a y * b) :=
λx, (ha x).mul_const b

lemma fderiv_within_mul_const' (hxs : unique_diff_within_at 𝕜 s x)
  (ha : differentiable_within_at 𝕜 a s x) (b : 𝔸) :
  fderiv_within 𝕜 (λ y, a y * b) s x = (fderiv_within 𝕜 a s x).smul_right b :=
(ha.has_fderiv_within_at.mul_const' b).fderiv_within hxs

lemma fderiv_within_mul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (d : 𝔸') :
  fderiv_within 𝕜 (λ y, c y * d) s x = d • fderiv_within 𝕜 c s x :=
(hc.has_fderiv_within_at.mul_const d).fderiv_within hxs

lemma fderiv_mul_const' (ha : differentiable_at 𝕜 a x) (b : 𝔸) :
  fderiv 𝕜 (λ y, a y * b) x = (fderiv 𝕜 a x).smul_right b :=
(ha.has_fderiv_at.mul_const' b).fderiv

lemma fderiv_mul_const (hc : differentiable_at 𝕜 c x) (d : 𝔸') :
  fderiv 𝕜 (λ y, c y * d) x = d • fderiv 𝕜 c x :=
(hc.has_fderiv_at.mul_const d).fderiv

theorem has_strict_fderiv_at.const_mul (ha : has_strict_fderiv_at a a' x) (b : 𝔸) :
  has_strict_fderiv_at (λ y, b * a y) (b • a') x :=
(((continuous_linear_map.mul 𝕜 𝔸) b).has_strict_fderiv_at).comp x ha

theorem has_fderiv_within_at.const_mul
  (ha : has_fderiv_within_at a a' s x) (b : 𝔸) :
  has_fderiv_within_at (λ y, b * a y) (b • a') s x :=
(((continuous_linear_map.mul 𝕜 𝔸) b).has_fderiv_at).comp_has_fderiv_within_at x ha

theorem has_fderiv_at.const_mul (ha : has_fderiv_at a a' x) (b : 𝔸) :
  has_fderiv_at (λ y, b * a y) (b • a') x :=
(((continuous_linear_map.mul 𝕜 𝔸) b).has_fderiv_at).comp x ha

lemma differentiable_within_at.const_mul
  (ha : differentiable_within_at 𝕜 a s x) (b : 𝔸) :
  differentiable_within_at 𝕜 (λ y, b * a y) s x :=
(ha.has_fderiv_within_at.const_mul b).differentiable_within_at

lemma differentiable_at.const_mul (ha : differentiable_at 𝕜 a x) (b : 𝔸) :
  differentiable_at 𝕜 (λ y, b * a y) x :=
(ha.has_fderiv_at.const_mul b).differentiable_at

lemma differentiable_on.const_mul (ha : differentiable_on 𝕜 a s) (b : 𝔸) :
  differentiable_on 𝕜 (λ y, b * a y) s :=
λx hx, (ha x hx).const_mul b

lemma differentiable.const_mul (ha : differentiable 𝕜 a) (b : 𝔸) :
  differentiable 𝕜 (λ y, b * a y) :=
λx, (ha x).const_mul b

lemma fderiv_within_const_mul (hxs : unique_diff_within_at 𝕜 s x)
  (ha : differentiable_within_at 𝕜 a s x) (b : 𝔸) :
  fderiv_within 𝕜 (λ y, b * a y) s x = b • fderiv_within 𝕜 a s x :=
(ha.has_fderiv_within_at.const_mul b).fderiv_within hxs

lemma fderiv_const_mul (ha : differentiable_at 𝕜 a x) (b : 𝔸) :
  fderiv 𝕜 (λ y, b * a y) x = b • fderiv 𝕜 a x :=
(ha.has_fderiv_at.const_mul b).fderiv

end mul

section algebra_inverse
variables {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R]
open normed_ring continuous_linear_map ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `λ t, - x⁻¹ * t * x⁻¹`. -/
lemma has_fderiv_at_ring_inverse (x : Rˣ) :
  has_fderiv_at ring.inverse (-mul_left_right 𝕜 R ↑x⁻¹ ↑x⁻¹) x :=
begin
  have h_is_o : (λ (t : R), inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] (λ (t : R), t),
  { refine (inverse_add_norm_diff_second_order x).trans_is_o ((is_o_norm_norm).mp _),
    simp only [norm_pow, norm_norm],
    have h12 : 1 < 2 := by norm_num,
    convert (asymptotics.is_o_pow_pow h12).comp_tendsto tendsto_norm_zero,
    ext, simp },
  have h_lim : tendsto (λ (y:R), y - x) (𝓝 x) (𝓝 0),
  { refine tendsto_zero_iff_norm_tendsto_zero.mpr _,
    exact tendsto_iff_norm_tendsto_zero.mp tendsto_id },
  simp only [has_fderiv_at, has_fderiv_at_filter],
  convert h_is_o.comp_tendsto h_lim,
  ext y,
  simp only [coe_comp', function.comp_app, mul_left_right_apply, neg_apply, inverse_unit x,
    units.inv_mul, add_sub_cancel'_right, mul_sub, sub_mul, one_mul, sub_neg_eq_add]
end

lemma differentiable_at_inverse (x : Rˣ) : differentiable_at 𝕜 (@ring.inverse R _) x :=
(has_fderiv_at_ring_inverse x).differentiable_at

lemma fderiv_inverse (x : Rˣ) :
  fderiv 𝕜 (@ring.inverse R _) x = - mul_left_right 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
(has_fderiv_at_ring_inverse x).fderiv

end algebra_inverse

namespace continuous_linear_equiv
/-! ### Differentiability of linear equivs, and invariance of differentiability -/

variable (iso : E ≃L[𝕜] F)

protected lemma has_strict_fderiv_at :
  has_strict_fderiv_at iso (iso : E →L[𝕜] F) x :=
iso.to_continuous_linear_map.has_strict_fderiv_at

protected lemma has_fderiv_within_at :
  has_fderiv_within_at iso (iso : E →L[𝕜] F) s x :=
iso.to_continuous_linear_map.has_fderiv_within_at

protected lemma has_fderiv_at : has_fderiv_at iso (iso : E →L[𝕜] F) x :=
iso.to_continuous_linear_map.has_fderiv_at_filter

protected lemma differentiable_at : differentiable_at 𝕜 iso x :=
iso.has_fderiv_at.differentiable_at

protected lemma differentiable_within_at :
  differentiable_within_at 𝕜 iso s x :=
iso.differentiable_at.differentiable_within_at

protected lemma fderiv : fderiv 𝕜 iso x = iso :=
iso.has_fderiv_at.fderiv

protected lemma fderiv_within (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 iso s x = iso :=
iso.to_continuous_linear_map.fderiv_within hxs

protected lemma differentiable : differentiable 𝕜 iso :=
λx, iso.differentiable_at

protected lemma differentiable_on : differentiable_on 𝕜 iso s :=
iso.differentiable.differentiable_on

lemma comp_differentiable_within_at_iff {f : G → E} {s : set G} {x : G} :
  differentiable_within_at 𝕜 (iso ∘ f) s x ↔ differentiable_within_at 𝕜 f s x :=
begin
  refine ⟨λ H, _, λ H, iso.differentiable.differentiable_at.comp_differentiable_within_at x H⟩,
  have : differentiable_within_at 𝕜 (iso.symm ∘ (iso ∘ f)) s x :=
    iso.symm.differentiable.differentiable_at.comp_differentiable_within_at x H,
  rwa [← function.comp.assoc iso.symm iso f, iso.symm_comp_self] at this,
end

lemma comp_differentiable_at_iff {f : G → E} {x : G} :
  differentiable_at 𝕜 (iso ∘ f) x ↔ differentiable_at 𝕜 f x :=
by rw [← differentiable_within_at_univ, ← differentiable_within_at_univ,
       iso.comp_differentiable_within_at_iff]

lemma comp_differentiable_on_iff {f : G → E} {s : set G} :
  differentiable_on 𝕜 (iso ∘ f) s ↔ differentiable_on 𝕜 f s :=
begin
  rw [differentiable_on, differentiable_on],
  simp only [iso.comp_differentiable_within_at_iff],
end

lemma comp_differentiable_iff {f : G → E} :
  differentiable 𝕜 (iso ∘ f) ↔ differentiable 𝕜 f :=
begin
  rw [← differentiable_on_univ, ← differentiable_on_univ],
  exact iso.comp_differentiable_on_iff
end

lemma comp_has_fderiv_within_at_iff
  {f : G → E} {s : set G} {x : G} {f' : G →L[𝕜] E} :
  has_fderiv_within_at (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ has_fderiv_within_at f f' s x :=
begin
  refine ⟨λ H, _, λ H, iso.has_fderiv_at.comp_has_fderiv_within_at x H⟩,
  have A : f = iso.symm ∘ (iso ∘ f), by { rw [← function.comp.assoc, iso.symm_comp_self], refl },
  have B : f' = (iso.symm : F →L[𝕜] E).comp ((iso : E →L[𝕜] F).comp f'),
    by rw [← continuous_linear_map.comp_assoc, iso.coe_symm_comp_coe,
             continuous_linear_map.id_comp],
  rw [A, B],
  exact iso.symm.has_fderiv_at.comp_has_fderiv_within_at x H
end

lemma comp_has_strict_fderiv_at_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
  has_strict_fderiv_at (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ has_strict_fderiv_at f f' x :=
begin
  refine ⟨λ H, _, λ H, iso.has_strict_fderiv_at.comp x H⟩,
  convert iso.symm.has_strict_fderiv_at.comp x H; ext z; apply (iso.symm_apply_apply _).symm
end

lemma comp_has_fderiv_at_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
  has_fderiv_at (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ has_fderiv_at f f' x :=
by simp_rw [← has_fderiv_within_at_univ, iso.comp_has_fderiv_within_at_iff]

lemma comp_has_fderiv_within_at_iff'
  {f : G → E} {s : set G} {x : G} {f' : G →L[𝕜] F} :
  has_fderiv_within_at (iso ∘ f) f' s x ↔
  has_fderiv_within_at f ((iso.symm : F →L[𝕜] E).comp f') s x :=
by rw [← iso.comp_has_fderiv_within_at_iff, ← continuous_linear_map.comp_assoc,
  iso.coe_comp_coe_symm, continuous_linear_map.id_comp]

lemma comp_has_fderiv_at_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
  has_fderiv_at (iso ∘ f) f' x ↔ has_fderiv_at f ((iso.symm : F →L[𝕜] E).comp f') x :=
by simp_rw [← has_fderiv_within_at_univ, iso.comp_has_fderiv_within_at_iff']

lemma comp_fderiv_within {f : G → E} {s : set G} {x : G}
  (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderiv_within 𝕜 f s x) :=
begin
  by_cases h : differentiable_within_at 𝕜 f s x,
  { rw [fderiv.comp_fderiv_within x iso.differentiable_at h hxs, iso.fderiv] },
  { have : ¬differentiable_within_at 𝕜 (iso ∘ f) s x,
      from mt iso.comp_differentiable_within_at_iff.1 h,
    rw [fderiv_within_zero_of_not_differentiable_within_at h,
        fderiv_within_zero_of_not_differentiable_within_at this,
        continuous_linear_map.comp_zero] }
end

lemma comp_fderiv {f : G → E} {x : G} :
  fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
begin
  rw [← fderiv_within_univ, ← fderiv_within_univ],
  exact iso.comp_fderiv_within unique_diff_within_at_univ,
end

lemma comp_right_differentiable_within_at_iff {f : F → G} {s : set F} {x : E} :
  differentiable_within_at 𝕜 (f ∘ iso) (iso ⁻¹' s) x ↔ differentiable_within_at 𝕜 f s (iso x) :=
begin
  refine ⟨λ H, _, λ H, H.comp x iso.differentiable_within_at (maps_to_preimage _ s)⟩,
  have : differentiable_within_at 𝕜 ((f ∘ iso) ∘ iso.symm) s (iso x),
  { rw ← iso.symm_apply_apply x at H,
    apply H.comp (iso x) iso.symm.differentiable_within_at,
    assume y hy,
    simpa only [mem_preimage, apply_symm_apply] using hy },
  rwa [function.comp.assoc, iso.self_comp_symm] at this,
end

lemma comp_right_differentiable_at_iff {f : F → G} {x : E} :
  differentiable_at 𝕜 (f ∘ iso) x ↔ differentiable_at 𝕜 f (iso x) :=
by simp only [← differentiable_within_at_univ, ← iso.comp_right_differentiable_within_at_iff,
  preimage_univ]

lemma comp_right_differentiable_on_iff {f : F → G} {s : set F} :
  differentiable_on 𝕜 (f ∘ iso) (iso ⁻¹' s) ↔ differentiable_on 𝕜 f s :=
begin
  refine ⟨λ H y hy, _, λ H y hy, iso.comp_right_differentiable_within_at_iff.2 (H _ hy)⟩,
  rw [← iso.apply_symm_apply y, ← comp_right_differentiable_within_at_iff],
  apply H,
  simpa only [mem_preimage, apply_symm_apply] using hy,
end

lemma comp_right_differentiable_iff {f : F → G} :
  differentiable 𝕜 (f ∘ iso) ↔ differentiable 𝕜 f :=
by simp only [← differentiable_on_univ, ← iso.comp_right_differentiable_on_iff, preimage_univ]

lemma comp_right_has_fderiv_within_at_iff
  {f : F → G} {s : set F} {x : E} {f' : F →L[𝕜] G} :
  has_fderiv_within_at (f ∘ iso) (f'.comp (iso : E →L[𝕜] F)) (iso ⁻¹' s) x ↔
    has_fderiv_within_at f f' s (iso x) :=
begin
  refine ⟨λ H, _, λ H, H.comp x iso.has_fderiv_within_at (maps_to_preimage _ s)⟩,
  rw [← iso.symm_apply_apply x] at H,
  have A : f = (f ∘ iso) ∘ iso.symm, by { rw [function.comp.assoc, iso.self_comp_symm], refl },
  have B : f' =  (f'.comp (iso : E →L[𝕜] F)).comp (iso.symm : F →L[𝕜] E),
    by rw [continuous_linear_map.comp_assoc, iso.coe_comp_coe_symm,
             continuous_linear_map.comp_id],
  rw [A, B],
  apply H.comp (iso x) iso.symm.has_fderiv_within_at,
  assume y hy,
  simpa only [mem_preimage, apply_symm_apply] using hy
end

lemma comp_right_has_fderiv_at_iff {f : F → G} {x : E} {f' : F →L[𝕜] G} :
  has_fderiv_at (f ∘ iso) (f'.comp (iso : E →L[𝕜] F)) x ↔ has_fderiv_at f f' (iso x) :=
by simp only [← has_fderiv_within_at_univ, ← comp_right_has_fderiv_within_at_iff, preimage_univ]

lemma comp_right_has_fderiv_within_at_iff'
  {f : F → G} {s : set F} {x : E} {f' : E →L[𝕜] G} :
  has_fderiv_within_at (f ∘ iso) f' (iso ⁻¹' s) x ↔
  has_fderiv_within_at f (f'.comp (iso.symm : F →L[𝕜] E)) s (iso x) :=
by rw [← iso.comp_right_has_fderiv_within_at_iff, continuous_linear_map.comp_assoc,
    iso.coe_symm_comp_coe, continuous_linear_map.comp_id]

lemma comp_right_has_fderiv_at_iff' {f : F → G} {x : E} {f' : E →L[𝕜] G} :
  has_fderiv_at (f ∘ iso) f' x ↔ has_fderiv_at f (f'.comp (iso.symm : F →L[𝕜] E)) (iso x) :=
by simp only [← has_fderiv_within_at_univ, ← iso.comp_right_has_fderiv_within_at_iff',
  preimage_univ]

lemma comp_right_fderiv_within {f : F → G} {s : set F} {x : E}
  (hxs : unique_diff_within_at 𝕜 (iso ⁻¹' s) x) :
  fderiv_within 𝕜 (f ∘ iso) (iso ⁻¹'s) x = (fderiv_within 𝕜 f s (iso x)).comp (iso : E →L[𝕜] F) :=
begin
  by_cases h : differentiable_within_at 𝕜 f s (iso x),
  { exact (iso.comp_right_has_fderiv_within_at_iff.2 (h.has_fderiv_within_at)).fderiv_within hxs },
  { have : ¬ differentiable_within_at 𝕜 (f ∘ iso) (iso ⁻¹' s) x,
    { assume h', exact h (iso.comp_right_differentiable_within_at_iff.1 h') },
    rw [fderiv_within_zero_of_not_differentiable_within_at h,
        fderiv_within_zero_of_not_differentiable_within_at this, continuous_linear_map.zero_comp] }
end

lemma comp_right_fderiv {f : F → G} {x : E} :
  fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 f (iso x)).comp (iso : E →L[𝕜] F) :=
begin
  rw [← fderiv_within_univ, ← fderiv_within_univ, ← iso.comp_right_fderiv_within, preimage_univ],
  exact unique_diff_within_at_univ,
end

end continuous_linear_equiv

namespace linear_isometry_equiv
/-! ### Differentiability of linear isometry equivs, and invariance of differentiability -/

variable (iso : E ≃ₗᵢ[𝕜] F)

protected lemma has_strict_fderiv_at : has_strict_fderiv_at iso (iso : E →L[𝕜] F) x :=
(iso : E ≃L[𝕜] F).has_strict_fderiv_at

protected lemma has_fderiv_within_at : has_fderiv_within_at iso (iso : E →L[𝕜] F) s x :=
(iso : E ≃L[𝕜] F).has_fderiv_within_at

protected lemma has_fderiv_at : has_fderiv_at iso (iso : E →L[𝕜] F) x :=
(iso : E ≃L[𝕜] F).has_fderiv_at

protected lemma differentiable_at : differentiable_at 𝕜 iso x :=
iso.has_fderiv_at.differentiable_at

protected lemma differentiable_within_at :
  differentiable_within_at 𝕜 iso s x :=
iso.differentiable_at.differentiable_within_at

protected lemma fderiv : fderiv 𝕜 iso x = iso := iso.has_fderiv_at.fderiv

protected lemma fderiv_within (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 iso s x = iso :=
(iso : E ≃L[𝕜] F).fderiv_within hxs

protected lemma differentiable : differentiable 𝕜 iso :=
λx, iso.differentiable_at

protected lemma differentiable_on : differentiable_on 𝕜 iso s :=
iso.differentiable.differentiable_on

lemma comp_differentiable_within_at_iff {f : G → E} {s : set G} {x : G} :
  differentiable_within_at 𝕜 (iso ∘ f) s x ↔ differentiable_within_at 𝕜 f s x :=
(iso : E ≃L[𝕜] F).comp_differentiable_within_at_iff

lemma comp_differentiable_at_iff {f : G → E} {x : G} :
  differentiable_at 𝕜 (iso ∘ f) x ↔ differentiable_at 𝕜 f x :=
(iso : E ≃L[𝕜] F).comp_differentiable_at_iff

lemma comp_differentiable_on_iff {f : G → E} {s : set G} :
  differentiable_on 𝕜 (iso ∘ f) s ↔ differentiable_on 𝕜 f s :=
(iso : E ≃L[𝕜] F).comp_differentiable_on_iff

lemma comp_differentiable_iff {f : G → E} :
  differentiable 𝕜 (iso ∘ f) ↔ differentiable 𝕜 f :=
(iso : E ≃L[𝕜] F).comp_differentiable_iff

lemma comp_has_fderiv_within_at_iff
  {f : G → E} {s : set G} {x : G} {f' : G →L[𝕜] E} :
  has_fderiv_within_at (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ has_fderiv_within_at f f' s x :=
(iso : E ≃L[𝕜] F).comp_has_fderiv_within_at_iff

lemma comp_has_strict_fderiv_at_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
  has_strict_fderiv_at (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ has_strict_fderiv_at f f' x :=
(iso : E ≃L[𝕜] F).comp_has_strict_fderiv_at_iff

lemma comp_has_fderiv_at_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
  has_fderiv_at (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ has_fderiv_at f f' x :=
(iso : E ≃L[𝕜] F).comp_has_fderiv_at_iff

lemma comp_has_fderiv_within_at_iff'
  {f : G → E} {s : set G} {x : G} {f' : G →L[𝕜] F} :
  has_fderiv_within_at (iso ∘ f) f' s x ↔
  has_fderiv_within_at f ((iso.symm : F →L[𝕜] E).comp f') s x :=
(iso : E ≃L[𝕜] F).comp_has_fderiv_within_at_iff'

lemma comp_has_fderiv_at_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
  has_fderiv_at (iso ∘ f) f' x ↔ has_fderiv_at f ((iso.symm : F →L[𝕜] E).comp f') x :=
(iso : E ≃L[𝕜] F).comp_has_fderiv_at_iff'

lemma comp_fderiv_within {f : G → E} {s : set G} {x : G}
  (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderiv_within 𝕜 f s x) :=
(iso : E ≃L[𝕜] F).comp_fderiv_within hxs

lemma comp_fderiv {f : G → E} {x : G} :
  fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
(iso : E ≃L[𝕜] F).comp_fderiv

end linear_isometry_equiv

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem has_strict_fderiv_at.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
  (hg : continuous_at g a) (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) (g a))
  (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
  has_strict_fderiv_at g (f'.symm : F →L[𝕜] E) a :=
begin
  replace hg := hg.prod_map' hg,
  replace hfg := hfg.prod_mk_nhds hfg,
  have : (λ p : F × F, g p.1 - g p.2 - f'.symm (p.1 - p.2)) =O[𝓝 (a, a)]
    (λ p : F × F, f' (g p.1 - g p.2) - (p.1 - p.2)),
  { refine ((f'.symm : F →L[𝕜] E).is_O_comp _ _).congr (λ x, _) (λ _, rfl),
    simp },
  refine this.trans_is_o _, clear this,
  refine ((hf.comp_tendsto hg).symm.congr' (hfg.mono _)
    (eventually_of_forall $ λ _, rfl)).trans_is_O _,
  { rintros p ⟨hp1, hp2⟩,
    simp [hp1, hp2] },
  { refine (hf.is_O_sub_rev.comp_tendsto hg).congr'
      (eventually_of_forall $ λ _, rfl) (hfg.mono _),
    rintros p ⟨hp1, hp2⟩,
    simp only [(∘), hp1, hp2] }
end

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem has_fderiv_at.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
  (hg : continuous_at g a) (hf : has_fderiv_at f (f' : E →L[𝕜] F) (g a))
  (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
  has_fderiv_at g (f'.symm : F →L[𝕜] E) a :=
begin
  have : (λ x : F, g x - g a - f'.symm (x - a)) =O[𝓝 a] (λ x : F, f' (g x - g a) - (x - a)),
  { refine ((f'.symm : F →L[𝕜] E).is_O_comp _ _).congr (λ x, _) (λ _, rfl),
    simp },
  refine this.trans_is_o _, clear this,
  refine ((hf.comp_tendsto hg).symm.congr' (hfg.mono _)
    (eventually_of_forall $ λ _, rfl)).trans_is_O _,
  { rintros p hp,
    simp [hp, hfg.self_of_nhds] },
  { refine ((hf.is_O_sub_rev f'.antilipschitz).comp_tendsto hg).congr'
      (eventually_of_forall $ λ _, rfl) (hfg.mono _),
    rintros p hp,
    simp only [(∘), hp, hfg.self_of_nhds] }
end

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` in the sense of strict differentiability at `f.symm a`, then `f.symm` has
the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
lemma local_homeomorph.has_strict_fderiv_at_symm (f : local_homeomorph E F) {f' : E ≃L[𝕜] F} {a : F}
  (ha : a ∈ f.target) (htff' : has_strict_fderiv_at f (f' : E →L[𝕜] F) (f.symm a)) :
  has_strict_fderiv_at f.symm (f'.symm : F →L[𝕜] E) a :=
htff'.of_local_left_inverse (f.symm.continuous_at ha) (f.eventually_right_inverse ha)

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
lemma local_homeomorph.has_fderiv_at_symm (f : local_homeomorph E F) {f' : E ≃L[𝕜] F} {a : F}
  (ha : a ∈ f.target) (htff' : has_fderiv_at f (f' : E →L[𝕜] F) (f.symm a)) :
  has_fderiv_at f.symm (f'.symm : F →L[𝕜] E) a :=
htff'.of_local_left_inverse (f.symm.continuous_at ha) (f.eventually_right_inverse ha)

lemma has_fderiv_within_at.eventually_ne (h : has_fderiv_within_at f f' s x)
  (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) :
  ∀ᶠ z in 𝓝[s \ {x}] x, f z ≠ f x :=
begin
  rw [nhds_within, diff_eq, ← inf_principal, ← inf_assoc, eventually_inf_principal],
  have A : (λ z, z - x) =O[𝓝[s] x] (λ z, f' (z - x)) :=
    (is_O_iff.2 $ hf'.imp $ λ C hC, eventually_of_forall $ λ z, hC _),
  have : (λ z, f z - f x) ~[𝓝[s] x] (λ z, f' (z - x)) := h.trans_is_O A,
  simpa [not_imp_not, sub_eq_zero] using (A.trans this.is_O_symm).eq_zero_imp
end

lemma has_fderiv_at.eventually_ne (h : has_fderiv_at f f' x) (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) :
  ∀ᶠ z in 𝓝[≠] x, f z ≠ f x :=
by simpa only [compl_eq_univ_diff] using (has_fderiv_within_at_univ.2 h).eventually_ne hf'

end

section
/-
  In the special case of a normed space over the reals,
  we can use  scalar multiplication in the `tendsto` characterization
  of the Fréchet derivative.
-/


variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
variables {F : Type*} [normed_add_comm_group F] [normed_space ℝ F]
variables {f : E → F} {f' : E →L[ℝ] F} {x : E}

theorem has_fderiv_at_filter_real_equiv {L : filter E} :
  tendsto (λ x' : E, ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) ↔
  tendsto (λ x' : E, ‖x' - x‖⁻¹ • (f x' - f x - f' (x' - x))) L (𝓝 0) :=
begin
  symmetry,
  rw [tendsto_iff_norm_tendsto_zero], refine tendsto_congr (λ x', _),
  have : ‖x' - x‖⁻¹ ≥ 0, from inv_nonneg.mpr (norm_nonneg _),
  simp [norm_smul, abs_of_nonneg this]
end

lemma has_fderiv_at.lim_real (hf : has_fderiv_at f f' x) (v : E) :
  tendsto (λ (c:ℝ), c • (f (x + c⁻¹ • v) - f x)) at_top (𝓝 (f' v)) :=
begin
  apply hf.lim v,
  rw tendsto_at_top_at_top,
  exact λ b, ⟨b, λ a ha, le_trans ha (le_abs_self _)⟩
end

end

section tangent_cone

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{f : E → F} {s : set E} {f' : E →L[𝕜] F}

/-- The image of a tangent cone under the differential of a map is included in the tangent cone to
the image. -/
lemma has_fderiv_within_at.maps_to_tangent_cone {x : E} (h : has_fderiv_within_at f f' s x) :
  maps_to f' (tangent_cone_at 𝕜 s x) (tangent_cone_at 𝕜 (f '' s) (f x)) :=
begin
  rintros v ⟨c, d, dtop, clim, cdlim⟩,
  refine ⟨c, (λn, f (x + d n) - f x), mem_of_superset dtop _, clim,
    h.lim at_top dtop clim cdlim⟩,
  simp [-mem_image, mem_image_of_mem] {contextual := tt}
end

/-- If a set has the unique differentiability property at a point x, then the image of this set
under a map with onto derivative has also the unique differentiability property at the image point.
-/
lemma has_fderiv_within_at.unique_diff_within_at {x : E} (h : has_fderiv_within_at f f' s x)
  (hs : unique_diff_within_at 𝕜 s x) (h' : dense_range f') :
  unique_diff_within_at 𝕜 (f '' s) (f x) :=
begin
  refine ⟨h'.dense_of_maps_to f'.continuous hs.1 _,
    h.continuous_within_at.mem_closure_image hs.2⟩,
  show submodule.span 𝕜 (tangent_cone_at 𝕜 s x) ≤
    (submodule.span 𝕜 (tangent_cone_at 𝕜 (f '' s) (f x))).comap f',
  rw [submodule.span_le],
  exact h.maps_to_tangent_cone.mono (subset.refl _) submodule.subset_span
end

lemma unique_diff_on.image {f' : E → E →L[𝕜] F} (hs : unique_diff_on 𝕜 s)
  (hf' : ∀ x ∈ s, has_fderiv_within_at f (f' x) s x) (hd : ∀ x ∈ s, dense_range (f' x)) :
  unique_diff_on 𝕜 (f '' s) :=
ball_image_iff.2 $ λ x hx, (hf' x hx).unique_diff_within_at (hs x hx) (hd x hx)

lemma has_fderiv_within_at.unique_diff_within_at_of_continuous_linear_equiv
  {x : E} (e' : E ≃L[𝕜] F) (h : has_fderiv_within_at f (e' : E →L[𝕜] F) s x)
  (hs : unique_diff_within_at 𝕜 s x) :
  unique_diff_within_at 𝕜 (f '' s) (f x) :=
h.unique_diff_within_at hs e'.surjective.dense_range

lemma continuous_linear_equiv.unique_diff_on_image (e : E ≃L[𝕜] F) (h : unique_diff_on 𝕜 s) :
  unique_diff_on 𝕜 (e '' s) :=
h.image (λ x _, e.has_fderiv_within_at) (λ x hx, e.surjective.dense_range)

@[simp] lemma continuous_linear_equiv.unique_diff_on_image_iff (e : E ≃L[𝕜] F) :
  unique_diff_on 𝕜 (e '' s) ↔ unique_diff_on 𝕜 s :=
⟨λ h, e.symm_image_image s ▸ e.symm.unique_diff_on_image h, e.unique_diff_on_image⟩

@[simp] lemma continuous_linear_equiv.unique_diff_on_preimage_iff (e : F ≃L[𝕜] E) :
  unique_diff_on 𝕜 (e ⁻¹' s) ↔ unique_diff_on 𝕜 s :=
by rw [← e.image_symm_eq_preimage, e.symm.unique_diff_on_image_iff]

end tangent_cone

section restrict_scalars
/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/

variables (𝕜 : Type*) [nontrivially_normed_field 𝕜]
variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] [normed_space 𝕜' E]
variables [is_scalar_tower 𝕜 𝕜' E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
variables [is_scalar_tower 𝕜 𝕜' F]
variables {f : E → F} {f' : E →L[𝕜'] F} {s : set E} {x : E}

lemma has_strict_fderiv_at.restrict_scalars (h : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at f (f'.restrict_scalars 𝕜) x := h

lemma has_fderiv_at_filter.restrict_scalars {L} (h : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter f (f'.restrict_scalars 𝕜) x L := h

lemma has_fderiv_at.restrict_scalars (h : has_fderiv_at f f' x) :
  has_fderiv_at f (f'.restrict_scalars 𝕜) x := h

lemma has_fderiv_within_at.restrict_scalars (h : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at f (f'.restrict_scalars 𝕜) s x := h

lemma differentiable_at.restrict_scalars (h : differentiable_at 𝕜' f x) :
  differentiable_at 𝕜 f x :=
(h.has_fderiv_at.restrict_scalars 𝕜).differentiable_at

lemma differentiable_within_at.restrict_scalars (h : differentiable_within_at 𝕜' f s x) :
  differentiable_within_at 𝕜 f s x :=
(h.has_fderiv_within_at.restrict_scalars 𝕜).differentiable_within_at

lemma differentiable_on.restrict_scalars (h : differentiable_on 𝕜' f s) :
  differentiable_on 𝕜 f s :=
λx hx, (h x hx).restrict_scalars 𝕜

lemma differentiable.restrict_scalars (h : differentiable 𝕜' f) :
  differentiable 𝕜 f :=
λx, (h x).restrict_scalars 𝕜

lemma has_fderiv_within_at_of_restrict_scalars
  {g' : E →L[𝕜] F} (h : has_fderiv_within_at f g' s x)
  (H : f'.restrict_scalars 𝕜 = g') : has_fderiv_within_at f f' s x :=
by { rw ← H at h, exact h }

lemma has_fderiv_at_of_restrict_scalars {g' : E →L[𝕜] F} (h : has_fderiv_at f g' x)
  (H : f'.restrict_scalars 𝕜 = g') : has_fderiv_at f f' x :=
by { rw ← H at h, exact h }

lemma differentiable_at.fderiv_restrict_scalars (h : differentiable_at 𝕜' f x) :
  fderiv 𝕜 f x = (fderiv 𝕜' f x).restrict_scalars 𝕜 :=
(h.has_fderiv_at.restrict_scalars 𝕜).fderiv

lemma differentiable_within_at_iff_restrict_scalars
  (hf : differentiable_within_at 𝕜 f s x) (hs : unique_diff_within_at 𝕜 s x) :
  differentiable_within_at 𝕜' f s x ↔
  ∃ (g' : E →L[𝕜'] F), g'.restrict_scalars 𝕜 = fderiv_within 𝕜 f s x :=
begin
  split,
  { rintros ⟨g', hg'⟩,
    exact ⟨g', hs.eq (hg'.restrict_scalars 𝕜) hf.has_fderiv_within_at⟩, },
  { rintros ⟨f', hf'⟩,
    exact ⟨f', has_fderiv_within_at_of_restrict_scalars 𝕜 hf.has_fderiv_within_at hf'⟩, },
end

lemma differentiable_at_iff_restrict_scalars (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜' f x ↔ ∃ (g' : E →L[𝕜'] F), g'.restrict_scalars 𝕜 = fderiv 𝕜 f x :=
begin
  rw [← differentiable_within_at_univ, ← fderiv_within_univ],
  exact differentiable_within_at_iff_restrict_scalars 𝕜
    hf.differentiable_within_at unique_diff_within_at_univ,
end

end restrict_scalars

/-! ### Support of derivatives -/

section support

open function
variables (𝕜 : Type*) {E F : Type*} [nontrivially_normed_field 𝕜] [normed_add_comm_group E]
  [normed_space 𝕜 E] [normed_add_comm_group F] [normed_space 𝕜 F] {f : E → F}

lemma support_fderiv_subset : support (fderiv 𝕜 f) ⊆ tsupport f :=
begin
  intros x,
  rw [← not_imp_not],
  intro h2x,
  rw [not_mem_tsupport_iff_eventually_eq] at h2x,
  exact nmem_support.mpr (h2x.fderiv_eq.trans $ fderiv_const_apply 0),
end

lemma has_compact_support.fderiv (hf : has_compact_support f) : has_compact_support (fderiv 𝕜 f) :=
hf.mono' $ support_fderiv_subset 𝕜

end support
