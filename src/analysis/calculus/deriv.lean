/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
import analysis.calculus.fderiv

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.lean). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

 - `has_deriv_at_filter f f' x L` states that the function `f` has the
    derivative `f'` at the point `x` as `x` goes along the filter `L`.

 - `has_deriv_within_at f f' s x` states that the function `f` has the
    derivative `f'` at the point `x` within the subset `s`.

 - `has_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x`.

For the last two notions we also define a functional version:

  - `deriv_within f s x` is a derivative of `f` at `x` within `s`. If the
    derivative does not exist, then `deriv_within f s x` equals zero.

  - `deriv f x` is a derivative of `f` at `x`. If the derivative does not
    exist, then `deriv f x` equals zero.

The theorems `fderiv_within_deriv_within` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps
  - addition
  - negation
  - subtraction
  - multiplication
  - inverse `x → x⁻¹`
  - multiplication of two functions in `𝕜 → 𝕜`
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E`
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜`
  - composition of a function in `F → E` with a function in `𝕜 → F`
  - division
  - polynomials

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

-/

universes u v w
noncomputable theory
open_locale classical topological_space
open filter asymptotics set
open continuous_linear_map (smul_right smul_right_one_eq_iff)

set_option class.instance_max_depth 100

variables {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
variables {F : Type v} [normed_group F] [normed_space 𝕜 F]
variables {E : Type w} [normed_group E] [normed_space 𝕜 E]

/--
`f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def has_deriv_at_filter (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : filter 𝕜) :=
has_fderiv_at_filter f (smul_right 1 f' : 𝕜 →L[𝕜] F) x L

/--
`f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def has_deriv_within_at (f : 𝕜 → F) (f' : F) (s : set 𝕜) (x : 𝕜) :=
has_deriv_at_filter f f' x (nhds_within x s)

/--
`f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def has_deriv_at (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
has_deriv_at_filter f f' x (𝓝 x)

/--
Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_within_at f f' s x`), then
`f x' = f x + (x' - x) • deriv_within f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def deriv_within (f : 𝕜 → F) (s : set 𝕜) (x : 𝕜) :=
(fderiv_within 𝕜 f s x : 𝕜 →L[𝕜] F) 1

/--
Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_at f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
(fderiv 𝕜 f x : 𝕜 →L[𝕜] F) 1

variables {f f₀ f₁ g : 𝕜 → F}
variables {f' f₀' f₁' g' : F}
variables {x : 𝕜}
variables {s t : set 𝕜}
variables {L L₁ L₂ : filter 𝕜}

/-- Expressing `has_fderiv_at_filter f f' x L` in terms of `has_deriv_at_filter` -/
lemma has_fderiv_at_filter_iff_has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at_filter f f' x L ↔ has_deriv_at_filter f (f' 1) x L :=
by simp [has_deriv_at_filter]

/-- Expressing `has_fderiv_within_at f f' s x` in terms of `has_deriv_within_at` -/
lemma has_fderiv_within_at_iff_has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_within_at f f' s x ↔ has_deriv_within_at f (f' 1) s x :=
by simp [has_deriv_within_at, has_deriv_at_filter, has_fderiv_within_at]

/-- Expressing `has_deriv_within_at f f' s x` in terms of `has_fderiv_within_at` -/
lemma has_deriv_within_at_iff_has_fderiv_within_at {f' : F} :
  has_deriv_within_at f f' s x ↔
  has_fderiv_within_at f (smul_right 1 f' : 𝕜 →L[𝕜] F) s x :=
iff.rfl

/-- Expressing `has_fderiv_at f f' x` in terms of `has_deriv_at` -/
lemma has_fderiv_at_iff_has_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at f f' x ↔ has_deriv_at f (f' 1) x :=
by simp [has_deriv_at, has_deriv_at_filter, has_fderiv_at]

/-- Expressing `has_deriv_at f f' x` in terms of `has_fderiv_at` -/
lemma has_deriv_at_iff_has_fderiv_at {f' : F} :
  has_deriv_at f f' x ↔
  has_fderiv_at f (smul_right 1 f' : 𝕜 →L[𝕜] F) x :=
iff.rfl

lemma deriv_within_zero_of_not_differentiable_within_at
  (h : ¬ differentiable_within_at 𝕜 f s x) : deriv_within f s x = 0 :=
by { unfold deriv_within, rw fderiv_within_zero_of_not_differentiable_within_at, simp, assumption }

lemma deriv_zero_of_not_differentiable_at (h : ¬ differentiable_at 𝕜 f x) : deriv f x = 0 :=
by { unfold deriv, rw fderiv_zero_of_not_differentiable_at, simp, assumption }

theorem unique_diff_within_at.eq_deriv (s : set 𝕜) (H : unique_diff_within_at 𝕜 s x)
  (h : has_deriv_within_at f f' s x) (h₁ : has_deriv_within_at f f₁' s x) : f' = f₁' :=
smul_right_one_eq_iff.mp $ unique_diff_within_at.eq H h h₁

theorem has_deriv_at_filter_iff_tendsto :
  has_deriv_at_filter f f' x L ↔
  tendsto (λ x' : 𝕜, ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) L (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_within_at_iff_tendsto : has_deriv_within_at f f' s x ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) (nhds_within x s) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_iff_tendsto : has_deriv_at f f' x ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) (𝓝 x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_iff_is_o_nhds_zero : has_deriv_at f f' x ↔
  is_o (λh, f (x + h) - f x - h • f') (λh, h) (𝓝 0) :=
has_fderiv_at_iff_is_o_nhds_zero

theorem has_deriv_at_filter.mono (h : has_deriv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) :
  has_deriv_at_filter f f' x L₁ :=
has_fderiv_at_filter.mono h hst

theorem has_deriv_within_at.mono (h : has_deriv_within_at f f' t x) (hst : s ⊆ t) :
  has_deriv_within_at f f' s x :=
has_fderiv_within_at.mono h hst

theorem has_deriv_at.has_deriv_at_filter (h : has_deriv_at f f' x) (hL : L ≤ 𝓝 x) :
  has_deriv_at_filter f f' x L :=
has_fderiv_at.has_fderiv_at_filter h hL

theorem has_deriv_at.has_deriv_within_at
  (h : has_deriv_at f f' x) : has_deriv_within_at f f' s x :=
has_fderiv_at.has_fderiv_within_at h

lemma has_deriv_within_at.differentiable_within_at (h : has_deriv_within_at f f' s x) :
  differentiable_within_at 𝕜 f s x :=
has_fderiv_within_at.differentiable_within_at h

lemma has_deriv_at.differentiable_at (h : has_deriv_at f f' x) : differentiable_at 𝕜 f x :=
has_fderiv_at.differentiable_at h

@[simp] lemma has_deriv_within_at_univ : has_deriv_within_at f f' univ x ↔ has_deriv_at f f' x :=
has_fderiv_within_at_univ

theorem has_deriv_at_unique
  (h₀ : has_deriv_at f f₀' x) (h₁ : has_deriv_at f f₁' x) : f₀' = f₁' :=
smul_right_one_eq_iff.mp $ has_fderiv_at_unique h₀ h₁

lemma has_deriv_within_at_inter' (h : t ∈ nhds_within x s) :
  has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_inter' h

lemma has_deriv_within_at_inter (h : t ∈ 𝓝 x) :
  has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_inter h

lemma has_deriv_within_at.nhds_within (h : has_deriv_within_at f f' s x)
  (ht : s ∈ nhds_within x t) : has_deriv_within_at f f' t x :=
(has_deriv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))

lemma differentiable_within_at.has_deriv_within_at (h : differentiable_within_at 𝕜 f s x) :
  has_deriv_within_at f (deriv_within f s x) s x :=
show has_fderiv_within_at _ _ _ _, by { convert h.has_fderiv_within_at, simp [deriv_within] }

lemma differentiable_at.has_deriv_at (h : differentiable_at 𝕜 f x) : has_deriv_at f (deriv f x) x :=
show has_fderiv_at _ _ _, by { convert h.has_fderiv_at, simp [deriv] }

lemma has_deriv_at.deriv (h : has_deriv_at f f' x) : deriv f x = f' :=
has_deriv_at_unique h.differentiable_at.has_deriv_at h

lemma has_deriv_within_at.deriv_within
  (h : has_deriv_within_at f f' s x) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within f s x = f' :=
hxs.eq_deriv _ h.differentiable_within_at.has_deriv_within_at h

lemma fderiv_within_deriv_within : (fderiv_within 𝕜 f s x : 𝕜 → F) 1 = deriv_within f s x :=
rfl

lemma deriv_within_fderiv_within :
  smul_right 1 (deriv_within f s x) = fderiv_within 𝕜 f s x :=
by simp [deriv_within]

lemma fderiv_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
rfl

lemma deriv_fderiv :
  smul_right 1 (deriv f x) = fderiv 𝕜 f x :=
by simp [deriv]

lemma differentiable_at.deriv_within (h : differentiable_at 𝕜 f x)
  (hxs : unique_diff_within_at 𝕜 s x) : deriv_within f s x = deriv f x :=
by { unfold deriv_within deriv, rw h.fderiv_within hxs }

lemma deriv_within_subset (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  deriv_within f s x = deriv_within f t x :=
((differentiable_within_at.has_deriv_within_at h).mono st).deriv_within ht

@[simp] lemma deriv_within_univ : deriv_within f univ = deriv f :=
by { ext, unfold deriv_within deriv, rw fderiv_within_univ }

lemma deriv_within_inter (ht : t ∈ 𝓝 x) (hs : unique_diff_within_at 𝕜 s x) :
  deriv_within f (s ∩ t) x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_inter ht hs }

section congr
/-! ### Congruence properties of derivatives -/

theorem has_deriv_at_filter_congr_of_mem_sets
  (hx : f₀ x = f₁ x) (h₀ : {x | f₀ x = f₁ x} ∈ L) (h₁ : f₀' = f₁') :
  has_deriv_at_filter f₀ f₀' x L ↔ has_deriv_at_filter f₁ f₁' x L :=
has_fderiv_at_filter_congr_of_mem_sets hx h₀ (by simp [h₁])

lemma has_deriv_at_filter.congr_of_mem_sets (h : has_deriv_at_filter f f' x L)
  (hL : {x | f₁ x = f x} ∈ L) (hx : f₁ x = f x) : has_deriv_at_filter f₁ f' x L :=
by rwa has_deriv_at_filter_congr_of_mem_sets hx hL rfl

lemma has_deriv_within_at.congr_mono (h : has_deriv_within_at f f' s x) (ht : ∀x ∈ t, f₁ x = f x)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_deriv_within_at f₁ f' t x :=
has_fderiv_within_at.congr_mono h ht hx h₁

lemma has_deriv_within_at.congr_of_mem_nhds_within (h : has_deriv_within_at f f' s x)
  (h₁ : {y | f₁ y = f y} ∈ nhds_within x s) (hx : f₁ x = f x) : has_deriv_within_at f₁ f' s x :=
has_deriv_at_filter.congr_of_mem_sets h h₁ hx

lemma has_deriv_at.congr_of_mem_nhds (h : has_deriv_at f f' x)
  (h₁ : {y | f₁ y = f y} ∈ 𝓝 x) : has_deriv_at f₁ f' x :=
has_deriv_at_filter.congr_of_mem_sets h h₁ (mem_of_nhds h₁ : _)

lemma deriv_within_congr_of_mem_nhds_within (hs : unique_diff_within_at 𝕜 s x)
  (hL : {y | f₁ y = f y} ∈ nhds_within x s) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_congr_of_mem_nhds_within hs hL hx }

lemma deriv_within_congr (hs : unique_diff_within_at 𝕜 s x)
  (hL : ∀y∈s, f₁ y = f y) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_congr hs hL hx }

lemma deriv_congr_of_mem_nhds (hL : {y | f₁ y = f y} ∈ 𝓝 x) : deriv f₁ x = deriv f x :=
by { unfold deriv, rwa fderiv_congr_of_mem_nhds }

end congr

section id
/-! ### Derivative of the identity -/
variables (s x L)

theorem has_deriv_at_filter_id : has_deriv_at_filter id 1 x L :=
(is_o_zero _ _).congr_left $ by simp

theorem has_deriv_within_at_id : has_deriv_within_at id 1 s x :=
has_deriv_at_filter_id _ _

theorem has_deriv_at_id : has_deriv_at id 1 x :=
has_deriv_at_filter_id _ _

@[simp] lemma deriv_id : deriv id x = 1 :=
has_deriv_at.deriv (has_deriv_at_id x)

lemma deriv_within_id (hxs : unique_diff_within_at 𝕜 s x) : deriv_within id s x = 1 :=
by { unfold deriv_within, rw fderiv_within_id, simp, assumption }

end id

section const
/-! ### Derivative of constant functions -/
variables (c : F) (s x L)

theorem has_deriv_at_filter_const : has_deriv_at_filter (λ x, c) 0 x L :=
(is_o_zero _ _).congr_left $ λ _, by simp [continuous_linear_map.zero_apply, sub_self]

theorem has_deriv_within_at_const : has_deriv_within_at (λ x, c) 0 s x :=
has_deriv_at_filter_const _ _ _

theorem has_deriv_at_const : has_deriv_at (λ x, c) 0 x :=
has_deriv_at_filter_const _ _ _

lemma deriv_const : deriv (λ x, c) x = 0 :=
has_deriv_at.deriv (has_deriv_at_const x c)

lemma deriv_within_const (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (λ x, c) s x = 0 :=
by { rw (differentiable_at_const _).deriv_within hxs, apply deriv_const }

end const

section is_linear_map
/-! ### Derivative of linear maps -/
variables (s x L) [is_linear_map 𝕜 f]

lemma is_linear_map.has_deriv_at_filter : has_deriv_at_filter f (f 1) x L :=
(is_o_zero _ _).congr_left begin
  intro y,
  simp [add_smul],
  rw ← is_linear_map.smul f x,
  rw ← is_linear_map.smul f y,
  simp
end

lemma is_linear_map.has_deriv_within_at : has_deriv_within_at f (f 1) s x :=
is_linear_map.has_deriv_at_filter _ _

lemma is_linear_map.has_deriv_at : has_deriv_at f (f 1) x  :=
is_linear_map.has_deriv_at_filter _ _

lemma is_linear_map.differentiable_at : differentiable_at 𝕜 f x :=
(is_linear_map.has_deriv_at _).differentiable_at

lemma is_linear_map.differentiable_within_at : differentiable_within_at 𝕜 f s x :=
(is_linear_map.differentiable_at _).differentiable_within_at

@[simp] lemma is_linear_map.deriv : deriv f x = f 1 :=
has_deriv_at.deriv (is_linear_map.has_deriv_at _)

lemma is_linear_map.deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within f s x = f 1 :=
begin
  rw differentiable_at.deriv_within (is_linear_map.differentiable_at _) hxs,
  apply is_linear_map.deriv,
  assumption
end

lemma is_linear_map.differentiable : differentiable 𝕜 f :=
λ x, is_linear_map.differentiable_at _

lemma is_linear_map.differentiable_on : differentiable_on 𝕜 f s :=
is_linear_map.differentiable.differentiable_on

end is_linear_map

section add
/-! ### Derivative of the sum of two functions -/

theorem has_deriv_at_filter.add
  (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) :
  has_deriv_at_filter (λ y, f y + g y) (f' + g') x L :=
(hf.add hg).congr_left $ by simp [add_smul, smul_add]

theorem has_deriv_within_at.add
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ y, f y + g y) (f' + g') s x :=
hf.add hg

theorem has_deriv_at.add
  (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) :
  has_deriv_at (λ x, f x + g x) (f' + g') x :=
hf.add hg

lemma deriv_within_add (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  deriv_within (λy, f y + g y) s x = deriv_within f s x + deriv_within g s x :=
(hf.has_deriv_within_at.add hg.has_deriv_within_at).deriv_within hxs

lemma deriv_add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  deriv (λy, f y + g y) x = deriv f x + deriv g x :=
(hf.has_deriv_at.add hg.has_deriv_at).deriv

end add

section neg
/-! ### Derivative of the negative of a function -/

theorem has_deriv_at_filter.neg (h : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ x, -f x) (-f') x L :=
(h.smul (-1)).congr (by simp) (by simp)

theorem has_deriv_within_at.neg (h : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, -f x) (-f') s x :=
h.neg

theorem has_deriv_at.neg (h : has_deriv_at f f' x) : has_deriv_at (λ x, -f x) (-f') x :=
h.neg

lemma deriv_within_neg (hxs : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f s x) :
  deriv_within (λy, -f y) s x = - deriv_within f s x :=
h.has_deriv_within_at.neg.deriv_within hxs

lemma deriv_neg (h : differentiable_at 𝕜 f x) : deriv (λy, -f y) x = - deriv f x :=
h.has_deriv_at.neg.deriv

end neg

section sub
/-! ### Derivative of the difference of two functions -/

theorem has_deriv_at_filter.sub
  (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) :
  has_deriv_at_filter (λ x, f x - g x) (f' - g') x L :=
hf.add hg.neg

theorem has_deriv_within_at.sub
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ x, f x - g x) (f' - g') s x :=
hf.sub hg

theorem has_deriv_at.sub
  (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) :
  has_deriv_at (λ x, f x - g x) (f' - g') x :=
hf.sub hg

lemma deriv_within_sub (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  deriv_within (λy, f y - g y) s x = deriv_within f s x - deriv_within g s x :=
(hf.has_deriv_within_at.sub hg.has_deriv_within_at).deriv_within hxs

lemma deriv_sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  deriv (λ y, f y - g y) x = deriv f x - deriv g x :=
(hf.has_deriv_at.sub hg.has_deriv_at).deriv

theorem has_deriv_at_filter.is_O_sub (h : has_deriv_at_filter f f' x L) :
  is_O (λ x', f x' - f x) (λ x', x' - x) L :=
has_fderiv_at_filter.is_O_sub h

end sub

section continuous
/-! ### Continuity of a function admitting a derivative -/

theorem has_deriv_at_filter.tendsto_nhds
  (hL : L ≤ 𝓝 x) (h : has_deriv_at_filter f f' x L) :
  tendsto f L (𝓝 (f x)) :=
has_fderiv_at_filter.tendsto_nhds hL h

theorem has_deriv_within_at.continuous_within_at
  (h : has_deriv_within_at f f' s x) : continuous_within_at f s x :=
has_deriv_at_filter.tendsto_nhds lattice.inf_le_left h

theorem has_deriv_at.continuous_at (h : has_deriv_at f f' x) : continuous_at f x :=
has_deriv_at_filter.tendsto_nhds (le_refl _) h

end continuous

section cartesian_product
/-! ### Derivative of the cartesian product of two functions -/

variables {G : Type w} [normed_group G] [normed_space 𝕜 G]
variables {f₂ : 𝕜 → G} {f₂' : G}

lemma has_deriv_at_filter.prod
  (hf₁ : has_deriv_at_filter f₁ f₁' x L) (hf₂ : has_deriv_at_filter f₂ f₂' x L) :
  has_deriv_at_filter (λ x, (f₁ x, f₂ x)) (f₁', f₂') x L :=
show has_fderiv_at_filter _ _ _ _,
by convert has_fderiv_at_filter.prod hf₁ hf₂

lemma has_deriv_within_at.prod
  (hf₁ : has_deriv_within_at f₁ f₁' s x) (hf₂ : has_deriv_within_at f₂ f₂' s x) :
  has_deriv_within_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') s x :=
hf₁.prod hf₂

lemma has_deriv_at.prod (hf₁ : has_deriv_at f₁ f₁' x) (hf₂ : has_deriv_at f₂ f₂' x) :
  has_deriv_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') x :=
hf₁.prod hf₂

end cartesian_product

section composition
/-! ### Derivative of the composition of a vector valued function and a scalar function -/

variables {h : 𝕜 → 𝕜} {h' : 𝕜}
/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable (x)

theorem has_deriv_at_filter.comp
  (hg : has_deriv_at_filter g g' (h x) (L.map h))
  (hh : has_deriv_at_filter h h' x L) :
  has_deriv_at_filter (g ∘ h) (h' • g') x L :=
have (smul_right 1 g' : 𝕜 →L[𝕜] _).comp
      (smul_right 1 h' : 𝕜 →L[𝕜] _) =
    smul_right 1 (h' • g'), by { ext, simp [mul_smul] },
begin
  unfold has_deriv_at_filter,
  rw ← this,
  exact has_fderiv_at_filter.comp x hg hh,
end

theorem has_deriv_within_at.comp {t : set 𝕜}
  (hg : has_deriv_within_at g g' t (h x))
  (hh : has_deriv_within_at h h' s x) (hst : s ⊆ h ⁻¹' t) :
  has_deriv_within_at (g ∘ h) (h' • g') s x :=
begin
  apply has_deriv_at_filter.comp _ (has_deriv_at_filter.mono hg _) hh,
  calc map h (nhds_within x s)
      ≤ nhds_within (h x) (h '' s) : hh.continuous_within_at.tendsto_nhds_within_image
  ... ≤ nhds_within (h x) t        : nhds_within_mono _ (image_subset_iff.mpr hst)
end

/-- The chain rule. -/
theorem has_deriv_at.comp
  (hg : has_deriv_at g g' (h x)) (hh : has_deriv_at h h' x) :
  has_deriv_at (g ∘ h) (h' • g') x :=
(hg.mono hh.continuous_at).comp x hh

theorem has_deriv_at.comp_has_deriv_within_at
  (hg : has_deriv_at g g' (h x)) (hh : has_deriv_within_at h h' s x) :
  has_deriv_within_at (g ∘ h) (h' • g') s x :=
begin
  rw ← has_deriv_within_at_univ at hg,
  exact has_deriv_within_at.comp x hg hh subset_preimage_univ
end

lemma deriv_within.comp
  (hg : differentiable_within_at 𝕜 g t (h x)) (hh : differentiable_within_at 𝕜 h s x)
  (hs : s ⊆ h ⁻¹' t) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (g ∘ h) s x = deriv_within h s x • deriv_within g t (h x) :=
begin
  apply has_deriv_within_at.deriv_within _ hxs,
  exact has_deriv_within_at.comp x (hg.has_deriv_within_at) (hh.has_deriv_within_at) hs
end

lemma deriv.comp
  (hg : differentiable_at 𝕜 g (h x)) (hh : differentiable_at 𝕜 h x) :
  deriv (g ∘ h) x = deriv h x • deriv g (h x) :=
begin
  apply has_deriv_at.deriv,
  exact has_deriv_at.comp x hg.has_deriv_at hh.has_deriv_at
end

end composition

section composition_vector
/-! ### Derivative of the composition of a function between vector spaces and of a function defined on `𝕜` -/

variables {l : F → E} {l' : F →L[𝕜] E}
variable (x)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_within_at.comp_has_deriv_within_at {t : set F}
  (hl : has_fderiv_within_at l l' t (f x)) (hf : has_deriv_within_at f f' s x) (hst : s ⊆ f ⁻¹' t) :
  has_deriv_within_at (l ∘ f) (l' (f')) s x :=
begin
  rw has_deriv_within_at_iff_has_fderiv_within_at,
  convert has_fderiv_within_at.comp x hl hf hst,
  ext,
  simp
end

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_at.comp_has_deriv_at
  (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_at f f' x) :
  has_deriv_at (l ∘ f) (l' (f')) x :=
begin
  rw has_deriv_at_iff_has_fderiv_at,
  convert has_fderiv_at.comp x hl hf,
  ext,
  simp
end

theorem has_fderiv_at.comp_has_deriv_within_at
  (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (l ∘ f) (l' (f')) s x :=
begin
  rw ← has_fderiv_within_at_univ at hl,
  exact has_fderiv_within_at.comp_has_deriv_within_at x hl hf subset_preimage_univ
end

lemma fderiv_within.comp_deriv_within {t : set F}
  (hl : differentiable_within_at 𝕜 l t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (hs : s ⊆ f ⁻¹' t) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (l ∘ f) s x = (fderiv_within 𝕜 l t (f x) : F → E) (deriv_within f s x) :=
begin
  apply has_deriv_within_at.deriv_within _ hxs,
  exact (hl.has_fderiv_within_at).comp_has_deriv_within_at x (hf.has_deriv_within_at) hs
end

lemma fderiv.comp_deriv
  (hl : differentiable_at 𝕜 l (f x)) (hf : differentiable_at 𝕜 f x) :
  deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
begin
  apply has_deriv_at.deriv _,
  exact (hl.has_fderiv_at).comp_has_deriv_at x (hf.has_deriv_at)
end

end composition_vector

section mul_vector
/-! ### Derivative of the multiplication of a scalar function and a vector function -/
variables {c : 𝕜 → 𝕜} {c' : 𝕜}

theorem has_deriv_within_at.smul'
  (hc : has_deriv_within_at c c' s x) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c y • f y) (c x • f' + c' • f x) s x :=
begin
  show has_fderiv_within_at _ _ _ _,
  convert has_fderiv_within_at.smul' hc hf,
  ext,
  simp [smul_add, (mul_smul _ _ _).symm, mul_comm]
end

theorem has_deriv_at.smul'
  (hc : has_deriv_at c c' x) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ y, c y • f y) (c x • f' + c' • f x) x :=
begin
  show has_fderiv_at _ _ _,
  convert has_fderiv_at.smul' hc hf,
  ext,
  simp [smul_add, (mul_smul _ _ _).symm, mul_comm]
end

lemma deriv_within_smul' (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  deriv_within (λ y, c y • f y) s x = c x • deriv_within f s x + (deriv_within c s x) • f x :=
(hc.has_deriv_within_at.smul' hf.has_deriv_within_at).deriv_within hxs

lemma deriv_smul' (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  deriv (λ y, c y • f y) x = c x • deriv f x + (deriv c x) • f x :=
(hc.has_deriv_at.smul' hf.has_deriv_at).deriv

end mul_vector

section mul
/-! ### Derivative of the multiplication of two scalar functions -/
variables {c d : 𝕜 → 𝕜} {c' d' : 𝕜}

theorem has_deriv_within_at.mul
  (hc : has_deriv_within_at c c' s x) (hd : has_deriv_within_at d d' s x) :
  has_deriv_within_at (λ y, c y * d y) (c x * d' + d x * c') s x :=
begin
  show has_fderiv_within_at _ _ _ _,
  convert has_fderiv_within_at.mul hc hd,
  ext, simp, ring,
end

theorem has_deriv_at.mul (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) :
  has_deriv_at (λ y, c y * d y) (c x * d' + d x * c') x :=
begin
  show has_fderiv_at _ _ _,
  convert has_fderiv_at.mul hc hd,
  ext, simp, ring,
end

lemma deriv_within_mul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  deriv_within (λ y, c y * d y) s x = c x * deriv_within d s x + d x * deriv_within c s x :=
(hc.has_deriv_within_at.mul hd.has_deriv_within_at).deriv_within hxs

lemma deriv_mul (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  deriv (λ y, c y * d y) x = c x * deriv d x + d x * deriv c x :=
(hc.has_deriv_at.mul hd.has_deriv_at).deriv

end mul

section inverse
/-! ### Derivative of `x ↦ x⁻¹` -/

lemma has_deriv_at_inv_one :
  has_deriv_at (λx, x⁻¹) (-1) (1 : 𝕜) :=
begin
  rw has_deriv_at_iff_is_o_nhds_zero,
  have : is_o (λ (h : 𝕜), h^2 * (1 + h)⁻¹) (λ (h : 𝕜), h * 1) (𝓝 0),
  { have : tendsto (λ (h : 𝕜), (1 + h)⁻¹) (𝓝 0) (𝓝 (1 + 0)⁻¹) :=
      ((tendsto_const_nhds).add tendsto_id).inv' (by norm_num),
    exact is_o_mul_right (is_o_pow_id (by norm_num)) (is_O_one_of_tendsto this) },
  apply (is_o_congr _ _).2 this,
  { have : metric.ball (0 : 𝕜) (∥(1:𝕜)∥) ∈ 𝓝 (0 : 𝕜),
    { apply mem_nhds_sets metric.is_open_ball,
      simp [zero_lt_one] },
    filter_upwards [this],
    assume h hx,
    have : 0 < ∥1 + h∥ := calc
      0 < ∥(1:𝕜)∥ - ∥-h∥ : by rwa [norm_neg, sub_pos, ← dist_zero_right h]
      ... ≤ ∥1 - -h∥ : norm_sub_norm_le _ _
      ... = ∥1 + h∥ : by simp,
    have : 1 + h ≠ 0 := (norm_pos_iff (1 + h)).mp this,
    calc (1 + h)⁻¹ - 1⁻¹ - h * -1 =
      (1+h)⁻¹ - ((1+h) * (1+h)⁻¹) + h * ((1+h) * (1+h)⁻¹) :
        by { simp only [mul_inv_cancel this], simp }
      ... = h^2 * (1+h)⁻¹ : by { generalize : (1+h)⁻¹ = y, ring } },
  { convert univ_mem_sets, simp }
end

theorem has_deriv_at_inv (x_ne_zero : x ≠ 0) :
  has_deriv_at (λy, y⁻¹) (-(x^2)⁻¹) x :=
begin
  have A : has_deriv_at (λy, y⁻¹) (-1) (x⁻¹ * x : 𝕜),
    by { simp [inv_mul_cancel x_ne_zero, has_deriv_at_inv_one] },
  have B : has_deriv_at (λy, x⁻¹ * y) (x⁻¹) x,
    by { convert ((has_deriv_at_const x (x⁻¹)).mul (has_deriv_at_id x)), simp },
  convert (has_deriv_at_const _ (x⁻¹)).mul (A.comp x B : _),
  { ext y,
    have : x⁻¹ * (y⁻¹ * x) = y⁻¹,
      by rw [← mul_assoc, mul_comm, ← mul_assoc, mul_inv_cancel x_ne_zero, one_mul],
    simp [mul_inv', this] },
  { simp [pow_two, mul_inv'] }
end

theorem has_deriv_within_at_inv (x_ne_zero : x ≠ 0) (s : set 𝕜) :
  has_deriv_within_at (λx, x⁻¹) (-(x^2)⁻¹) s x :=
(has_deriv_at_inv x_ne_zero).has_deriv_within_at

lemma differentiable_at_inv (x_ne_zero : x ≠ 0) :
  differentiable_at 𝕜 (λx, x⁻¹) x :=
(has_deriv_at_inv x_ne_zero).differentiable_at

lemma differentiable_within_at_inv (x_ne_zero : x ≠ 0) :
  differentiable_within_at 𝕜 (λx, x⁻¹) s x :=
(differentiable_at_inv x_ne_zero).differentiable_within_at

lemma differentiable_on_inv : differentiable_on 𝕜 (λx:𝕜, x⁻¹) {x | x ≠ 0} :=
λx hx, differentiable_within_at_inv hx

lemma deriv_inv (x_ne_zero : x ≠ 0) :
  deriv (λx, x⁻¹) x = -(x^2)⁻¹ :=
(has_deriv_at_inv x_ne_zero).deriv

lemma deriv_within_inv (x_ne_zero : x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, x⁻¹) s x = -(x^2)⁻¹ :=
begin
  rw differentiable_at.deriv_within (differentiable_at_inv x_ne_zero) hxs,
  exact deriv_inv x_ne_zero
end

lemma has_fderiv_at_inv (x_ne_zero : x ≠ 0) :
  has_fderiv_at (λx, x⁻¹) (smul_right 1 (-(x^2)⁻¹) : 𝕜 →L[𝕜] 𝕜) x :=
by simpa [has_deriv_at_iff_has_fderiv_at] using has_deriv_at_inv x_ne_zero

lemma has_fderiv_within_at_inv (x_ne_zero : x ≠ 0) :
  has_fderiv_within_at (λx, x⁻¹) (smul_right 1 (-(x^2)⁻¹) : 𝕜 →L[𝕜] 𝕜) s x :=
(has_fderiv_at_inv x_ne_zero).has_fderiv_within_at

lemma fderiv_inv (x_ne_zero : x ≠ 0) :
  fderiv 𝕜 (λx, x⁻¹) x = smul_right 1 (-(x^2)⁻¹) :=
(has_fderiv_at_inv x_ne_zero).fderiv

lemma fderiv_within_inv (x_ne_zero : x ≠ 0) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx, x⁻¹) s x = smul_right 1 (-(x^2)⁻¹) :=
begin
  rw differentiable_at.fderiv_within (differentiable_at_inv x_ne_zero) hxs,
  exact fderiv_inv x_ne_zero
end

end inverse

section division
/-! ### Derivative of `x ↦ c x / d x` -/

variables {c d : 𝕜 → 𝕜} {c' d' : 𝕜}

lemma has_deriv_within_at.div
  (hc : has_deriv_within_at c c' s x) (hd : has_deriv_within_at d d' s x) (hx : d x ≠ 0) :
  has_deriv_within_at (λ y, c y / d y) ((c' * d x - c x * d') / (d x)^2) s x :=
begin
  have A : (d x)⁻¹ * (d x)⁻¹ * (c' * d x) = (d x)⁻¹ * c',
    by rw [← mul_assoc, mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel hx, one_mul],
  convert hc.mul ((has_deriv_at_inv hx).comp_has_deriv_within_at x hd),
  simp [div_eq_inv_mul, pow_two, mul_inv', mul_add, A],
  ring
end

lemma has_deriv_at.div (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) (hx : d x ≠ 0) :
  has_deriv_at (λ y, c y / d y) ((c' * d x - c x * d') / (d x)^2) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hc.div hd hx
end

lemma differentiable_within_at.div
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) (hx : d x ≠ 0) :
differentiable_within_at 𝕜 (λx, c x / d x) s x :=
((hc.has_deriv_within_at).div (hd.has_deriv_within_at) hx).differentiable_within_at

lemma differentiable_at.div
  (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) (hx : d x ≠ 0) :
differentiable_at 𝕜 (λx, c x / d x) x :=
((hc.has_deriv_at).div (hd.has_deriv_at) hx).differentiable_at

lemma differentiable_on.div
  (hc : differentiable_on 𝕜 c s) (hd : differentiable_on 𝕜 d s) (hx : ∀ x ∈ s, d x ≠ 0) :
differentiable_on 𝕜 (λx, c x / d x) s :=
λx h, (hc x h).div (hd x h) (hx x h)

lemma differentiable.div
  (hc : differentiable 𝕜 c) (hd : differentiable 𝕜 d) (hx : ∀ x, d x ≠ 0) :
differentiable 𝕜 (λx, c x / d x) :=
λx, (hc x).div (hd x) (hx x)

lemma deriv_within_div
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) (hx : d x ≠ 0)
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, c x / d x) s x
    = ((deriv_within c s x) * d x - c x * (deriv_within d s x)) / (d x)^2 :=
((hc.has_deriv_within_at).div (hd.has_deriv_within_at) hx).deriv_within hxs

lemma deriv_div
  (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) (hx : d x ≠ 0) :
  deriv (λx, c x / d x) x = ((deriv c x) * d x - c x * (deriv d x)) / (d x)^2 :=
((hc.has_deriv_at).div (hd.has_deriv_at) hx).deriv

end division

namespace polynomial
/-! ### Derivative of a polynomial -/

variable (p : polynomial 𝕜)

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected lemma has_deriv_at (x : 𝕜) : has_deriv_at (λx, p.eval x) (p.derivative.eval x) x :=
begin
  apply p.induction_on,
  { simp [has_deriv_at_const] },
  { assume p q hp hq,
    convert hp.add hq;
    simp },
  { assume n a h,
    convert h.mul (has_deriv_at_id x),
    { ext y, simp [pow_add, mul_assoc] },
    { simp [pow_add], ring } }
end

protected theorem has_deriv_within_at (x : 𝕜) (s : set 𝕜) :
  has_deriv_within_at (λx, p.eval x) (p.derivative.eval x) s x :=
(p.has_deriv_at x).has_deriv_within_at

protected lemma differentiable_at : differentiable_at 𝕜 (λx, p.eval x) x :=
(p.has_deriv_at x).differentiable_at

protected lemma differentiable_within_at : differentiable_within_at 𝕜 (λx, p.eval x) s x :=
p.differentiable_at.differentiable_within_at

protected lemma differentiable : differentiable 𝕜 (λx, p.eval x) :=
λx, p.differentiable_at

protected lemma differentiable_on : differentiable_on 𝕜 (λx, p.eval x) s :=
p.differentiable.differentiable_on

@[simp] protected lemma deriv : deriv (λx, p.eval x) x = p.derivative.eval x :=
(p.has_deriv_at x).deriv

protected lemma deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, p.eval x) s x = p.derivative.eval x :=
begin
  rw differentiable_at.deriv_within p.differentiable_at hxs,
  exact p.deriv
end

protected lemma continuous : continuous (λx, p.eval x) :=
p.differentiable.continuous

protected lemma continuous_on : continuous_on (λx, p.eval x) s :=
p.continuous.continuous_on

protected lemma continuous_at : continuous_at (λx, p.eval x) x :=
p.continuous.continuous_at

protected lemma continuous_within_at : continuous_within_at (λx, p.eval x) s x :=
p.continuous_at.continuous_within_at

protected lemma has_fderiv_at (x : 𝕜) :
  has_fderiv_at (λx, p.eval x) (smul_right 1 (p.derivative.eval x) : 𝕜 →L[𝕜] 𝕜) x :=
by simpa [has_deriv_at_iff_has_fderiv_at] using p.has_deriv_at x

protected lemma has_fderiv_within_at (x : 𝕜) :
  has_fderiv_within_at (λx, p.eval x) (smul_right 1 (p.derivative.eval x) : 𝕜 →L[𝕜] 𝕜) s x :=
(p.has_fderiv_at x).has_fderiv_within_at

@[simp] protected lemma fderiv : fderiv 𝕜 (λx, p.eval x) x = smul_right 1 (p.derivative.eval x) :=
(p.has_fderiv_at x).fderiv

protected lemma fderiv_within (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx, p.eval x) s x = smul_right 1 (p.derivative.eval x) :=
begin
  rw differentiable_at.fderiv_within p.differentiable_at hxs,
  exact p.fderiv
end

end polynomial

section pow
/-! ### Derivative of `x ↦ x^n` for `n : ℕ` -/
variable {n : ℕ }

lemma has_deriv_at_pow (n : ℕ) (x : 𝕜) : has_deriv_at (λx, x^n) ((n : 𝕜) * x^(n-1)) x :=
begin
  convert (polynomial.C 1 * (polynomial.X)^n).has_deriv_at x,
  { simp },
  { rw [polynomial.derivative_monomial], simp }
end

theorem has_deriv_within_at_pow (n : ℕ) (x : 𝕜) (s : set 𝕜) :
  has_deriv_within_at (λx, x^n) ((n : 𝕜) * x^(n-1)) s x :=
(has_deriv_at_pow n x).has_deriv_within_at

lemma differentiable_at_pow : differentiable_at 𝕜 (λx, x^n) x :=
(has_deriv_at_pow n x).differentiable_at

lemma differentiable_within_at_pow : differentiable_within_at 𝕜 (λx, x^n) s x :=
differentiable_at_pow.differentiable_within_at

lemma differentiable_pow : differentiable 𝕜 (λx:𝕜, x^n) :=
λx, differentiable_at_pow

lemma differentiable_on_pow : differentiable_on 𝕜 (λx, x^n) s :=
differentiable_pow.differentiable_on

@[simp] lemma deriv_pow : deriv (λx, x^n) x = (n : 𝕜) * x^(n-1) :=
(has_deriv_at_pow n x).deriv

lemma deriv_within_pow (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, x^n) s x = (n : 𝕜) * x^(n-1) :=
begin
  rw differentiable_at.deriv_within differentiable_at_pow hxs,
  exact deriv_pow
end

end pow
