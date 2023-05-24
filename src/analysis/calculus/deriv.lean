/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
import analysis.calculus.fderiv.add
import analysis.calculus.fderiv.mul
import analysis.calculus.fderiv.equiv
import analysis.calculus.fderiv.restrict_scalars
import analysis.calculus.fderiv.star
import data.polynomial.algebra_map
import data.polynomial.derivative

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.html). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

 - `has_deriv_at_filter f f' x L` states that the function `f` has the
    derivative `f'` at the point `x` as `x` goes along the filter `L`.

 - `has_deriv_within_at f f' s x` states that the function `f` has the
    derivative `f'` at the point `x` within the subset `s`.

 - `has_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x`.

 - `has_strict_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x` in the sense of strict differentiability, i.e.,
   `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

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
  - sum of finitely many functions
  - negation
  - subtraction
  - multiplication
  - star
  - inverse `x → x⁻¹`
  - multiplication of two functions in `𝕜 → 𝕜`
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E`
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜`
  - composition of a function in `F → E` with a function in `𝕜 → F`
  - inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)
  - division
  - polynomials

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }
```

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in `fderiv.lean`.
See the explanations there.
-/

universes u v w
noncomputable theory
open_locale classical topology big_operators filter ennreal polynomial
open filter asymptotics set
open continuous_linear_map (smul_right smul_right_one_eq_iff)


variables {𝕜 : Type u} [nontrivially_normed_field 𝕜]

section
variables {F : Type v} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {E : Type w} [normed_add_comm_group E] [normed_space 𝕜 E]

/--
`f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def has_deriv_at_filter (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : filter 𝕜) :=
has_fderiv_at_filter f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x L

/--
`f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def has_deriv_within_at (f : 𝕜 → F) (f' : F) (s : set 𝕜) (x : 𝕜) :=
has_deriv_at_filter f f' x (𝓝[s] x)

/--
`f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def has_deriv_at (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
has_deriv_at_filter f f' x (𝓝 x)

/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
def has_strict_deriv_at (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
has_strict_fderiv_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x

/--
Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_within_at f f' s x`), then
`f x' = f x + (x' - x) • deriv_within f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def deriv_within (f : 𝕜 → F) (s : set 𝕜) (x : 𝕜) :=
fderiv_within 𝕜 f s x 1

/--
Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_at f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
fderiv 𝕜 f x 1

variables {f f₀ f₁ g : 𝕜 → F}
variables {f' f₀' f₁' g' : F}
variables {x : 𝕜}
variables {s t : set 𝕜}
variables {L L₁ L₂ : filter 𝕜}

/-- Expressing `has_fderiv_at_filter f f' x L` in terms of `has_deriv_at_filter` -/
lemma has_fderiv_at_filter_iff_has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at_filter f f' x L ↔ has_deriv_at_filter f (f' 1) x L :=
by simp [has_deriv_at_filter]

lemma has_fderiv_at_filter.has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at_filter f f' x L → has_deriv_at_filter f (f' 1) x L :=
has_fderiv_at_filter_iff_has_deriv_at_filter.mp

/-- Expressing `has_fderiv_within_at f f' s x` in terms of `has_deriv_within_at` -/
lemma has_fderiv_within_at_iff_has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_within_at f f' s x ↔ has_deriv_within_at f (f' 1) s x :=
has_fderiv_at_filter_iff_has_deriv_at_filter

/-- Expressing `has_deriv_within_at f f' s x` in terms of `has_fderiv_within_at` -/
lemma has_deriv_within_at_iff_has_fderiv_within_at {f' : F} :
  has_deriv_within_at f f' s x ↔
  has_fderiv_within_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
iff.rfl

lemma has_fderiv_within_at.has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_within_at f f' s x → has_deriv_within_at f (f' 1) s x :=
has_fderiv_within_at_iff_has_deriv_within_at.mp

lemma has_deriv_within_at.has_fderiv_within_at {f' : F} :
  has_deriv_within_at f f' s x → has_fderiv_within_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
has_deriv_within_at_iff_has_fderiv_within_at.mp

/-- Expressing `has_fderiv_at f f' x` in terms of `has_deriv_at` -/
lemma has_fderiv_at_iff_has_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at f f' x ↔ has_deriv_at f (f' 1) x :=
has_fderiv_at_filter_iff_has_deriv_at_filter

lemma has_fderiv_at.has_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at f f' x → has_deriv_at f (f' 1) x :=
has_fderiv_at_iff_has_deriv_at.mp

lemma has_strict_fderiv_at_iff_has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_strict_fderiv_at f f' x ↔ has_strict_deriv_at f (f' 1) x :=
by simp [has_strict_deriv_at, has_strict_fderiv_at]

protected lemma has_strict_fderiv_at.has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_strict_fderiv_at f f' x → has_strict_deriv_at f (f' 1) x :=
has_strict_fderiv_at_iff_has_strict_deriv_at.mp

lemma has_strict_deriv_at_iff_has_strict_fderiv_at :
  has_strict_deriv_at f f' x ↔ has_strict_fderiv_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
iff.rfl

alias has_strict_deriv_at_iff_has_strict_fderiv_at ↔ has_strict_deriv_at.has_strict_fderiv_at _

/-- Expressing `has_deriv_at f f' x` in terms of `has_fderiv_at` -/
lemma has_deriv_at_iff_has_fderiv_at {f' : F} :
  has_deriv_at f f' x ↔
  has_fderiv_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
iff.rfl

alias has_deriv_at_iff_has_fderiv_at ↔ has_deriv_at.has_fderiv_at _

lemma deriv_within_zero_of_not_differentiable_within_at
  (h : ¬ differentiable_within_at 𝕜 f s x) : deriv_within f s x = 0 :=
by { unfold deriv_within, rw fderiv_within_zero_of_not_differentiable_within_at, simp, assumption }

lemma differentiable_within_at_of_deriv_within_ne_zero (h : deriv_within f s x ≠ 0) :
  differentiable_within_at 𝕜 f s x :=
not_imp_comm.1 deriv_within_zero_of_not_differentiable_within_at h

lemma deriv_zero_of_not_differentiable_at (h : ¬ differentiable_at 𝕜 f x) : deriv f x = 0 :=
by { unfold deriv, rw fderiv_zero_of_not_differentiable_at, simp, assumption }

lemma differentiable_at_of_deriv_ne_zero (h : deriv f x ≠ 0) : differentiable_at 𝕜 f x :=
not_imp_comm.1 deriv_zero_of_not_differentiable_at h

theorem unique_diff_within_at.eq_deriv (s : set 𝕜) (H : unique_diff_within_at 𝕜 s x)
  (h : has_deriv_within_at f f' s x) (h₁ : has_deriv_within_at f f₁' s x) : f' = f₁' :=
smul_right_one_eq_iff.mp $ unique_diff_within_at.eq H h h₁

theorem has_deriv_at_filter_iff_is_o :
  has_deriv_at_filter f f' x L ↔ (λ x' : 𝕜, f x' - f x - (x' - x) • f') =o[L] (λ x', x' - x) :=
iff.rfl

theorem has_deriv_at_filter_iff_tendsto :
  has_deriv_at_filter f f' x L ↔
  tendsto (λ x' : 𝕜, ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) L (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_within_at_iff_is_o :
  has_deriv_within_at f f' s x
    ↔ (λ x' : 𝕜, f x' - f x - (x' - x) • f') =o[𝓝[s] x] (λ x', x' - x) :=
iff.rfl

theorem has_deriv_within_at_iff_tendsto : has_deriv_within_at f f' s x ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_iff_is_o :
  has_deriv_at f f' x ↔ (λ x' : 𝕜, f x' - f x - (x' - x) • f') =o[𝓝 x] (λ x', x' - x) :=
iff.rfl

theorem has_deriv_at_iff_tendsto : has_deriv_at f f' x ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_strict_deriv_at.has_deriv_at (h : has_strict_deriv_at f f' x) :
  has_deriv_at f f' x :=
h.has_fderiv_at
theorem has_deriv_within_at_congr_set' {s t : set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    has_deriv_within_at f f' s x ↔ has_deriv_within_at f f' t x :=
has_fderiv_within_at_congr_set' y h

theorem has_deriv_within_at_congr_set {s t : set 𝕜} (h : s =ᶠ[𝓝 x] t) :
    has_deriv_within_at f f' s x ↔ has_deriv_within_at f f' t x :=
has_fderiv_within_at_congr_set h

alias has_deriv_within_at_congr_set ↔ has_deriv_within_at.congr_set _

@[simp] lemma has_deriv_within_at_diff_singleton :
  has_deriv_within_at f f' (s \ {x}) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_diff_singleton _

@[simp] lemma has_deriv_within_at_Ioi_iff_Ici [partial_order 𝕜] :
  has_deriv_within_at f f' (Ioi x) x ↔ has_deriv_within_at f f' (Ici x) x :=
by rw [← Ici_diff_left, has_deriv_within_at_diff_singleton]

alias has_deriv_within_at_Ioi_iff_Ici ↔
  has_deriv_within_at.Ici_of_Ioi has_deriv_within_at.Ioi_of_Ici

@[simp] lemma has_deriv_within_at_Iio_iff_Iic [partial_order 𝕜] :
  has_deriv_within_at f f' (Iio x) x ↔ has_deriv_within_at f f' (Iic x) x :=
by rw [← Iic_diff_right, has_deriv_within_at_diff_singleton]

alias has_deriv_within_at_Iio_iff_Iic ↔
  has_deriv_within_at.Iic_of_Iio has_deriv_within_at.Iio_of_Iic

theorem has_deriv_within_at.Ioi_iff_Ioo [linear_order 𝕜] [order_closed_topology 𝕜] {x y : 𝕜}
  (h : x < y) :
  has_deriv_within_at f f' (Ioo x y) x ↔ has_deriv_within_at f f' (Ioi x) x :=
has_fderiv_within_at_inter $ Iio_mem_nhds h

alias has_deriv_within_at.Ioi_iff_Ioo ↔
  has_deriv_within_at.Ioi_of_Ioo has_deriv_within_at.Ioo_of_Ioi

theorem has_deriv_at_iff_is_o_nhds_zero : has_deriv_at f f' x ↔
  (λh, f (x + h) - f x - h • f') =o[𝓝 0] (λh, h) :=
has_fderiv_at_iff_is_o_nhds_zero

theorem has_deriv_at_filter.mono (h : has_deriv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) :
  has_deriv_at_filter f f' x L₁ :=
has_fderiv_at_filter.mono h hst

theorem has_deriv_within_at.mono (h : has_deriv_within_at f f' t x) (hst : s ⊆ t) :
  has_deriv_within_at f f' s x :=
has_fderiv_within_at.mono h hst

theorem has_deriv_within_at.mono_of_mem (h : has_deriv_within_at f f' t x) (hst : t ∈ 𝓝[s] x) :
  has_deriv_within_at f f' s x :=
has_fderiv_within_at.mono_of_mem h hst

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

theorem has_deriv_at.unique
  (h₀ : has_deriv_at f f₀' x) (h₁ : has_deriv_at f f₁' x) : f₀' = f₁' :=
smul_right_one_eq_iff.mp $ h₀.has_fderiv_at.unique h₁

lemma has_deriv_within_at_inter' (h : t ∈ 𝓝[s] x) :
  has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_inter' h

lemma has_deriv_within_at_inter (h : t ∈ 𝓝 x) :
  has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_inter h

lemma has_deriv_within_at.union (hs : has_deriv_within_at f f' s x)
  (ht : has_deriv_within_at f f' t x) :
  has_deriv_within_at f f' (s ∪ t) x :=
hs.has_fderiv_within_at.union ht.has_fderiv_within_at

lemma has_deriv_within_at.nhds_within (h : has_deriv_within_at f f' s x)
  (ht : s ∈ 𝓝[t] x) : has_deriv_within_at f f' t x :=
(has_deriv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))

lemma has_deriv_within_at.has_deriv_at (h : has_deriv_within_at f f' s x) (hs : s ∈ 𝓝 x) :
  has_deriv_at f f' x :=
has_fderiv_within_at.has_fderiv_at h hs

lemma differentiable_within_at.has_deriv_within_at (h : differentiable_within_at 𝕜 f s x) :
  has_deriv_within_at f (deriv_within f s x) s x :=
h.has_fderiv_within_at.has_deriv_within_at

lemma differentiable_at.has_deriv_at (h : differentiable_at 𝕜 f x) : has_deriv_at f (deriv f x) x :=
h.has_fderiv_at.has_deriv_at

@[simp] lemma has_deriv_at_deriv_iff : has_deriv_at f (deriv f x) x ↔ differentiable_at 𝕜 f x :=
⟨λ h, h.differentiable_at, λ h, h.has_deriv_at⟩

@[simp] lemma has_deriv_within_at_deriv_within_iff :
  has_deriv_within_at f (deriv_within f s x) s x ↔ differentiable_within_at 𝕜 f s x :=
⟨λ h, h.differentiable_within_at, λ h, h.has_deriv_within_at⟩

lemma differentiable_on.has_deriv_at (h : differentiable_on 𝕜 f s) (hs : s ∈ 𝓝 x) :
  has_deriv_at f (deriv f x) x :=
(h.has_fderiv_at hs).has_deriv_at

lemma has_deriv_at.deriv (h : has_deriv_at f f' x) : deriv f x = f' :=
h.differentiable_at.has_deriv_at.unique h

lemma deriv_eq {f' : 𝕜 → F} (h : ∀ x, has_deriv_at f (f' x) x) : deriv f = f' :=
funext $ λ x, (h x).deriv

lemma has_deriv_within_at.deriv_within
  (h : has_deriv_within_at f f' s x) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within f s x = f' :=
hxs.eq_deriv _ h.differentiable_within_at.has_deriv_within_at h

lemma fderiv_within_deriv_within : (fderiv_within 𝕜 f s x : 𝕜 → F) 1 = deriv_within f s x :=
rfl

lemma deriv_within_fderiv_within :
  smul_right (1 : 𝕜 →L[𝕜] 𝕜) (deriv_within f s x) = fderiv_within 𝕜 f s x :=
by simp [deriv_within]

lemma fderiv_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
rfl

lemma deriv_fderiv :
  smul_right (1 : 𝕜 →L[𝕜] 𝕜) (deriv f x) = fderiv 𝕜 f x :=
by simp [deriv]

lemma differentiable_at.deriv_within (h : differentiable_at 𝕜 f x)
  (hxs : unique_diff_within_at 𝕜 s x) : deriv_within f s x = deriv f x :=
by { unfold deriv_within deriv, rw h.fderiv_within hxs }

theorem has_deriv_within_at.deriv_eq_zero (hd : has_deriv_within_at f 0 s x)
  (H : unique_diff_within_at 𝕜 s x) : deriv f x = 0 :=
(em' (differentiable_at 𝕜 f x)).elim deriv_zero_of_not_differentiable_at $
  λ h, H.eq_deriv _ h.has_deriv_at.has_deriv_within_at hd

lemma deriv_within_of_mem (st : t ∈ 𝓝[s] x) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  deriv_within f s x = deriv_within f t x :=
((differentiable_within_at.has_deriv_within_at h).mono_of_mem st).deriv_within ht

lemma deriv_within_subset (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  deriv_within f s x = deriv_within f t x :=
((differentiable_within_at.has_deriv_within_at h).mono st).deriv_within ht

lemma deriv_within_congr_set' (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
  deriv_within f s x = deriv_within f t x :=
by simp only [deriv_within, fderiv_within_congr_set' y h]

lemma deriv_within_congr_set (h : s =ᶠ[𝓝 x] t) : deriv_within f s x = deriv_within f t x :=
by simp only [deriv_within, fderiv_within_congr_set h]

@[simp] lemma deriv_within_univ : deriv_within f univ = deriv f :=
by { ext, unfold deriv_within deriv, rw fderiv_within_univ }

lemma deriv_within_inter (ht : t ∈ 𝓝 x) :
  deriv_within f (s ∩ t) x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_inter ht }

lemma deriv_within_of_open (hs : is_open s) (hx : x ∈ s) :
  deriv_within f s x = deriv f x :=
by { unfold deriv_within, rw fderiv_within_of_open hs hx, refl }

lemma deriv_mem_iff {f : 𝕜 → F} {s : set F} {x : 𝕜} :
  deriv f x ∈ s ↔ (differentiable_at 𝕜 f x ∧ deriv f x ∈ s) ∨
    (¬differentiable_at 𝕜 f x ∧ (0 : F) ∈ s) :=
by by_cases hx : differentiable_at 𝕜 f x; simp [deriv_zero_of_not_differentiable_at, *]

lemma deriv_within_mem_iff {f : 𝕜 → F} {t : set 𝕜} {s : set F} {x : 𝕜} :
  deriv_within f t x ∈ s ↔ (differentiable_within_at 𝕜 f t x ∧ deriv_within f t x ∈ s) ∨
    (¬differentiable_within_at 𝕜 f t x ∧ (0 : F) ∈ s) :=
by by_cases hx : differentiable_within_at 𝕜 f t x;
  simp [deriv_within_zero_of_not_differentiable_within_at, *]

lemma differentiable_within_at_Ioi_iff_Ici [partial_order 𝕜] :
  differentiable_within_at 𝕜 f (Ioi x) x ↔ differentiable_within_at 𝕜 f (Ici x) x :=
⟨λ h, h.has_deriv_within_at.Ici_of_Ioi.differentiable_within_at,
λ h, h.has_deriv_within_at.Ioi_of_Ici.differentiable_within_at⟩

lemma deriv_within_Ioi_eq_Ici {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] (f : ℝ → E)
  (x : ℝ) :
  deriv_within f (Ioi x) x = deriv_within f (Ici x) x :=
begin
  by_cases H : differentiable_within_at ℝ f (Ioi x) x,
  { have A := H.has_deriv_within_at.Ici_of_Ioi,
    have B := (differentiable_within_at_Ioi_iff_Ici.1 H).has_deriv_within_at,
    simpa using (unique_diff_on_Ici x).eq le_rfl A B },
  { rw [deriv_within_zero_of_not_differentiable_within_at H,
      deriv_within_zero_of_not_differentiable_within_at],
    rwa differentiable_within_at_Ioi_iff_Ici at H }
end

section congr
/-! ### Congruence properties of derivatives -/

theorem filter.eventually_eq.has_deriv_at_filter_iff
  (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x) (h₁ : f₀' = f₁') :
  has_deriv_at_filter f₀ f₀' x L ↔ has_deriv_at_filter f₁ f₁' x L :=
h₀.has_fderiv_at_filter_iff hx (by simp [h₁])

lemma has_deriv_at_filter.congr_of_eventually_eq (h : has_deriv_at_filter f f' x L)
  (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : has_deriv_at_filter f₁ f' x L :=
by rwa hL.has_deriv_at_filter_iff hx rfl

lemma has_deriv_within_at.congr_mono (h : has_deriv_within_at f f' s x) (ht : ∀x ∈ t, f₁ x = f x)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_deriv_within_at f₁ f' t x :=
has_fderiv_within_at.congr_mono h ht hx h₁

lemma has_deriv_within_at.congr (h : has_deriv_within_at f f' s x) (hs : ∀x ∈ s, f₁ x = f x)
  (hx : f₁ x = f x) : has_deriv_within_at f₁ f' s x :=
h.congr_mono hs hx (subset.refl _)

lemma has_deriv_within_at.congr_of_mem (h : has_deriv_within_at f f' s x) (hs : ∀x ∈ s, f₁ x = f x)
  (hx : x ∈ s) : has_deriv_within_at f₁ f' s x :=
h.congr hs (hs _ hx)

lemma has_deriv_within_at.congr_of_eventually_eq (h : has_deriv_within_at f f' s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : has_deriv_within_at f₁ f' s x :=
has_deriv_at_filter.congr_of_eventually_eq h h₁ hx

lemma has_deriv_within_at.congr_of_eventually_eq_of_mem (h : has_deriv_within_at f f' s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : has_deriv_within_at f₁ f' s x :=
h.congr_of_eventually_eq h₁ (h₁.eq_of_nhds_within hx)

lemma has_deriv_at.congr_of_eventually_eq (h : has_deriv_at f f' x)
  (h₁ : f₁ =ᶠ[𝓝 x] f) : has_deriv_at f₁ f' x :=
has_deriv_at_filter.congr_of_eventually_eq h h₁ (mem_of_mem_nhds h₁ : _)

lemma filter.eventually_eq.deriv_within_eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw hL.fderiv_within_eq hx }

lemma deriv_within_congr (hs : eq_on f₁ f s) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_congr hs hx }

lemma filter.eventually_eq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x :=
by { unfold deriv, rwa filter.eventually_eq.fderiv_eq }

protected lemma filter.eventually_eq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
h.eventually_eq_nhds.mono $ λ x h, h.deriv_eq

end congr

section id
/-! ### Derivative of the identity -/
variables (s x L)

theorem has_deriv_at_filter_id : has_deriv_at_filter id 1 x L :=
(has_fderiv_at_filter_id x L).has_deriv_at_filter

theorem has_deriv_within_at_id : has_deriv_within_at id 1 s x :=
has_deriv_at_filter_id _ _

theorem has_deriv_at_id : has_deriv_at id 1 x :=
has_deriv_at_filter_id _ _

theorem has_deriv_at_id' : has_deriv_at (λ (x : 𝕜), x) 1 x :=
has_deriv_at_filter_id _ _

theorem has_strict_deriv_at_id : has_strict_deriv_at id 1 x :=
(has_strict_fderiv_at_id x).has_strict_deriv_at

lemma deriv_id : deriv id x = 1 :=
has_deriv_at.deriv (has_deriv_at_id x)

@[simp] lemma deriv_id' : deriv (@id 𝕜) = λ _, 1 := funext deriv_id

@[simp] lemma deriv_id'' : deriv (λ x : 𝕜, x) = λ _, 1 := deriv_id'

lemma deriv_within_id (hxs : unique_diff_within_at 𝕜 s x) : deriv_within id s x = 1 :=
(has_deriv_within_at_id x s).deriv_within hxs

end id

section const
/-! ### Derivative of constant functions -/
variables (c : F) (s x L)

theorem has_deriv_at_filter_const : has_deriv_at_filter (λ x, c) 0 x L :=
(has_fderiv_at_filter_const c x L).has_deriv_at_filter

theorem has_strict_deriv_at_const : has_strict_deriv_at (λ x, c) 0 x :=
(has_strict_fderiv_at_const c x).has_strict_deriv_at

theorem has_deriv_within_at_const : has_deriv_within_at (λ x, c) 0 s x :=
has_deriv_at_filter_const _ _ _

theorem has_deriv_at_const : has_deriv_at (λ x, c) 0 x :=
has_deriv_at_filter_const _ _ _

lemma deriv_const : deriv (λ x, c) x = 0 :=
has_deriv_at.deriv (has_deriv_at_const x c)

@[simp] lemma deriv_const' : deriv (λ x:𝕜, c) = λ x, 0 :=
funext (λ x, deriv_const x c)

lemma deriv_within_const (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (λ x, c) s x = 0 :=
(has_deriv_within_at_const _ _ _).deriv_within hxs

end const

section continuous_linear_map
/-! ### Derivative of continuous linear maps -/
variables (e : 𝕜 →L[𝕜] F)

protected lemma continuous_linear_map.has_deriv_at_filter : has_deriv_at_filter e (e 1) x L :=
e.has_fderiv_at_filter.has_deriv_at_filter

protected lemma continuous_linear_map.has_strict_deriv_at : has_strict_deriv_at e (e 1) x :=
e.has_strict_fderiv_at.has_strict_deriv_at

protected lemma continuous_linear_map.has_deriv_at : has_deriv_at e (e 1) x :=
e.has_deriv_at_filter

protected lemma continuous_linear_map.has_deriv_within_at : has_deriv_within_at e (e 1) s x :=
e.has_deriv_at_filter

@[simp] protected lemma continuous_linear_map.deriv : deriv e x = e 1 :=
e.has_deriv_at.deriv

protected lemma continuous_linear_map.deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within e s x = e 1 :=
e.has_deriv_within_at.deriv_within hxs

end continuous_linear_map

section linear_map
/-! ### Derivative of bundled linear maps -/
variables (e : 𝕜 →ₗ[𝕜] F)

protected lemma linear_map.has_deriv_at_filter : has_deriv_at_filter e (e 1) x L :=
e.to_continuous_linear_map₁.has_deriv_at_filter

protected lemma linear_map.has_strict_deriv_at : has_strict_deriv_at e (e 1) x :=
e.to_continuous_linear_map₁.has_strict_deriv_at

protected lemma linear_map.has_deriv_at : has_deriv_at e (e 1) x :=
e.has_deriv_at_filter

protected lemma linear_map.has_deriv_within_at : has_deriv_within_at e (e 1) s x :=
e.has_deriv_at_filter

@[simp] protected lemma linear_map.deriv : deriv e x = e 1 :=
e.has_deriv_at.deriv

protected lemma linear_map.deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within e s x = e 1 :=
e.has_deriv_within_at.deriv_within hxs

end linear_map

section add
/-! ### Derivative of the sum of two functions -/

theorem has_deriv_at_filter.add
  (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) :
  has_deriv_at_filter (λ y, f y + g y) (f' + g') x L :=
by simpa using (hf.add hg).has_deriv_at_filter

theorem has_strict_deriv_at.add
  (hf : has_strict_deriv_at f f' x) (hg : has_strict_deriv_at g g' x) :
  has_strict_deriv_at (λ y, f y + g y) (f' + g') x :=
by simpa using (hf.add hg).has_strict_deriv_at

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

@[simp] lemma deriv_add
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  deriv (λy, f y + g y) x = deriv f x + deriv g x :=
(hf.has_deriv_at.add hg.has_deriv_at).deriv

theorem has_deriv_at_filter.add_const
  (hf : has_deriv_at_filter f f' x L) (c : F) :
  has_deriv_at_filter (λ y, f y + c) f' x L :=
add_zero f' ▸ hf.add (has_deriv_at_filter_const x L c)

theorem has_deriv_within_at.add_const
  (hf : has_deriv_within_at f f' s x) (c : F) :
  has_deriv_within_at (λ y, f y + c) f' s x :=
hf.add_const c

theorem has_deriv_at.add_const
  (hf : has_deriv_at f f' x) (c : F) :
  has_deriv_at (λ x, f x + c) f' x :=
hf.add_const c

lemma deriv_within_add_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, f y + c) s x = deriv_within f s x :=
by simp only [deriv_within, fderiv_within_add_const hxs]

lemma deriv_add_const (c : F) : deriv (λy, f y + c) x = deriv f x :=
by simp only [deriv, fderiv_add_const]

@[simp] lemma deriv_add_const' (c : F) : deriv (λ y, f y + c) = deriv f :=
funext $ λ x, deriv_add_const c

theorem has_deriv_at_filter.const_add (c : F) (hf : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ y, c + f y) f' x L :=
zero_add f' ▸ (has_deriv_at_filter_const x L c).add hf

theorem has_deriv_within_at.const_add (c : F) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c + f y) f' s x :=
hf.const_add c

theorem has_deriv_at.const_add (c : F) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, c + f x) f' x :=
hf.const_add c

lemma deriv_within_const_add (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, c + f y) s x = deriv_within f s x :=
by simp only [deriv_within, fderiv_within_const_add hxs]

lemma deriv_const_add (c : F)  : deriv (λy, c + f y) x = deriv f x :=
by simp only [deriv, fderiv_const_add]

@[simp] lemma deriv_const_add' (c : F) : deriv (λ y, c + f y) = deriv f :=
funext $ λ x, deriv_const_add c

end add

section sum
/-! ### Derivative of a finite sum of functions -/

open_locale big_operators

variables {ι : Type*} {u : finset ι} {A : ι → (𝕜 → F)} {A' : ι → F}

theorem has_deriv_at_filter.sum (h : ∀ i ∈ u, has_deriv_at_filter (A i) (A' i) x L) :
  has_deriv_at_filter (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x L :=
by simpa [continuous_linear_map.sum_apply] using (has_fderiv_at_filter.sum h).has_deriv_at_filter

theorem has_strict_deriv_at.sum (h : ∀ i ∈ u, has_strict_deriv_at (A i) (A' i) x) :
  has_strict_deriv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
by simpa [continuous_linear_map.sum_apply] using (has_strict_fderiv_at.sum h).has_strict_deriv_at

theorem has_deriv_within_at.sum (h : ∀ i ∈ u, has_deriv_within_at (A i) (A' i) s x) :
  has_deriv_within_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) s x :=
has_deriv_at_filter.sum h

theorem has_deriv_at.sum (h : ∀ i ∈ u, has_deriv_at (A i) (A' i) x) :
  has_deriv_at (λ y, ∑ i in u, A i y) (∑ i in u, A' i) x :=
has_deriv_at_filter.sum h

lemma deriv_within_sum (hxs : unique_diff_within_at 𝕜 s x)
  (h : ∀ i ∈ u, differentiable_within_at 𝕜 (A i) s x) :
  deriv_within (λ y, ∑ i in u, A i y) s x = ∑ i in u, deriv_within (A i) s x :=
(has_deriv_within_at.sum (λ i hi, (h i hi).has_deriv_within_at)).deriv_within hxs

@[simp] lemma deriv_sum (h : ∀ i ∈ u, differentiable_at 𝕜 (A i) x) :
  deriv (λ y, ∑ i in u, A i y) x = ∑ i in u, deriv (A i) x :=
(has_deriv_at.sum (λ i hi, (h i hi).has_deriv_at)).deriv

end sum

section pi

/-! ### Derivatives of functions `f : 𝕜 → Π i, E i` -/

variables {ι : Type*} [fintype ι] {E' : ι → Type*} [Π i, normed_add_comm_group (E' i)]
  [Π i, normed_space 𝕜 (E' i)] {φ : 𝕜 → Π i, E' i} {φ' : Π i, E' i}

@[simp] lemma has_strict_deriv_at_pi :
  has_strict_deriv_at φ φ' x ↔ ∀ i, has_strict_deriv_at (λ x, φ x i) (φ' i) x :=
has_strict_fderiv_at_pi'

@[simp] lemma has_deriv_at_filter_pi :
  has_deriv_at_filter φ φ' x L ↔
    ∀ i, has_deriv_at_filter (λ x, φ x i) (φ' i) x L :=
has_fderiv_at_filter_pi'

lemma has_deriv_at_pi :
  has_deriv_at φ φ' x ↔ ∀ i, has_deriv_at (λ x, φ x i) (φ' i) x:=
has_deriv_at_filter_pi

lemma has_deriv_within_at_pi :
  has_deriv_within_at φ φ' s x ↔ ∀ i, has_deriv_within_at (λ x, φ x i) (φ' i) s x:=
has_deriv_at_filter_pi

lemma deriv_within_pi (h : ∀ i, differentiable_within_at 𝕜 (λ x, φ x i) s x)
  (hs : unique_diff_within_at 𝕜 s x) :
  deriv_within φ s x = λ i, deriv_within (λ x, φ x i) s x :=
(has_deriv_within_at_pi.2 (λ i, (h i).has_deriv_within_at)).deriv_within hs

lemma deriv_pi (h : ∀ i, differentiable_at 𝕜 (λ x, φ x i) x) :
  deriv φ x = λ i, deriv (λ x, φ x i) x :=
(has_deriv_at_pi.2 (λ i, (h i).has_deriv_at)).deriv

end pi

section smul

/-! ### Derivative of the multiplication of a scalar function and a vector function -/

variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {c : 𝕜 → 𝕜'} {c' : 𝕜'}

theorem has_deriv_within_at.smul
  (hc : has_deriv_within_at c c' s x) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c y • f y) (c x • f' + c' • f x) s x :=
by simpa using (has_fderiv_within_at.smul hc hf).has_deriv_within_at

theorem has_deriv_at.smul
  (hc : has_deriv_at c c' x) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ y, c y • f y) (c x • f' + c' • f x) x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.smul hf
end

theorem has_strict_deriv_at.smul
  (hc : has_strict_deriv_at c c' x) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ y, c y • f y) (c x • f' + c' • f x) x :=
by simpa using (hc.smul hf).has_strict_deriv_at

lemma deriv_within_smul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  deriv_within (λ y, c y • f y) s x = c x • deriv_within f s x + (deriv_within c s x) • f x :=
(hc.has_deriv_within_at.smul hf.has_deriv_within_at).deriv_within hxs

lemma deriv_smul (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  deriv (λ y, c y • f y) x = c x • deriv f x + (deriv c x) • f x :=
(hc.has_deriv_at.smul hf.has_deriv_at).deriv

theorem has_strict_deriv_at.smul_const
  (hc : has_strict_deriv_at c c' x) (f : F) :
  has_strict_deriv_at (λ y, c y • f) (c' • f) x :=
begin
  have := hc.smul (has_strict_deriv_at_const x f),
  rwa [smul_zero, zero_add] at this,
end

theorem has_deriv_within_at.smul_const
  (hc : has_deriv_within_at c c' s x) (f : F) :
  has_deriv_within_at (λ y, c y • f) (c' • f) s x :=
begin
  have := hc.smul (has_deriv_within_at_const x s f),
  rwa [smul_zero, zero_add] at this
end

theorem has_deriv_at.smul_const
  (hc : has_deriv_at c c' x) (f : F) :
  has_deriv_at (λ y, c y • f) (c' • f) x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.smul_const f
end

lemma deriv_within_smul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (f : F) :
  deriv_within (λ y, c y • f) s x = (deriv_within c s x) • f :=
(hc.has_deriv_within_at.smul_const f).deriv_within hxs

lemma deriv_smul_const (hc : differentiable_at 𝕜 c x) (f : F) :
  deriv (λ y, c y • f) x = (deriv c x) • f :=
(hc.has_deriv_at.smul_const f).deriv

end smul

section const_smul

variables {R : Type*} [semiring R] [module R F] [smul_comm_class 𝕜 R F]
  [has_continuous_const_smul R F]

theorem has_strict_deriv_at.const_smul
  (c : R) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ y, c • f y) (c • f') x :=
by simpa using (hf.const_smul c).has_strict_deriv_at

theorem has_deriv_at_filter.const_smul
  (c : R) (hf : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ y, c • f y) (c • f') x L :=
by simpa using (hf.const_smul c).has_deriv_at_filter

theorem has_deriv_within_at.const_smul
  (c : R) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ y, c • f y) (c • f') s x :=
hf.const_smul c

theorem has_deriv_at.const_smul (c : R) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ y, c • f y) (c • f') x :=
hf.const_smul c

lemma deriv_within_const_smul (hxs : unique_diff_within_at 𝕜 s x)
  (c : R) (hf : differentiable_within_at 𝕜 f s x) :
  deriv_within (λ y, c • f y) s x = c • deriv_within f s x :=
(hf.has_deriv_within_at.const_smul c).deriv_within hxs

lemma deriv_const_smul (c : R) (hf : differentiable_at 𝕜 f x) :
  deriv (λ y, c • f y) x = c • deriv f x :=
(hf.has_deriv_at.const_smul c).deriv

end const_smul

section neg
/-! ### Derivative of the negative of a function -/

theorem has_deriv_at_filter.neg (h : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ x, -f x) (-f') x L :=
by simpa using h.neg.has_deriv_at_filter

theorem has_deriv_within_at.neg (h : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, -f x) (-f') s x :=
h.neg

theorem has_deriv_at.neg (h : has_deriv_at f f' x) : has_deriv_at (λ x, -f x) (-f') x :=
h.neg

theorem has_strict_deriv_at.neg (h : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, -f x) (-f') x :=
by simpa using h.neg.has_strict_deriv_at

lemma deriv_within.neg (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λy, -f y) s x = - deriv_within f s x :=
by simp only [deriv_within, fderiv_within_neg hxs, continuous_linear_map.neg_apply]

lemma deriv.neg : deriv (λy, -f y) x = - deriv f x :=
by simp only [deriv, fderiv_neg, continuous_linear_map.neg_apply]

@[simp] lemma deriv.neg' : deriv (λy, -f y) = (λ x, - deriv f x) :=
funext $ λ x, deriv.neg

end neg

section neg2
/-! ### Derivative of the negation function (i.e `has_neg.neg`) -/

variables (s x L)

theorem has_deriv_at_filter_neg : has_deriv_at_filter has_neg.neg (-1) x L :=
has_deriv_at_filter.neg $ has_deriv_at_filter_id _ _

theorem has_deriv_within_at_neg : has_deriv_within_at has_neg.neg (-1) s x :=
has_deriv_at_filter_neg _ _

theorem has_deriv_at_neg : has_deriv_at has_neg.neg (-1) x :=
has_deriv_at_filter_neg _ _

theorem has_deriv_at_neg' : has_deriv_at (λ x, -x) (-1) x :=
has_deriv_at_filter_neg _ _

theorem has_strict_deriv_at_neg : has_strict_deriv_at has_neg.neg (-1) x :=
has_strict_deriv_at.neg $ has_strict_deriv_at_id _

lemma deriv_neg : deriv has_neg.neg x = -1 :=
has_deriv_at.deriv (has_deriv_at_neg x)

@[simp] lemma deriv_neg' : deriv (has_neg.neg : 𝕜 → 𝕜) = λ _, -1 :=
funext deriv_neg

@[simp] lemma deriv_neg'' : deriv (λ x : 𝕜, -x) x = -1 :=
deriv_neg x

lemma deriv_within_neg (hxs : unique_diff_within_at 𝕜 s x) : deriv_within has_neg.neg s x = -1 :=
(has_deriv_within_at_neg x s).deriv_within hxs

lemma differentiable_neg : differentiable 𝕜 (has_neg.neg : 𝕜 → 𝕜) :=
differentiable.neg differentiable_id

lemma differentiable_on_neg : differentiable_on 𝕜 (has_neg.neg : 𝕜 → 𝕜) s :=
differentiable_on.neg differentiable_on_id

end neg2

section sub
/-! ### Derivative of the difference of two functions -/

theorem has_deriv_at_filter.sub
  (hf : has_deriv_at_filter f f' x L) (hg : has_deriv_at_filter g g' x L) :
  has_deriv_at_filter (λ x, f x - g x) (f' - g') x L :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem has_deriv_within_at.sub
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ x, f x - g x) (f' - g') s x :=
hf.sub hg

theorem has_deriv_at.sub
  (hf : has_deriv_at f f' x) (hg : has_deriv_at g g' x) :
  has_deriv_at (λ x, f x - g x) (f' - g') x :=
hf.sub hg

theorem has_strict_deriv_at.sub
  (hf : has_strict_deriv_at f f' x) (hg : has_strict_deriv_at g g' x) :
  has_strict_deriv_at (λ x, f x - g x) (f' - g') x :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma deriv_within_sub (hxs : unique_diff_within_at 𝕜 s x)
  (hf : differentiable_within_at 𝕜 f s x) (hg : differentiable_within_at 𝕜 g s x) :
  deriv_within (λy, f y - g y) s x = deriv_within f s x - deriv_within g s x :=
(hf.has_deriv_within_at.sub hg.has_deriv_within_at).deriv_within hxs

@[simp] lemma deriv_sub
  (hf : differentiable_at 𝕜 f x) (hg : differentiable_at 𝕜 g x) :
  deriv (λ y, f y - g y) x = deriv f x - deriv g x :=
(hf.has_deriv_at.sub hg.has_deriv_at).deriv

theorem has_deriv_at_filter.is_O_sub (h : has_deriv_at_filter f f' x L) :
  (λ x', f x' - f x) =O[L] (λ x', x' - x) :=
has_fderiv_at_filter.is_O_sub h

theorem has_deriv_at_filter.is_O_sub_rev (hf : has_deriv_at_filter f f' x L) (hf' : f' ≠ 0) :
  (λ x', x' - x) =O[L] (λ x', f x' - f x) :=
suffices antilipschitz_with ‖f'‖₊⁻¹ (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f'), from hf.is_O_sub_rev this,
add_monoid_hom_class.antilipschitz_of_bound (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') $
  λ x, by simp [norm_smul, ← div_eq_inv_mul, mul_div_cancel _ (mt norm_eq_zero.1 hf')]

theorem has_deriv_at_filter.sub_const
  (hf : has_deriv_at_filter f f' x L) (c : F) :
  has_deriv_at_filter (λ x, f x - c) f' x L :=
by simpa only [sub_eq_add_neg] using hf.add_const (-c)

theorem has_deriv_within_at.sub_const
  (hf : has_deriv_within_at f f' s x) (c : F) :
  has_deriv_within_at (λ x, f x - c) f' s x :=
hf.sub_const c

theorem has_deriv_at.sub_const
  (hf : has_deriv_at f f' x) (c : F) :
  has_deriv_at (λ x, f x - c) f' x :=
hf.sub_const c

lemma deriv_within_sub_const (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, f y - c) s x = deriv_within f s x :=
by simp only [deriv_within, fderiv_within_sub_const hxs]

lemma deriv_sub_const (c : F) : deriv (λ y, f y - c) x = deriv f x :=
by simp only [deriv, fderiv_sub_const]

theorem has_deriv_at_filter.const_sub (c : F) (hf : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ x, c - f x) (-f') x L :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_deriv_within_at.const_sub (c : F) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, c - f x) (-f') s x :=
hf.const_sub c

theorem has_strict_deriv_at.const_sub (c : F) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, c - f x) (-f') x :=
by simpa only [sub_eq_add_neg] using hf.neg.const_add c

theorem has_deriv_at.const_sub (c : F) (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, c - f x) (-f') x :=
hf.const_sub c

lemma deriv_within_const_sub (hxs : unique_diff_within_at 𝕜 s x) (c : F) :
  deriv_within (λy, c - f y) s x = -deriv_within f s x :=
by simp [deriv_within, fderiv_within_const_sub hxs]

lemma deriv_const_sub (c : F) : deriv (λ y, c - f y) x = -deriv f x :=
by simp only [← deriv_within_univ,
  deriv_within_const_sub (unique_diff_within_at_univ : unique_diff_within_at 𝕜 _ _)]

end sub

section continuous
/-! ### Continuity of a function admitting a derivative -/

theorem has_deriv_at_filter.tendsto_nhds
  (hL : L ≤ 𝓝 x) (h : has_deriv_at_filter f f' x L) :
  tendsto f L (𝓝 (f x)) :=
h.tendsto_nhds hL

theorem has_deriv_within_at.continuous_within_at
  (h : has_deriv_within_at f f' s x) : continuous_within_at f s x :=
has_deriv_at_filter.tendsto_nhds inf_le_left h

theorem has_deriv_at.continuous_at (h : has_deriv_at f f' x) : continuous_at f x :=
has_deriv_at_filter.tendsto_nhds le_rfl h

protected theorem has_deriv_at.continuous_on {f f' : 𝕜 → F}
  (hderiv : ∀ x ∈ s, has_deriv_at f (f' x) x) : continuous_on f s :=
λ x hx, (hderiv x hx).continuous_at.continuous_within_at

end continuous

section cartesian_product
/-! ### Derivative of the cartesian product of two functions -/

variables {G : Type w} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {f₂ : 𝕜 → G} {f₂' : G}

lemma has_deriv_at_filter.prod
  (hf₁ : has_deriv_at_filter f₁ f₁' x L) (hf₂ : has_deriv_at_filter f₂ f₂' x L) :
  has_deriv_at_filter (λ x, (f₁ x, f₂ x)) (f₁', f₂') x L :=
hf₁.prod hf₂

lemma has_deriv_within_at.prod
  (hf₁ : has_deriv_within_at f₁ f₁' s x) (hf₂ : has_deriv_within_at f₂ f₂' s x) :
  has_deriv_within_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') s x :=
hf₁.prod hf₂

lemma has_deriv_at.prod (hf₁ : has_deriv_at f₁ f₁' x) (hf₂ : has_deriv_at f₂ f₂' x) :
  has_deriv_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') x :=
hf₁.prod hf₂

lemma has_strict_deriv_at.prod (hf₁ : has_strict_deriv_at f₁ f₁' x)
  (hf₂ : has_strict_deriv_at f₂ f₂' x) :
  has_strict_deriv_at (λ x, (f₁ x, f₂ x)) (f₁', f₂') x :=
hf₁.prod hf₂

end cartesian_product

section composition
/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector valued and scalar valued functions, and `comp`
in lemmas on composition of scalar valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/

/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {s' t' : set 𝕜'}
  {h : 𝕜 → 𝕜'} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'} {h₁' : 𝕜}
  {g₁ : 𝕜' → F} {g₁' : F} {L' : filter 𝕜'} (x)

theorem has_deriv_at_filter.scomp
  (hg : has_deriv_at_filter g₁ g₁' (h x) L')
  (hh : has_deriv_at_filter h h' x L) (hL : tendsto h L L'):
  has_deriv_at_filter (g₁ ∘ h) (h' • g₁') x L :=
by simpa using ((hg.restrict_scalars 𝕜).comp x hh hL).has_deriv_at_filter

theorem has_deriv_within_at.scomp_has_deriv_at
  (hg : has_deriv_within_at g₁ g₁' s' (h x))
  (hh : has_deriv_at h h' x) (hs : ∀ x, h x ∈ s') :
  has_deriv_at (g₁ ∘ h) (h' • g₁') x :=
hg.scomp x hh $ tendsto_inf.2 ⟨hh.continuous_at, tendsto_principal.2 $ eventually_of_forall hs⟩

theorem has_deriv_within_at.scomp
  (hg : has_deriv_within_at g₁ g₁' t' (h x))
  (hh : has_deriv_within_at h h' s x) (hst : maps_to h s t') :
  has_deriv_within_at (g₁ ∘ h) (h' • g₁') s x :=
hg.scomp x hh $ hh.continuous_within_at.tendsto_nhds_within hst

/-- The chain rule. -/
theorem has_deriv_at.scomp
  (hg : has_deriv_at g₁ g₁' (h x)) (hh : has_deriv_at h h' x) :
  has_deriv_at (g₁ ∘ h) (h' • g₁') x :=
hg.scomp x hh hh.continuous_at

theorem has_strict_deriv_at.scomp
  (hg : has_strict_deriv_at g₁ g₁' (h x)) (hh : has_strict_deriv_at h h' x) :
  has_strict_deriv_at (g₁ ∘ h) (h' • g₁') x :=
by simpa using ((hg.restrict_scalars 𝕜).comp x hh).has_strict_deriv_at

theorem has_deriv_at.scomp_has_deriv_within_at
  (hg : has_deriv_at g₁ g₁' (h x)) (hh : has_deriv_within_at h h' s x) :
  has_deriv_within_at (g₁ ∘ h) (h' • g₁') s x :=
has_deriv_within_at.scomp x hg.has_deriv_within_at hh (maps_to_univ _ _)

lemma deriv_within.scomp
  (hg : differentiable_within_at 𝕜' g₁ t' (h x)) (hh : differentiable_within_at 𝕜 h s x)
  (hs : maps_to h s t') (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (g₁ ∘ h) s x = deriv_within h s x • deriv_within g₁ t' (h x) :=
(has_deriv_within_at.scomp x hg.has_deriv_within_at hh.has_deriv_within_at hs).deriv_within hxs

lemma deriv.scomp
  (hg : differentiable_at 𝕜' g₁ (h x)) (hh : differentiable_at 𝕜 h x) :
  deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) :=
(has_deriv_at.scomp x hg.has_deriv_at hh.has_deriv_at).deriv

/-! ### Derivative of the composition of a scalar and vector functions -/

theorem has_deriv_at_filter.comp_has_fderiv_at_filter {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
  {L'' : filter E} (hh₂ : has_deriv_at_filter h₂ h₂' (f x) L')
  (hf : has_fderiv_at_filter f f' x L'') (hL : tendsto f L'' L') :
  has_fderiv_at_filter (h₂ ∘ f) (h₂' • f') x L'' :=
by { convert (hh₂.restrict_scalars 𝕜).comp x hf hL, ext x, simp [mul_comm] }

theorem has_strict_deriv_at.comp_has_strict_fderiv_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
  (hh : has_strict_deriv_at h₂ h₂' (f x)) (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (h₂ ∘ f) (h₂' • f') x :=
begin
  rw has_strict_deriv_at at hh,
  convert (hh.restrict_scalars 𝕜).comp x hf,
  ext x,
  simp [mul_comm]
end

theorem has_deriv_at.comp_has_fderiv_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
  (hh : has_deriv_at h₂ h₂' (f x)) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (h₂ ∘ f) (h₂' • f') x :=
hh.comp_has_fderiv_at_filter x hf hf.continuous_at

theorem has_deriv_at.comp_has_fderiv_within_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
  (hh : has_deriv_at h₂ h₂' (f x)) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (h₂ ∘ f) (h₂' • f') s x :=
hh.comp_has_fderiv_at_filter x hf hf.continuous_within_at

theorem has_deriv_within_at.comp_has_fderiv_within_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
  (hh : has_deriv_within_at h₂ h₂' t (f x)) (hf : has_fderiv_within_at f f' s x)
  (hst : maps_to f s t) :
  has_fderiv_within_at (h₂ ∘ f) (h₂' • f') s x :=
hh.comp_has_fderiv_at_filter x hf $ hf.continuous_within_at.tendsto_nhds_within hst

/-! ### Derivative of the composition of two scalar functions -/

theorem has_deriv_at_filter.comp
  (hh₂ : has_deriv_at_filter h₂ h₂' (h x) L')
  (hh : has_deriv_at_filter h h' x L) (hL : tendsto h L L') :
  has_deriv_at_filter (h₂ ∘ h) (h₂' * h') x L :=
by { rw mul_comm, exact hh₂.scomp x hh hL }

theorem has_deriv_within_at.comp
  (hh₂ : has_deriv_within_at h₂ h₂' s' (h x))
  (hh : has_deriv_within_at h h' s x) (hst : maps_to h s s') :
  has_deriv_within_at (h₂ ∘ h) (h₂' * h') s x :=
by { rw mul_comm, exact hh₂.scomp x hh hst, }

/-- The chain rule. -/
theorem has_deriv_at.comp
  (hh₂ : has_deriv_at h₂ h₂' (h x)) (hh : has_deriv_at h h' x) :
  has_deriv_at (h₂ ∘ h) (h₂' * h') x :=
hh₂.comp x hh hh.continuous_at

theorem has_strict_deriv_at.comp
  (hh₂ : has_strict_deriv_at h₂ h₂' (h x)) (hh : has_strict_deriv_at h h' x) :
  has_strict_deriv_at (h₂ ∘ h) (h₂' * h') x :=
by { rw mul_comm, exact hh₂.scomp x hh }

theorem has_deriv_at.comp_has_deriv_within_at
  (hh₂ : has_deriv_at h₂ h₂' (h x)) (hh : has_deriv_within_at h h' s x) :
  has_deriv_within_at (h₂ ∘ h) (h₂' * h') s x :=
hh₂.has_deriv_within_at.comp x hh (maps_to_univ _ _)

lemma deriv_within.comp
  (hh₂ : differentiable_within_at 𝕜' h₂ s' (h x)) (hh : differentiable_within_at 𝕜 h s x)
  (hs : maps_to h s s') (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (h₂ ∘ h) s x = deriv_within h₂ s' (h x) * deriv_within h s x :=
(hh₂.has_deriv_within_at.comp x hh.has_deriv_within_at hs).deriv_within hxs

lemma deriv.comp
  (hh₂ : differentiable_at 𝕜' h₂ (h x)) (hh : differentiable_at 𝕜 h x) :
  deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
(hh₂.has_deriv_at.comp x hh.has_deriv_at).deriv

protected lemma has_deriv_at_filter.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_deriv_at_filter f f' x L) (hL : tendsto f L L) (hx : f x = x) (n : ℕ) :
  has_deriv_at_filter (f^[n]) (f'^n) x L :=
begin
  have := hf.iterate hL hx n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

protected lemma has_deriv_at.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_deriv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_deriv_at (f^[n]) (f'^n) x :=
begin
  have := has_fderiv_at.iterate hf hx n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

protected lemma has_deriv_within_at.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_deriv_within_at f f' s x) (hx : f x = x) (hs : maps_to f s s) (n : ℕ) :
  has_deriv_within_at (f^[n]) (f'^n) s x :=
begin
  have := has_fderiv_within_at.iterate hf hx hs n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

protected lemma has_strict_deriv_at.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_strict_deriv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_strict_deriv_at (f^[n]) (f'^n) x :=
begin
  have := hf.iterate hx n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

end composition

section composition_vector
/-! ### Derivative of the composition of a function between vector spaces and a function on `𝕜` -/

open continuous_linear_map

variables {l : F → E} {l' : F →L[𝕜] E}
variable (x)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_within_at.comp_has_deriv_within_at {t : set F}
  (hl : has_fderiv_within_at l l' t (f x)) (hf : has_deriv_within_at f f' s x)
  (hst : maps_to f s t) :
  has_deriv_within_at (l ∘ f) (l' f') s x :=
by simpa only [one_apply, one_smul, smul_right_apply, coe_comp', (∘)]
  using (hl.comp x hf.has_fderiv_within_at hst).has_deriv_within_at

theorem has_fderiv_at.comp_has_deriv_within_at
  (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (l ∘ f) (l' f') s x :=
hl.has_fderiv_within_at.comp_has_deriv_within_at x hf (maps_to_univ _ _)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_at.comp_has_deriv_at (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_at f f' x) :
  has_deriv_at (l ∘ f) (l' f') x :=
has_deriv_within_at_univ.mp $ hl.comp_has_deriv_within_at x hf.has_deriv_within_at

theorem has_strict_fderiv_at.comp_has_strict_deriv_at
  (hl : has_strict_fderiv_at l l' (f x)) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (l ∘ f) (l' f') x :=
by simpa only [one_apply, one_smul, smul_right_apply, coe_comp', (∘)]
  using (hl.comp x hf.has_strict_fderiv_at).has_strict_deriv_at

lemma fderiv_within.comp_deriv_within {t : set F}
  (hl : differentiable_within_at 𝕜 l t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (hs : maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (l ∘ f) s x = (fderiv_within 𝕜 l t (f x) : F → E) (deriv_within f s x) :=
(hl.has_fderiv_within_at.comp_has_deriv_within_at x hf.has_deriv_within_at hs).deriv_within hxs

lemma fderiv.comp_deriv
  (hl : differentiable_at 𝕜 l (f x)) (hf : differentiable_at 𝕜 f x) :
  deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
(hl.has_fderiv_at.comp_has_deriv_at x hf.has_deriv_at).deriv

end composition_vector

section mul
/-! ### Derivative of the multiplication of two functions -/
variables {𝕜' 𝔸 : Type*} [normed_field 𝕜'] [normed_ring 𝔸] [normed_algebra 𝕜 𝕜']
  [normed_algebra 𝕜 𝔸] {c d : 𝕜 → 𝔸} {c' d' : 𝔸} {u v : 𝕜 → 𝕜'}

theorem has_deriv_within_at.mul
  (hc : has_deriv_within_at c c' s x) (hd : has_deriv_within_at d d' s x) :
  has_deriv_within_at (λ y, c y * d y) (c' * d x + c x * d') s x :=
begin
  have := (has_fderiv_within_at.mul' hc hd).has_deriv_within_at,
  rwa [continuous_linear_map.add_apply, continuous_linear_map.smul_apply,
      continuous_linear_map.smul_right_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply,
      one_smul, one_smul, add_comm] at this,
end

theorem has_deriv_at.mul (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) :
  has_deriv_at (λ y, c y * d y) (c' * d x + c x * d') x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.mul hd
end

theorem has_strict_deriv_at.mul
  (hc : has_strict_deriv_at c c' x) (hd : has_strict_deriv_at d d' x) :
  has_strict_deriv_at (λ y, c y * d y) (c' * d x + c x * d') x :=
begin
  have := (has_strict_fderiv_at.mul' hc hd).has_strict_deriv_at,
  rwa [continuous_linear_map.add_apply, continuous_linear_map.smul_apply,
      continuous_linear_map.smul_right_apply, continuous_linear_map.smul_right_apply,
      continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply,
      one_smul, one_smul, add_comm] at this,
end

lemma deriv_within_mul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  deriv_within (λ y, c y * d y) s x = deriv_within c s x * d x + c x * deriv_within d s x :=
(hc.has_deriv_within_at.mul hd.has_deriv_within_at).deriv_within hxs

@[simp] lemma deriv_mul (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  deriv (λ y, c y * d y) x = deriv c x * d x + c x * deriv d x :=
(hc.has_deriv_at.mul hd.has_deriv_at).deriv

theorem has_deriv_within_at.mul_const (hc : has_deriv_within_at c c' s x) (d : 𝔸) :
  has_deriv_within_at (λ y, c y * d) (c' * d) s x :=
begin
  convert hc.mul (has_deriv_within_at_const x s d),
  rw [mul_zero, add_zero]
end

theorem has_deriv_at.mul_const (hc : has_deriv_at c c' x) (d : 𝔸) :
  has_deriv_at (λ y, c y * d) (c' * d) x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.mul_const d
end

theorem has_deriv_at_mul_const (c : 𝕜) : has_deriv_at (λ x, x * c) c x :=
by simpa only [one_mul] using (has_deriv_at_id' x).mul_const c

theorem has_strict_deriv_at.mul_const (hc : has_strict_deriv_at c c' x) (d : 𝔸) :
  has_strict_deriv_at (λ y, c y * d) (c' * d) x :=
begin
  convert hc.mul (has_strict_deriv_at_const x d),
  rw [mul_zero, add_zero]
end

lemma deriv_within_mul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (d : 𝔸) :
  deriv_within (λ y, c y * d) s x = deriv_within c s x * d :=
(hc.has_deriv_within_at.mul_const d).deriv_within hxs

lemma deriv_mul_const (hc : differentiable_at 𝕜 c x) (d : 𝔸) :
  deriv (λ y, c y * d) x = deriv c x * d :=
(hc.has_deriv_at.mul_const d).deriv

lemma deriv_mul_const_field (v : 𝕜') :
  deriv (λ y, u y * v) x = deriv u x * v :=
begin
  by_cases hu : differentiable_at 𝕜 u x,
  { exact deriv_mul_const hu v },
  { rw [deriv_zero_of_not_differentiable_at hu, zero_mul],
    rcases eq_or_ne v 0 with rfl|hd,
    { simp only [mul_zero, deriv_const] },
    { refine deriv_zero_of_not_differentiable_at (mt (λ H, _) hu),
      simpa only [mul_inv_cancel_right₀ hd] using H.mul_const v⁻¹ } }
end

@[simp] lemma deriv_mul_const_field' (v : 𝕜') : deriv (λ x, u x * v) = λ x, deriv u x * v :=
funext $ λ _, deriv_mul_const_field v

theorem has_deriv_within_at.const_mul (c : 𝔸) (hd : has_deriv_within_at d d' s x) :
  has_deriv_within_at (λ y, c * d y) (c * d') s x :=
begin
  convert (has_deriv_within_at_const x s c).mul hd,
  rw [zero_mul, zero_add]
end

theorem has_deriv_at.const_mul (c : 𝔸) (hd : has_deriv_at d d' x) :
  has_deriv_at (λ y, c * d y) (c * d') x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hd.const_mul c
end

theorem has_strict_deriv_at.const_mul (c : 𝔸) (hd : has_strict_deriv_at d d' x) :
  has_strict_deriv_at (λ y, c * d y) (c * d') x :=
begin
  convert (has_strict_deriv_at_const _ _).mul hd,
  rw [zero_mul, zero_add]
end

lemma deriv_within_const_mul (hxs : unique_diff_within_at 𝕜 s x)
  (c : 𝔸) (hd : differentiable_within_at 𝕜 d s x) :
  deriv_within (λ y, c * d y) s x = c * deriv_within d s x :=
(hd.has_deriv_within_at.const_mul c).deriv_within hxs

lemma deriv_const_mul (c : 𝔸) (hd : differentiable_at 𝕜 d x) :
  deriv (λ y, c * d y) x = c * deriv d x :=
(hd.has_deriv_at.const_mul c).deriv

lemma deriv_const_mul_field (u : 𝕜') : deriv (λ y, u * v y) x = u * deriv v x :=
by simp only [mul_comm u, deriv_mul_const_field]

@[simp] lemma deriv_const_mul_field' (u : 𝕜') : deriv (λ x, u * v x) = λ x, u * deriv v x :=
funext (λ x, deriv_const_mul_field u)

end mul

section clm_comp_apply
/-! ### Derivative of the pointwise composition/application of continuous linear maps -/

open continuous_linear_map

variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G] {c : 𝕜 → F →L[𝕜] G}
  {c' : F →L[𝕜] G} {d : 𝕜 → E →L[𝕜] F} {d' : E →L[𝕜] F} {u : 𝕜 → F} {u' : F}

lemma has_strict_deriv_at.clm_comp (hc : has_strict_deriv_at c c' x)
  (hd : has_strict_deriv_at d d' x) :
  has_strict_deriv_at (λ y, (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') x :=
begin
  have := (hc.has_strict_fderiv_at.clm_comp hd.has_strict_fderiv_at).has_strict_deriv_at,
  rwa [add_apply, comp_apply, comp_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma has_deriv_within_at.clm_comp (hc : has_deriv_within_at c c' s x)
  (hd : has_deriv_within_at d d' s x) :
  has_deriv_within_at (λ y, (c y).comp (d y)) (c'.comp (d x) + (c x).comp d') s x :=
begin
  have := (hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).has_deriv_within_at,
  rwa [add_apply, comp_apply, comp_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma has_deriv_at.clm_comp (hc : has_deriv_at c c' x) (hd : has_deriv_at d d' x) :
  has_deriv_at (λ y, (c y).comp (d y))
  (c'.comp (d x) + (c x).comp d') x :=
begin
  rw [← has_deriv_within_at_univ] at *,
  exact hc.clm_comp hd
end

lemma deriv_within_clm_comp (hc : differentiable_within_at 𝕜 c s x)
  (hd : differentiable_within_at 𝕜 d s x) (hxs : unique_diff_within_at 𝕜 s x):
  deriv_within (λ y, (c y).comp (d y)) s x =
    ((deriv_within c s x).comp (d x) + (c x).comp (deriv_within d s x)) :=
(hc.has_deriv_within_at.clm_comp hd.has_deriv_within_at).deriv_within hxs

lemma deriv_clm_comp (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  deriv (λ y, (c y).comp (d y)) x =
    ((deriv c x).comp (d x) + (c x).comp (deriv d x)) :=
(hc.has_deriv_at.clm_comp hd.has_deriv_at).deriv

lemma has_strict_deriv_at.clm_apply (hc : has_strict_deriv_at c c' x)
  (hu : has_strict_deriv_at u u' x) :
  has_strict_deriv_at (λ y, (c y) (u y)) (c' (u x) + c x u') x :=
begin
  have := (hc.has_strict_fderiv_at.clm_apply hu.has_strict_fderiv_at).has_strict_deriv_at,
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma has_deriv_within_at.clm_apply (hc : has_deriv_within_at c c' s x)
  (hu : has_deriv_within_at u u' s x) :
  has_deriv_within_at (λ y, (c y) (u y)) (c' (u x) + c x u') s x :=
begin
  have := (hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).has_deriv_within_at,
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma has_deriv_at.clm_apply (hc : has_deriv_at c c' x) (hu : has_deriv_at u u' x) :
  has_deriv_at (λ y, (c y) (u y)) (c' (u x) + c x u') x :=
begin
  have := (hc.has_fderiv_at.clm_apply hu.has_fderiv_at).has_deriv_at,
  rwa [add_apply, comp_apply, flip_apply, smul_right_apply, smul_right_apply, one_apply, one_smul,
      one_smul, add_comm] at this,
end

lemma deriv_within_clm_apply (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hu : differentiable_within_at 𝕜 u s x) :
  deriv_within (λ y, (c y) (u y)) s x = (deriv_within c s x (u x) + c x (deriv_within u s x)) :=
(hc.has_deriv_within_at.clm_apply hu.has_deriv_within_at).deriv_within hxs

lemma deriv_clm_apply (hc : differentiable_at 𝕜 c x) (hu : differentiable_at 𝕜 u x) :
  deriv (λ y, (c y) (u y)) x = (deriv c x (u x) + c x (deriv u x)) :=
(hc.has_deriv_at.clm_apply hu.has_deriv_at).deriv

end clm_comp_apply

theorem has_strict_deriv_at.has_strict_fderiv_at_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜}
  (hf : has_strict_deriv_at f f' x) (hf' : f' ≠ 0) :
  has_strict_fderiv_at f
    (continuous_linear_equiv.units_equiv_aut 𝕜 (units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
hf

theorem has_deriv_at.has_fderiv_at_equiv {f : 𝕜 → 𝕜} {f' x : 𝕜} (hf : has_deriv_at f f' x)
  (hf' : f' ≠ 0) :
  has_fderiv_at f (continuous_linear_equiv.units_equiv_aut 𝕜 (units.mk0 f' hf') : 𝕜 →L[𝕜] 𝕜) x :=
hf

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem has_strict_deriv_at.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜}
  (hg : continuous_at g a) (hf : has_strict_deriv_at f f' (g a)) (hf' : f' ≠ 0)
  (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
  has_strict_deriv_at g f'⁻¹ a :=
(hf.has_strict_fderiv_at_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has a
nonzero derivative `f'` at `f.symm a` in the strict sense, then `f.symm` has the derivative `f'⁻¹`
at `a` in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
lemma local_homeomorph.has_strict_deriv_at_symm (f : local_homeomorph 𝕜 𝕜) {a f' : 𝕜}
  (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : has_strict_deriv_at f f' (f.symm a)) :
  has_strict_deriv_at f.symm f'⁻¹ a :=
htff'.of_local_left_inverse (f.symm.continuous_at ha) hf' (f.eventually_right_inverse ha)

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem has_deriv_at.of_local_left_inverse {f g : 𝕜 → 𝕜} {f' a : 𝕜}
  (hg : continuous_at g a) (hf : has_deriv_at f f' (g a)) (hf' : f' ≠ 0)
  (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) :
  has_deriv_at g f'⁻¹ a :=
(hf.has_fderiv_at_equiv hf').of_local_left_inverse hg hfg

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
nonzero derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
lemma local_homeomorph.has_deriv_at_symm (f : local_homeomorph 𝕜 𝕜) {a f' : 𝕜}
  (ha : a ∈ f.target) (hf' : f' ≠ 0) (htff' : has_deriv_at f f' (f.symm a)) :
  has_deriv_at f.symm f'⁻¹ a :=
htff'.of_local_left_inverse (f.symm.continuous_at ha) hf' (f.eventually_right_inverse ha)

lemma has_deriv_at.eventually_ne (h : has_deriv_at f f' x) (hf' : f' ≠ 0) :
  ∀ᶠ z in 𝓝[≠] x, f z ≠ f x :=
(has_deriv_at_iff_has_fderiv_at.1 h).eventually_ne
  ⟨‖f'‖⁻¹, λ z, by field_simp [norm_smul, mt norm_eq_zero.1 hf']⟩

lemma has_deriv_at.tendsto_punctured_nhds (h : has_deriv_at f f' x) (hf' : f' ≠ 0) :
  tendsto f (𝓝[≠] x) (𝓝[≠] (f x)) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  h.continuous_at.continuous_within_at (h.eventually_ne hf')

theorem not_differentiable_within_at_of_local_left_inverse_has_deriv_within_at_zero
  {f g : 𝕜 → 𝕜} {a : 𝕜} {s t : set 𝕜} (ha : a ∈ s) (hsu : unique_diff_within_at 𝕜 s a)
  (hf : has_deriv_within_at f 0 t (g a)) (hst : maps_to g s t) (hfg : f ∘ g =ᶠ[𝓝[s] a] id) :
  ¬differentiable_within_at 𝕜 g s a :=
begin
  intro hg,
  have := (hf.comp a hg.has_deriv_within_at hst).congr_of_eventually_eq_of_mem hfg.symm ha,
  simpa using hsu.eq_deriv _ this (has_deriv_within_at_id _ _)
end

theorem not_differentiable_at_of_local_left_inverse_has_deriv_at_zero
  {f g : 𝕜 → 𝕜} {a : 𝕜} (hf : has_deriv_at f 0 (g a)) (hfg : f ∘ g =ᶠ[𝓝 a] id) :
  ¬differentiable_at 𝕜 g a :=
begin
  intro hg,
  have := (hf.comp a hg.has_deriv_at).congr_of_eventually_eq hfg.symm,
  simpa using this.unique (has_deriv_at_id a)
end

end
