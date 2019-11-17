/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner
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
  - subtraction
  - multiplication
  - negation
  - multiplication of two functions in `𝕜 → 𝕜`
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜`

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

-/

universes u v w
noncomputable theory
open_locale classical
open filter continuous_linear_map asymptotics set

set_option class.instance_max_depth 100

variables {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
variables {F : Type v} [normed_group F] [normed_space 𝕜 F]

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
has_deriv_at_filter f f' x (nhds x)

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

lemma has_fderiv_at_filter_iff_has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at_filter f f' x L ↔ has_deriv_at_filter f (f' 1) x L :=
by simp [has_deriv_at_filter]

lemma has_fderiv_within_at_iff_has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_within_at f f' s x ↔ has_deriv_within_at f (f' 1) s x :=
by simp [has_deriv_within_at, has_deriv_at_filter, has_fderiv_within_at]

lemma has_fderiv_at_iff_has_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at f f' x ↔ has_deriv_at f (f' 1) x :=
by simp [has_deriv_at, has_deriv_at_filter, has_fderiv_at]

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
  tendsto (λ x' : 𝕜, ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) L (nhds 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_within_at_iff_tendsto : has_deriv_within_at f f' s x ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) (nhds_within x s) (nhds 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_iff_tendsto : has_deriv_at f f' x ↔
  tendsto (λ x', ∥x' - x∥⁻¹ * ∥f x' - f x - (x' - x) • f'∥) (nhds x) (nhds 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_filter.mono (h : has_deriv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) :
  has_deriv_at_filter f f' x L₁ :=
has_fderiv_at_filter.mono h hst

theorem has_deriv_within_at.mono (h : has_deriv_within_at f f' t x) (hst : s ⊆ t) :
  has_deriv_within_at f f' s x :=
has_fderiv_within_at.mono h hst

theorem has_deriv_at.has_deriv_at_filter (h : has_deriv_at f f' x) (hL : L ≤ nhds x) :
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

lemma has_deriv_within_at_inter (h : t ∈ nhds x) :
  has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_inter h

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

lemma deriv_within_fderiv_within : smul_right 1 (deriv_within f s x) = fderiv_within 𝕜 f s x :=
by simp [deriv_within]

lemma fderiv_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
rfl

lemma deriv_fderiv : smul_right 1 (deriv f x) = fderiv 𝕜 f x :=
by simp [deriv]

lemma differentiable_at.deriv_within (h : differentiable_at 𝕜 f x)
  (hxs : unique_diff_within_at 𝕜 s x) : deriv_within f s x = deriv f x :=
by { unfold deriv_within deriv, rw differentiable.fderiv_within h hxs }

lemma deriv_within_subset (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  deriv_within f s x = deriv_within f t x :=
((differentiable_within_at.has_deriv_within_at h).mono st).deriv_within ht

@[simp] lemma deriv_within_univ : deriv_within f univ = deriv f :=
by { ext, unfold deriv_within deriv, rw fderiv_within_univ }

lemma deriv_within_inter (ht : t ∈ nhds x) (hs : unique_diff_within_at 𝕜 s x) :
  deriv_within f (s ∩ t) x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_inter ht hs }

section congr

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
  (h₁ : {y | f₁ y = f y} ∈ nhds x) : has_deriv_at f₁ f' x :=
has_deriv_at_filter.congr_of_mem_sets h h₁ (mem_of_nhds h₁ : _)

lemma deriv_within_congr_of_mem_nhds_within (hs : unique_diff_within_at 𝕜 s x)
  (hL : {y | f₁ y = f y} ∈ nhds_within x s) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_congr_of_mem_nhds_within hs hL hx }

lemma deriv_within_congr (hs : unique_diff_within_at 𝕜 s x)
  (hL : ∀y∈s, f₁ y = f y) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_congr hs hL hx }

lemma deriv_congr_of_mem_nhds (hL : {y | f₁ y = f y} ∈ nhds x) : deriv f₁ x = deriv f x :=
by { unfold deriv, rwa fderiv_congr_of_mem_nhds }

end congr

/- id -/
section id
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

/- constants -/
section const
variables (c : F) (s x L)

theorem has_deriv_at_filter_const : has_deriv_at_filter (λ x, c) 0 x L :=
(is_o_zero _ _).congr_left $ λ _, by simp [zero_apply, sub_self]

theorem has_deriv_within_at_const : has_deriv_within_at (λ x, c) 0 s x :=
has_deriv_at_filter_const _ _ _

theorem has_deriv_at_const : has_deriv_at (λ x, c) 0 x :=
has_deriv_at_filter_const _ _ _

lemma deriv_const : deriv (λ x, c) x = 0 :=
has_deriv_at.deriv (has_deriv_at_const x c)

lemma deriv_within_const (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (λ x, c) s x = 0 :=
by { rw (differentiable_at_const _).deriv_within hxs, apply deriv_const }

end const

/- Linear maps -/
section is_linear_map
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

/- neg -/
section neg

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

/- sub -/
section sub

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

/- Continuity -/
section continuous

theorem has_deriv_at_filter.tendsto_nhds
  (hL : L ≤ nhds x) (h : has_deriv_at_filter f f' x L) :
  tendsto f L (nhds (f x)) :=
has_fderiv_at_filter.tendsto_nhds hL h

theorem has_deriv_within_at.continuous_within_at
  (h : has_deriv_within_at f f' s x) : continuous_within_at f s x :=
has_deriv_at_filter.tendsto_nhds lattice.inf_le_left h

theorem has_deriv_at.continuous_at (h : has_deriv_at f f' x) : continuous_at f x :=
has_deriv_at_filter.tendsto_nhds (le_refl _) h

end continuous

/- Cartesian products -/
section cartesian_product
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

/- Composition -/
section composition
variables {h : 𝕜 → 𝕜} {h' : 𝕜}
/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variable (x)

theorem has_deriv_at_filter.comp
  (hg : has_deriv_at_filter g g' (h x) (L.map h))
  (hh : has_deriv_at_filter h h' x L) :
  has_deriv_at_filter (g ∘ h) (h' • g') x L :=
have (smul_right 1 g' : 𝕜 →L[𝕜] _).comp (smul_right 1 h' : 𝕜 →L[𝕜] _) =
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

/- Multiplication -/
section mul
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
