/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.fderiv.basic
import analysis.calculus.fderiv.linear
import analysis.calculus.fderiv.comp
import analysis.calculus.fderiv.prod
import analysis.calculus.fderiv.bilinear

open filter asymptotics continuous_linear_map set metric
open_locale topology classical nnreal filter asymptotics ennreal

noncomputable theory


section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']

variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[𝕜] F}
variables (e : E →L[𝕜] F)
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}

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
