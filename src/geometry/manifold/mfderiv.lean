/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import geometry.manifold.local_invariant_properties
import geometry.manifold.tangent_bundle

/-!
# The derivative of functions between smooth manifolds

Let `M` and `M'` be two smooth manifolds with corners over a field `𝕜` (with respective models with
corners `I` on `(E, H)` and `I'` on `(E', H')`), and let `f : M → M'`. We define the
derivative of the function at a point, within a set or along the whole space, mimicking the API
for (Fréchet) derivatives. It is denoted by `mfderiv I I' f x`, where "m" stands for "manifold" and
"f" for "Fréchet" (as in the usual derivative `fderiv 𝕜 f x`).

## Main definitions

* `unique_mdiff_on I s` : predicate saying that, at each point of the set `s`, a function can have
  at most one derivative. This technical condition is important when we define
  `mfderiv_within` below, as otherwise there is an arbitrary choice in the derivative,
  and many properties will fail (for instance the chain rule). This is analogous to
  `unique_diff_on 𝕜 s` in a vector space.

Let `f` be a map between smooth manifolds. The following definitions follow the `fderiv` API.

* `mfderiv I I' f x` : the derivative of `f` at `x`, as a continuous linear map from the tangent
  space at `x` to the tangent space at `f x`. If the map is not differentiable, this is `0`.
* `mfderiv_within I I' f s x` : the derivative of `f` at `x` within `s`, as a continuous linear map
  from the tangent space at `x` to the tangent space at `f x`. If the map is not differentiable
  within `s`, this is `0`.
* `mdifferentiable_at I I' f x` : Prop expressing whether `f` is differentiable at `x`.
* `mdifferentiable_within_at 𝕜 f s x` : Prop expressing whether `f` is differentiable within `s`
  at `x`.
* `has_mfderiv_at I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative at `x`.
* `has_mfderiv_within_at I I' f s x f'` : Prop expressing whether `f` has `f'` as a derivative
  within `s` at `x`.
* `mdifferentiable_on I I' f s` : Prop expressing that `f` is differentiable on the set `s`.
* `mdifferentiable I I' f` : Prop expressing that `f` is differentiable everywhere.
* `tangent_map I I' f` : the derivative of `f`, as a map from the tangent bundle of `M` to the
  tangent bundle of `M'`.

We also establish results on the differential of the identity, constant functions, charts, extended
charts. For functions between vector spaces, we show that the usual notions and the manifold notions
coincide.

## Implementation notes

The tangent bundle is constructed using the machinery of topological fiber bundles, for which one
can define bundled morphisms and construct canonically maps from the total space of one bundle to
the total space of another one. One could use this mechanism to construct directly the derivative
of a smooth map. However, we want to define the derivative of any map (and let it be zero if the map
is not differentiable) to avoid proof arguments everywhere. This means we have to go back to the
details of the definition of the total space of a fiber bundle constructed from core, to cook up a
suitable definition of the derivative. It is the following: at each point, we have a preferred chart
(used to identify the fiber above the point with the model vector space in fiber bundles). Then one
should read the function using these preferred charts at `x` and `f x`, and take the derivative
of `f` in these charts.

Due to the fact that we are working in a model with corners, with an additional embedding `I` of the
model space `H` in the model vector space `E`, the charts taking values in `E` are not the original
charts of the manifold, but those ones composed with `I`, called extended charts. We define
`written_in_ext_chart I I' x f` for the function `f` written in the preferred extended charts.  Then
the manifold derivative of `f`, at `x`, is just the usual derivative of `written_in_ext_chart I I' x
f`, at the point `(ext_chart_at I x) x`.

There is a subtelty with respect to continuity: if the function is not continuous, then the image
of a small open set around `x` will not be contained in the source of the preferred chart around
`f x`, which means that when reading `f` in the chart one is losing some information. To avoid this,
we include continuity in the definition of differentiablity (which is reasonable since with any
definition, differentiability implies continuity).

*Warning*: the derivative (even within a subset) is a linear map on the whole tangent space. Suppose
that one is given a smooth submanifold `N`, and a function which is smooth on `N` (i.e., its
restriction to the subtype  `N` is smooth). Then, in the whole manifold `M`, the property
`mdifferentiable_on I I' f N` holds. However, `mfderiv_within I I' f N` is not uniquely defined
(what values would one choose for vectors that are transverse to `N`?), which can create issues down
the road. The problem here is that knowing the value of `f` along `N` does not determine the
differential of `f` in all directions. This is in contrast to the case where `N` would be an open
subset, or a submanifold with boundary of maximal dimension, where this issue does not appear.
The predicate `unique_mdiff_on I N` indicates that the derivative along `N` is unique if it exists,
and is an assumption in most statements requiring a form of uniqueness.

On a vector space, the manifold derivative and the usual derivative are equal. This means in
particular that they live on the same space, i.e., the tangent space is defeq to the original vector
space. To get this property is a motivation for our definition of the tangent space as a single
copy of the vector space, instead of more usual definitions such as the space of derivations, or
the space of equivalence classes of smooth curves in the manifold.

## Tags
Derivative, manifold
-/

noncomputable theory
open_locale classical topology manifold

open set

universe u

section derivatives_definitions
/-!
### Derivative of maps between manifolds

The derivative of a smooth map `f` between smooth manifold `M` and `M'` at `x` is a bounded linear
map from the tangent space to `M` at `x`, to the tangent space to `M'` at `f x`. Since we defined
the tangent space using one specific chart, the formula for the derivative is written in terms of
this specific chart.

We use the names `mdifferentiable` and `mfderiv`, where the prefix letter `m` means "manifold".
-/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M']

/-- Property in the model space of a model with corners of being differentiable within at set at a
point, when read in the model vector space. This property will be lifted to manifolds to define
differentiable functions between manifolds. -/
def differentiable_within_at_prop (f : H → H') (s : set H) (x : H) : Prop :=
differentiable_within_at 𝕜 (I' ∘ f ∘ (I.symm)) (⇑(I.symm) ⁻¹' s ∩ set.range I) (I x)

/-- Being differentiable in the model space is a local property, invariant under smooth maps.
Therefore, it will lift nicely to manifolds. -/
lemma differentiable_within_at_local_invariant_prop :
  (cont_diff_groupoid ⊤ I).local_invariant_prop (cont_diff_groupoid ⊤ I')
    (differentiable_within_at_prop I I') :=
{ is_local :=
  begin
    assume s x u f u_open xu,
    have : I.symm ⁻¹' (s ∩ u) ∩ set.range I = (I.symm ⁻¹' s ∩ set.range I) ∩ I.symm ⁻¹' u,
      by simp only [set.inter_right_comm, set.preimage_inter],
    rw [differentiable_within_at_prop, differentiable_within_at_prop, this],
    symmetry,
    apply differentiable_within_at_inter,
    have : u ∈ 𝓝 (I.symm (I x)),
      by { rw [model_with_corners.left_inv], exact is_open.mem_nhds u_open xu },
    apply continuous_at.preimage_mem_nhds I.continuous_symm.continuous_at this,
  end,
  right_invariance' :=
  begin
    assume s x f e he hx h,
    rw differentiable_within_at_prop at h ⊢,
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)), by simp only [hx] with mfld_simps,
    rw this at h,
    have : I (e x) ∈ (I.symm) ⁻¹' e.target ∩ set.range I, by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he).2.cont_diff_within_at this),
    convert (h.comp' _ (this.differentiable_within_at le_top)).mono_of_mem _ using 1,
    { ext y, simp only with mfld_simps },
    refine mem_nhds_within.mpr ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm,
      by simp_rw [set.mem_preimage, I.left_inv, e.maps_to hx], _⟩,
    mfld_set_tac
  end,
  congr_of_forall :=
  begin
    assume s x f g h hx hf,
    apply hf.congr,
    { assume y hy,
      simp only with mfld_simps at hy,
      simp only [h, hy] with mfld_simps },
    { simp only [hx] with mfld_simps }
  end,
  left_invariance' :=
  begin
    assume s x f e' he' hs hx h,
    rw differentiable_within_at_prop at h ⊢,
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ (I'.symm ⁻¹' e'.source ∩ set.range I'),
      by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he').1.cont_diff_within_at A),
    convert (this.differentiable_within_at le_top).comp _ h _,
    { ext y, simp only with mfld_simps },
    { assume y hy, simp only with mfld_simps at hy, simpa only [hy] with mfld_simps using hs hy.1 }
  end }

/-- Predicate ensuring that, at a point and within a set, a function can have at most one
derivative. This is expressed using the preferred chart at the considered point. -/
def unique_mdiff_within_at (s : set M) (x : M) :=
unique_diff_within_at 𝕜 ((ext_chart_at I x).symm ⁻¹' s ∩ range I) ((ext_chart_at I x) x)

/-- Predicate ensuring that, at all points of a set, a function can have at most one derivative. -/
def unique_mdiff_on (s : set M) :=
∀x∈s, unique_mdiff_within_at I s x

/-- `mdifferentiable_within_at I I' f s x` indicates that the function `f` between manifolds
has a derivative at the point `x` within the set `s`.
This is a generalization of `differentiable_within_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def mdifferentiable_within_at (f : M → M') (s : set M) (x : M) :=
continuous_within_at f s x ∧
differentiable_within_at 𝕜 (written_in_ext_chart_at I I' x f)
  ((ext_chart_at I x).symm ⁻¹' s ∩ range I) ((ext_chart_at I x) x)

lemma mdifferentiable_within_at_iff_lift_prop_within_at (f : M → M') (s : set M) (x : M) :
  mdifferentiable_within_at I I' f s x
  ↔ lift_prop_within_at (differentiable_within_at_prop I I') f s x :=
by refl

/-- `mdifferentiable_at I I' f x` indicates that the function `f` between manifolds
has a derivative at the point `x`.
This is a generalization of `differentiable_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def mdifferentiable_at (f : M → M') (x : M) :=
continuous_at f x ∧
differentiable_within_at 𝕜 (written_in_ext_chart_at I I' x f) (range I)
  ((ext_chart_at I x) x)

lemma mdifferentiable_at_iff_lift_prop_at (f : M → M') (x : M) :
  mdifferentiable_at I I' f x
  ↔ lift_prop_at (differentiable_within_at_prop I I') f x :=
begin
  congrm _ ∧ _,
  { rw continuous_within_at_univ },
  { simp [differentiable_within_at_prop, set.univ_inter] }
end

/-- `mdifferentiable_on I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `differentiable_on` to manifolds. -/
def mdifferentiable_on (f : M → M') (s : set M) :=
∀x ∈ s, mdifferentiable_within_at I I' f s x

/-- `mdifferentiable I I' f` indicates that the function `f` between manifolds
has a derivative everywhere.
This is a generalization of `differentiable` to manifolds. -/
def mdifferentiable (f : M → M') :=
∀x, mdifferentiable_at I I' f x

/-- Prop registering if a local homeomorphism is a local diffeomorphism on its source -/
def local_homeomorph.mdifferentiable (f : local_homeomorph M M') :=
(mdifferentiable_on I I' f f.source) ∧ (mdifferentiable_on I' I f.symm f.target)

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']

/-- `has_mfderiv_within_at I I' f s x f'` indicates that the function `f` between manifolds
has, at the point `x` and within the set `s`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

This is a generalization of `has_fderiv_within_at` to manifolds (as indicated by the prefix `m`).
The order of arguments is changed as the type of the derivative `f'` depends on the choice of `x`.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def has_mfderiv_within_at (f : M → M') (s : set M) (x : M)
  (f' : tangent_space I x →L[𝕜] tangent_space I' (f x)) :=
continuous_within_at f s x ∧
has_fderiv_within_at (written_in_ext_chart_at I I' x f : E → E') f'
  ((ext_chart_at I x).symm ⁻¹' s ∩ range I) ((ext_chart_at I x) x)

/-- `has_mfderiv_at I I' f x f'` indicates that the function `f` between manifolds
has, at the point `x`, the derivative `f'`. Here, `f'` is a continuous linear
map from the tangent space at `x` to the tangent space at `f x`.

We require continuity in the definition, as otherwise points close to `x` `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def has_mfderiv_at (f : M → M') (x : M)
  (f' : tangent_space I x →L[𝕜] tangent_space I' (f x)) :=
continuous_at f x ∧
has_fderiv_within_at (written_in_ext_chart_at I I' x f : E → E') f' (range I)
  ((ext_chart_at I x) x)

/-- Let `f` be a function between two smooth manifolds. Then `mfderiv_within I I' f s x` is the
derivative of `f` at `x` within `s`, as a continuous linear map from the tangent space at `x` to the
tangent space at `f x`. -/
def mfderiv_within (f : M → M') (s : set M) (x : M) :
  tangent_space I x →L[𝕜] tangent_space I' (f x) :=
if mdifferentiable_within_at I I' f s x then
(fderiv_within 𝕜 (written_in_ext_chart_at I I' x f) ((ext_chart_at I x).symm ⁻¹' s ∩ range I)
  ((ext_chart_at I x) x) : _)
else 0

/-- Let `f` be a function between two smooth manifolds. Then `mfderiv I I' f x` is the derivative of
`f` at `x`, as a continuous linear map from the tangent space at `x` to the tangent space at
`f x`. -/
def mfderiv (f : M → M') (x : M) : tangent_space I x →L[𝕜] tangent_space I' (f x) :=
if mdifferentiable_at I I' f x then
(fderiv_within 𝕜 (written_in_ext_chart_at I I' x f : E → E') (range I)
  ((ext_chart_at I x) x) : _)
else 0

/-- The derivative within a set, as a map between the tangent bundles -/
def tangent_map_within (f : M → M') (s : set M) : tangent_bundle I M → tangent_bundle I' M' :=
λp, ⟨f p.1, (mfderiv_within I I' f s p.1 : tangent_space I p.1 → tangent_space I' (f p.1)) p.2⟩

/-- The derivative, as a map between the tangent bundles -/
def tangent_map (f : M → M') : tangent_bundle I M → tangent_bundle I' M' :=
λp, ⟨f p.1, (mfderiv I I' f p.1 : tangent_space I p.1 → tangent_space I' (f p.1)) p.2⟩

end derivatives_definitions

section derivatives_properties
/-! ### Unique differentiability sets in manifolds -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] --
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M']
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']
{f f₀ f₁ : M → M'}
{x : M}
{s t : set M}
{g : M' → M''}
{u : set M'}

lemma unique_mdiff_within_at_univ : unique_mdiff_within_at I univ x :=
begin
  unfold unique_mdiff_within_at,
  simp only [preimage_univ, univ_inter],
  exact I.unique_diff _ (mem_range_self _)
end
variable {I}

lemma unique_mdiff_within_at_iff {s : set M} {x : M} :
  unique_mdiff_within_at I s x ↔
  unique_diff_within_at 𝕜 ((ext_chart_at I x).symm ⁻¹' s ∩ (ext_chart_at I x).target)
  ((ext_chart_at I x) x) :=
begin
  apply unique_diff_within_at_congr,
  rw [nhds_within_inter, nhds_within_inter, nhds_within_ext_chart_at_target_eq]
end

lemma unique_mdiff_within_at.mono (h : unique_mdiff_within_at I s x) (st : s ⊆ t) :
  unique_mdiff_within_at I t x :=
unique_diff_within_at.mono h $ inter_subset_inter (preimage_mono st) (subset.refl _)

lemma unique_mdiff_within_at.inter' (hs : unique_mdiff_within_at I s x) (ht : t ∈ 𝓝[s] x) :
  unique_mdiff_within_at I (s ∩ t) x :=
begin
  rw [unique_mdiff_within_at, ext_chart_at_preimage_inter_eq],
  exact unique_diff_within_at.inter' hs (ext_chart_at_preimage_mem_nhds_within I x ht)
end

lemma unique_mdiff_within_at.inter (hs : unique_mdiff_within_at I s x) (ht : t ∈ 𝓝 x) :
  unique_mdiff_within_at I (s ∩ t) x :=
begin
  rw [unique_mdiff_within_at, ext_chart_at_preimage_inter_eq],
  exact unique_diff_within_at.inter hs (ext_chart_at_preimage_mem_nhds I x ht)
end

lemma is_open.unique_mdiff_within_at (xs : x ∈ s) (hs : is_open s) : unique_mdiff_within_at I s x :=
begin
  have := unique_mdiff_within_at.inter (unique_mdiff_within_at_univ I) (is_open.mem_nhds hs xs),
  rwa univ_inter at this
end

lemma unique_mdiff_on.inter (hs : unique_mdiff_on I s) (ht : is_open t) :
  unique_mdiff_on I (s ∩ t) :=
λx hx, unique_mdiff_within_at.inter (hs _ hx.1) (is_open.mem_nhds ht hx.2)

lemma is_open.unique_mdiff_on (hs : is_open s) : unique_mdiff_on I s :=
λx hx, is_open.unique_mdiff_within_at hx hs

lemma unique_mdiff_on_univ : unique_mdiff_on I (univ : set M) :=
is_open_univ.unique_mdiff_on

/- We name the typeclass variables related to `smooth_manifold_with_corners` structure as they are
necessary in lemmas mentioning the derivative, but not in lemmas about differentiability, so we
want to include them or omit them when necessary. -/
variables [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M']
[I''s : smooth_manifold_with_corners I'' M'']
{f' f₀' f₁' : tangent_space I x →L[𝕜] tangent_space I' (f x)}
{g' : tangent_space I' (f x) →L[𝕜] tangent_space I'' (g (f x))}

/-- `unique_mdiff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem unique_mdiff_within_at.eq (U : unique_mdiff_within_at I s x)
  (h : has_mfderiv_within_at I I' f s x f') (h₁ : has_mfderiv_within_at I I' f s x f₁') :
  f' = f₁' :=
U.eq h.2 h₁.2

theorem unique_mdiff_on.eq (U : unique_mdiff_on I s) (hx : x ∈ s)
  (h : has_mfderiv_within_at I I' f s x f') (h₁ : has_mfderiv_within_at I I' f s x f₁') :
  f' = f₁' :=
unique_mdiff_within_at.eq (U _ hx) h h₁


/-!
### General lemmas on derivatives of functions between manifolds

We mimick the API for functions between vector spaces
-/

lemma mdifferentiable_within_at_iff {f : M → M'} {s : set M} {x : M} :
  mdifferentiable_within_at I I' f s x ↔
  continuous_within_at f s x ∧
  differentiable_within_at 𝕜 (written_in_ext_chart_at I I' x f)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' s) ((ext_chart_at I x) x) :=
begin
  refine and_congr iff.rfl (exists_congr $ λ f', _),
  rw [inter_comm],
  simp only [has_fderiv_within_at, nhds_within_inter, nhds_within_ext_chart_at_target_eq]
end

include Is I's

/-- One can reformulate differentiability within a set at a point as continuity within this set at
this point, and differentiability in any chart containing that point. -/
lemma mdifferentiable_within_at_iff_of_mem_source
  {x' : M} {y : M'}
  (hx : x' ∈ (charted_space.chart_at H x).source)
  (hy : f x' ∈ (charted_space.chart_at H' y).source) :
  mdifferentiable_within_at I I' f s x'
  ↔ continuous_within_at f s x'
    ∧ differentiable_within_at 𝕜
        ((ext_chart_at I' y) ∘ f ∘ ((ext_chart_at I x).symm))
        (((ext_chart_at I x).symm) ⁻¹' s ∩ set.range I)
        ((ext_chart_at I x) x') :=
(differentiable_within_at_local_invariant_prop I I').lift_prop_within_at_indep_chart
  (structure_groupoid.chart_mem_maximal_atlas _ x) hx
  (structure_groupoid.chart_mem_maximal_atlas _ y) hy

lemma mfderiv_within_zero_of_not_mdifferentiable_within_at
  (h : ¬ mdifferentiable_within_at I I' f s x) : mfderiv_within I I' f s x = 0 :=
by simp only [mfderiv_within, h, if_neg, not_false_iff]

lemma mfderiv_zero_of_not_mdifferentiable_at
  (h : ¬ mdifferentiable_at I I' f x) : mfderiv I I' f x = 0 :=
by simp only [mfderiv, h, if_neg, not_false_iff]

theorem has_mfderiv_within_at.mono (h : has_mfderiv_within_at I I' f t x f') (hst : s ⊆ t) :
  has_mfderiv_within_at I I' f s x f' :=
⟨ continuous_within_at.mono h.1 hst,
  has_fderiv_within_at.mono h.2 (inter_subset_inter (preimage_mono hst) (subset.refl _)) ⟩

theorem has_mfderiv_at.has_mfderiv_within_at
  (h : has_mfderiv_at I I' f x f') : has_mfderiv_within_at I I' f s x f' :=
⟨ continuous_at.continuous_within_at h.1, has_fderiv_within_at.mono h.2 (inter_subset_right _ _) ⟩

lemma has_mfderiv_within_at.mdifferentiable_within_at (h : has_mfderiv_within_at I I' f s x f') :
  mdifferentiable_within_at I I' f s x :=
⟨h.1, ⟨f', h.2⟩⟩

lemma has_mfderiv_at.mdifferentiable_at (h : has_mfderiv_at I I' f x f') :
  mdifferentiable_at I I' f x :=
⟨h.1, ⟨f', h.2⟩⟩

@[simp, mfld_simps] lemma has_mfderiv_within_at_univ :
  has_mfderiv_within_at I I' f univ x f' ↔ has_mfderiv_at I I' f x f' :=
by simp only [has_mfderiv_within_at, has_mfderiv_at, continuous_within_at_univ] with mfld_simps

theorem has_mfderiv_at_unique
  (h₀ : has_mfderiv_at I I' f x f₀') (h₁ : has_mfderiv_at I I' f x f₁') : f₀' = f₁' :=
begin
  rw ← has_mfderiv_within_at_univ at h₀ h₁,
  exact (unique_mdiff_within_at_univ I).eq h₀ h₁
end

lemma has_mfderiv_within_at_inter' (h : t ∈ 𝓝[s] x) :
  has_mfderiv_within_at I I' f (s ∩ t) x f' ↔ has_mfderiv_within_at I I' f s x f' :=
begin
  rw [has_mfderiv_within_at, has_mfderiv_within_at, ext_chart_at_preimage_inter_eq,
      has_fderiv_within_at_inter', continuous_within_at_inter' h],
  exact ext_chart_at_preimage_mem_nhds_within I x h,
end

lemma has_mfderiv_within_at_inter (h : t ∈ 𝓝 x) :
  has_mfderiv_within_at I I' f (s ∩ t) x f' ↔ has_mfderiv_within_at I I' f s x f' :=
begin
  rw [has_mfderiv_within_at, has_mfderiv_within_at, ext_chart_at_preimage_inter_eq,
      has_fderiv_within_at_inter, continuous_within_at_inter h],
  exact ext_chart_at_preimage_mem_nhds I x h,
end

lemma has_mfderiv_within_at.union
  (hs : has_mfderiv_within_at I I' f s x f') (ht : has_mfderiv_within_at I I' f t x f') :
  has_mfderiv_within_at I I' f (s ∪ t) x f' :=
begin
  split,
  { exact continuous_within_at.union hs.1 ht.1 },
  { convert has_fderiv_within_at.union hs.2 ht.2,
    simp only [union_inter_distrib_right, preimage_union] }
end

lemma has_mfderiv_within_at.nhds_within (h : has_mfderiv_within_at I I' f s x f')
  (ht : s ∈ 𝓝[t] x) : has_mfderiv_within_at I I' f t x f' :=
(has_mfderiv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))

lemma has_mfderiv_within_at.has_mfderiv_at (h : has_mfderiv_within_at I I' f s x f')
  (hs : s ∈ 𝓝 x) :
  has_mfderiv_at I I' f x f' :=
by rwa [← univ_inter s, has_mfderiv_within_at_inter hs, has_mfderiv_within_at_univ] at h

lemma mdifferentiable_within_at.has_mfderiv_within_at (h : mdifferentiable_within_at I I' f s x) :
  has_mfderiv_within_at I I' f s x (mfderiv_within I I' f s x) :=
begin
  refine ⟨h.1, _⟩,
  simp only [mfderiv_within, h, if_pos] with mfld_simps,
  exact differentiable_within_at.has_fderiv_within_at h.2
end

lemma mdifferentiable_within_at.mfderiv_within (h : mdifferentiable_within_at I I' f s x) :
  (mfderiv_within I I' f s x) =
  fderiv_within 𝕜 (written_in_ext_chart_at I I' x f : _) ((ext_chart_at I x).symm ⁻¹' s ∩ range I)
  ((ext_chart_at I x) x) :=
by simp only [mfderiv_within, h, if_pos]

lemma mdifferentiable_at.has_mfderiv_at (h : mdifferentiable_at I I' f x) :
  has_mfderiv_at I I' f x (mfderiv I I' f x) :=
begin
  refine ⟨h.1, _⟩,
  simp only [mfderiv, h, if_pos] with mfld_simps,
  exact differentiable_within_at.has_fderiv_within_at h.2
end

lemma mdifferentiable_at.mfderiv (h : mdifferentiable_at I I' f x) :
  (mfderiv I I' f x) =
  fderiv_within 𝕜 (written_in_ext_chart_at I I' x f : _) (range I) ((ext_chart_at I x) x) :=
by simp only [mfderiv, h, if_pos]

lemma has_mfderiv_at.mfderiv (h : has_mfderiv_at I I' f x f') :
  mfderiv I I' f x = f' :=
(has_mfderiv_at_unique h h.mdifferentiable_at.has_mfderiv_at).symm

lemma has_mfderiv_within_at.mfderiv_within
  (h : has_mfderiv_within_at I I' f s x f') (hxs : unique_mdiff_within_at I s x) :
  mfderiv_within I I' f s x = f' :=
by { ext, rw hxs.eq h h.mdifferentiable_within_at.has_mfderiv_within_at }

lemma mdifferentiable.mfderiv_within
  (h : mdifferentiable_at I I' f x) (hxs : unique_mdiff_within_at I s x) :
  mfderiv_within I I' f s x = mfderiv I I' f x :=
begin
  apply has_mfderiv_within_at.mfderiv_within _ hxs,
  exact h.has_mfderiv_at.has_mfderiv_within_at
end

lemma mfderiv_within_subset (st : s ⊆ t) (hs : unique_mdiff_within_at I s x)
  (h : mdifferentiable_within_at I I' f t x) :
  mfderiv_within I I' f s x = mfderiv_within I I' f t x :=
((mdifferentiable_within_at.has_mfderiv_within_at h).mono st).mfderiv_within hs

omit Is I's

lemma mdifferentiable_within_at.mono (hst : s ⊆ t)
  (h : mdifferentiable_within_at I I' f t x) : mdifferentiable_within_at I I' f s x :=
⟨ continuous_within_at.mono h.1 hst,
  differentiable_within_at.mono h.2 (inter_subset_inter (preimage_mono hst) (subset.refl _)) ⟩

lemma mdifferentiable_within_at_univ :
  mdifferentiable_within_at I I' f univ x ↔ mdifferentiable_at I I' f x :=
by simp only [mdifferentiable_within_at, mdifferentiable_at, continuous_within_at_univ]
  with mfld_simps

lemma mdifferentiable_within_at_inter (ht : t ∈ 𝓝 x) :
  mdifferentiable_within_at I I' f (s ∩ t) x ↔ mdifferentiable_within_at I I' f s x :=
begin
  rw [mdifferentiable_within_at, mdifferentiable_within_at, ext_chart_at_preimage_inter_eq,
      differentiable_within_at_inter, continuous_within_at_inter ht],
  exact ext_chart_at_preimage_mem_nhds I x ht
end

lemma mdifferentiable_within_at_inter' (ht : t ∈ 𝓝[s] x) :
  mdifferentiable_within_at I I' f (s ∩ t) x ↔ mdifferentiable_within_at I I' f s x :=
begin
  rw [mdifferentiable_within_at, mdifferentiable_within_at, ext_chart_at_preimage_inter_eq,
      differentiable_within_at_inter', continuous_within_at_inter' ht],
  exact ext_chart_at_preimage_mem_nhds_within I x ht
end

lemma mdifferentiable_at.mdifferentiable_within_at
  (h : mdifferentiable_at I I' f x) : mdifferentiable_within_at I I' f s x :=
mdifferentiable_within_at.mono (subset_univ _) (mdifferentiable_within_at_univ.2 h)

lemma mdifferentiable_within_at.mdifferentiable_at
  (h : mdifferentiable_within_at I I' f s x) (hs : s ∈ 𝓝 x) : mdifferentiable_at I I' f x :=
begin
  have : s = univ ∩ s, by rw univ_inter,
  rwa [this, mdifferentiable_within_at_inter hs, mdifferentiable_within_at_univ] at h,
end

lemma mdifferentiable_on.mono
  (h : mdifferentiable_on I I' f t) (st : s ⊆ t) : mdifferentiable_on I I' f s :=
λx hx, (h x (st hx)).mono st

lemma mdifferentiable_on_univ :
  mdifferentiable_on I I' f univ ↔ mdifferentiable I I' f :=
by { simp only [mdifferentiable_on, mdifferentiable_within_at_univ] with mfld_simps, refl }

lemma mdifferentiable.mdifferentiable_on
  (h : mdifferentiable I I' f) : mdifferentiable_on I I' f s :=
(mdifferentiable_on_univ.2 h).mono (subset_univ _)

lemma mdifferentiable_on_of_locally_mdifferentiable_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ mdifferentiable_on I I' f (s ∩ u)) :
  mdifferentiable_on I I' f s :=
begin
  assume x xs,
  rcases h x xs with ⟨t, t_open, xt, ht⟩,
  exact (mdifferentiable_within_at_inter (is_open.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
end

include Is I's
@[simp, mfld_simps] lemma mfderiv_within_univ : mfderiv_within I I' f univ = mfderiv I I' f :=
begin
  ext x : 1,
  simp only [mfderiv_within, mfderiv] with mfld_simps,
  rw mdifferentiable_within_at_univ
end

lemma mfderiv_within_inter (ht : t ∈ 𝓝 x) (hs : unique_mdiff_within_at I s x) :
  mfderiv_within I I' f (s ∩ t) x = mfderiv_within I I' f s x :=
by rw [mfderiv_within, mfderiv_within, ext_chart_at_preimage_inter_eq,
  mdifferentiable_within_at_inter ht,
  fderiv_within_inter (ext_chart_at_preimage_mem_nhds I x ht) hs]

lemma mdifferentiable_at_iff_of_mem_source {x' : M} {y : M'}
  (hx : x' ∈ (charted_space.chart_at H x).source)
  (hy : f x' ∈ (charted_space.chart_at H' y).source) :
  mdifferentiable_at I I' f x'
  ↔ continuous_at f x'
    ∧ differentiable_within_at 𝕜
        ((ext_chart_at I' y) ∘ f ∘ ((ext_chart_at I x).symm))
        (set.range I)
        ((ext_chart_at I x) x') :=
mdifferentiable_within_at_univ.symm.trans $
  (mdifferentiable_within_at_iff_of_mem_source hx hy).trans $
  by rw [continuous_within_at_univ, set.preimage_univ, set.univ_inter]

omit Is I's

/-! ### Deriving continuity from differentiability on manifolds -/

theorem has_mfderiv_within_at.continuous_within_at
  (h : has_mfderiv_within_at I I' f s x f') : continuous_within_at f s x :=
h.1

theorem has_mfderiv_at.continuous_at (h : has_mfderiv_at I I' f x f') :
  continuous_at f x :=
h.1

lemma mdifferentiable_within_at.continuous_within_at (h : mdifferentiable_within_at I I' f s x) :
  continuous_within_at f s x :=
h.1

lemma mdifferentiable_at.continuous_at (h : mdifferentiable_at I I' f x) : continuous_at f x :=
h.1

lemma mdifferentiable_on.continuous_on (h : mdifferentiable_on I I' f s) : continuous_on f s :=
λx hx, (h x hx).continuous_within_at

lemma mdifferentiable.continuous (h : mdifferentiable I I' f) : continuous f :=
continuous_iff_continuous_at.2 $ λx, (h x).continuous_at

include Is I's
lemma tangent_map_within_subset {p : tangent_bundle I M}
  (st : s ⊆ t) (hs : unique_mdiff_within_at I s p.1) (h : mdifferentiable_within_at I I' f t p.1) :
  tangent_map_within I I' f s p = tangent_map_within I I' f t p :=
begin
  simp only [tangent_map_within] with mfld_simps,
  rw mfderiv_within_subset st hs h,
end

lemma tangent_map_within_univ :
  tangent_map_within I I' f univ = tangent_map I I' f :=
by { ext p : 1, simp only [tangent_map_within, tangent_map] with mfld_simps }

lemma tangent_map_within_eq_tangent_map {p : tangent_bundle I M}
  (hs : unique_mdiff_within_at I s p.1) (h : mdifferentiable_at I I' f p.1) :
  tangent_map_within I I' f s p = tangent_map I I' f p :=
begin
  rw ← mdifferentiable_within_at_univ at h,
  rw ← tangent_map_within_univ,
  exact tangent_map_within_subset (subset_univ _) hs h,
end

@[simp, mfld_simps] lemma tangent_map_within_tangent_bundle_proj {p : tangent_bundle I M} :
  tangent_bundle.proj I' M' (tangent_map_within I I' f s p) = f (tangent_bundle.proj I M p) := rfl

@[simp, mfld_simps] lemma tangent_map_within_proj {p : tangent_bundle I M} :
  (tangent_map_within I I' f s p).1 = f p.1 := rfl

@[simp, mfld_simps] lemma tangent_map_tangent_bundle_proj {p : tangent_bundle I M} :
  tangent_bundle.proj I' M' (tangent_map I I' f p) = f (tangent_bundle.proj I M p) := rfl

@[simp, mfld_simps] lemma tangent_map_proj {p : tangent_bundle I M} :
  (tangent_map I I' f p).1 = f p.1 := rfl

omit Is I's

/-! ### Congruence lemmas for derivatives on manifolds -/

lemma has_mfderiv_within_at.congr_of_eventually_eq (h : has_mfderiv_within_at I I' f s x f')
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : has_mfderiv_within_at I I' f₁ s x f' :=
begin
  refine ⟨continuous_within_at.congr_of_eventually_eq h.1 h₁ hx, _⟩,
  apply has_fderiv_within_at.congr_of_eventually_eq h.2,
  { have : (ext_chart_at I x).symm ⁻¹' {y | f₁ y = f y} ∈
      𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] ((ext_chart_at I x) x)  :=
      ext_chart_at_preimage_mem_nhds_within I x h₁,
    apply filter.mem_of_superset this (λy, _),
    simp only [hx] with mfld_simps {contextual := tt} },
  { simp only [hx] with mfld_simps },
end

lemma has_mfderiv_within_at.congr_mono (h : has_mfderiv_within_at I I' f s x f')
  (ht : ∀x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
  has_mfderiv_within_at I I' f₁ t x f' :=
(h.mono h₁).congr_of_eventually_eq (filter.mem_inf_of_right ht) hx

lemma has_mfderiv_at.congr_of_eventually_eq (h : has_mfderiv_at I I' f x f')
  (h₁ : f₁ =ᶠ[𝓝 x] f) : has_mfderiv_at I I' f₁ x f' :=
begin
  rw ← has_mfderiv_within_at_univ at ⊢ h,
  apply h.congr_of_eventually_eq _ (mem_of_mem_nhds h₁ : _),
  rwa nhds_within_univ
end

include Is I's

lemma mdifferentiable_within_at.congr_of_eventually_eq
  (h : mdifferentiable_within_at I I' f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
  (hx : f₁ x = f x) : mdifferentiable_within_at I I' f₁ s x :=
(h.has_mfderiv_within_at.congr_of_eventually_eq h₁ hx).mdifferentiable_within_at

variables (I I')
lemma filter.eventually_eq.mdifferentiable_within_at_iff
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  mdifferentiable_within_at I I' f s x ↔ mdifferentiable_within_at I I' f₁ s x :=
begin
  split,
  { assume h,
    apply h.congr_of_eventually_eq h₁ hx },
  { assume h,
    apply h.congr_of_eventually_eq _ hx.symm,
    apply h₁.mono,
    intro y,
    apply eq.symm }
end
variables {I I'}

lemma mdifferentiable_within_at.congr_mono (h : mdifferentiable_within_at I I' f s x)
  (ht : ∀x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
  mdifferentiable_within_at I I' f₁ t x :=
(has_mfderiv_within_at.congr_mono h.has_mfderiv_within_at ht hx h₁).mdifferentiable_within_at

lemma mdifferentiable_within_at.congr (h : mdifferentiable_within_at I I' f s x)
  (ht : ∀x ∈ s, f₁ x = f x) (hx : f₁ x = f x) : mdifferentiable_within_at I I' f₁ s x :=
(has_mfderiv_within_at.congr_mono h.has_mfderiv_within_at ht hx
  (subset.refl _)).mdifferentiable_within_at

lemma mdifferentiable_on.congr_mono (h : mdifferentiable_on I I' f s) (h' : ∀x ∈ t, f₁ x = f x)
  (h₁ : t ⊆ s) : mdifferentiable_on I I' f₁ t :=
λ x hx, (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

lemma mdifferentiable_at.congr_of_eventually_eq (h : mdifferentiable_at I I' f x)
  (hL : f₁ =ᶠ[𝓝 x] f) : mdifferentiable_at I I' f₁ x :=
((h.has_mfderiv_at).congr_of_eventually_eq hL).mdifferentiable_at

lemma mdifferentiable_within_at.mfderiv_within_congr_mono (h : mdifferentiable_within_at I I' f s x)
  (hs : ∀x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : unique_mdiff_within_at I t x) (h₁ : t ⊆ s) :
  mfderiv_within I I' f₁ t x = (mfderiv_within I I' f s x : _) :=
(has_mfderiv_within_at.congr_mono h.has_mfderiv_within_at hs hx h₁).mfderiv_within hxt

lemma filter.eventually_eq.mfderiv_within_eq (hs : unique_mdiff_within_at I s x)
  (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  mfderiv_within I I' f₁ s x = (mfderiv_within I I' f s x : _) :=
begin
  by_cases h : mdifferentiable_within_at I I' f s x,
  { exact ((h.has_mfderiv_within_at).congr_of_eventually_eq hL hx).mfderiv_within hs },
  { unfold mfderiv_within,
    rw [if_neg h, if_neg],
    rwa ← hL.mdifferentiable_within_at_iff I I' hx }
end

lemma mfderiv_within_congr (hs : unique_mdiff_within_at I s x)
  (hL : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) :
  mfderiv_within I I' f₁ s x = (mfderiv_within I I' f s x : _) :=
filter.eventually_eq.mfderiv_within_eq hs (filter.eventually_eq_of_mem (self_mem_nhds_within) hL) hx

lemma tangent_map_within_congr (h : ∀ x ∈ s, f x = f₁ x)
  (p : tangent_bundle I M) (hp : p.1 ∈ s) (hs : unique_mdiff_within_at I s p.1) :
  tangent_map_within I I' f s p = tangent_map_within I I' f₁ s p :=
begin
  simp only [tangent_map_within, h p.fst hp, true_and, eq_self_iff_true, heq_iff_eq,
    sigma.mk.inj_iff],
  congr' 1,
  exact mfderiv_within_congr hs h (h _ hp)
end

lemma filter.eventually_eq.mfderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) :
  mfderiv I I' f₁ x = (mfderiv I I' f x : _) :=
begin
  have A : f₁ x = f x := (mem_of_mem_nhds hL : _),
  rw [← mfderiv_within_univ, ← mfderiv_within_univ],
  rw ← nhds_within_univ at hL,
  exact hL.mfderiv_within_eq (unique_mdiff_within_at_univ I) A
end

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
lemma mfderiv_congr_point {x' : M} (h : x = x') :
  @eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f x') :=
by subst h

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `tangent_space I' (f x)` is
definitionally equal to `E'`. -/
lemma mfderiv_congr {f' : M → M'} (h : f = f') :
  @eq (E →L[𝕜] E') (mfderiv I I' f x) (mfderiv I I' f' x) :=
by subst h

/-! ### Composition lemmas -/

omit Is I's

lemma written_in_ext_chart_comp (h : continuous_within_at f s x) :
  {y | written_in_ext_chart_at I I'' x (g ∘ f) y
       = ((written_in_ext_chart_at I' I'' (f x) g) ∘ (written_in_ext_chart_at I I' x f)) y}
  ∈ 𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] ((ext_chart_at I x) x)  :=
begin
  apply @filter.mem_of_superset _ _
    ((f ∘ (ext_chart_at I x).symm)⁻¹' (ext_chart_at I' (f x)).source) _
    (ext_chart_at_preimage_mem_nhds_within I x
      (h.preimage_mem_nhds_within (ext_chart_at_source_mem_nhds _ _))),
  mfld_set_tac,
end

variable (x)
include Is I's I''s

theorem has_mfderiv_within_at.comp
  (hg : has_mfderiv_within_at I' I'' g u (f x) g') (hf : has_mfderiv_within_at I I' f s x f')
  (hst : s ⊆ f ⁻¹' u) :
  has_mfderiv_within_at I I'' (g ∘ f) s x (g'.comp f') :=
begin
  refine ⟨continuous_within_at.comp hg.1 hf.1 hst, _⟩,
  have A : has_fderiv_within_at ((written_in_ext_chart_at I' I'' (f x) g) ∘
       (written_in_ext_chart_at I I' x f))
    (continuous_linear_map.comp g' f' : E →L[𝕜] E'')
    ((ext_chart_at I x).symm ⁻¹' s ∩ range (I))
    ((ext_chart_at I x) x),
  { have : (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' (f x)).source)
    ∈ 𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] ((ext_chart_at I x) x)  :=
      (ext_chart_at_preimage_mem_nhds_within I x
        (hf.1.preimage_mem_nhds_within (ext_chart_at_source_mem_nhds _ _))),
    unfold has_mfderiv_within_at at *,
    rw [← has_fderiv_within_at_inter' this, ← ext_chart_at_preimage_inter_eq] at hf ⊢,
    have : written_in_ext_chart_at I I' x f ((ext_chart_at I x) x)
        = (ext_chart_at I' (f x)) (f x),
      by simp only with mfld_simps,
    rw ← this at hg,
    apply has_fderiv_within_at.comp ((ext_chart_at I x) x) hg.2 hf.2 _,
    assume y hy,
    simp only with mfld_simps at hy,
    have : f (((chart_at H x).symm : H → M) (I.symm y)) ∈ u := hst hy.1.1,
    simp only [hy, this] with mfld_simps },
  apply A.congr_of_eventually_eq (written_in_ext_chart_comp hf.1),
  simp only with mfld_simps
end

/-- The chain rule. -/
theorem has_mfderiv_at.comp
  (hg : has_mfderiv_at I' I'' g (f x) g') (hf : has_mfderiv_at I I' f x f') :
  has_mfderiv_at I I'' (g ∘ f) x (g'.comp f') :=
begin
  rw ← has_mfderiv_within_at_univ at *,
  exact has_mfderiv_within_at.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
end

theorem has_mfderiv_at.comp_has_mfderiv_within_at
  (hg : has_mfderiv_at I' I'' g (f x) g') (hf : has_mfderiv_within_at I I' f s x f') :
  has_mfderiv_within_at I I'' (g ∘ f) s x (g'.comp f') :=
begin
  rw ← has_mfderiv_within_at_univ at *,
  exact has_mfderiv_within_at.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
end

lemma mdifferentiable_within_at.comp
  (hg : mdifferentiable_within_at I' I'' g u (f x)) (hf : mdifferentiable_within_at I I' f s x)
  (h : s ⊆ f ⁻¹' u) : mdifferentiable_within_at I I'' (g ∘ f) s x :=
begin
  rcases hf.2 with ⟨f', hf'⟩,
  have F : has_mfderiv_within_at I I' f s x f' := ⟨hf.1, hf'⟩,
  rcases hg.2 with ⟨g', hg'⟩,
  have G : has_mfderiv_within_at I' I'' g u (f x) g' := ⟨hg.1, hg'⟩,
  exact (has_mfderiv_within_at.comp x G F h).mdifferentiable_within_at
end

lemma mdifferentiable_at.comp
  (hg : mdifferentiable_at I' I'' g (f x)) (hf : mdifferentiable_at I I' f x) :
  mdifferentiable_at I I'' (g ∘ f) x :=
(hg.has_mfderiv_at.comp x hf.has_mfderiv_at).mdifferentiable_at

lemma mfderiv_within_comp
  (hg : mdifferentiable_within_at I' I'' g u (f x)) (hf : mdifferentiable_within_at I I' f s x)
  (h : s ⊆ f ⁻¹' u) (hxs : unique_mdiff_within_at I s x) :
  mfderiv_within I I'' (g ∘ f) s x =
    (mfderiv_within I' I'' g u (f x)).comp (mfderiv_within I I' f s x) :=
begin
  apply has_mfderiv_within_at.mfderiv_within _ hxs,
  exact has_mfderiv_within_at.comp x hg.has_mfderiv_within_at hf.has_mfderiv_within_at h
end

lemma mfderiv_comp
  (hg : mdifferentiable_at I' I'' g (f x)) (hf : mdifferentiable_at I I' f x) :
  mfderiv I I'' (g ∘ f) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) :=
begin
  apply has_mfderiv_at.mfderiv,
  exact has_mfderiv_at.comp x hg.has_mfderiv_at hf.has_mfderiv_at
end

lemma mdifferentiable_on.comp
  (hg : mdifferentiable_on I' I'' g u) (hf : mdifferentiable_on I I' f s) (st : s ⊆ f ⁻¹' u) :
  mdifferentiable_on I I'' (g ∘ f) s :=
λx hx, mdifferentiable_within_at.comp x (hg (f x) (st hx)) (hf x hx) st

lemma mdifferentiable.comp
  (hg : mdifferentiable I' I'' g) (hf : mdifferentiable I I' f) : mdifferentiable I I'' (g ∘ f) :=
λx, mdifferentiable_at.comp x (hg (f x)) (hf x)

lemma tangent_map_within_comp_at (p : tangent_bundle I M)
  (hg : mdifferentiable_within_at I' I'' g u (f p.1)) (hf : mdifferentiable_within_at I I' f s p.1)
  (h : s ⊆ f ⁻¹' u)  (hps : unique_mdiff_within_at I s p.1) :
  tangent_map_within I I'' (g ∘ f) s p =
  tangent_map_within I' I'' g u (tangent_map_within I I' f s p) :=
begin
  simp only [tangent_map_within] with mfld_simps,
  rw mfderiv_within_comp p.1 hg hf h hps,
  refl
end

lemma tangent_map_comp_at (p : tangent_bundle I M)
  (hg : mdifferentiable_at I' I'' g (f p.1)) (hf : mdifferentiable_at I I' f p.1) :
  tangent_map I I'' (g ∘ f) p = tangent_map I' I'' g (tangent_map I I' f p) :=
begin
  simp only [tangent_map] with mfld_simps,
  rw mfderiv_comp p.1 hg hf,
  refl
end

lemma tangent_map_comp (hg : mdifferentiable I' I'' g) (hf : mdifferentiable I I' f) :
  tangent_map I I'' (g ∘ f) = (tangent_map I' I'' g) ∘ (tangent_map I I' f) :=
by { ext p : 1, exact tangent_map_comp_at _ (hg _) (hf _) }

end derivatives_properties

section mfderiv_fderiv

/-!
### Relations between vector space derivative and manifold derivative

The manifold derivative `mfderiv`, when considered on the model vector space with its trivial
manifold structure, coincides with the usual Frechet derivative `fderiv`. In this section, we prove
this and related statements.
-/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{f : E → E'} {s : set E} {x : E}

lemma unique_mdiff_within_at_iff_unique_diff_within_at :
  unique_mdiff_within_at (𝓘(𝕜, E)) s x ↔ unique_diff_within_at 𝕜 s x :=
by simp only [unique_mdiff_within_at] with mfld_simps

alias unique_mdiff_within_at_iff_unique_diff_within_at ↔
  unique_mdiff_within_at.unique_diff_within_at unique_diff_within_at.unique_mdiff_within_at

lemma unique_mdiff_on_iff_unique_diff_on :
  unique_mdiff_on (𝓘(𝕜, E)) s ↔ unique_diff_on 𝕜 s :=
by simp [unique_mdiff_on, unique_diff_on, unique_mdiff_within_at_iff_unique_diff_within_at]

alias unique_mdiff_on_iff_unique_diff_on ↔
  unique_mdiff_on.unique_diff_on unique_diff_on.unique_mdiff_on

@[simp, mfld_simps] lemma written_in_ext_chart_model_space :
  written_in_ext_chart_at (𝓘(𝕜, E)) (𝓘(𝕜, E')) x f = f :=
rfl

lemma has_mfderiv_within_at_iff_has_fderiv_within_at {f'} :
  has_mfderiv_within_at 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f' ↔
    has_fderiv_within_at f f' s x :=
by simpa only [has_mfderiv_within_at, and_iff_right_iff_imp] with mfld_simps
  using has_fderiv_within_at.continuous_within_at

alias has_mfderiv_within_at_iff_has_fderiv_within_at ↔
  has_mfderiv_within_at.has_fderiv_within_at has_fderiv_within_at.has_mfderiv_within_at

lemma has_mfderiv_at_iff_has_fderiv_at {f'} :
  has_mfderiv_at 𝓘(𝕜, E) 𝓘(𝕜, E') f x f' ↔ has_fderiv_at f f' x :=
by rw [← has_mfderiv_within_at_univ, has_mfderiv_within_at_iff_has_fderiv_within_at,
  has_fderiv_within_at_univ]

alias has_mfderiv_at_iff_has_fderiv_at ↔ has_mfderiv_at.has_fderiv_at has_fderiv_at.has_mfderiv_at

/-- For maps between vector spaces, `mdifferentiable_within_at` and `fdifferentiable_within_at`
coincide -/
theorem mdifferentiable_within_at_iff_differentiable_within_at :
  mdifferentiable_within_at (𝓘(𝕜, E)) (𝓘(𝕜, E')) f s x
  ↔ differentiable_within_at 𝕜 f s x :=
begin
  simp only [mdifferentiable_within_at] with mfld_simps,
  exact ⟨λH, H.2, λH, ⟨H.continuous_within_at, H⟩⟩
end

alias mdifferentiable_within_at_iff_differentiable_within_at ↔
  mdifferentiable_within_at.differentiable_within_at
  differentiable_within_at.mdifferentiable_within_at

/-- For maps between vector spaces, `mdifferentiable_at` and `differentiable_at` coincide -/
theorem mdifferentiable_at_iff_differentiable_at :
  mdifferentiable_at (𝓘(𝕜, E)) (𝓘(𝕜, E')) f x ↔ differentiable_at 𝕜 f x :=
begin
  simp only [mdifferentiable_at, differentiable_within_at_univ] with mfld_simps,
  exact ⟨λH, H.2, λH, ⟨H.continuous_at, H⟩⟩
end

alias mdifferentiable_at_iff_differentiable_at ↔
  mdifferentiable_at.differentiable_at differentiable_at.mdifferentiable_at

/-- For maps between vector spaces, `mdifferentiable_on` and `differentiable_on` coincide -/
theorem mdifferentiable_on_iff_differentiable_on :
  mdifferentiable_on (𝓘(𝕜, E)) (𝓘(𝕜, E')) f s ↔ differentiable_on 𝕜 f s :=
by simp only [mdifferentiable_on, differentiable_on,
              mdifferentiable_within_at_iff_differentiable_within_at]

alias mdifferentiable_on_iff_differentiable_on ↔
  mdifferentiable_on.differentiable_on differentiable_on.mdifferentiable_on

/-- For maps between vector spaces, `mdifferentiable` and `differentiable` coincide -/
theorem mdifferentiable_iff_differentiable :
  mdifferentiable (𝓘(𝕜, E)) (𝓘(𝕜, E')) f ↔ differentiable 𝕜 f :=
by simp only [mdifferentiable, differentiable, mdifferentiable_at_iff_differentiable_at]

alias mdifferentiable_iff_differentiable ↔
  mdifferentiable.differentiable differentiable.mdifferentiable

/-- For maps between vector spaces, `mfderiv_within` and `fderiv_within` coincide -/
@[simp] theorem mfderiv_within_eq_fderiv_within :
  mfderiv_within (𝓘(𝕜, E)) (𝓘(𝕜, E')) f s x = fderiv_within 𝕜 f s x :=
begin
  by_cases h : mdifferentiable_within_at (𝓘(𝕜, E)) (𝓘(𝕜, E')) f s x,
  { simp only [mfderiv_within, h, if_pos] with mfld_simps },
  { simp only [mfderiv_within, h, if_neg, not_false_iff],
    rw [mdifferentiable_within_at_iff_differentiable_within_at] at h,
    exact (fderiv_within_zero_of_not_differentiable_within_at h).symm }
end

/-- For maps between vector spaces, `mfderiv` and `fderiv` coincide -/
@[simp] theorem mfderiv_eq_fderiv :
  mfderiv (𝓘(𝕜, E)) (𝓘(𝕜, E')) f x = fderiv 𝕜 f x :=
begin
  rw [← mfderiv_within_univ, ← fderiv_within_univ],
  exact mfderiv_within_eq_fderiv_within
end

end mfderiv_fderiv

section specific_functions

/-! ### Differentiability of specific functions -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

namespace continuous_linear_map

variables (f : E →L[𝕜] E') {s : set E} {x : E}

protected lemma has_mfderiv_within_at : has_mfderiv_within_at 𝓘(𝕜, E) 𝓘(𝕜, E') f s x f :=
f.has_fderiv_within_at.has_mfderiv_within_at

protected lemma has_mfderiv_at : has_mfderiv_at 𝓘(𝕜, E) 𝓘(𝕜, E') f x f :=
f.has_fderiv_at.has_mfderiv_at

protected lemma mdifferentiable_within_at : mdifferentiable_within_at 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
f.differentiable_within_at.mdifferentiable_within_at

protected lemma mdifferentiable_on : mdifferentiable_on 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
f.differentiable_on.mdifferentiable_on

protected lemma mdifferentiable_at : mdifferentiable_at 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
f.differentiable_at.mdifferentiable_at

protected lemma mdifferentiable : mdifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
f.differentiable.mdifferentiable

lemma mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = f :=
f.has_mfderiv_at.mfderiv

lemma mfderiv_within_eq (hs : unique_mdiff_within_at 𝓘(𝕜, E) s x)  :
  mfderiv_within 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = f :=
f.has_mfderiv_within_at.mfderiv_within hs

end continuous_linear_map

namespace continuous_linear_equiv

variables (f : E ≃L[𝕜] E') {s : set E} {x : E}

protected lemma has_mfderiv_within_at :
  has_mfderiv_within_at 𝓘(𝕜, E) 𝓘(𝕜, E') f s x (f : E →L[𝕜] E') :=
f.has_fderiv_within_at.has_mfderiv_within_at

protected lemma has_mfderiv_at : has_mfderiv_at 𝓘(𝕜, E) 𝓘(𝕜, E') f x (f : E →L[𝕜] E') :=
f.has_fderiv_at.has_mfderiv_at

protected lemma mdifferentiable_within_at : mdifferentiable_within_at 𝓘(𝕜, E) 𝓘(𝕜, E') f s x :=
f.differentiable_within_at.mdifferentiable_within_at

protected lemma mdifferentiable_on : mdifferentiable_on 𝓘(𝕜, E) 𝓘(𝕜, E') f s :=
f.differentiable_on.mdifferentiable_on

protected lemma mdifferentiable_at : mdifferentiable_at 𝓘(𝕜, E) 𝓘(𝕜, E') f x :=
f.differentiable_at.mdifferentiable_at

protected lemma mdifferentiable : mdifferentiable 𝓘(𝕜, E) 𝓘(𝕜, E') f :=
f.differentiable.mdifferentiable

lemma mfderiv_eq : mfderiv 𝓘(𝕜, E) 𝓘(𝕜, E') f x = (f : E →L[𝕜] E') :=
f.has_mfderiv_at.mfderiv

lemma mfderiv_within_eq (hs : unique_mdiff_within_at 𝓘(𝕜, E) s x)  :
  mfderiv_within 𝓘(𝕜, E) 𝓘(𝕜, E') f s x = (f : E →L[𝕜] E') :=
f.has_mfderiv_within_at.mfderiv_within hs

end continuous_linear_equiv

variables {s : set M} {x : M}

section id
/-! #### Identity -/

lemma has_mfderiv_at_id (x : M) :
  has_mfderiv_at I I (@_root_.id M) x (continuous_linear_map.id 𝕜 (tangent_space I x)) :=
begin
  refine ⟨continuous_id.continuous_at, _⟩,
  have : ∀ᶠ y in 𝓝[range I] ((ext_chart_at I x) x),
    ((ext_chart_at I x) ∘ (ext_chart_at I x).symm) y = id y,
  { apply filter.mem_of_superset (ext_chart_at_target_mem_nhds_within I x),
    mfld_set_tac },
  apply has_fderiv_within_at.congr_of_eventually_eq (has_fderiv_within_at_id _ _) this,
  simp only with mfld_simps
end

theorem has_mfderiv_within_at_id (s : set M) (x : M) :
  has_mfderiv_within_at I I (@_root_.id M) s x (continuous_linear_map.id 𝕜 (tangent_space I x)) :=
(has_mfderiv_at_id I x).has_mfderiv_within_at

lemma mdifferentiable_at_id : mdifferentiable_at I I (@_root_.id M) x :=
(has_mfderiv_at_id I x).mdifferentiable_at

lemma mdifferentiable_within_at_id : mdifferentiable_within_at I I (@_root_.id M) s x :=
(mdifferentiable_at_id I).mdifferentiable_within_at

lemma mdifferentiable_id : mdifferentiable I I (@_root_.id M) :=
λx, mdifferentiable_at_id I

lemma mdifferentiable_on_id : mdifferentiable_on I I (@_root_.id M) s :=
(mdifferentiable_id I).mdifferentiable_on

@[simp, mfld_simps] lemma mfderiv_id :
  mfderiv I I (@_root_.id M) x = (continuous_linear_map.id 𝕜 (tangent_space I x)) :=
has_mfderiv_at.mfderiv (has_mfderiv_at_id I x)

lemma mfderiv_within_id (hxs : unique_mdiff_within_at I s x) :
  mfderiv_within I I (@_root_.id M) s x = (continuous_linear_map.id 𝕜 (tangent_space I x)) :=
begin
  rw mdifferentiable.mfderiv_within (mdifferentiable_at_id I) hxs,
  exact mfderiv_id I
end

@[simp, mfld_simps] lemma tangent_map_id : tangent_map I I (id : M → M) = id :=
by { ext1 ⟨x, v⟩, simp [tangent_map] }

lemma tangent_map_within_id {p : tangent_bundle I M}
  (hs : unique_mdiff_within_at I s (tangent_bundle.proj I M p)) :
  tangent_map_within I I (id : M → M) s p = p :=
begin
  simp only [tangent_map_within, id.def],
  rw mfderiv_within_id,
  { rcases p, refl },
  { exact hs }
end

end id

section const
/-! #### Constants -/

variables {c : M'}

lemma has_mfderiv_at_const (c : M') (x : M) :
  has_mfderiv_at I I' (λy : M, c) x
  (0 : tangent_space I x →L[𝕜] tangent_space I' c) :=
begin
  refine ⟨continuous_const.continuous_at, _⟩,
  simp only [written_in_ext_chart_at, (∘), has_fderiv_within_at_const]
end

theorem has_mfderiv_within_at_const (c : M') (s : set M) (x : M) :
  has_mfderiv_within_at I I' (λy : M, c) s x
  (0 : tangent_space I x →L[𝕜] tangent_space I' c) :=
(has_mfderiv_at_const I I' c x).has_mfderiv_within_at

lemma mdifferentiable_at_const : mdifferentiable_at I I' (λy : M, c) x :=
(has_mfderiv_at_const I I' c x).mdifferentiable_at

lemma mdifferentiable_within_at_const : mdifferentiable_within_at I I' (λy : M, c) s x :=
(mdifferentiable_at_const I I').mdifferentiable_within_at

lemma mdifferentiable_const : mdifferentiable I I' (λy : M, c) :=
λx, mdifferentiable_at_const I I'

lemma mdifferentiable_on_const : mdifferentiable_on I I' (λy : M, c) s :=
(mdifferentiable_const I I').mdifferentiable_on

@[simp, mfld_simps] lemma mfderiv_const : mfderiv I I' (λy : M, c) x =
  (0 : tangent_space I x →L[𝕜] tangent_space I' c) :=
has_mfderiv_at.mfderiv (has_mfderiv_at_const I I' c x)

lemma mfderiv_within_const (hxs : unique_mdiff_within_at I s x) :
  mfderiv_within I I' (λy : M, c) s x =
  (0 : tangent_space I x →L[𝕜] tangent_space I' c) :=
(has_mfderiv_within_at_const _ _ _ _ _).mfderiv_within hxs

end const

section arithmetic
/-! #### Arithmetic

Note that in the in `has_mfderiv_at` lemmas there is an abuse of the defeq between `E'` and
`tangent_space 𝓘(𝕜, E') (f z)` (similarly for `g',F',p',q'`). In general this defeq is not
canonical, but in this case (the tangent space of a vector space) it is canonical.
 -/

section group
variables {I} {z : M} {f g : M → E'} {f' g' : tangent_space I z →L[𝕜] E'}

lemma has_mfderiv_at.add (hf : has_mfderiv_at I 𝓘(𝕜, E') f z f')
  (hg : has_mfderiv_at I 𝓘(𝕜, E') g z g') : has_mfderiv_at I 𝓘(𝕜, E') (f + g) z (f' + g') :=
⟨hf.1.add hg.1, hf.2.add hg.2⟩

lemma mdifferentiable_at.add (hf : mdifferentiable_at I 𝓘(𝕜, E') f z)
  (hg : mdifferentiable_at I 𝓘(𝕜, E') g z) : mdifferentiable_at I 𝓘(𝕜, E') (f + g) z :=
(hf.has_mfderiv_at.add hg.has_mfderiv_at).mdifferentiable_at

lemma mdifferentiable.add (hf : mdifferentiable I 𝓘(𝕜, E') f) (hg : mdifferentiable I 𝓘(𝕜, E') g) :
  mdifferentiable I 𝓘(𝕜, E') (f + g) :=
λ x, (hf x).add (hg x)

lemma mfderiv_add (hf : mdifferentiable_at I 𝓘(𝕜, E') f z)
  (hg : mdifferentiable_at I 𝓘(𝕜, E') g z) :
  (mfderiv I 𝓘(𝕜, E') (f + g) z : tangent_space I z →L[𝕜] E') =
  (mfderiv I 𝓘(𝕜, E') f z + mfderiv I 𝓘(𝕜, E') g z : tangent_space I z →L[𝕜] E') :=
(hf.has_mfderiv_at.add hg.has_mfderiv_at).mfderiv

lemma has_mfderiv_at.const_smul (hf : has_mfderiv_at I 𝓘(𝕜, E') f z f') (s : 𝕜) :
   has_mfderiv_at I 𝓘(𝕜, E') (s • f) z (s • f') :=
⟨hf.1.const_smul s, hf.2.const_smul s⟩

lemma mdifferentiable_at.const_smul (hf : mdifferentiable_at I 𝓘(𝕜, E') f z) (s : 𝕜) :
  mdifferentiable_at I 𝓘(𝕜, E') (s • f) z :=
(hf.has_mfderiv_at.const_smul s).mdifferentiable_at

lemma mdifferentiable.const_smul (s : 𝕜) (hf : mdifferentiable I 𝓘(𝕜, E') f) :
  mdifferentiable I 𝓘(𝕜, E') (s • f) :=
λ x, (hf x).const_smul s

lemma const_smul_mfderiv (hf : mdifferentiable_at I 𝓘(𝕜, E') f z) (s : 𝕜) :
  (mfderiv I 𝓘(𝕜, E') (s • f) z : tangent_space I z →L[𝕜] E') =
  (s • mfderiv I 𝓘(𝕜, E') f z : tangent_space I z →L[𝕜] E') :=
(hf.has_mfderiv_at.const_smul s).mfderiv

lemma has_mfderiv_at.neg (hf : has_mfderiv_at I 𝓘(𝕜, E') f z f') :
   has_mfderiv_at I 𝓘(𝕜, E') (-f) z (-f') :=
⟨hf.1.neg, hf.2.neg⟩

lemma has_mfderiv_at_neg :
  has_mfderiv_at I 𝓘(𝕜, E') (-f) z (-f') ↔ has_mfderiv_at I 𝓘(𝕜, E') f z f' :=
⟨λ hf, by { convert hf.neg; rw [neg_neg] }, λ hf, hf.neg⟩

lemma mdifferentiable_at.neg (hf : mdifferentiable_at I 𝓘(𝕜, E') f z) :
  mdifferentiable_at I 𝓘(𝕜, E') (-f) z :=
hf.has_mfderiv_at.neg.mdifferentiable_at

lemma mdifferentiable_at_neg :
  mdifferentiable_at I 𝓘(𝕜, E') (-f) z ↔ mdifferentiable_at I 𝓘(𝕜, E') f z :=
⟨λ hf, by { convert hf.neg; rw [neg_neg] }, λ hf, hf.neg⟩

lemma mdifferentiable.neg (hf : mdifferentiable I 𝓘(𝕜, E') f) :
  mdifferentiable I 𝓘(𝕜, E') (-f) :=
λ x, (hf x).neg

lemma mfderiv_neg (f : M → E') (x : M) :
  (mfderiv I 𝓘(𝕜, E') (-f) x : tangent_space I x →L[𝕜] E') =
  (- mfderiv I 𝓘(𝕜, E') f x : tangent_space I x →L[𝕜] E') :=
begin
  simp_rw [mfderiv],
  by_cases hf : mdifferentiable_at I 𝓘(𝕜, E') f x,
  { exact hf.has_mfderiv_at.neg.mfderiv },
  { rw [if_neg hf], rw [← mdifferentiable_at_neg] at hf, rw [if_neg hf, neg_zero] },
end

lemma has_mfderiv_at.sub (hf : has_mfderiv_at I 𝓘(𝕜, E') f z f')
  (hg : has_mfderiv_at I 𝓘(𝕜, E') g z g') : has_mfderiv_at I 𝓘(𝕜, E') (f - g) z (f'- g') :=
⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

lemma mdifferentiable_at.sub (hf : mdifferentiable_at I 𝓘(𝕜, E') f z)
  (hg : mdifferentiable_at I 𝓘(𝕜, E') g z) : mdifferentiable_at I 𝓘(𝕜, E') (f - g) z :=
(hf.has_mfderiv_at.sub hg.has_mfderiv_at).mdifferentiable_at

lemma mdifferentiable.sub (hf : mdifferentiable I 𝓘(𝕜, E') f)
  (hg : mdifferentiable I 𝓘(𝕜, E') g)  : mdifferentiable I 𝓘(𝕜, E') (f - g) :=
λ x, (hf x).sub (hg x)

lemma mfderiv_sub (hf : mdifferentiable_at I 𝓘(𝕜, E') f z)
  (hg : mdifferentiable_at I 𝓘(𝕜, E') g z) :
  (mfderiv I 𝓘(𝕜, E') (f - g) z : tangent_space I z →L[𝕜] E') =
  (mfderiv I 𝓘(𝕜, E') f z - mfderiv I 𝓘(𝕜, E') g z : tangent_space I z →L[𝕜] E') :=
(hf.has_mfderiv_at.sub hg.has_mfderiv_at).mfderiv

end group

section algebra_over_ring
variables {I} {z : M} {F' : Type*} [normed_ring F'] [normed_algebra 𝕜 F']
  {p q : M → F'} {p' q' : tangent_space I z →L[𝕜] F'}

lemma has_mfderiv_within_at.mul' (hp : has_mfderiv_within_at I 𝓘(𝕜, F') p s z p')
  (hq : has_mfderiv_within_at I 𝓘(𝕜, F') q s z q') :
  has_mfderiv_within_at I 𝓘(𝕜, F') (p * q) s z (p z • q' + p'.smul_right (q z) : E →L[𝕜] F') :=
⟨hp.1.mul hq.1, by simpa only with mfld_simps using hp.2.mul' hq.2⟩

lemma has_mfderiv_at.mul' (hp : has_mfderiv_at I 𝓘(𝕜, F') p z p')
  (hq : has_mfderiv_at I 𝓘(𝕜, F') q z q') :
  has_mfderiv_at I 𝓘(𝕜, F') (p * q) z (p z • q' + p'.smul_right (q z) : E →L[𝕜] F') :=
has_mfderiv_within_at_univ.mp $ hp.has_mfderiv_within_at.mul' hq.has_mfderiv_within_at

lemma mdifferentiable_within_at.mul (hp : mdifferentiable_within_at I 𝓘(𝕜, F') p s z)
  (hq : mdifferentiable_within_at I 𝓘(𝕜, F') q s z) :
  mdifferentiable_within_at I 𝓘(𝕜, F') (p * q) s z :=
(hp.has_mfderiv_within_at.mul' hq.has_mfderiv_within_at).mdifferentiable_within_at

lemma mdifferentiable_at.mul (hp : mdifferentiable_at I 𝓘(𝕜, F') p z)
  (hq : mdifferentiable_at I 𝓘(𝕜, F') q z) : mdifferentiable_at I 𝓘(𝕜, F') (p * q) z :=
(hp.has_mfderiv_at.mul' hq.has_mfderiv_at).mdifferentiable_at

lemma mdifferentiable_on.mul (hp : mdifferentiable_on I 𝓘(𝕜, F') p s)
  (hq : mdifferentiable_on I 𝓘(𝕜, F') q s) : mdifferentiable_on I 𝓘(𝕜, F') (p * q) s :=
λ x hx, (hp x hx).mul $ hq x hx

lemma mdifferentiable.mul (hp : mdifferentiable I 𝓘(𝕜, F') p)
  (hq : mdifferentiable I 𝓘(𝕜, F') q) : mdifferentiable I 𝓘(𝕜, F') (p * q) :=
λ x, (hp x).mul (hq x)

end algebra_over_ring

section algebra_over_comm_ring
variables {I} {z : M} {F' : Type*} [normed_comm_ring F'] [normed_algebra 𝕜 F']
  {p q : M → F'} {p' q' : tangent_space I z →L[𝕜] F'}

lemma has_mfderiv_within_at.mul (hp : has_mfderiv_within_at I 𝓘(𝕜, F') p s z p')
  (hq : has_mfderiv_within_at I 𝓘(𝕜, F') q s z q') :
  has_mfderiv_within_at I 𝓘(𝕜, F') (p * q) s z (p z • q' + q z • p' : E →L[𝕜] F') :=
by { convert hp.mul' hq, ext z, apply mul_comm }

lemma has_mfderiv_at.mul (hp : has_mfderiv_at I 𝓘(𝕜, F') p z p')
  (hq : has_mfderiv_at I 𝓘(𝕜, F') q z q') :
  has_mfderiv_at I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E →L[𝕜] F') :=
has_mfderiv_within_at_univ.mp $ hp.has_mfderiv_within_at.mul hq.has_mfderiv_within_at

end algebra_over_comm_ring

end arithmetic

namespace model_with_corners
/-! #### Model with corners -/

protected lemma has_mfderiv_at {x} :
  has_mfderiv_at I 𝓘(𝕜, E) I x (continuous_linear_map.id _ _) :=
⟨I.continuous_at, (has_fderiv_within_at_id _ _).congr' I.right_inv_on (mem_range_self _)⟩

protected lemma has_mfderiv_within_at {s x} :
  has_mfderiv_within_at I 𝓘(𝕜, E) I s x (continuous_linear_map.id _ _) :=
I.has_mfderiv_at.has_mfderiv_within_at

protected lemma mdifferentiable_within_at {s x} :
  mdifferentiable_within_at I 𝓘(𝕜, E) I s x :=
I.has_mfderiv_within_at.mdifferentiable_within_at

protected lemma mdifferentiable_at {x} :
  mdifferentiable_at I 𝓘(𝕜, E) I x :=
I.has_mfderiv_at.mdifferentiable_at

protected lemma mdifferentiable_on {s} :
  mdifferentiable_on I 𝓘(𝕜, E) I s :=
λ x hx, I.mdifferentiable_within_at

protected lemma mdifferentiable :
  mdifferentiable I (𝓘(𝕜, E)) I :=
λ x, I.mdifferentiable_at

lemma has_mfderiv_within_at_symm {x} (hx : x ∈ range I) :
  has_mfderiv_within_at 𝓘(𝕜, E) I I.symm (range I) x (continuous_linear_map.id _ _) :=
⟨I.continuous_within_at_symm, (has_fderiv_within_at_id _ _).congr'
  (λ y hy, I.right_inv_on hy.1) ⟨hx, mem_range_self _⟩⟩

lemma mdifferentiable_on_symm :
  mdifferentiable_on (𝓘(𝕜, E)) I I.symm (range I) :=
λ x hx, (I.has_mfderiv_within_at_symm hx).mdifferentiable_within_at

end model_with_corners

section charts

variable {e : local_homeomorph M H}

lemma mdifferentiable_at_atlas (h : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) :
  mdifferentiable_at I I e x :=
begin
  refine ⟨(e.continuous_on x hx).continuous_at (is_open.mem_nhds e.open_source hx), _⟩,
  have mem : I ((chart_at H x : M → H) x) ∈
    I.symm ⁻¹' ((chart_at H x).symm ≫ₕ e).source ∩ range I,
    by simp only [hx] with mfld_simps,
  have : (chart_at H x).symm.trans e ∈ cont_diff_groupoid ∞ I :=
    has_groupoid.compatible _ (chart_mem_atlas H x) h,
  have A : cont_diff_on 𝕜 ∞
    (I ∘ ((chart_at H x).symm.trans e) ∘ I.symm)
    (I.symm ⁻¹' ((chart_at H x).symm.trans e).source ∩ range I) :=
    this.1,
  have B := A.differentiable_on le_top (I ((chart_at H x : M → H) x)) mem,
  simp only with mfld_simps at B,
  rw [inter_comm, differentiable_within_at_inter] at B,
  { simpa only with mfld_simps },
  { apply is_open.mem_nhds ((local_homeomorph.open_source _).preimage I.continuous_symm) mem.1 }
end

lemma mdifferentiable_on_atlas (h : e ∈ atlas H M) :
  mdifferentiable_on I I e e.source :=
λx hx, (mdifferentiable_at_atlas I h hx).mdifferentiable_within_at

lemma mdifferentiable_at_atlas_symm (h : e ∈ atlas H M) {x : H} (hx : x ∈ e.target) :
  mdifferentiable_at I I e.symm x :=
begin
  refine ⟨(e.continuous_on_symm x hx).continuous_at (is_open.mem_nhds e.open_target hx), _⟩,
  have mem : I x ∈ I.symm ⁻¹' (e.symm ≫ₕ chart_at H (e.symm x)).source ∩ range (I),
    by simp only [hx] with mfld_simps,
  have : e.symm.trans (chart_at H (e.symm x)) ∈ cont_diff_groupoid ∞ I :=
    has_groupoid.compatible _ h (chart_mem_atlas H _),
  have A : cont_diff_on 𝕜 ∞
    (I ∘ (e.symm.trans (chart_at H (e.symm x))) ∘ I.symm)
    (I.symm ⁻¹' (e.symm.trans (chart_at H (e.symm x))).source ∩ range I) :=
    this.1,
  have B := A.differentiable_on le_top (I x) mem,
  simp only with mfld_simps at B,
  rw [inter_comm, differentiable_within_at_inter] at B,
  { simpa only with mfld_simps },
  { apply (is_open.mem_nhds ((local_homeomorph.open_source _).preimage I.continuous_symm) mem.1) }
end

lemma mdifferentiable_on_atlas_symm (h : e ∈ atlas H M) :
  mdifferentiable_on I I e.symm e.target :=
λx hx, (mdifferentiable_at_atlas_symm I h hx).mdifferentiable_within_at

lemma mdifferentiable_of_mem_atlas (h : e ∈ atlas H M) : e.mdifferentiable I I :=
⟨mdifferentiable_on_atlas I h, mdifferentiable_on_atlas_symm I h⟩

lemma mdifferentiable_chart (x : M) : (chart_at H x).mdifferentiable I I :=
mdifferentiable_of_mem_atlas _ (chart_mem_atlas _ _)

/-- The derivative of the chart at a base point is the chart of the tangent bundle, composed with
the identification between the tangent bundle of the model space and the product space. -/
lemma tangent_map_chart {p q : tangent_bundle I M} (h : q.1 ∈ (chart_at H p.1).source) :
  tangent_map I I (chart_at H p.1) q =
  (equiv.sigma_equiv_prod _ _).symm
    ((chart_at (model_prod H E) p : tangent_bundle I M → model_prod H E) q) :=
begin
  dsimp [tangent_map],
  rw mdifferentiable_at.mfderiv,
  { refl },
  { exact mdifferentiable_at_atlas _ (chart_mem_atlas _ _) h }
end

/-- The derivative of the inverse of the chart at a base point is the inverse of the chart of the
tangent bundle, composed with the identification between the tangent bundle of the model space and
the product space. -/
lemma tangent_map_chart_symm {p : tangent_bundle I M} {q : tangent_bundle I H}
  (h : q.1 ∈ (chart_at H p.1).target) :
  tangent_map I I (chart_at H p.1).symm q =
  ((chart_at (model_prod H E) p).symm : model_prod H E → tangent_bundle I M)
    ((equiv.sigma_equiv_prod H E) q) :=
begin
  dsimp only [tangent_map],
  rw mdifferentiable_at.mfderiv (mdifferentiable_at_atlas_symm _ (chart_mem_atlas _ _) h),
  -- a trivial instance is needed after the rewrite, handle it right now.
  rotate, { apply_instance },
  simp only [continuous_linear_map.coe_coe, basic_smooth_vector_bundle_core.chart, h,
    tangent_bundle_core, basic_smooth_vector_bundle_core.to_vector_bundle_core,
    chart_at, sigma.mk.inj_iff] with mfld_simps,
end

end charts

end specific_functions

/-! ### Differentiable local homeomorphisms -/
namespace local_homeomorph.mdifferentiable

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M']
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']
{e : local_homeomorph M M'} (he : e.mdifferentiable I I')
{e' : local_homeomorph M' M''}
include he

lemma symm : e.symm.mdifferentiable I' I :=
⟨he.2, he.1⟩

protected lemma mdifferentiable_at {x : M} (hx : x ∈ e.source) :
  mdifferentiable_at I I' e x :=
(he.1 x hx).mdifferentiable_at (is_open.mem_nhds e.open_source hx)

lemma mdifferentiable_at_symm {x : M'} (hx : x ∈ e.target) :
  mdifferentiable_at I' I e.symm x :=
(he.2 x hx).mdifferentiable_at (is_open.mem_nhds e.open_target hx)

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
[smooth_manifold_with_corners I'' M'']

lemma symm_comp_deriv {x : M} (hx : x ∈ e.source) :
  (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) =
    continuous_linear_map.id 𝕜 (tangent_space I x) :=
begin
  have : (mfderiv I I (e.symm ∘ e) x) =
         (mfderiv I' I e.symm (e x)).comp (mfderiv I I' e x) :=
    mfderiv_comp x (he.mdifferentiable_at_symm (e.map_source hx)) (he.mdifferentiable_at hx),
  rw ← this,
  have : mfderiv I I (_root_.id : M → M) x = continuous_linear_map.id _ _ := mfderiv_id I,
  rw ← this,
  apply filter.eventually_eq.mfderiv_eq,
  have : e.source ∈ 𝓝 x := is_open.mem_nhds e.open_source hx,
  exact filter.mem_of_superset this (by mfld_set_tac)
end

lemma comp_symm_deriv {x : M'} (hx : x ∈ e.target) :
  (mfderiv I I' e (e.symm x)).comp (mfderiv I' I e.symm x) =
    continuous_linear_map.id 𝕜 (tangent_space I' x) :=
he.symm.symm_comp_deriv hx

/-- The derivative of a differentiable local homeomorphism, as a continuous linear equivalence
between the tangent spaces at `x` and `e x`. -/
protected def mfderiv {x : M} (hx : x ∈ e.source) :
  tangent_space I x ≃L[𝕜] tangent_space I' (e x) :=
{ inv_fun := (mfderiv I' I e.symm (e x)),
  continuous_to_fun := (mfderiv I I' e x).cont,
  continuous_inv_fun := (mfderiv I' I e.symm (e x)).cont,
  left_inv := λy, begin
    have : (continuous_linear_map.id _ _ : tangent_space I x →L[𝕜] tangent_space I x) y = y := rfl,
    conv_rhs { rw [← this, ← he.symm_comp_deriv hx] },
    refl
  end,
  right_inv := λy, begin
    have : (continuous_linear_map.id 𝕜 _ :
      tangent_space I' (e x) →L[𝕜] tangent_space I' (e x)) y = y := rfl,
    conv_rhs { rw [← this, ← he.comp_symm_deriv (e.map_source hx)] },
    rw e.left_inv hx,
    refl
  end,
  .. mfderiv I I' e x }

lemma mfderiv_bijective {x : M} (hx : x ∈ e.source) :
  function.bijective (mfderiv I I' e x) :=
(he.mfderiv hx).bijective

lemma mfderiv_injective {x : M} (hx : x ∈ e.source) :
  function.injective (mfderiv I I' e x) :=
(he.mfderiv hx).injective

lemma mfderiv_surjective {x : M} (hx : x ∈ e.source) :
  function.surjective (mfderiv I I' e x) :=
(he.mfderiv hx).surjective

lemma ker_mfderiv_eq_bot {x : M} (hx : x ∈ e.source) :
  linear_map.ker (mfderiv I I' e x) = ⊥ :=
(he.mfderiv hx).to_linear_equiv.ker

lemma range_mfderiv_eq_top {x : M} (hx : x ∈ e.source) :
  linear_map.range (mfderiv I I' e x) = ⊤ :=
(he.mfderiv hx).to_linear_equiv.range

lemma range_mfderiv_eq_univ {x : M} (hx : x ∈ e.source) :
  range (mfderiv I I' e x) = univ :=
(he.mfderiv_surjective hx).range_eq

lemma trans (he': e'.mdifferentiable I' I'') : (e.trans e').mdifferentiable I I'' :=
begin
  split,
  { assume x hx,
    simp only with mfld_simps at hx,
    exact ((he'.mdifferentiable_at hx.2).comp _
           (he.mdifferentiable_at hx.1)).mdifferentiable_within_at },
  { assume x hx,
    simp only with mfld_simps at hx,
    exact ((he.symm.mdifferentiable_at hx.2).comp _
           (he'.symm.mdifferentiable_at hx.1)).mdifferentiable_within_at }
end

end local_homeomorph.mdifferentiable

/-! ### Differentiability of `ext_chart_at` -/

section ext_chart_at

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{s : set M} {x y : M}

lemma has_mfderiv_at_ext_chart_at (h : y ∈ (chart_at H x).source) :
  has_mfderiv_at I 𝓘(𝕜, E) (ext_chart_at I x) y (mfderiv I I (chart_at H x) y : _) :=
I.has_mfderiv_at.comp y ((mdifferentiable_chart I x).mdifferentiable_at h).has_mfderiv_at

lemma has_mfderiv_within_at_ext_chart_at (h : y ∈ (chart_at H x).source) :
  has_mfderiv_within_at I 𝓘(𝕜, E) (ext_chart_at I x) s y (mfderiv I I (chart_at H x) y : _) :=
(has_mfderiv_at_ext_chart_at I h).has_mfderiv_within_at

lemma mdifferentiable_at_ext_chart_at (h : y ∈ (chart_at H x).source) :
  mdifferentiable_at I 𝓘(𝕜, E) (ext_chart_at I x) y :=
(has_mfderiv_at_ext_chart_at I h).mdifferentiable_at

lemma mdifferentiable_on_ext_chart_at :
  mdifferentiable_on I 𝓘(𝕜, E) (ext_chart_at I x) (chart_at H x).source :=
λ y hy, (has_mfderiv_within_at_ext_chart_at I hy).mdifferentiable_within_at

end ext_chart_at

/-! ### Unique derivative sets in manifolds -/
section unique_mdiff

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M']
{s : set M}

/-- If a set has the unique differential property, then its image under a local
diffeomorphism also has the unique differential property. -/
lemma unique_mdiff_on.unique_mdiff_on_preimage [smooth_manifold_with_corners I' M']
  (hs : unique_mdiff_on I s) {e : local_homeomorph M M'} (he : e.mdifferentiable I I') :
  unique_mdiff_on I' (e.target ∩ e.symm ⁻¹' s) :=
begin
  /- Start from a point `x` in the image, and let `z` be its preimage. Then the unique
  derivative property at `x` is expressed through `ext_chart_at I' x`, and the unique
  derivative property at `z` is expressed through `ext_chart_at I z`. We will argue that
  the composition of these two charts with `e` is a local diffeomorphism in vector spaces,
  and therefore preserves the unique differential property thanks to lemma
  `has_fderiv_within_at.unique_diff_within_at`, saying that a differentiable function with onto
  derivative preserves the unique derivative property.-/
  assume x hx,
  let z := e.symm x,
  have z_source : z ∈ e.source, by simp only [hx.1] with mfld_simps,
  have zx : e z = x, by simp only [z, hx.1] with mfld_simps,
  let F := ext_chart_at I z,
  -- the unique derivative property at `z` is expressed through its preferred chart,
  -- that we call `F`.
  have B : unique_diff_within_at 𝕜
    (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' ((ext_chart_at I' x).source))) ∩ F.target) (F z),
  { have : unique_mdiff_within_at I s z := hs _ hx.2,
    have S : e.source ∩ e ⁻¹' ((ext_chart_at I' x).source) ∈ 𝓝 z,
    { apply is_open.mem_nhds,
      apply e.continuous_on.preimage_open_of_open e.open_source (is_open_ext_chart_at_source I' x),
      simp only [z_source, zx] with mfld_simps },
    have := this.inter S,
    rw [unique_mdiff_within_at_iff] at this,
    exact this },
  -- denote by `G` the change of coordinate, i.e., the composition of the two extended charts and
  -- of `e`
  let G := F.symm ≫ e.to_local_equiv ≫ (ext_chart_at I' x),
  -- `G` is differentiable
  have Diff : ((chart_at H z).symm ≫ₕ e ≫ₕ (chart_at H' x)).mdifferentiable I I',
  { have A := mdifferentiable_of_mem_atlas I (chart_mem_atlas H z),
    have B := mdifferentiable_of_mem_atlas I' (chart_mem_atlas H' x),
    exact A.symm.trans (he.trans B) },
  have Mmem : (chart_at H z : M → H) z ∈ ((chart_at H z).symm ≫ₕ e ≫ₕ (chart_at H' x)).source,
    by simp only [z_source, zx] with mfld_simps,
  have A : differentiable_within_at 𝕜 G (range I) (F z),
  { refine (Diff.mdifferentiable_at Mmem).2.congr (λp hp, _) _;
    simp only [G, F] with mfld_simps },
  -- let `G'` be its derivative
  let G' := fderiv_within 𝕜 G (range I) (F z),
  have D₁ : has_fderiv_within_at G G' (range I) (F z) :=
    A.has_fderiv_within_at,
  have D₂ : has_fderiv_within_at G G'
      (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' ((ext_chart_at I' x).source))) ∩ F.target) (F z) :=
    D₁.mono (by mfld_set_tac),
  -- The derivative `G'` is onto, as it is the derivative of a local diffeomorphism, the composition
  -- of the two charts and of `e`.
  have C : dense_range (G' : E → E'),
  { have : G' = mfderiv I I' ((chart_at H z).symm ≫ₕ e ≫ₕ (chart_at H' x))
      ((chart_at H z : M → H) z),
      by { rw (Diff.mdifferentiable_at Mmem).mfderiv, refl },
    rw this,
    exact (Diff.mfderiv_surjective Mmem).dense_range },
  -- key step: thanks to what we have proved about it, `G` preserves the unique derivative property
  have key : unique_diff_within_at 𝕜
    (G '' (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' ((ext_chart_at I' x).source))) ∩ F.target))
    (G (F z)) := D₂.unique_diff_within_at B C,
  have : G (F z) = (ext_chart_at I' x) x, by { dsimp [G, F], simp only [hx.1] with mfld_simps },
  rw this at key,
  apply key.mono,
  show G '' (F.symm ⁻¹' (s ∩ (e.source ∩ e ⁻¹' ((ext_chart_at I' x).source))) ∩ F.target) ⊆
    (ext_chart_at I' x).symm ⁻¹' e.target ∩ (ext_chart_at I' x).symm ⁻¹' (e.symm ⁻¹' s) ∩
      range (I'),
  rw image_subset_iff,
  mfld_set_tac
end

/-- If a set in a manifold has the unique derivative property, then its pullback by any extended
chart, in the vector space, also has the unique derivative property. -/
lemma unique_mdiff_on.unique_diff_on_target_inter (hs : unique_mdiff_on I s) (x : M) :
  unique_diff_on 𝕜 ((ext_chart_at I x).target ∩ ((ext_chart_at I x).symm ⁻¹' s)) :=
begin
  -- this is just a reformulation of `unique_mdiff_on.unique_mdiff_on_preimage`, using as `e`
  -- the local chart at `x`.
  assume z hz,
  simp only with mfld_simps at hz,
  have : (chart_at H x).mdifferentiable I I := mdifferentiable_chart _ _,
  have T := (hs.unique_mdiff_on_preimage this) (I.symm z),
  simp only [hz.left.left, hz.left.right, hz.right, unique_mdiff_within_at] with mfld_simps at ⊢ T,
  convert T using 1,
  rw @preimage_comp _ _ _ _ (chart_at H x).symm,
  mfld_set_tac
end

/-- When considering functions between manifolds, this statement shows up often. It entails
the unique differential of the pullback in extended charts of the set where the function can
be read in the charts. -/
lemma unique_mdiff_on.unique_diff_on_inter_preimage (hs : unique_mdiff_on I s) (x : M) (y : M')
  {f : M → M'} (hf : continuous_on f s) :
  unique_diff_on 𝕜 ((ext_chart_at I x).target
    ∩ ((ext_chart_at I x).symm ⁻¹' (s ∩ f⁻¹' (ext_chart_at I' y).source))) :=
begin
  have : unique_mdiff_on I (s ∩ f ⁻¹' (ext_chart_at I' y).source),
  { assume z hz,
    apply (hs z hz.1).inter',
    apply (hf z hz.1).preimage_mem_nhds_within,
    exact (is_open_ext_chart_at_source I' y).mem_nhds hz.2 },
  exact this.unique_diff_on_target_inter _
end

variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
(Z : basic_smooth_vector_bundle_core I M F)

/-- In a smooth fiber bundle constructed from core, the preimage under the projection of a set with
unique differential in the basis also has unique differential. -/
lemma unique_mdiff_on.smooth_bundle_preimage (hs : unique_mdiff_on I s) :
  unique_mdiff_on (I.prod (𝓘(𝕜, F))) (Z.to_vector_bundle_core.proj ⁻¹' s) :=
begin
  /- Using a chart (and the fact that unique differentiability is invariant under charts), we
  reduce the situation to the model space, where we can use the fact that products respect
  unique differentiability. -/
  assume p hp,
  replace hp : p.fst ∈ s, by simpa only with mfld_simps using hp,
  let e₀ := chart_at H p.1,
  let e := chart_at (model_prod H F) p,
  -- It suffices to prove unique differentiability in a chart
  suffices h : unique_mdiff_on (I.prod (𝓘(𝕜, F)))
    (e.target ∩ e.symm⁻¹' (Z.to_vector_bundle_core.proj ⁻¹' s)),
  { have A : unique_mdiff_on (I.prod (𝓘(𝕜, F))) (e.symm.target ∩
      e.symm.symm ⁻¹' (e.target ∩ e.symm⁻¹' (Z.to_vector_bundle_core.proj ⁻¹' s))),
    { apply h.unique_mdiff_on_preimage,
      exact (mdifferentiable_of_mem_atlas _ (chart_mem_atlas _ _)).symm,
      apply_instance },
    have : p ∈ e.symm.target ∩
      e.symm.symm ⁻¹' (e.target ∩ e.symm⁻¹' (Z.to_vector_bundle_core.proj ⁻¹' s)),
        by simp only [e, hp] with mfld_simps,
    apply (A _ this).mono,
    assume q hq,
    simp only [e, local_homeomorph.left_inv _ hq.1] with mfld_simps at hq,
    simp only [hq] with mfld_simps },
  -- rewrite the relevant set in the chart as a direct product
  have : (λ (p : E × F), (I.symm p.1, p.snd)) ⁻¹' e.target ∩
         (λ (p : E × F), (I.symm p.1, p.snd)) ⁻¹' (e.symm ⁻¹' (sigma.fst ⁻¹' s)) ∩
         (range I ×ˢ univ)
        = (I.symm ⁻¹' (e₀.target ∩ e₀.symm⁻¹' s) ∩ range I) ×ˢ univ,
    by mfld_set_tac,
  assume q hq,
  replace hq : q.1 ∈ (chart_at H p.1).target ∧ ((chart_at H p.1).symm : H → M) q.1 ∈ s,
    by simpa only with mfld_simps using hq,
  simp only [unique_mdiff_within_at, model_with_corners.prod, preimage_inter, this] with mfld_simps,
  -- apply unique differentiability of products to conclude
  apply unique_diff_on.prod _ unique_diff_on_univ,
  { simp only [hq] with mfld_simps },
  { assume x hx,
    have A : unique_mdiff_on I (e₀.target ∩ e₀.symm⁻¹' s),
    { apply hs.unique_mdiff_on_preimage,
      exact (mdifferentiable_of_mem_atlas _ (chart_mem_atlas _ _)),
      apply_instance },
    simp only [unique_mdiff_on, unique_mdiff_within_at, preimage_inter] with mfld_simps at A,
    have B := A (I.symm x) hx.1.1 hx.1.2,
    rwa [← preimage_inter, model_with_corners.right_inv _ hx.2] at B }
end

lemma unique_mdiff_on.tangent_bundle_proj_preimage (hs : unique_mdiff_on I s):
  unique_mdiff_on I.tangent ((tangent_bundle.proj I M) ⁻¹' s) :=
hs.smooth_bundle_preimage _

end unique_mdiff
