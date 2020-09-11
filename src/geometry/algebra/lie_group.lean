/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.times_cont_mdiff

/-!
# Lie groups

A Lie group is a group that is also a smooth manifold, in which the group operations of
multiplication and inversion are smooth maps. Smoothness of the group multiplication means that
multiplication is a smooth mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff a Lie group here is not
guaranteed to be second-countable (even though it can be proved it is Hausdorff). Note also that Lie
groups here are not necessarily finite dimensional.

## Main definitions and statements

* `lie_add_group I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `lie_group I G`     : a Lie multiplicative group where `G` is a manifold on the model with
                        corners `I`.
* `lie_add_group_morphism I I' G G'`  : morphism of addittive Lie groups
* `lie_group_morphism I I' G G'`      : morphism of Lie groups
* `lie_add_group_core I G`            : allows to define a Lie additive group without first proving
                                        it is a topological additive group.
* `lie_group_core I G`                : allows to define a Lie group without first proving
                                        it is a topological group.

* `reals_lie_group`                   : real numbers are a Lie group


## Implementation notes
A priori, a Lie group here is a manifold with corners.

The definition of Lie group cannot require `I : model_with_corners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, beause in the product situation,
the model space is `model_prod E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : model_with_corners 𝕜 E H`.
-/

noncomputable theory

section lie_group

/-- A Lie (additive) group is a group and a smooth manifold at the same time in which
the addition and negation operations are smooth. -/
class lie_add_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [add_group G] [topological_space G] [topological_add_group G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
(smooth_add : smooth (I.prod I) I (λ p : G×G, p.1 + p.2))
(smooth_neg : smooth I I (λ a:G, -a))

/-- A Lie group is a group and a smooth manifold at the same time in which
the multiplication and inverse operations are smooth. -/
@[to_additive]
class lie_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [group G] [topological_space G] [topological_group G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
(smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2))
(smooth_inv : smooth I I (λ a:G, a⁻¹))

section lie_group

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{F : Type*} [normed_group F] [normed_space 𝕜 F] {J : model_with_corners 𝕜 F F}
{G : Type*} [topological_space G] [charted_space H G] [group G]
[topological_group G] [lie_group I G]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H' M] [smooth_manifold_with_corners I' M]
{E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M' : Type*} [topological_space M'] [charted_space H'' M'] [smooth_manifold_with_corners I'' M']

@[to_additive]
lemma smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2) :=
lie_group.smooth_mul

@[to_additive]
lemma smooth.mul {f : M → G} {g : M → G} (hf : smooth I' I f) (hg : smooth I' I g) :
  smooth I' I (f * g) :=
smooth_mul.comp (hf.prod_mk hg)

localized "notation `L_add` := left_add" in lie_group

localized "notation `R_add` := right_add" in lie_group

localized "notation `L` := left_mul" in lie_group

localized "notation `R` := right_mul" in lie_group

@[to_additive]
lemma smooth_left_mul {a : G} : smooth I I (left_mul a) :=
smooth_mul.comp (smooth_const.prod_mk smooth_id)

@[to_additive]
lemma smooth_right_mul {a : G} : smooth I I (right_mul a) :=
smooth_mul.comp (smooth_id.prod_mk smooth_const)

@[to_additive]
lemma smooth_on.mul {f : M → G} {g : M → G} {s : set M}
  (hf : smooth_on I' I f s) (hg : smooth_on I' I g s) :
  smooth_on I' I (f * g) s :=
(smooth_mul.comp_smooth_on (hf.prod_mk hg) : _)

lemma smooth_pow : ∀ n : ℕ, smooth I I (λ a : G, a ^ n)
| 0 := by { simp only [pow_zero], exact smooth_const }
| (k+1) := show smooth I I (λ (a : G), a * a ^ k), from smooth_id.mul (smooth_pow _)

@[to_additive]
lemma smooth_inv : smooth I I (λ x : G, x⁻¹) :=
lie_group.smooth_inv

@[to_additive]
lemma smooth.inv {f : M → G}
  (hf : smooth I' I f) : smooth I' I (λx, (f x)⁻¹) :=
smooth_inv.comp hf

@[to_additive]
lemma smooth_on.inv {f : M → G} {s : set M}
  (hf : smooth_on I' I f s) : smooth_on I' I (λx, (f x)⁻¹) s :=
smooth_inv.comp_smooth_on hf

end lie_group

section prod_lie_group

/- Instance of product group -/
@[to_additive]
instance {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]  {I : model_with_corners 𝕜 E H}
  {G : Type*} [topological_space G] [charted_space H G] [group G] [topological_group G]
  [h : lie_group I G] {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {G' : Type*} [topological_space G'] [charted_space H' G']
  [group G'] [topological_group G'] [h' : lie_group I' G'] : lie_group (I.prod I') (G×G') :=
{ smooth_mul := ((smooth_fst.comp smooth_fst).smooth.mul (smooth_fst.comp smooth_snd)).prod_mk
    ((smooth_snd.comp smooth_fst).smooth.mul (smooth_snd.comp smooth_snd)),
  smooth_inv := smooth_fst.inv.prod_mk smooth_snd.inv, }

end prod_lie_group

section lie_add_group_morphism

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']

/-- Morphism of additive Lie groups. -/
structure lie_add_group_morphism (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E')
  (G : Type*) [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G]
  [add_group G] [topological_add_group G] [lie_add_group I G]
  (G' : Type*) [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G']
  [add_group G'] [topological_add_group G'] [lie_add_group I' G'] extends add_monoid_hom G G' :=
(smooth_to_fun : smooth I I' to_fun)

/-- Morphism of Lie groups. -/
@[to_additive]
structure lie_group_morphism (I : model_with_corners 𝕜 E E) (I' : model_with_corners 𝕜 E' E')
  (G : Type*) [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G] [group G]
  [topological_group G] [lie_group I G]
  (G' : Type*) [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G']
  [group G'] [topological_group G'] [lie_group I' G'] extends monoid_hom G G' :=
(smooth_to_fun : smooth I I' to_fun)

variables {I : model_with_corners 𝕜 E E} {I' : model_with_corners 𝕜 E' E'}
{G : Type*} [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G]
[group G] [topological_group G] [lie_group I G]
{G' : Type*} [topological_space G'] [charted_space E' G'] [smooth_manifold_with_corners I' G']
[group G'] [topological_group G'] [lie_group I' G']

@[to_additive]
instance : has_one (lie_group_morphism I I' G G') := ⟨⟨1, smooth_const⟩⟩

@[to_additive]
instance : inhabited (lie_group_morphism I I' G G') := ⟨1⟩

@[to_additive]
instance : has_coe_to_fun (lie_group_morphism I I' G G') := ⟨_, λ a, a.to_fun⟩

end lie_add_group_morphism

end lie_group

section lie_group_core

/-- Sometimes one might want to define a Lie additive group `G` without having proved previously
that `G` is a topological additive group. In such case it is possible to use `lie_add_group_core`
that does not require such instance, and then get a Lie group by invoking `to_lie_add_group`. -/
structure lie_add_group_core {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E]
  [normed_space 𝕜 E] (I : model_with_corners 𝕜 E E)
  (G : Type*) [add_group G] [topological_space G]
  [charted_space E G] [smooth_manifold_with_corners I G] : Prop :=
(smooth_add : smooth (I.prod I) I (λ p : G×G, p.1 + p.2))
(smooth_neg : smooth I I (λ a:G, -a))

/-- Sometimes one might want to define a Lie group `G` without having proved previously that `G` is
a topological group. In such case it is possible to use `lie_group_core` that does not require such
instance, and then get a Lie group by invoking `to_lie_group` defined below. -/
@[to_additive]
structure lie_group_core {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E]
  [normed_space 𝕜 E] (I : model_with_corners 𝕜 E E)
  (G : Type*) [group G] [topological_space G]
  [charted_space E G] [smooth_manifold_with_corners I G] : Prop :=
(smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2))
(smooth_inv : smooth I I (λ a:G, a⁻¹))

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E E}
{F : Type*} [normed_group F] [normed_space 𝕜 F] {J : model_with_corners 𝕜 F F}
{G : Type*} [topological_space G] [charted_space E G] [smooth_manifold_with_corners I G] [group G]

namespace lie_group_core

variables (c : lie_group_core I G)

@[to_additive]
protected lemma to_topological_group : topological_group G :=
{ continuous_mul := c.smooth_mul.continuous,
  continuous_inv := c.smooth_inv.continuous, }

@[to_additive]
protected lemma to_lie_group : @lie_group 𝕜 _ _ _ E _ _ I G _ _ c.to_topological_group _ :=
{ smooth_mul := c.smooth_mul,
  smooth_inv := c.smooth_inv, }

end lie_group_core

end lie_group_core

/-! ### Real numbers are a Lie group -/

section real_numbers_lie_group

instance normed_group_lie_group {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] :
lie_add_group (model_with_corners_self 𝕜 E) E :=
{ smooth_add :=
  begin
    rw smooth_iff,
    refine ⟨continuous_add, λ x y, _⟩,
    simp only [prod.mk.eta] with mfld_simps,
    rw times_cont_diff_on_univ,
    exact times_cont_diff_add,
  end,
  smooth_neg :=
  begin
    rw smooth_iff,
    refine ⟨continuous_neg, λ x y, _⟩,
    simp only [prod.mk.eta] with mfld_simps,
    rw times_cont_diff_on_univ,
    exact times_cont_diff_neg,
  end }

instance reals_lie_group : lie_add_group (model_with_corners_self ℝ ℝ) ℝ := by apply_instance

end real_numbers_lie_group
