/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.internal.functor_category
import category_theory.monoidal.limits

/-!
# Limits of monoid objects.

If `C` has limits, so does `Mon_ C`.

(This could potentially replace many individual constructions for concrete categories,
in particular `Mon`, `SemiRing`, `Ring`, and `Algebra R`.)
-/

open category_theory
open category_theory.limits
open category_theory.monoidal

universes v u

noncomputable theory

namespace Mon_

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v} C] [has_limits C] [monoidal_category.{v} C]

/--
We construct the (candidate) limit of a functor `F : J ⥤ Mon_ C`
by interpreting it as a functor `Mon_ (J ⥤ C)`,
and noting that taking limits is a lax monoidal functor,
and hence sends monoid objects to monoid objects.
-/
@[simps {rhs_md:=semireducible}]
def limit (F : J ⥤ Mon_ C) : Mon_ C :=
lim_lax.map_Mon.obj (Mon_functor_category_equivalence.inverse.obj F)

/--
Implementation of `Mon_.has_limits`: a limiting cone over a functor `F : J ⥤ Mon_ C`.
-/
@[simps]
def limit_cone (F : J ⥤ Mon_ C) : cone F :=
{ X := limit F,
  π :=
  { app := λ j, { hom := limit.π (F ⋙ Mon_.forget) j, },
    naturality' := λ j j' f, by { ext, exact (limit.cone (F ⋙ Mon_.forget)).π.naturality f, } } }

/--
Implementation of `Mon_.has_limits`:
the proposed cone over a functor `F : J ⥤ Mon_ C` is a limit cone.
-/
@[simps]
def limit_cone_is_limit (F : J ⥤ Mon_ C) : is_limit (limit_cone F) :=
{ lift := λ s,
  { hom := limit.lift (F ⋙ Mon_.forget) (Mon_.forget.map_cone s),
    mul_hom' :=
    begin
      ext, dsimp, simp, dsimp,
      slice_rhs 1 2 { rw [←monoidal_category.tensor_comp, limit.lift_π], dsimp, }
    end },
  fac' := λ s h, by { ext, simp, },
  uniq' := λ s m w,
  begin
    ext,
    dsimp, simp only [Mon_.forget_map, limit.lift_π, functor.map_cone_π],
    exact congr_arg Mon_.hom.hom (w j),
  end, }

instance has_limits : has_limits (Mon_ C) :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk
    { cone     := limit_cone F,
      is_limit := limit_cone_is_limit F } } }

end Mon_
