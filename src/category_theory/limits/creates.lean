/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.limits
import category_theory.limits.preserves
import category_theory.monad.adjunction
import category_theory.adjunction.limits
import category_theory.reflect_isomorphisms

open category_theory category_theory.limits

namespace category_theory

universes v u₁ u₂ u₃

variables {C : Type u₁} [𝒞 : category.{v} C]
include 𝒞

section creates
variables {D : Type u₂} [𝒟 : category.{v} D]
include 𝒟

variables {J : Type v} [small_category J] {K : J ⥤ C}

/--
Define the lift of a cone: For a cone `c` for `K ⋙ F`, give a cone for `K`
which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of limits:
every limit cone has a lift.

Note this definition is really only useful when `c` is a limit already.
-/
structure liftable_cone (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) :=
(lifted_cone : cone K)
(valid_lift : F.map_cone lifted_cone ≅ c)

structure liftable_cocone (K : J ⥤ C) (F : C ⥤ D) (c : cocone (K ⋙ F)) :=
(lifted_cocone : cocone K)
(valid_lift : F.map_cocone lifted_cocone ≅ c)

/--
Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone above, and further that `F` reflects
limits for `K`.

Note this is equivalent to Riehl's definition - the missing part here appears
to be that the lifted cone is not a limit, but the `extends reflects_limit K F`
is (proved in `lifted_limit_is_limit`).

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class creates_limit (K : J ⥤ C) (F : C ⥤ D) extends reflects_limit K F : Type (max u₁ u₂ v) :=
(lifts : Π c, is_limit c → liftable_cone K F c)

class creates_limits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(creates_limit : Π {K : J ⥤ C}, creates_limit K F)

class creates_limits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(creates_limits_of_shape : Π {J : Type v} {𝒥 : small_category J}, by exactI creates_limits_of_shape J F)

class creates_colimit (K : J ⥤ C) (F : C ⥤ D) extends reflects_colimit K F : Type (max u₁ u₂ v) :=
(lifts : Π c, is_colimit c → liftable_cocone K F c)

class creates_colimits_of_shape (J : Type v) [small_category J] (F : C ⥤ D) : Type (max u₁ u₂ v) :=
(creates_colimit : Π {K : J ⥤ C}, creates_colimit K F)

class creates_colimits (F : C ⥤ D) : Type (max u₁ u₂ (v+1)) :=
(creates_colimits_of_shape : Π {J : Type v} {𝒥 : small_category J}, by exactI creates_colimits_of_shape J F)

attribute [instance, priority 100] -- see Note [lower instance priority]
  creates_limits_of_shape.creates_limit creates_limits.creates_limits_of_shape
  creates_colimits_of_shape.creates_colimit creates_colimits.creates_colimits_of_shape

/- Interface to the `creates_limit` class. -/

def lift_limit {K : J ⥤ C} {F : C ⥤ D} [i : creates_limit K F] {c : cone (K ⋙ F)} (t : is_limit c) : cone K :=
(creates_limit.lifts c t).lifted_cone

def lifted_limit_maps_to_original {K : J ⥤ C} (F : C ⥤ D) [i : creates_limit K F] {c : cone (K ⋙ F)} (t : is_limit c) :
  F.map_cone (lift_limit t) ≅ c :=
(creates_limit.lifts c t).valid_lift

def lifted_limit_is_limit {K : J ⥤ C} {F : C ⥤ D} [i : creates_limit K F] {c : cone (K ⋙ F)} (t : is_limit c) :
  is_limit (lift_limit t) :=
reflects_limit.reflects (is_limit.of_iso_limit t (lifted_limit_maps_to_original F t).symm)

def has_limit_of_created (K : J ⥤ C) (F : C ⥤ D) [has_limit (K ⋙ F)] [creates_limit K F] : has_limit K :=
{ cone := lift_limit (limit.is_limit (K ⋙ F)),
  is_limit := lifted_limit_is_limit _ }

-- TODO: reflects iso is equivalent to reflecting limits of shape 1 (punit)

/--
A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
structure lifts_to_limit (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) (t : is_limit c) :=
(lifted : liftable_cone K F c)
(makes_limit : is_limit lifted.lifted_cone)

/--
If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
-/
def creates_limit_of_reflects_iso {K : J ⥤ C} {F : C ⥤ D} [reflects_isomorphisms F]
  (h : Π c t, lifts_to_limit K F c t) :
  creates_limit K F :=
{ lifts := λ c t, (h c t).lifted,
  to_reflects_limit :=
  { reflects := λ (d : cone K) (hd : is_limit (F.map_cone d)),
    begin
      let d' : cone K := (h (F.map_cone d) hd).lifted.lifted_cone,
      let hd'₁ : F.map_cone d' ≅ F.map_cone d := (h (F.map_cone d) hd).lifted.valid_lift,
      let hd'₂ : is_limit d' := (h (F.map_cone d) hd).makes_limit,
      let f : d ⟶ d' := hd'₂.lift_cone_morphism d,
      have: F.map_cone_morphism f = hd'₁.inv := (hd.of_iso_limit hd'₁.symm).uniq_cone_morphism,
      have: @is_iso _ cone.category _ _ (functor.map_cone_morphism F f),
        rw this, apply_instance,
      haveI: is_iso ((cones.functoriality F).map f) := this,
      haveI := is_iso_of_reflects_iso f (cones.functoriality F),
      exact is_limit.of_iso_limit hd'₂ (as_iso f).symm,
    end } }

def map_cone_map_cone_inv (F : J ⥤ D) (H : D ⥤ C) [is_equivalence H] (c : cone (F ⋙ H)) :
  functor.map_cone H (functor.map_cone_inv H c) ≅ c :=
begin
  apply cones.ext _ (λ j, _),
  exact (functor.as_equivalence H).counit_iso.app c.X,
  dsimp [functor.map_cone_inv, functor.as_equivalence, functor.inv],
  erw category.comp_id,
  erw ← H.inv_fun_id.hom.naturality (c.π.app j),
  rw functor.comp_map, rw H.map_comp,
  congr' 1,
  rw ← cancel_epi (H.inv_fun_id.inv.app (H.obj (F.obj j))),
  erw nat_iso.inv_hom_id_app,
  erw ← (functor.as_equivalence H).functor_unit _,
  erw ← H.map_comp,
  erw nat_iso.hom_inv_id_app,
  rw H.map_id, refl
end

@[priority 100] -- see Note [lower instance priority]
instance is_equivalence_creates_limits (H : D ⥤ C) [is_equivalence H] : creates_limits H :=
{ creates_limits_of_shape := λ J 𝒥, by exactI
  { creates_limit := λ F,
    { lifts := λ c t,
      { lifted_cone := H.map_cone_inv c,
        valid_lift := map_cone_map_cone_inv F H c } } } }

section comp

variables {E : Type u₃} [ℰ : category.{v} E]
variables (F : C ⥤ D) (G : D ⥤ E)

instance comp_creates_limit [i₁ : creates_limit K F] [i₂ : creates_limit (K ⋙ F) G] :
  creates_limit K (F ⋙ G) :=
{ lifts := λ c t,
  { lifted_cone := lift_limit (lifted_limit_is_limit t),
    valid_lift := (cones.functoriality G).map_iso (lifted_limit_maps_to_original F (lifted_limit_is_limit t)) ≪≫ (lifted_limit_maps_to_original G t),
  } }

end comp

end creates

end category_theory
