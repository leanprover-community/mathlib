/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.presheafed_space
import topology.sheaves.stalks

/-!
# Stalks for presheaved spaces

This file lifts constructions of stalks and pushforwards of stalks to work with
the category of presheafed spaces.
-/

noncomputable theory

universes v u v' u'

open category_theory
open category_theory.limits category_theory.category category_theory.functor
open algebraic_geometry
open topological_space
open opposite

variables {C : Type u} [category.{v} C] [has_colimits C]

local attribute [tidy] tactic.op_induction'

open Top.presheaf

namespace algebraic_geometry.PresheafedSpace

/--
The stalk at `x` of a `PresheafedSpace`.
-/
def stalk (X : PresheafedSpace C) (x : X) : C := X.presheaf.stalk x

/--
A morphism of presheafed spaces induces a morphism of stalks.
-/
def stalk_map {X Y : PresheafedSpace C} (α : X ⟶ Y) (x : X) : Y.stalk (α.base x) ⟶ X.stalk x :=
(stalk_functor C (α.base x)).map (α.c) ≫ X.presheaf.stalk_pushforward C α.base x

@[simp, elementwise, reassoc]
lemma stalk_map_germ {X Y : PresheafedSpace C} (α : X ⟶ Y) (U : opens Y.carrier)
  (x : (opens.map α.base).obj U) :
  Y.presheaf.germ ⟨α.base x, x.2⟩ ≫ stalk_map α ↑x = α.c.app (op U) ≫ X.presheaf.germ x :=
by rw [stalk_map, stalk_functor_map_germ_assoc, stalk_pushforward_germ]

section restrict

-- PROJECT: restriction preserves stalks.
-- We'll want to define cofinal functors, show precomposing with a cofinal functor preserves
-- colimits, and (easily) verify that "open neighbourhoods of x within U" is cofinal in "open
-- neighbourhoods of x".
/-
def restrict_stalk_iso {U : Top} (X : PresheafedSpace C)
  (f : U ⟶ (X : Top.{v})) (h : open_embedding f) (x : U) :
  (X.restrict f h).stalk x ≅ X.stalk (f x) :=
begin
  dsimp only [stalk, Top.presheaf.stalk, stalk_functor],
  dsimp [colim],
  sorry
end

-- TODO `restrict_stalk_iso` is compatible with `germ`.
-/

end restrict

namespace stalk_map

@[simp] lemma id (X : PresheafedSpace C) (x : X) : stalk_map (𝟙 X) x = 𝟙 (X.stalk x) :=
begin
  dsimp [stalk_map],
  simp only [stalk_pushforward.id],
  rw [←map_comp],
  convert (stalk_functor C x).map_id X.presheaf,
  tidy,
end

-- TODO understand why this proof is still gross (i.e. requires using `erw`)
@[simp] lemma comp {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
  stalk_map (α ≫ β) x =
    (stalk_map β (α.base x) : Z.stalk (β.base (α.base x)) ⟶ Y.stalk (α.base x)) ≫
    (stalk_map α x : Y.stalk (α.base x) ⟶ X.stalk x) :=
begin
  dsimp [stalk_map, stalk_functor, stalk_pushforward],
  ext U,
  op_induction U,
  cases U,
  simp only [colimit.ι_map_assoc, colimit.ι_pre_assoc, colimit.ι_pre,
    whisker_left_app, whisker_right_app,
    assoc, id_comp, map_id, map_comp],
  dsimp,
  simp only [map_id, assoc, pushforward.comp_inv_app],
  -- FIXME Why doesn't simp do this:
  erw [category_theory.functor.map_id],
  erw [category_theory.functor.map_id],
  erw [id_comp, id_comp, id_comp],
end

lemma congr {X Y : PresheafedSpace C} (α β : X ⟶ Y) (h₁ : α = β)
  (x x': X) (h₂ : x = x') :
    stalk_map α x ≫ eq_to_hom (show X.stalk x = X.stalk x', by rw h₂) =
    eq_to_hom (show Y.stalk (α.base x) = Y.stalk (β.base x'), by rw [h₁, h₂]) ≫ stalk_map β x' :=
stalk_hom_ext _ $ λ U hx, by { subst h₁, subst h₂, simp }

lemma congr_hom {X Y : PresheafedSpace C} (α β : X ⟶ Y) (h : α = β) (x : X) :
  stalk_map α x =
    eq_to_hom (show Y.stalk (α.base x) = Y.stalk (β.base x), by rw h) ≫ stalk_map β x :=
by rw [← stalk_map.congr α β h x x rfl, eq_to_hom_refl, category.comp_id]

lemma congr_point {X Y : PresheafedSpace C} (α : X ⟶ Y) (x x' : X) (h : x = x') :
  stalk_map α x ≫ eq_to_hom (show X.stalk x = X.stalk x', by rw h) =
  eq_to_hom (show Y.stalk (α.base x) = Y.stalk (α.base x'), by rw h) ≫ stalk_map α x' :=
by rw stalk_map.congr α α rfl x x' h

instance is_iso {X Y : PresheafedSpace C} (α : X ⟶ Y) [is_iso α] (x : X) :
  is_iso (stalk_map α x) :=
{ out := begin
  let β : Y ⟶ X := category_theory.inv α,
  -- Intuitively, the inverse of the stalk map of `α` at `x` should just be the stalk map of `β`
  -- at `α x`. Unfortunately, we have a problem with dependent type theory here, because `x`
  -- is not *definitionally* equal to `β (α x)`. Hence we need to introduce an `eq_to_hom` arrow.
  have h_eq : (α ≫ β).base x = x,
  { rw [is_iso.hom_inv_id α, id_base, Top.id_app] },
  -- To get the inverse of `stalk_map α x`, we start with an eq_to_hom arrow
  -- `X.stalk x ⟶ X.stalk ((α ≫ β).base x)` and then compose with `stalk_map β (α.base x)`.
  refine ⟨eq_to_hom (show X.stalk x = X.stalk ((α ≫ β).base x), by rw h_eq) ≫
    (stalk_map β (α.base x) : _), _, _⟩,
  { rw [← category.assoc, congr_point α x ((α ≫ β).base x) h_eq.symm, category.assoc],
    erw ← stalk_map.comp β α (α.base x),
    rw [congr_hom _ _ (is_iso.inv_hom_id α), stalk_map.id, eq_to_hom_trans_assoc,
      eq_to_hom_refl, category.id_comp] },
  { rw [category.assoc, ← stalk_map.comp, congr_hom _ _ (is_iso.hom_inv_id α),
    stalk_map.id, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp] },
end }

/--
An isomorphism between presheafed spaces induces an isomorphism of stalks.
-/
def stalk_iso {X Y : PresheafedSpace C} (α : X ≅ Y) (x : X) :
  Y.stalk (α.hom.base x) ≅ X.stalk x :=
as_iso (stalk_map α.hom x)

end stalk_map

end algebraic_geometry.PresheafedSpace
