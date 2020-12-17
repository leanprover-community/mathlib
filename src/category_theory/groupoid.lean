/-
Copyright (c) 2018 Reid Barton All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison, David Wärn
-/
import category_theory.epi_mono

namespace category_theory

universes v v₂ u u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

/-- A `groupoid` is a category such that all morphisms are isomorphisms. -/
class groupoid (obj : Type u) extends category.{v} obj : Type (max u (v+1)) :=
(inv       : Π {X Y : obj}, (X ⟶ Y) → (Y ⟶ X))
(inv_comp' : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y . obviously)
(comp_inv' : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X . obviously)

restate_axiom groupoid.inv_comp'
restate_axiom groupoid.comp_inv'

attribute [simp] groupoid.inv_comp groupoid.comp_inv

/--
A `large_groupoid` is a groupoid
where the objects live in `Type (u+1)` while the morphisms live in `Type u`.
-/
abbreviation large_groupoid (C : Type (u+1)) : Type (u+1) := groupoid.{u} C
/--
A `small_groupoid` is a groupoid
where the objects and morphisms live in the same universe.
-/
abbreviation small_groupoid (C : Type u) : Type (u+1) := groupoid.{u} C

section

variables {C : Type u} [groupoid.{v} C] {X Y : C}

@[priority 100] -- see Note [lower instance priority]
instance is_iso.of_groupoid (f : X ⟶ Y) : is_iso f := { inv := groupoid.inv f }

variables (X Y)

/-- In a groupoid, isomorphisms are equivalent to morphisms. -/
def groupoid.iso_equiv_hom : (X ≅ Y) ≃ (X ⟶ Y) :=
{ to_fun := iso.hom,
  inv_fun := λ f, as_iso f,
  left_inv := λ i, iso.ext rfl,
  right_inv := λ f, rfl }

end

section

variables {C : Type u} [category.{v} C]

/-- A category where every morphism `is_iso` is a groupoid. -/
def groupoid.of_is_iso (all_is_iso : ∀ {X Y : C} (f : X ⟶ Y), is_iso f) : groupoid.{v} C :=
{ inv := λ X Y f, (all_is_iso f).inv }

/-- A category where every morphism has a `trunc` retraction is computably a groupoid. -/
def groupoid.of_trunc_split_mono
  (all_split_mono : ∀ {X Y : C} (f : X ⟶ Y), trunc (split_mono f)) :
  groupoid.{v} C :=
begin
  apply groupoid.of_is_iso,
  intros X Y f,
  trunc_cases all_split_mono f,
  trunc_cases all_split_mono (retraction f),
  apply is_iso.of_mono_retraction,
end

end

instance induced_category.groupoid {C : Type u} (D : Type u₂) [groupoid.{v} D] (F : C → D) :
   groupoid.{v} (induced_category D F) :=
{ inv       := λ X Y f, groupoid.inv f,
  inv_comp' := λ X Y f, groupoid.inv_comp f,
  comp_inv' := λ X Y f, groupoid.comp_inv f,
  .. induced_category.category F }

end category_theory
