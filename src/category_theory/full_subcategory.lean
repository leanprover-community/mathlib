-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Reid Barton
import category_theory.fully_faithful

namespace category_theory

universes v u₁ u₂ -- declare the `v`'s first; see `category_theory.category` for an explanation

section induced

/- Induced categories.

  Given a category D and a function F : C → D from a type C to the
  objects of D, there is an essentially unique way to give C a
  category structure such that F becomes a fully faithful functor,
  namely by taking Hom_C(X, Y) = Hom_D(FX, FY). We call this the
  category induced from D along F.

  As a special case, if C is a subtype of D, this produces the full
  subcategory of D on the objects belonging to C. In general the
  induced category is equivalent to the full subcategory of D on the
  image of F.

-/

variables {C : Sort u₁} {D : Sort u₂} [𝒟 : category.{v u₂} D]
include 𝒟
variables (F : C → D)
include F

def induced_category : Sort u₁ := C

instance induced_category.category : category.{v} (induced_category F) :=
{ hom  := λ X Y, F X ⟶ F Y,
  id   := λ X, 𝟙 (F X),
  comp := λ _ _ _ f g, f ≫ g }

def induced_functor : induced_category F ⥤ D :=
{ obj := F, map := λ x y f, f }

@[simp] lemma induced_functor.obj {X} : (induced_functor F).obj X = F X := rfl
@[simp] lemma induced_functor.hom {X Y} {f : X ⟶ Y} : (induced_functor F).map f = f := rfl

instance induced_category.fully_faithful : fully_faithful (induced_functor F) :=
{ preimage := λ x y f, f }

end induced

section full_subcategory
/- A full subcategory is the special case of an induced category with F = subtype.val. -/

variables {C : Sort u₂} [𝒞 : category.{v} C]
include 𝒞
variables (Z : C → Prop)

instance full_subcategory : category.{v} {X : C // Z X} :=
induced_category.category subtype.val

def full_subcategory_inclusion : {X : C // Z X} ⥤ C :=
induced_functor subtype.val

@[simp] lemma full_subcategory_inclusion.obj {X} :
  (full_subcategory_inclusion Z).obj X = X.val := rfl
@[simp] lemma full_subcategory_inclusion.map {X Y} {f : X ⟶ Y} :
  (full_subcategory_inclusion Z).map f = f := rfl

instance full_subcategory.fully_faithful : fully_faithful (full_subcategory_inclusion Z) :=
induced_category.fully_faithful subtype.val

end full_subcategory

end category_theory
