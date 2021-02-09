/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.shift
import category_theory.concrete_category

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, and zero morphisms and zero objects.
-/

open category_theory.limits

universes v u

namespace category_theory

variables (C : Type u) [category.{v} C]

variables [has_zero_morphisms C] [has_shift C]

/--
A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.
-/
@[nolint has_inhabited_instance]
structure differential_object :=
(X : C)
(d : X ⟶ X⟦1⟧)
(d_squared' : d ≫ d⟦1⟧' = 0 . obviously)

restate_axiom differential_object.d_squared'
attribute [simp] differential_object.d_squared

variables {C}

namespace differential_object

/--
A morphism of differential objects is a morphism commuting with the differentials.
-/
@[ext, nolint has_inhabited_instance]
structure hom (X Y : differential_object C) :=
(f : X.X ⟶ Y.X)
(comm' : X.d ≫ f⟦1⟧' = f ≫ Y.d . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc] hom.comm

namespace hom

/-- The identity morphism of a differential object. -/
@[simps]
def id (X : differential_object C) : hom X X :=
{ f := 𝟙 X.X }

/-- The composition of morphisms of differential objects. -/
@[simps]
def comp {X Y Z : differential_object C} (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ f := f.f ≫ g.f, }

end hom

instance category_of_differential_objects : category (differential_object C) :=
{ hom := hom,
  id := hom.id,
  comp := λ X Y Z f g, hom.comp f g, }

@[simp]
lemma id_f (X : differential_object C) : ((𝟙 X) : X ⟶ X).f = 𝟙 (X.X) := rfl

@[simp]
lemma comp_f {X Y Z : differential_object C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g).f = f.f ≫ g.f :=
rfl

variables (C)

/-- The forgetful functor taking a differential object to its underlying object. -/
def forget : (differential_object C) ⥤ C :=
{ obj := λ X, X.X,
  map := λ X Y f, f.f, }

instance forget_faithful : faithful (forget C) :=
{ }

instance has_zero_morphisms : has_zero_morphisms (differential_object C) :=
{ has_zero := λ X Y,
  ⟨{ f := 0, }⟩}

variables {C}

@[simp]
lemma zero_f (P Q : differential_object C) : (0 : P ⟶ Q).f = 0 := rfl

/--
An isomorphism of differential objects gives an isomorphism of the underlying objects.
-/
@[simps] def iso_app {X Y : differential_object C} (f : X ≅ Y) : X.X ≅ Y.X :=
⟨f.hom.f, f.inv.f, by { dsimp, rw [← comp_f, iso.hom_inv_id, id_f] },
  by { dsimp, rw [← comp_f, iso.inv_hom_id, id_f] }⟩

@[simp] lemma iso_app_refl (X : differential_object C) : iso_app (iso.refl X) = iso.refl X.X := rfl
@[simp] lemma iso_app_symm {X Y : differential_object C} (f : X ≅ Y) :
  iso_app f.symm = (iso_app f).symm := rfl
@[simp] lemma iso_app_trans {X Y Z : differential_object C} (f : X ≅ Y) (g : Y ≅ Z) :
  iso_app (f ≪≫ g) = iso_app f ≪≫ iso_app g := rfl

end differential_object

namespace functor

universes v' u'
variables (D : Type u') [category.{v'} D]
variables [has_zero_morphisms D] [has_shift D]

/--
A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and preserves zero morphisms
can be lifted to a functor `differential_object C ⥤ differential_object D`.
-/
@[simps]
def map_differential_object (F : C ⥤ D) (η : (shift C).functor.comp F ⟶ F.comp (shift D).functor)
  (hF : ∀ c c', F.map (0 : c ⟶ c') = 0) :
  differential_object C ⥤ differential_object D :=
{ obj := λ X, { X := F.obj X.X,
    d := F.map X.d ≫ η.app X.X,
    d_squared' := begin
      dsimp, rw [functor.map_comp, ← functor.comp_map F (shift D).functor],
      slice_lhs 2 3 { rw [← η.naturality X.d] },
      rw [functor.comp_map],
      slice_lhs 1 2 { rw [← F.map_comp, X.d_squared, hF] },
      rw [zero_comp, zero_comp],
    end },
  map := λ X Y f, { f := F.map f.f,
    comm' := begin
      dsimp,
      slice_lhs 2 3 { rw [← functor.comp_map F (shift D).functor, ← η.naturality f.f] },
      slice_lhs 1 2 { rw [functor.comp_map, ← F.map_comp, f.comm, F.map_comp] },
      rw [category.assoc]
    end },
  map_id' := by { intros, ext, simp },
  map_comp' := by { intros, ext, simp }, }

end functor

end category_theory

namespace category_theory

namespace differential_object

variables (C : Type u) [category.{v} C]

variables [has_zero_object C] [has_zero_morphisms C] [has_shift C]

local attribute [instance] has_zero_object.has_zero

instance has_zero_object : has_zero_object (differential_object C) :=
{ zero :=
  { X := (0 : C),
    d := 0, },
  unique_to := λ X, ⟨⟨{ f := 0 }⟩, λ f, (by ext)⟩,
  unique_from := λ X, ⟨⟨{ f := 0 }⟩, λ f, (by ext)⟩, }

end differential_object

namespace differential_object

variables (C : Type (u+1)) [large_category C] [concrete_category C]
  [has_zero_morphisms C] [has_shift C]

instance concrete_category_of_differential_objects :
  concrete_category (differential_object C) :=
{ forget := forget C ⋙ category_theory.forget C }

instance : has_forget₂ (differential_object C) C :=
{ forget₂ := forget C }

end differential_object

end category_theory
