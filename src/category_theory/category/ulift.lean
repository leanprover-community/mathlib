/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.category
import category_theory.equivalence
import category_theory.filtered

/-!
# Basic API for ulift

This file contains a very basic API for working with the categorical
instance on `ulift C` where `C` is a type with a category instance.

1. `category_theory.ulift.up` is the functorial version of the usual `ulift.up`.
2. `category_theory.ulift.down` is the functorial version of the usual `ulift.down`.
3. `category_theory.ulift.equivalence` is the categorical equivalence between
  `C` and `ulift C`.
-/

universes v u1 u2

namespace category_theory

variables {C : Type u1} [category.{v} C]

/-- The functorial version of `ulift.up`. -/
@[simps]
def ulift.up : C ⥤ (ulift.{u2} C) :=
{ obj := ulift.up,
  map := λ X Y f, f }

/-- The functorial version of `ulift.down`. -/
@[simps]
def ulift.down : (ulift.{u2} C) ⥤ C :=
{ obj := ulift.down,
  map := λ X Y f, f }

/-- The categorical equivalence between `C` and `ulift C`. -/
@[simps]
def ulift.equivalence : C ≌ (ulift.{u2} C) :=
{ functor := ulift.up,
  inverse := ulift.down,
  unit_iso :=
  { hom := 𝟙 _,
    inv := 𝟙 _ },
  counit_iso :=
  { hom :=
    { app := λ X, 𝟙 _,
      naturality' := λ X Y f, by {change f ≫ 𝟙 _ = 𝟙 _ ≫ f, simp} },
    inv :=
    { app := λ X, 𝟙 _,
      naturality' := λ X Y f, by {change f ≫ 𝟙 _ = 𝟙 _ ≫ f, simp} },
  hom_inv_id' := by {ext, change (𝟙 _) ≫ (𝟙 _) = 𝟙 _, simp},
  inv_hom_id' := by {ext, change (𝟙 _) ≫ (𝟙 _) = 𝟙 _, simp} },
  functor_unit_iso_comp' := λ X, by {change (𝟙 X) ≫ (𝟙 X) = 𝟙 X, simp} }

instance [is_filtered C] : is_filtered (ulift.{u2} C) :=
is_filtered.of_equivalence ulift.equivalence

instance [is_cofiltered C] : is_cofiltered (ulift.{u2} C) :=
is_cofiltered.of_equivalence ulift.equivalence

variable (C)
/-- `as_small C` is a small category equivalent to `C`.-/
@[nolint unused_arguments]
def as_small := ulift.{v} C
variable {C}

instance : small_category (as_small C) :=
{ hom := λ X Y, ulift.{u1} $ X.down ⟶ Y.down,
  id := λ X, ⟨𝟙 _⟩,
  comp := λ X Y Z f g, ⟨f.down ≫ g.down⟩ }

/-- One half of the equivalence between `C` and `as_small C`. -/
@[simps]
def as_small.up : C ⥤ as_small C :=
{ obj := λ X, ⟨X⟩,
  map := λ X Y f, ⟨f⟩ }

/-- One half of the equivalence between `C` and `as_small C`. -/
@[simps]
def as_small.down : as_small C ⥤ C :=
{ obj := λ X, X.down,
  map := λ X Y f, f.down }

/-- The equivalence between `C` and `as_small C`. -/
@[simps]
def as_small.equiv : C ≌ as_small C :=
{ functor := as_small.up,
  inverse := as_small.down,
  unit_iso := nat_iso.of_components (λ X, eq_to_iso rfl) (by tidy),
  counit_iso := nat_iso.of_components (λ X, eq_to_iso $ by { ext, refl }) (by tidy) }

instance [inhabited C] : inhabited (as_small C) := ⟨⟨arbitrary _⟩⟩

instance [is_filtered C] : is_filtered (as_small C) :=
is_filtered.of_equivalence as_small.equiv

instance [is_cofiltered C] : is_cofiltered (as_small C) :=
is_cofiltered.of_equivalence as_small.equiv

end category_theory
