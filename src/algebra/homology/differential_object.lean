/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homological_complex
import category_theory.differential_object

/-!
# Homological complexes are differential graded objects.

We verify that a `homological_complex` indexed by an `add_comm_group` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/

open category_theory
open category_theory.limits

open_locale classical
noncomputable theory

namespace homological_complex

variables {β : Type*} [add_comm_group β] (b : β)
variables (V : Type*) [category V] [has_zero_morphisms V]

@[simp, reassoc] lemma eq_to_hom_d (X : differential_object (graded_object_with_shift b V))
  {x y : β} (h : x = y) :
  eq_to_hom (congr_arg X.X h) ≫ X.d y = X.d x ≫ eq_to_hom (by { cases h, refl }) :=
by { cases h, simp }

@[simp, reassoc] lemma d_eq_to_hom (X : homological_complex V (complex_shape.up' b))
  {x y z : β} (h : y = z) :
  X.d x y ≫ eq_to_hom (by { cases h, refl }) = X.d x z :=
by { cases h, simp }

@[simp, reassoc] lemma eq_to_hom_f {X Y : differential_object (graded_object_with_shift b V)}
  (f : X ⟶ Y) {x y : β} (h : x = y) :
  eq_to_hom (congr_arg X.X h) ≫ f.f y = f.f x ≫ eq_to_hom (by { cases h, refl }) :=
by { cases h, simp }

/--
The functor from differential graded objects to homological complexes.
-/
@[simps]
def dgo_to_homological_complex :
  differential_object (graded_object_with_shift b V) ⥤
    homological_complex V (complex_shape.up' b) :=
{ obj := λ X,
  { X := λ i, X.X i,
    d := λ i j, if h : i + b = j then X.d i ≫
      eq_to_hom (congr_arg X.X (show i + (1 : ℤ) • b = j, by simp [h])) else 0,
    shape' := λ i j w, by { dsimp at w, rw dif_neg w, },
    d_comp_d' := λ i j k hij hjk, begin
      dsimp at hij hjk, substs hij hjk,
      have : X.d i ≫ X.d (i + 1 • b) = 0 := congr_fun (X.d_squared) i,
      reassoc! this,
      simp only [category.comp_id, eq_to_hom_refl, dif_pos rfl, category.assoc,
        eq_to_hom_d_assoc, eq_to_hom_trans, this, zero_comp]
    end },
  map := λ X Y f,
  { f := f.f,
    comm' := λ i j h, begin
      dsimp at h ⊢,
      subst h,
      have : f.f i ≫ Y.d i = X.d i ≫ f.f (i + 1 • b) := (congr_fun f.comm i).symm,
      reassoc! this,
      simp only [category.comp_id, eq_to_hom_refl, dif_pos rfl, this, category.assoc, eq_to_hom_f]
    end, } }

/--
The functor from homological complexes to differential graded objects.
-/
@[simps]
def homological_complex_to_dgo :
  homological_complex V (complex_shape.up' b) ⥤
    differential_object (graded_object_with_shift b V) :=
{ obj := λ X,
  { X := λ i, X.X i,
    d := λ i, X.d i (i + 1 • b),
    d_squared' := by { ext i, dsimp, simp, } },
  map := λ X Y f,
  { f := f.f,
    comm' := by { ext i, dsimp, simp, }, } }

/--
The unit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_unit_iso :
  𝟭 (differential_object (graded_object_with_shift b V)) ≅
    dgo_to_homological_complex b V ⋙ homological_complex_to_dgo b V :=
nat_iso.of_components (λ X,
  { hom := { f := λ i, 𝟙 (X.X i), },
    inv := { f := λ i, 𝟙 (X.X i), }, }) (by tidy)

/--
The counit isomorphism for `dgo_equiv_homological_complex`.
-/
@[simps]
def dgo_equiv_homological_complex_counit_iso :
  homological_complex_to_dgo b V ⋙ dgo_to_homological_complex b V ≅
    𝟭 (homological_complex V (complex_shape.up' b)) :=
nat_iso.of_components (λ X,
  { hom :=
    { f := λ i, 𝟙 (X.X i),
      comm' := λ i j h, begin
        dsimp at h ⊢, subst h,
        simp only [category.comp_id, category.id_comp, dif_pos rfl, eq_to_hom_refl],
        erw d_eq_to_hom,
        simp
      end },
    inv :=
    { f := λ i, 𝟙 (X.X i),
      comm' := λ i j h, begin
        dsimp at h ⊢, subst h,
        simp only [category.comp_id, category.id_comp, dif_pos rfl, eq_to_hom_refl],
        erw d_eq_to_hom,
        simp
      end }, }) (by tidy)

/--
The category of differential graded objects in `V` is equivalent
to the category of homological complexes in `V`.
-/
@[simps]
def dgo_equiv_homological_complex :
  differential_object (graded_object_with_shift b V) ≌
    homological_complex V (complex_shape.up' b) :=
{ functor := dgo_to_homological_complex b V,
  inverse := homological_complex_to_dgo b V,
  unit_iso := dgo_equiv_homological_complex_unit_iso b V,
  counit_iso := dgo_equiv_homological_complex_counit_iso b V, }

end homological_complex
