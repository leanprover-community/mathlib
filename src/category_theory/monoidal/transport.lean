/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.category

/-!
# Transport a monoidal structure along an equivalence.

When `C` and `D` are equivalent as categories,
we can transport a monoidal structure on `C` along the equivalence,
obtaining a monoidal structure on `D`.

We don't yet prove anything about this transported structure!
The next step would be to show that the original functor can be upgraded
to a monoidal functor with respect to this new structure.
-/

universes v₁ v₂ u₁ u₂

open category_theory
open category_theory.monoidal_category

namespace category_theory.monoidal

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

/--
Transport a monoidal structure along an equivalence of (plain) categories.
-/
def transport (e : C ≌ D) : monoidal_category.{v₂} D :=
{ tensor_obj := λ X Y, e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y),
  tensor_hom := λ W X Y Z f g, e.functor.map (e.inverse.map f ⊗ e.inverse.map g),
  tensor_unit := e.functor.obj (𝟙_ C),
  associator := λ X Y Z, e.functor.map_iso
  (((e.unit_iso.app _).symm ⊗ iso.refl _) ≪≫
    (α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z)) ≪≫
    (iso.refl _ ⊗ (e.unit_iso.app _))),
  left_unitor := λ X,
    e.functor.map_iso (((e.unit_iso.app _).symm ⊗ iso.refl _) ≪≫
      λ_ (e.inverse.obj X)) ≪≫ (e.counit_iso.app _),
  right_unitor := λ X,
    e.functor.map_iso ((iso.refl _ ⊗ (e.unit_iso.app _).symm) ≪≫
      ρ_ (e.inverse.obj X)) ≪≫ (e.counit_iso.app _),
  triangle' := λ X Y,
  begin
    dsimp,
    simp, -- This is a non-terminal simp, but squeeze_simp reports the wrong results!
    simp only [←e.functor.map_comp],
    congr' 2,
    slice_lhs 2 3 { rw [←id_tensor_comp], simp, dsimp, rw [tensor_id], },
    rw [category.id_comp, ←associator_naturality_assoc, triangle],
  end,
  pentagon' := λ W X Y Z,
  begin
    dsimp,
    simp, -- This is a non-terminal simp, but squeeze_simp reports the wrong results!
    simp only [←e.functor.map_comp],
    congr' 2,
    slice_lhs 4 5 { rw [←comp_tensor_id, iso.hom_inv_id_app], dsimp, rw [tensor_id], },
    simp only [category.id_comp, category.assoc],
    slice_lhs 5 6 { rw [←id_tensor_comp, iso.hom_inv_id_app], dsimp, rw [tensor_id], },
    simp only [category.id_comp, category.assoc],
    slice_rhs 2 3 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
    slice_rhs 1 2 { rw [←tensor_id, ←associator_naturality], },
    slice_rhs 3 4 { rw [←tensor_id, associator_naturality], },
    slice_rhs 2 3 { rw [←pentagon], },
    simp only [category.assoc],
    congr' 2,
    slice_lhs 1 2 { rw [associator_naturality], },
    simp only [category.assoc],
    congr' 1,
    slice_lhs 1 2
    { rw [←id_tensor_comp, ←comp_tensor_id, iso.hom_inv_id_app],
      dsimp, rw [tensor_id, tensor_id], },
    simp only [category.id_comp, category.assoc],
  end,
  left_unitor_naturality' := λ X Y f,
  begin
    dsimp,
    simp only [functor.map_comp, functor.map_id, category.assoc],
    erw ←e.counit_iso.hom.naturality,
    simp only [functor.comp_map, ←e.functor.map_comp_assoc],
    congr' 2,
    rw [e.inverse.map_id, id_tensor_comp_tensor_id_assoc, ←tensor_id_comp_id_tensor_assoc,
      left_unitor_naturality],
  end,
  right_unitor_naturality' := λ X Y f,
  begin
    dsimp,
    simp only [functor.map_comp, functor.map_id, category.assoc],
    erw ←e.counit_iso.hom.naturality,
    simp only [functor.comp_map, ←e.functor.map_comp_assoc],
    congr' 2,
    rw [e.inverse.map_id, tensor_id_comp_id_tensor_assoc, ←id_tensor_comp_tensor_id_assoc,
      right_unitor_naturality],
  end,
  associator_naturality' := λ X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃,
  begin
    dsimp,
    simp only [equivalence.inv_fun_map, functor.map_comp, category.assoc],
    simp only [←e.functor.map_comp],
    congr' 1,
    conv_lhs { rw [←tensor_id_comp_id_tensor] },
    slice_lhs 2 3 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor, ←tensor_id], },
    simp only [category.assoc],
    slice_lhs 3 4 { rw [associator_naturality], },
    conv_lhs { simp only [comp_tensor_id], },
    slice_lhs 3 4 { rw [←comp_tensor_id, iso.hom_inv_id_app], dsimp, rw [tensor_id], },
    simp only [category.id_comp, category.assoc],
    slice_lhs 2 3 { rw [associator_naturality], },
    simp only [category.assoc],
    congr' 2,
    slice_lhs 1 1 { rw [←tensor_id_comp_id_tensor], },
    slice_lhs 2 3 { rw [←id_tensor_comp, tensor_id_comp_id_tensor], },
    slice_lhs 1 2 { rw [tensor_id_comp_id_tensor], },
    conv_rhs { congr, skip, rw [←id_tensor_comp_tensor_id, id_tensor_comp], },
    simp only [category.assoc],
    slice_rhs 1 2 { rw [←id_tensor_comp, iso.hom_inv_id_app], dsimp, rw [tensor_id],},
    simp only [category.id_comp, category.assoc],
    conv_rhs { rw [id_tensor_comp], },
    slice_rhs 2 3 { rw [id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor], },
    slice_rhs 1 2 { rw [id_tensor_comp_tensor_id], },
  end, }

-- PROJECT:
-- We should show that `e.functor` can be upgraded to a (strong) monoidal functor.

-- Etingof-Gelaki-Nikshych-Ostrik "Tensor categories" define an equivalence of monoidal categories
-- as a monoidal functor which, as a functor, is an equivalence.
-- Presumably one can show that the inverse functor can be upgraded to a monoidal
-- functor in a unique way, such that the unit and counit are monoidal natural isomorphisms,
-- but I've never seen this explained or worked it out.

end category_theory.monoidal
