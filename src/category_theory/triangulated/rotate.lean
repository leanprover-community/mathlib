/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
import category_theory.additive.basic
import category_theory.shift
import category_theory.abelian.additive_functor
import category_theory.natural_isomorphism
import category_theory.triangulated.basic

/-!
# Rotate

This file adds the ability to rotate triangles and triangle morphisms.
It also shows that rotation gives an equivalence on the category of triangles.

-/

noncomputable theory

open category_theory
open category_theory.preadditive
open category_theory.limits

universes v v₀ v₁ v₂ u u₀ u₁ u₂

namespace category_theory.triangulated
open category_theory.category

/--
We work in an additive category C equipped with an additive shift.
-/
variables (C : Type u) [category.{v} C] [has_shift C] [additive_category C]
[functor.additive (shift C).functor]
variables (X : C)

/--
If you rotate a triangle, you get another triangle.
-/
@[simps]
def triangle.rotate (T : triangle C) : triangle C :=
{ obj1 := T.obj2,
  obj2 := T.obj3,
  obj3 := T.obj1⟦1⟧,
  mor1 := T.mor2,
  mor2 := T.mor3,
  mor3 := T.mor1⟦1⟧' }

@[simps]
def triangle.inv_rotate (T : triangle C) : triangle C :=
{ obj1 := T.obj3⟦-1⟧,
  obj2 := T.obj1,
  obj3 := T.obj2,
  mor1 := T.mor3⟦-1⟧' ≫ (shift C).unit_iso.inv.app T.obj1,
  mor2 := T.mor1,
  mor3 := T.mor2 ≫ (shift C).counit_iso.inv.app T.obj3}



namespace triangle_morphism
variables {T₁ T₂ T₃ T₄: triangle C}
/--
You can also rotate a triangle morphism to get a morphism between the two rotated triangles.
-/
@[simps]
def rotate (f : triangle_morphism T₁ T₂)
: triangle_morphism (T₁.rotate C) (T₂.rotate C):=
{ trimor1 := f.trimor2,
  trimor2 := f.trimor3,
  trimor3 := f.trimor1⟦1⟧',
  comm1 := by exact f.comm2,
  comm2 := by exact f.comm3,
  comm3 := begin
    repeat {rw triangle.rotate_mor3},
    repeat {rw ← functor.map_comp},
    rw f.comm1,
  end }

@[simps]
def inv_rotate (f : triangle_morphism T₁ T₂)
: triangle_morphism (T₁.inv_rotate C) (T₂.inv_rotate C) :=
{ trimor1 := f.trimor3⟦-1⟧',
  trimor2 := f.trimor1,
  trimor3 := f.trimor2,
  comm1 := begin
    simp only [triangle.inv_rotate_mor1],
    rw ← assoc,
    dsimp,
    rw ← functor.map_comp (shift C ).inverse,
    rw ← f.comm3,
    rw functor.map_comp,
    repeat {rw assoc},
    suffices h : (shift C).unit_iso.inv.app T₁.obj1 ≫ f.trimor1 = (shift C).inverse.map ((shift C).functor.map f.trimor1) ≫ (shift C).unit_iso.inv.app T₂.obj1,
    {
      rw h,
      refl,
    },
    {
      simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map, nat_iso.cancel_nat_iso_inv_left],
      exact (category.comp_id f.trimor1).symm,
    }
  end,
  comm2 := by exact f.comm1,
  comm3 := begin
    have h := f.comm2,
    repeat {rw triangle.inv_rotate_mor3},
    rw ← assoc f.trimor2 _,
    rw ← f.comm2,
    dsimp,
    repeat {rw assoc},
    simp only [equivalence.fun_inv_map, iso.inv_hom_id_app_assoc],
  end }

end triangle_morphism

/--
Rotating triangles gives an endofunctor on the category of triangles in C.
-/
@[simps]
def rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.rotate C,
  map := λ _ _ f, f.rotate C,
  map_id' := begin
    intro T₁,
    simp only [triangulated.triangle_category_to_category_struct_id],
    unfold triangle_morphism.rotate,
    dsimp,
    ext,
    { refl },
    { refl },
    {
      simp only [triangulated.triangle_morphism_id_trimor3, (shift C).functor.map_id],
      refl,
    }
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    unfold triangle_morphism.rotate,
    ext,
    { refl },
    { refl },
    {
      dsimp,
      rw (shift C).functor.map_comp,
    }
  end
}

@[simps]
def inv_rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.inv_rotate C,
  map := λ _ _ f, f.inv_rotate C,
  map_id' := begin
    intro T₁,
    simp only [triangulated.triangle_category_to_category_struct_id],
    ext,
    {
      simp only [triangulated.triangle_morphism_id_trimor3, triangle_morphism.inv_rotate_trimor1,
      triangulated.triangle_morphism_id_trimor1],
      dsimp,
      rw (shift C).inverse.map_id,
    },
    { refl },
    { refl }
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    unfold triangle_morphism.inv_rotate,
    ext,
    {
      simp only [triangulated.triangle_morphism.comp_trimor3,
      triangulated.triangle_morphism.comp_trimor1,
      triangulated.triangle_category_to_category_struct_comp, functor.map_comp],
    },
    { refl },
    { refl }
  end
}

-- Separated parts of the equivalence to avoid deterministic timeout
@[simps]
def rot_comp_inv_rot_hom : 𝟭 (triangle C) ⟶ (rotate C) ⋙ (inv_rotate C) :=
{
  app := begin
    intro T,
    rw functor.id_obj,
    rw functor.comp_obj,
    let f : triangle_morphism T ((inv_rotate C).obj ((rotate C).obj T)) :=
    {
      trimor1 := (shift C).unit.app T.obj1,
      trimor2 := 𝟙 T.obj2,
      trimor3 := 𝟙 T.obj3,
      comm1 := begin
        rw comp_id,
        dsimp,
        rw ← functor.comp_map,
        rw nat_iso.naturality_2 (shift C).unit_iso T.mor1,
        exact functor.id_map T.mor1,
      end,
      comm2 := by {rw [id_comp, comp_id], refl},
      comm3 := begin
        rw id_comp,
        dsimp,
        rw equivalence.counit_inv_app_functor,
      end
    },
    exact f,
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp only [functor.id_obj, congr_arg_mpr_hom_left, functor.id_map, functor.comp_map,
    id_comp, eq_to_hom_refl, congr_arg_mpr_hom_right, comp_id, functor.comp_obj],
    ext,
    {
      dsimp,
      simp only [iso.hom_inv_id_app_assoc, equivalence.inv_fun_map],
    },
    {
      dsimp,
      simp only [id_comp, comp_id],
    },
    {
      dsimp,
      simp only [id_comp, comp_id],
    },
  end
}

@[simps]
def rot_comp_inv_rot_inv : (rotate C) ⋙ (inv_rotate C) ⟶ 𝟭 (triangle C) :=
{
  app := begin
    intro T,
    rw [functor.id_obj, functor.comp_obj],
    let f : triangle_morphism ((inv_rotate C).obj ((rotate C).obj T)) T :=
    {
      trimor1 := (shift C).unit_inv.app T.obj1,
      trimor2 := 𝟙 T.obj2,
      trimor3 := 𝟙 T.obj3,
      comm1 := begin
        dsimp,
        simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map,
        nat_iso.cancel_nat_iso_inv_left],
        dsimp,
        simp only [comp_id],
      end,
      comm2 := begin
        dsimp,
        simp only [id_comp, comp_id],
      end,
      comm3 := begin
        dsimp,
        simp only [equivalence.counit_inv_functor_comp, assoc, id_comp, comp_id],
      end
    },
    exact f,
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp only [functor.id_obj, congr_arg_mpr_hom_left, functor.id_map, functor.comp_map,
    id_comp, eq_to_hom_refl, congr_arg_mpr_hom_right, comp_id, functor.comp_obj],
    dsimp,
    ext,
    {
      simp only [triangulated.triangle_morphism.comp_trimor1,
      triangle_morphism.inv_rotate_trimor1, triangle_morphism.rotate_trimor3],
      dsimp,
      simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map,
      nat_iso.cancel_nat_iso_inv_left],
      dsimp,
      simp only [comp_id],
    },
    {
      simp only [triangulated.triangle_morphism.comp_trimor2,
      triangle_morphism.inv_rotate_trimor2, triangle_morphism.rotate_trimor1,
      comp_id f.trimor2, id_comp f.trimor2],
    },
    {
      simp only [triangulated.triangle_morphism.comp_trimor3, triangle_morphism.rotate_trimor2, triangle_morphism.inv_rotate_trimor3, comp_id f.trimor3, id_comp f.trimor3],
    },
  end
}

def rot_comp_inv_rot :𝟭 (triangle C) ≅ (rotate C) ⋙ (inv_rotate C) :=
{
  hom := rot_comp_inv_rot_hom C,
  inv := rot_comp_inv_rot_inv C,
  hom_inv_id' := begin
    ext T,
    {
      simp only [functor.id_obj, congr_arg_mpr_hom_left,
      triangulated.triangle_morphism.comp_trimor1,
      triangulated.triangle_category_to_category_struct_comp, rot_comp_inv_rot_inv_app,
      rot_comp_inv_rot_hom_app, iso.hom_inv_id_app, triangulated.triangle_morphism.id_comp,
      nat_trans.id_app, triangulated.triangle_category_to_category_struct_id,
      triangulated.triangle_morphism_id_trimor1, eq_to_hom_refl, congr_arg_mpr_hom_right,
      triangulated.triangle_morphism.comp_id, functor.comp_obj, nat_trans.comp_app],
      dsimp,
      refl,
    },
    {
      simp only [functor.id_obj, congr_arg_mpr_hom_left,
      triangulated.triangle_category_to_category_struct_comp, rot_comp_inv_rot_inv_app,
      triangulated.triangle_morphism.comp_trimor2, rot_comp_inv_rot_hom_app,
      triangulated.triangle_morphism.id_comp, nat_trans.id_app,
      triangulated.triangle_category_to_category_struct_id,
      triangulated.triangle_morphism_id_trimor2, eq_to_hom_refl, congr_arg_mpr_hom_right,
      triangulated.triangle_morphism.comp_id, functor.comp_obj, nat_trans.comp_app],
      dsimp,
      simp only [comp_id],
    },
    {
      simp,
      dsimp,
      simp only [comp_id],
      -- sorry,
    }
  end, -- (deterministic) timeout when replace simp with squeeze_simp
  inv_hom_id' := begin
    ext T,
    {
      simp,
      dsimp,
      refl,
      -- sorry,
    },
    {
      simp,
      dsimp,
      simp only [comp_id],
      -- sorry,
    },
    {
      simp,
      dsimp,
      simp only [comp_id],
      -- sorry,
    }
  end -- (deterministic) timeout when replace simp with squeeze_simp
}



/--
Rotating triangles gives an auto-equivalence on the category of triangles.
-/
def triangle_rotation : equivalence (triangle C) (triangle C) :=
{
  functor := rotate C,
  inverse := inv_rotate C,
  unit_iso := rot_comp_inv_rot C,
  counit_iso := sorry
}

end category_theory.triangulated
