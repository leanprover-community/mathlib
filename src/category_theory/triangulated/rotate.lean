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
  [functor.additive (shift C).functor] [functor.additive (shift C).inverse]
variables (X : C)

/--
If you rotate a triangle, you get another triangle.
Given a triangle of the form:
```
      f       g       h
  X  ---> Y  ---> Z  ---> X[1]
```
applying `rotate` gives a triangle of the form:
```
      g        h       -f[1]
  Y  ---> Z  --->  X[1] ---> Y[1]
```
-/
@[simps]
def triangle.rotate (T : triangle C) : triangle C :=
{ obj₁ := T.obj₂,
  obj₂ := T.obj₃,
  obj₃ := T.obj₁⟦1⟧,
  mor₁ := T.mor₂,
  mor₂ := T.mor₃,
  mor₃ := -T.mor₁⟦1⟧' }

/--
Given a triangle of the form:
```
      f       g       h
  X  ---> Y  ---> Z  ---> X[1]
```
applying `inv_rotate` gives a triangle that can be thought of as:
```
        -h[-1]     f       g
  Z[-1]  --->  X  ---> Y  ---> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `Z[-1][1]` is
not necessarily equal to `Z`, but it is isomorphic, by the counit_iso of (shift C))
-/
@[simps]
def triangle.inv_rotate (T : triangle C) : triangle C :=
{ obj₁ := T.obj₃⟦-1⟧,
  obj₂ := T.obj₁,
  obj₃ := T.obj₂,
  mor₁ := -T.mor₃⟦-1⟧' ≫ (shift C).unit_iso.inv.app T.obj₁,
  mor₂ := T.mor₁,
  mor₃ := T.mor₂ ≫ (shift C).counit_iso.inv.app T.obj₃ }



namespace triangle_morphism
variables {T₁ T₂ T₃ T₄: triangle C}
/--
You can also rotate a triangle morphism to get a morphism between the two rotated triangles.
Given a triangle morphism of the form:
```
      f       g       h
  X  ---> Y  ---> Z  ---> X[1]
  |       |       |        |
  |a      |b      |c       |a[1]
  V       V       V        V
  X' ---> Y' ---> Z' ---> X'[1]
      f'      g'      h'
```
applying `rotate` gives a triangle morphism of the form:
```
      g        h       -f[1]
  Y  ---> Z  --->  X[1] ---> Y[1]
  |       |         |         |
  |b      |c        |a[1]     |b[1]
  V       V         V         V
  Y' ---> Z' ---> X'[1] ---> Y'[1]
      g'      h'       -f'[1]
```
-/
@[simps]
def rotate (f : triangle_morphism T₁ T₂) :
  triangle_morphism (T₁.rotate C) (T₂.rotate C):=
{ hom₁ := f.hom₂,
  hom₂ := f.hom₃,
  hom₃ := f.hom₁⟦1⟧',
  comm₃' := begin
    repeat {rw triangle.rotate_mor₃},
    rw [comp_neg, neg_comp],
    repeat {rw ← functor.map_comp},
    rw f.comm₁,
  end }

/--
Given a triangle morphism of the form:
```
      f       g       h
  X  ---> Y  ---> Z  ---> X[1]
  |       |       |        |
  |a      |b      |c       |a[1]
  V       V       V        V
  X' ---> Y' ---> Z' ---> X'[1]
      f'      g'      h'
```
applying `inv_rotate` gives a triangle morphism that can be thought of as:
```
        -h[-1]      f         g
  Z[-1]  --->  X   --->  Y   --->  Z
    |          |         |         |
    |a         |b        |c        |a[1]
    V          V         V         V
  Z'[-1] --->  X'  --->  Y'  --->  Z'
        -h'[-1]     f'        g'
```
(note that this diagram doesn't technically fit the definition of triangle morphism,
as `Z[-1][1]` is not necessarily equal to `Z`, and `Z'[-1][1]` is not necessarily equal to `Z'`,
but they are isomorphic, by the `counit_iso` of `shift C`)
-/
@[simps]
def inv_rotate (f : triangle_morphism T₁ T₂) :
  triangle_morphism (T₁.inv_rotate C) (T₂.inv_rotate C) :=
{ hom₁ := f.hom₃⟦-1⟧',
  hom₂ := f.hom₁,
  hom₃ := f.hom₂,
  comm₁' := begin
    simp only [triangle.inv_rotate_mor₁],
    rw [comp_neg, neg_comp, ← assoc],
    dsimp,
    rw [← functor.map_comp (shift C ).inverse, ← f.comm₃, functor.map_comp],
    repeat {rw assoc},
    suffices h : (shift C).unit_iso.inv.app T₁.obj₁ ≫ f.hom₁ =
      (shift C).inverse.map ((shift C).functor.map f.hom₁) ≫ (shift C).unit_iso.inv.app T₂.obj₁,
    { rw h },
    { simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map,
        nat_iso.cancel_nat_iso_inv_left],
      exact (category.comp_id f.hom₁).symm }
  end,
  comm₃' := begin
    have h := f.comm₂,
    repeat {rw triangle.inv_rotate_mor₃},
    rw [← assoc f.hom₂ _, ← f.comm₂],
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
    simp only [triangle_category_to_category_struct_id],
    unfold triangle_morphism.rotate,
    dsimp,
    ext,
    { refl },
    { refl },
    { simp only [triangle_morphism_id_hom₃, (shift C).functor.map_id],
      refl }
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    unfold triangle_morphism.rotate,
    ext,
    { refl },
    { refl },
    { dsimp,
      rw (shift C).functor.map_comp }
  end
}

/--
The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
def inv_rotate : (triangle C) ⥤ (triangle C) :=
{ obj := triangle.inv_rotate C,
  map := λ _ _ f, f.inv_rotate C,
  map_id' := begin
    intro T₁,
    simp only [triangle_category_to_category_struct_id],
    ext,
    { simp only [triangle_morphism_id_hom₃, triangle_morphism.inv_rotate_hom₁,
        triangle_morphism_id_hom₁],
      dsimp,
      rw (shift C).inverse.map_id },
    { refl },
    { refl }
  end,
  map_comp' := begin
    intros T₁ T₂ T₃ f g,
    unfold triangle_morphism.inv_rotate,
    ext,
    { simp only [triangle_morphism.comp_hom₃, triangle_morphism.comp_hom₁,
        triangle_category_to_category_struct_comp, functor.map_comp] },
    { refl },
    { refl }
  end
}

/--
There is a natural transformation between the identity functor on triangles,
and the composition of a rotation with an inverse rotation.
-/
@[simps]
def rot_comp_inv_rot_hom : 𝟭 (triangle C) ⟶ (rotate C) ⋙ (inv_rotate C) :=
{ app := begin
    intro T,
    rw [functor.id_obj, functor.comp_obj],
    let f : triangle_morphism T ((inv_rotate C).obj ((rotate C).obj T)) :=
    { hom₁ := (shift C).unit.app T.obj₁,
      hom₂ := 𝟙 T.obj₂,
      hom₃ := 𝟙 T.obj₃,
      comm₁' := begin
        rw comp_id,
        dsimp,
        rw [comp_neg, functor.additive.map_neg (shift C).inverse, ← functor.comp_map],
        simp only [neg_comp, comp_neg, functor.comp_map, iso.hom_inv_id_app_assoc,
          iso.hom_inv_id_app, assoc, equivalence.inv_fun_map, neg_neg],
        dsimp,
        simp only [comp_id],
      end,
      comm₃' := begin
        rw id_comp,
        dsimp,
        rw equivalence.counit_inv_app_functor,
      end },
    exact f,
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp only [functor.id_obj, congr_arg_mpr_hom_left, functor.id_map, functor.comp_map,
      id_comp, eq_to_hom_refl, congr_arg_mpr_hom_right, comp_id, functor.comp_obj],
    ext,
    { dsimp,
      simp only [iso.hom_inv_id_app_assoc, equivalence.inv_fun_map] },
    { dsimp,
      simp only [id_comp, comp_id] },
    { dsimp,
      simp only [id_comp, comp_id] }
  end
}

/--
There is a natural transformation between the composition of a rotation with an inverse rotation
on triangles, and the identity functor.
-/
@[simps]
def rot_comp_inv_rot_inv : (rotate C) ⋙ (inv_rotate C) ⟶ 𝟭 (triangle C) :=
{ app := begin
    intro T,
    rw [functor.id_obj, functor.comp_obj],
    let f : triangle_morphism ((inv_rotate C).obj ((rotate C).obj T)) T :=
    { hom₁ := (shift C).unit_inv.app T.obj₁,
      hom₂ := 𝟙 T.obj₂,
      hom₃ := 𝟙 T.obj₃,
      comm₁' := begin
        dsimp,
        simp only [neg_comp, iso.hom_inv_id_app, functor.additive.map_neg, assoc,
          equivalence.inv_fun_map, neg_neg, comp_id, nat_iso.cancel_nat_iso_inv_left],
        dsimp,
        simp only [comp_id],
      end },
    exact f
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp only [functor.id_obj, congr_arg_mpr_hom_left, functor.id_map, functor.comp_map,
      id_comp, eq_to_hom_refl, congr_arg_mpr_hom_right, comp_id, functor.comp_obj],
    dsimp,
    ext,
    { simp only [triangle_morphism.comp_hom₁,
        triangle_morphism.inv_rotate_hom₁, triangle_morphism.rotate_hom₃],
      dsimp,
      simp only [iso.hom_inv_id_app, assoc, equivalence.inv_fun_map,
        nat_iso.cancel_nat_iso_inv_left],
      dsimp,
      simp only [comp_id] },
    { simp only [triangle_morphism.comp_hom₂, triangle_morphism.inv_rotate_hom₂,
        triangle_morphism.rotate_hom₁, comp_id f.hom₂, id_comp f.hom₂] },
    { simp only [triangle_morphism.comp_hom₃, triangle_morphism.rotate_hom₂,
        triangle_morphism.inv_rotate_hom₃, comp_id f.hom₃, id_comp f.hom₃] }
  end
}

/--
The natural transformations between the identity functor on triangles and the composition
of a rotation with an inverse rotation are natural isomorphisms (they are isomorphisms in the
category of functors).
-/
@[simps]
def rot_comp_inv_rot : 𝟭 (triangle C) ≅ (rotate C) ⋙ (inv_rotate C) :=
{ hom := rot_comp_inv_rot_hom C,
  inv := rot_comp_inv_rot_inv C,
  hom_inv_id' := begin
    ext T,
    { simp only [functor.id_obj, congr_arg_mpr_hom_left, triangle_morphism.comp_hom₁,
        triangle_category_to_category_struct_comp, rot_comp_inv_rot_inv_app,
        rot_comp_inv_rot_hom_app, iso.hom_inv_id_app, category.id_comp,
        nat_trans.id_app, triangle_category_to_category_struct_id,
        triangle_morphism_id_hom₁, eq_to_hom_refl, congr_arg_mpr_hom_right,
        category.comp_id, functor.comp_obj, nat_trans.comp_app],
      dsimp,
      refl },
    { simp only [functor.id_obj, congr_arg_mpr_hom_left,
        triangle_category_to_category_struct_comp,
        rot_comp_inv_rot_inv_app, triangle_morphism.comp_hom₂, rot_comp_inv_rot_hom_app,
        category.id_comp, nat_trans.id_app, triangle_category_to_category_struct_id,
        triangle_morphism_id_hom₂, eq_to_hom_refl, congr_arg_mpr_hom_right,
        category.comp_id, functor.comp_obj, nat_trans.comp_app],
      dsimp,
      refl },
    { simp only [functor.id_obj, congr_arg_mpr_hom_left,
        triangle_category_to_category_struct_comp,
        rot_comp_inv_rot_inv_app, triangle_morphism.comp_hom₃, rot_comp_inv_rot_hom_app,
        category.id_comp, nat_trans.id_app, triangle_category_to_category_struct_id,
        triangle_morphism_id_hom₃, eq_to_hom_refl, congr_arg_mpr_hom_right,
        category.comp_id, functor.comp_obj, nat_trans.comp_app],
      dsimp,
      refl }
  end,
  inv_hom_id' := begin
    ext T,
    { simp,
      refl },
    { simp,
      refl },
    { simp,
      refl }
  end -- (deterministic) timeout when replace simp with squeeze_simp
}

/--
There is a natural transformation between the composition of an inverse rotation with a rotation
on triangles, and the identity functor.
-/
@[simps]
def inv_rot_comp_rot_hom : (inv_rotate C) ⋙ (rotate C) ⟶ 𝟭 (triangle C) :=
{ app := begin
    intro T,
    rw [functor.id_obj, functor.comp_obj],
    let f : triangle_morphism ((rotate C).obj((inv_rotate C).obj T)) T :=
    { hom₁ := 𝟙 T.obj₁,
      hom₂ := 𝟙 T.obj₂,
      hom₃ := (shift C).counit.app T.obj₃ },
    exact f
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp,
    dsimp,
    ext,
    { simp,
      dsimp,
      simp },
    { simp,
      dsimp,
      simp },
    { simp,
      dsimp,
      simp,
      dsimp,
      rw comp_id }
  end
}

/--
There is a natural transformation between the identity functor on triangles,
and  the composition of an inverse rotation with a rotation.
-/
@[simps]
def inv_rot_comp_rot_inv : 𝟭 (triangle C) ⟶ (inv_rotate C) ⋙ (rotate C) :=
{ app := begin
    intro T,
    rw [functor.id_obj, functor.comp_obj],
    let f : triangle_morphism T ((rotate C).obj ((inv_rotate C).obj T)) :=
    { hom₁ := 𝟙 T.obj₁,
      hom₂ := 𝟙 T.obj₂,
      hom₃ := (shift C).counit_inv.app T.obj₃ },
    exact f
  end,
  naturality' := begin
    intros T₁ T₂ f,
    simp,
    dsimp,
    ext,
    { simp },
    { simp },
    { simp,
      dsimp,
      simp }
  end
}

/--
The natural transformations between the composition of a rotation with an inverse rotation
on triangles, and the identity functor on triangles are natural isomorphisms
(they are isomorphisms in the category of functors).
-/
@[simps]
def inv_rot_comp_rot : (inv_rotate C) ⋙ (rotate C) ≅ 𝟭 (triangle C) :=
{
  hom := inv_rot_comp_rot_hom C,
  inv := inv_rot_comp_rot_inv C,
  hom_inv_id' := begin
    ext T,
    { dsimp,
      simp,
      dsimp,
      simp },
    { dsimp,
      simp,
      dsimp,
      simp },
    { simp,
      dsimp,
      simp }
  end,
  inv_hom_id' := begin
    ext T,
    { dsimp,
      simp,
      dsimp,
      simp },
    { dsimp,
      simp,
      dsimp,
      simp },
    { dsimp,
      simp,
      dsimp,
      simp,
      refl }
  end
}

/--
Rotating triangles gives an auto-equivalence on the category of triangles.
-/
def triangle_rotation : equivalence (triangle C) (triangle C) :=
{ functor := rotate C,
  inverse := inv_rotate C,
  unit_iso := rot_comp_inv_rot C,
  counit_iso := inv_rot_comp_rot C,
  functor_unit_iso_comp' := begin
    intro T,
    ext,
    { dsimp,
      simp,
      dsimp,
      simp },
    { dsimp,
      simp,
      dsimp,
      simp },
    { dsimp,
      simp,
      dsimp,
      simp }
  end
}

end category_theory.triangulated
