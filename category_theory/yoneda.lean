-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

/- The Yoneda embedding, as a functor `yoneda : C ⥤ ((Cᵒᵖ) ⥤ (Type v₁))`,
   along with instances that it is `full` and `faithful`.
   
   Also the Yoneda lemma, `yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C)`. -/

import category_theory.natural_transformation
import category_theory.opposites
import category_theory.types
import category_theory.embedding

namespace category_theory

universes u₁ v₁ u₂

variables (C : Type u₁) [𝒞 : category.{u₁ v₁} C]
include 𝒞

def yoneda : C ⥤ ((Cᵒᵖ) ⥤ (Type v₁)) := 
{ obj := λ X, { obj := λ Y : C, Y ⟶ X,
                map' := λ Y Y' f g, f ≫ g,
                map_comp' := begin intros X_1 Y Z f g, ext1, dsimp at *, erw [category.assoc] end,
                map_id' := begin intros X_1, ext1, dsimp at *, erw [category.id_comp] end },
  map' := λ X X' f, { app := λ Y g, g ≫ f } }

namespace yoneda
@[simp] lemma obj_obj (X Y : C) : ((yoneda C) X) Y = (Y ⟶ X) := rfl
@[simp] lemma obj_map (X : C) {Y Y' : C} (f : Y ⟶ Y') : ((yoneda C) X).map f = λ g, f ≫ g := rfl
@[simp] lemma map_app {X X' : C} (f : X ⟶ X') (Y : C) : ((yoneda C).map f) Y = λ g, g ≫ f := rfl

lemma aux_1 {X Y : Cᵒᵖ} (f : X ⟶ Y) : ((yoneda C) X).map f (𝟙 X) = ((yoneda C).map f) Y (𝟙 Y) := by obviously
@[simp] lemma aux_2 {X Y : C} (α : (yoneda C) X ⟶ (yoneda C) Y) 
  {Z Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X) : f ≫ α Z' h = α Z (f ≫ h) :=
begin erw [functor_to_types.naturality], refl end

instance full : full (yoneda C) := 
{ preimage := λ X Y f, (f X) (𝟙 X) }.

instance faithful : faithful (yoneda C) := 
begin
  fsplit, 
  intros X Y f g p, 
  injection p with h,
  convert (congr_fun (congr_fun h X) (𝟙 X)) ; simp
end

-- We need to help typeclass inference with some awkward universe levels here.
instance prod_category_instance_1 : category (((Cᵒᵖ) ⥤ Type v₁) × (Cᵒᵖ)) := category_theory.prod.{(max u₁ (v₁+1)) (max u₁ v₁) u₁ v₁} (Cᵒᵖ ⥤ Type v₁) (Cᵒᵖ)
instance prod_category_instance_2 : category ((Cᵒᵖ) × ((Cᵒᵖ) ⥤ Type v₁)) := category_theory.prod.{u₁ v₁ (max u₁ (v₁+1)) (max u₁ v₁)} (Cᵒᵖ) (Cᵒᵖ ⥤ Type v₁) 
end yoneda

def yoneda_evaluation : (((Cᵒᵖ) ⥤ (Type v₁)) × (Cᵒᵖ)) ⥤ (Type (max u₁ v₁)) 
  := (evaluation (Cᵒᵖ) (Type v₁)) ⋙ ulift_functor.{v₁ u₁}

@[simp] lemma yoneda_evaluation_map_down (P Q : (Cᵒᵖ ⥤ Type v₁) ×  (Cᵒᵖ)) (α : P ⟶ Q) (x : (yoneda_evaluation C) P)
 : ((yoneda_evaluation C).map α x).down = (α.1) (Q.2) ((P.1).map (α.2) (x.down)) := rfl

def yoneda_pairing : (((Cᵒᵖ) ⥤ (Type v₁)) × (Cᵒᵖ)) ⥤ (Type (max u₁ v₁)) := 
let F := (category_theory.prod.swap ((Cᵒᵖ) ⥤ (Type v₁)) (Cᵒᵖ)) in
let G := (functor.prod ((yoneda C).op) (functor.id ((Cᵒᵖ) ⥤ (Type v₁)))) in
let H := (functor.hom ((Cᵒᵖ) ⥤ (Type v₁))) in
  (F ⋙ G ⋙ H)      

@[simp] lemma yoneda_pairing_map (P Q : (Cᵒᵖ ⥤ Type v₁) ×  (Cᵒᵖ)) (α : P ⟶ Q) (β : (yoneda_pairing C) (P.1, P.2)): (yoneda_pairing C).map α β = (yoneda C).map (α.snd) ≫ β ≫ α.fst := rfl

def yoneda_lemma : (yoneda_pairing C) ≅ (yoneda_evaluation C) := 
{ hom := { app := λ F x, ulift.up ((x.app F.2) (𝟙 F.2)),
           naturality' := begin intros X Y f, ext1, ext1, cases f, cases Y, cases X, dsimp at *, simp at *, erw [←functor_to_types.naturality, yoneda.aux_1, functor_to_types.naturality, functor_to_types.map_id] end },
  inv := { app := λ F x, { app := λ X a, (F.1.map a) x.down,
                           naturality' := begin intros X Y f, ext1, cases x, cases F, dsimp at *, erw [functor_to_types.map_comp], refl end },
           naturality' := begin intros X Y f, ext1, ext1, ext1, cases x, cases f, cases Y, cases X, dsimp at *, simp at *, erw [←functor_to_types.naturality, functor_to_types.map_comp] end },
  hom_inv_id' := begin ext1, ext1, ext1, ext1, cases X, dsimp at *, simp at *, erw [←functor_to_types.naturality, yoneda.aux_1, functor_to_types.naturality, functor_to_types.map_id] end,
  inv_hom_id' := begin ext1, ext1, ext1, cases x, cases X, dsimp at *, erw [functor_to_types.map_id] end }.

end category_theory