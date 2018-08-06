-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import .natural_transformation

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃

instance FunctorCategory (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] : category.{(max u₁ v₁ u₂ v₂) (max u₁ v₂)} (C ↝ D) := 
{ Hom      := λ F G, F ⟹ G,
  id       := λ F, NaturalTransformation.id F,
  comp     := λ _ _ _ α β, α ⊟ β,
  id_comp  := begin
                      -- `obviously'` says:
                      intros,
                      apply NaturalTransformation.componentwise_equal,
                      intros,
                      dsimp,
                      simp
                    end,
  comp_id := begin
                      -- `obviously'` says:
                      intros,
                      apply NaturalTransformation.componentwise_equal,
                      intros,
                      dsimp,
                      simp
                    end,
  assoc  := begin
                      -- `obviously'` says:
                      intros,
                      apply NaturalTransformation.componentwise_equal,
                      intros,
                      simp
                    end }

namespace FunctorCategory

section
variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

@[simp,ematch] lemma id.components (F : C ↝ D) (X : C) : (𝟙 F : F ⟹ F) X = 𝟙 (F X) := rfl
@[simp,ematch] lemma comp.components {F G H : C ↝ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) : ((α ≫ β) : F ⟹ H) X = (α : F ⟹ G) X ≫ (β : G ⟹ H) X := rfl
end

namespace NaturalTransformation
-- This section gives two lemmas about natural transformations between functors into functor categories, spelling them out in components.

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D] {E : Type u₃} [ℰ : category.{u₃ v₃} E]
include 𝒞 𝒟 ℰ 

@[ematch] lemma components_naturality {F G : C ↝ (D ↝ E)} (T : F ⟹ G) (X : C) {Y Z : D} (f : Y ⟶ Z) : ((F X).map f) ≫ ((T X) Z) = ((T X) Y) ≫ ((G X).map f) :=
begin
  exact (T.components _).naturality _
end

@[ematch] lemma naturality_components {F G : C ↝ (D ↝ E)} (T : F ⟹ G) (Z : D) {X Y : C} (f : X ⟶ Y) : ((F.map f) Z) ≫ ((T Y) Z) = ((T X) Z) ≫ ((G.map f) Z) :=
begin
  have p := (T.naturality f),
  -- obviously' does something equivalent to:
  injection p, clear p, dsimp at h_1,
  have h_2 := congr_fun h_1 Z,
  solve_by_elim
end
end NaturalTransformation

end FunctorCategory
end category_theory
