/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison

Defines a functor between categories.

(As it is a 'bundled' object rather than the `is_functorial` typeclass parametrised 
by the underlying function on objects, the name is capitalised.)

Introduces notations
  `F +> X` for the action on objects
  `F &> f` for the action on morphisms, and
  `C ↝ D` for the type of all functors from `C` to `D`. (I would like a better notation here.)
-/

import .category

namespace category_theory
 
universes u₁ v₁ u₂ v₂ u₃ v₃

structure Functor (C : Type u₁) [category.{u₁ v₁} C] (D : Type u₂) [category.{u₂ v₂} D] : Type (max u₁ v₁ u₂ v₂) :=
(on_objects     : C → D)
(on_morphisms   : Π {X Y : C}, (X ⟶ Y) → ((on_objects X) ⟶ (on_objects Y)))
(identities    : ∀ (X : C), on_morphisms (𝟙 X) = 𝟙 (on_objects X) . obviously)
(functoriality : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), on_morphisms (f ≫ g) = (on_morphisms f) ≫ (on_morphisms g) . obviously)

make_lemma Functor.identities
make_lemma Functor.functoriality
attribute [simp,ematch] Functor.functoriality_lemma Functor.identities_lemma

infixr ` +> `:70 := Functor.on_objects
infixr ` &> `:70 := Functor.on_morphisms -- switch to ▹?
infixr ` ↝ `:70 := Functor              -- type as \lea 

namespace Functor

definition id (C : Type u₁) [category.{u₁ v₁} C] : C ↝ C := 
{ on_objects     := id,
  on_morphisms   := λ _ _ f, f,
  identities    := begin 
                     -- `obviously'` says:
                     intros,
                     refl 
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     refl
                   end }

instance has_one (C) [category C] : has_one (C ↝ C) :=
{ one := id C }

variable {C : Type u₁}
variable [𝒞 : category.{u₁ v₁} C]
include 𝒞

@[simp] lemma id.on_objects (X : C) : (id C) +> X = X := by refl
@[simp] lemma id.on_morphisms {X Y : C} (f : X ⟶ Y) : (id C) &> f = f := by refl

variable {D : Type u₂}
variable [𝒟 : category.{u₂ v₂} D]
variable {E : Type u₃}
variable [ℰ : category.{u₃ v₃} E]
include 𝒟 ℰ

definition comp (F : C ↝ D) (G : D ↝ E) : C ↝ E := 
{ on_objects     := λ X, G +> (F +> X),
  on_morphisms   := λ _ _ f, G &> (F &> f),
  identities    := begin 
                     -- `obviously'` says:
                     intros,
                     simp,
                   end,
  functoriality := begin
                     -- `obviously'` says:
                     intros,
                     simp
                   end }
infixr ` ⋙ `:80 := comp

@[simp] lemma comp.on_objects (F : C ↝ D) (G : D ↝ E) (X : C) : (F ⋙ G) +> X = G +> (F +> X) := by refl
@[simp] lemma comp.on_morphisms (F : C ↝ D) (G : D ↝ E) (X Y : C) (f : X ⟶ Y) : (F ⋙ G) &> f = G.on_morphisms (F &> f) := by refl

end Functor
end category_theory
