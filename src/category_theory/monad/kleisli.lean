/-
Copyright (c) 2020 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki, Bhavik Mehta
-/

import category_theory.adjunction
import category_theory.monad.basic

/-! # Kleisli category on a monad

This file defines the Kleisli category on a monad `(T, η_ T, μ_ T)`. It also defines the Kleisli
adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.

## References
* [Riehl, *Category theory in context*, Definition 5.2.9][riehl2017]
-/
namespace category_theory

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u} [category.{v} C]

def kleisli (T : C ⥤ C) := C

namespace kleisli

variables (T : C ⥤ C) [monad.{v} T]

/-- The Kleisli category on a monad `T`.
    cf Definition 5.2.9 in [Riehl][riehl2017]. -/
instance kleisli.category : category (kleisli T) :=
{ hom  := λ (X Y : C), X ⟶ T.obj Y,
  id   := λ X, (η_ T).app X,
  comp := λ X Y Z f g, f ≫ T.map g ≫ (μ_ T).app Z,
  id_comp' := λ X Y f, by simp [← (η_ T).naturality_assoc f, monad.left_unit'],
  assoc'   := λ W X Y Z f g h,
  begin
    simp only [T.map_comp, category.assoc, monad.assoc],
    erw (μ_ T).naturality_assoc h,
  end }

namespace adjunction

@[simps] def F_T : C ⥤ kleisli T :=
{ obj       := λ X, (X : kleisli T),
  map       := λ X Y f, (f ≫ (η_ T).app Y : _),
  map_comp' := λ X Y Z f g,
  begin
    unfold_projs,
    simp [← (η_ T).naturality g],
  end }

@[simps] def U_T : kleisli T ⥤ C :=
{ obj       := λ X, T.obj X,
  map       := λ X Y f, T.map f ≫ (μ_ T).app Y,
  map_id'   := λ X, monad.right_unit _,
  map_comp' := λ X Y Z f g,
  begin
    unfold_projs,
    simp [monad.assoc, ← (μ_ T).naturality_assoc g],
  end }

/-- The Kleisli adjunction which gives rise to the monad `(T, η_ T, μ_ T)`.
    cf Lemma 5.2.11 of [Riehl][riehl2017]. -/
def adj : F_T T ⊣ U_T T :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, equiv.refl _,
  hom_equiv_naturality_left_symm' := λ X Y Z f g,
  begin
    unfold_projs,
    dsimp,
    rw [category.assoc, ← (η_ T).naturality_assoc g, functor.id_map],
    dsimp,
    simp [monad.left_unit],
  end }

def F_T_comp_U_T_iso_T : F_T T ⋙ U_T T ≅ T :=
nat_iso.of_components (λ X, iso.refl _) (λ X Y f, by { dsimp, simp })

end adjunction
end kleisli

end category_theory
