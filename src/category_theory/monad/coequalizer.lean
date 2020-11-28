/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.limits.shapes.reflexive
import category_theory.limits.preserves.shapes.equalizers
import category_theory.limits.preserves.limits
import category_theory.monad.adjunction

/-!
# Special coequalizers associated to a monad

Associated to a monad `T : C ⥤ C` we have important coequalizer constructions:
Any algebra is a coequalizer (in the category of algebras) of free algebras. Furthermore, this
coequalizer is reflexive.
In `C`, this cofork diagram is a split coequalizer (in particular, it is still a coequalizer).
This split coequalizer is known as the Ceck coequalizer (as it features heavily in Ceck's
monadicity theorem).
-/
universes v₁ u₁

namespace category_theory
namespace monad
open limits

/-!
Show that any algebra is a coequalizer of free algebras.
-/
namespace cofork_free
variables {C : Type u₁}
variables [category.{v₁} C]

variables (T : C ⥤ C) [monad T] (X : monad.algebra T)

/-- The top map in the coequalizer diagram we will construct. -/
@[simps {rhs_md := semireducible}]
def top_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
(monad.free T).map X.a

/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
def bottom_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
{ f := (μ_ T).app X.A,
  h' := monad.assoc X.A }

/-- The cofork map in the coequalizer diagram we will construct. -/
@[simps]
def coequalizer_map : (monad.free T).obj X.A ⟶ X :=
{ f := X.a,
  h' := X.assoc.symm }

lemma comm : top_map T X ≫ coequalizer_map T X = bottom_map T X ≫ coequalizer_map T X :=
monad.algebra.hom.ext _ _ X.assoc.symm

@[simps {rhs_md := semireducible}]
def beck_algebra_cofork : cofork (top_map T X) (bottom_map T X) :=
cofork.of_π _ (comm T X)

/--
The cofork constructed is a colimit. This shows that any algebra is a coequalizer of free algebras.
-/
def beck_algebra_coequalizer : is_colimit (beck_algebra_cofork T X) :=
cofork.is_colimit.mk' _ $ λ s,
begin
  have h₁ : T.map X.a ≫ s.π.f = (μ_ T).app X.A ≫ s.π.f := congr_arg monad.algebra.hom.f s.condition,
  have h₂ : T.map s.π.f ≫ s.X.a = (μ_ T).app X.A ≫ s.π.f := s.π.h,
  refine ⟨⟨(η_ T).app _ ≫ s.π.f, _⟩, _, _⟩,
  { dsimp,
    rw [T.map_comp, category.assoc, h₂, monad.right_unit_assoc,
        (show X.a ≫ _ ≫ _ = _, from (η_ T).naturality_assoc _ _), h₁, monad.left_unit_assoc] },
  { ext1,
    dsimp,
    rw [(show X.a ≫ _ ≫ _ = _, from (η_ T).naturality_assoc _ _), h₁, monad.left_unit_assoc] },
  { intros m hm,
    ext1,
    dsimp at hm,
    dsimp,
    rw ← hm,
    dsimp,
    rw X.unit_assoc }
end
@[simp] lemma is_colimit_X : (cofork.of_π _ (comm T X)).X = X := rfl

lemma beck_split_coequalizer : is_split_coequalizer (T.map X.a) ((μ_ T).app _) X.a :=
⟨X.assoc.symm, (η_ T).app _, (η_ T).app _, X.unit, monad.left_unit _, ((η_ T).naturality _).symm⟩

/-- This is the Ceck cofork. It is a split coequalizer, in particular a coequalizer. -/
@[simps {rhs_md := semireducible}]
def beck_cofork : cofork (T.map X.a) ((μ_ T).app _)  :=
(beck_split_coequalizer T X).as_cofork

noncomputable def beck_coequalizer : limits.is_colimit (beck_cofork T X) :=
(beck_split_coequalizer T X).is_coequalizer

end cofork_free

end monad
end category_theory
