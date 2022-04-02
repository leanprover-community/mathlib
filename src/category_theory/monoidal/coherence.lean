/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
import category_theory.monoidal.free.coherence

/-!
# A `coherence` tactic for monoidal categories, and `⊗≫` (composition up to associators)

We provide a `coherence` tactic,
which proves that any two morphisms (with the same source and target)
in a monoidal category which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `monoidal_comp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.
-/

noncomputable theory

universes v u

open category_theory
namespace category_theory.monoidal_category

variables {C : Type u} [category.{v} C] [monoidal_category C]

open category_theory.free_monoidal_category

/-- A typeclass carrying a choice of lift of an object from `C` to `free_monoidal_category C`. -/
class lift_obj (X : C) :=
(lift : free_monoidal_category C)

instance lift_obj_unit : lift_obj (𝟙_ C) := { lift := unit, }
instance lift_obj_tensor (X Y : C) [lift_obj X] [lift_obj Y] : lift_obj (X ⊗ Y) :=
{ lift := lift_obj.lift X ⊗ lift_obj.lift Y, }
@[priority 100]
instance lift_obj_of (X : C) : lift_obj X := { lift := of X, }

/-- A typeclass carrying a choice of lift of a morphism from `C` to `free_monoidal_category C`. -/
class lift_hom {X Y : C} [lift_obj X] [lift_obj Y] (f : X ⟶ Y) :=
(lift : lift_obj.lift X ⟶ lift_obj.lift Y)

instance lift_hom_id (X : C) [lift_obj X] : lift_hom (𝟙 X) :=
{ lift := 𝟙 _, }
instance lift_hom_left_unitor_hom (X : C) [lift_obj X] : lift_hom (λ_ X).hom :=
{ lift := (λ_ (lift_obj.lift X)).hom, }
instance lift_hom_left_unitor_inv (X : C) [lift_obj X] : lift_hom (λ_ X).inv :=
{ lift := (λ_ (lift_obj.lift X)).inv, }
instance lift_hom_right_unitor_hom (X : C) [lift_obj X] : lift_hom (ρ_ X).hom :=
{ lift := (ρ_ (lift_obj.lift X)).hom, }
instance lift_hom_right_unitor_inv (X : C) [lift_obj X] : lift_hom (ρ_ X).inv :=
{ lift := (ρ_ (lift_obj.lift X)).inv, }
instance lift_hom_associator_hom (X Y Z : C) [lift_obj X] [lift_obj Y] [lift_obj Z] :
  lift_hom (α_ X Y Z).hom :=
{ lift := (α_ (lift_obj.lift X) (lift_obj.lift Y) (lift_obj.lift Z)).hom, }
instance lift_hom_associator_inv (X Y Z : C) [lift_obj X] [lift_obj Y] [lift_obj Z] :
  lift_hom (α_ X Y Z).inv :=
{ lift := (α_ (lift_obj.lift X) (lift_obj.lift Y) (lift_obj.lift Z)).inv, }
instance lift_hom_comp {X Y Z : C} [lift_obj X] [lift_obj Y] [lift_obj Z] (f : X ⟶ Y) (g : Y ⟶ Z)
  [lift_hom f] [lift_hom g] : lift_hom (f ≫ g) :=
{ lift := lift_hom.lift f ≫ lift_hom.lift g }
instance lift_hom_tensor {W X Y Z : C} [lift_obj W] [lift_obj X] [lift_obj Y] [lift_obj Z]
  (f : W ⟶ X) (g : Y ⟶ Z) [lift_hom f] [lift_hom g] : lift_hom (f ⊗ g) :=
{ lift := lift_hom.lift f ⊗ lift_hom.lift g }

section

open tactic
setup_tactic_parser

/-- Coherence tactic for monoidal categories. -/
meta def _root_.tactic.interactive.monoidal_coherence : tactic unit :=
do
  `(%%lhs = %%rhs) ← target,
  to_expr  ``(project_map id _ _ (lift_hom.lift %%lhs) = project_map id _ _ (lift_hom.lift %%rhs))
    >>= tactic.change,
  congr

/--
`coherence` uses the coherence theorem for monoidal categories to prove the goal.
It can prove any equality made up only of associators and unitors.
```lean
example {C : Type} [category C] [monoidal_category C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by coherence
```
-/
-- TODO: provide the `bicategory_coherence` tactic, and add that here.
meta def _root_.tactic.interactive.coherence : tactic unit := tactic.interactive.monoidal_coherence

add_tactic_doc
{ name        := "coherence",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.coherence],
  tags        := ["category theory"] }
end

example (X₁ X₂ : C) :
  ((λ_ (𝟙_ C)).inv ⊗ 𝟙 (X₁ ⊗ X₂)) ≫ (α_ (𝟙_ C) (𝟙_ C) (X₁ ⊗ X₂)).hom ≫
    (𝟙 (𝟙_ C) ⊗ (α_ (𝟙_ C) X₁ X₂).inv) =
  𝟙 (𝟙_ C) ⊗ ((λ_ X₁).inv ⊗ 𝟙 X₂) :=
by coherence

-- We could likely turn this into a `Prop` valued existential if that proves useful.
class monoidal_coherence (X Y : C) [lift_obj X] [lift_obj Y] :=
(hom [] : X ⟶ Y)
[is_iso : is_iso hom . tactic.apply_instance]

attribute [instance] monoidal_coherence.is_iso

namespace monoidal_coherence

@[simps]
instance refl (X : C) [lift_obj X] : monoidal_coherence X X := ⟨𝟙 _⟩

@[simps]
instance tensor (X Y Z : C) [lift_obj X] [lift_obj Y] [lift_obj Z] [monoidal_coherence Y Z] :
  monoidal_coherence (X ⊗ Y) (X ⊗ Z) :=
⟨𝟙 X ⊗ monoidal_coherence.hom Y Z⟩

@[simps]
instance left (X Y : C) [lift_obj X] [lift_obj Y] [monoidal_coherence X Y] :
  monoidal_coherence (𝟙_ C ⊗ X) Y :=
⟨(λ_ X).hom ≫ monoidal_coherence.hom X Y⟩

@[simps]
instance left' (X Y : C) [lift_obj X] [lift_obj Y] [monoidal_coherence X Y] :
  monoidal_coherence X (𝟙_ C ⊗ Y) :=
⟨monoidal_coherence.hom X Y ≫ (λ_ Y).inv⟩

@[simps]
instance right (X Y : C) [lift_obj X] [lift_obj Y] [monoidal_coherence X Y] :
  monoidal_coherence (X ⊗ 𝟙_ C) Y :=
⟨(ρ_ X).hom ≫ monoidal_coherence.hom X Y⟩

@[simps]
instance right' (X Y : C) [lift_obj X] [lift_obj Y] [monoidal_coherence X Y] :
  monoidal_coherence X (Y ⊗ 𝟙_ C) :=
⟨monoidal_coherence.hom X Y ≫ (ρ_ Y).inv⟩

@[simps]
instance assoc (X Y Z W : C) [lift_obj W] [lift_obj X] [lift_obj Y] [lift_obj Z]
  [monoidal_coherence (X ⊗ (Y ⊗ Z)) W] : monoidal_coherence ((X ⊗ Y) ⊗ Z) W :=
⟨(α_ X Y Z).hom ≫ monoidal_coherence.hom (X ⊗ (Y ⊗ Z)) W⟩

@[simps]
instance assoc' (W X Y Z : C) [lift_obj W] [lift_obj X] [lift_obj Y] [lift_obj Z]
  [monoidal_coherence W (X ⊗ (Y ⊗ Z))] : monoidal_coherence W ((X ⊗ Y) ⊗ Z) :=
⟨monoidal_coherence.hom W (X ⊗ (Y ⊗ Z)) ≫ (α_ X Y Z).inv⟩

end monoidal_coherence

/-- Construct an isomorphism between two objects in a monoidal category
out of unitors and associators. -/
def monoidal_iso (X Y : C) [lift_obj X] [lift_obj Y] [monoidal_coherence X Y] : X ≅ Y :=
as_iso (monoidal_coherence.hom X Y)

example (X1 X2 X3 X4 X5 X6 X7 X8 X9 : C) :
  (𝟙_ C ⊗ (X1 ⊗ X2 ⊗ ((X3 ⊗ X4) ⊗ X5)) ⊗ X6 ⊗ (X7 ⊗ X8 ⊗ X9)) ≅
  (X1 ⊗ (X2 ⊗ X3) ⊗ X4 ⊗ (X5 ⊗ (𝟙_ C ⊗ X6) ⊗ X7) ⊗ X8 ⊗ X9) :=
monoidal_iso _ _

/-- Compose two morphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
def monoidal_comp {W X Y Z : C} [lift_obj X] [lift_obj Y]
  [monoidal_coherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
f ≫ monoidal_coherence.hom X Y ≫ g

infixr ` ⊗≫ `:80 := monoidal_comp -- type as \ot \gg

example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) : U ⟶ Y := f ⊗≫ g

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `f ⊗≫ 𝟙 _`
example {W X Y Z : C} (f : W ⟶ (X ⊗ Y) ⊗ Z) : W ⟶ X ⊗ (Y ⊗ Z) := f ⊗≫ 𝟙 _

@[simp] lemma monoidal_comp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  f ⊗≫ g = f ≫ g :=
by { dsimp [monoidal_comp], simp, }

example {U V W X Y : C} (f : U ⟶ V ⊗ (W ⊗ X)) (g : (V ⊗ W) ⊗ X ⟶ Y) :
  f ⊗≫ g = f ≫ (α_ _ _ _).inv ≫ g :=
by simp [monoidal_comp]

/-!
Sadly, we can't prove lemmas such as the following,
because we've forgotten that our `monoidal_coherence` instances,
provided by typeclass inference, are built out of the monoidal isomorphisms.
```
@[simp] lemma monoidal_comp_assoc {U V W X Y Z : C}
  [monoidal_coherence V (W ⊗ (X ⊗ Y))] [monoidal_coherence V ((W ⊗ X) ⊗ Y)]
  (f : U ⟶ V) (g : W ⊗ (X ⊗ Y) ⟶ Z) : f ⊗≫ ((α_ W X Y).hom ≫ g) = f ⊗≫ g :=
begin
  dsimp [monoidal_comp],
  congr' 1,
  rw ←category.assoc,
  congr' 1,
  coherence, -- fails
end
```
-/

/-!
# Proposal for a better `coherence` tactic:

To prove an equality `f = g` in a monoidal category,
parse each of `f` and `g` as the composition of some list of morphisms.
Identify the morphisms for which we can not construct a `lift_hom`.
Make sure the lists of such morphisms in `f` and `g` are identical; fail if not.
Now split the lists at these points,
and for each corresponding pair of lists of morphisms for which we have a `lift_hom`
(one list from `f`, one list from `g`),
try to prove these are equal using the `coherence` tactic above.
-/

end category_theory.monoidal_category
