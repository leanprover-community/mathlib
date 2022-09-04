/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import category_theory.limits.shapes.pullbacks
import category_theory.arrow
import category_theory.limits.shapes.comm_sq

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-properties are defined

* `respects_iso`: `P` respects isomorphisms if `P f → P (e ≫ f)` and `P f → P (f ≫ e)`, where
  `e` is an isomorphism.
* `stable_under_composition`: `P` is stable under composition if `P f → P g → P (f ≫ g)`.
* `stable_under_base_change`: `P` is stable under base change if in all pullback
  squares, the left map satisfies `P` if the right map satisfies it.

-/

universes v u

open category_theory category_theory.limits opposite

noncomputable theory

namespace category_theory

variables (C : Type u) [category.{v} C] {D : Type*} [category D]

/-- A `morphism_property C` is a class of morphisms between objects in `C`. -/
@[derive complete_lattice]
def morphism_property := ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Prop

instance : inhabited (morphism_property C) := ⟨⊤⟩

variable {C}

namespace morphism_property

/-- A morphism property `respects_iso` if it still holds when composed with an isomorphism -/
def respects_iso (P : morphism_property C) : Prop :=
  (∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z), P f → P (e.hom ≫ f)) ∧
  (∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y), P f → P (f ≫ e.hom))

/-- A morphism property is `stable_under_composition` if the composition of two such morphisms
still falls in the class. -/
def stable_under_composition (P : morphism_property C) : Prop :=
  ∀ ⦃X Y Z⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g)

/-- A morphism property is `stable_under_inverse` if the inverse of a morphism satisfying
the property still falls in the class. -/
def stable_under_inverse (P : morphism_property C) : Prop :=
∀ ⦃X Y⦄ (e : X ≅ Y), P e.hom → P e.inv

/-- A morphism property is `stable_under_base_change` if the base change of such a morphism
still falls in the class. -/
def stable_under_base_change (P : morphism_property C) : Prop :=
∀ ⦃X Y Y' S : C⦄ ⦃f : X ⟶ S⦄ ⦃g : Y ⟶ S⦄ ⦃f' : Y' ⟶ Y⦄ ⦃g' : Y' ⟶ X⦄
  (sq : is_pullback f' g' g f) (hg : P g), P g'

lemma stable_under_composition.respects_iso {P : morphism_property C}
  (hP : stable_under_composition P) (hP' : ∀ {X Y} (e : X ≅ Y), P e.hom) : respects_iso P :=
⟨λ X Y Z e f hf, hP _ _ (hP' e) hf, λ X Y Z e f hf, hP _ _ hf (hP' e)⟩

lemma respects_iso.cancel_left_is_iso {P : morphism_property C}
  (hP : respects_iso P) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso f] :
    P (f ≫ g) ↔ P g :=
⟨λ h, by simpa using hP.1 (as_iso f).symm (f ≫ g) h, hP.1 (as_iso f) g⟩

lemma respects_iso.cancel_right_is_iso {P : morphism_property C}
  (hP : respects_iso P) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [is_iso g] :
    P (f ≫ g) ↔ P f :=
⟨λ h, by simpa using hP.2 (as_iso g).symm (f ≫ g) h, hP.2 (as_iso g) f⟩

lemma respects_iso.arrow_iso_iff {P : morphism_property C}
  (hP : respects_iso P) {f g : arrow C} (e : f ≅ g) : P f.hom ↔ P g.hom :=
by { rw [← arrow.inv_left_hom_right e.hom, hP.cancel_left_is_iso, hP.cancel_right_is_iso], refl }

lemma respects_iso.arrow_mk_iso_iff {P : morphism_property C}
  (hP : respects_iso P) {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : arrow.mk f ≅ arrow.mk g) :
    P f ↔ P g :=
hP.arrow_iso_iff e

lemma respects_iso.of_respects_arrow_iso (P : morphism_property C)
  (hP : ∀ (f g : arrow C) (e : f ≅ g) (hf : P f.hom), P g.hom) : respects_iso P :=
begin
  split,
  { intros X Y Z e f hf,
    refine hP (arrow.mk f) (arrow.mk (e.hom ≫ f)) (arrow.iso_mk e.symm (iso.refl _) _) hf,
    dsimp,
    simp only [iso.inv_hom_id_assoc, category.comp_id], },
  { intros X Y Z e f hf,
    refine hP (arrow.mk f) (arrow.mk (f ≫ e.hom)) (arrow.iso_mk (iso.refl _) e _) hf,
    dsimp,
    simp only [category.id_comp], },
end

lemma stable_under_base_change.mk {P : morphism_property C} [has_pullbacks C]
  (hP₁ : respects_iso P)
  (hP₂ : ∀ (X Y S : C) (f : X ⟶ S) (g : Y ⟶ S) (hg : P g), P (pullback.fst : pullback f g ⟶ X)) :
  stable_under_base_change P := λ X Y Y' S f g f' g' sq hg,
begin
  let e := sq.flip.iso_pullback,
  rw [← hP₁.cancel_left_is_iso e.inv, sq.flip.iso_pullback_inv_fst],
  exact hP₂ _ _ _ f g hg,
end

lemma stable_under_base_change.respects_iso {P : morphism_property C}
  (hP : stable_under_base_change P) : respects_iso P :=
begin
  apply respects_iso.of_respects_arrow_iso,
  intros f g e,
  exact hP (is_pullback.of_horiz_is_iso (comm_sq.mk e.inv.w)),
end

lemma stable_under_base_change.fst {P : morphism_property C}
  (hP : stable_under_base_change P) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [has_pullback f g]
  (H : P g) : P (pullback.fst : pullback f g ⟶ X) :=
hP (is_pullback.of_has_pullback f g).flip H

lemma stable_under_base_change.snd {P : morphism_property C}
  (hP : stable_under_base_change P) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S) [has_pullback f g]
  (H : P f) : P (pullback.snd : pullback f g ⟶ Y) :=
hP (is_pullback.of_has_pullback f g) H

lemma stable_under_base_change.base_change_obj [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) {S S' : C} (f : S' ⟶ S)
  (X : over S) (H : P X.hom) : P ((base_change f).obj X).hom :=
hP.snd X.hom f H

lemma stable_under_base_change.base_change_map [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) {S S' : C} (f : S' ⟶ S)
  {X Y : over S} (g : X ⟶ Y) (H : P g.left) : P ((base_change f).map g).left :=
begin
  let e := pullback_right_pullback_fst_iso Y.hom f g.left ≪≫
    pullback.congr_hom (g.w.trans (category.comp_id _)) rfl,
  have : e.inv ≫ pullback.snd = ((base_change f).map g).left,
  { apply pullback.hom_ext; dsimp; simp },
  rw [← this, hP.respects_iso.cancel_left_is_iso],
  exact hP.snd _ _ H,
end

lemma stable_under_base_change.pullback_map [has_pullbacks C] {P : morphism_property C}
  (hP : stable_under_base_change P) (hP' : stable_under_composition P) {S X X' Y Y' : C}
  {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ S} {g' : Y' ⟶ S} {i₁ : X ⟶ X'} {i₂ : Y ⟶ Y'}
  (h₁ : P i₁) (h₂ : P i₂) (e₁ : f = i₁ ≫ f') (e₂ : g = i₂ ≫ g') :
    P (pullback.map f g f' g' i₁ i₂ (𝟙 _)
      ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂)) :=
begin
  have : pullback.map f g f' g' i₁ i₂ (𝟙 _)
    ((category.comp_id _).trans e₁) ((category.comp_id _).trans e₂) =
      ((pullback_symmetry _ _).hom ≫
      ((base_change _).map (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g')).left) ≫
      (pullback_symmetry _ _).hom ≫
      ((base_change g').map (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f')).left,
  { apply pullback.hom_ext; dsimp; simp },
  rw this,
  apply hP'; rw hP.respects_iso.cancel_left_is_iso,
  exacts [hP.base_change_map _ (over.hom_mk _ e₂.symm : over.mk g ⟶ over.mk g') h₂,
    hP.base_change_map _ (over.hom_mk _ e₁.symm : over.mk f ⟶ over.mk f') h₁],
end

/-- If `P : morphism_property C` and `F : C ⥤ D`, then
`P.is_inverted_by F` means that all morphisms in `P` are mapped by `F`
to isomorphisms in `D`. -/
def is_inverted_by (P : morphism_property C) (F : C ⥤ D) : Prop :=
∀ ⦃X Y : C⦄ (f : X ⟶ Y) (hf : P f), is_iso (F.map f)

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `morphism_property C` satisfied by the morphisms in `C` with respect
to whom `app` is natural. -/
@[simp]
def naturality_property {F₁ F₂ : C ⥤ D} (app : Π X, F₁.obj X ⟶ F₂.obj X) :
  morphism_property C := λ X Y f, F₁.map f ≫ app Y = app X ≫ F₂.map f

namespace naturality_property

lemma is_stable_under_composition {F₁ F₂ : C ⥤ D} (app : Π X, F₁.obj X ⟶ F₂.obj X) :
  (naturality_property app).stable_under_composition := λ X Y Z f g hf hg,
begin
  simp only [naturality_property] at ⊢ hf hg,
  simp only [functor.map_comp, category.assoc, hg],
  slice_lhs 1 2 { rw hf },
  rw category.assoc,
end

lemma is_stable_under_inverse {F₁ F₂ : C ⥤ D} (app : Π X, F₁.obj X ⟶ F₂.obj X) :
  (naturality_property app).stable_under_inverse := λ X Y e he,
begin
  simp only [naturality_property] at ⊢ he,
  rw ← cancel_epi (F₁.map e.hom),
  slice_rhs 1 2 { rw he },
  simp only [category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp,
    e.hom_inv_id, functor.map_id, category.id_comp, category.comp_id],
end

end naturality_property

end morphism_property

end category_theory
