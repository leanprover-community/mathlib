/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.ring_hom_properties
import topology.local_at_target

/-!

# Open immersions

A morphism is an open immersions if the underlying map of spaces is an open embedding
`f : X ⟶ U ⊆ Y`, and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Most of the theories are developed in `algebraic_geometry/open_immersion`, and we provide the
remaining theorems analogous to other lemmas in `algebraic_geometry/morphisms/*`.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

variables {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma is_open_immersion_iff_stalk {f : X ⟶ Y} :
  is_open_immersion f ↔
    open_embedding f.1.base ∧ ∀ x, is_iso (PresheafedSpace.stalk_map f.1 x) :=
begin
  split,
  { intro h, exactI ⟨h.1, infer_instance⟩ },
  { rintro ⟨h₁, h₂⟩, exactI is_open_immersion.of_stalk_iso f h₁ }
end

lemma is_open_immersion_stable_under_composition :
  morphism_property.stable_under_composition @is_open_immersion :=
begin
  introsI X Y Z f g h₁ h₂, apply_instance
end

lemma is_open_immersion_respects_iso :
  morphism_property.respects_iso @is_open_immersion :=
begin
  apply is_open_immersion_stable_under_composition.respects_iso,
  intros _ _ _, apply_instance
end

lemma morphism_restrict_val_base {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) :
  ⇑(f ∣_ U).1.base = U.1.restrict_preimage f.1.base :=
funext (λ x, subtype.ext (morphism_restrict_base_coe f U x))

lemma morphism_restrict_stalk_map {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) (x) :
  arrow.mk (PresheafedSpace.stalk_map (f ∣_ U).1 x) ≅
    arrow.mk (PresheafedSpace.stalk_map f.1 x.1) :=
begin
  fapply arrow.iso_mk',
  { refine Y.restrict_stalk_iso U.open_embedding ((f ∣_ U).1 x) ≪≫ Top.presheaf.stalk_congr _ _,
    apply inseparable.of_eq,
    exact morphism_restrict_base_coe f U x },
  { exact X.restrict_stalk_iso _ _ },
  { apply Top.presheaf.stalk_hom_ext,
    intros V hxV,
    simp only [Top.presheaf.stalk_congr_hom, category_theory.category.assoc,
      category_theory.iso.trans_hom],
    erw PresheafedSpace.restrict_stalk_iso_hom_eq_germ_assoc,
    erw PresheafedSpace.stalk_map_germ_assoc _ _ ⟨_, _⟩,
    rw [Top.presheaf.germ_stalk_specializes'_assoc],
    erw PresheafedSpace.stalk_map_germ _ _ ⟨_, _⟩,
    erw PresheafedSpace.restrict_stalk_iso_hom_eq_germ,
    rw [morphism_restrict_c_app, category.assoc, Top.presheaf.germ_res],
    refl }
end

lemma is_open_immersion_is_local_at_target : property_is_local_at_target @is_open_immersion :=
begin
  constructor,
  { exact is_open_immersion_respects_iso },
  { introsI, apply_instance },
  { intros X Y f 𝒰 H,
    rw is_open_immersion_iff_stalk,
    split,
    { apply (open_embedding_iff_open_embedding_of_supr_eq_top
        𝒰.supr_opens_range f.1.base.2).mpr,
      intro i,
      have := ((is_open_immersion_respects_iso.arrow_iso_iff
        (morphism_restrict_opens_range f (𝒰.map i))).mpr (H i)).1,
      rwa [arrow.mk_hom, morphism_restrict_val_base] at this },
    { intro x,
      have := arrow.iso_w (morphism_restrict_stalk_map f ((𝒰.map $ 𝒰.f $ f.1 x).opens_range)
        ⟨x, 𝒰.covers _⟩),
      dsimp only [arrow.mk_hom] at this,
      rw this,
      haveI : is_open_immersion (f ∣_ (𝒰.map $ 𝒰.f $ f.1 x).opens_range) :=
        (is_open_immersion_respects_iso.arrow_iso_iff
          (morphism_restrict_opens_range f (𝒰.map _))).mpr (H _),
      apply_instance } }
end

lemma is_open_immersion.open_cover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
  tfae [is_open_immersion f,
    ∃ (𝒰 : Scheme.open_cover.{u} Y), ∀ (i : 𝒰.J),
      is_open_immersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (𝒰 : Scheme.open_cover.{u} Y) (i : 𝒰.J),
      is_open_immersion (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
    ∀ (U : opens Y.carrier), is_open_immersion (f ∣_ U),
    ∀ {U : Scheme} (g : U ⟶ Y) [is_open_immersion g],
      is_open_immersion (pullback.snd : pullback f g ⟶ _),
    ∃ {ι : Type u} (U : ι → opens Y.carrier) (hU : supr U = ⊤),
      ∀ i, is_open_immersion (f ∣_ (U i))] :=
is_open_immersion_is_local_at_target.open_cover_tfae f

lemma is_open_immersion.open_cover_iff {X Y : Scheme.{u}}
  (𝒰 : Scheme.open_cover.{u} Y) (f : X ⟶ Y) :
  is_open_immersion f ↔ ∀ i, is_open_immersion (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
is_open_immersion_is_local_at_target.open_cover_iff f 𝒰

lemma is_open_immersion_stable_under_base_change :
  morphism_property.stable_under_base_change @is_open_immersion :=
morphism_property.stable_under_base_change.mk is_open_immersion_respects_iso $
  by { introsI X Y Z f g H, apply_instance }

end algebraic_geometry
