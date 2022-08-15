/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.basic
import ring_theory.local_properties

/-!
# Properties of morphisms from properties of ring homs.

We provide the basic framework for talking about properties of morphisms that comes from properties
of ring homs. For `P` a property of ring homs, we have two ways of defining a property of scheme
morphisms:

Let `f : X ⟶ Y`,
- `affine_and P`: the preimage of an affine open `U = Spec A` is affine (`= Spec B`) and `A ⟶ B`
  satisfies `P`.
- `target_affine_locally (source_affine_locally P)`: For each pair of affine open
  `U = Spec A ⊆ X` and `V = Spec B ⊆ f ⁻¹' U`, the ring hom `A ⟶ B` satisfies `P`.

For these notions to be well defined, we require `P` be a sufficient local property. For the former,
`P` should be local on source (`ring_hom.respects_iso P`, `ring_hom.localization_preserves P`,
`ring_hom.of_localization_span`), and `affine_and P` will be local on target. (TODO)

For the latter `P` should be local on both the source and the target `ring_hom.property_is_local P`,
and `target_affine_locally (source_affine_locally P)` will also be local on both the source and the
target.

Further more, these properties are stable under compositions (resp. base change) if `P` is. (TODO)

-/

universe u

open category_theory opposite topological_space category_theory.limits algebraic_geometry

variable (P : ∀ {R S : Type u} [comm_ring R] [comm_ring S] (f : by exactI R →+* S), Prop)

instance {C : Type*} [category C] {X Y : Cᵒᵖ} (f : X ⟶ Y) [H : is_iso f] : is_iso f.unop :=
@@is_iso_of_op _ f.unop H

namespace algebraic_geometry

instance {X : Scheme} [is_affine X] (r : X.presheaf.obj (op ⊤)) :
  is_localization.away r (X.presheaf.obj (op $ X.basic_open r)) :=
is_localization_basic_open (top_is_affine_open X) r

instance Γ_restrict_algebra
  {X : Scheme} {Y : Top} {f : Y ⟶ X.carrier} (hf : open_embedding f) :
  algebra (Scheme.Γ.obj (op X)) (Scheme.Γ.obj (op $ X.restrict hf)) :=
(Scheme.Γ.map (X.of_restrict hf).op).to_algebra

 lemma is_localization_of_eq_basic_open {X : Scheme} {U V : opens X.carrier} (i : V ⟶ U)
   (hU : is_affine_open U) (r : X.presheaf.obj (op U)) (e : V = X.basic_open r) :
   @@is_localization.away _ r (X.presheaf.obj (op V)) _ (X.presheaf.map i.op).to_algebra :=
 by { subst e, convert is_localization_basic_open hU r using 3 }

instance Γ_restrict_is_localization (X : Scheme.{u}) [is_affine X] (r : Scheme.Γ.obj (op X)) :
   is_localization.away r (Scheme.Γ.obj (op $ X.restrict (X.basic_open r).open_embedding)) :=
 is_localization_of_eq_basic_open _ (top_is_affine_open X) r (opens.open_embedding_obj_top _)

lemma _root_.opens.functor_obj_map_obj {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f) (U : opens Y) :
  hf.functor.obj ((opens.map f).obj U) = hf.functor.obj ⊤ ⊓ U :=
begin
  ext, split,
  { rintros ⟨x, hx, rfl⟩, exact ⟨⟨x, trivial, rfl⟩, hx⟩ },
  { rintros ⟨⟨x, -, rfl⟩, hx⟩, exact ⟨x, hx, rfl⟩ }
end

def AffineScheme.of (X : Scheme) [h : is_affine X] : AffineScheme :=
AffineScheme.mk X h

def AffineScheme.of_hom {X Y : Scheme} [is_affine X] [is_affine Y] (f : X ⟶ Y) :
  AffineScheme.of X ⟶ AffineScheme.of Y :=
f

noncomputable
instance : preserves_limits AffineScheme.Γ.{u}.right_op :=
@@adjunction.is_equivalence_preserves_limits _ _ AffineScheme.Γ.right_op
  (is_equivalence.of_equivalence AffineScheme.equiv_CommRing)

noncomputable
instance : preserves_limits AffineScheme.forget_to_Scheme :=
begin
  apply_with (@@preserves_limits_of_nat_iso _ _
    (iso_whisker_right AffineScheme.equiv_CommRing.unit_iso AffineScheme.forget_to_Scheme).symm) { instances := ff },
  change preserves_limits (AffineScheme.equiv_CommRing.functor ⋙ Scheme.Spec),
  apply_instance,
end

lemma is_affine_open_iff_of_is_open_immersion {X Y : Scheme} (f : X ⟶ Y) [H : is_open_immersion f]
  (U : opens X.carrier) :
  is_affine_open (H.open_functor.obj U) ↔ is_affine_open U :=
begin
  refine ⟨λ hU, @@is_affine_of_iso _ _ hU, λ hU, hU.image_is_open_immersion f⟩,
  refine (is_open_immersion.iso_of_range_eq (X.of_restrict _ ≫ f) (Y.of_restrict _) _).hom,
  { rw [Scheme.comp_val_base, coe_comp, set.range_comp],
    dsimp [opens.inclusion],
    rw [subtype.range_coe, subtype.range_coe],
    refl },
  { apply_instance }
end

lemma is_affine_open.map_restrict_basic_open {X : Scheme} (r : X.presheaf.obj (op ⊤))
  {U : opens X.carrier} (hU : is_affine_open U) :
  is_affine_open ((opens.map (X.of_restrict (X.basic_open r).open_embedding).1.base).obj U) :=
begin
  apply (is_affine_open_iff_of_is_open_immersion
    (X.of_restrict (X.basic_open r).open_embedding) _).mp,
  delta PresheafedSpace.is_open_immersion.open_functor,
  dsimp,
  rw [opens.functor_obj_map_obj, opens.open_embedding_obj_top, inf_comm, ← opens.inter_eq,
    ← Scheme.basic_open_res _ _ (hom_of_le le_top).op],
  exact hU.basic_open_is_affine _,
end
.
lemma _root_.CommRing.comp_eq_ring_hom_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T) :
  f ≫ g = g.comp f := rfl

lemma _root_.CommRing.ring_hom_comp_eq_comp {R S T : Type*} [comm_ring R] [comm_ring S]
  [comm_ring T] (f : R →+* S) (g : S →+* T) :
  g.comp f = CommRing.of_hom f ≫ CommRing.of_hom g := rfl

instance {X Y : Scheme} (f : X ⟶ Y) (U : opens Y.carrier) [is_open_immersion f] :
  is_open_immersion (f ∣_ U) :=
by { delta morphism_restrict, apply_instance }

end algebraic_geometry

open algebraic_geometry

namespace ring_hom

include P

variable {P}

lemma respects_iso.basic_open_iff (hP : respects_iso @P) {X Y : Scheme}
  [is_affine X] [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (opposite.op ⊤)) :
  P (Scheme.Γ.map (f ∣_ Y.basic_open r).op) ↔
  P (@is_localization.away.map (Y.presheaf.obj (opposite.op ⊤)) _
      (Y.presheaf.obj (opposite.op $ Y.basic_open r)) _ _
      (X.presheaf.obj (opposite.op ⊤)) _ (X.presheaf.obj
      (opposite.op $ X.basic_open (Scheme.Γ.map f.op r))) _ _ (Scheme.Γ.map f.op) r _ _) :=
begin
  rw [Γ_map_morphism_restrict, hP.cancel_left_is_iso, hP.cancel_right_is_iso,
    ← (hP.cancel_right_is_iso (f.val.c.app (opposite.op (Y.basic_open r))) (X.presheaf.map
      (eq_to_hom (Scheme.preimage_basic_open f r).symm).op)), ← eq_iff_iff],
  congr,
  delta is_localization.away.map,
  refine is_localization.ring_hom_ext (submonoid.powers r) _,
  convert (is_localization.map_comp _).symm using 1,
  change Y.presheaf.map _ ≫ _ = _ ≫ X.presheaf.map _,
  rw f.val.c.naturality_assoc,
  erw ← X.presheaf.map_comp,
  congr,
end

lemma respects_iso.basic_open_iff_localization (hP : respects_iso @P)
  {X Y : Scheme} [is_affine X] [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (opposite.op ⊤)) :
  P (Scheme.Γ.map (f ∣_ Y.basic_open r).op) ↔
  P (localization.away_map (Scheme.Γ.map f.op) r) :=
(hP.basic_open_iff _ _).trans (hP.is_localization_away_iff _ _ _ _).symm

lemma respects_iso.of_restrict_morphism_restrict_iff (hP : ring_hom.respects_iso @P)
  {X Y : Scheme} [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (opposite.op ⊤))
  (U : opens X.carrier) (hU : is_affine_open U) {V : opens _}
  (e : V = (opens.map (X.of_restrict ((opens.map f.1.base).obj _).open_embedding).1.base).obj U) :
  P (Scheme.Γ.map ((X.restrict ((opens.map f.1.base).obj _).open_embedding).of_restrict
    V.open_embedding ≫ f ∣_ Y.basic_open r).op) ↔
    P (localization.away_map (Scheme.Γ.map (X.of_restrict U.open_embedding ≫ f).op) r) :=
begin
  subst e,
  convert (hP.is_localization_away_iff _ _ _ _).symm,
  rotate,
  { apply_instance },
  { apply ring_hom.to_algebra,
    refine X.presheaf.map
      (@hom_of_le _ _ ((is_open_map.functor _).obj _) ((is_open_map.functor _).obj _) _).op,
    rw [opens.le_def],
    dsimp,
    change coe '' (coe '' set.univ) ⊆ coe '' set.univ,
    rw [subtype.coe_image_univ, subtype.coe_image_univ],
    exact set.image_preimage_subset _ _ },
  { exact algebraic_geometry.Γ_restrict_is_localization Y r },
  { rw ← U.open_embedding_obj_top at hU,
    dsimp [Scheme.Γ_obj_op, Scheme.Γ_map_op, Scheme.restrict],
    apply algebraic_geometry.is_localization_of_eq_basic_open _ hU,
    rw [opens.open_embedding_obj_top, opens.functor_obj_map_obj],
    convert (X.basic_open_res (Scheme.Γ.map f.op r) (hom_of_le le_top).op).symm using 1,
    rw [opens.open_embedding_obj_top, opens.open_embedding_obj_top, inf_comm,
      Scheme.Γ_map_op, ← Scheme.preimage_basic_open],
    refl },
  { apply is_localization.ring_hom_ext (submonoid.powers r) _,
    swap, { exact algebraic_geometry.Γ_restrict_is_localization Y r },
    rw [is_localization.away.map, is_localization.map_comp, ring_hom.algebra_map_to_algebra,
      ring_hom.algebra_map_to_algebra, op_comp, functor.map_comp, op_comp, functor.map_comp],
    refine (@category.assoc CommRing _ _ _ _ _ _ _ _).symm.trans _,
    refine eq.trans _ (@category.assoc CommRing _ _ _ _ _ _ _ _),
    dsimp only [Scheme.Γ_map, quiver.hom.unop_op],
    rw [morphism_restrict_c_app, category.assoc, category.assoc, category.assoc],
    erw [f.1.c.naturality_assoc, ← X.presheaf.map_comp, ← X.presheaf.map_comp,
      ← X.presheaf.map_comp],
    congr },
end

lemma stable_under_base_change.Γ_pullback_fst
  (hP : stable_under_base_change @P) (hP' : respects_iso @P) {X Y S : Scheme}
  [is_affine X] [is_affine Y] [is_affine S]
  (f : X ⟶ S) (g : Y ⟶ S) (H : P (Scheme.Γ.map g.op)) :
    P (Scheme.Γ.map (pullback.fst : pullback f g ⟶ _).op) :=
begin
  rw [← preserves_pullback.iso_inv_fst AffineScheme.forget_to_Scheme
    (AffineScheme.of_hom f) (AffineScheme.of_hom g), op_comp, functor.map_comp,
    hP'.cancel_right_is_iso, AffineScheme.forget_to_Scheme_map],
  have := _root_.congr_arg quiver.hom.unop (preserves_pullback.iso_hom_fst AffineScheme.Γ.right_op
    (AffineScheme.of_hom f) (AffineScheme.of_hom g)),
  simp only [quiver.hom.unop_op, functor.right_op_map, unop_comp] at this,
  delta AffineScheme.Γ at this,
  simp only [quiver.hom.unop_op, functor.comp_map, AffineScheme.forget_to_Scheme_map,
    functor.op_map] at this,
  rw [← this, hP'.cancel_right_is_iso,
    ← pushout_iso_unop_pullback_inl_hom (quiver.hom.unop _) (quiver.hom.unop _),
    hP'.cancel_right_is_iso],
  exact hP.pushout_inl _ hP' _ _ H
end

end ring_hom

namespace algebraic_geometry

def source_affine_locally : affine_target_morphism_property :=
λ X Y f hY, ∀ (U : X.affine_opens), P (Scheme.Γ.map (X.of_restrict U.1.open_embedding ≫ f).op)

abbreviation affine_locally : morphism_property Scheme :=
target_affine_locally (source_affine_locally @P)

lemma affine_target_morphism_property.respects_iso_mk {P : affine_target_morphism_property}
   (h₁ : ∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [is_affine Z], by exactI P f → P (e.hom ≫ f))
   (h₂ : ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [h : is_affine Y],
      by exactI P f → @@P (f ≫ e.hom) (is_affine_of_iso e.inv)) : P.to_property.respects_iso :=
 begin
   split,
   { rintros X Y Z e f ⟨a, h⟩, exactI ⟨a, h₁ e f h⟩ },
   { rintros X Y Z e f ⟨a, h⟩, exactI ⟨is_affine_of_iso e.inv, h₂ e f h⟩ },
 end

variable {P}

lemma source_affine_locally_respects_iso (h₁ : ring_hom.respects_iso @P) :
  (source_affine_locally @P).to_property.respects_iso :=
begin
  apply affine_target_morphism_property.respects_iso_mk,
  { introv H U,
    rw [← h₁.cancel_right_is_iso _ (Scheme.Γ.map (Scheme.restrict_map_iso e.inv U.1).hom.op),
      ← functor.map_comp, ← op_comp],
    convert H ⟨_, U.prop.map_is_iso e.inv⟩ using 3,
    rw [is_open_immersion.iso_of_range_eq_hom, is_open_immersion.lift_fac_assoc,
      category.assoc, e.inv_hom_id_assoc],
    refl },
  { introv H U,
    rw [← category.assoc, op_comp, functor.map_comp, h₁.cancel_left_is_iso],
    exact H U }
end

lemma localization_preserves.Scheme_restrict_basic_open
  (h₁ : ring_hom.respects_iso @P)
  (h₂ : ring_hom.localization_preserves @P)
  {X Y : Scheme} [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (op ⊤))
  (H : source_affine_locally @P f)
  (U : (X.restrict ((opens.map f.1.base).obj $ Y.basic_open r).open_embedding).affine_opens) :
  P (Scheme.Γ.map
    ((X.restrict ((opens.map f.1.base).obj $ Y.basic_open r).open_embedding).of_restrict
      U.1.open_embedding ≫ f ∣_ Y.basic_open r).op) :=
begin
  specialize H ⟨_, U.2.image_is_open_immersion (X.of_restrict _)⟩,
  convert (h₁.of_restrict_morphism_restrict_iff _ _ _ _ _).mpr _ using 1,
  swap 5,
  { exact h₂.away r H },
  { apply_instance },
  { exact U.2.image_is_open_immersion _},
  { ext1, exact (set.preimage_image_eq _ subtype.coe_injective).symm }
end

lemma is_local_source_affine_locally
  (h₁ : ring_hom.respects_iso @P)
  (h₂ : ring_hom.localization_preserves @P)
  (h₃ : ring_hom.of_localization_span @P) : (source_affine_locally @P).is_local :=
begin
  constructor,
  { exact source_affine_locally_respects_iso h₁ },
  { introv H U,
    apply localization_preserves.Scheme_restrict_basic_open h₁ h₂; assumption },
  { introv hs hs' U,
    resetI,
    apply h₃ _ _ hs,
    intro r,
    have := hs' r ⟨(opens.map (X.of_restrict _).1.base).obj U.1, _⟩,
    rwa h₁.of_restrict_morphism_restrict_iff at this,
    { exact U.2 },
    { refl },
    { apply_instance },
    { suffices : ∀ (V = (opens.map f.val.base).obj (Y.basic_open r.val)),
        is_affine_open ((opens.map (X.of_restrict V.open_embedding).1.base).obj U.1),
      { exact this _ rfl, },
      intros V hV,
      rw Scheme.preimage_basic_open at hV,
      subst hV,
      exact U.2.map_restrict_basic_open (Scheme.Γ.map f.op r.1) } }
end

variables {P} (hP : ring_hom.property_is_local @P)

lemma source_affine_locally_of_source_open_cover_aux
  (h₁ : ring_hom.respects_iso @P)
  (h₃ : ring_hom.of_localization_span_target @P)
  {X Y : Scheme} (f : X ⟶ Y) [is_affine Y] (U : X.affine_opens)
  (s : set (X.presheaf.obj (op U.1))) (hs : ideal.span s = ⊤)
  (hs' : ∀ (r : s), P (Scheme.Γ.map (X.of_restrict (X.basic_open r.1).open_embedding ≫ f).op)) :
    P (Scheme.Γ.map (X.of_restrict U.1.open_embedding ≫ f).op) :=
begin
  apply_fun ideal.map (X.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op) at hs,
  rw [ideal.map_span, ideal.map_top] at hs,
  apply h₃ _ _ hs,
  rintro ⟨s, r, hr, hs⟩,
  have := (@@localization.alg_equiv _ _ _ _ _ (@@algebraic_geometry.Γ_restrict_is_localization
    _ U.2 s)).to_ring_equiv.to_CommRing_iso,
  refine (h₁.cancel_right_is_iso _ (@@localization.alg_equiv _ _ _ _ _
    (@@algebraic_geometry.Γ_restrict_is_localization _ U.2 s)).to_ring_equiv.to_CommRing_iso.hom).mp _,
  subst hs,
  rw [CommRing.comp_eq_ring_hom_comp, ← ring_hom.comp_assoc],
  erw [is_localization.map_comp, ring_hom.comp_id],
  rw [ring_hom.algebra_map_to_algebra, op_comp, functor.map_comp, ← CommRing.comp_eq_ring_hom_comp,
    Scheme.Γ_map_op, Scheme.Γ_map_op, Scheme.Γ_map_op, category.assoc],
  erw ← X.presheaf.map_comp,
  rw [← h₁.cancel_right_is_iso _ (X.presheaf.map (eq_to_hom _))],
  convert hs' ⟨r, hr⟩ using 1,
  { erw category.assoc, rw [← X.presheaf.map_comp, op_comp, Scheme.Γ.map_comp,
    Scheme.Γ_map_op, Scheme.Γ_map_op], congr },
  { dsimp [functor.op],
    conv_lhs { rw opens.open_embedding_obj_top },
    conv_rhs { rw opens.open_embedding_obj_top },
    erw is_open_immersion.image_basic_open (X.of_restrict U.1.open_embedding),
    erw PresheafedSpace.is_open_immersion.of_restrict_inv_app_apply,
    rw Scheme.basic_open_res_eq },
  { apply_instance }
end

lemma is_open_immersion_comp_of_source_affine_locally (h₁ : ring_hom.respects_iso @P)
  {X Y Z : Scheme} [is_affine X] [is_affine Z] (f : X ⟶ Y) [is_open_immersion f] (g : Y ⟶ Z)
  (h₂ : source_affine_locally @P g) :
  P (Scheme.Γ.map (f ≫ g).op) :=
begin
  rw [← h₁.cancel_right_is_iso _ (Scheme.Γ.map (is_open_immersion.iso_of_range_eq
    (Y.of_restrict _) f _).hom.op), ← functor.map_comp, ← op_comp],
  convert h₂ ⟨_, range_is_affine_open_of_open_immersion f⟩ using 3,
  { rw [is_open_immersion.iso_of_range_eq_hom, is_open_immersion.lift_fac_assoc] },
  { apply_instance },
  { exact subtype.range_coe },
  { apply_instance }
end

lemma affine_locally_respects_iso (h : ring_hom.respects_iso @P) :
  (affine_locally @P).respects_iso :=
target_affine_locally_respects_iso (source_affine_locally_respects_iso h)

include hP

lemma _root_.ring_hom.property_is_local.source_affine_locally_of_source_open_cover
  {X Y : Scheme} (f : X ⟶ Y) [is_affine Y]
  (𝒰 : X.open_cover) [∀ i, is_affine (𝒰.obj i)] (H : ∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op)) :
  source_affine_locally @P f :=
begin
  let S := λ i, (⟨⟨set.range (𝒰.map i).1.base, (𝒰.is_open i).base_open.open_range⟩,
    range_is_affine_open_of_open_immersion (𝒰.map i)⟩ : X.affine_opens),
  intros U,
  apply of_affine_open_cover U,
  swap 5, { exact set.range S },
  { intros U r H,
    convert hP.stable_under_composition _ _ H _ using 1,
    swap,
    { refine X.presheaf.map
        (@hom_of_le _ _ ((is_open_map.functor _).obj _) ((is_open_map.functor _).obj _) _).op,
      rw [unop_op, unop_op, opens.open_embedding_obj_top, opens.open_embedding_obj_top],
      exact X.basic_open_subset _ },
    { rw [op_comp, op_comp, functor.map_comp, functor.map_comp],
      refine (eq.trans _ (category.assoc _ _ _).symm : _),
      congr' 1,
      refine eq.trans _ (X.presheaf.map_comp _ _),
      change X.presheaf.map _ = _,
      congr },
    convert hP.holds_for_localization_away _ (X.presheaf.map (eq_to_hom U.1.open_embedding_obj_top).op r),
    { exact (ring_hom.algebra_map_to_algebra _).symm },
    { dsimp [Scheme.Γ],
      have := U.2,
      rw ← U.1.open_embedding_obj_top at this,
      convert is_localization_basic_open this _ using 6;
        rw opens.open_embedding_obj_top; exact (Scheme.basic_open_res_eq _ _ _).symm } },
  { introv hs hs',
    exact source_affine_locally_of_source_open_cover_aux hP.respects_iso hP.2 _ _ _ hs hs' },
  { rw set.eq_univ_iff_forall,
    intro x,
    rw set.mem_Union,
    exact ⟨⟨_, 𝒰.f x, rfl⟩, 𝒰.covers x⟩ },
  { rintro ⟨_, i, rfl⟩,
    specialize H i,
    rw ← hP.respects_iso.cancel_right_is_iso _ (Scheme.Γ.map (is_open_immersion.iso_of_range_eq
      (𝒰.map i) (X.of_restrict (S i).1.open_embedding) subtype.range_coe.symm).inv.op) at H,
    rwa [← Scheme.Γ.map_comp, ← op_comp, is_open_immersion.iso_of_range_eq_inv,
      is_open_immersion.lift_fac_assoc] at H }
end

lemma _root_.ring_hom.property_is_local.affine_open_cover_tfae {X Y : Scheme.{u}}
  [is_affine Y] (f : X ⟶ Y) :
  tfae [source_affine_locally @P f,
    ∃ (𝒰 : Scheme.open_cover.{u} X) [∀ i, is_affine (𝒰.obj i)],
      ∀ (i : 𝒰.J), P (Scheme.Γ.map (𝒰.map i ≫ f).op),
    ∀ (𝒰 : Scheme.open_cover.{u} X) [∀ i, is_affine (𝒰.obj i)] (i : 𝒰.J),
      P (Scheme.Γ.map (𝒰.map i ≫ f).op),
    ∀ {U : Scheme} (g : U ⟶ X) [is_affine U] [is_open_immersion g],
      P (Scheme.Γ.map (g ≫ f).op)] :=
begin
  tfae_have : 1 → 4,
  { intros H U g _ hg,
    resetI,
    specialize H ⟨⟨_, hg.base_open.open_range⟩,
      range_is_affine_open_of_open_immersion g⟩,
    rw [← hP.respects_iso.cancel_right_is_iso _ (Scheme.Γ.map (is_open_immersion.iso_of_range_eq
      g (X.of_restrict (opens.open_embedding ⟨_, hg.base_open.open_range⟩))
      subtype.range_coe.symm).hom.op), ← Scheme.Γ.map_comp, ← op_comp,
      is_open_immersion.iso_of_range_eq_hom] at H,
    erw is_open_immersion.lift_fac_assoc at H,
    exact H },
  tfae_have : 4 → 3,
  { intros H 𝒰 _ i, resetI, apply H },
  tfae_have : 3 → 2,
  { intro H, refine ⟨X.affine_cover, infer_instance, H _⟩ },
  tfae_have : 2 → 1,
  { rintro ⟨𝒰, _, h𝒰⟩,
    exactI hP.source_affine_locally_of_source_open_cover f 𝒰 h𝒰 },
  tfae_finish
end

lemma _root_.ring_hom.property_is_local.open_cover_tfae {X Y : Scheme.{u}} [is_affine Y] (f : X ⟶ Y) :
  tfae [source_affine_locally @P f,
    ∃ (𝒰 : Scheme.open_cover.{u} X), ∀ (i : 𝒰.J), source_affine_locally @P (𝒰.map i ≫ f),
    ∀ (𝒰 : Scheme.open_cover.{u} X) (i : 𝒰.J), source_affine_locally @P (𝒰.map i ≫ f),
    ∀ {U : Scheme} (g : U ⟶ X) [is_open_immersion g], source_affine_locally @P (g ≫ f)] :=
begin
  tfae_have : 1 → 4,
  { intros H U g hg V,
    resetI,
    rw (hP.affine_open_cover_tfae f).out 0 3 at H,
    haveI : is_affine _ := V.2,
    rw ← category.assoc,
    apply H },
  tfae_have : 4 → 3,
  { intros H 𝒰 _ i, resetI, apply H },
  tfae_have : 3 → 2,
  { intro H, refine ⟨X.affine_cover, H _⟩ },
  tfae_have : 2 → 1,
  { rintro ⟨𝒰, h𝒰⟩,
    rw (hP.affine_open_cover_tfae f).out 0 1,
    refine ⟨𝒰.bind (λ _, Scheme.affine_cover _), _, _⟩,
    { intro i, dsimp, apply_instance },
    { intro i,
      specialize h𝒰 i.1,
      rw (hP.affine_open_cover_tfae (𝒰.map i.fst ≫ f)).out 0 3 at h𝒰,
      erw category.assoc,
      apply @@h𝒰 _ (show _, from _),
      dsimp, apply_instance } },
  tfae_finish
end

lemma _root_.ring_hom.property_is_local.source_affine_locally_of_is_open_immersion_comp
  {X Y Z : Scheme.{u}} [is_affine Z] (f : X ⟶ Y) (g : Y ⟶ Z) [is_open_immersion f]
  (H : source_affine_locally @P g) : source_affine_locally @P (f ≫ g) :=
by apply ((hP.open_cover_tfae g).out 0 3).mp H

lemma _root_.ring_hom.property_is_local.source_affine_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  [is_affine Y] (𝒰 : Scheme.open_cover.{u} X) [∀ i, is_affine (𝒰.obj i)] :
  source_affine_locally @P f ↔ (∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op)) :=
⟨λ H, let h := ((hP.affine_open_cover_tfae f).out 0 2).mp H in h 𝒰,
  λ H, let h := ((hP.affine_open_cover_tfae f).out 1 0).mp in h ⟨𝒰, infer_instance, H⟩⟩

lemma affine_locally_iff_affine_opens_le
  (hP : ring_hom.respects_iso @P) {X Y : Scheme} (f : X ⟶ Y) :
  affine_locally @P f ↔
  (∀ (U : Y.affine_opens) (V : X.affine_opens) (e : V.1 ≤ (opens.map f.1.base).obj U.1),
    P (f.1.c.app (op U) ≫ X.presheaf.map (hom_of_le e).op)) :=
begin
  apply forall_congr,
  intro U,
  delta source_affine_locally,
  simp_rw [op_comp, Scheme.Γ.map_comp, Γ_map_morphism_restrict, category.assoc, Scheme.Γ_map_op,
    hP.cancel_left_is_iso],
  split,
  { intros H V e,
    let U' := (opens.map f.val.base).obj U.1,
    have e' : U'.open_embedding.is_open_map.functor.obj ((opens.map U'.inclusion).obj V.1) = V.1,
    { ext1, refine set.image_preimage_eq_inter_range.trans (set.inter_eq_left_iff_subset.mpr _),
      convert e, exact subtype.range_coe },
    have := H ⟨(opens.map (X.of_restrict (U'.open_embedding)).1.base).obj V.1, _⟩,
    erw ← X.presheaf.map_comp at this,
    rw [← hP.cancel_right_is_iso _ (X.presheaf.map (eq_to_hom _)), category.assoc,
      ← X.presheaf.map_comp],
    convert this using 1,
    { dsimp only [functor.op, unop_op], rw opens.open_embedding_obj_top, congr' 1, exact e'.symm },
    { apply_instance },
    { apply (is_affine_open_iff_of_is_open_immersion (X.of_restrict _) _).mp,
      convert V.2,
      apply_instance } },
  { intros H V,
    specialize H ⟨_, V.2.image_is_open_immersion (X.of_restrict _)⟩ (subtype.coe_image_subset _ _),
    erw ← X.presheaf.map_comp,
    rw [← hP.cancel_right_is_iso _ (X.presheaf.map (eq_to_hom _)), category.assoc,
      ← X.presheaf.map_comp],
    convert H,
    { dsimp only [functor.op, unop_op], rw opens.open_embedding_obj_top, refl },
    { apply_instance } }
end

lemma _root_.ring_hom.property_is_local.is_local_source_affine_locally :
  (source_affine_locally @P).is_local :=
is_local_source_affine_locally hP.respects_iso hP.localization_preserves
  (@ring_hom.property_is_local.of_localization_span _ hP)

lemma _root_.ring_hom.property_is_local.affine_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} Y) [∀ i, is_affine (𝒰.obj i)]
  (𝒰' : ∀ i, Scheme.open_cover.{u} ((𝒰.pullback_cover f).obj i)) [∀ i j, is_affine ((𝒰' i).obj j)] :
  affine_locally @P f ↔
    (∀ i j, P (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op)) :=
(hP.is_local_source_affine_locally.affine_open_cover_iff f 𝒰).trans
    (forall_congr (λ i, hP.source_affine_open_cover_iff _ (𝒰' i)))

lemma _root_.ring_hom.property_is_local.source_open_cover_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
  (𝒰 : Scheme.open_cover.{u} X) :
  affine_locally @P f ↔ ∀ i, affine_locally @P (𝒰.map i ≫ f) :=
begin
  split,
  { intros H i U,
    rw morphism_restrict_comp,
    delta morphism_restrict,
    apply hP.source_affine_locally_of_is_open_immersion_comp,
    apply H },
  { intros H U,
    haveI : is_affine _ := U.2,
    apply ((hP.open_cover_tfae (f ∣_ U.1)).out 1 0).mp,
    use 𝒰.pullback_cover (X.of_restrict _),
    intro i,
    specialize H i U,
    rw morphism_restrict_comp at H,
    delta morphism_restrict at H,
    have := source_affine_locally_respects_iso hP.respects_iso,
    rw [category.assoc, affine_cancel_left_is_iso this, ← affine_cancel_left_is_iso
      this (pullback_symmetry _ _).hom, pullback_symmetry_hom_comp_snd_assoc] at H,
    exact H }
end

lemma affine_locally_of_is_open_immersion (hP : ring_hom.property_is_local @P) {X Y : Scheme}
  (f : X ⟶ Y) [hf : is_open_immersion f] : affine_locally @P f :=
begin
  intro U,
  haveI H : is_affine _ := U.2,
  rw ← category.comp_id (f ∣_ U),
  apply hP.source_affine_locally_of_is_open_immersion_comp,
  rw hP.source_affine_open_cover_iff _ (Scheme.open_cover_of_is_iso (𝟙 _)),
  { intro i, erw [category.id_comp, op_id, Scheme.Γ.map_id],
    convert hP.holds_for_localization_away _ (1 : Scheme.Γ.obj _),
    { exact (ring_hom.algebra_map_to_algebra _).symm },
    { apply_instance },
    { refine is_localization.away_of_is_unit_of_bijective _ is_unit_one function.bijective_id } },
  { intro i, exact H }
end
.
lemma affine_locally_stable_under_composition :
  (affine_locally @P).stable_under_composition :=
begin
  intros X Y S f g hf hg,
  let 𝒰 : ∀ i, ((S.affine_cover.pullback_cover (f ≫ g)).obj i).open_cover,
  { intro i,
    refine Scheme.open_cover.bind _ (λ i, Scheme.affine_cover _),
    apply Scheme.open_cover.pushforward_iso _
    (pullback_right_pullback_fst_iso g (S.affine_cover.map i) f).hom,
    apply Scheme.pullback.open_cover_of_right,
    exact (pullback g (S.affine_cover.map i)).affine_cover },
  rw hP.affine_open_cover_iff (f ≫ g) S.affine_cover _,
  rotate,
  { exact 𝒰 },
  { intros i j, dsimp at *, apply_instance },
  { rintros i ⟨j, k⟩,
    dsimp at i j k,
    dsimp only [Scheme.open_cover.bind_map, Scheme.open_cover.pushforward_iso_obj,
      Scheme.pullback.open_cover_of_right_obj, Scheme.open_cover.pushforward_iso_map,
      Scheme.pullback.open_cover_of_right_map, Scheme.open_cover.bind_obj],
    rw [category.assoc, category.assoc, pullback_right_pullback_fst_iso_hom_snd,
      pullback.lift_snd_assoc, category.assoc, ← category.assoc, op_comp, functor.map_comp],
    apply hP.stable_under_composition,
    { exact (hP.affine_open_cover_iff _ _ _).mp hg _ _ },
    { delta affine_locally at hf,
      rw (hP.is_local_source_affine_locally.affine_open_cover_tfae f).out 0 3 at hf,
      specialize hf ((pullback g (S.affine_cover.map i)).affine_cover.map j ≫ pullback.fst),
      rw (hP.affine_open_cover_tfae (pullback.snd : pullback f ((pullback g (S.affine_cover.map i))
        .affine_cover.map j ≫ pullback.fst) ⟶ _)).out 0 3 at hf,
      apply hf } }
end

end algebraic_geometry
