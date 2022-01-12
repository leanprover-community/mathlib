/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.Gamma_Spec_adjunction
import algebraic_geometry.open_immersion
import category_theory.limits.opposites

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `algebraic_geometry.AffineScheme`: The category of affine schemes.
* `algebraic_geometry.is_affine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `algebraic_geometry.Scheme.iso_Spec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `algebraic_geometry.AffineScheme.equiv_CommRing`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRing`.
* `algebraic_geometry.is_affine_open`: An open subset of a scheme is affine if the open subscheme is
  affine.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

/-- The category of affine schemes -/
def AffineScheme := Scheme.Spec.ess_image

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class is_affine (X : Scheme) : Prop :=
(affine : is_iso (Γ_Spec.adjunction.unit.app X))

attribute [instance] is_affine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
def Scheme.iso_Spec (X : Scheme) [is_affine X] :
  X ≅ Scheme.Spec.obj (op $ Scheme.Γ.obj $ op X) :=
as_iso (Γ_Spec.adjunction.unit.app X)

lemma mem_AffineScheme (X : Scheme) : X ∈ AffineScheme ↔ is_affine X :=
⟨λ h, ⟨functor.ess_image.unit_is_iso h⟩, λ h, @@mem_ess_image_of_unit_is_iso _ _ _ X h.1⟩

instance is_affine_AffineScheme (X : AffineScheme.{u}) : is_affine (X : Scheme.{u}) :=
(mem_AffineScheme _).mp X.prop

instance Spec_is_affine (R : CommRingᵒᵖ) : is_affine (Scheme.Spec.obj R) :=
(mem_AffineScheme _).mp (Scheme.Spec.obj_mem_ess_image R)

lemma is_affine_of_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] [h : is_affine Y] :
  is_affine X :=
by { rw [← mem_AffineScheme] at h ⊢, exact functor.ess_image.of_iso (as_iso f).symm h }

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
@[derive [full, faithful, ess_surj], simps]
def Spec : CommRingᵒᵖ ⥤ AffineScheme := Scheme.Spec.to_ess_image

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[derive [full, faithful], simps]
def forget_to_Scheme : AffineScheme ⥤ Scheme := Scheme.Spec.ess_image_inclusion

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRing := forget_to_Scheme.op ⋙ Scheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equiv_CommRing : AffineScheme ≌ CommRingᵒᵖ :=
equiv_ess_image_of_reflective.symm

instance Γ_is_equiv : is_equivalence Γ.{u} :=
begin
  haveI : is_equivalence Γ.{u}.right_op.op := is_equivalence.of_equivalence equiv_CommRing.op,
  exact (functor.is_equivalence_trans Γ.{u}.right_op.op (op_op_equivalence _).functor : _),
end

instance : has_colimits AffineScheme.{u} :=
begin
  haveI := adjunction.has_limits_of_equivalence.{u} Γ.{u},
  haveI : has_colimits AffineScheme.{u} ᵒᵖᵒᵖ := has_colimits_op_of_has_limits,
  exactI adjunction.has_colimits_of_equivalence.{u} (op_op_equivalence AffineScheme.{u}).inverse
end

instance : has_limits AffineScheme.{u} :=
begin
  haveI := adjunction.has_colimits_of_equivalence Γ.{u},
  haveI : has_limits AffineScheme.{u} ᵒᵖᵒᵖ := limits.has_limits_op_of_has_colimits,
  exactI adjunction.has_limits_of_equivalence (op_op_equivalence AffineScheme.{u}).inverse
end

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def is_affine_open {X : Scheme} (U : opens X.carrier) : Prop :=
is_affine (X.restrict U.open_embedding)

lemma range_is_affine_open_of_open_immersion {X Y : Scheme} [is_affine X] (f : X ⟶ Y)
  [H : is_open_immersion f] : is_affine_open ⟨set.range f.1.base, H.base_open.open_range⟩ :=
begin
  refine is_affine_of_iso (is_open_immersion.iso_of_range_eq f (Y.of_restrict _) _).inv,
  exact subtype.range_coe.symm,
  apply_instance
end

lemma top_is_affine_open (X : Scheme) [is_affine X] : is_affine_open (⊤ : opens X.carrier) :=
begin
  convert range_is_affine_open_of_open_immersion (𝟙 X),
  ext1,
  exact set.range_id.symm
end

instance Scheme.affine_basis_cover_is_affine (X : Scheme) (i : X.affine_basis_cover.J) :
  is_affine (X.affine_basis_cover.obj i) :=
algebraic_geometry.Spec_is_affine _

lemma is_basis_affine_open (X : Scheme) :
  opens.is_basis { U : opens X.carrier | is_affine_open U } :=
begin
  rw opens.is_basis_iff_nbhd,
  rintros U x (hU : x ∈ (U : set X.carrier)),
  obtain ⟨S, hS, hxS, hSU⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open hU U.prop,
  refine ⟨⟨S, X.affine_basis_cover_is_basis.is_open hS⟩, _, hxS, hSU⟩,
  rcases hS with ⟨i, rfl⟩,
  exact range_is_affine_open_of_open_immersion _,
end

/-- The open immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`. -/
def is_affine_open.from_Spec {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  Scheme.Spec.obj (op $ X.presheaf.obj $ op U) ⟶ X :=
begin
  haveI : is_affine (X.restrict U.open_embedding) := hU,
  have : U.open_embedding.is_open_map.functor.obj ⊤ = U,
  { ext1, exact set.image_univ.trans subtype.range_coe },
  exact Scheme.Spec.map (X.presheaf.map (eq_to_hom this.symm).op).op ≫
    (X.restrict U.open_embedding).iso_Spec.inv ≫ X.of_restrict _
end

instance is_affine_open.is_open_immersion_from_Spec {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  is_open_immersion hU.from_Spec :=
by { delta is_affine_open.from_Spec, apply_instance }

lemma is_affine_open.from_Spec_range {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  set.range hU.from_Spec.1.base = (U : set X.carrier) :=
begin
  delta is_affine_open.from_Spec,
  erw [← category.assoc, LocallyRingedSpace.comp_val, PresheafedSpace.comp_base],
  rw [coe_comp, set.range_comp, set.range_iff_surjective.mpr, set.image_univ],
  exact subtype.range_coe,
  rw ← Top.epi_iff_surjective,
  apply_instance
end

lemma is_affine_open.from_Spec_image_top {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  hU.is_open_immersion_from_Spec.base_open.is_open_map.functor.obj ⊤ = U :=
by { ext1, exact set.image_univ.trans hU.from_Spec_range }

lemma is_affine_open.is_compact {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  is_compact (U : set X.carrier) :=
begin
  convert @is_compact.image _ _ _ set.univ _ hU.from_Spec.1.base
    prime_spectrum.compact_space.1 (by continuity),
  convert hU.from_Spec_range.symm,
  exact set.image_univ
end

abbreviation Scheme.basic_open (X : Scheme) {U : opens X.carrier} (f : X.presheaf.obj (op U)) :
  opens X.carrier := X.to_LocallyRingedSpace.to_RingedSpace.basic_open f

lemma basic_open_eq_of_affine {R : CommRing} (f : R) :
  RingedSpace.basic_open (Spec.to_SheafedSpace.obj (op R)) ((Spec_Γ_identity.app R).inv f) =
    prime_spectrum.basic_open f :=
begin
  ext,
  change ↑(⟨x, trivial⟩ : (⊤ : opens _)) ∈
    RingedSpace.basic_open (Spec.to_SheafedSpace.obj (op R)) _ ↔ _,
  rw RingedSpace.mem_basic_open,
  suffices : is_unit (structure_sheaf.to_stalk R x f) ↔ f ∉ prime_spectrum.as_ideal x,
  { exact this },
  erw [← is_unit_map_iff (structure_sheaf.stalk_to_fiber_ring_hom R x),
    structure_sheaf.stalk_to_fiber_ring_hom_to_stalk],
  exact (is_localization.at_prime.is_unit_to_map_iff
    (localization.at_prime (prime_spectrum.as_ideal x)) (prime_spectrum.as_ideal x) f : _)
end

lemma basic_open_eq_of_affine' {R : CommRing}
  (f : (Spec.to_SheafedSpace.obj (op R)).presheaf.obj (op ⊤)) :
  RingedSpace.basic_open (Spec.to_SheafedSpace.obj (op R)) f =
    prime_spectrum.basic_open ((Spec_Γ_identity.app R).hom f) :=
begin
  convert basic_open_eq_of_affine ((Spec_Γ_identity.app R).hom f),
  exact (coe_hom_inv_id _ _).symm
end

lemma is_affine_open.from_Spec_base_preimage
  {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    (opens.map hU.from_Spec.val.base).obj U = ⊤ :=
begin
  ext1,
  change hU.from_Spec.1.base ⁻¹' (U : set X.carrier) = set.univ,
  rw [← hU.from_Spec_range, ← set.image_univ],
  exact set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj
end
.

lemma Γ_Spec.adjunction.unit.app_app_top (X : Scheme) :
  @eq ((Scheme.Spec.obj (op $ X.presheaf.obj (op ⊤))).presheaf.obj (op ⊤) ⟶
    ((Γ_Spec.adjunction.unit.app X).1.base _* X.presheaf).obj (op ⊤))
  ((Γ_Spec.adjunction.unit.app X).val.c.app (op ⊤))
    (Spec_Γ_identity.hom.app (X.presheaf.obj (op ⊤))) :=
begin
  have := congr_app Γ_Spec.adjunction.left_triangle X,
  dsimp at this,
  rw ← is_iso.eq_comp_inv at this,
  simp only [Γ_Spec.LocallyRingedSpace_adjunction_counit, nat_trans.op_app, category.id_comp,
    Γ_Spec.adjunction_counit_app] at this,
  rw [← op_inv, nat_iso.inv_inv_app, quiver.hom.op_inj.eq_iff] at this,
  exact this
end
.
@[reassoc, simp]
lemma Scheme.comp_val_c_app {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (f ≫ g).val.c.app U = g.val.c.app U ≫ f.val.c.app _ := rfl

lemma Scheme.congr_app {X Y : Scheme} {f g : X ⟶ Y} (e : f = g) (U) :
  f.val.c.app U = g.val.c.app U ≫ X.presheaf.map (eq_to_hom (by subst e)) :=
by { subst e, dsimp, simp, }

lemma _root_.topological_space.opens.open_embedding_obj_top {X : Top} (U : opens X) :
  U.open_embedding.is_open_map.functor.obj ⊤ = U :=
by { ext1, exact set.image_univ.trans subtype.range_coe }

lemma _root_.topological_space.opens.inclusion_map_eq_top {X : Top} (U : opens X) :
  (opens.map U.inclusion).obj U = ⊤ :=
by { ext1, exact subtype.coe_preimage_self _ }

lemma Scheme.Spec_map_presheaf_map_eq_to_hom {X : Scheme} {U V : opens X.carrier} (h : U = V) (W) :
  (Scheme.Spec.map (X.presheaf.map (eq_to_hom h).op).op).val.c.app W =
    eq_to_hom (by { cases h, dsimp, induction W using opposite.rec, congr, ext1, simpa }) :=
begin
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _,
  { rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]  },
  cases h,
  refine (Scheme.congr_app this _).trans _,
  erw category.id_comp,
  simpa
end

lemma is_affine_open.Spec_Γ_identity_hom_app_from_Spec {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  (Spec_Γ_identity.hom.app (X.presheaf.obj $ op U)) ≫ hU.from_Spec.1.c.app (op U) =
    (Scheme.Spec.obj _).presheaf.map (eq_to_hom hU.from_Spec_base_preimage).op :=
begin
  haveI : is_affine _ := hU,
  have e₁ :=
    Spec_Γ_identity.hom.naturality (X.presheaf.map (eq_to_hom U.open_embedding_obj_top).op),
  rw ← is_iso.comp_inv_eq at e₁,
  have e₂ := Γ_Spec.adjunction.unit.app_app_top (X.restrict U.open_embedding),
  erw ← e₂ at e₁,
  simp only [functor.id_map, quiver.hom.unop_op, functor.comp_map, ← functor.map_inv, ← op_inv,
    LocallyRingedSpace.Γ_map, category.assoc, functor.right_op_map, inv_eq_to_hom] at e₁,
  delta is_affine_open.from_Spec Scheme.iso_Spec,
  erw [LocallyRingedSpace.comp_val_c_app, LocallyRingedSpace.comp_val_c_app],
  rw ← e₁,
  simp_rw category.assoc,
  erw ← X.presheaf.map_comp_assoc,
  rw ← op_comp,
  have : U.open_embedding.is_open_map.adjunction.counit.app U ≫ eq_to_hom U.open_embedding_obj_top
    .symm = U.open_embedding.is_open_map.functor.map (eq_to_hom U.inclusion_map_eq_top) :=
    subsingleton.elim _ _,
  erw this,
  have : X.presheaf.map _ ≫ _ = _ :=
    (as_iso (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding)))
    .inv.1.c.naturality_assoc (eq_to_hom U.inclusion_map_eq_top).op _,
  erw this,
  erw ← Scheme.comp_val_c_app_assoc,
  erw iso.inv_hom_id,
  simp only [eq_to_hom_map, eq_to_hom_op, Scheme.Spec_map_presheaf_map_eq_to_hom],
  erw [Scheme.Spec_map_presheaf_map_eq_to_hom, category.id_comp],
  simpa only [eq_to_hom_trans]
end
.
@[elementwise]
lemma is_affine_open.from_Spec_app_eq {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  hU.from_Spec.1.c.app (op U) = Spec_Γ_identity.inv.app (X.presheaf.obj $ op U) ≫
    (Scheme.Spec.obj _).presheaf.map (eq_to_hom hU.from_Spec_base_preimage).op :=
by rw [← hU.Spec_Γ_identity_hom_app_from_Spec, iso.inv_hom_id_app_assoc]

lemma is_affine_open.basic_open_is_affine {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) : is_affine_open (X.basic_open f) :=
begin
  convert range_is_affine_open_of_open_immersion (Scheme.Spec.map (CommRing.of_hom
    (algebra_map (X.presheaf.obj (op U)) (localization.away f))).op ≫ hU.from_Spec),
  ext1,
  rw subtype.coe_mk,
  have : hU.from_Spec.val.base '' (hU.from_Spec.val.base ⁻¹' (X.basic_open f : set X.carrier)) =
    (X.basic_open f : set X.carrier),
  { rw [set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset, hU.from_Spec_range],
    exact RingedSpace.basic_open_subset _ _ },
  erw [LocallyRingedSpace.comp_val, PresheafedSpace.comp_base],
  rw [← this, coe_comp, set.range_comp],
  congr' 1,
  refine (congr_arg coe $ LocallyRingedSpace.preimage_basic_open hU.from_Spec f).trans _,
  refine eq.trans _ (prime_spectrum.localization_away_comap_range (localization.away f) f).symm,
  congr' 1,
  have : (opens.map hU.from_Spec.val.base).obj U = ⊤,
  { ext1,
    change hU.from_Spec.1.base ⁻¹' (U : set X.carrier) = set.univ,
    rw [← hU.from_Spec_range, ← set.image_univ],
    exact set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj },
  refine eq.trans _ (basic_open_eq_of_affine f),
  have lm : ∀ s, (opens.map hU.from_Spec.val.base).obj U ⊓ s = s := λ s, this.symm ▸ top_inf_eq,
  refine eq.trans _ (lm _),
  refine eq.trans _ ((Scheme.Spec.obj $ op $ X.presheaf.obj $ op U)
    .to_LocallyRingedSpace.to_RingedSpace.basic_open_res (eq_to_hom this).op _),
  rw ← comp_apply,
  congr' 2,
  rw iso.eq_inv_comp,
  erw hU.Spec_Γ_identity_hom_app_from_Spec,
  congr
end

instance Scheme.quasi_compact_of_affine (X : Scheme) [is_affine X] : compact_space X.carrier :=
⟨(top_is_affine_open X).is_compact⟩

instance is_LocallyRingedSpace_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] :
  @is_iso LocallyRingedSpace _ _ _ f :=
Scheme.forget_to_LocallyRingedSpace.map_is_iso f

instance is_SheafedSpace_iso {X Y : LocallyRingedSpace} (f : X ⟶ Y) [is_iso f] :
  is_iso f.1 :=
LocallyRingedSpace.forget_to_SheafedSpace.map_is_iso f

instance {C : Type*} [category C] [has_products C] {X Y : SheafedSpace C}
  (f : X ⟶ Y) [is_iso f] : is_iso f.c :=
@@PresheafedSpace.c_is_iso_of_iso _ f (SheafedSpace.forget_to_PresheafedSpace.map_is_iso f)

attribute [elementwise] functor.map_comp

lemma RingedSpace.basic_open_res_eq (X : RingedSpace) {U V : (opens X)ᵒᵖ} (i : U ⟶ V) [is_iso i]
  (f : X.presheaf.obj U) :
  @RingedSpace.basic_open X (unop V) (X.presheaf.map i f) = @RingedSpace.basic_open X (unop U) f :=
begin
  apply le_antisymm,
  { rw X.basic_open_res i f, exact inf_le_right },
  { have := X.basic_open_res (inv i) (X.presheaf.map i f),
    rw [← X.presheaf.map_comp_apply, is_iso.hom_inv_id, X.presheaf.map_id] at this,
    erw this,
    exact inf_le_right }
end

lemma LocallyRingedSpace.preimage_basic_open_of_iso {X Y : LocallyRingedSpace} (f : X ⟶ Y)
  [is_iso f]
  {U : opens X} (r : X.presheaf.obj (op U)) :
  (opens.map f.val.base).obj (Y.to_RingedSpace.basic_open
    (inv (f.val.c.app (op $ (opens.map (inv f).1.base).obj U)) (X.presheaf.map (eq_to_hom
      (by { dsimp, congr, ext1, change U.1 = f.1.base ⁻¹' ((inv f).1.base ⁻¹' U.1),
        rw [← set.preimage_comp, ← coe_comp, ← SheafedSpace.comp_base,
          ← LocallyRingedSpace.comp_val, is_iso.hom_inv_id], ext, refl })) r))) =
    X.to_RingedSpace.basic_open r :=
begin
  refine (LocallyRingedSpace.preimage_basic_open f _).trans _,
  rw is_iso.inv_hom_id_apply,
  erw RingedSpace.basic_open_res_eq,
end

lemma is_basis_basic_open (X : Scheme) [is_affine X] :
  opens.is_basis (set.range (X.basic_open : X.presheaf.obj (op ⊤) → opens X.carrier)) :=
begin
  delta opens.is_basis,
  convert prime_spectrum.is_basis_basic_opens.inducing
    (Top.homeo_of_iso (Scheme.forget_to_Top.map_iso X.iso_Spec)).inducing using 1,
  ext,
  simp only [set.mem_image, exists_exists_eq_and],
  suffices : ∀ (x : Scheme.Γ.obj (op X)),
    (opens.map X.iso_Spec.hom.1.base).obj (prime_spectrum.basic_open x) = X.basic_open x,
  { split,
    { rintro ⟨_, ⟨x, rfl⟩, rfl⟩,
      refine ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, _⟩,
      exact congr_arg subtype.val (this x) },
    { rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩,
      refine ⟨_, ⟨x, rfl⟩, _⟩,
      exact congr_arg subtype.val (this x).symm } },
  intro x,
  delta Scheme.basic_open,
  rw [← basic_open_eq_of_affine, ← LocallyRingedSpace.preimage_basic_open_of_iso X.iso_Spec.hom],
  congr,
  { rw [← is_iso.inv_eq_inv, is_iso.inv_inv, is_iso.iso.inv_inv, nat_iso.app_hom],
    erw ← Γ_Spec.adjunction.unit.app_app_top,
    refl },
  { rw eq_to_hom_map, refl }
end

attribute [elementwise] PresheafedSpace.is_open_immersion.inv_app_app

lemma image_basic_open_of_is_open_immersion {X Y: Scheme} (f : X ⟶ Y) [H : is_open_immersion f]
  {U : opens X.carrier} (r : X.presheaf.obj (op U)) :
  H.base_open.is_open_map.functor.obj (X.basic_open r)
    = Y.basic_open (H.inv_app U r) :=
begin
  have e := LocallyRingedSpace.preimage_basic_open f (H.inv_app U r),
  erw [PresheafedSpace.is_open_immersion.inv_app_app_apply, RingedSpace.basic_open_res,
    opens.inter_eq, inf_eq_right.mpr _] at e,
  delta Scheme.basic_open,
  rw ← e,
  ext1,
  refine set.image_preimage_eq_inter_range.trans _,
  erw [set.inter_eq_left_iff_subset],
  refine set.subset.trans (RingedSpace.basic_open_subset _ _) (set.image_subset_range _ _),
  refine le_trans (RingedSpace.basic_open_subset _ _) (le_of_eq _),
  ext1,
  exact (set.preimage_image_eq _ H.base_open.inj).symm
end

@[simp, elementwise]
lemma of_restrict_inv_app (X : Scheme) {Y : Top} {f : Y ⟶ Top.of X.carrier}
  (h : open_embedding f) (U : opens (X.restrict h).carrier) :
  (PresheafedSpace.is_open_immersion.of_restrict X.to_PresheafedSpace h).inv_app U = 𝟙 _ :=
begin
  delta PresheafedSpace.is_open_immersion.inv_app,
  rw [is_iso.comp_inv_eq, category.id_comp],
  change X.presheaf.map _ = X.presheaf.map _,
  congr,
end

lemma is_affine_open.exists_basic_open_subset {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) {V : opens X.carrier} (x : V) (h : ↑x ∈ U) :
  ∃ f : X.presheaf.obj (op U), X.basic_open f ⊆ V ∧ ↑x ∈ X.basic_open f :=
begin
  haveI : is_affine _ := hU,
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, h₁, h₂⟩ := (is_basis_basic_open (X.restrict U.open_embedding))
    .exists_subset_of_mem_open _ ((opens.map U.inclusion).obj V).prop,
  swap, exact ⟨x, h⟩,
  have : U.open_embedding.is_open_map.functor.obj ((X.restrict U.open_embedding).basic_open r)
    = X.basic_open (X.presheaf.map (eq_to_hom U.open_embedding_obj_top.symm).op r),
  { refine (image_basic_open_of_is_open_immersion (X.of_restrict U.open_embedding) r).trans _,
    delta Scheme.basic_open,
    erw ← RingedSpace.basic_open_res_eq _ (eq_to_hom U.open_embedding_obj_top).op,
    rw [← category_theory.functor.map_comp_apply, ← op_comp, eq_to_hom_trans, eq_to_hom_refl,
      op_id, category_theory.functor.map_id],
    erw of_restrict_inv_app_apply,
    congr },
  use X.presheaf.map (eq_to_hom U.open_embedding_obj_top.symm).op r,
  rw ← this,
  exact ⟨set.image_subset_iff.mpr h₂, set.mem_image_of_mem _ h₁⟩,
  exact x.prop,
end

instance {X : Scheme} {U : opens X.carrier} (f : X.presheaf.obj (op U)) :
  algebra (X.presheaf.obj (op U)) (X.presheaf.obj (op $ X.basic_open f)) :=
(X.presheaf.map (hom_of_le $ RingedSpace.basic_open_subset _ f : _ ⟶ U).op).to_algebra

lemma PresheafedSpace.is_open_immersion.is_iso_of_subset {C : Type*} [category C]
  {X Y : PresheafedSpace C} (f : X ⟶ Y) [H : PresheafedSpace.is_open_immersion f]
  (U : opens Y.carrier) (hU : (U : set Y.carrier) ⊆ set.range f.base) : is_iso (f.c.app $ op U) :=
begin
  have : U = H.base_open.is_open_map.functor.obj ((opens.map f.base).obj U),
  { ext1,
    exact (set.inter_eq_left_iff_subset.mpr hU).symm.trans set.image_preimage_eq_inter_range.symm },
  convert PresheafedSpace.is_open_immersion.c_iso ((opens.map f.base).obj U),
end

lemma is_affine_open.from_Spec_preimage_basic_open {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) :
  (opens.map hU.from_Spec.val.base).obj (X.basic_open f) =
    RingedSpace.basic_open _ (Spec_Γ_identity.inv.app (X.presheaf.obj $ op U) f) :=
begin
  erw LocallyRingedSpace.preimage_basic_open,
  refine eq.trans _ (RingedSpace.basic_open_res_eq (Scheme.Spec.obj $ op $ X.presheaf.obj (op U))
    .to_LocallyRingedSpace.to_RingedSpace (eq_to_hom hU.from_Spec_base_preimage).op _),
  congr,
  rw ← comp_apply,
  congr,
  erw ← hU.Spec_Γ_identity_hom_app_from_Spec,
  rw iso.inv_hom_id_app_assoc,
end

def basic_open_sections_to_affine {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U)
  (f : X.presheaf.obj (op U)) : X.presheaf.obj (op $ X.basic_open f) ⟶
    (Scheme.Spec.obj $ op $ X.presheaf.obj (op U)).presheaf.obj
      (op $ RingedSpace.basic_open _ $ Spec_Γ_identity.inv.app (X.presheaf.obj (op U)) f) :=
hU.from_Spec.1.c.app (op $ X.basic_open f) ≫ (Scheme.Spec.obj $ op $ X.presheaf.obj (op U))
  .presheaf.map (eq_to_hom $ (hU.from_Spec_preimage_basic_open f).symm).op
.
instance {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U)
  (f : X.presheaf.obj (op U)) : is_iso (basic_open_sections_to_affine hU f) :=
begin
  delta basic_open_sections_to_affine,
  apply_with is_iso.comp_is_iso { instances := ff },
  { apply PresheafedSpace.is_open_immersion.is_iso_of_subset,
    rw hU.from_Spec_range,
    exact RingedSpace.basic_open_subset _ _ },
  apply_instance
end
.

@[simp]
lemma Spec_Γ_identity_inv_app {X : CommRing} : Spec_Γ_identity.inv.app X = to_Spec_Γ X := rfl

lemma is_localization_basic_open {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U)
  (f : X.presheaf.obj (op U)) :
  is_localization.away f (X.presheaf.obj (op $ X.basic_open f)) :=
begin
  apply (is_localization.is_localization_iff_of_ring_equiv (submonoid.powers f)
    (as_iso $ basic_open_sections_to_affine hU f ≫ (Scheme.Spec.obj _).presheaf.map
      (eq_to_hom (basic_open_eq_of_affine _).symm).op).CommRing_iso_to_ring_equiv).mpr,
  convert structure_sheaf.is_localization.to_basic_open _ f,
  change _ ≫ (basic_open_sections_to_affine hU f ≫ _) = _,
  delta basic_open_sections_to_affine,
  erw ring_hom.algebra_map_to_algebra,
  simp only [Scheme.comp_val_c_app, category.assoc],
  erw hU.from_Spec.val.c.naturality_assoc,
  rw hU.from_Spec_app_eq,
  dsimp,
  simp only [category.assoc, ← functor.map_comp, ← op_comp],
  apply structure_sheaf.to_open_res,
end
.
lemma RingedSpace.basic_open_mul (X : RingedSpace) {U : opens X} (f g : X.presheaf.obj (op U)) :
  X.basic_open (f * g) = X.basic_open f ⊓ X.basic_open g :=
begin
  ext1,
  dsimp [RingedSpace.basic_open],
  rw set.image_inter subtype.coe_injective,
  congr,
  ext,
  simp_rw map_mul,
  exact is_unit.mul_iff,
end

lemma RingedSpace.basic_open_of_is_unit (X : RingedSpace) {U : opens X} {f : X.presheaf.obj (op U)}
  (hf : is_unit f) :
  X.basic_open f = U :=
begin
  apply le_antisymm,
  { exact X.basic_open_subset f },
  intros x hx,
  erw X.mem_basic_open f (⟨x, hx⟩ : U),
  exact ring_hom.is_unit_map _ hf
end

lemma basic_open_basic_open_is_basic_open {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) (g : X.presheaf.obj (op $ X.basic_open f)) :
    ∃ f' : X.presheaf.obj (op U), X.basic_open f' = X.basic_open g :=
begin
  haveI := is_localization_basic_open hU f,
  obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := is_localization.surj' (submonoid.powers f) g,
  use f * x,
  delta Scheme.basic_open,
  rw [algebra.smul_def, RingedSpace.basic_open_mul, RingedSpace.basic_open_mul],
  erw RingedSpace.basic_open_res,
  refine (inf_eq_left.mpr _).symm,
  convert inf_le_left using 1,
  apply RingedSpace.basic_open_of_is_unit,
  apply submonoid.left_inv_le_is_unit _ (is_localization.to_inv_submonoid (submonoid.powers f)
    (X.presheaf.obj (op $ X.basic_open f)) _).prop
end

lemma exists_basic_open_subset_affine_inter {X : Scheme} {U V : opens X.carrier}
  (hU : is_affine_open U) (hV : is_affine_open V) (x : X.carrier) (hx : x ∈ U ∩ V) :
  ∃ (f : X.presheaf.obj $ op U) (g : X.presheaf.obj $ op V),
    X.basic_open f = X.basic_open g ∧ x ∈ X.basic_open f :=
begin
  obtain ⟨f, hf₁, hf₂⟩ := hU.exists_basic_open_subset ⟨x, hx.2⟩ hx.1,
  obtain ⟨g, hg₁, hg₂⟩ := hV.exists_basic_open_subset ⟨x, hf₂⟩ hx.2,
  obtain ⟨f', hf'⟩ := basic_open_basic_open_is_basic_open hU f
    (X.presheaf.map (hom_of_le hf₁ : _ ⟶ V).op g),
  replace hf' := (hf'.trans (RingedSpace.basic_open_res _ _ _)).trans (inf_eq_right.mpr hg₁),
  exact ⟨f', g, hf', hf'.symm ▸ hg₂⟩
end

end algebraic_geometry
