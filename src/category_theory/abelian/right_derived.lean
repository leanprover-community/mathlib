/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison
-/
import category_theory.abelian.injective_resolution
import algebra.homology.additive
import category_theory.limits.constructions.epi_mono
import category_theory.abelian.homology
import category_theory.abelian.exact

/-!
# Right-derived functors

We define the right-derived functors `F.right_derived n : C ⥤ D` for any additive functor `F`
out of a category with injective resolutions.

The definition is
```
injective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n
```
that is, we pick an injective resolution (thought of as an object of the homotopy category),
we apply `F` objectwise, and compute `n`-th homology.

We show that these right-derived functors can be calculated
on objects using any choice of injective resolution,
and on morphisms by any choice of lift to a cochain map between chosen injective resolutions.

Similarly we define natural transformations between right-derived functors coming from
natural transformations between the original additive functors,
and show how to compute the components.
-/

noncomputable theory

open category_theory
open category_theory.limits


namespace category_theory
universes v u
variables {C : Type u} [category.{v} C] {D : Type*} [category D]
variables [abelian C] [has_injective_resolutions C] [abelian D]

/-- The right derived functors of an additive functor. -/
def functor.right_derived (F : C ⥤ D) [F.additive] (n : ℕ) : C ⥤ D :=
injective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n

/-- We can compute a right derived functor using a chosen injective resolution. -/
@[simps]
def functor.right_derived_obj_iso (F : C ⥤ D) [F.additive] (n : ℕ)
  {X : C} (P : InjectiveResolution X) :
  (F.right_derived n).obj X ≅
    (homology_functor D _ n).obj ((F.map_homological_complex _).obj P.cocomplex) :=
(homotopy_category.homology_functor D _ n).map_iso
  (homotopy_category.iso_of_homotopy_equiv
    (F.map_homotopy_equiv (InjectiveResolution.homotopy_equiv _ P)))
  ≪≫ (homotopy_category.homology_factors D _ n).app _

/-- The 0-th derived functor of `F` on an injective object `X` is just `F.obj X`. -/
@[simps]
def functor.right_derived_obj_injective_zero (F : C ⥤ D) [F.additive]
  (X : C) [injective X] :
  (F.right_derived 0).obj X ≅ F.obj X :=
F.right_derived_obj_iso 0 (InjectiveResolution.self X) ≪≫
  (homology_functor _ _ _).map_iso ((cochain_complex.single₀_map_homological_complex F).app X) ≪≫
  (cochain_complex.homology_functor_0_single₀ D).app (F.obj X)

open_locale zero_object

/-- The higher derived functors vanish on injective objects. -/
@[simps]
def functor.right_derived_obj_injective_succ (F : C ⥤ D) [F.additive] (n : ℕ)
  (X : C) [injective X] :
  (F.right_derived (n+1)).obj X ≅ 0 :=
F.right_derived_obj_iso (n+1) (InjectiveResolution.self X) ≪≫
  (homology_functor _ _ _).map_iso ((cochain_complex.single₀_map_homological_complex F).app X) ≪≫
  (cochain_complex.homology_functor_succ_single₀ D n).app (F.obj X)

/--
We can compute a right derived functor on a morphism using a descent of that morphism
to a cochain map between chosen injective resolutions.
-/
lemma functor.right_derived_map_eq (F : C ⥤ D) [F.additive] (n : ℕ) {X Y : C} (f : Y ⟶ X)
  {P : InjectiveResolution X} {Q : InjectiveResolution Y} (g : Q.cocomplex ⟶ P.cocomplex)
  (w : Q.ι ≫ g = (cochain_complex.single₀ C).map f ≫ P.ι) :
  (F.right_derived n).map f =
  (F.right_derived_obj_iso n Q).hom ≫
    (homology_functor D _ n).map ((F.map_homological_complex _).map g) ≫
    (F.right_derived_obj_iso n P).inv :=
begin
  dsimp only [functor.right_derived, functor.right_derived_obj_iso],
  dsimp, simp only [category.comp_id, category.id_comp],
  rw [←homology_functor_map, homotopy_category.homology_functor_map_factors],
  simp only [←functor.map_comp],
  congr' 1,
  apply homotopy_category.eq_of_homotopy,
  apply functor.map_homotopy,
  apply homotopy.trans,
  exact homotopy_category.homotopy_out_map _,
  apply InjectiveResolution.desc_homotopy f,
  { simp, },
  { simp only [InjectiveResolution.homotopy_equiv_hom_ι_assoc],
    rw [←category.assoc, w, category.assoc],
    simp only [InjectiveResolution.homotopy_equiv_inv_ι], },
end

/-- The natural transformation between right-derived functors induced by a natural transformation.-/
@[simps]
def nat_trans.right_derived {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ) :
  F.right_derived n ⟶ G.right_derived n :=
whisker_left (injective_resolutions C)
  (whisker_right (nat_trans.map_homotopy_category α _)
    (homotopy_category.homology_functor D _ n))

@[simp] lemma nat_trans.right_derived_id (F : C ⥤ D) [F.additive] (n : ℕ) :
  nat_trans.right_derived (𝟙 F) n = 𝟙 (F.right_derived n) :=
by { simp [nat_trans.right_derived], refl, }

@[simp, nolint simp_nf] lemma nat_trans.right_derived_comp
  {F G H : C ⥤ D} [F.additive] [G.additive] [H.additive]
  (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
  nat_trans.right_derived (α ≫ β) n = nat_trans.right_derived α n ≫ nat_trans.right_derived β n :=
by simp [nat_trans.right_derived]

/--
A component of the natural transformation between right-derived functors can be computed
using a chosen injective resolution.
-/
lemma nat_trans.right_derived_eq {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ)
  {X : C} (P : InjectiveResolution X) :
  (nat_trans.right_derived α n).app X =
    (F.right_derived_obj_iso n P).hom ≫
      (homology_functor D _ n).map ((nat_trans.map_homological_complex α _).app P.cocomplex) ≫
        (G.right_derived_obj_iso n P).inv :=
begin
  symmetry,
  dsimp [nat_trans.right_derived, functor.right_derived_obj_iso],
  simp only [category.comp_id, category.id_comp],
  rw [←homology_functor_map, homotopy_category.homology_functor_map_factors],
  simp only [←functor.map_comp],
  congr' 1,
  apply homotopy_category.eq_of_homotopy,
  simp only [nat_trans.map_homological_complex_naturality_assoc,
    ←functor.map_comp],
  apply homotopy.comp_left_id,
  rw [←functor.map_id],
  apply functor.map_homotopy,
  apply homotopy_equiv.homotopy_hom_inv_id,
end

end category_theory

section

noncomputable theory

universes w v u

open category_theory.limits category_theory category_theory.functor

variables {C : Type u} [category.{w} C] {D : Type u} [category.{w} D]
variables (F : C ⥤ D) {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

namespace category_theory.abelian.functor

open category_theory.preadditive

variables [abelian C] [abelian D] [additive F]

/-- If `preserves_finite_colimits F` and `epi g`, then `exact (F.map f) (F.map g)` if
`exact f g`. -/
lemma preserves_exact_of_preserves_finite_colimits_of_mono [preserves_finite_limits F] [mono f]
  (ex : exact f g) : exact (F.map f) (F.map g) :=
abelian.exact_of_is_kernel _ _ (by simp [← functor.map_comp, ex.w]) $
  limits.is_limit_fork_map_of_is_limit' _ ex.w (abelian.is_limit_of_exact_of_mono _ _ ex)

lemma exact_of_map_injective_resolution (P: InjectiveResolution X) [preserves_finite_limits F] :
  exact (F.map (P.ι.f 0))
    (((F.map_homological_complex (complex_shape.up ℕ)).obj P.cocomplex).d_from 0) :=
begin
  have : (complex_shape.up ℕ).rel 0 1 := rfl,
  let f := (homological_complex.X_next_iso ((F.map_homological_complex _).obj P.cocomplex) this),
  refine preadditive.exact_of_iso_of_exact' (F.map (P.ι.f 0)) (F.map (P.cocomplex.d 0 1)) _ _
    (iso.refl _) (iso.refl _) f.symm (by simp) _ (preserves_exact_of_preserves_finite_colimits_of_mono _ (P.exact₀)),
  rw [iso.refl_hom, category.id_comp, iso.symm_hom, homological_complex.d_from_eq _ this],
  congr',
end

/-- Given `P : ProjectiveResolution X`, a morphism `(F.left_derived 0).obj X ⟶ F.obj X`. -/
@[nolint unused_arguments]
def right_derived_zero_to_self_app [enough_injectives C] [preserves_finite_limits F] {X : C}
  (P : InjectiveResolution X) :
  (F.right_derived 0).obj X ⟶ F.obj X := -- sorry
begin
  haveI ex := (exact_of_map_injective_resolution F P),
  refine (right_derived_obj_iso F 0 P).hom ≫ (homology_iso_kernel_desc _ _ _).hom ≫ _ ≫
    (as_iso (kernel.lift _ _ ex.w)).inv,
  exact kernel.map _ _ (cokernel.desc _ (𝟙 _) (by simp)) (𝟙 _) (by { ext, simp }),
end

/-- Given `P : ProjectiveResolution X`, a morphism `F.obj X ⟶ (F.left_derived 0).obj X` given
`preserves_finite_colimits F`. -/
@[nolint unused_arguments]
def right_derived_zero_to_self_app_inv [enough_injectives C] {X : C}
  (P : InjectiveResolution X) :
  F.obj X ⟶ (F.right_derived 0).obj X :=
F.map (𝟙 _) ≫ homology.lift _ _ _ (F.map (P.ι.f 0) ≫ cokernel.π _) begin
  have : (complex_shape.up ℕ).rel 0 1 := rfl,
  rw [category.assoc, cokernel.π_desc, homological_complex.d_from_eq _ this,
    map_homological_complex_obj_d, ← category.assoc, ← functor.map_comp],
  simp only [exact.w, functor.map_zero, zero_comp],
end ≫ (right_derived_obj_iso F 0 P).inv

lemma right_derived_zero_to_self_app_comp_inv [enough_injectives C] [preserves_finite_limits F]
  {X : C} (P : InjectiveResolution X) : right_derived_zero_to_self_app F P ≫
  right_derived_zero_to_self_app_inv F P = 𝟙 _ := -- sorry
begin
  dsimp [right_derived_zero_to_self_app, right_derived_zero_to_self_app_inv],
  -- type_check cokernel.desc,
  -- simp only [right_derived_obj_iso_hom, map_id, right_derived_obj_iso_inv, category.id_comp, category.assoc],
  rw [map_id, category.id_comp, category.assoc],
  refine (iso.eq_inv_comp _).1 _,
  rw [← category.assoc, ← category.assoc],
  refine (iso.comp_inv_eq _).2 _,
  rw [category.comp_id, iso.inv_hom_id, category.assoc, category.assoc, iso.hom_comp_eq_id],
  ext,
  simp [category.assoc, homology.lift_ι_assoc,
    cokernel.π_desc, homology.ι, iso.inv_hom_id, category.id_comp, category.comp_id],
  nth_rewrite 1 [← category.id_comp (kernel.ι _)],
  rw [← category.assoc, ← category.assoc, ← category.assoc],
  congr' 1,
  dsimp [homology.lift],
  rw [category.assoc, category.assoc, category.assoc, iso.inv_hom_id, category.comp_id],
  ext,
  simp [limits.equalizer_as_kernel, category.assoc, limits.kernel.lift_ι_assoc,
    limits.kernel.lift_ι, category.comp_id],
  -- rw [← category.assoc],
  nth_rewrite 1 [← category.comp_id (kernel.ι _)],
  congr' 1,
  ext,
  simp,
end

lemma right_derived_zero_to_self_app_inv_comp [enough_injectives C] [preserves_finite_limits F]
  {X : C} (P : InjectiveResolution X) : right_derived_zero_to_self_app_inv F P ≫
  right_derived_zero_to_self_app F P = 𝟙 _ :=
begin
  dsimp [right_derived_zero_to_self_app, right_derived_zero_to_self_app_inv],
  rw [map_id, category.id_comp, ← category.assoc _ (F.right_derived_obj_iso 0 P).hom,
    category.assoc _ _ (F.right_derived_obj_iso 0 P).hom, iso.inv_hom_id, category.comp_id,
    ← category.assoc, ← category.assoc, is_iso.comp_inv_eq, category.id_comp],
  ext,
  simp only [limits.kernel.lift_ι_assoc, category.assoc, limits.kernel.lift_ι, homology.lift],
  rw [← category.assoc, ← category.assoc, category.assoc _ _ (homology_iso_kernel_desc _ _ _).hom,
    iso.inv_hom_id, category.comp_id],
  simp,
end

/-- Given `P : ProjectiveResolution X`, the isomorphism `(F.left_derived 0).obj X ≅ F.obj X` if
`preserves_finite_colimits F`. -/
def right_derived_zero_to_self_app_iso [enough_injectives C] [preserves_finite_limits F]
  {X : C} (P : InjectiveResolution X) : (F.right_derived 0).obj X ≅ F.obj X :=
{ hom := right_derived_zero_to_self_app _ P,
  inv := right_derived_zero_to_self_app_inv _ P,
  hom_inv_id' := right_derived_zero_to_self_app_comp_inv _ P,
  inv_hom_id' := right_derived_zero_to_self_app_inv_comp _ P }

/-- Given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y` and a morphism `f : X ⟶ Y`,
naturality of the square given by `left_derived_zero_to_self_obj_hom. -/
lemma right_derived_zero_to_self_natural [enough_injectives C] [preserves_finite_limits F] {X : C} {Y : C} (f : X ⟶ Y)
  (P : InjectiveResolution X) (Q : InjectiveResolution Y) :
  (F.right_derived 0).map f ≫ right_derived_zero_to_self_app F Q =
  right_derived_zero_to_self_app F P ≫ F.map f :=
begin
  sorry
end

/-- Given `preserves_finite_colimits F`, the natural isomorphism `(F.left_derived 0) ≅ F`. -/
def left_derived_zero_iso_self [enough_injectives C] [preserves_finite_limits F] :
  (F.right_derived 0) ≅ F :=
nat_iso.of_components (λ X, right_derived_zero_to_self_app_iso _ (InjectiveResolution.of X))
  (λ X Y f, right_derived_zero_to_self_natural _ _ _ _)

end category_theory.abelian.functor


end
