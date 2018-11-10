-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.products
import category_theory.limits
import category_theory.limits.preserves

open category_theory

namespace category_theory.limits

universes u v

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables {J K : Type v} [small_category J] [small_category K]

@[simp] lemma cone.functor_w {F : J ⥤ (K ⥤ C)} (c : cone F) {j j' : J} (f : j ⟶ j') (k : K) :
  (c.π.app j).app k ≫ (F.map f).app k = (c.π.app j').app k :=
begin
  have h := congr_fun (congr_arg (nat_trans.app) (eq.symm (c.π.naturality f))) k,
  dsimp at h,
  rw h,
  simp,
end
@[simp] lemma cocone.functor_w {F : J ⥤ (K ⥤ C)} (c : cocone F) {j j' : J} (f : j ⟶ j') (k : K) :
  (F.map f).app k ≫ (c.ι.app j').app k = (c.ι.app j).app k :=
begin
  have h := congr_fun (congr_arg (nat_trans.app) (eq.symm (c.ι.naturality f))) k,
  dsimp at h,
  simp at h,
  rw h,
end

@[simp] def functor_category_limit_cone
  [has_limits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) : cone F :=
{ X := F.flip ⋙ lim,
  π :=
  { app := λ j,
    { app := λ k, limit.π (F.flip.obj k) j },
      naturality' := λ j j' f,
        begin
          dsimp, simp, ext k, dsimp,
          erw limit.w (F.flip.obj k),
        end } }
@[simp] def functor_category_colimit_cocone
  [has_colimits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) : cocone F :=
{ X := F.flip ⋙ colim,
  ι :=
  { app := λ j,
    { app := λ k , colimit.ι (F.flip.obj k) j },
      naturality' := λ j j' f,
        begin
          dsimp, simp, ext k, dsimp,
          erw colimit.w (F.flip.obj k),
        end } }

@[simp] def evaluate_functor_category_limit_cone
  [has_limits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) (k : K) :
  ((evaluation K C).obj k).map_cone (functor_category_limit_cone F) ≅
    limit.cone (F.flip.obj k) :=
by tidy
@[simp] def evaluate_functor_category_colimit_cocone
  [has_colimits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) (k : K) :
  ((evaluation K C).obj k).map_cocone (functor_category_colimit_cocone F) ≅
    colimit.cocone (F.flip.obj k) :=
by tidy

def functor_category_is_limit_cone [has_limits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) :
  is_limit (functor_category_limit_cone F) :=
{ lift := λ s,
  { app := λ k, limit.lift (F.flip.obj k)
    { X := s.X.obj k,
      π := { app := λ j, (s.π.app j).app k } },
    naturality' := λ k k' f,
    begin
      ext, dsimp, simp, rw nat_trans.naturality, refl,
    end },
  uniq' := λ s m w,
  begin
    ext k j, dsimp, simp,
    rw ← w j,
    refl
  end }
def functor_category_is_colimit_cocone [has_colimits_of_shape.{u v} J C] (F : J ⥤ K ⥤ C) :
  is_colimit (functor_category_colimit_cocone F) :=
{ desc := λ s,
  { app := λ k, colimit.desc (F.flip.obj k)
    { X := s.X.obj k,
      ι := { app := λ j, (s.ι.app j).app k } },
    naturality' := λ k k' f,
    begin
      ext, dsimp,
      rw ←category.assoc, simp,
      rw ←category.assoc, simp,
      erw ← nat_trans.naturality, refl,
    end },
  uniq' := λ s m w,
  begin
    ext k j, dsimp, simp,
    rw ← w j,
    refl
  end }

instance functor_category_has_limits_of_shape
  [has_limits_of_shape.{u v} J C] : has_limits_of_shape J (K ⥤ C) :=
{ cone := λ F, functor_category_limit_cone F,
  is_limit := λ F, functor_category_is_limit_cone F }
instance functor_category_has_colimits_of_shape
  [has_colimits_of_shape.{u v} J C] : has_colimits_of_shape J (K ⥤ C) :=
{ cocone := λ F, functor_category_colimit_cocone F,
  is_colimit := λ F, functor_category_is_colimit_cocone F }

-- Perhaps we need hand-rolled versions of these? Let's see what people need.
instance functor_category_has_products
  [has_products.{u v} C] : has_products.{(max u v) v} (K ⥤ C) :=
limits.has_products_of_has_limits
instance functor_category_has_coproducts
  [has_coproducts.{u v} C] : has_coproducts.{(max u v) v} (K ⥤ C) :=
limits.has_coproducts_of_has_colimits
instance functor_category_has_pullbacks
  [has_pullbacks.{u v} C] : has_pullbacks.{(max u v) v} (K ⥤ C) :=
limits.has_pullbacks_of_has_limits
instance functor_category_has_pushouts
  [has_pushouts.{u v} C] : has_pushouts.{(max u v) v} (K ⥤ C) :=
limits.has_pushouts_of_has_colimits
instance functor_category_has_equalizers
  [has_equalizers.{u v} C] : has_equalizers.{(max u v) v} (K ⥤ C) :=
limits.has_equalizers_of_has_limits
instance functor_category_has_coequalizers
  [has_coequalizers.{u v} C] : has_coequalizers.{(max u v) v} (K ⥤ C) :=
limits.has_coequalizers_of_has_colimits

instance functor_category_has_limits
  [has_limits.{u v} C] : has_limits.{(max u v) v} (K ⥤ C) :=
{ cone := λ J 𝒥 F, by resetI; exact functor_category_limit_cone F,
  is_limit := λ J 𝒥 F, by resetI; exact functor_category_is_limit_cone F }
instance functor_category_has_colimits
  [has_colimits.{u v} C] : has_colimits.{(max u v) v} (K ⥤ C) :=
{ cocone := λ J 𝒥 F, by resetI; exact functor_category_colimit_cocone F,
  is_colimit := λ J 𝒥 F, by resetI; exact functor_category_is_colimit_cocone F }

instance evaluation_preserves_limits_of_shape [has_limits_of_shape.{u v} J C] (k : K) :
  preserves_limits_of_shape J ((evaluation.{v v u v} K C).obj k) :=
{ preserves := λ F c h,
  begin
    have i : functor_category_limit_cone F ≅ c :=
      limit_cone.ext (functor_category_is_limit_cone F) h,
    apply is_limit_invariance _ _ (functor.on_iso _ i),

    -- Next, we know exactly what the evaluation of the `product_cone F` is:
    apply is_limit_invariance _ _ (evaluate_functor_category_limit_cone F k).symm,

    -- Finally, it's just that the limit cone is a limit.
    exact limit.universal_property _
  end }
instance evaluation_preserves_colimits_of_shape [has_colimits_of_shape.{u v} J C] (k : K) :
  preserves_colimits_of_shape J ((evaluation.{v v u v} K C).obj k) :=
{ preserves := λ F c h,
  begin
    have i : functor_category_colimit_cocone F ≅ c :=
      colimit_cocone.ext (functor_category_is_colimit_cocone F) h,
    apply is_colimit_invariance _ _ (functor.on_iso _ i),

    -- Next, we know exactly what the evaluation of the `product_cocone F` is:
    apply is_colimit_invariance _ _ (evaluate_functor_category_colimit_cocone F k).symm,

    -- Finally, it's just that the colimit cocone is a colimit.
    exact colimit.universal_property _
  end }

instance evaluation_preserves_limits [has_limits.{u v} C] (k : K) :
  preserves_limits ((evaluation.{v v u v} K C).obj k) :=
@preserves_limits_of_preserves_limits_of_all_shapes _ _ _ _
  ((evaluation.{v v u v} K C).obj k)
  (λ J 𝒥, by resetI; apply_instance)
instance evaluation_preserves_colimits [has_colimits.{u v} C] (k : K) :
  preserves_colimits ((evaluation.{v v u v} K C).obj k) :=
@preserves_colimits_of_preserves_colimits_of_all_shapes _ _ _ _
  ((evaluation.{v v u v} K C).obj k)
  (λ J 𝒥, by resetI; apply_instance)

end category_theory.limits
