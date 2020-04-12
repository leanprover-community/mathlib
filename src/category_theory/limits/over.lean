/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
import category_theory.comma
import category_theory.limits.preserves
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

open category_theory category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variable {X : C}

namespace category_theory.functor

@[simps] def to_cocone (F : J ⥤ over X) : cocone (F ⋙ over.forget) :=
{ X := X,
  ι := { app := λ j, (F.obj j).hom } }

@[simps] def to_cone (F : J ⥤ under X) : cone (F ⋙ under.forget) :=
{ X := X,
  π := { app := λ j, (F.obj j).hom } }

end category_theory.functor

namespace category_theory.over

@[simps] def colimit (F : J ⥤ over X) [has_colimit (F ⋙ forget)] : cocone F :=
{ X := mk $ colimit.desc (F ⋙ forget) F.to_cocone,
  ι :=
  { app := λ j, hom_mk $ colimit.ι (F ⋙ forget) j,
    naturality' :=
    begin
      intros j j' f,
      have := colimit.w (F ⋙ forget) f,
      tidy
    end } }

def forget_colimit_is_colimit (F : J ⥤ over X) [has_colimit (F ⋙ forget)] :
  is_colimit (forget.map_cocone (colimit F)) :=
is_colimit.of_iso_colimit (colimit.is_colimit (F ⋙ forget)) (cocones.ext (iso.refl _) (by tidy))

instance : reflects_colimits (forget : over X ⥤ C) :=
{ reflects_colimits_of_shape := λ J 𝒥,
  { reflects_colimit := λ F,
    by constructor; exactI λ t ht,
    { desc := λ s, hom_mk (ht.desc (forget.map_cocone s))
        begin
          apply ht.hom_ext, intro j,
          rw [←category.assoc, ht.fac],
          transitivity (F.obj j).hom,
          exact w (s.ι.app j), -- TODO: How to write (s.ι.app j).w?
          exact (w (t.ι.app j)).symm,
        end,
      fac' := begin
        intros s j, ext, exact ht.fac (forget.map_cocone s) j
        -- TODO: Ask Simon about multiple ext lemmas for defeq types (comma_morphism & over.category.hom)
      end,
      uniq' :=
      begin
        intros s m w,
        ext1 j,
        exact ht.uniq (forget.map_cocone s) m.left (λ j, congr_arg comma_morphism.left (w j))
      end } } }

instance has_colimit {F : J ⥤ over X} [has_colimit (F ⋙ forget)] : has_colimit F :=
{ cocone := colimit F,
  is_colimit := reflects_colimit.reflects (forget_colimit_is_colimit F) }

instance has_colimits_of_shape [has_colimits_of_shape J C] :
  has_colimits_of_shape J (over X) :=
{ has_colimit := λ F, by apply_instance }

instance has_colimits [has_colimits.{v} C] : has_colimits.{v} (over X) :=
{ has_colimits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance forget_preserves_colimits [has_colimits.{v} C] {X : C} :
  preserves_colimits (forget : over X ⥤ C) :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F, by exactI
    preserves_colimit_of_preserves_colimit_cocone (colimit.is_colimit F) (forget_colimit_is_colimit F) } }

/-- Given the appropriate pullback in C, construct a product in the over category -/
def over_product_of_pullbacks (B : C) (F : discrete walking_pair ⥤ over B)
  [q : has_limit (cospan (F.obj walking_pair.left).hom (F.obj walking_pair.right).hom)] :
has_limit F :=
{ cone :=
  begin
    refine ⟨_, _⟩,
    exact @over.mk _ _ B (pullback (F.obj walking_pair.left).hom (F.obj walking_pair.right).hom) (pullback.fst ≫ (F.obj walking_pair.left).hom),
    apply nat_trans.of_homs, intro i, cases i,
    apply over.hom_mk _ _, apply pullback.fst, dsimp, refl,
    apply over.hom_mk _ _, apply pullback.snd, exact pullback.condition.symm
  end,
  is_limit :=
  { lift := λ s,
      begin
        apply over.hom_mk _ _,
          apply pullback.lift _ _ _,
              exact (s.π.app walking_pair.left).left,
            exact (s.π.app walking_pair.right).left,
          erw over.w (s.π.app walking_pair.left),
          erw over.w (s.π.app walking_pair.right),
          refl,
        dsimp, erw ← category.assoc, simp,
      end,
    fac' := λ s j,
      begin
        ext, cases j; simp [nat_trans.of_homs]
      end,
    uniq' := λ s m j,
      begin
        ext,
        { erw ← j walking_pair.left, simp },
        { erw ← j walking_pair.right, simp }
      end } }

/-- Construct terminal object in the over category. -/
instance (B : C) : has_terminal.{v} (over B) :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone :=
      { X := over.mk (𝟙 _),
        π := { app := λ p, pempty.elim p } },
      is_limit :=
        { lift := λ s, over.hom_mk _,
          fac' := λ _ j, j.elim,
          uniq' := λ s m _,
            begin
              ext,
              rw over.hom_mk_left,
              have := m.w,
              dsimp at this,
              rwa [category.comp_id, category.comp_id] at this
            end } } } }

-- TODO: this should work for any connected limit, not just pullbacks
/-- Given pullbacks in C, we have pullbacks in C/B -/
instance {B : C} [has_pullbacks.{v} C] : has_pullbacks.{v} (over B) :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    let X : over B := F.obj walking_cospan.one in
    let Y : over B := F.obj walking_cospan.left in
    let Z : over B := F.obj walking_cospan.right in
    let f : Y ⟶ X := (F.map walking_cospan.hom.inl) in
    let g : Z ⟶ X := (F.map walking_cospan.hom.inr) in
    let L : over B := over.mk (pullback.fst ≫ Y.hom : pullback f.left g.left ⟶ B) in
    let π₁ : L ⟶ Y := over.hom_mk pullback.fst in
    let π₂ : L ⟶ Z := @over.hom_mk _ _ _ L Z (pullback.snd : L.left ⟶ Z.left)
      (by {dsimp, rw [← over.w f, ← category.assoc, pullback.condition, category.assoc, over.w g]}) in
    { cone := cone.of_pullback_cone (pullback_cone.mk π₁ π₂
        (by { ext, rw [over.comp_left, over.hom_mk_left, pullback.condition], refl, })),
      is_limit :=
      { lift := λ s,
      begin
        apply over.hom_mk _ _,
        { apply pullback.lift (s.π.app walking_cospan.left).left (s.π.app walking_cospan.right).left,
          rw [← over.comp_left, ← over.comp_left, s.w, s.w], },
        { show pullback.lift _ _ _ ≫ (pullback.fst ≫ Y.hom) = (s.X).hom,
          rw [limit.lift_π_assoc, pullback_cone.mk_π_app_left, over.w], refl, }
       end,
       fac' := λ s j,
       begin
        ext1, dsimp,
        cases j; simp only [limit.lift_π, limit.lift_π_assoc, over.hom_mk_left, over.id_left,
          over.comp_left, pullback_cone.mk_π_app_one, pullback_cone.mk_π_app_left,
          pullback_cone.mk_π_app_right, eq_to_hom_refl, category.comp_id],
        rw [← over.comp_left, ← s.w walking_cospan.hom.inl],
       end,
       uniq' := λ s m J, over.over_morphism.ext
       begin
        simp only [over.hom_mk_left],
        apply pullback.hom_ext,
        { rw [limit.lift_π, pullback_cone.mk_π_app_left, ←(J walking_cospan.left)],
          dsimp,
          rw [category.comp_id], },
        { rw [limit.lift_π, pullback_cone.mk_π_app_right, ←(J walking_cospan.right)],
          dsimp,
          rw [category.comp_id], }
       end } },
  } }

/-- Given pullbacks in C, we have binary products in any over category -/
instance over_has_prods_of_pullback [has_pullbacks.{v} C] (B : C) :
  has_binary_products.{v} (over B) :=
{has_limits_of_shape := {has_limit := λ F, over_product_of_pullbacks B F}}

/-! A collection of lemmas to decompose products in the over category -/
@[simp] lemma over_prod_pair_left [has_pullbacks.{v} C] {B : C} (f g : over B) :
  (f ⨯ g).left = pullback f.hom g.hom := rfl

@[simp] lemma over_prod_pair_hom [has_pullbacks.{v} C] {B : C} (f g : over B) :
  (f ⨯ g).hom = pullback.fst ≫ f.hom := rfl

@[simp] lemma over_prod_fst_left [has_pullbacks.{v} C] {B : C} (f g : over B) :
  (limits.prod.fst : f ⨯ g ⟶ f).left = pullback.fst := rfl

@[simp] lemma over_prod_snd_left [has_pullbacks.{v} C] {B : C} (f g : over B) :
  (limits.prod.snd : f ⨯ g ⟶ g).left = pullback.snd := rfl

lemma over_prod_map_left [has_pullbacks.{v} C] {B : C} (f g h k : over B) (α : f ⟶ g) (β : h ⟶ k) :
  (limits.prod.map α β).left = pullback.lift (pullback.fst ≫ α.left) (pullback.snd ≫ β.left) (by { simp only [category.assoc], convert pullback.condition; apply over.w }) :=
rfl

end category_theory.over

namespace category_theory.under

@[simps] def limit (F : J ⥤ under X) [has_limit (F ⋙ forget)] : cone F :=
{ X := mk $ limit.lift (F ⋙ forget) F.to_cone,
  π :=
  { app := λ j, hom_mk $ limit.π (F ⋙ forget) j,
    naturality' :=
    begin
      intros j j' f,
      have := (limit.w (F ⋙ forget) f).symm,
      tidy
    end } }

def forget_limit_is_limit (F : J ⥤ under X) [has_limit (F ⋙ forget)] :
  is_limit (forget.map_cone (limit F)) :=
is_limit.of_iso_limit (limit.is_limit (F ⋙ forget)) (cones.ext (iso.refl _) (by tidy))

instance : reflects_limits (forget : under X ⥤ C) :=
{ reflects_limits_of_shape := λ J 𝒥,
  { reflects_limit := λ F,
    by constructor; exactI λ t ht,
    { lift := λ s, hom_mk (ht.lift (forget.map_cone s))
        begin
          apply ht.hom_ext, intro j,
          rw [category.assoc, ht.fac],
          transitivity (F.obj j).hom,
          exact w (s.π.app j),
          exact (w (t.π.app j)).symm,
        end,
      fac' := begin
        intros s j, ext, exact ht.fac (forget.map_cone s) j
      end,
      uniq' :=
      begin
        intros s m w,
        ext1 j,
        exact ht.uniq (forget.map_cone s) m.right (λ j, congr_arg comma_morphism.right (w j))
      end } } }

instance has_limit {F : J ⥤ under X} [has_limit (F ⋙ forget)] : has_limit F :=
{ cone := limit F,
  is_limit := reflects_limit.reflects (forget_limit_is_limit F) }

instance has_limits_of_shape [has_limits_of_shape J C] :
  has_limits_of_shape J (under X) :=
{ has_limit := λ F, by apply_instance }

instance has_limits [has_limits.{v} C] : has_limits.{v} (under X) :=
{ has_limits_of_shape := λ J 𝒥, by resetI; apply_instance }

instance forget_preserves_limits [has_limits.{v} C] {X : C} :
  preserves_limits (forget : under X ⥤ C) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F, by exactI
    preserves_limit_of_preserves_limit_cone (limit.is_limit F) (forget_limit_is_limit F) } }

end category_theory.under
