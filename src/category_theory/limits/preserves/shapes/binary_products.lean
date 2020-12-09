/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.binary_products
import category_theory.limits.preserves.basic

/-!
# Preserving binary products

Constructions to relate the notions of preserving binary products and reflecting binary products
to concrete binary fans.

In particular, we show that `prod_comparison G X Y` is an isomorphism iff `G` preserves
the product of `X` and `Y`.
-/

noncomputable theory

universes v u₁ u₂

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

namespace category_theory.limits

variables {P X Y Z : C} (f : P ⟶ X) (g : P ⟶ Y)

/--
The map of a binary fan is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `binary_fan.mk` with `functor.map_cone`.
-/
def is_limit_map_cone_binary_fan_equiv :
  is_limit (G.map_cone (binary_fan.mk f g)) ≃ is_limit (binary_fan.mk (G.map f) (G.map g)) :=
(is_limit.postcompose_hom_equiv (diagram_iso_pair _) _).symm.trans
  (is_limit.equiv_iso_limit (cones.ext (iso.refl _) (by { rintro (_ | _), tidy })))

/-- The property of preserving products expressed in terms of binary fans. -/
def map_is_limit_of_preserves_of_is_limit [preserves_limit (pair X Y) G]
  (l : is_limit (binary_fan.mk f g)) :
  is_limit (binary_fan.mk (G.map f) (G.map g)) :=
is_limit_map_cone_binary_fan_equiv G f g (preserves_limit.preserves l)

/-- The property of reflecting products expressed in terms of binary fans. -/
def is_limit_of_reflects_of_map_is_limit [reflects_limit (pair X Y) G]
  (l : is_limit (binary_fan.mk (G.map f) (G.map g))) :
  is_limit (binary_fan.mk f g) :=
reflects_limit.reflects ((is_limit_map_cone_binary_fan_equiv G f g).symm l)

variables (X Y) [has_binary_product X Y]

/--
If `G` preserves binary products and `C` has them, then the binary fan constructed of the mapped
morphisms of the binary product cone is a limit.
-/
def is_limit_of_has_binary_product_of_preserves_limit
  [preserves_limit (pair X Y) G] :
  is_limit (binary_fan.mk (G.map (limits.prod.fst : X ⨯ Y ⟶ X)) (G.map (limits.prod.snd))) :=
map_is_limit_of_preserves_of_is_limit G _ _ (prod_is_prod X Y)

variables [has_binary_product (G.obj X) (G.obj Y)]

/--
If the product comparison map for `G` at `(X,Y)` is an isomorphism, then `G` preserves the
pair of `(X,Y)`.
-/
def preserves_pair.of_iso_comparison [i : is_iso (prod_comparison G X Y)] :
  preserves_limit (pair X Y) G :=
begin
  apply preserves_limit_of_preserves_limit_cone (prod_is_prod X Y),
  apply (is_limit_map_cone_binary_fan_equiv _ _ _).symm _,
  apply is_limit.of_point_iso (limit.is_limit (pair (G.obj X) (G.obj Y))),
  apply i,
end

variables [preserves_limit (pair X Y) G]
/--
If `G` preserves the product of `(X,Y)`, then the product comparison map for `G` at `(X,Y)` is
an isomorphism.
-/
def preserves_pair.iso :
  G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y :=
is_limit.cone_point_unique_up_to_iso
  (is_limit_of_has_binary_product_of_preserves_limit G X Y)
  (limit.is_limit _)

@[simp]
lemma preserves_pair.iso_hom : (preserves_pair.iso G X Y).hom = prod_comparison G X Y := rfl

instance : is_iso (prod_comparison G X Y) :=
begin
  rw ← preserves_pair.iso_hom,
  apply_instance
end

end category_theory.limits
