/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.ring.boolean_ring
import order.category.BoolAlg

/-!
# The category of Boolean rings

This file defines `BoolRing`, the category of Boolean rings.
-/

universes u

open category_theory order

/-- The category of Boolean rings. -/
def BoolRing := bundled boolean_ring

namespace BoolRing

instance : has_coe_to_sort BoolRing Type* := bundled.has_coe_to_sort
instance (X : BoolRing) : boolean_ring X := X.str

/-- Construct a bundled `BoolRing` from a `boolean_ring`. -/
def of (α : Type*) [boolean_ring α] : BoolRing := bundled.of α

instance : inhabited BoolRing := ⟨of punit⟩

instance : large_category.{u} BoolRing :=
{ hom := λ X Y, ring_hom X Y,
  id := λ X, ring_hom.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, ring_hom.comp_id,
  comp_id' := λ X Y, ring_hom.id_comp,
  assoc' := λ W X Y Z _ _ _, ring_hom.comp_assoc _ _ _ }

instance : concrete_category BoolRing :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y f g h, fun_like.coe_injective h⟩ }

/-- Constructs an isomorphism of Boolean rings from a group isomorphism between them. -/
@[simps] def iso.mk {α β : BoolRing.{u}} (e : α ≃+* β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

end BoolRing

/-! ### Equivalence between `BoolAlg` and `BoolRing` -/

instance BoolRing.has_forget_to_BoolAlg : has_forget₂ BoolRing BoolAlg :=
{ forget₂ := { obj := λ X, BoolAlg.of (as_boolalg X), map := λ X Y, ring_hom.as_boolalg } }
