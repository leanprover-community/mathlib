/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import representation_theory.Rep
import algebra.category.FinVect
import representation_theory.basic

/-!
# `fdRep k G` is the category of finite dimensional `k`-linear representations of `G`.

If `V : fdRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `module k V` and `finite_dimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We verify that `fdRep k G` is a rigid monoidal category.

## TODO
* `fdRep k G` has all finite (co)limits.
* `fdRep k G` is abelian.
* `fdRep k G ≌ FinVect (monoid_algebra k G)` (this will require generalising `FinVect` first).
* Upgrade the right rigid structure to a rigid structure.
-/

universes u

open category_theory
open category_theory.limits

/-- The category of finite dimensional `k`-linear representations of a monoid `G`. -/
@[derive [large_category, concrete_category/-, has_limits, has_colimits-/]]
abbreviation fdRep (k G : Type u) [field k] [monoid G] :=
Action (FinVect.{u} k) (Mon.of G)

namespace fdRep

variables {k G : Type u} [field k] [monoid G]

instance : has_coe_to_sort (fdRep k G) (Type u) := concrete_category.has_coe_to_sort _

instance (V : fdRep k G) : add_comm_group V :=
by { change add_comm_group ((forget₂ (fdRep k G) (FinVect k)).obj V), apply_instance, }

instance (V : fdRep k G) : module k V :=
by { change module k ((forget₂ (fdRep k G) (FinVect k)).obj V), apply_instance, }

instance (V : fdRep k G) : finite_dimensional k V :=
by { change finite_dimensional k ((forget₂ (fdRep k G) (FinVect k)).obj V), apply_instance, }

/-- The monoid homomorphism corresponding to the action of `G` onto `V : fdRep k G`. -/
def ρ (V : fdRep k G) : G →* (V →ₗ[k] V) := V.ρ

/-- The underlying `linear_equiv` of an isomorphism of representations. -/
def iso_to_linear_equiv {V W : fdRep k G} (i : V ≅ W) : V ≃ₗ[k] W :=
  FinVect.iso_to_linear_equiv ((Action.forget (FinVect k) (Mon.of G)).map_iso i)

lemma iso.conj_ρ {V W : fdRep k G} (i : V ≅ W) (g : G) :
   W.ρ g = (fdRep.iso_to_linear_equiv i).conj (V.ρ g) :=
begin
  rw [fdRep.iso_to_linear_equiv, ←FinVect.iso.conj_eq_conj, iso.conj_apply],
  rw [iso.eq_inv_comp ((Action.forget (FinVect k) (Mon.of G)).map_iso i)],
  exact (i.hom.comm g).symm,
end

-- This works well with the new design for representations:
example (V : fdRep k G) : G →* (V →ₗ[k] V) := V.ρ

/-- Lift an unbundled representation to `fdRep`. -/
@[simps ρ]
def of {V : Type u} [add_comm_group V] [module k V] [finite_dimensional k V]
  (ρ : representation k G V) : fdRep k G :=
⟨FinVect.of k V, ρ⟩

instance : has_forget₂ (fdRep k G) (Rep k G) :=
{ forget₂ := (forget₂ (FinVect k) (Module k)).map_Action (Mon.of G), }

-- Verify that the monoidal structure is available.
example : monoidal_category (fdRep k G) := by apply_instance

end fdRep

namespace fdRep
variables {k G : Type u} [field k] [group G]

-- Verify that the rigid structure is available when the monoid is a group.
noncomputable instance : right_rigid_category (fdRep k G) :=
by { change right_rigid_category (Action (FinVect k) (Group.of G)), apply_instance, }

end fdRep

namespace fdRep

open representation

variables {k G V W : Type u} [field k] [group G]
variables [add_comm_group V] [module k V] [add_comm_group W] [module k W]
variables [finite_dimensional k V] [finite_dimensional k W]
variables (ρV : representation k G V) (ρW : representation k G W)

local attribute tensor_product.ext

lemma dual_tensor_hom_comm (g : G) :
  (dual_tensor_hom k V W) ∘ₗ (tensor_product.map (ρV.dual g) (ρW g)) =
  (lin_hom ρV ρW) g ∘ₗ (dual_tensor_hom k V W) :=
begin
  ext, simp [module.dual.transpose_apply],
end

/-- Auxiliary definition for `fdRep.dual_tensor_iso_lin_hom`. -/
noncomputable def dual_tensor_iso_lin_hom_aux :
  ((fdRep.of ρV.dual) ⊗ (fdRep.of ρW)).V ≅ (fdRep.of (lin_hom ρV ρW)).V :=
(dual_tensor_hom_equiv k V W).to_FinVect_iso

/-- When `V` and `W` are finite dimensional representations of a group `G`, the isomorphism
`dual_tensor_hom_equiv k V W` of vector spaces induces an isomorphism of representations. -/
noncomputable def dual_tensor_iso_lin_hom :
  (fdRep.of ρV.dual) ⊗ (fdRep.of ρW) ≅ fdRep.of (lin_hom ρV ρW) :=
begin
  apply Action.mk_iso (dual_tensor_iso_lin_hom_aux ρV ρW),
  convert (dual_tensor_hom_comm ρV ρW),
end

@[simp] lemma dual_tensor_iso_lin_hom_hom_hom :
  (dual_tensor_iso_lin_hom ρV ρW).hom.hom = dual_tensor_hom k V W := rfl

end fdRep
