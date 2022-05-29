/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import algebra.module.basic
import algebra.module.linear_map
import algebra.monoid_algebra.basic
import linear_algebra.trace
import linear_algebra.dual
import linear_algebra.free_module.basic
import representation_theory.fdRep

/-!
# Monoid representations

This file introduces monoid representations and their characters and defines a few ways to construct
representations.

## Main definitions

  * representation.representation
  * representation.character
  * representation.tprod
  * representation.lin_hom
  * represensation.dual

## Implementation notes

Representations of a monoid `G` on a `k`-module `V` are implemented as
homomorphisms `G →* (V →ₗ[k] V)`.
-/

universes u

open monoid_algebra (lift) (of)
open linear_map

section
variables (k G V : Type*) [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]

/--
A representation of `G` on the `k`-module `V` is an homomorphism `G →* (V →ₗ[k] V)`.
-/
abbreviation representation := G →* (V →ₗ[k] V)

end

namespace representation

section trivial

variables {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]

/--
The trivial representation of `G` on the one-dimensional module `k`.
-/
def trivial : representation k G k := 1

@[simp]
lemma trivial_def (g : G) (v : k) : trivial g v = v := rfl

end trivial

section monoid_algebra

variables {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
variables (ρ : representation k G V)

/--
A `k`-linear representation of `G` on `V` can be thought of as
an algebra map from `monoid_algebra k G` into the `k`-linear endomorphisms of `V`.
-/
noncomputable def as_algebra_hom : monoid_algebra k G →ₐ[k] (module.End k V) :=
  (lift k G _) ρ

lemma as_algebra_hom_def :
  as_algebra_hom ρ = (lift k G _) ρ := rfl

@[simp]
lemma as_algebra_hom_single (g : G):
  (as_algebra_hom ρ (finsupp.single g 1)) = ρ g :=
by simp only [as_algebra_hom_def, monoid_algebra.lift_single, one_smul]

lemma as_algebra_hom_of (g : G):
  (as_algebra_hom ρ (of k G g)) = ρ g :=
by simp only [monoid_algebra.of_apply, as_algebra_hom_single]

/--
A `k`-linear representation of `G` on `V` can be thought of as
a module over `monoid_algebra k G`.
-/
noncomputable def as_module : module (monoid_algebra k G) V :=
  module.comp_hom V (as_algebra_hom ρ).to_ring_hom

end monoid_algebra

section group

variables {k G V : Type*} [comm_semiring k] [group G] [add_comm_monoid V] [module k V]
variables (ρ : representation k G V)

/--
When `G` is a group, a `k`-linear representation of `G` on `V` can be thought of as
a group homomorphism from `G` into the invertible `k`-linear endomorphisms of `V`.
-/
def as_group_hom : G →* units (V →ₗ[k] V) :=
  monoid_hom.to_hom_units ρ

lemma as_group_hom_apply (g : G) : ↑(as_group_hom ρ g) = ρ g :=
by simp only [as_group_hom, monoid_hom.coe_to_hom_units]

end group

section tensor_product

variables {k G V W : Type*} [comm_semiring k] [monoid G]
variables [add_comm_monoid V] [module k V] [add_comm_monoid W] [module k W]
variables (ρV : representation k G V) (ρW : representation k G W)

open_locale tensor_product

/--
Given representations of `G` on `V` and `W`, there is a natural representation of `G` on their
tensor product `V ⊗[k] W`.
-/
def tprod : representation k G (V ⊗[k] W) :=
{ to_fun := λ g, tensor_product.map (ρV g) (ρW g),
  map_one' := by simp only [map_one, tensor_product.map_one],
  map_mul' := λ g h, by simp only [map_mul, tensor_product.map_mul] }

local notation ρV ` ⊗ ` ρW := tprod ρV ρW

@[simp]
lemma tprod_apply (g : G) : (ρV ⊗ ρW) g = tensor_product.map (ρV g) (ρW g) := rfl

end tensor_product

section linear_hom

variables {k G V W : Type*} [comm_semiring k] [group G]
variables [add_comm_monoid V] [module k V] [add_comm_monoid W] [module k W]
variables (ρV : representation k G V) (ρW : representation k G W)

/--
Given representations of `G` on `V` and `W`, there is a natural representation of `G` on the
module `V →ₗ[k] W`, where `G` acts by conjugation.
-/
def lin_hom : representation k G (V →ₗ[k] W) :=
{ to_fun := λ g,
  { to_fun := λ f, (ρW g) ∘ₗ f ∘ₗ (ρV g⁻¹),
    map_add' := λ f₁ f₂, by simp_rw [add_comp, comp_add],
    map_smul' := λ r f, by simp_rw [ring_hom.id_apply, smul_comp, comp_smul]},
  map_one' := linear_map.ext $ λ x,
    by simp_rw [coe_mk, inv_one, map_one, one_apply, one_eq_id, comp_id, id_comp],
  map_mul' := λ g h,  linear_map.ext $ λ x,
    by simp_rw [coe_mul, coe_mk, function.comp_apply, mul_inv_rev, map_mul, mul_eq_comp,
                comp_assoc ]}
@[simp]
lemma lin_hom_apply (g : G) (f : V →ₗ[k] W) : (lin_hom ρV ρW) g f = (ρW g) ∘ₗ f ∘ₗ (ρV g⁻¹) := rfl

/--
The dual of a representation `ρ` of `G` on a module `V`, given by `(dual ρ) g f = f ∘ₗ (ρ g⁻¹)`,
where `f : module.dual k V`.
-/
def dual : representation k G (module.dual k V) :=
{ to_fun := λ g,
  { to_fun := λ f, f ∘ₗ (ρV g⁻¹),
    map_add' := λ f₁ f₂, by simp only [add_comp],
    map_smul' := λ r f,
      by {ext, simp only [coe_comp, function.comp_app, smul_apply, ring_hom.id_apply]} },
  map_one' :=
    by {ext, simp only [coe_comp, function.comp_app, map_one, inv_one, coe_mk, one_apply]},
  map_mul' := λ g h,
    by {ext, simp only [coe_comp, function.comp_app, mul_inv_rev, map_mul, coe_mk, mul_apply]}}

@[simp]
lemma dual_apply (g : G) : (dual ρV) g = module.dual.transpose (ρV g⁻¹) := rfl

end linear_hom

section

variables {k G V W : Type u} [field k] [group G]
variables [add_comm_group V] [module k V] [add_comm_group W] [module k W]
variables [finite_dimensional k V] [finite_dimensional k W]
variables (ρV : representation k G V) (ρW : representation k G W)

local attribute tensor_product.ext

/-- When `V` and `W` are finite dimensional representations of a group `G`, the isomorphism
`dual_tensor_hom_equiv k V W` of vector spaces induces an isomorphism of representations.  -/
noncomputable
def dual_tensor_iso_lin_hom : (fdRep.of ρV.dual) ⊗ (fdRep.of ρW) ≅ fdRep.of (lin_hom ρV ρW) :=
begin
  refine Action.mk_iso (dual_tensor_hom_equiv k V W).to_FinVect_iso _,
  intro g, ext f w v,
  simp only [linear_equiv.to_FinVect_iso_hom, tensor_product.curry_apply, fdRep.of_ρ,
  module.dual.transpose_apply, dual_tensor_hom_apply, dual_tensor_hom_equiv_of_basis_to_linear_map,
  category_theory.comp_apply, Action.tensor_rho, dual_tensor_hom_equiv.equations._eqn_1,
  id.def, ring_hom.id_apply, eq_self_iff_true, function.comp_app,
  category_theory.monoidal_category.full_monoidal_subcategory_tensor_hom, linear_map.coe_comp,
  representation.dual_apply, representation.lin_hom_apply, Module.monoidal_category.hom_apply,
  linear_map.map_smulₛₗ, tensor_product.algebra_tensor_module.curry_apply, linear_map.to_fun_eq_coe,
  linear_map.coe_restrict_scalars_eq_coe],
end

end

end representation
