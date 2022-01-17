/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes
-/
import group_theory.quotient_group
import tactic.group

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `algebra/category/Group/adjunctions`.

## Main definitions

* `commutator`: defines the commutator of a group `G` as a subgroup of `G`.
* `abelianization`: defines the abelianization of a group `G` as the quotient of a group by its
  commutator subgroup.
-/

universes u v

-- Let G be a group.
variables (G : Type u) [group G]

/-- The commutator subgroup of a group G is the normal subgroup
  generated by the commutators [p,q]=`p*q*p⁻¹*q⁻¹`. -/
@[derive subgroup.normal]
def commutator : subgroup G :=
subgroup.normal_closure {x | ∃ p q, p * q * p⁻¹ * q⁻¹ = x}

/-- The abelianization of G is the quotient of G by its commutator subgroup. -/
def abelianization : Type u :=
G ⧸ (commutator G)

namespace abelianization

local attribute [instance] quotient_group.left_rel

instance : comm_group (abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂' x y $ λ a b,
  begin
    apply quotient.sound,
    apply subgroup.subset_normal_closure,
    use b⁻¹, use a⁻¹,
    group,
  end,
.. quotient_group.quotient.group _ }

instance : inhabited (abelianization G) := ⟨1⟩

instance [fintype G] [decidable_pred (∈ commutator G)] :
  fintype (abelianization G) :=
quotient_group.fintype (commutator G)

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
def of : G →* abelianization G :=
{ to_fun := quotient_group.mk,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

@[simp] lemma mk_eq_of {a : G} :
  quot.mk (@setoid.r _ (quotient_group.left_rel (commutator G))) a = of a := rfl

section lift
-- So far we have built Gᵃᵇ and proved it's an abelian group.
-- Furthremore we defined the canonical projection `of : G → Gᵃᵇ`

-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
variables {A : Type v} [comm_group A] (f : G →* A)

lemma commutator_subset_ker : commutator G ≤ f.ker :=
begin
  apply subgroup.normal_closure_le_normal,
  rintros x ⟨p, q, rfl⟩,
  simp [monoid_hom.mem_ker, mul_right_comm (f p) (f q)],
end

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map from
  the abelianization of a `G` to `A` that factors through `f`. -/
def lift : (G →* A) ≃ (abelianization G →* A) :=
{ to_fun := λ f, quotient_group.lift _ f (λ x h, f.mem_ker.2 $ commutator_subset_ker _ h),
  inv_fun := λ F, F.comp of,
  left_inv := λ f, monoid_hom.ext $ λ x, rfl,
  right_inv := λ F, monoid_hom.ext $ λ x, quotient_group.induction_on x $ λ z, rfl }

@[simp] lemma lift.of (x : G) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (φ : abelianization G →* A)
  -- hφ : φ agrees with f on the image of G in Gᵃᵇ
  (hφ : ∀ (x : G), φ (of x) = f x)
  {x : abelianization G} :
  φ x = lift f x :=
quotient_group.induction_on x hφ

end lift

variables {A : Type v} [monoid A]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext (φ ψ : abelianization G →* A)
  (h : φ.comp of = ψ.comp of) : φ = ψ :=
monoid_hom.ext $ λ x, quotient_group.induction_on x $ monoid_hom.congr_fun h

end abelianization

/-- Equivalent groups have equivalent abelianizations -/
def mul_equiv.abelianization_congr {G H : Type*} [group G] [group H] (e : G ≃* H) :
  abelianization G ≃* abelianization H :=
{ to_fun := abelianization.lift $ abelianization.of.comp e.to_monoid_hom,
  inv_fun := abelianization.lift $ abelianization.of.comp e.symm.to_monoid_hom,
  left_inv := by { rintros ⟨a⟩, simp },
  right_inv := by { rintros ⟨a⟩, simp },
  map_mul' := by tidy }


@[simp]
lemma coe_abelianization_congr_of
  {G H : Type*} [group G] [group H] (e : G ≃* H) { x : G } :
  (e.abelianization_congr) (abelianization.of x) = abelianization.of (e x) := rfl

@[simp]
lemma abelianization_congr_ref {G : Type*} [group G] :
  (mul_equiv.refl G).abelianization_congr = mul_equiv.refl (abelianization G) :=
begin
  apply mul_equiv.to_monoid_hom_injective,
  apply abelianization.hom_ext,
  ext,
  simp,
end

@[simp]
lemma abelianization_congr_symm {G H : Type*} [group G] [group H] (e : G ≃* H) :
  e.abelianization_congr.symm = e.symm.abelianization_congr := rfl

@[simp]
lemma abelianization_congr_trans
  {G₁ G₂ G₃ : Type*} [group G₁] [group G₂] [group G₃] (e₁ : G₁ ≃* G₂) (e₂ : G₂ ≃* G₃) :
  e₁.abelianization_congr.trans e₂.abelianization_congr = (e₁.trans e₂).abelianization_congr :=
begin
  apply mul_equiv.to_monoid_hom_injective,
  apply abelianization.hom_ext,
  ext,
  simp,
end

/-- The abelianization of an Abelian group is equivalent to the group itself -/
def abelianization_of_comm_group {H : Type*} [comm_group H] :
  abelianization H ≃* H :=
{ to_fun := abelianization.lift (monoid_hom.id H),
  inv_fun := abelianization.of,
  left_inv := by {rintros ⟨a⟩, simp,},
  right_inv := by {intros a, simp,},
  map_mul' := by tidy }
