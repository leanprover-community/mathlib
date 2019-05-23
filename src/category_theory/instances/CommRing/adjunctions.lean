/- Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl

Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/

import category_theory.instances.CommRing.basic
import category_theory.adjunction.basic
import data.mv_polynomial

universe u

open mv_polynomial
open category_theory
open category_theory.instances

namespace category_theory.instances.CommRing

local attribute [instance, priority 0] classical.prop_decidable

noncomputable def polynomial_ring : Type u ⥤ CommRing.{u} :=
{ obj := λ α, ⟨mv_polynomial α ℤ, by apply_instance⟩,
  map := λ α β f, ⟨rename f, by apply_instance⟩ }

@[simp] lemma polynomial_ring_obj_α {α : Type u} :
  (polynomial_ring.obj α).α = mv_polynomial α ℤ := rfl

@[simp] lemma polynomial_ring_map_val {α β : Type u} {f : α → β} :
  (polynomial_ring.map f).val = rename f := rfl

noncomputable def adj : polynomial_ring ⊣ (forget : CommRing.{u} ⥤ Type u) :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ α R,
  { to_fun    := λ f, f ∘ X,
    inv_fun   := λ f, ⟨eval₂ (λ n : ℤ, (n : R)) f, by { unfold_coes, apply_instance }⟩,
    left_inv  := λ f, CommRing.hom.ext $ @eval₂_hom_X _ _ _ _ _ _ f _,
    right_inv := λ x, by { ext1, unfold_coes, simp only [function.comp_app, eval₂_X] } },
  hom_equiv_naturality_left_symm' :=
  λ X X' Y f g, by { ext1, dsimp, apply eval₂_cast_comp }
}.

end category_theory.instances.CommRing
