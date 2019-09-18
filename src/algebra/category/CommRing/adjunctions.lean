/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl
-/
import algebra.category.CommRing.basic
import category_theory.adjunction.basic
import data.mv_polynomial

/-!
Multivariable polynomials on a type is the left adjoint of the
forgetful functor from commutative rings to types.
-/

noncomputable theory

universe u

open mv_polynomial
open category_theory

namespace CommRing

open_locale classical

-- TODO: Something is painfully slow in this definition, perhaps a heavy definitional equality.
-- If that can be solved, ideally the proofs here could be done by `tidy`.
def free : Type u ⥤ CommRing.{u} :=
{ obj := λ α, of (mv_polynomial α ℤ),
  map := λ _ _ f, @ring_hom.of _ _ _ _ (rename f) (rename.is_semiring_hom f),
  map_id' := λ X, ring_hom.ext (funext rename_id),
  map_comp' := λ X Y Z f g, ring_hom.ext $ funext $ λ p, (rename_rename f g p).symm }

@[simp] lemma free_obj_coe {α : Type u} :
  (free.obj α : Type u) = mv_polynomial α ℤ := rfl

@[simp] lemma free_map_coe {α β : Type u} {f : α → β} :
  ⇑(free.map f) = rename f := rfl

def adj : free ⊣ forget CommRing :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X R, hom_equiv,
  hom_equiv_naturality_left_symm' := by {intros, ext, dsimp, apply eval₂_cast_comp} }

end CommRing
