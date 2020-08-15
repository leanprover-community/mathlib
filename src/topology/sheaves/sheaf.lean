/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.presheaf
import category_theory.limits.punit
import category_theory.limits.shapes.products
import category_theory.limits.shapes.equalizers
import category_theory.full_subcategory

/-!
# Sheaves

We define sheaves on a topological space, with values in an arbitrary category.

The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.

We provide the instance `category (sheaf C X)` as the full subcategory of presheaves,
and the fully faithful functor `sheaf.forget : sheaf C X ⥤ presheaf C X`.
-/

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite
open topological_space.opens

namespace Top

variables {C : Type u} [category.{v} C] [has_products C]
variables {X : Top.{v}} (F : presheaf C X) {ι : Type v} (U : ι → opens X)

namespace sheaf_condition

/-- The product of the sections of a presheaf over a family of open sets. -/
def pi_opens : C := ∏ (λ i : ι, F.obj (op (U i)))
/--
The product of the sections of a presheaf over the pairwise intersections of
a family of open sets.
-/
def pi_inters : C := ∏ (λ p : ι × ι, F.obj (op (U p.1 ⊓ U p.2)))

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U i` to `U i ⊓ U j`.
-/
def left_res : pi_opens F U ⟶ pi_inters F U :=
pi.lift (λ p : ι × ι, pi.π _ p.1 ≫ F.map (inf_le_left (U p.1) (U p.2)).op)

/--
The morphism `Π F.obj (U i) ⟶ Π F.obj (U i) ⊓ (U j)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def right_res : pi_opens F U ⟶ pi_inters F U :=
pi.lift (λ p : ι × ι, pi.π _ p.2 ≫ F.map (inf_le_right (U p.1) (U p.2)).op)

/--
The morphism `F.obj U ⟶ Π F.obj (U i)` whose components
are given by the restriction maps from `U j` to `U i ⊓ U j`.
-/
def res : F.obj (op (supr U)) ⟶ pi_opens F U :=
pi.lift (λ i : ι, F.map (topological_space.opens.le_supr U i).op)

lemma w : res F U ≫ left_res F U = res F U ≫ right_res F U :=
begin
  dsimp [res, left_res, right_res],
  ext,
  simp only [limit.lift_π, limit.lift_π_assoc, fan.mk_π_app, category.assoc],
  rw [←F.map_comp],
  rw [←F.map_comp],
  congr,
end

/--
The equalizer diagram for the sheaf condition.
-/
@[reducible]
def diagram : walking_parallel_pair.{v} ⥤ C :=
parallel_pair (left_res F U) (right_res F U)

/--
The restriction map `F.obj U ⟶ Π F.obj (U i)` gives a cone over the equalizer diagram
for the sheaf condition. The sheaf condition asserts this cone is a limit cone.
-/
def fork : fork.{v} (left_res F U) (right_res F U) := fork.of_ι _ (w F U)

@[simp]
lemma fork_X : (fork F U).X = F.obj (op (supr U)) := rfl

@[simp]
lemma fork_ι : (fork F U).ι = res F U := rfl
@[simp]
lemma fork_π_app_walking_parallel_pair_zero :
  (fork F U).π.app walking_parallel_pair.zero = res F U := rfl
@[simp]
lemma fork_π_app_walking_parallel_pair_one :
  (fork F U).π.app walking_parallel_pair.one = res F U ≫ left_res F U := rfl

end sheaf_condition

/--
The sheaf condition for a `F : presheaf C X` requires that the morphism
`F.obj U ⟶ ∏ F.obj (U i)` (where `U` is some open set which is the union of the `U i`)
is the equalizer of the two morphisms
`∏ F.obj (U i) ⟶ ∏ F.obj (U i) ⊓ (U j)`.
-/
-- One might prefer to work with sets of opens, rather than indexed families,
-- which would reduce the universe level here to `max u v`.
-- However as it's a subsingleton the universe level doesn't matter much.
@[derive subsingleton]
def sheaf_condition (F : presheaf C X) : Type (max u (v+1)) :=
Π ⦃ι : Type v⦄ (U : ι → opens X), is_limit (sheaf_condition.fork F U)

/--
The presheaf valued in `punit` over any topological space is a sheaf.
-/
def sheaf_condition_punit (F : presheaf (category_theory.discrete punit) X) :
  sheaf_condition F :=
λ ι U, punit_cone_is_limit

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheaf_condition_inhabited (F : presheaf (category_theory.discrete punit) X) :
  inhabited (sheaf_condition F) := ⟨sheaf_condition_punit F⟩

variables (C X)

/--
A `sheaf C X` is a presheaf of objects from `C` over a (bundled) topological space `X`,
satisfying the sheaf condition.
-/
structure sheaf :=
(presheaf : presheaf C X)
(sheaf_condition : sheaf_condition presheaf)

instance : category (sheaf C X) := induced_category.category sheaf.presheaf

-- Let's construct a trivial example, to keep the inhabited linter happy.
instance sheaf_inhabited : inhabited (sheaf (category_theory.discrete punit) X) :=
⟨{ presheaf := functor.star _, sheaf_condition := default _ }⟩

namespace sheaf

/--
The forgetful functor from sheaves to presheaves.
-/
@[derive [full, faithful]]
def forget : Top.sheaf C X ⥤ Top.presheaf C X := induced_functor sheaf.presheaf

end sheaf

end Top
