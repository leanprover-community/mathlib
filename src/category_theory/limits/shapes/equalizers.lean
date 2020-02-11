/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import data.fintype
import category_theory.limits.limits

open category_theory

namespace category_theory.limits

local attribute [tidy] tactic.case_bash

universes v u

/-- The type of objects for the diagram indexing a (co)equalizer. -/
@[derive decidable_eq] inductive walking_parallel_pair : Type v
| zero | one

instance fintype_walking_parallel_pair : fintype walking_parallel_pair :=
{ elems := [walking_parallel_pair.zero, walking_parallel_pair.one].to_finset,
  complete := λ x, by { cases x; simp } }

open walking_parallel_pair

/-- The type family of morphisms for the diagram indexing a (co)equalizer. -/
inductive walking_parallel_pair_hom : walking_parallel_pair → walking_parallel_pair → Type v
| left : walking_parallel_pair_hom zero one
| right : walking_parallel_pair_hom zero one
| id : Π X : walking_parallel_pair.{v}, walking_parallel_pair_hom X X

open walking_parallel_pair_hom

def walking_parallel_pair_hom.comp :
  Π (X Y Z : walking_parallel_pair)
    (f : walking_parallel_pair_hom X Y) (g : walking_parallel_pair_hom Y Z),
    walking_parallel_pair_hom X Z
  | _ _ _ (id _) h := h
  | _ _ _ left   (id one) := left
  | _ _ _ right  (id one) := right
.

instance walking_parallel_pair_hom_category : small_category.{v} walking_parallel_pair :=
{ hom  := walking_parallel_pair_hom,
  id   := walking_parallel_pair_hom.id,
  comp := walking_parallel_pair_hom.comp }

lemma walking_parallel_pair_hom_id (X : walking_parallel_pair.{v}) :
  walking_parallel_pair_hom.id X = 𝟙 X :=
rfl

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
variables {X Y : C}

def parallel_pair (f g : X ⟶ Y) : walking_parallel_pair.{v} ⥤ C :=
{ obj := λ x, match x with
  | zero := X
  | one := Y
  end,
  map := λ x y h, match x, y, h with
  | _, _, (id _) := 𝟙 _
  | _, _, left := f
  | _, _, right := g
  end }.

@[simp] lemma parallel_pair_map_left (f g : X ⟶ Y) : (parallel_pair f g).map left = f := rfl
@[simp] lemma parallel_pair_map_right (f g : X ⟶ Y) : (parallel_pair f g).map right = g := rfl

@[simp] lemma parallel_pair_functor_obj
  {F : walking_parallel_pair.{v} ⥤ C} (j : walking_parallel_pair.{v}) :
  (parallel_pair (F.map left) (F.map right)).obj j = F.obj j :=
begin
  cases j; refl
end

abbreviation fork (f g : X ⟶ Y) := cone (parallel_pair f g)
abbreviation cofork (f g : X ⟶ Y) := cocone (parallel_pair f g)

variables {f g : X ⟶ Y}

attribute [simp] walking_parallel_pair_hom_id

def fork.of_ι {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : fork f g :=
{ X := P,
  π :=
  { app := λ X, begin cases X, exact ι, exact ι ≫ f, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      exact w
    end }}
def cofork.of_π {P : C} (π : Y ⟶ P) (w : f ≫ π = g ≫ π) : cofork f g :=
{ X := P,
  ι :=
  { app := λ X, begin cases X, exact f ≫ π, exact π, end,
    naturality' := λ X Y f,
    begin
      cases X; cases Y; cases f; dsimp; simp,
      exact eq.symm w
    end }}

@[simp] lemma fork.of_ι_app_zero {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  (fork.of_ι ι w).π.app zero = ι := rfl
@[simp] lemma fork.of_ι_app_one {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) :
  (fork.of_ι ι w).π.app one = ι ≫ f := rfl

def fork.ι (t : fork f g) := t.π.app zero
def cofork.π (t : cofork f g) := t.ι.app one
lemma fork.condition (t : fork f g) : (fork.ι t) ≫ f = (fork.ι t) ≫ g :=
begin
  erw [t.w left, ← t.w right], refl
end
lemma cofork.condition (t : cofork f g) : f ≫ (cofork.π t) = g ≫ (cofork.π t) :=
begin
  erw [t.w left, ← t.w right], refl
end

def cone.of_fork
  {F : walking_parallel_pair.{v} ⥤ C} (t : fork (F.map left) (F.map right)) : cone F :=
{ X := t.X,
  π :=
  { app := λ X, t.π.app X ≫ eq_to_hom (by tidy),
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w left, refl,
      erw ← t.w right, refl,
    end } }.
def cocone.of_cofork
  {F : walking_parallel_pair.{v} ⥤ C} (t : cofork (F.map left) (F.map right)) : cocone F :=
{ X := t.X,
  ι :=
  { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X,
    naturality' := λ j j' g,
    begin
      cases j; cases j'; cases g; dsimp; simp,
      erw ← t.w left, refl,
      erw ← t.w right, refl,
    end } }.

@[simp] lemma cone.of_fork_π
  {F : walking_parallel_pair.{v} ⥤ C} (t : fork (F.map left) (F.map right)) (j) :
  (cone.of_fork t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl

@[simp] lemma cocone.of_cofork_ι
  {F : walking_parallel_pair.{v} ⥤ C} (t : cofork (F.map left) (F.map right)) (j) :
  (cocone.of_cofork t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

def fork.of_cone
  {F : walking_parallel_pair.{v} ⥤ C} (t : cone F) : fork (F.map left) (F.map right) :=
{ X := t.X,
  π := { app := λ X, t.π.app X ≫ eq_to_hom (by tidy) } }
def cofork.of_cocone
  {F : walking_parallel_pair.{v} ⥤ C} (t : cocone F) : cofork (F.map left) (F.map right) :=
{ X := t.X,
  ι := { app := λ X, eq_to_hom (by tidy) ≫ t.ι.app X } }

@[simp] lemma fork.of_cone_π {F : walking_parallel_pair.{v} ⥤ C} (t : cone F) (j) :
  (fork.of_cone t).π.app j = t.π.app j ≫ eq_to_hom (by tidy) := rfl
@[simp] lemma cofork.of_cocone_ι {F : walking_parallel_pair.{v} ⥤ C} (t : cocone F) (j) :
  (cofork.of_cocone t).ι.app j = eq_to_hom (by tidy) ≫ t.ι.app j := rfl

variables (f g)

section
variables [has_limit (parallel_pair f g)]

abbreviation equalizer := limit (parallel_pair f g)

abbreviation equalizer.ι : equalizer f g ⟶ X :=
limit.π (parallel_pair f g) zero

lemma equalizer.ι.fork : fork.ι (limits.limit.cone (parallel_pair f g)) = equalizer.ι f g := rfl

@[reassoc] lemma equalizer.condition : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
begin
  erw limit.w (parallel_pair f g) walking_parallel_pair_hom.left,
  erw limit.w (parallel_pair f g) walking_parallel_pair_hom.right
end

abbreviation equalizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) : W ⟶ equalizer f g :=
limit.lift (parallel_pair f g) (fork.of_ι k h)

-- TODO: Move to the right place, add variants + duals
lemma fork_comm {P Q : C} {f g : P ⟶ Q} (s : fork f g) :
    (fork.ι s ≫ f) = (s.π.app walking_parallel_pair.one) :=
by convert @cone.w _ _ _ _ _ s _ _ walking_parallel_pair_hom.left

lemma equalizer.lift.unique {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) (l : W ⟶ equalizer f g)
  (i : l ≫ (equalizer.ι f g) = k) : l = (equalizer.lift f g k h) :=
begin
  refine is_limit.uniq (limit.is_limit (parallel_pair f g)) (fork.of_ι k h) l _,
  intros j, cases j,
  { simp only [fork.of_ι_app_zero, limit.cone_π], exact i, },
  { rw [←fork_comm, fork.of_ι_app_one, equalizer.ι.fork, ←category.assoc, i] },
end

lemma equalizer.ι_mono : mono (equalizer.ι f g) :=
{ right_cancellation := λ Z h k w, begin
  have h₀ : (h ≫ (equalizer.ι f g)) ≫ f = (h ≫ (equalizer.ι f g)) ≫ g :=
    by simp only [category.assoc, equalizer.condition],
  have h₁ : h = equalizer.lift f g (h ≫ (equalizer.ι f g)) h₀ :=
    equalizer.lift.unique _ _ _ _ _ rfl,
  have h₂ : k = equalizer.lift f g (h ≫ (equalizer.ι f g)) h₀ :=
    equalizer.lift.unique _ _ _ _ _ w.symm,
  rw [h₁, h₂]
end }
end

@[simp] lemma cone_parallel_pair_left (s : limits.cone (parallel_pair f g)) :
  (s.π).app zero ≫ f = (s.π).app one :=
begin
  conv { to_lhs, congr, skip, rw ←parallel_pair_map_left f g, },
  rw s.w,
end
@[simp] lemma cone_parallel_pair_right (s : limits.cone (parallel_pair f g)) :
  (s.π).app zero ≫ g = (s.π).app one :=
begin
  conv { to_lhs, congr, skip, rw ←parallel_pair_map_right f g, },
  rw s.w,
end

def cone_parallel_pair_self : cone (parallel_pair f f) :=
{ X := X,
  π :=
  { app := λ j, match j with | zero := 𝟙 X | one := f end }}

@[simp] lemma cone_parallel_pair_self_π_app_zero : (cone_parallel_pair_self f).π.app zero = 𝟙 X :=
rfl

-- TODO squeeze_simp, and diagnose the `erw`s.
def is_limit_cone_parallel_pair_self : is_limit (cone_parallel_pair_self f) :=
{ lift := λ s, s.π.app zero,
  fac' := λ s j,
  begin
    cases j,
    { dsimp, erw [category.comp_id], },
    { dsimp [cone_parallel_pair_self], simp, }
  end,
  uniq' := λ s m w, begin convert w zero, dsimp, erw [category.comp_id], end }

def limit_cone_parallel_pair_self_is_iso (c : cone (parallel_pair f f)) (h : is_limit c) :
  is_iso (c.π.app zero) :=
begin
  let c' := cone_parallel_pair_self f,
  have z : c ≅ c', sorry,
  have t : c.π.app zero = z.hom.hom ≫ c'.π.app zero, sorry,
  replace t : c.π.app zero = z.hom.hom, sorry,
  rw t,
  sorry
end

section
variables [has_colimit (parallel_pair f g)]

abbreviation coequalizer := colimit (parallel_pair f g)

abbreviation coequalizer.π : Y ⟶ coequalizer f g :=
colimit.ι (parallel_pair f g) one

@[reassoc] lemma coequalizer.condition : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
begin
  erw colimit.w (parallel_pair f g) walking_parallel_pair_hom.left,
  erw colimit.w (parallel_pair f g) walking_parallel_pair_hom.right
end

abbreviation coequalizer.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = g ≫ k) : coequalizer f g ⟶ W :=
colimit.desc (parallel_pair f g) (cofork.of_π k h)
end

variables (C)

class has_equalizers :=
(has_limits_of_shape : has_limits_of_shape.{v} walking_parallel_pair C)
class has_coequalizers :=
(has_colimits_of_shape : has_colimits_of_shape.{v} walking_parallel_pair C)

attribute [instance] has_equalizers.has_limits_of_shape has_coequalizers.has_colimits_of_shape

end category_theory.limits
