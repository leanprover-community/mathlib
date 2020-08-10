/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.limits
import category_theory.products.basic
import category_theory.currying

/-!
# A Fubini theorem for limits

We prove that $lim_{J × K} G = lim_J (lim_K G(j, -))$ for a functor `G : J × K ⥤ C`,
when all the appropriate limits exist.

We begin working with a functor `F : J ⥤ K ⥤ C`. We'll write `G : J × K ⥤ C` for the associated
"uncurried" functor.

In the first part, given a coherent family `D` of limit cones over the functors `F.obj j`,
and a cone `c` over `G`, we construct a cone over the cone points of `D`.
We then show that if `c` is a limit cone, the constructed cone is also a limit cone.

In the second part, we state the Fubini theorem in the setting where we have chosen limits
provided by suitable `has_limit` classes.

We construct `fubini F : limit (uncurry.obj F) ≅ limit (F ⋙ lim)`,
and give simp lemmas characterising it.
For convenience, we also provide `fubini' G : limit G ≅ limit ((curry.obj G) ⋙ lim)`,
in terms of the uncurried functor.
-/

universes v u

open category_theory

namespace category_theory.limits

variables {J K : Type v} [small_category J] [small_category K]
variables {C : Type u} [category.{v} C]

variables (F : J ⥤ K ⥤ C)

/--
A structure carrying a diagram of cones over the the functors `F.obj j`.
-/
-- We could try introducing a "dependent functor type" to handle this?
structure diagram_of_cones :=
(obj : Π j : J, cone (F.obj j))
(map : Π {j j' : J} (f : j ⟶ j'), (cones.postcompose (F.map f)).obj (obj j) ⟶ obj j')
(id : ∀ j : J, (map (𝟙 j)).hom = 𝟙 _ . obviously)
(comp : ∀ {j₁ j₂ j₃ : J} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
  (map (f ≫ g)).hom = (map f).hom ≫ (map g).hom . obviously)

variables {F}

/--
Extract the functor `J ⥤ C` consisting of the cone points and the maps between them,
from a `diagram_of_cones`.
-/
@[simps]
def diagram_of_cones.cone_points (D : diagram_of_cones F) :
  J ⥤ C :=
{ obj := λ j, (D.obj j).X,
  map := λ j j' f, (D.map f).hom,
  map_id' := λ j, D.id j,
  map_comp' := λ j₁ j₂ j₃ f g, D.comp f g, }

/--
Given a diagram `D` of limit cones over the `F.obj j`, and a cone over `uncurry.obj F`,
we can construct a cone over the diagram consisting of the cone points from `D`.
-/
@[simps]
def cone_of_cone_uncurry
  {D : diagram_of_cones F} (Q : Π j, is_limit (D.obj j))
  (c : cone (uncurry.obj F)) :
  cone (D.cone_points) :=
{ X := c.X,
  π :=
  { app := λ j, (Q j).lift
    { X := c.X,
      π :=
      { app := λ k, c.π.app (j, k),
        naturality' := λ k k' f,
        begin
          dsimp, simp,
          have := @nat_trans.naturality _ _ _ _ _ _ c.π (j, k) (j, k') (𝟙 j, f),
          dsimp at this,
          simp only [category.id_comp, category_theory.functor.map_id, nat_trans.id_app] at this,
          exact this,
        end } },
    naturality' := λ j j' f, (Q j').hom_ext
    begin
      dsimp,
      intro k, simp,
      have := @nat_trans.naturality _ _ _ _ _ _ c.π (j, k) (j', k) (f, 𝟙 k),
      dsimp at this,
      simp only [category.id_comp, category.comp_id,
        category_theory.functor.map_id, nat_trans.id_app] at this,
      exact this,
    end, } }.

/--
`cone_of_cone_uncurry Q c` is a limit cone when `c` is a limit cone.`
-/
def cone_of_cone_uncurry_is_limit
  {D : diagram_of_cones F} (Q : Π j, is_limit (D.obj j))
  {c : cone (uncurry.obj F)} (P : is_limit c) :
  is_limit (cone_of_cone_uncurry Q c) :=
{ lift := λ s, P.lift
  { X := s.X,
    π :=
    { app := λ p, s.π.app p.1 ≫ (D.obj p.1).π.app p.2,
      naturality' := λ p p' f,
      begin
        dsimp, simp,
        rcases p with ⟨j, k⟩,
        rcases p' with ⟨j', k'⟩,
        rcases f with ⟨fj, fk⟩,
        dsimp,
        slice_rhs 3 4 { rw ←nat_trans.naturality, },
        slice_rhs 2 3 { rw ←(D.obj j).π.naturality, },
        simp only [functor.const.obj_map, category.id_comp, category.assoc],
        have w := (D.map fj).w k',
        dsimp at w,
        rw ←w,
        have n := s.π.naturality fj,
        dsimp at n,
        simp only [category.id_comp] at n,
        rw n,
        simp,
      end, } },
  fac' := λ s j,
  begin
    apply (Q j).hom_ext,
    intro k,
    simp,
  end,
  uniq' := λ s m w,
  begin
    refine P.uniq { X := s.X, π := _, } m _,
    rintro ⟨j, k⟩,
    dsimp,
    rw [←w j],
    simp,
  end, }

section
variables (F)
variables [has_limits_of_shape K C]

/--
Given a functor `F : J ⥤ K ⥤ C`, with all needed chosen limits,
we can construct a diagram consisting of the limit cone over each functor `F.obj j`,
and the universal cone morphisms between these.
-/
@[simps]
def diagram_of_cones.mk_of_has_limits : diagram_of_cones F :=
{ obj := λ j, limit.cone (F.obj j),
  map := λ j j' f, { hom := lim.map (F.map f), }, }

-- Satisfying the inhabited linter.
instance : inhabited (diagram_of_cones F) := ⟨diagram_of_cones.mk_of_has_limits F⟩

@[simp]
lemma diagram_of_cones.mk_of_has_limits_cone_points :
  (diagram_of_cones.mk_of_has_limits F).cone_points = (F ⋙ lim) :=
rfl

variables [has_limit (uncurry.obj F)]
variables [has_limit (F ⋙ lim)]

/--
The Fubini theorem for a functor `F : J ⥤ K ⥤ C`,
showing that the limit of `uncurry.obj F` can be computed as
the limit of the limits of the functors `F.obj j`.
-/
def fubini : limit (uncurry.obj F) ≅ limit (F ⋙ lim) :=
begin
  let c := limit.cone (uncurry.obj F),
  let P : is_limit c := limit.is_limit _,
  let G := diagram_of_cones.mk_of_has_limits F,
  let Q : Π j, is_limit (G.obj j) := λ j, limit.is_limit _,
  have Q' := cone_of_cone_uncurry_is_limit Q P,
  have Q'' := (limit.is_limit (F ⋙ lim)),
  exact is_limit.cone_point_unique_up_to_iso Q' Q'',
end

@[simp]
lemma fubini_hom_π_π {j} {k} : (fubini F).hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) :=
begin
  dsimp [fubini, is_limit.cone_point_unique_up_to_iso, is_limit.unique_up_to_iso],
  simp,
end

@[simp]
lemma fubini_inv_π {j} {k} : (fubini F).inv ≫ limit.π _ (j, k) = limit.π _ j ≫ limit.π _ k :=
begin
  rw [←cancel_epi (fubini F).hom],
  simp,
end
end

section
variables (G : J × K ⥤ C)
variables [has_limits_of_shape K C]
variables [has_limit G]
variables [has_limit ((curry.obj G) ⋙ lim)]

/--
The Fubini theorem for a functor `G : J × K ⥤ C`,
showing that the limit of `G` can be computed as
the limit of the limits of the functors `G.obj (j, _)`.
-/
def fubini' : limit G ≅ limit ((curry.obj G) ⋙ lim) :=
begin
  have i : G ≅ uncurry.obj ((@curry J _ K _ C _).obj G) := currying.symm.unit_iso.app G,
  haveI : limits.has_limit (uncurry.obj ((@curry J _ K _ C _).obj G)) :=
    has_limit_of_iso i,
  transitivity limit (uncurry.obj ((@curry J _ K _ C _).obj G)),
  apply has_limit.iso_of_nat_iso i,
  exact fubini ((@curry J _ K _ C _).obj G),
end

@[simp]
lemma fubini'_hom_π_π {j} {k} : (fubini' G).hom ≫ limit.π _ j ≫ limit.π _ k = limit.π _ (j, k) :=
begin
  dsimp [fubini', is_limit.cone_point_unique_up_to_iso, is_limit.unique_up_to_iso],
  simp, dsimp, simp, -- See note [dsimp, simp].
end

@[simp]
lemma fubini'_inv_π {j} {k} : (fubini' G).inv ≫ limit.π _ (j, k) = limit.π _ j ≫ limit.π _ k :=
begin
  rw [←cancel_epi (fubini' G).hom],
  simp,
end

end

end category_theory.limits
