/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.category.Top.basic
import category_theory.eq_to_hom

/-!
# The category of open sets in a topological space.

We define `to_Top : opens X ⥤ Top` and
`map (f : X ⟶ Y) : opens Y ⥤ opens X`, given by taking preimages of open sets.

Unfortunately `opens` isn't (usefully) a functor `Top ⥤ Cat`.
(One can in fact define such a functor,
but using it results in unresolvable `eq.rec` terms in goals.)

Really it's a 2-functor from (spaces, continuous functions, equalities)
to (categories, functors, natural isomorphisms).
We don't attempt to set up the full theory here, but do provide the natural isomorphisms
`map_id : map (𝟙 X) ≅ 𝟭 (opens X)` and
`map_comp : map (f ≫ g) ≅ map g ⋙ map f`.

Beyond that, there's a collection of simp lemmas for working with these constructions.
-/

open category_theory
open topological_space
open opposite

universe u

namespace topological_space.opens

variables {X Y Z : Top.{u}}

/-!
Since `opens X` has a partial order, it automatically receives a `category` instance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ulift (plift (U ≤ V))`.
-/

/-!
We now construct as morphisms various inclusions of open sets.
-/
-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...

/--
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def inf_le_left (U V : opens X) : U ⊓ V ⟶ U :=
hom_of_le inf_le_left

/--
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def inf_le_right (U V : opens X) : U ⊓ V ⟶ V :=
hom_of_le inf_le_right

/--
The inclusion `U i ⟶ supr U` as a morphism in the category of open sets.
-/
def le_supr {ι : Type*} (U : ι → opens X) (i : ι) : U i ⟶ supr U :=
hom_of_le (le_supr U i)

instance opens_hom_has_coe_to_fun {U V : opens X} : has_coe_to_fun (U ⟶ V) :=
{ F := λ f, U → V,
  coe := λ f x, ⟨x, (le_of_hom f) x.2⟩ }

/--
The functor from open sets in `X` to `Top`,
realising each open set as a topological space itself.
-/
def to_Top (X : Top.{u}) : opens X ⥤ Top :=
{ obj := λ U, ⟨U.val, infer_instance⟩,
  map := λ U V i, ⟨λ x, ⟨x.1, (le_of_hom i) x.2⟩,
    (embedding.continuous_iff embedding_subtype_coe).2 continuous_induced_dom⟩ }

@[simp]
lemma to_Top_map (X : Top.{u}) {U V : opens X} {f : U ⟶ V} {x} {h} :
  ((to_Top X).map f) ⟨x, h⟩ = ⟨x, (le_of_hom f) h⟩ :=
rfl

/-- `opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map (f : X ⟶ Y) : opens Y ⥤ opens X :=
{ obj := λ U, ⟨ f ⁻¹' U.val, f.continuous _ U.property ⟩,
  map := λ U V i, ⟨ ⟨ λ a b, (le_of_hom i) b ⟩ ⟩ }.

@[simp] lemma map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, f.continuous _ p⟩ :=
rfl

@[simp] lemma map_id_obj (U : opens X) : (map (𝟙 X)).obj U = U :=
by { ext, refl } -- not quite `rfl`, since we don't have eta for records

@[simp] lemma map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
rfl

@[simp] lemma map_id_obj_unop (U : (opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U :=
by simp
@[simp] lemma op_map_id_obj (U : (opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U :=
by simp

section
variable (X)

/--
The functor `opens X ⥤ opens X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simps]
def map_id : map (𝟙 X) ≅ 𝟭 (opens X) :=
{ hom := { app := λ U, eq_to_hom (map_id_obj U) },
  inv := { app := λ U, eq_to_hom (map_id_obj U).symm } }

end

@[simp] lemma map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
by { ext, refl } -- not quite `rfl`, since we don't have eta for records

@[simp] lemma map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) :
  (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
rfl

@[simp] lemma map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
by simp
@[simp] lemma op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
by simp

/--
The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simps]
def map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
{ hom := { app := λ U, eq_to_hom (map_comp_obj f g U) },
  inv := { app := λ U, eq_to_hom (map_comp_obj f g U).symm } }

-- We could make `f g` implicit here, but it's nice to be able to see when
-- they are the identity (often!)
def map_iso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
nat_iso.of_components (λ U, eq_to_iso (congr_fun (congr_arg functor.obj (congr_arg map h)) U) )
  (by obviously)

@[simp] lemma map_iso_refl (f : X ⟶ Y) (h) : map_iso f f h = iso.refl (map _) := rfl

@[simp] lemma map_iso_hom_app (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).hom.app U = eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h)) U) :=
rfl

@[simp] lemma map_iso_inv_app (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).inv.app U =
     eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h.symm)) U) :=
rfl

end topological_space.opens
