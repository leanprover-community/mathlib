/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Lemmas about traversing collections.

Inspired by:

    The Essence of the Iterator Pattern
    Jeremy Gibbons and Bruno César dos Santos Oliveira
    In Journal of Functional Programming. Vol. 19. No. 3&4. Pages 377−402. 2009.
    http://www.cs.ox.ac.uk/jeremy.gibbons/publications/iterator.pdf
-/

import tactic.cache
import category.traversable.basic

universe variables u

open is_lawful_traversable
open function (hiding comp)
open functor

attribute [functor_norm] is_lawful_traversable.naturality
attribute [simp] is_lawful_traversable.id_traverse

namespace traversable

variable {t : Type u → Type u}
variables [traversable t] [is_lawful_traversable t]
variables {G H : Type u → Type u}

variables [applicative G] [is_lawful_applicative G]
variables [applicative H] [is_lawful_applicative H]
variables {α β γ : Type u}
variables g : α → G β
variables h : β → H γ
variables f : β → γ

variables G H

def pure_transformation : applicative_transformation id G :=
{ app := @pure G _,
  preserves_pure' := λ α x, rfl,
  preserves_seq' := λ α β f x, by simp; refl }

@[simp] theorem pure_transformation_apply {α} (x : id α) :
  (pure_transformation G) x = pure x := rfl


variables {G H} (x : t β)

lemma map_eq_traverse_id : map f = @traverse t _ _ _ _ _ (id.mk ∘ f) :=
funext $ λ y, (traverse_eq_map_id f y).symm

theorem map_traverse (x : t α) :
  map f <$> traverse g x = traverse (map f ∘ g) x :=
begin
  rw @map_eq_traverse_id t _ _ _ _ f,
  refine (comp_traverse (id.mk ∘ f) g x).symm.trans _,
  congr, apply comp.applicative_comp_id
end

theorem traverse_map (f : β → G γ) (g : α → β) (x : t α) :
  traverse f (g <$> x) = traverse (f ∘ g) x :=
begin
  rw @map_eq_traverse_id t _ _ _ _ g,
  refine (comp_traverse f (id.mk ∘ g) x).symm.trans _,
  congr, apply comp.applicative_id_comp
end

lemma pure_traverse (x : t α) :
  traverse pure x = (pure x : G (t α)) :=
by have : traverse pure x = pure (traverse id.mk x) :=
     (naturality (pure_transformation G) id.mk x).symm;
   rwa id_traverse at this

lemma id_sequence (x : t α) :
  sequence (id.mk <$> x) = id.mk x :=
by simp [sequence, traverse_map, id_traverse]; refl

lemma comp_sequence (x : t (G (H α))) :
  sequence (comp.mk <$> x) = comp.mk (sequence <$> sequence x) :=
by simp [sequence, traverse_map]; rw ← comp_traverse; simp [map_id]

lemma naturality' (η : applicative_transformation G H) (x : t (G α)) :
  η (sequence x) = sequence (@η _ <$> x) :=
by simp [sequence, naturality, traverse_map]

end traversable
