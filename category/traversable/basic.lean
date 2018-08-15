/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Type classes for traversing collections. The concepts and laws are taken from
http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Traversable.html
-/

import tactic.cache
import category.applicative

open function (hiding comp)

universes u v w

section applicative_transformation

variables (f : Type u → Type v) [applicative f] [is_lawful_applicative f]
variables (g : Type u → Type w) [applicative g] [is_lawful_applicative g]

structure applicative_transformation : Type (max (u+1) v w) :=
(F : ∀ {α : Type u}, f α → g α)
(preserves_pure' : ∀ {α : Type u} (x : α), F (pure x) = pure x)
(preserves_seq' : ∀ {α β : Type u} (x : f (α → β)) (y : f α), F (x <*> y) = F x <*> F y)

end applicative_transformation

namespace applicative_transformation

variables (f : Type u → Type v) [applicative f] [is_lawful_applicative f]
variables (g : Type u → Type w) [applicative g] [is_lawful_applicative g]

instance : has_coe_to_fun (applicative_transformation f g) :=
{ F := λ _, ∀ {α}, f α → g α,
  coe := λ m, m.F }

variables {f g}
variables (η : applicative_transformation f g)

@[functor_norm]
lemma preserves_pure :
  ∀ {α : Type u} (x : α), η (pure x) = pure x :=
by apply applicative_transformation.preserves_pure'

@[functor_norm]
lemma preserves_seq :
  ∀ {α β : Type u} (x : f (α → β)) (y : f α), η (x <*> y) = η x <*> η y :=
by apply applicative_transformation.preserves_seq'

@[functor_norm]
lemma preserves_map {α β : Type u} (x : α → β)  (y : f α) :
  η (x <$> y) = x <$> η y :=
by rw [← pure_seq_eq_map,η.preserves_seq]; simp with functor_norm

end applicative_transformation

open applicative_transformation

class traversable (t : Type u → Type u) extends functor t :=
(traverse : Π {m : Type u → Type u} [applicative m]
   {α β : Type u},
   (α → m β) → t α → m (t β))

open functor

export traversable (traverse)

section functions

variables {t : Type u → Type u}
variables {m : Type u → Type v} [applicative m]
variables {α β : Type u}


variables {f : Type u → Type u} [applicative f]

def sequence [traversable t] :
  t (f α) → f (t α) :=
traverse id

end functions

class is_lawful_traversable (t : Type u → Type u) [traversable t]
extends is_lawful_functor t :
  Type (u+1) :=
(id_traverse : ∀ {α : Type u} (x : t α), traverse id.mk x = x )
(comp_traverse : ∀ {G H : Type u → Type u}
               [applicative G] [applicative H]
               [is_lawful_applicative G] [is_lawful_applicative H]
               {α β γ : Type u}
               (g : α → G β) (h : β → H γ) (x : t α),
   traverse (comp.mk ∘ map h ∘ g) x =
   comp.mk (map (traverse h) (traverse g x)))
(map_traverse : ∀ {G : Type u → Type u}
               [applicative G] [is_lawful_applicative G]
               {α β γ : Type u}
               (g : α → G β) (h : β → γ)
               (x : t α),
               map (map h) (traverse g x) =
               traverse (map h ∘ g) x)
(traverse_map : ∀ {G : Type u → Type u}
               [applicative G] [is_lawful_applicative G]
               {α β γ : Type u}
               (g : α → β) (h : β → G γ)
               (x : t α),
               traverse h (map g x) =
               traverse (h ∘ g) x)
(naturality : ∀ {G H : Type u → Type u}
                [applicative G] [applicative H]
                [is_lawful_applicative G] [is_lawful_applicative H]
                (η : applicative_transformation G H),
                ∀ {α β : Type u} (f : α → G β) (x : t α),
                  η (traverse f x) = traverse (@η _ ∘ f) x)
