/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison

Defines a category, as a typeclass parametrised by the type of objects.
Introduces notations
  `X ⟶ Y` for the morphism spaces,
  `f ≫ g` for composition in the 'arrows' convention.

Users may like to add `f ⊚ g` for composition in the standard convention, using
```
local notation f ` ⊚ `:80 g:80 := category.comp g f    -- type as \oo
```
-/

import tactic.make_lemma
import tactic.interactive

namespace category_theory

universes u v

meta def obviously := `[skip]  

/- 
The propositional fields of `category` are annotated with the auto_param `obviously`, which is just a synonym for `skip`.
Actually, there is a tactic called `obviously` which is not part of this pull request, which should be used here. It successfully
discharges a great many of these goals. For now, proofs which could be provided entirely by `obviously` (and hence omitted entirely
and discharged by an auto_param), are all marked with a comment "-- obviously says:".
-/

class category (Obj : Type u) : Type (max u (v+1)) :=
(Hom     : Obj → Obj → Type v)
(id      : Π X : Obj, Hom X X)
(comp    : Π {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z)
(id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f . obviously)
(comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f . obviously)
(assoc   : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z), comp (comp f g) h = comp f (comp g h) . obviously)

notation `𝟙` := category.id -- type as \b1
infixr ` ≫ `:80 := category.comp -- type as \gg
infixr ` ⟶ `:10 := category.Hom -- type as \h

-- make_lemma is a command that creates a lemma from a structure field, discarding all auto_param wrappers from the type.
restate_axiom category.id_comp
restate_axiom category.comp_id
restate_axiom category.assoc
-- We tag some lemmas with the attribute `@[ematch]`, for later automation. (I'd be happy to change this to e.g. `@[search]`.)
attribute [simp,ematch] category.id_comp_lemma category.comp_id_lemma category.assoc_lemma 

abbreviation large_category (C : Type (u+1)) : Type (u+1) := category.{u+1 u} C
abbreviation small_category (C : Type u)     : Type (u+1) := category.{u u} C

end category_theory
