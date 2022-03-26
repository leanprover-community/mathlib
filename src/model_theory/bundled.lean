/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.semantics
import category_theory.concrete_category.bundled
/-!
# Bundled First-Order Structures
This file bundles types together with their first-order structure.

## Main Definitions
* `first_order.language.Theory.Model` is the type of nonempty models of a particular theory.
* `first_order.language.equiv_setoid` is the isomorphism equivalence relation on bundled structures.

## TODO
* Define category structures on bundled structures and models.

-/

universes u v w

variables {L : first_order.language.{u v}}

@[protected] instance category_theory.bundled.Structure
  {L : first_order.language.{u v}} (M : category_theory.bundled.{w} L.Structure) :
  L.Structure M :=
M.str

namespace first_order
namespace language
open_locale first_order

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
instance equiv_setoid : setoid (category_theory.bundled L.Structure) :=
{ r := λ M N, nonempty (M ≃[L] N),
  iseqv := ⟨λ M, ⟨equiv.refl L M⟩, λ M N, nonempty.map equiv.symm,
    λ M N P, nonempty.map2 (λ MN NP, NP.comp MN)⟩ }

variable (T : L.Theory)

namespace Theory

/-- The type of nonempty models of a first-order theory. -/
structure Model :=
(carrier : Type w)
[struc : L.Structure carrier]
[is_model : T.model carrier]
[nonempty' : nonempty carrier]

attribute [instance] Model.struc Model.is_model Model.nonempty'

namespace Model

instance : has_coe_to_sort (T.Model) (Type w) := ⟨Model.carrier⟩

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (M : Type w) [L.Structure M] [M ⊨ T] [nonempty M] :
  T.Model := ⟨M⟩

@[simp]
lemma coe_of (M : Type w) [L.Structure M] [M ⊨ T] [nonempty M] : (of T M : Type w) = M := rfl

instance (M : T.Model) : nonempty M := infer_instance

section inhabited

local attribute [instance] trivial_unit_structure

instance : inhabited (Model (∅ : L.Theory)) :=
⟨Model.of _ unit⟩

end inhabited

end Model
end Theory
end language
end first_order
