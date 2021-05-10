/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bryan Gin-ge Chen
-/

import order.boolean_algebra

/-!
# Symmetric difference

The symmetric difference or disjunctive union of sets `A` and `B` is the set of elements that are
in either `A` or `B` but not both. Translated into propositions, the symmetric difference is `xor`.

The symmetric difference operator (`symm_diff`) is defined in this file for any type with `⊔` and
`\` via the formula `(A \ B) ⊔ (B \ A)`, however the theorems proved about it only hold for
`generalized_boolean_algebra`s and `boolean_algebra`s.

The symmetric difference is the addition operator in the Boolean ring structure on Boolean algebras.

## Main declarations

* `symm_diff`: the symmetric difference operator, defined as `(A \ B) ⊔ (B \ A)`

In generalized Boolean algebras, the symmetric difference operator is:

* `symm_diff_comm`: commutative, and
* `symm_diff_assoc`: associative.

## Notations

* `a Δ b`: `symm_diff a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags
boolean ring, generalized boolean algebra, boolean algebra, symmetric differences
-/

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
def symm_diff {α : Type*} [has_sup α] [has_sdiff α] (A B : α) : α := (A \ B) ⊔ (B \ A)

infix ` Δ `:100 := symm_diff

lemma symm_diff_def {α : Type*} [has_sup α] [has_sdiff α] (A B : α) :
  A Δ B = (A \ B) ⊔ (B \ A) :=
rfl

lemma symm_diff_eq_xor (p q : Prop) : p Δ q = xor p q := rfl

section generalized_boolean_algebra
variables {α : Type*} [generalized_boolean_algebra α] (a b c : α)

lemma symm_diff_comm : a Δ b = b Δ a := by simp only [(Δ), sup_comm]

instance symm_diff_is_comm : is_commutative α (Δ) := ⟨symm_diff_comm⟩

lemma sdiff_symm_diff : c \ (a Δ b) = (c ⊓ a ⊓ b) ⊔ ((c \ a) ⊓ (c \ b)) :=
by simp only [(Δ), sdiff_sdiff_sup_sdiff']

lemma sdiff_symm_diff' : c \ (a Δ b) = (c \ (a ⊔ b)) ⊔ (c ⊓ a ⊓ b) :=
by rw [sdiff_symm_diff, sdiff_sup, sup_comm]

lemma symm_diff_sdiff : (a Δ b) \ c = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) :=
by rw [symm_diff_def, sup_sdiff, sdiff_sdiff_left, sdiff_sdiff_left]

lemma symm_diff_symm_diff_left :
  a Δ b Δ c = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔ (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c) :=
calc a Δ b Δ c = ((a Δ b) \ c) ⊔ (c \ (a Δ b))   : symm_diff_def _ _
           ... = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔
                   ((c \ (a ⊔ b)) ⊔ (c ⊓ a ⊓ b)) : by rw [sdiff_symm_diff', symm_diff_sdiff]
           ... = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔
                   (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c)   : by ac_refl

lemma symm_diff_symm_diff_right :
  a Δ (b Δ c) = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔ (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c) :=
calc a Δ (b Δ c) = (a \ (b Δ c)) ⊔ ((b Δ c) \ a) : symm_diff_def _ _
           ... = (a \ (b ⊔ c)) ⊔ (a ⊓ b ⊓ c) ⊔
                   (b \ (c ⊔ a) ⊔ c \ (b ⊔ a))   : by rw [sdiff_symm_diff', symm_diff_sdiff]
           ... = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔
                   (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c)   : by ac_refl

lemma symm_diff_assoc : a Δ b Δ c = a Δ (b Δ c) :=
by rw [symm_diff_symm_diff_left, symm_diff_symm_diff_right]

instance symm_diff_is_assoc : is_associative α (Δ) := ⟨symm_diff_assoc⟩

end generalized_boolean_algebra

section boolean_algebra
variables {α : Type*} [boolean_algebra α] (a b c : α)

lemma symm_diff_eq : a Δ b = (a ⊓ bᶜ) ⊔ (b ⊓ aᶜ) := by simp only [(Δ), sdiff_eq]

lemma compl_symm_diff : (a Δ b)ᶜ = (a ⊓ b) ⊔ (aᶜ ⊓ bᶜ) :=
by simp only [←top_sdiff, sdiff_symm_diff, top_inf_eq]

lemma symm_diff_symm_diff_right' :
  a Δ (b Δ c) = (a ⊓ b ⊓ c) ⊔ (a ⊓ bᶜ ⊓ cᶜ) ⊔ (aᶜ ⊓ b ⊓ cᶜ) ⊔ (aᶜ ⊓ bᶜ ⊓ c) :=
calc a Δ (b Δ c) = (a ⊓ ((b ⊓ c) ⊔ (bᶜ ⊓ cᶜ))) ⊔
                     (((b ⊓ cᶜ) ⊔ (c ⊓ bᶜ)) ⊓ aᶜ)  : by rw [symm_diff_eq, compl_symm_diff,
                                                            symm_diff_eq]
             ... = (a ⊓ b ⊓ c) ⊔ (a ⊓ bᶜ ⊓ cᶜ) ⊔
                     (b ⊓ cᶜ ⊓ aᶜ) ⊔ (c ⊓ bᶜ ⊓ aᶜ) : by rw [inf_sup_left, inf_sup_right,
                                                            ←sup_assoc, ←inf_assoc, ←inf_assoc]
             ... = (a ⊓ b ⊓ c) ⊔ (a ⊓ bᶜ ⊓ cᶜ) ⊔
                     (aᶜ ⊓ b ⊓ cᶜ) ⊔ (aᶜ ⊓ bᶜ ⊓ c) : begin
                                                       congr' 1,
                                                       { congr' 1,
                                                         rw [inf_comm, inf_assoc], },
                                                       { apply inf_left_right_swap }
                                                     end

end boolean_algebra
