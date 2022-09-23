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

* `a ∆ b`: `symm_diff a b`

## References

The proof of associativity follows the note "Associativity of the Symmetric Difference of Sets: A
Proof from the Book" by John McCuan:

* <https://people.math.gatech.edu/~mccuan/courses/4317/symmetricdifference.pdf>

## Tags
boolean ring, generalized boolean algebra, boolean algebra, symmetric differences
-/

open function

variables {α : Type*}

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
def symm_diff [has_sup α] [has_sdiff α] (a b : α) : α := a \ b ⊔ b \ a

/- This notation might conflict with the Laplacian once we have it. Feel free to put it in locale
`order` or `symm_diff` if that happens. -/
infix ` ∆ `:100 := symm_diff

lemma symm_diff_def [has_sup α] [has_sdiff α] (a b : α) : a ∆ b = (a \ b) ⊔ (b \ a) := rfl

lemma symm_diff_eq_xor (p q : Prop) : p ∆ q = xor p q := rfl

@[simp] lemma bool.symm_diff_eq_bxor : ∀ p q : bool, p ∆ q = bxor p q := dec_trivial

section generalized_coheyting_algebra
variables [generalized_coheyting_algebra α] (a b c d : α)

lemma symm_diff_comm : a ∆ b = b ∆ a := by simp only [(∆), sup_comm]

instance symm_diff_is_comm : is_commutative α (∆) := ⟨symm_diff_comm⟩

@[simp] lemma symm_diff_self : a ∆ a = ⊥ := by rw [(∆), sup_idem, sdiff_self]
@[simp] lemma symm_diff_bot : a ∆ ⊥ = a := by rw [(∆), sdiff_bot, bot_sdiff, sup_bot_eq]
@[simp] lemma bot_symm_diff : ⊥ ∆ a = a := by rw [symm_diff_comm, symm_diff_bot]

lemma symm_diff_of_le {a b : α} (h : a ≤ b) : a ∆ b = b \ a :=
by rw [symm_diff, sdiff_eq_bot_iff.2 h, bot_sup_eq]

lemma symm_diff_of_ge {a b : α} (h : b ≤ a) : a ∆ b = a \ b :=
by rw [symm_diff, sdiff_eq_bot_iff.2 h, sup_bot_eq]

lemma symm_diff_le {a b c : α} (ha : a ≤ b ⊔ c) (hb : b ≤ a ⊔ c) : a ∆ b ≤ c :=
sup_le (sdiff_le_iff.2 ha) $ sdiff_le_iff.2 hb

lemma symm_diff_le_iff {a b c : α} : a ∆ b ≤ c ↔ a ≤ b ⊔ c ∧ b ≤ a ⊔ c :=
by simp_rw [symm_diff, sup_le_iff, sdiff_le_iff]

@[simp] lemma symm_diff_le_sup {a b : α} : a ∆ b ≤ a ⊔ b := sup_le_sup sdiff_le sdiff_le

lemma symm_diff_eq_sup_sdiff_inf : a ∆ b = (a ⊔ b) \ (a ⊓ b) := by simp [sup_sdiff, symm_diff]

lemma disjoint.symm_diff_eq_sup {a b : α} (h : disjoint a b) : a ∆ b = a ⊔ b :=
by rw [(∆), h.sdiff_eq_left, h.sdiff_eq_right]

lemma symm_diff_sdiff : (a ∆ b) \ c = a \ (b ⊔ c) ⊔ b \ (a ⊔ c) :=
by rw [symm_diff, sup_sdiff_distrib, sdiff_sdiff_left, sdiff_sdiff_left]

@[simp] lemma symm_diff_sdiff_inf : a ∆ b \ (a ⊓ b) = a ∆ b :=
by { rw symm_diff_sdiff, simp [symm_diff] }

@[simp] lemma symm_diff_sdiff_eq_sup : a ∆ (b \ a) = a ⊔ b :=
begin
  rw [symm_diff, sdiff_idem],
  exact le_antisymm (sup_le_sup sdiff_le sdiff_le)
    (sup_le le_sdiff_sup $ le_sdiff_sup.trans $ sup_le le_sup_right le_sdiff_sup),
end

@[simp] lemma sdiff_symm_diff_eq_sup : (a \ b) ∆ b = a ⊔ b :=
by rw [symm_diff_comm, symm_diff_sdiff_eq_sup, sup_comm]

@[simp] lemma symm_diff_sup_inf : a ∆ b ⊔ a ⊓ b = a ⊔ b :=
begin
  refine le_antisymm (sup_le symm_diff_le_sup inf_le_sup) _,
  rw [sup_inf_left, symm_diff],
  refine sup_le (le_inf le_sup_right _) (le_inf _ le_sup_right),
  { rw sup_right_comm,
    exact le_sup_of_le_left le_sdiff_sup },
  { rw sup_assoc,
    exact le_sup_of_le_right le_sdiff_sup }
end

@[simp] lemma inf_sup_symm_diff : a ⊓ b ⊔ a ∆ b = a ⊔ b := by rw [sup_comm, symm_diff_sup_inf]

@[simp] lemma symm_diff_symm_diff_inf : a ∆ b ∆ (a ⊓ b) = a ⊔ b :=
by rw [←symm_diff_sdiff_inf a, sdiff_symm_diff_eq_sup, symm_diff_sup_inf]

@[simp] lemma inf_symm_diff_symm_diff : (a ⊓ b) ∆ (a ∆ b) = a ⊔ b :=
by rw [symm_diff_comm, symm_diff_symm_diff_inf]

lemma symm_diff_triangle : a ∆ c ≤ a ∆ b ⊔ b ∆ c :=
begin
  refine (sup_le_sup (sdiff_triangle a b c) $ sdiff_triangle _ b _).trans_eq _,
  rw [@sup_comm _ _ (c \ b), sup_sup_sup_comm, symm_diff, symm_diff],
end

end generalized_coheyting_algebra

section coheyting_algebra
variables [coheyting_algebra α] (a : α)

@[simp] lemma symm_diff_top' : a ∆ ⊤ = ￢a := by simp [symm_diff]
@[simp] lemma top_symm_diff' : ⊤ ∆ a = ￢a := by simp [symm_diff]

@[simp] lemma hnot_symm_diff_self : (￢a) ∆ a = ⊤ :=
by { rw [eq_top_iff, symm_diff, hnot_sdiff, sup_sdiff_self], exact codisjoint_hnot_left }

@[simp] lemma symm_diff_hnot_self : a ∆ ￢a = ⊤ := by rw [symm_diff_comm, hnot_symm_diff_self]

lemma is_compl.symm_diff_eq_top {a b : α} (h : is_compl a b) : a ∆ b = ⊤ :=
by rw [h.eq_hnot, hnot_symm_diff_self]

end coheyting_algebra

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] (a b c d : α)

@[simp] lemma sup_sdiff_symm_diff : (a ⊔ b) \ (a ∆ b) = a ⊓ b :=
sdiff_eq_symm inf_le_sup (by rw symm_diff_eq_sup_sdiff_inf)

lemma disjoint_symm_diff_inf : disjoint (a ∆ b) (a ⊓ b) :=
begin
  rw [symm_diff_eq_sup_sdiff_inf],
  exact disjoint_sdiff_self_left,
end

lemma inf_symm_diff_distrib_left : a ⊓ (b ∆ c) = (a ⊓ b) ∆ (a ⊓ c) :=
by rw [symm_diff_eq_sup_sdiff_inf, inf_sdiff_distrib_left, inf_sup_left, inf_inf_distrib_left,
  symm_diff_eq_sup_sdiff_inf]

lemma inf_symm_diff_distrib_right : (a ∆ b) ⊓ c = (a ⊓ c) ∆ (b ⊓ c) :=
by simp_rw [@inf_comm _ _ _ c, inf_symm_diff_distrib_left]

lemma sdiff_symm_diff : c \ (a ∆ b) = (c ⊓ a ⊓ b) ⊔ ((c \ a) ⊓ (c \ b)) :=
by simp only [(∆), sdiff_sdiff_sup_sdiff']

lemma sdiff_symm_diff' : c \ (a ∆ b) = (c ⊓ a ⊓ b) ⊔ (c \ (a ⊔ b)) :=
by rw [sdiff_symm_diff, sdiff_sup, sup_comm]

@[simp] lemma symm_diff_sdiff_left : (a ∆ b) \ a = b \ a :=
by rw [symm_diff_def, sup_sdiff, sdiff_idem, sdiff_sdiff_self, bot_sup_eq]

@[simp] lemma symm_diff_sdiff_right : (a ∆ b) \ b = a \ b :=
by rw [symm_diff_comm, symm_diff_sdiff_left]

@[simp] lemma sdiff_symm_diff_self : a \ (a ∆ b) = a ⊓ b := by simp [sdiff_symm_diff]

lemma symm_diff_eq_sup : a ∆ b = a ⊔ b ↔ disjoint a b :=
begin
  refine ⟨λ h, _, disjoint.symm_diff_eq_sup⟩,
  rw [symm_diff_eq_sup_sdiff_inf, sdiff_eq_self_iff_disjoint] at h,
  exact h.of_disjoint_inf_of_le le_sup_left,
end

@[simp] lemma le_symm_diff_iff_left : a ≤ a ∆ b ↔ disjoint a b :=
begin
  refine ⟨λ h, _, λ h, h.symm_diff_eq_sup.symm ▸ le_sup_left⟩,
  rw symm_diff_eq_sup_sdiff_inf at h,
  exact (le_sdiff_iff.1 $ inf_le_of_left_le h).le,
end

@[simp] lemma le_symm_diff_iff_right : b ≤ a ∆ b ↔ disjoint a b :=
by rw [symm_diff_comm, le_symm_diff_iff_left, disjoint.comm]

lemma symm_diff_symm_diff_left :
  a ∆ b ∆ c = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔ (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c) :=
calc a ∆ b ∆ c = ((a ∆ b) \ c) ⊔ (c \ (a ∆ b))   : symm_diff_def _ _
           ... = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔
                   ((c \ (a ⊔ b)) ⊔ (c ⊓ a ⊓ b)) :
                                by rw [sdiff_symm_diff', @sup_comm _ _ (c ⊓ a ⊓ b), symm_diff_sdiff]
           ... = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔
                   (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c)   : by ac_refl

lemma symm_diff_symm_diff_right :
  a ∆ (b ∆ c) = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔ (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c) :=
calc a ∆ (b ∆ c) = (a \ (b ∆ c)) ⊔ ((b ∆ c) \ a) : symm_diff_def _ _
             ... = (a \ (b ⊔ c)) ⊔ (a ⊓ b ⊓ c) ⊔
                     (b \ (c ⊔ a) ⊔ c \ (b ⊔ a))   :
                                by rw [sdiff_symm_diff', @sup_comm _ _ (a ⊓ b ⊓ c), symm_diff_sdiff]
             ... = (a \ (b ⊔ c)) ⊔ (b \ (a ⊔ c)) ⊔
                     (c \ (a ⊔ b)) ⊔ (a ⊓ b ⊓ c)   : by ac_refl

lemma symm_diff_assoc : a ∆ b ∆ c = a ∆ (b ∆ c) :=
by rw [symm_diff_symm_diff_left, symm_diff_symm_diff_right]

instance symm_diff_is_assoc : is_associative α (∆) := ⟨symm_diff_assoc⟩

lemma symm_diff_left_comm : a ∆ (b ∆ c) = b ∆ (a ∆ c) :=
by simp_rw [←symm_diff_assoc, symm_diff_comm]

lemma symm_diff_right_comm : a ∆ b ∆ c = a ∆ c ∆ b := by simp_rw [symm_diff_assoc, symm_diff_comm]

lemma symm_diff_symm_diff_symm_diff_comm : (a ∆ b) ∆ (c ∆ d) = (a ∆ c) ∆ (b ∆ d) :=
by simp_rw [symm_diff_assoc, symm_diff_left_comm]

@[simp] lemma symm_diff_symm_diff_cancel_left : a ∆ (a ∆ b) = b := by simp [←symm_diff_assoc]
@[simp] lemma symm_diff_symm_diff_cancel_right : b ∆ a ∆ a = b := by simp [symm_diff_assoc]

@[simp] lemma symm_diff_symm_diff_self' : a ∆ b ∆ a = b :=
by rw [symm_diff_comm,symm_diff_symm_diff_cancel_left]

lemma symm_diff_left_involutive (a : α) : involutive (∆ a) := symm_diff_symm_diff_cancel_right _
lemma symm_diff_right_involutive (a : α) : involutive ((∆) a) := symm_diff_symm_diff_cancel_left _
lemma symm_diff_left_injective (a : α) : injective (∆ a) := (symm_diff_left_involutive _).injective
lemma symm_diff_right_injective (a : α) : injective ((∆) a) :=
(symm_diff_right_involutive _).injective
lemma symm_diff_left_surjective (a : α) : surjective (∆ a) :=
(symm_diff_left_involutive _).surjective
lemma symm_diff_right_surjective (a : α) : surjective ((∆) a) :=
(symm_diff_right_involutive _).surjective

variables {a b c}

@[simp] lemma symm_diff_left_inj : a ∆ b = c ∆ b ↔ a = c := (symm_diff_left_injective _).eq_iff
@[simp] lemma symm_diff_right_inj : a ∆ b = a ∆ c ↔ b = c := (symm_diff_right_injective _).eq_iff

@[simp] lemma symm_diff_eq_left : a ∆ b = a ↔ b = ⊥ :=
calc a ∆ b = a ↔ a ∆ b = a ∆ ⊥ : by rw symm_diff_bot
           ... ↔     b = ⊥     : by rw symm_diff_right_inj

@[simp] lemma symm_diff_eq_right : a ∆ b = b ↔ a = ⊥ := by rw [symm_diff_comm, symm_diff_eq_left]

@[simp] lemma symm_diff_eq_bot : a ∆ b = ⊥ ↔ a = b :=
calc a ∆ b = ⊥ ↔ a ∆ b = a ∆ a : by rw symm_diff_self
           ... ↔     a = b     : by rw [symm_diff_right_inj, eq_comm]

protected lemma disjoint.symm_diff_left (ha : disjoint a c) (hb : disjoint b c) :
  disjoint (a ∆ b) c :=
by { rw symm_diff_eq_sup_sdiff_inf, exact (ha.sup_left hb).disjoint_sdiff_left }

protected lemma disjoint.symm_diff_right (ha : disjoint a b) (hb : disjoint a c) :
  disjoint a (b ∆ c) :=
(ha.symm.symm_diff_left hb.symm).symm

lemma symm_diff_eq_iff_sdiff_eq (ha : a ≤ c) : a ∆ b = c ↔ c \ a = b :=
begin
  rw ←symm_diff_of_le ha,
  exact ((symm_diff_right_involutive a).to_perm _).apply_eq_iff_eq_symm_apply.trans eq_comm,
end

end generalized_boolean_algebra

section boolean_algebra
variables [boolean_algebra α] (a b c : α)

lemma symm_diff_eq : a ∆ b = (a ⊓ bᶜ) ⊔ (b ⊓ aᶜ) := by simp only [(∆), sdiff_eq]

lemma symm_diff_top : a ∆ ⊤ = aᶜ := symm_diff_top' _
lemma top_symm_diff : ⊤ ∆ a = aᶜ := top_symm_diff' _

lemma compl_symm_diff : (a ∆ b)ᶜ = (a ⊓ b) ⊔ (aᶜ ⊓ bᶜ) :=
by simp only [←top_sdiff, sdiff_symm_diff, top_inf_eq]

lemma symm_diff_eq_top_iff : a ∆ b = ⊤ ↔ is_compl a b :=
by rw [symm_diff_eq_iff_sdiff_eq le_top, top_sdiff, compl_eq_iff_is_compl]

@[simp] lemma compl_symm_diff_self : aᶜ ∆ a = ⊤ := hnot_symm_diff_self _
@[simp] lemma symm_diff_compl_self : a ∆ aᶜ = ⊤ := symm_diff_hnot_self _

lemma symm_diff_symm_diff_right' :
  a ∆ (b ∆ c) = (a ⊓ b ⊓ c) ⊔ (a ⊓ bᶜ ⊓ cᶜ) ⊔ (aᶜ ⊓ b ⊓ cᶜ) ⊔ (aᶜ ⊓ bᶜ ⊓ c) :=
calc a ∆ (b ∆ c) = (a ⊓ ((b ⊓ c) ⊔ (bᶜ ⊓ cᶜ))) ⊔
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
