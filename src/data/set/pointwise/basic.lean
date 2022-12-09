/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import data.set.lattice
import group_theory.group_action.opposite

/-!
# Pointwise operations of sets

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s * t`: Multiplication, set of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s + t`: Addition, set of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s⁻¹`: Inversion, set of all `x⁻¹` where `x ∈ s`.
* `-s`: Negation, set of all `-x` where `x ∈ s`.
* `s / t`: Division, set of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s - t`: Subtraction, set of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

/--
Pointwise monoids (`set`, `finset`, `filter`) have derived pointwise actions of the form
`has_smul α β → has_smul α (set β)`. When `α` is `ℕ` or `ℤ`, this action conflicts with the
nat or int action coming from `set β` being a `monoid` or `div_inv_monoid`. For example,
`2 • {a, b}` can both be `{2 • a, 2 • b}` (pointwise action, pointwise repeated addition,
`set.has_smul_set`) and `{a + a, a + b, b + a, b + b}` (nat or int action, repeated pointwise
addition, `set.has_nsmul`).

Because the pointwise action can easily be spelled out in such cases, we give higher priority to the
nat and int actions.
-/
library_note "pointwise nat action"

open function

variables {F α β γ : Type*} {ι : Sort*} {κ : ι → Sort*}

namespace set

/-! ### `0`/`1` as sets -/

section one
variables [has_one α] {s : set α} {a : α}

/-- The set `1 : set α` is defined as `{1}` in locale `pointwise`. -/
@[to_additive "The set `0 : set α` is defined as `{0}` in locale `pointwise`."]
protected def has_one : has_one (set α) := ⟨{1}⟩

localized "attribute [instance] set.has_one set.has_zero" in pointwise

@[to_additive] lemma singleton_one : ({1} : set α) = 1 := rfl
@[simp, to_additive] lemma mem_one : a ∈ (1 : set α) ↔ a = 1 := iff.rfl
@[to_additive] lemma one_mem_one : (1 : α) ∈ (1 : set α) := eq.refl _
@[simp, to_additive] lemma one_subset : 1 ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff
@[to_additive] lemma one_nonempty : (1 : set α).nonempty := ⟨1, rfl⟩
@[simp, to_additive] lemma image_one {f : α → β} : f '' 1 = {f 1} := image_singleton
@[to_additive] lemma subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 := subset_singleton_iff_eq
@[to_additive] lemma nonempty.subset_one_iff (h : s.nonempty) : s ⊆ 1 ↔ s = 1 :=
h.subset_singleton_iff

/-- The singleton operation as a `one_hom`. -/
@[to_additive "The singleton operation as a `zero_hom`."]
def singleton_one_hom : one_hom α (set α) := ⟨singleton, singleton_one⟩

@[simp, to_additive] lemma coe_singleton_one_hom : (singleton_one_hom : α → set α) = singleton :=
rfl

end one

/-! ### Set negation/inversion -/

section inv

/-- The pointwise inversion of set `s⁻¹` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`. It i
equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[to_additive "The pointwise negation of set `-s` is defined as `{x | -x ∈ s}` in locale
`pointwise`. It is equal to `{-x | x ∈ s}`, see `set.image_neg`."]
protected def has_inv [has_inv α] : has_inv (set α) := ⟨preimage has_inv.inv⟩

localized "attribute [instance] set.has_inv set.has_neg" in pointwise

section has_inv
variables [has_inv α] {s t : set α} {a : α}

@[simp, to_additive] lemma mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := iff.rfl
@[simp, to_additive] lemma inv_preimage : has_inv.inv ⁻¹' s = s⁻¹ := rfl
@[simp, to_additive] lemma inv_empty : (∅ : set α)⁻¹ = ∅ := rfl
@[simp, to_additive] lemma inv_univ : (univ : set α)⁻¹ = univ := rfl
@[simp, to_additive] lemma inter_inv : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ := preimage_inter
@[simp, to_additive] lemma union_inv : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ := preimage_union
@[simp, to_additive] lemma Inter_inv (s : ι → set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ := preimage_Inter
@[simp, to_additive] lemma Union_inv (s : ι → set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ := preimage_Union
@[simp, to_additive] lemma compl_inv : (sᶜ)⁻¹ = (s⁻¹)ᶜ := preimage_compl

end has_inv

section has_involutive_inv
variables [has_involutive_inv α] {s t : set α} {a : α}

@[to_additive] lemma inv_mem_inv : a⁻¹ ∈ s⁻¹ ↔ a ∈ s := by simp only [mem_inv, inv_inv]

@[simp, to_additive] lemma nonempty_inv : s⁻¹.nonempty ↔ s.nonempty :=
inv_involutive.surjective.nonempty_preimage

@[to_additive] lemma nonempty.inv (h : s.nonempty) : s⁻¹.nonempty := nonempty_inv.2 h

@[simp, to_additive]
lemma image_inv : has_inv.inv '' s = s⁻¹ :=
congr_fun (image_eq_preimage_of_inverse inv_involutive.left_inverse inv_involutive.right_inverse) _

@[simp, to_additive]
instance : has_involutive_inv (set α) :=
{ inv := has_inv.inv,
  inv_inv := λ s, by { simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id'] } }

@[simp, to_additive]
lemma inv_subset_inv : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
(equiv.inv α).surjective.preimage_subset_preimage_iff

@[to_additive] lemma inv_subset : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ := by { rw [← inv_subset_inv, inv_inv] }

@[simp, to_additive] lemma inv_singleton (a : α) : ({a} : set α)⁻¹ = {a⁻¹} :=
by rw [←image_inv, image_singleton]

@[simp, to_additive] lemma inv_insert (a : α) (s : set α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ :=
by rw [insert_eq, union_inv, inv_singleton, insert_eq]

@[to_additive] lemma inv_range {ι : Sort*} {f : ι → α} : (range f)⁻¹ = range (λ i, (f i)⁻¹) :=
by { rw ←image_inv, exact (range_comp _ _).symm }

open mul_opposite

@[to_additive]
lemma image_op_inv : op '' s⁻¹ = (op '' s)⁻¹ :=
by simp_rw [←image_inv, function.semiconj.set_image op_inv s]

end has_involutive_inv
end inv

open_locale pointwise

/-! ### Set addition/multiplication -/

section has_mul
variables [has_mul α] {s s₁ s₂ t t₁ t₂ u : set α} {a b : α}

/-- The pointwise multiplication of sets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive "The pointwise addition of sets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in
locale `pointwise`."]
protected def has_mul : has_mul (set α) := ⟨image2 (*)⟩

localized "attribute [instance] set.has_mul set.has_add" in pointwise

@[simp, to_additive]
lemma image2_mul : image2 has_mul.mul s t = s * t := rfl

@[to_additive]
lemma mem_mul : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a := iff.rfl

@[to_additive] lemma mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t := mem_image2_of_mem

@[to_additive add_image_prod]
lemma image_mul_prod : (λ x : α × α, x.fst * x.snd) '' s ×ˢ t = s * t := image_prod _

@[simp, to_additive] lemma empty_mul : ∅ * s = ∅ := image2_empty_left
@[simp, to_additive] lemma mul_empty : s * ∅ = ∅ := image2_empty_right
@[simp, to_additive] lemma mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp, to_additive] lemma mul_nonempty : (s * t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
@[to_additive] lemma nonempty.mul : s.nonempty → t.nonempty → (s * t).nonempty := nonempty.image2
@[to_additive] lemma nonempty.of_mul_left : (s * t).nonempty → s.nonempty := nonempty.of_image2_left
@[to_additive] lemma nonempty.of_mul_right : (s * t).nonempty → t.nonempty :=
nonempty.of_image2_right
@[simp, to_additive] lemma mul_singleton : s * {b} = (* b) '' s := image2_singleton_right
@[simp, to_additive] lemma singleton_mul : {a} * t = ((*) a) '' t := image2_singleton_left
@[simp, to_additive] lemma singleton_mul_singleton : ({a} : set α) * {b} = {a * b} :=
image2_singleton

@[to_additive, mono] lemma mul_subset_mul : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ * s₂ ⊆ t₁ * t₂ := image2_subset
@[to_additive] lemma mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ := image2_subset_left
@[to_additive] lemma mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t := image2_subset_right
@[to_additive] lemma mul_subset_iff : s * t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x * y ∈ u := image2_subset_iff

attribute [mono] add_subset_add

@[to_additive] lemma union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t := image2_union_left
@[to_additive] lemma mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ := image2_union_right
@[to_additive] lemma inter_mul_subset : (s₁ ∩ s₂) * t ⊆ s₁ * t ∩ (s₂ * t) :=
image2_inter_subset_left
@[to_additive] lemma mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
image2_inter_subset_right

@[to_additive] lemma Union_mul_left_image : (⋃ a ∈ s, ((*) a) '' t) = s * t := Union_image_left _
@[to_additive] lemma Union_mul_right_image : (⋃ a ∈ t, (* a) '' s) = s * t := Union_image_right _

@[to_additive] lemma Union_mul (s : ι → set α) (t : set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
image2_Union_left _ _ _
@[to_additive] lemma mul_Union (s : set α) (t : ι → set α) : s * (⋃ i, t i) = ⋃ i, s * t i :=
image2_Union_right _ _ _

@[to_additive]
lemma Union₂_mul (s : Π i, κ i → set α) (t : set α) : (⋃ i j, s i j) * t = ⋃ i j, s i j * t :=
image2_Union₂_left _ _ _

@[to_additive]
lemma mul_Union₂ (s : set α) (t : Π i, κ i → set α) : s * (⋃ i j, t i j) = ⋃ i j, s * t i j :=
image2_Union₂_right _ _ _

@[to_additive]
lemma Inter_mul_subset (s : ι → set α) (t : set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
image2_Inter_subset_left _ _ _

@[to_additive]
lemma mul_Inter_subset (s : set α) (t : ι → set α) : s * (⋂ i, t i) ⊆ ⋂ i, s * t i :=
image2_Inter_subset_right _ _ _

@[to_additive]
lemma Inter₂_mul_subset (s : Π i, κ i → set α) (t : set α) :
  (⋂ i j, s i j) * t ⊆ ⋂ i j, s i j * t :=
image2_Inter₂_subset_left _ _ _

@[to_additive]
lemma mul_Inter₂_subset (s : set α) (t : Π i, κ i → set α) :
  s * (⋂ i j, t i j) ⊆ ⋂ i j, s * t i j :=
image2_Inter₂_subset_right _ _ _

/-- The singleton operation as a `mul_hom`. -/
@[to_additive "The singleton operation as an `add_hom`."]
def singleton_mul_hom : α →ₙ* set α := ⟨singleton, λ a b, singleton_mul_singleton.symm⟩

@[simp, to_additive] lemma coe_singleton_mul_hom : (singleton_mul_hom : α → set α) = singleton :=
rfl
@[simp, to_additive] lemma singleton_mul_hom_apply (a : α) : singleton_mul_hom a = {a} := rfl

open mul_opposite

@[simp, to_additive]
lemma image_op_mul : op '' (s * t) = op '' t * op '' s := image_image2_antidistrib op_mul

end has_mul

/-! ### Set subtraction/division -/

section has_div
variables [has_div α] {s s₁ s₂ t t₁ t₂ u : set α} {a b : α}

/-- The pointwise division of sets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`pointwise`. -/
@[to_additive "The pointwise subtraction of sets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}` in
locale `pointwise`."]
protected def has_div : has_div (set α) := ⟨image2 (/)⟩

localized "attribute [instance] set.has_div set.has_sub" in pointwise

@[simp, to_additive]
lemma image2_div : image2 has_div.div s t = s / t := rfl

@[to_additive]
lemma mem_div : a ∈ s / t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x / y = a := iff.rfl

@[to_additive] lemma div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t := mem_image2_of_mem

@[to_additive add_image_prod]
lemma image_div_prod : (λ x : α × α, x.fst / x.snd) '' s ×ˢ t = s / t := image_prod _

@[simp, to_additive] lemma empty_div : ∅ / s = ∅ := image2_empty_left
@[simp, to_additive] lemma div_empty : s / ∅ = ∅ := image2_empty_right
@[simp, to_additive] lemma div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp, to_additive] lemma div_nonempty : (s / t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
@[to_additive] lemma nonempty.div : s.nonempty → t.nonempty → (s / t).nonempty := nonempty.image2
@[to_additive] lemma nonempty.of_div_left : (s / t).nonempty → s.nonempty := nonempty.of_image2_left
@[to_additive] lemma nonempty.of_div_right : (s / t).nonempty → t.nonempty :=
nonempty.of_image2_right
@[simp, to_additive] lemma div_singleton : s / {b} = (/ b) '' s := image2_singleton_right
@[simp, to_additive] lemma singleton_div : {a} / t = ((/) a) '' t := image2_singleton_left
@[simp, to_additive] lemma singleton_div_singleton : ({a} : set α) / {b} = {a / b} :=
image2_singleton

@[to_additive, mono] lemma div_subset_div : s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ / s₂ ⊆ t₁ / t₂ := image2_subset
@[to_additive] lemma div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ := image2_subset_left
@[to_additive] lemma div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t := image2_subset_right
@[to_additive] lemma div_subset_iff : s / t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x / y ∈ u := image2_subset_iff

attribute [mono] sub_subset_sub

@[to_additive] lemma union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t := image2_union_left
@[to_additive] lemma div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ := image2_union_right
@[to_additive] lemma inter_div_subset : (s₁ ∩ s₂) / t ⊆ s₁ / t ∩ (s₂ / t) :=
image2_inter_subset_left
@[to_additive] lemma div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
image2_inter_subset_right

@[to_additive] lemma Union_div_left_image : (⋃ a ∈ s, ((/) a) '' t) = s / t := Union_image_left _
@[to_additive] lemma Union_div_right_image : (⋃ a ∈ t, (/ a) '' s) = s / t := Union_image_right _

@[to_additive] lemma Union_div (s : ι → set α) (t : set α) : (⋃ i, s i) / t = ⋃ i, s i / t :=
image2_Union_left _ _ _
@[to_additive] lemma div_Union (s : set α) (t : ι → set α) : s / (⋃ i, t i) = ⋃ i, s / t i :=
image2_Union_right _ _ _

@[to_additive]
lemma Union₂_div (s : Π i, κ i → set α) (t : set α) : (⋃ i j, s i j) / t = ⋃ i j, s i j / t :=
image2_Union₂_left _ _ _

@[to_additive]
lemma div_Union₂ (s : set α) (t : Π i, κ i → set α) : s / (⋃ i j, t i j) = ⋃ i j, s / t i j :=
image2_Union₂_right _ _ _

@[to_additive]
lemma Inter_div_subset (s : ι → set α) (t : set α) : (⋂ i, s i) / t ⊆ ⋂ i, s i / t :=
image2_Inter_subset_left _ _ _

@[to_additive]
lemma div_Inter_subset (s : set α) (t : ι → set α) : s / (⋂ i, t i) ⊆ ⋂ i, s / t i :=
image2_Inter_subset_right _ _ _

@[to_additive]
lemma Inter₂_div_subset (s : Π i, κ i → set α) (t : set α) :
  (⋂ i j, s i j) / t ⊆ ⋂ i j, s i j / t :=
image2_Inter₂_subset_left _ _ _

@[to_additive]
lemma div_Inter₂_subset (s : set α) (t : Π i, κ i → set α) :
  s / (⋂ i j, t i j) ⊆ ⋂ i j, s / t i j :=
image2_Inter₂_subset_right _ _ _

end has_div

/-!
### Algebraic instances

We declare `set.has_nsmul` before `set.has_smul_set` to make sure `n • s` means the right thing.
See note [pointwise nat action].
-/

open_locale pointwise

/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `finset`. See
note [pointwise nat action].-/
protected def has_nsmul [has_zero α] [has_add α] : has_smul ℕ (set α) := ⟨nsmul_rec⟩

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`set`. See note [pointwise nat action]. -/
@[to_additive]
protected def has_npow [has_one α] [has_mul α] : has_pow (set α) ℕ := ⟨λ s n, npow_rec n s⟩

/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `set`. See note [pointwise nat action]. -/
protected def has_zsmul [has_zero α] [has_add α] [has_neg α] : has_smul ℤ (set α) := ⟨zsmul_rec⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `set`. See note [pointwise nat action]. -/
@[to_additive] protected def has_zpow [has_one α] [has_mul α] [has_inv α] : has_pow (set α) ℤ :=
⟨λ s n, zpow_rec n s⟩

localized "attribute [instance] set.has_nsmul set.has_npow set.has_zsmul set.has_zpow" in pointwise

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_semigroup` under pointwise operations if `α` is."]
protected def semigroup [semigroup α] : semigroup (set α) :=
{ mul_assoc := λ _ _ _, image2_assoc mul_assoc,
  ..set.has_mul }

/-- `set α` is a `comm_semigroup` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_semigroup` under pointwise operations if `α` is."]
protected def comm_semigroup [comm_semigroup α] : comm_semigroup (set α) :=
{ mul_comm := λ s t, image2_comm mul_comm
  ..set.semigroup }

section mul_one_class
variables [mul_one_class α]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_zero_class` under pointwise operations if `α` is."]
protected def mul_one_class : mul_one_class (set α) :=
{ mul_one := λ s, by { simp only [← singleton_one, mul_singleton, mul_one, image_id'] },
  one_mul := λ s, by { simp only [← singleton_one, singleton_mul, one_mul, image_id'] },
  ..set.has_one, ..set.has_mul }

localized "attribute [instance] set.mul_one_class set.add_zero_class set.semigroup set.add_semigroup
  set.comm_semigroup set.add_comm_semigroup" in pointwise

@[to_additive] lemma subset_mul_left (s : set α) {t : set α} (ht : (1 : α) ∈ t) : s ⊆ s * t :=
λ x hx, ⟨x, 1, hx, ht, mul_one _⟩

@[to_additive] lemma subset_mul_right {s : set α} (t : set α) (hs : (1 : α) ∈ s) : t ⊆ s * t :=
λ x hx, ⟨1, x, hs, hx, one_mul _⟩

/-- The singleton operation as a `monoid_hom`. -/
@[to_additive "The singleton operation as an `add_monoid_hom`."]
def singleton_monoid_hom : α →* set α := { ..singleton_mul_hom, ..singleton_one_hom }

@[simp, to_additive] lemma coe_singleton_monoid_hom :
  (singleton_monoid_hom : α → set α) = singleton := rfl
@[simp, to_additive] lemma singleton_monoid_hom_apply (a : α) : singleton_monoid_hom a = {a} := rfl

end mul_one_class

section monoid
variables [monoid α] {s t : set α} {a : α} {m n : ℕ}

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_monoid` under pointwise operations if `α` is."]
protected def monoid : monoid (set α) := { ..set.semigroup, ..set.mul_one_class, ..set.has_npow }

localized "attribute [instance] set.monoid set.add_monoid" in pointwise

@[to_additive] lemma pow_mem_pow (ha : a ∈ s) : ∀ n : ℕ, a ^ n ∈ s ^ n
| 0 := by { rw pow_zero, exact one_mem_one }
| (n + 1) := by { rw pow_succ, exact mul_mem_mul ha (pow_mem_pow _) }

@[to_additive] lemma pow_subset_pow (hst : s ⊆ t) : ∀ n : ℕ, s ^ n ⊆ t ^ n
| 0 := by { rw pow_zero, exact subset.rfl }
| (n + 1) := by { rw pow_succ, exact mul_subset_mul hst (pow_subset_pow _) }

@[to_additive] lemma mul_univ_of_one_mem (hs : (1 : α) ∈ s) : s * univ = univ :=
eq_univ_iff_forall.2 $ λ a, mem_mul.2 ⟨_, _, hs, mem_univ _, one_mul _⟩

@[to_additive] lemma univ_mul_of_one_mem (ht : (1 : α) ∈ t) : univ * t = univ :=
eq_univ_iff_forall.2 $ λ a, mem_mul.2 ⟨_, _, mem_univ _, ht, mul_one _⟩

@[simp, to_additive] lemma univ_mul_univ : (univ : set α) * univ = univ :=
mul_univ_of_one_mem $ mem_univ _

end monoid

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive "`set α` is an `add_comm_monoid` under pointwise operations if `α` is."]
protected def comm_monoid [comm_monoid α] : comm_monoid (set α) :=
{ ..set.monoid, ..set.comm_semigroup }

localized "attribute [instance] set.comm_monoid set.add_comm_monoid" in pointwise

section division_monoid
variables [division_monoid α] {s t : set α}

@[to_additive] protected lemma mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 :=
begin
  refine ⟨λ h, _, _⟩,
  { have hst : (s * t).nonempty := h.symm.subst one_nonempty,
    obtain ⟨a, ha⟩ := hst.of_image2_left,
    obtain ⟨b, hb⟩ := hst.of_image2_right,
    have H : ∀ {a b}, a ∈ s → b ∈ t → a * b = (1 : α) :=
      λ a b ha hb, (h.subset $ mem_image2_of_mem ha hb),
    refine ⟨a, b, _, _, H ha hb⟩; refine eq_singleton_iff_unique_mem.2 ⟨‹_›, λ x hx, _⟩,
    { exact (eq_inv_of_mul_eq_one_left $ H hx hb).trans (inv_eq_of_mul_eq_one_left $ H ha hb) },
    { exact (eq_inv_of_mul_eq_one_right $ H ha hx).trans (inv_eq_of_mul_eq_one_right $ H ha hb) } },
  { rintro ⟨b, c, rfl, rfl, h⟩,
    rw [singleton_mul_singleton, h, singleton_one] }
end

/-- `set α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive "`set α` is a subtraction monoid under pointwise operations if `α` is."]
protected def division_monoid : division_monoid (set α) :=
{ mul_inv_rev := λ s t, by { simp_rw ←image_inv, exact image_image2_antidistrib mul_inv_rev },
  inv_eq_of_mul := λ s t h, begin
    obtain ⟨a, b, rfl, rfl, hab⟩ := set.mul_eq_one_iff.1 h,
    rw [inv_singleton, inv_eq_of_mul_eq_one_right hab],
  end,
  div_eq_mul_inv := λ s t,
    by { rw [←image_id (s / t), ←image_inv], exact image_image2_distrib_right div_eq_mul_inv },
  ..set.monoid, ..set.has_involutive_inv, ..set.has_div, ..set.has_zpow }

end division_monoid

/-- `set α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive subtraction_comm_monoid "`set α` is a commutative subtraction monoid under pointwise
operations if `α` is."]
protected def division_comm_monoid [division_comm_monoid α] : division_comm_monoid (set α) :=
{ ..set.division_monoid, ..set.comm_semigroup }

localized "attribute [instance] set.division_monoid set.subtraction_monoid set.division_comm_monoid
  set.subtraction_comm_monoid" in pointwise

section group
variables [group α] {s t : set α} {a b : α}

/-! Note that `set` is not a `group` because `s / s ≠ 1` in general. -/

@[simp, to_additive] lemma one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬ disjoint s t :=
by simp [not_disjoint_iff_nonempty_inter, mem_div, div_eq_one, set.nonempty]

@[to_additive] lemma not_one_mem_div_iff : (1 : α) ∉ s / t ↔ disjoint s t :=
one_mem_div_iff.not_left

alias not_one_mem_div_iff ↔ _ _root_.disjoint.one_not_mem_div_set

attribute [to_additive] disjoint.one_not_mem_div_set

@[to_additive] lemma nonempty.one_mem_div (h : s.nonempty) : (1 : α) ∈ s / s :=
let ⟨a, ha⟩ := h in mem_div.2 ⟨a, a, ha, ha, div_self' _⟩

@[simp, to_additive] lemma image_mul_left : ((*) a) '' t = ((*) a⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[simp, to_additive] lemma image_mul_right : (* b) '' t = (* b⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[to_additive] lemma image_mul_left' : (λ b, a⁻¹ * b) '' t = (λ b, a * b) ⁻¹' t := by simp
@[to_additive] lemma image_mul_right' : (* b⁻¹) '' t = (* b) ⁻¹' t := by simp

@[simp, to_additive] lemma preimage_mul_left_singleton : ((*) a) ⁻¹' {b} = {a⁻¹ * b} :=
by rw [← image_mul_left', image_singleton]

@[simp, to_additive] lemma preimage_mul_right_singleton : (* a) ⁻¹' {b} = {b * a⁻¹} :=
by rw [← image_mul_right', image_singleton]

@[simp, to_additive] lemma preimage_mul_left_one : ((*) a) ⁻¹' 1 = {a⁻¹} :=
by rw [← image_mul_left', image_one, mul_one]

@[simp, to_additive] lemma preimage_mul_right_one : (* b) ⁻¹' 1 = {b⁻¹} :=
by rw [← image_mul_right', image_one, one_mul]

@[to_additive] lemma preimage_mul_left_one' : (λ b, a⁻¹ * b) ⁻¹' 1 = {a} := by simp
@[to_additive] lemma preimage_mul_right_one' : (* b⁻¹) ⁻¹' 1 = {b} := by simp

@[simp, to_additive] lemma mul_univ (hs : s.nonempty) : s * (univ : set α) = univ :=
let ⟨a, ha⟩ := hs in eq_univ_of_forall $ λ b, ⟨a, a⁻¹ * b, ha, trivial, mul_inv_cancel_left _ _⟩

@[simp, to_additive] lemma univ_mul (ht : t.nonempty) : (univ : set α) * t = univ :=
let ⟨a, ha⟩ := ht in eq_univ_of_forall $ λ b, ⟨b * a⁻¹, a, trivial, ha, inv_mul_cancel_right _ _⟩

end group

/-! ### Translation/scaling of sets -/

section smul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in locale `pointwise`. -/
@[to_additive "The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in
locale `pointwise`."]
protected def has_smul_set [has_smul α β] : has_smul α (set β) := ⟨λ a, image ((•) a)⟩

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive "The pointwise scalar addition of sets `s +ᵥ t` is defined as
`{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def has_smul [has_smul α β] : has_smul (set α) (set β) := ⟨image2 (•)⟩

localized "attribute [instance] set.has_smul_set set.has_smul" in pointwise
localized "attribute [instance] set.has_vadd_set set.has_vadd" in pointwise

section has_smul
variables [has_smul α β] {s s₁ s₂ : set α} {t t₁ t₂ u : set β} {a : α} {b : β}

@[simp, to_additive] lemma image2_smul : image2 (•) s t = s • t := rfl

@[to_additive add_image_prod]
lemma image_smul_prod : (λ x : α × β, x.fst • x.snd) '' s ×ˢ t = s • t := image_prod _

@[to_additive] lemma mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b := iff.rfl

@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image2_of_mem

@[simp, to_additive] lemma empty_smul : (∅ : set α) • t = ∅ := image2_empty_left
@[simp, to_additive] lemma smul_empty : s • (∅ : set β) = ∅ := image2_empty_right
@[simp, to_additive] lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp, to_additive] lemma smul_nonempty : (s • t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
@[to_additive] lemma nonempty.smul : s.nonempty → t.nonempty → (s • t).nonempty := nonempty.image2
@[to_additive] lemma nonempty.of_smul_left : (s • t).nonempty → s.nonempty :=
nonempty.of_image2_left
@[to_additive] lemma nonempty.of_smul_right : (s • t).nonempty → t.nonempty :=
nonempty.of_image2_right
@[simp, to_additive] lemma smul_singleton : s • {b} = (• b) '' s := image2_singleton_right
@[simp, to_additive] lemma singleton_smul : ({a} : set α) • t = a • t := image2_singleton_left
@[simp, to_additive] lemma singleton_smul_singleton : ({a} : set α) • ({b} : set β) = {a • b} :=
image2_singleton

@[to_additive, mono] lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image2_subset
@[to_additive] lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image2_subset_left
@[to_additive] lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image2_subset_right
@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a • b ∈ u := image2_subset_iff

attribute [mono] vadd_subset_vadd

@[to_additive] lemma union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t := image2_union_left
@[to_additive] lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image2_union_right
@[to_additive] lemma inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t := image2_inter_subset_left
@[to_additive] lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
image2_inter_subset_right

@[to_additive] lemma Union_smul_left_image : (⋃ a ∈ s, a • t) = s • t := Union_image_left _
@[to_additive] lemma Union_smul_right_image : (⋃ a ∈ t, (• a) '' s) = s • t := Union_image_right _

@[to_additive] lemma Union_smul (s : ι → set α) (t : set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
image2_Union_left _ _ _
@[to_additive] lemma smul_Union (s : set α) (t : ι → set β) : s • (⋃ i, t i) = ⋃ i, s • t i :=
image2_Union_right _ _ _

@[to_additive]
lemma Union₂_smul (s : Π i, κ i → set α) (t : set β) : (⋃ i j, s i j) • t = ⋃ i j, s i j • t :=
image2_Union₂_left _ _ _

@[to_additive]
lemma smul_Union₂ (s : set α) (t : Π i, κ i → set β) : s • (⋃ i j, t i j) = ⋃ i j, s • t i j :=
image2_Union₂_right _ _ _

@[to_additive]
lemma Inter_smul_subset (s : ι → set α) (t : set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
image2_Inter_subset_left _ _ _

@[to_additive]
lemma smul_Inter_subset (s : set α) (t : ι → set β) : s • (⋂ i, t i) ⊆ ⋂ i, s • t i :=
image2_Inter_subset_right _ _ _

@[to_additive]
lemma Inter₂_smul_subset (s : Π i, κ i → set α) (t : set β) :
  (⋂ i j, s i j) • t ⊆ ⋂ i j, s i j • t :=
image2_Inter₂_subset_left _ _ _

@[to_additive]
lemma smul_Inter₂_subset (s : set α) (t : Π i, κ i → set β) :
  s • (⋂ i j, t i j) ⊆ ⋂ i j, s • t i j :=
image2_Inter₂_subset_right _ _ _

@[simp, to_additive] lemma bUnion_smul_set (s : set α) (t : set β) : (⋃ a ∈ s, a • t) = s • t :=
Union_image_left _

end has_smul

section has_smul_set
variables [has_smul α β] {s t t₁ t₂ : set β} {a : α} {b : β} {x y : β}

@[simp, to_additive] lemma image_smul : (λ x, a • x) '' t = a • t := rfl

@[to_additive] lemma mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x := iff.rfl

@[to_additive] lemma smul_mem_smul_set : b ∈ s → a • b ∈ a • s := mem_image_of_mem _

@[simp, to_additive] lemma smul_set_empty : a • (∅ : set β) = ∅ := image_empty _
@[simp, to_additive] lemma smul_set_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty
@[simp, to_additive] lemma smul_set_nonempty : (a • s).nonempty ↔ s.nonempty := nonempty_image_iff

@[simp, to_additive] lemma smul_set_singleton : a • ({b} : set β) = {a • b} := image_singleton

@[to_additive] lemma smul_set_mono : s ⊆ t → a • s ⊆ a • t := image_subset _
@[to_additive] lemma smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t := image_subset_iff

@[to_additive] lemma smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ := image_union _ _ _

@[to_additive]
lemma smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ (a • t₂) := image_inter_subset _ _ _

@[to_additive]
lemma smul_set_Union (a : α) (s : ι → set β) : a • (⋃ i, s i) = ⋃ i, a • s i := image_Union

@[to_additive]
lemma smul_set_Union₂ (a : α) (s : Π i, κ i → set β) : a • (⋃ i j, s i j) = ⋃ i j, a • s i j :=
image_Union₂ _ _

@[to_additive]
lemma smul_set_Inter_subset (a : α) (t : ι → set β) : a • (⋂ i, t i) ⊆ ⋂ i, a • t i :=
image_Inter_subset _ _

@[to_additive]
lemma smul_set_Inter₂_subset (a : α) (t : Π i, κ i → set β) :
  a • (⋂ i j, t i j) ⊆ ⋂ i j, a • t i j :=
image_Inter₂_subset _ _

@[to_additive] lemma nonempty.smul_set : s.nonempty → (a • s).nonempty := nonempty.image _

end has_smul_set

variables {s s₁ s₂ : set α} {t t₁ t₂ : set β} {a : α} {b : β}

@[simp, to_additive] lemma bUnion_op_smul_set [has_mul α] (s t : set α) :
  (⋃ a ∈ t, mul_opposite.op a • s) = s * t :=
Union_image_right _

@[to_additive]
lemma range_smul_range {ι κ : Type*} [has_smul α β] (b : ι → α) (c : κ → β) :
  range b • range c = range (λ p : ι × κ, b p.1 • c p.2) :=
ext $ λ x, ⟨λ ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩, ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
  λ ⟨⟨i, j⟩, h⟩, ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩

@[to_additive] lemma smul_set_range [has_smul α β] {f : ι → β} :
  a • range f = range (λ i, a • f i) := (range_comp _ _).symm

end smul

section vsub
variables [has_vsub α β] {s s₁ s₂ t t₁ t₂ : set β} {u : set α} {a : α} {b c : β}
include α

instance has_vsub : has_vsub (set α) (set β) := ⟨image2 (-ᵥ)⟩

@[simp] lemma image2_vsub : (image2 has_vsub.vsub s t : set α) = s -ᵥ t := rfl

lemma mem_vsub : a ∈ s -ᵥ t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x -ᵥ y = a := iff.rfl

lemma vsub_mem_vsub : b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t := mem_image2_of_mem

lemma image_vsub_prod : (λ x : β × β, x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t := image_prod _

@[simp] lemma empty_vsub (t : set β) : ∅ -ᵥ t = ∅ := image2_empty_left
@[simp] lemma vsub_empty (s : set β) : s -ᵥ ∅ = ∅ := image2_empty_right
@[simp] lemma vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp] lemma vsub_nonempty : (s -ᵥ t : set α).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
lemma nonempty.vsub : s.nonempty → t.nonempty → (s -ᵥ t : set α).nonempty := nonempty.image2
lemma nonempty.of_vsub_left : (s -ᵥ t :set α).nonempty → s.nonempty := nonempty.of_image2_left
lemma nonempty.of_vsub_right : (s -ᵥ t : set α).nonempty → t.nonempty := nonempty.of_image2_right
@[simp] lemma vsub_singleton (s : set β) (b : β) : s -ᵥ {b} = (-ᵥ b) '' s := image2_singleton_right
@[simp] lemma singleton_vsub (t : set β) (b : β) : {b} -ᵥ t = ((-ᵥ) b) '' t := image2_singleton_left
@[simp] lemma singleton_vsub_singleton : ({b} : set β) -ᵥ {c} = {b -ᵥ c} := image2_singleton

@[mono] lemma vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ := image2_subset
lemma vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ := image2_subset_left
lemma vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t := image2_subset_right
lemma vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x -ᵥ y ∈ u := image2_subset_iff
lemma vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t := vsub_subset_vsub h h

lemma union_vsub : (s₁ ∪ s₂) -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) := image2_union_left
lemma vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) := image2_union_right
lemma inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) := image2_inter_subset_left
lemma vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) := image2_inter_subset_right

lemma Union_vsub_left_image : (⋃ a ∈ s, ((-ᵥ) a) '' t) = s -ᵥ t := Union_image_left _
lemma Union_vsub_right_image : (⋃ a ∈ t, (-ᵥ a) '' s) = s -ᵥ t := Union_image_right _

lemma Union_vsub (s : ι → set β) (t : set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
image2_Union_left _ _ _
lemma vsub_Union (s : set β) (t : ι → set β) : s -ᵥ (⋃ i, t i) = ⋃ i, s -ᵥ t i :=
image2_Union_right _ _ _

lemma Union₂_vsub (s : Π i, κ i → set β) (t : set β) : (⋃ i j, s i j) -ᵥ t = ⋃ i j, s i j -ᵥ t :=
image2_Union₂_left _ _ _

lemma vsub_Union₂ (s : set β) (t : Π i, κ i → set β) : s -ᵥ (⋃ i j, t i j) = ⋃ i j, s -ᵥ t i j :=
image2_Union₂_right _ _ _

lemma Inter_vsub_subset (s : ι → set β) (t : set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
image2_Inter_subset_left _ _ _

lemma vsub_Inter_subset (s : set β) (t : ι → set β) : s -ᵥ (⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
image2_Inter_subset_right _ _ _

lemma Inter₂_vsub_subset (s : Π i, κ i → set β) (t : set β) :
  (⋂ i j, s i j) -ᵥ t ⊆ ⋂ i j, s i j -ᵥ t :=
image2_Inter₂_subset_left _ _ _

lemma vsub_Inter₂_subset (s : set β) (t : Π i, κ i → set β) :
  s -ᵥ (⋂ i j, t i j) ⊆ ⋂ i j, s -ᵥ t i j :=
image2_Inter₂_subset_right _ _ _

end vsub
end set
