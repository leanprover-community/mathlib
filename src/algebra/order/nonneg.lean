/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import algebra.order.archimedean
import order.lattice_intervals
import order.complete_lattice_intervals

/-!
# The type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Main declarations

* `{x : α // 0 ≤ x}` is a `canonically_linear_ordered_add_monoid` if `α` is a `linear_ordered_ring`.
* `{x : α // 0 ≤ x}` is a `linear_ordered_comm_group_with_zero` if `α` is a `linear_ordered_field`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing and element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `set.Ici` to this subtype.
-/

open set

variables {α : Type*}

namespace nonneg

/-- This instance uses data fields from `subtype.partial_order` to help type-class inference.
The `set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
instance order_bot [preorder α] {a : α} : order_bot {x : α // a ≤ x} :=
{ ..set.Ici.order_bot }

lemma bot_eq [preorder α] {a : α} : (⊥ : {x : α // a ≤ x}) = ⟨a, le_rfl⟩ := rfl

instance no_max_order [partial_order α] [no_max_order α] {a : α} : no_max_order {x : α // a ≤ x} :=
set.Ici.no_max_order

instance semilattice_inf [semilattice_inf α] {a : α} : semilattice_inf {x : α // a ≤ x} :=
set.Ici.semilattice_inf

instance densely_ordered [preorder α] [densely_ordered α] {a : α} :
  densely_ordered {x : α // a ≤ x} :=
show densely_ordered (Ici a), from set.densely_ordered

/-- If `Sup ∅ ≤ a` then `{x : α // a ≤ x}` is a `conditionally_complete_linear_order`. -/
@[reducible]
protected noncomputable def conditionally_complete_linear_order
  [conditionally_complete_linear_order α] {a : α} :
  conditionally_complete_linear_order {x : α // a ≤ x} :=
{ .. @ord_connected_subset_conditionally_complete_linear_order α (set.Ici a) _ ⟨⟨a, le_rfl⟩⟩ _ }

/-- If `Sup ∅ ≤ a` then `{x : α // a ≤ x}` is a `conditionally_complete_linear_order_bot`.

This instance uses data fields from `subtype.linear_order` to help type-class inference.
The `set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
@[reducible]
protected noncomputable def conditionally_complete_linear_order_bot
  [conditionally_complete_linear_order α] {a : α} (h : Sup ∅ ≤ a) :
  conditionally_complete_linear_order_bot {x : α // a ≤ x} :=
{ cSup_empty := (function.funext_iff.1
    (@subset_Sup_def α (set.Ici a) _ ⟨⟨a, le_rfl⟩⟩) ∅).trans $ subtype.eq $
      by { rw bot_eq, cases h.lt_or_eq with h2 h2, { simp [h2.not_le] }, simp [h2] },
  ..nonneg.order_bot,
  ..nonneg.conditionally_complete_linear_order }

instance inhabited [preorder α] {a : α} : inhabited {x : α // a ≤ x} :=
⟨⟨a, le_rfl⟩⟩

instance has_zero [has_zero α] [preorder α] : has_zero {x : α // 0 ≤ x} :=
⟨⟨0, le_rfl⟩⟩

@[simp, norm_cast]
protected lemma coe_zero [has_zero α] [preorder α] : ((0 : {x : α // 0 ≤ x}) : α) = 0 := rfl

@[simp] lemma mk_eq_zero [has_zero α] [preorder α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) = 0 ↔ x = 0 :=
subtype.ext_iff

instance has_add [add_zero_class α] [preorder α] [covariant_class α α (+) (≤)] :
  has_add {x : α // 0 ≤ x} :=
⟨λ x y, ⟨x + y, add_nonneg x.2 y.2⟩⟩

@[simp] lemma mk_add_mk [add_zero_class α] [preorder α] [covariant_class α α (+) (≤)] {x y : α}
  (hx : 0 ≤ x) (hy : 0 ≤ y) : (⟨x, hx⟩ : {x : α // 0 ≤ x}) + ⟨y, hy⟩ = ⟨x + y, add_nonneg hx hy⟩ :=
rfl

@[simp, norm_cast]
protected lemma coe_add [add_zero_class α] [preorder α] [covariant_class α α (+) (≤)]
  (a b : {x : α // 0 ≤ x}) : ((a + b : {x : α // 0 ≤ x}) : α) = a + b := rfl

instance has_nsmul [add_monoid α] [preorder α] [covariant_class α α (+) (≤)] :
  has_smul ℕ {x : α // 0 ≤ x} :=
⟨λ n x, ⟨n • x, nsmul_nonneg x.prop n⟩⟩

@[simp] lemma nsmul_mk [add_monoid α] [preorder α] [covariant_class α α (+) (≤)] (n : ℕ)
  {x : α} (hx : 0 ≤ x) : (n • ⟨x, hx⟩ : {x : α // 0 ≤ x}) = ⟨n • x, nsmul_nonneg hx n⟩ :=
rfl

@[simp, norm_cast]
protected lemma coe_nsmul [add_monoid α] [preorder α] [covariant_class α α (+) (≤)]
  (a : {x : α // 0 ≤ x}) (n : ℕ) : ((n • a : {x : α // 0 ≤ x}) : α) = n • a := rfl

instance ordered_add_comm_monoid [ordered_add_comm_monoid α] :
  ordered_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_add_comm_monoid _ rfl (λ x y, rfl) (λ _ _, rfl)

instance linear_ordered_add_comm_monoid [linear_ordered_add_comm_monoid α] :
  linear_ordered_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_add_comm_monoid _ rfl (λ x y, rfl) (λ _ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl)

instance ordered_cancel_add_comm_monoid [ordered_cancel_add_comm_monoid α] :
  ordered_cancel_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_cancel_add_comm_monoid _ rfl (λ x y, rfl) (λ _ _, rfl)

instance linear_ordered_cancel_add_comm_monoid [linear_ordered_cancel_add_comm_monoid α] :
  linear_ordered_cancel_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_cancel_add_comm_monoid _ rfl (λ x y, rfl) (λ _ _, rfl)
  (λ _ _, rfl) (λ _ _, rfl)

/-- Coercion `{x : α // 0 ≤ x} → α` as a `add_monoid_hom`. -/
def coe_add_monoid_hom [ordered_add_comm_monoid α] : {x : α // 0 ≤ x} →+ α :=
⟨coe, nonneg.coe_zero, nonneg.coe_add⟩

@[norm_cast]
lemma nsmul_coe [ordered_add_comm_monoid α] (n : ℕ) (r : {x : α // 0 ≤ x}) :
  ↑(n • r) = n • (r : α) :=
nonneg.coe_add_monoid_hom.map_nsmul _ _

instance archimedean [ordered_add_comm_monoid α] [archimedean α] : archimedean {x : α // 0 ≤ x} :=
⟨ assume x y pos_y,
  let ⟨n, hr⟩ := archimedean.arch (x : α) (pos_y : (0 : α) < y) in
  ⟨n, show (x : α) ≤ (n • y : {x : α // 0 ≤ x}), by simp [*, -nsmul_eq_mul, nsmul_coe]⟩ ⟩

instance has_one [ordered_semiring α] : has_one {x : α // 0 ≤ x} :=
{ one := ⟨1, zero_le_one⟩ }

@[simp, norm_cast]
protected lemma coe_one [ordered_semiring α] : ((1 : {x : α // 0 ≤ x}) : α) = 1 := rfl

@[simp] lemma mk_eq_one [ordered_semiring α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) = 1 ↔ x = 1 :=
subtype.ext_iff

instance has_mul [ordered_semiring α] : has_mul {x : α // 0 ≤ x} :=
{ mul := λ x y, ⟨x * y, mul_nonneg x.2 y.2⟩ }

@[simp, norm_cast]
protected lemma coe_mul [ordered_semiring α] (a b : {x : α // 0 ≤ x}) :
  ((a * b : {x : α // 0 ≤ x}) : α) = a * b := rfl

@[simp] lemma mk_mul_mk [ordered_semiring α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) * ⟨y, hy⟩ = ⟨x * y, mul_nonneg hx hy⟩ :=
rfl

instance add_monoid_with_one [ordered_semiring α] : add_monoid_with_one {x : α // 0 ≤ x} :=
{ nat_cast := λ n, ⟨n, nat.cast_nonneg n⟩,
  nat_cast_zero := by simp [nat.cast],
  nat_cast_succ := λ _, by simp [nat.cast]; refl,
  .. nonneg.has_one, .. nonneg.ordered_cancel_add_comm_monoid }

instance has_pow [ordered_semiring α] : has_pow {x : α // 0 ≤ x} ℕ :=
{ pow := λ x n, ⟨x ^ n, pow_nonneg x.2 n⟩ }

@[simp, norm_cast]
protected lemma coe_pow [ordered_semiring α] (a : {x : α // 0 ≤ x}) (n : ℕ) :
  ((a ^ n: {x : α // 0 ≤ x}) : α) = a ^ n := rfl

@[simp] lemma mk_pow [ordered_semiring α] {x : α} (hx : 0 ≤ x) (n : ℕ) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) ^ n = ⟨x ^ n, pow_nonneg hx n⟩ :=
rfl

instance ordered_semiring [ordered_semiring α] : ordered_semiring {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_semiring _
  rfl rfl (λ x y, rfl) (λ x y, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)

instance ordered_comm_semiring [ordered_comm_semiring α] : ordered_comm_semiring {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_comm_semiring _
  rfl rfl (λ x y, rfl) (λ x y, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)

-- These prevent noncomputable instances being found, as it does not require `linear_order` which
-- is frequently non-computable.
instance monoid_with_zero [ordered_semiring α] : monoid_with_zero {x : α // 0 ≤ x} :=
by apply_instance

instance comm_monoid_with_zero [ordered_comm_semiring α] : comm_monoid_with_zero {x : α // 0 ≤ x} :=
by apply_instance

instance nontrivial [linear_ordered_semiring α] : nontrivial {x : α // 0 ≤ x} :=
⟨ ⟨0, 1, λ h, zero_ne_one (congr_arg subtype.val h)⟩ ⟩

instance linear_ordered_semiring [linear_ordered_semiring α] :
  linear_ordered_semiring {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_semiring _
  rfl rfl (λ x y, rfl) (λ x y, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl)(λ _ _, rfl) (λ _ _, rfl)

instance linear_ordered_comm_monoid_with_zero [linear_ordered_comm_ring α] :
  linear_ordered_comm_monoid_with_zero {x : α // 0 ≤ x} :=
{ mul_le_mul_left := λ a b h c, mul_le_mul_of_nonneg_left h c.2,
  ..nonneg.linear_ordered_semiring,
  ..nonneg.ordered_comm_semiring }

/-- Coercion `{x : α // 0 ≤ x} → α` as a `ring_hom`. -/
def coe_ring_hom [ordered_semiring α] : {x : α // 0 ≤ x} →+* α :=
⟨coe, nonneg.coe_one, nonneg.coe_mul, nonneg.coe_zero, nonneg.coe_add⟩

@[simp, norm_cast]
protected lemma coe_nat_cast [ordered_semiring α] (n : ℕ) : ((↑n : {x : α // 0 ≤ x}) : α) = n :=
map_nat_cast (coe_ring_hom : {x : α // 0 ≤ x} →+* α) n

instance canonically_ordered_add_monoid [ordered_ring α] :
  canonically_ordered_add_monoid {x : α // 0 ≤ x} :=
{ le_self_add := λ a b, le_add_of_nonneg_right b.2,
  exists_add_of_le := λ a b h,
    ⟨⟨b - a, sub_nonneg_of_le h⟩, subtype.ext (add_sub_cancel'_right _ _).symm⟩,
  ..nonneg.ordered_add_comm_monoid,
  ..nonneg.order_bot }

instance canonically_ordered_comm_semiring [ordered_comm_ring α] [no_zero_divisors α] :
  canonically_ordered_comm_semiring {x : α // 0 ≤ x} :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by { rintro ⟨a, ha⟩ ⟨b, hb⟩, simp },
  ..nonneg.canonically_ordered_add_monoid,
  ..nonneg.ordered_comm_semiring }

instance canonically_linear_ordered_add_monoid [linear_ordered_ring α] :
  canonically_linear_ordered_add_monoid {x : α // 0 ≤ x} :=
{ ..subtype.linear_order _, ..nonneg.canonically_ordered_add_monoid }

section linear_ordered_semifield
variables [linear_ordered_semifield α] {x y : α}

instance has_inv : has_inv {x : α // 0 ≤ x} := ⟨λ x, ⟨x⁻¹, inv_nonneg.mpr x.2⟩⟩

@[simp, norm_cast]
protected lemma coe_inv (a : {x : α // 0 ≤ x}) : ((a⁻¹ : {x : α // 0 ≤ x}) : α) = a⁻¹ := rfl

@[simp] lemma inv_mk (hx : 0 ≤ x) : (⟨x, hx⟩ : {x : α // 0 ≤ x})⁻¹ = ⟨x⁻¹, inv_nonneg.mpr hx⟩ := rfl

instance has_div : has_div {x : α // 0 ≤ x} := ⟨λ x y, ⟨x / y, div_nonneg x.2 y.2⟩⟩

@[simp, norm_cast] protected lemma coe_div (a b : {x : α // 0 ≤ x}) :
  ((a / b : {x : α // 0 ≤ x}) : α) = a / b := rfl

@[simp] lemma mk_div_mk (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ := rfl

instance has_zpow : has_pow {x : α // 0 ≤ x} ℤ := ⟨λ a n, ⟨a ^ n, zpow_nonneg a.2 _⟩⟩

@[simp, norm_cast] protected lemma coe_zpow (a : {x : α // 0 ≤ x}) (n : ℤ) :
  ((a ^ n : {x : α // 0 ≤ x}) : α) = a ^ n := rfl

@[simp] lemma mk_zpow (hx : 0 ≤ x) (n : ℤ) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) ^ n = ⟨x ^ n, zpow_nonneg hx n⟩ := rfl

instance linear_ordered_semifield : linear_ordered_semifield {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_semifield _ nonneg.coe_zero nonneg.coe_one nonneg.coe_add
    nonneg.coe_mul nonneg.coe_inv nonneg.coe_div (λ _ _, rfl) nonneg.coe_pow nonneg.coe_zpow
    nonneg.coe_nat_cast (λ _ _, rfl) (λ _ _, rfl)

end linear_ordered_semifield

instance linear_ordered_comm_group_with_zero [linear_ordered_field α] :
  linear_ordered_comm_group_with_zero {x : α // 0 ≤ x} :=
{ inv_zero := by { ext, exact inv_zero },
  mul_inv_cancel := by { intros a ha, ext, refine mul_inv_cancel (mt (λ h, _) ha), ext, exact h },
  ..nonneg.nontrivial,
  ..nonneg.has_inv,
  ..nonneg.linear_ordered_comm_monoid_with_zero }

instance canonically_linear_ordered_semifield [linear_ordered_field α] :
  canonically_linear_ordered_semifield {x : α // 0 ≤ x} :=
{ ..nonneg.linear_ordered_semifield, ..nonneg.canonically_ordered_comm_semiring }

instance floor_semiring [ordered_semiring α] [floor_semiring α] : floor_semiring {r : α // 0 ≤ r} :=
{ floor := λ a, ⌊(a : α)⌋₊,
  ceil := λ a, ⌈(a : α)⌉₊,
  floor_of_neg := λ a ha, floor_semiring.floor_of_neg ha,
  gc_floor := λ a n ha, begin
    refine (floor_semiring.gc_floor (show 0 ≤ (a : α), from ha)).trans _,
    rw [←subtype.coe_le_coe, nonneg.coe_nat_cast]
  end,
  gc_ceil := λ a n, begin
    refine (floor_semiring.gc_ceil (a : α) n).trans _,
    rw [←subtype.coe_le_coe, nonneg.coe_nat_cast]
  end}

@[norm_cast] lemma nat_floor_coe [ordered_semiring α] [floor_semiring α] (a : {r : α // 0 ≤ r}) :
  ⌊(a : α)⌋₊ = ⌊a⌋₊ := rfl

@[norm_cast] lemma nat_ceil_coe [ordered_semiring α] [floor_semiring α] (a : {r : α // 0 ≤ r}) :
  ⌈(a : α)⌉₊ = ⌈a⌉₊  := rfl

section linear_order

variables [has_zero α] [linear_order α]

/-- The function `a ↦ max a 0` of type `α → {x : α // 0 ≤ x}`. -/
def to_nonneg (a : α) : {x : α // 0 ≤ x} :=
⟨max a 0, le_max_right _ _⟩

@[simp]
lemma coe_to_nonneg {a : α} : (to_nonneg a : α) = max a 0 := rfl

@[simp]
lemma to_nonneg_of_nonneg {a : α} (h : 0 ≤ a) : to_nonneg a = ⟨a, h⟩ :=
by simp [to_nonneg, h]

@[simp]
lemma to_nonneg_coe {a : {x : α // 0 ≤ x}} : to_nonneg (a : α) = a :=
by { cases a with a ha, exact to_nonneg_of_nonneg ha }

@[simp]
lemma to_nonneg_le {a : α} {b : {x : α // 0 ≤ x}} : to_nonneg a ≤ b ↔ a ≤ b :=
by { cases b with b hb, simp [to_nonneg, hb] }

@[simp]
lemma to_nonneg_lt {a : {x : α // 0 ≤ x}} {b : α} : a < to_nonneg b ↔ ↑a < b :=
by { cases a with a ha, simp [to_nonneg, ha.not_lt] }

instance has_sub [has_sub α] : has_sub {x : α // 0 ≤ x} :=
⟨λ x y, to_nonneg (x - y)⟩

@[simp] lemma mk_sub_mk [has_sub α] {x y : α}
  (hx : 0 ≤ x) (hy : 0 ≤ y) : (⟨x, hx⟩ : {x : α // 0 ≤ x}) - ⟨y, hy⟩ = to_nonneg (x - y) :=
rfl

end linear_order

instance has_ordered_sub [linear_ordered_ring α] : has_ordered_sub {x : α // 0 ≤ x} :=
⟨by { rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, simp only [sub_le_iff_le_add, subtype.mk_le_mk, mk_sub_mk,
  mk_add_mk, to_nonneg_le, subtype.coe_mk]}⟩

end nonneg
