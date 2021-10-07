/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import data.set.intervals.ord_connected
import algebra.order.sub
import order.lattice_intervals

/-!
## The type of nonnegative elements

This file proves properties about `{x : α // 0 ≤ x}`.
Note that we could also use `set.Ici (0 : α)`.
However, using the explicit subtype has a big advantage: when writing and element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confused the elaborator.
We prove that `{x : α // 0 ≤ x}` is a `canonically_linear_ordered_add_monoid` if `α` is a
`linear_ordered_ring`.
When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.
-/

open set

variables {α : Type*}

namespace nonneg

/-- -/
instance order_bot [order_bot α] {a : α} : order_bot {x : α // a ≤ x} :=
set.Ici.order_bot

instance no_top_order [partial_order α] [no_top_order α] {a : α} : no_top_order {x : α // a ≤ x} :=
set.Ici.no_top_order

instance has_zero [has_zero α] [preorder α] : has_zero {x : α // 0 ≤ x} :=
⟨⟨0, le_rfl⟩⟩

@[simp] protected lemma coe_zero [has_zero α] [preorder α] : ((0 : {x : α // 0 ≤ x}) : α) = 0 := rfl

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

instance ordered_add_comm_monoid [ordered_add_comm_monoid α] :
  ordered_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_add_comm_monoid (coe : {x : α // 0 ≤ x} → α) rfl (λ x y, rfl)

instance linear_ordered_add_comm_monoid [linear_ordered_add_comm_monoid α] :
  linear_ordered_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_add_comm_monoid (coe : {x : α // 0 ≤ x} → α) rfl (λ x y, rfl)

instance ordered_cancel_add_comm_monoid [ordered_cancel_add_comm_monoid α] :
  ordered_cancel_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_cancel_add_comm_monoid (coe : {x : α // 0 ≤ x} → α) rfl (λ x y, rfl)

instance linear_ordered_cancel_add_comm_monoid [linear_ordered_cancel_add_comm_monoid α] :
  linear_ordered_cancel_add_comm_monoid {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_cancel_add_comm_monoid
  (coe : {x : α // 0 ≤ x} → α) rfl (λ x y, rfl)

instance has_one [ordered_semiring α] : has_one {x : α // 0 ≤ x} :=
{ one := ⟨1, zero_le_one⟩ }

@[simp] protected lemma coe_one [ordered_semiring α] : ((1 : {x : α // 0 ≤ x}) : α) = 1 := rfl

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

instance ordered_semiring [ordered_semiring α] : ordered_semiring {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_semiring
  (coe : {x : α // 0 ≤ x} → α) rfl rfl (λ x y, rfl) (λ x y, rfl)

instance ordered_comm_semiring [ordered_comm_semiring α] : ordered_comm_semiring {x : α // 0 ≤ x} :=
subtype.coe_injective.ordered_comm_semiring
  (coe : {x : α // 0 ≤ x} → α) rfl rfl (λ x y, rfl) (λ x y, rfl)

instance nontrivial [linear_ordered_semiring α] : nontrivial {x : α // 0 ≤ x} :=
⟨ ⟨0, 1, λ h, zero_ne_one (congr_arg subtype.val h)⟩ ⟩

instance linear_ordered_semiring [linear_ordered_semiring α] :
  linear_ordered_semiring {x : α // 0 ≤ x} :=
subtype.coe_injective.linear_ordered_semiring
  (coe : {x : α // 0 ≤ x} → α) rfl rfl (λ x y, rfl) (λ x y, rfl)

instance has_inv [linear_ordered_field α] : has_inv {x : α // 0 ≤ x} :=
{ inv := λ x, ⟨x⁻¹, inv_nonneg.mpr x.2⟩ }

@[simp, norm_cast]
protected lemma coe_inv [linear_ordered_field α] (a : {x : α // 0 ≤ x}) :
  ((a⁻¹ : {x : α // 0 ≤ x}) : α) = a⁻¹ := rfl

@[simp] lemma inv_mk [linear_ordered_field α] {x : α} (hx : 0 ≤ x) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x})⁻¹ = ⟨x⁻¹, inv_nonneg.mpr hx⟩ :=
rfl

instance has_div [linear_ordered_field α] : has_div {x : α // 0 ≤ x} :=
{ div := λ x y, ⟨x / y, div_nonneg x.2 y.2⟩ }

@[simp, norm_cast]
protected lemma coe_div [linear_ordered_field α] (a b : {x : α // 0 ≤ x}) :
  ((a / b : {x : α // 0 ≤ x}) : α) = a / b := rfl

@[simp] lemma mk_div_mk [linear_ordered_field α] {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) :
  (⟨x, hx⟩ : {x : α // 0 ≤ x}) / ⟨y, hy⟩ = ⟨x / y, div_nonneg hx hy⟩ :=
rfl

instance canonically_ordered_add_monoid [ordered_ring α] :
  canonically_ordered_add_monoid {x : α // 0 ≤ x} :=
{ le_iff_exists_add     := λ ⟨a, ha⟩ ⟨b, hb⟩,
    by simpa only [mk_add_mk, set_coe.exists, subtype.mk_eq_mk] using le_iff_exists_nonneg_add a b,
  ..nonneg.ordered_add_comm_monoid,
  ..nonneg.order_bot }

instance canonically_ordered_comm_semiring [ordered_comm_ring α] [no_zero_divisors α] :
  canonically_ordered_comm_semiring {x : α // 0 ≤ x} :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by { rintro ⟨a, ha⟩ ⟨b, hb⟩, simp },
  .. set.Ici.canonically_ordered_add_monoid,
  .. set.Ici.ordered_comm_semiring }

instance canonically_linear_ordered_add_monoid [linear_ordered_ring α] :
  canonically_linear_ordered_add_monoid {x : α // 0 ≤ x} :=
{ ..subtype.linear_order _, ..set.Ici.canonically_ordered_add_monoid }

section linear_order

variables [has_zero α] [linear_order α]

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

instance [has_sub α] : has_sub {x : α // 0 ≤ x} :=
⟨λ x y, to_nonneg (x - y)⟩

@[simp] lemma mk_sub_mk [has_sub α] {x y : α}
  (hx : 0 ≤ x) (hy : 0 ≤ y) : (⟨x, hx⟩ : {x : α // 0 ≤ x}) - ⟨y, hy⟩ = to_nonneg (x - y) :=
rfl

end linear_order

end nonneg

instance [linear_ordered_ring α] : has_ordered_sub {x : α // 0 ≤ x} :=
⟨by { rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, simp [sub_le_iff_le_add] }⟩
