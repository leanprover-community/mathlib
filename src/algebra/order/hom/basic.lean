/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.hom.group
import algebra.order.with_zero
import order.hom.basic
import tactic.positivity

/-!
# Algebraic order homomorphism classes

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

* `nonneg_hom_class`: Homs are nonnegative: `∀ f a, 0 ≤ f a`
* `subadditive_hom_class`: Homs are subadditive: `∀ f a b, f (a + b) ≤ f a + f b`
* `submultiplicative_hom_class`: Homs are submultiplicative: `∀ f a b, f (a * b) ≤ f a * f b`
* `mul_le_add_hom_class`: `∀ f a b, f (a * b) ≤ f a + f b`
-/

set_option old_structure_cmd true

open function

variables {F α β γ δ : Type*}

/-- `nonneg_hom_class F α β` states that `F` is a type of nonnegative morphisms. -/
class nonneg_hom_class (F : Type*) (α β : out_param $ Type*) [has_zero β] [has_le β]
  extends fun_like F α (λ _, β) :=
(map_nonneg (f : F) : ∀ a, 0 ≤ f a)

/-- `subadditive_hom_class F α β` states that `F` is a type of subadditive morphisms. -/
class subadditive_hom_class (F : Type*) (α β : out_param $ Type*) [has_add α] [has_add β] [has_le β]
  extends fun_like F α (λ _, β) :=
(map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b)

/-- `submultiplicative_hom_class F α β` states that `F` is a type of submultiplicative morphisms. -/
@[to_additive subadditive_hom_class]
class submultiplicative_hom_class (F : Type*) (α β : out_param $ Type*) [has_mul α] [has_mul β]
  [has_le β] extends fun_like F α (λ _, β) :=
(map_mul_le_mul (f : F) : ∀ a b, f (a * b) ≤ f a * f b)

/-- `map_add_le_class F α β` states that `F` is a type of subadditive morphisms. -/
@[to_additive subadditive_hom_class]
class mul_le_add_hom_class (F : Type*) (α β : out_param $ Type*) [has_mul α] [has_add β] [has_le β]
  extends fun_like F α (λ _, β) :=
(map_mul_le_add (f : F) : ∀ a b, f (a * b) ≤ f a + f b)

export nonneg_hom_class (map_nonneg)
export subadditive_hom_class (map_add_le_add)
export submultiplicative_hom_class (map_mul_le_mul)
export mul_le_add_hom_class (map_mul_le_add)

attribute [simp] map_nonneg

@[to_additive] lemma le_map_mul_map_div [group α] [comm_semigroup β] [has_le β]
  [submultiplicative_hom_class F α β] (f : F) (a b : α) : f a ≤ f b * f (a / b) :=
by simpa only [mul_comm, div_mul_cancel'] using map_mul_le_mul f (a / b) b

@[to_additive] lemma le_map_add_map_div [group α] [add_comm_semigroup β] [has_le β]
  [mul_le_add_hom_class F α β] (f : F) (a b : α) : f a ≤ f b + f (a / b) :=
by simpa only [add_comm, div_mul_cancel'] using map_mul_le_add f (a / b) b

@[to_additive]
lemma le_map_div_mul_map_div [group α] [comm_semigroup β] [has_le β]
  [submultiplicative_hom_class F α β] (f : F) (a b c: α) : f (a / c) ≤ f (a / b) * f (b / c) :=
by simpa only [div_mul_div_cancel'] using map_mul_le_mul f (a / b) (b / c)

@[to_additive]
lemma le_map_div_add_map_div [group α] [add_comm_semigroup β] [has_le β]
  [mul_le_add_hom_class F α β] (f : F) (a b c: α) : f (a / c) ≤ f (a / b) + f (b / c) :=
by simpa only [div_mul_div_cancel'] using map_mul_le_add f (a / b) (b / c)

namespace tactic
open positivity

/-- Extension for the `positivity` tactic: nonnegative maps take nonnegative values. -/
@[positivity]
meta def positivity_map : expr → tactic strictness
| (expr.app `(⇑%%f) `(%%a)) := nonnegative <$> mk_app ``map_nonneg [f, a]
| _ := failed

end tactic
