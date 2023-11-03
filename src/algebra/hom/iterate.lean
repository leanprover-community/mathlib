/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.group_power.lemmas
import group_theory.group_action.opposite

/-!
# Iterates of monoid and ring homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Iterate of a monoid/ring homomorphism is a monoid/ring homomorphism but it has a wrong type, so Lean
can't apply lemmas like `monoid_hom.map_one` to `f^[n] 1`. Though it is possible to define
a monoid structure on the endomorphisms, quite often we do not want to convert from
`M →* M` to `monoid.End M` and from `f^[n]` to `f^n` just to apply a simple lemma.

So, we restate standard `*_hom.map_*` lemmas under names `*_hom.iterate_map_*`.

We also prove formulas for iterates of add/mul left/right.

## TODO

Redefine `npow` in `monoid_hom.End`, `module.End`, etc using `nat.iterate`.

## Tags

homomorphism, iterate
-/

open function

variables {M : Type*} {N : Type*} {G : Type*} {H : Type*}

/-- An auxiliary lemma that can be used to prove `⇑(f ^ n) = (⇑f^[n])`. -/
lemma hom_coe_pow {F : Type*} [monoid F] (c : F → M → M) (h1 : c 1 = id)
  (hmul : ∀ f g, c (f * g) = c f ∘ c g) (f : F) : ∀ n, c (f ^ n) = (c f^[n])
| 0 := by { rw [pow_zero, h1], refl }
| (n + 1) := by rw [pow_succ, iterate_succ', hmul, hom_coe_pow]

namespace monoid_hom

section

variables [mul_one_class M] [mul_one_class N]

@[simp, to_additive]
theorem iterate_map_one (f : M →* M) (n : ℕ) : f^[n] 1 = 1 :=
iterate_fixed f.map_one n

@[simp, to_additive]
theorem iterate_map_mul (f : M →* M) (n : ℕ) (x y) :
  f^[n] (x * y) = (f^[n] x) * (f^[n] y) :=
semiconj₂.iterate f.map_mul n x y

end

variables [monoid M] [monoid N] [group G] [group H]

@[simp, to_additive]
theorem iterate_map_inv (f : G →* G) (n : ℕ) (x) :
  f^[n] (x⁻¹) = (f^[n] x)⁻¹ :=
commute.iterate_left f.map_inv n x

@[simp, to_additive]
theorem iterate_map_div (f : G →* G) (n : ℕ) (x y) :
  f^[n] (x / y) = (f^[n] x) / (f^[n] y) :=
semiconj₂.iterate f.map_div n x y

theorem iterate_map_pow (f : M →* M) (n : ℕ) (a) (m : ℕ) : f^[n] (a^m) = (f^[n] a)^m :=
commute.iterate_left (λ x, f.map_pow x m) n a

theorem iterate_map_zpow (f : G →* G) (n : ℕ) (a) (m : ℤ) : f^[n] (a^m) = (f^[n] a)^m :=
commute.iterate_left (λ x, f.map_zpow x m) n a

lemma coe_pow {M} [comm_monoid M] (f : monoid.End M) (n : ℕ) : ⇑(f^n) = (f^[n]) :=
hom_coe_pow _ rfl (λ f g, rfl) _ _

end monoid_hom

lemma monoid.End.coe_pow {M} [monoid M] (f : monoid.End M) (n : ℕ) : ⇑(f^n) = (f^[n]) :=
hom_coe_pow _ rfl (λ f g, rfl) _ _

-- we define these manually so that we can pick a better argument order
namespace add_monoid_hom
variables [add_monoid M] [add_group G]

theorem iterate_map_smul (f : M →+ M) (n m : ℕ) (x : M) :
  f^[n] (m • x) = m • (f^[n] x) :=
f.to_multiplicative.iterate_map_pow n x m

attribute [to_additive, to_additive_reorder 5] monoid_hom.iterate_map_pow

theorem iterate_map_zsmul (f : G →+ G) (n : ℕ) (m : ℤ) (x : G) :
  f^[n] (m • x) = m • (f^[n] x) :=
f.to_multiplicative.iterate_map_zpow n x m

attribute [to_additive, to_additive_reorder 5] monoid_hom.iterate_map_zpow

end add_monoid_hom

lemma add_monoid.End.coe_pow {A} [add_monoid A] (f : add_monoid.End A) (n : ℕ) : ⇑(f^n) = (f^[n]) :=
hom_coe_pow _ rfl (λ f g, rfl) _ _

namespace ring_hom

section semiring

variables {R : Type*} [semiring R] (f : R →+* R) (n : ℕ) (x y : R)

lemma coe_pow (n : ℕ) : ⇑(f^n) = (f^[n]) :=
hom_coe_pow _ rfl (λ f g, rfl) f n

theorem iterate_map_one : f^[n] 1 = 1 := f.to_monoid_hom.iterate_map_one n

theorem iterate_map_zero : f^[n] 0 = 0 := f.to_add_monoid_hom.iterate_map_zero n

theorem iterate_map_add : f^[n] (x + y) = (f^[n] x) + (f^[n] y) :=
f.to_add_monoid_hom.iterate_map_add n x y

theorem iterate_map_mul : f^[n] (x * y) = (f^[n] x) * (f^[n] y) :=
f.to_monoid_hom.iterate_map_mul n x y

theorem iterate_map_pow (a) (n m : ℕ) : f^[n] (a^m) = (f^[n] a)^m :=
f.to_monoid_hom.iterate_map_pow n a m

theorem iterate_map_smul (n m : ℕ) (x : R) :
  f^[n] (m • x) = m • (f^[n] x) :=
f.to_add_monoid_hom.iterate_map_smul n m x

end semiring

variables {R : Type*} [ring R] (f : R →+* R) (n : ℕ) (x y : R)

theorem iterate_map_sub : f^[n] (x - y) = (f^[n] x) - (f^[n] y) :=
f.to_add_monoid_hom.iterate_map_sub n x y

theorem iterate_map_neg : f^[n] (-x) = -(f^[n] x) :=
f.to_add_monoid_hom.iterate_map_neg n x

theorem iterate_map_zsmul (n : ℕ) (m : ℤ) (x : R) :
  f^[n] (m • x) = m • (f^[n] x) :=
f.to_add_monoid_hom.iterate_map_zsmul n m x

end ring_hom

--what should be the namespace for this section?
section monoid

variables [monoid G] (a : G) (n : ℕ)

@[simp, to_additive] lemma smul_iterate [mul_action G H] :
  ((•) a : H → H)^[n] = (•) (a^n) :=
funext (λ b, nat.rec_on n (by rw [iterate_zero, id.def, pow_zero, one_smul])
  (λ n ih, by rw [iterate_succ', comp_app, ih, pow_succ, mul_smul]))

@[simp, to_additive] lemma mul_left_iterate : ((*) a)^[n] = (*) (a^n) :=
smul_iterate a n

@[simp, to_additive] lemma mul_right_iterate : (* a)^[n] = (* a ^ n) :=
smul_iterate (mul_opposite.op a) n

@[to_additive]
lemma mul_right_iterate_apply_one : (* a)^[n] 1 = a ^ n :=
by simp [mul_right_iterate]

@[simp, to_additive]
lemma pow_iterate (n : ℕ) (j : ℕ) : ((λ (x : G), x^n)^[j]) = λ x, x^(n^j) :=
begin
  letI : mul_action ℕ G :=
  { smul := λ n g, g^n,
    one_smul := pow_one,
    mul_smul := λ m n g, pow_mul' g m n },
  exact smul_iterate n j,
end

end monoid

section group

variables [group G]

@[simp, to_additive]
lemma zpow_iterate (n : ℤ) (j : ℕ) : ((λ (x : G), x^n)^[j]) = λ x, x^(n^j) :=
begin
  letI : mul_action ℤ G :=
  { smul := λ n g, g^n,
    one_smul := zpow_one,
    mul_smul := λ m n g, zpow_mul' g m n },
  exact smul_iterate n j,
end

end group

section semigroup

variables [semigroup G] {a b c : G}

@[to_additive]
lemma semiconj_by.function_semiconj_mul_left (h : semiconj_by a b c) :
  function.semiconj ((*)a) ((*)b) ((*)c) :=
λ j, by rw [← mul_assoc, h.eq, mul_assoc]

@[to_additive]
lemma commute.function_commute_mul_left (h : commute a b) :
  function.commute ((*)a) ((*)b) :=
semiconj_by.function_semiconj_mul_left h

@[to_additive]
lemma semiconj_by.function_semiconj_mul_right_swap (h : semiconj_by a b c) :
  function.semiconj (*a) (*c) (*b) :=
λ j, by simp_rw [mul_assoc, ← h.eq]

@[to_additive]
lemma commute.function_commute_mul_right (h : commute a b) :
  function.commute (*a) (*b) :=
semiconj_by.function_semiconj_mul_right_swap h

end semigroup
