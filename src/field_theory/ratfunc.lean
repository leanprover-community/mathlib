/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.euclidean_domain
import ring_theory.localization

/-!
# The field of rational functions

This file defines the field `ratfunc K` of rational functions over a field `K`,
and shows it is the field of fractions of `polynomial K`.

## Main definitions

Working with rational functions as polynomials:
 - `ratfunc.field` provides a field structure
 - `ratfunc.C` is the constant polynomial
 - `ratfunc.X` is the indeterminate
 - `ratfunc.eval` evaluates a rational function given a value for the indeterminate
Use `algebra_map` to map polynomials to rational functions and `is_fraction_ring.alg_equiv`
to map other fields of fractions of `polynomial K` to `ratfunc K`.

Working with rational functions as fractions:
 - `ratfunc.num` and `ratfunc.denom` give the numerator and denominator.
   These values are chosen to be coprime and such that `ratfunc.denom` is monic.

We also have a set of recursion and induction principles:
 - `ratfunc.lift_on`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
   if `f` is well-defined in the sense that `p/q = p'/q' → f p q = f p' q'`.
 - `ratfunc.lift_on'`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
   if `f` is well-defined in the sense that `f (a * p) (a * q) = f p' q'`.
 - `ratfunc.induction_on`: if `P` holds on `p / q` for all polynomials `p q`, then `P` holds on all
   rational functions

## Implementation notes

To provide good API encapsulation and speed up unification problems,
`ratfunc` is defined as a structure, and all operations are `@[irreducible] def`s

We need a couple of maps to set up the `field` and `is_fraction_ring` structure,
namely `ratfunc.of_fraction_ring`, `ratfunc.to_fraction_ring`, `ratfunc.mk` and
`ratfunc.aux_equiv`.
All these maps get `simp`ed to bundled morphisms like `algebra_map (polynomial K) (ratfunc K)`
and `is_localization.alg_equiv`.
-/

noncomputable theory
open_locale classical
open_locale non_zero_divisors

universes u v

variables (K : Type u) [hring : comm_ring K] [hdomain : is_domain K]
include hring

/-- `ratfunc K` is `K(x)`, the field of rational functions over `K`.

The inclusion of polynomials into `ratfunc` is `algebra_map (polynomial K) (ratfunc K)`,
the maps between `ratfunc K` and another field of fractions of `polynomial K`,
especially `fraction_ring (polynomial K)`, are given by `is_localization.algebra_equiv`.
-/
structure ratfunc : Type u := of_fraction_ring ::
(to_fraction_ring : fraction_ring (polynomial K))

namespace ratfunc

variables {K}

section rec

/-! ### Constructing `ratfunc`s and their induction principles -/

lemma of_fraction_ring_injective : function.injective (of_fraction_ring : _ → ratfunc K) :=
λ x y, of_fraction_ring.inj

lemma to_fraction_ring_injective :
  function.injective (to_fraction_ring : _ → fraction_ring (polynomial K))
| ⟨x⟩ ⟨y⟩ rfl := rfl

include hdomain

/-- `ratfunc.mk (p q : polynomial K)` is `p / q` as a rational function.

If `q = 0`, then `mk` returns 0.

This is an auxiliary definition used to define an `algebra` structure on `ratfunc`;
the `simp` normal form of `mk p q` is `algebra_map _ _ p / algebra_map _ _ q`.
-/
@[irreducible] protected def mk (p q : polynomial K) : ratfunc K :=
of_fraction_ring (algebra_map _ _ p / algebra_map _ _ q)

lemma mk_eq_div' (p q : polynomial K) :
  ratfunc.mk p q = of_fraction_ring (algebra_map _ _ p / algebra_map _ _ q) :=
by unfold ratfunc.mk

lemma mk_zero (p : polynomial K) : ratfunc.mk p 0 = of_fraction_ring 0 :=
by rw [mk_eq_div', ring_hom.map_zero, div_zero]

lemma mk_coe_def (p : polynomial K) (q : (polynomial K)⁰) :
  ratfunc.mk p q = of_fraction_ring (is_localization.mk' _ p q) :=
by simp only [mk_eq_div', ← localization.mk_eq_mk', fraction_ring.mk_eq_div]

lemma mk_def_of_mem (p : polynomial K) {q} (hq : q ∈ (polynomial K)⁰) :
  ratfunc.mk p q = of_fraction_ring (is_localization.mk' _ p ⟨q, hq⟩) :=
by simp only [← mk_coe_def, set_like.coe_mk]

lemma mk_def_of_ne (p : polynomial K) {q : polynomial K} (hq : q ≠ 0) :
  ratfunc.mk p q = of_fraction_ring (is_localization.mk' _ p
    ⟨q, mem_non_zero_divisors_iff_ne_zero.mpr hq⟩) :=
mk_def_of_mem p _

lemma mk_eq_localization_mk (p : polynomial K) {q : polynomial K} (hq : q ≠ 0) :
  ratfunc.mk p q = of_fraction_ring (localization.mk p
    ⟨q, mem_non_zero_divisors_iff_ne_zero.mpr hq⟩) :=
by rw [mk_def_of_ne, localization.mk_eq_mk']

lemma mk_one' (p : polynomial K) : ratfunc.mk p 1 = of_fraction_ring (algebra_map _ _ p) :=
by rw [← is_localization.mk'_one (fraction_ring (polynomial K)) p, ← mk_coe_def, submonoid.coe_one]

lemma mk_eq_mk {p q p' q' : polynomial K} (hq : q ≠ 0) (hq' : q' ≠ 0) :
  ratfunc.mk p q = ratfunc.mk p' q' ↔ p * q' = p' * q :=
by rw [mk_def_of_ne _ hq, mk_def_of_ne _ hq', of_fraction_ring_injective.eq_iff,
       is_localization.mk'_eq_iff_eq, set_like.coe_mk, set_like.coe_mk,
       (is_fraction_ring.injective (polynomial K) (fraction_ring (polynomial K))).eq_iff]

/-- Non-dependent recursion principle for `ratfunc K`: if `f p q : P` for all `p q`,
such that `p * q' = p' * q` implies `f p q = f p' q'`, then we can find a value of `P`
for all elements of `ratfunc K` by setting `lift_on (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on` assume `f p 0 = f 0 1`.
-/
@[irreducible] protected def lift_on {P : Sort v} (x : ratfunc K)
  (f : ∀ (p q : polynomial K), P)
  (H : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), p * q' = p' * q → f p q = f p' q') :
  P :=
localization.lift_on (to_fraction_ring x) (λ p q, f p q) (λ p p' q q' h, H
  (mem_non_zero_divisors_iff_ne_zero.mp q.2)
  (mem_non_zero_divisors_iff_ne_zero.mp q'.2)
  (let ⟨⟨c, hc⟩, mul_eq⟩ := (localization.r_iff_exists).mp h in
    (mul_eq_mul_right_iff.mp mul_eq).resolve_right (mem_non_zero_divisors_iff_ne_zero.mp hc)))

lemma lift_on_mk {P : Sort v} (p q : polynomial K)
  (f : ∀ (p q : polynomial K), P) (f0 : ∀ p, f p 0 = f 0 1)
  (H : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), p * q' = p' * q → f p q = f p' q') :
  (ratfunc.mk p q).lift_on f @H = f p q :=
begin
  unfold ratfunc.lift_on,
  by_cases hq : q = 0,
  { subst hq,
    simp only [mk_zero, f0, ← localization.mk_zero 1, localization.lift_on_mk,
               submonoid.coe_one] },
  { simp only [mk_eq_localization_mk _ hq, localization.lift_on_mk, set_like.coe_mk] }
end

/-- Non-dependent recursion principle for `ratfunc K`: if `f p q : P` for all `p q`,
such that `f (a * p) (a * q) = f p q`, then we can find a value of `P`
for all elements of `ratfunc K` by setting `lift_on' (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on'` assume `f p 0 = f 0 1`.
-/
@[irreducible] protected def lift_on' {P : Sort v} (x : ratfunc K)
  (f : ∀ (p q : polynomial K), P)
  (H : ∀ {p q a} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q) :
  P :=
x.lift_on f (λ p q p' q' hq hq' h, begin
  have H0 : f 0 q = f 0 q',
  { calc f 0 q = f (q' * 0) (q' * q) : (H hq hq').symm
           ... = f (q * 0) (q * q') : by rw [mul_zero, mul_zero, mul_comm]
           ... = f 0 q' : H hq' hq },
  by_cases hp : p = 0,
  { simp [hp, hq] at ⊢ h, rw [h, H0] },
  by_cases hp' : p' = 0,
  { simp [hp', hq'] at ⊢ h, rw [h, H0] },
  calc f p q = f (p' * p) (p' * q) : (H hq hp').symm
         ... = f (p * p') (p * q') : by rw [mul_comm p p', h]
         ... = f p' q' : H hq' hp
end)

lemma lift_on'_mk {P : Sort v} (p q : polynomial K)
  (f : ∀ (p q : polynomial K), P) (f0 : ∀ p, f p 0 = f 0 1)
  (H : ∀ {p q a} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q) :
  (ratfunc.mk p q).lift_on' f @H = f p q :=
by rw [ratfunc.lift_on', ratfunc.lift_on_mk _ _ _ f0]

/-- Induction principle for `ratfunc K`: if `f p q : P (ratfunc.mk p q)` for all `p q`,
then `P` holds on all elements of `ratfunc K`.

See also `induction_on`, which is a recursion principle defined in terms of `algebra_map`.
-/
@[irreducible] protected lemma induction_on' {P : ratfunc K → Prop} :
  Π (x : ratfunc K) (f : ∀ (p q : polynomial K) (hq : q ≠ 0), P (ratfunc.mk p q)), P x
| ⟨x⟩ f := localization.induction_on x
  (λ ⟨p, q⟩, by simpa only [mk_coe_def, localization.mk_eq_mk'] using f p q
    (mem_non_zero_divisors_iff_ne_zero.mp q.2))

end rec

section field

/-! ### Defining the field structure -/

/-- The zero rational function. -/
@[irreducible] protected def zero : ratfunc K := ⟨0⟩
instance : has_zero (ratfunc K) := ⟨ratfunc.zero⟩
lemma of_fraction_ring_zero : (of_fraction_ring 0 : ratfunc K) = 0 :=
by unfold has_zero.zero ratfunc.zero

/-- Addition of rational functions. -/
@[irreducible] protected def add : ratfunc K → ratfunc K → ratfunc K
| ⟨p⟩ ⟨q⟩ := ⟨p + q⟩
instance : has_add (ratfunc K) := ⟨ratfunc.add⟩
lemma of_fraction_ring_add (p q : fraction_ring (polynomial K)) :
  of_fraction_ring (p + q) = of_fraction_ring p + of_fraction_ring q :=
by unfold has_add.add ratfunc.add

/-- Subtraction of rational functions. -/
@[irreducible] protected def sub : ratfunc K → ratfunc K → ratfunc K
| ⟨p⟩ ⟨q⟩ := ⟨p - q⟩
instance : has_sub (ratfunc K) := ⟨ratfunc.sub⟩
lemma of_fraction_ring_sub (p q : fraction_ring (polynomial K)) :
  of_fraction_ring (p - q) = of_fraction_ring p - of_fraction_ring q :=
by unfold has_sub.sub ratfunc.sub

/-- Additive inverse of a rational function. -/
@[irreducible] protected def neg : ratfunc K → ratfunc K
| ⟨p⟩ := ⟨-p⟩
instance : has_neg (ratfunc K) := ⟨ratfunc.neg⟩
lemma of_fraction_ring_neg (p : fraction_ring (polynomial K)) :
  of_fraction_ring (-p) = - of_fraction_ring p :=
by unfold has_neg.neg ratfunc.neg

/-- The multiplicative unit of rational functions. -/
@[irreducible] protected def one : ratfunc K := ⟨1⟩
instance : has_one (ratfunc K) := ⟨ratfunc.one⟩
lemma of_fraction_ring_one : (of_fraction_ring 1 : ratfunc K) = 1 :=
by unfold has_one.one ratfunc.one

/-- Multiplication of rational functions. -/
@[irreducible] protected def mul : ratfunc K → ratfunc K → ratfunc K
| ⟨p⟩ ⟨q⟩ := ⟨p * q⟩
instance : has_mul (ratfunc K) := ⟨ratfunc.mul⟩
lemma of_fraction_ring_mul (p q : fraction_ring (polynomial K)) :
  of_fraction_ring (p * q) = of_fraction_ring p * of_fraction_ring q :=
by unfold has_mul.mul ratfunc.mul

include hdomain

/-- Division of rational functions. -/
@[irreducible] protected def div : ratfunc K → ratfunc K → ratfunc K
| ⟨p⟩ ⟨q⟩ := ⟨p / q⟩
instance : has_div (ratfunc K) := ⟨ratfunc.div⟩
lemma of_fraction_ring_div (p q : fraction_ring (polynomial K)) :
  of_fraction_ring (p / q) = of_fraction_ring p / of_fraction_ring q :=
by unfold has_div.div ratfunc.div

/-- Multiplicative inverse of a rational function. -/
@[irreducible] protected def inv : ratfunc K → ratfunc K
| ⟨p⟩ := ⟨p⁻¹⟩
instance : has_inv (ratfunc K) := ⟨ratfunc.inv⟩
lemma of_fraction_ring_inv (p : fraction_ring (polynomial K)) :
  of_fraction_ring (p⁻¹) = (of_fraction_ring p)⁻¹ :=
by unfold has_inv.inv ratfunc.inv

-- Auxiliary lemma for the `field` instance
lemma mul_inv_cancel : ∀ {p : ratfunc K} (hp : p ≠ 0), p * p⁻¹ = 1
| ⟨p⟩ h := have p ≠ 0 := λ hp, h $ by rw [hp, of_fraction_ring_zero],
by simpa only [← of_fraction_ring_inv, ← of_fraction_ring_mul, ← of_fraction_ring_one]
  using _root_.mul_inv_cancel this

section has_scalar

variables {R : Type*} [monoid R] [distrib_mul_action R (polynomial K)]
variables [htower : is_scalar_tower R (polynomial K) (polynomial K)]
include htower

-- Can't define this in terms of `localization.has_scalar`, because that one
-- is not general enough.
instance : has_scalar R (ratfunc K) :=
⟨λ c p, p.lift_on (λ p q, ratfunc.mk (c • p) q) (λ p q p' q' hq hq' h, (mk_eq_mk hq hq').mpr $
  by rw [smul_mul_assoc, h, smul_mul_assoc])⟩

lemma mk_smul (c : R) (p q : polynomial K) :
  ratfunc.mk (c • p) q = c • ratfunc.mk p q :=
show ratfunc.mk (c • p) q = (ratfunc.mk p q).lift_on _ _,
from symm $ (lift_on_mk p q _ (λ p, show ratfunc.mk (c • p) 0 = ratfunc.mk (c • 0) 1,
  by rw [mk_zero, smul_zero, mk_eq_localization_mk (0 : polynomial K) one_ne_zero,
         localization.mk_zero]) _)

instance : is_scalar_tower R (polynomial K) (ratfunc K) :=
⟨λ c p q, q.induction_on' (λ q r _, by rw [← mk_smul, smul_assoc, mk_smul, mk_smul])⟩

end has_scalar

variables (K)

omit hdomain

instance : inhabited (ratfunc K) :=
⟨0⟩
instance [is_domain K] : nontrivial (ratfunc K) :=
⟨⟨0, 1, mt (congr_arg to_fraction_ring) $
  by simpa only [← of_fraction_ring_zero, ← of_fraction_ring_one] using zero_ne_one⟩⟩

omit hring

/-- Solve equations for `ratfunc K` by working in `fraction_ring (polynomial K)`. -/
meta def frac_tac : tactic unit :=
`[repeat { rintro (⟨⟩ : ratfunc _) },
  simp only [← of_fraction_ring_zero, ← of_fraction_ring_add, ← of_fraction_ring_sub,
    ← of_fraction_ring_neg, ← of_fraction_ring_one, ← of_fraction_ring_mul, ← of_fraction_ring_div,
    ← of_fraction_ring_inv,
    add_assoc, zero_add, add_zero, mul_assoc, mul_zero, mul_one, mul_add, inv_zero,
    add_comm, add_left_comm, mul_comm, mul_left_comm, sub_eq_add_neg, div_eq_mul_inv,
    add_mul, zero_mul, one_mul, ← neg_mul_eq_neg_mul, ← neg_mul_eq_mul_neg, add_right_neg]]

/-- Solve equations for `ratfunc K` by applying `ratfunc.induction_on`. -/
meta def smul_tac : tactic unit :=
`[repeat { rintro (x : ratfunc _) <|> intro },
  refine x.induction_on' (λ p q hq, _),
  simp_rw [← mk_smul, mk_eq_localization_mk _ hq],
  simp only [add_comm, mul_comm, zero_smul, succ_nsmul, zsmul_eq_mul, mul_add, mul_one, mul_zero,
    neg_add, ← neg_mul_eq_mul_neg,
    int.of_nat_eq_coe, int.coe_nat_succ, int.cast_zero, int.cast_add, int.cast_one,
    int.cast_neg_succ_of_nat, int.cast_coe_nat,
    localization.mk_zero, localization.add_mk_self, localization.neg_mk,
    of_fraction_ring_zero, ← of_fraction_ring_add, ← of_fraction_ring_neg]]

include hring hdomain

instance : field (ratfunc K) :=
{ add := (+),
  add_assoc := by frac_tac,
  add_comm := by frac_tac,
  zero := 0,
  zero_add := by frac_tac,
  add_zero := by frac_tac,
  neg := has_neg.neg,
  add_left_neg := by frac_tac,
  sub := has_sub.sub,
  sub_eq_add_neg := by frac_tac,
  mul := (*),
  mul_assoc := by frac_tac,
  mul_comm := by frac_tac,
  left_distrib := by frac_tac,
  right_distrib := by frac_tac,
  one := 1,
  one_mul := by frac_tac,
  mul_one := by frac_tac,
  inv := has_inv.inv,
  inv_zero := by frac_tac,
  div := (/),
  div_eq_mul_inv := by frac_tac,
  mul_inv_cancel := λ _, mul_inv_cancel,
  nsmul := (•),
  nsmul_zero' := by smul_tac,
  nsmul_succ' := by smul_tac,
  zsmul := (•),
  zsmul_zero' := by smul_tac,
  zsmul_succ' := by smul_tac,
  zsmul_neg' := by smul_tac,
  npow := npow_rec,
  zpow := zpow_rec,
  .. ratfunc.nontrivial K }

end field

section is_fraction_ring

/-! ### `ratfunc` as field of fractions of `polynomial` -/

include hdomain

instance (R : Type*) [comm_semiring R] [algebra R (polynomial K)] :
  algebra R (ratfunc K) :=
{ to_fun := λ x, ratfunc.mk (algebra_map _ _ x) 1,
  map_add' := λ x y, by simp only [mk_one', ring_hom.map_add, of_fraction_ring_add],
  map_mul' := λ x y, by simp only [mk_one', ring_hom.map_mul, of_fraction_ring_mul],
  map_one' := by simp only [mk_one', ring_hom.map_one, of_fraction_ring_one],
  map_zero' := by simp only [mk_one', ring_hom.map_zero, of_fraction_ring_zero],
  smul := (•),
  smul_def' := λ c x, x.induction_on' $ λ p q hq,
    by simp_rw [mk_one', ← mk_smul, mk_def_of_ne (c • p) hq, mk_def_of_ne p hq,
      ← of_fraction_ring_mul, is_localization.mul_mk'_eq_mk'_of_mul, algebra.smul_def],
  commutes' := λ c x, mul_comm _ _ }

variables {K}

lemma mk_one (x : polynomial K) : ratfunc.mk x 1 = algebra_map _ _ x := rfl

lemma of_fraction_ring_algebra_map (x : polynomial K) :
  of_fraction_ring (algebra_map _ (fraction_ring (polynomial K)) x) = algebra_map _ _ x :=
by rw [← mk_one, mk_one']

@[simp] lemma mk_eq_div (p q : polynomial K) :
  ratfunc.mk p q = (algebra_map _ _ p / algebra_map _ _ q) :=
by simp only [mk_eq_div', of_fraction_ring_div, of_fraction_ring_algebra_map]

variables (K)

lemma of_fraction_ring_comp_algebra_map :
  of_fraction_ring ∘ algebra_map (polynomial K) (fraction_ring (polynomial K)) = algebra_map _ _ :=
funext of_fraction_ring_algebra_map

lemma algebra_map_injective : function.injective (algebra_map (polynomial K) (ratfunc K)) :=
begin
  rw ← of_fraction_ring_comp_algebra_map,
  exact of_fraction_ring_injective.comp (is_fraction_ring.injective _ _),
end

@[simp] lemma algebra_map_eq_zero_iff {x : polynomial K} :
  algebra_map (polynomial K) (ratfunc K) x = 0 ↔ x = 0 :=
⟨(ring_hom.injective_iff _).mp (algebra_map_injective K) _, λ hx, by rw [hx, ring_hom.map_zero]⟩

variables {K}

lemma algebra_map_ne_zero {x : polynomial K} (hx : x ≠ 0) :
  algebra_map (polynomial K) (ratfunc K) x ≠ 0 :=
mt (algebra_map_eq_zero_iff K).mp hx

variables (K)

omit hdomain

/-- `ratfunc K` is isomorphic to the field of fractions of `polynomial K`, as rings.

This is an auxiliary definition; `simp`-normal form is `is_localization.alg_equiv`.
-/
def aux_equiv : fraction_ring (polynomial K) ≃+* ratfunc K :=
{ to_fun := of_fraction_ring,
  inv_fun := to_fraction_ring,
  left_inv := λ x, rfl,
  right_inv := λ ⟨x⟩, rfl,
  map_add' := of_fraction_ring_add,
  map_mul' := of_fraction_ring_mul }

include hdomain

/-- `ratfunc K` is the field of fractions of the polynomials over `K`. -/
instance : is_fraction_ring (polynomial K) (ratfunc K) :=
{ map_units := λ y, by rw ← of_fraction_ring_algebra_map;
    exact (aux_equiv K).to_ring_hom.is_unit_map (is_localization.map_units _ y),
  eq_iff_exists := λ x y, by rw [← of_fraction_ring_algebra_map, ← of_fraction_ring_algebra_map];
    exact (aux_equiv K).injective.eq_iff.trans (is_localization.eq_iff_exists _ _),
  surj := by { rintro ⟨z⟩, convert is_localization.surj (polynomial K)⁰ z, ext ⟨x, y⟩,
    simp only [← of_fraction_ring_algebra_map, function.comp_app, ← of_fraction_ring_mul] } }

variables {K}

@[simp] lemma lift_on_div {P : Sort v} (p q : polynomial K)
  (f : ∀ (p q : polynomial K), P) (f0 : ∀ p, f p 0 = f 0 1)
  (H : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), p * q' = p' * q → f p q = f p' q') :
  (algebra_map _ (ratfunc K) p / algebra_map _ _ q).lift_on f @H = f p q :=
by rw [← mk_eq_div, lift_on_mk _ _ f f0 @H]

@[simp] lemma lift_on'_div {P : Sort v} (p q : polynomial K)
  (f : ∀ (p q : polynomial K), P) (f0 : ∀ p, f p 0 = f 0 1) (H) :
  (algebra_map _ (ratfunc K) p / algebra_map _ _ q).lift_on' f @H = f p q :=
by { rw [ratfunc.lift_on', lift_on_div], assumption }

/-- Induction principle for `ratfunc K`: if `f p q : P (p / q)` for all `p q : polynomial K`,
then `P` holds on all elements of `ratfunc K`.

See also `induction_on'`, which is a recursion principle defined in terms of `ratfunc.mk`.
-/
protected lemma induction_on {P : ratfunc K → Prop} (x : ratfunc K)
  (f : ∀ (p q : polynomial K) (hq : q ≠ 0),
    P (algebra_map _ (ratfunc K) p / algebra_map _ _ q)) :
  P x :=
x.induction_on' (λ p q hq, by simpa using f p q hq)

lemma of_fraction_ring_mk' (x : polynomial K) (y : (polynomial K)⁰) :
  of_fraction_ring (is_localization.mk' _ x y) = is_localization.mk' (ratfunc K) x y :=
by rw [is_fraction_ring.mk'_eq_div, is_fraction_ring.mk'_eq_div, ← mk_eq_div', ← mk_eq_div]

@[simp] lemma of_fraction_ring_eq :
  (of_fraction_ring : fraction_ring (polynomial K) → ratfunc K) =
    is_localization.alg_equiv (polynomial K)⁰ _ _ :=
funext $ λ x, localization.induction_on x $ λ x,
by simp only [is_localization.alg_equiv_apply, is_localization.ring_equiv_of_ring_equiv_apply,
    ring_equiv.to_fun_eq_coe, localization.mk_eq_mk'_apply, is_localization.map_mk',
    of_fraction_ring_mk', ring_equiv.coe_to_ring_hom, ring_equiv.refl_apply, set_like.eta]

@[simp] lemma to_fraction_ring_eq :
  (to_fraction_ring : ratfunc K → fraction_ring (polynomial K)) =
    is_localization.alg_equiv (polynomial K)⁰ _ _ :=
funext $ λ ⟨x⟩, localization.induction_on x $ λ x,
by simp only [localization.mk_eq_mk'_apply, of_fraction_ring_mk', is_localization.alg_equiv_apply,
  ring_equiv.to_fun_eq_coe, is_localization.ring_equiv_of_ring_equiv_apply,
  is_localization.map_mk', ring_equiv.coe_to_ring_hom, ring_equiv.refl_apply, set_like.eta]

@[simp] lemma aux_equiv_eq :
  aux_equiv K = (is_localization.alg_equiv (polynomial K)⁰ _ _).to_ring_equiv :=
by { ext x,
     simp only [aux_equiv, ring_equiv.coe_mk, of_fraction_ring_eq, alg_equiv.coe_ring_equiv'] }

end is_fraction_ring

section num_denom

/-! ### Numerator and denominator -/

open gcd_monoid polynomial

omit hring
variables [hfield : field K]
include hfield

/-- `ratfunc.num_denom` are numerator and denominator of a rational function over a field,
normalized such that the denominator is monic. -/
def num_denom (x : ratfunc K) : polynomial K × polynomial K :=
x.lift_on' (λ p q, if q = 0 then ⟨0, 1⟩ else let r := gcd p q in
  ⟨polynomial.C ((q / r).leading_coeff⁻¹) * (p / r),
   polynomial.C ((q / r).leading_coeff⁻¹) * (q / r)⟩)
  begin
    intros p q a hq ha,
    rw [if_neg hq, if_neg (mul_ne_zero ha hq)],
    have hpq : gcd p q ≠ 0 := mt (and.right ∘ (gcd_eq_zero_iff _ _).mp) hq,
    have ha' : a.leading_coeff ≠ 0 := polynomial.leading_coeff_ne_zero.mpr ha,
    have hainv : (a.leading_coeff)⁻¹ ≠ 0 := inv_ne_zero ha',
    simp only [prod.ext_iff, gcd_mul_left, normalize_apply, polynomial.coe_norm_unit, mul_assoc,
      comm_group_with_zero.coe_norm_unit _ ha'],
    have hdeg : (gcd p q).degree ≤ q.degree := degree_gcd_le_right _ hq,
    have hdeg' : (polynomial.C (a.leading_coeff⁻¹) * gcd p q).degree ≤ q.degree,
    { rw [polynomial.degree_mul, polynomial.degree_C hainv, zero_add],
      exact hdeg },
    have hdivp : (polynomial.C a.leading_coeff⁻¹) * gcd p q ∣ p :=
      (C_mul_dvd hainv).mpr (gcd_dvd_left p q),
    have hdivq : (polynomial.C a.leading_coeff⁻¹) * gcd p q ∣ q :=
      (C_mul_dvd hainv).mpr (gcd_dvd_right p q),
    rw [euclidean_domain.mul_div_mul_cancel ha hdivp, euclidean_domain.mul_div_mul_cancel ha hdivq,
        leading_coeff_div hdeg, leading_coeff_div hdeg', polynomial.leading_coeff_mul,
        polynomial.leading_coeff_C, div_C_mul, div_C_mul,
        ← mul_assoc, ← polynomial.C_mul, ← mul_assoc, ← polynomial.C_mul],
    split; congr; rw [inv_div, mul_comm, mul_div_assoc, ← mul_assoc, inv_inv₀,
      _root_.mul_inv_cancel ha', one_mul, inv_div],
  end

@[simp] lemma num_denom_div (p : polynomial K) {q : polynomial K} (hq : q ≠ 0) :
  num_denom (algebra_map _ _ p / algebra_map _ _ q) =
    (polynomial.C ((q / gcd p q).leading_coeff⁻¹) * (p / gcd p q),
     polynomial.C ((q / gcd p q).leading_coeff⁻¹) * (q / gcd p q)) :=
begin
  rw [num_denom, lift_on'_div, if_neg hq],
  intros p,
  rw [if_pos rfl, if_neg (@one_ne_zero (polynomial K) _ _)],
  simp,
end

/-- `ratfunc.num` is the numerator of a rational function,
normalized such that the denominator is monic. -/
def num (x : ratfunc K) : polynomial K := x.num_denom.1

@[simp] lemma num_div (p : polynomial K) {q : polynomial K} (hq : q ≠ 0) :
  num (algebra_map _ _ p / algebra_map _ _ q) =
    polynomial.C ((q / gcd p q).leading_coeff⁻¹) * (p / gcd p q) :=
by rw [num, num_denom_div _ hq]

@[simp] lemma num_zero : num (0 : ratfunc K) = 0 :=
by { convert num_div (0 : polynomial K) one_ne_zero; simp }

@[simp] lemma num_one : num (1 : ratfunc K) = 1 :=
by { convert num_div (1 : polynomial K) one_ne_zero; simp }

@[simp] lemma num_algebra_map (p : polynomial K) :
  num (algebra_map _ _ p) = p :=
by { convert num_div p one_ne_zero; simp }

@[simp] lemma num_div_dvd (p : polynomial K) {q : polynomial K} (hq : q ≠ 0) :
  num (algebra_map _ _ p / algebra_map _ _ q) ∣ p :=
begin
  rw [num_div _ hq, C_mul_dvd],
  { exact euclidean_domain.div_dvd_of_dvd (gcd_dvd_left p q) },
  { simpa only [ne.def, inv_eq_zero, polynomial.leading_coeff_eq_zero]
      using right_div_gcd_ne_zero hq },
end

/-- `ratfunc.denom` is the denominator of a rational function,
normalized such that it is monic. -/
def denom (x : ratfunc K) : polynomial K := x.num_denom.2

@[simp] lemma denom_div (p : polynomial K) {q : polynomial K} (hq : q ≠ 0) :
  denom (algebra_map _ _ p / algebra_map _ _ q) =
    polynomial.C ((q / gcd p q).leading_coeff⁻¹) * (q / gcd p q) :=
by rw [denom, num_denom_div _ hq]

lemma monic_denom (x : ratfunc K) : (denom x).monic :=
x.induction_on (λ p q hq, begin
  rw [denom_div p hq, mul_comm],
  exact polynomial.monic_mul_leading_coeff_inv (right_div_gcd_ne_zero hq)
end)

lemma denom_ne_zero (x : ratfunc K) : denom x ≠ 0 :=
(monic_denom x).ne_zero

@[simp] lemma denom_zero : denom (0 : ratfunc K) = 1 :=
by { convert denom_div (0 : polynomial K) one_ne_zero; simp }

@[simp] lemma denom_one : denom (1 : ratfunc K) = 1 :=
by { convert denom_div (1 : polynomial K) one_ne_zero; simp }

@[simp] lemma denom_algebra_map (p : polynomial K) :
  denom (algebra_map _ (ratfunc K) p) = 1 :=
by { convert denom_div p one_ne_zero; simp }

@[simp] lemma denom_div_dvd (p : polynomial K) {q : polynomial K} (hq : q ≠ 0) :
  denom (algebra_map _ _ p / algebra_map _ _ q) ∣ q :=
begin
  rw [denom_div _ hq, C_mul_dvd],
  { exact euclidean_domain.div_dvd_of_dvd (gcd_dvd_right p q) },
  { simpa only [ne.def, inv_eq_zero, polynomial.leading_coeff_eq_zero]
      using right_div_gcd_ne_zero hq },
end

@[simp] lemma num_div_denom (x : ratfunc K) :
  algebra_map _ _ (num x) / algebra_map _ _ (denom x) = x :=
x.induction_on (λ p q hq, begin
  by_cases hp : p = 0, { simp [hp] },
  have q_div_ne_zero := right_div_gcd_ne_zero hq,
  rw [num_div p hq, denom_div p hq, ring_hom.map_mul, ring_hom.map_mul,
    mul_div_mul_left, div_eq_div_iff, ← ring_hom.map_mul, ← ring_hom.map_mul, mul_comm _ q,
    ← euclidean_domain.mul_div_assoc, ← euclidean_domain.mul_div_assoc, mul_comm],
  { apply gcd_dvd_right },
  { apply gcd_dvd_left },
  { exact algebra_map_ne_zero q_div_ne_zero },
  { exact algebra_map_ne_zero hq },
  { refine algebra_map_ne_zero (mt polynomial.C_eq_zero.mp _),
    exact inv_ne_zero (polynomial.leading_coeff_ne_zero.mpr q_div_ne_zero) },
end)

@[simp] lemma num_eq_zero_iff {x : ratfunc K} : num x = 0 ↔ x = 0 :=
⟨λ h, by rw [← num_div_denom x, h, ring_hom.map_zero, zero_div],
 λ h, h.symm ▸ num_zero⟩

lemma num_ne_zero {x : ratfunc K} (hx : x ≠ 0) : num x ≠ 0 :=
mt num_eq_zero_iff.mp hx

lemma num_mul_eq_mul_denom_iff {x : ratfunc K} {p q : polynomial K}
  (hq : q ≠ 0) :
  x.num * q = p * x.denom ↔ x = algebra_map _ _ p / algebra_map _ _ q :=
begin
  rw [← (algebra_map_injective K).eq_iff, eq_div_iff (algebra_map_ne_zero hq)],
  conv_rhs { rw ← num_div_denom x },
  rw [ring_hom.map_mul, ring_hom.map_mul, div_eq_mul_inv, mul_assoc, mul_comm (has_inv.inv _),
      ← mul_assoc, ← div_eq_mul_inv, div_eq_iff],
  exact algebra_map_ne_zero (denom_ne_zero x)
end

lemma num_denom_add (x y : ratfunc K) :
  (x + y).num * (x.denom * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom :=
(num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr $
begin
  conv_lhs { rw [← num_div_denom x, ← num_div_denom y] },
  rw [div_add_div, ring_hom.map_mul, ring_hom.map_add, ring_hom.map_mul, ring_hom.map_mul],
  { exact algebra_map_ne_zero (denom_ne_zero x) },
  { exact algebra_map_ne_zero (denom_ne_zero y) }
end

lemma num_denom_mul (x y : ratfunc K) :
  (x * y).num * (x.denom * y.denom) = x.num * y.num * (x * y).denom :=
(num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr $
  by conv_lhs { rw [← num_div_denom x, ← num_div_denom y, div_mul_div,
                    ← ring_hom.map_mul, ← ring_hom.map_mul] }

lemma num_dvd {x : ratfunc K} {p : polynomial K} (hp : p ≠ 0) :
  num x ∣ p ↔ ∃ (q : polynomial K) (hq : q ≠ 0), x = algebra_map _ _ p / algebra_map _ _ q :=
begin
  split,
  { rintro ⟨q, rfl⟩,
    obtain ⟨hx, hq⟩ := mul_ne_zero_iff.mp hp,
    use denom x * q,
    rw [ring_hom.map_mul, ring_hom.map_mul, ← div_mul_div, div_self, mul_one, num_div_denom],
    { exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩ },
    { exact algebra_map_ne_zero hq } },
  { rintro ⟨q, hq, rfl⟩,
    exact num_div_dvd p hq },
end

lemma denom_dvd {x : ratfunc K} {q : polynomial K} (hq : q ≠ 0) :
  denom x ∣ q ↔ ∃ (p : polynomial K), x = algebra_map _ _ p / algebra_map _ _ q :=
begin
  split,
  { rintro ⟨p, rfl⟩,
    obtain ⟨hx, hp⟩ := mul_ne_zero_iff.mp hq,
    use num x * p,
    rw [ring_hom.map_mul, ring_hom.map_mul, ← div_mul_div, div_self, mul_one, num_div_denom],
    { exact algebra_map_ne_zero hp } },
  { rintro ⟨p, rfl⟩,
    exact denom_div_dvd p hq },
end

lemma num_mul_dvd (x y : ratfunc K) : num (x * y) ∣ num x * num y :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  by_cases hy : y = 0,
  { simp [hy] },
  rw num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy)),
  refine ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), _⟩,
  rw [ring_hom.map_mul, ring_hom.map_mul, ← div_mul_div, num_div_denom, num_div_denom]
end

lemma denom_mul_dvd (x y : ratfunc K) : denom (x * y) ∣ denom x * denom y :=
begin
  rw denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y)),
  refine ⟨x.num * y.num, _⟩,
  rw [ring_hom.map_mul, ring_hom.map_mul, ← div_mul_div, num_div_denom, num_div_denom]
end

lemma denom_add_dvd (x y : ratfunc K) : denom (x + y) ∣ denom x * denom y :=
begin
  rw denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y)),
  refine ⟨x.num * y.denom + x.denom * y.num, _⟩,
  rw [ring_hom.map_mul, ring_hom.map_add, ring_hom.map_mul, ring_hom.map_mul, ← div_add_div,
      num_div_denom, num_div_denom],
  { exact algebra_map_ne_zero (denom_ne_zero x) },
  { exact algebra_map_ne_zero (denom_ne_zero y) },
end

end num_denom

section eval

/-! ### Polynomial structure: `C`, `X`, `eval` -/

include hdomain

/-- `ratfunc.C a` is the constant rational function `a`. -/
def C : K →+* ratfunc K :=
algebra_map _ _

@[simp] lemma algebra_map_eq_C : algebra_map K (ratfunc K) = C := rfl
@[simp] lemma algebra_map_C (a : K) :
  algebra_map (polynomial K) (ratfunc K) (polynomial.C a) = C a := rfl
@[simp] lemma algebra_map_comp_C :
  (algebra_map (polynomial K) (ratfunc K)).comp polynomial.C = C := rfl

/-- `ratfunc.X` is the polynomial variable (aka indeterminate). -/
def X : ratfunc K := algebra_map (polynomial K) (ratfunc K) polynomial.X

@[simp] lemma algebra_map_X :
  algebra_map (polynomial K) (ratfunc K) polynomial.X = X := rfl

omit hring hdomain
variables [hfield : field K]
include hfield

@[simp] lemma num_C (c : K) : num (C c) = polynomial.C c :=
num_algebra_map _
@[simp] lemma denom_C (c : K) : denom (C c) = 1 :=
denom_algebra_map _

@[simp] lemma num_X : num (X : ratfunc K) = polynomial.X :=
num_algebra_map _
@[simp] lemma denom_X : denom (X : ratfunc K) = 1 :=
denom_algebra_map _

variables {L : Type*} [field L]

/-- Evaluate a rational function `p` given a ring hom `f` from the scalar field
to the target and a value `x` for the variable in the target.

Fractions are reduced by clearing common denominators before evaluating:
`eval id 1 ((X^2 - 1) / (X - 1)) = eval id 1 (X + 1) = 2`, not `0 / 0 = 0`.
-/
def eval (f : K →+* L) (a : L) (p : ratfunc K) : L :=
(num p).eval₂ f a / (denom p).eval₂ f a

variables {f : K →+* L} {a : L}

lemma eval_eq_zero_of_eval₂_denom_eq_zero
  {x : ratfunc K} (h : polynomial.eval₂ f a (denom x) = 0) :
  eval f a x = 0 :=
by rw [eval, h, div_zero]
lemma eval₂_denom_ne_zero {x : ratfunc K} (h : eval f a x ≠ 0) :
  polynomial.eval₂ f a (denom x) ≠ 0 :=
mt eval_eq_zero_of_eval₂_denom_eq_zero h

variables (f a)

@[simp] lemma eval_C {c : K} : eval f a (C c) = f c := by simp [eval]
@[simp] lemma eval_X : eval f a X = a := by simp [eval]
@[simp] lemma eval_zero : eval f a 0 = 0 := by simp [eval]
@[simp] lemma eval_one : eval f a 1 = 1 := by simp [eval]
@[simp] lemma eval_algebra_map {S : Type*} [comm_semiring S] [algebra S (polynomial K)] (p : S) :
  eval f a (algebra_map _ _ p) = (algebra_map _ (polynomial K) p).eval₂ f a :=
by simp [eval, is_scalar_tower.algebra_map_apply S (polynomial K) (ratfunc K)]

/-- `eval` is an additive homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 1 (X / (X-1)) + eval _ 1 (-1 / (X-1)) = 0`
`... ≠ 1 = eval _ 1 ((X-1) / (X-1))`.

See also `ratfunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
lemma eval_add {x y : ratfunc K}
  (hx : polynomial.eval₂ f a (denom x) ≠ 0) (hy : polynomial.eval₂ f a (denom y) ≠ 0) :
  eval f a (x + y) = eval f a x + eval f a y :=
begin
  unfold eval,
  by_cases hxy : polynomial.eval₂ f a (denom (x + y)) = 0,
  { have := polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_add_dvd x y) hxy,
    rw polynomial.eval₂_mul at this,
    cases mul_eq_zero.mp this; contradiction },
  rw [div_add_div _ _ hx hy, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv, div_eq_iff hxy],
  simp only [← polynomial.eval₂_mul, ← polynomial.eval₂_add],
  congr' 1,
  apply num_denom_add
end

/-- `eval` is a multiplicative homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 0 X * eval _ 0 (1/X) = 0 ≠ 1 = eval _ 0 1 = eval _ 0 (X * 1/X)`.

See also `ratfunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
lemma eval_mul {x y : ratfunc K}
  (hx : polynomial.eval₂ f a (denom x) ≠ 0) (hy : polynomial.eval₂ f a (denom y) ≠ 0) :
  eval f a (x * y) = eval f a x * eval f a y :=
begin
  unfold eval,
  by_cases hxy : polynomial.eval₂ f a (denom (x * y)) = 0,
  { have := polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_mul_dvd x y) hxy,
    rw polynomial.eval₂_mul at this,
    cases mul_eq_zero.mp this; contradiction },
  rw [div_mul_div, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv, div_eq_iff hxy],
  repeat { rw ← polynomial.eval₂_mul },
  congr' 1,
  apply num_denom_mul,
end

end eval

end ratfunc
