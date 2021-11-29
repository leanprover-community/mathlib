/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.char_p.basic
import tactic.interval_cases

/-!
# Lemmas about rings of characteristic two

This file contains results about `char_p R 2`, in the `char_two` namespace.

The lemmas in this file with a `_sq` suffix are just special cases of the `_pow_char` lemmas
elsewhere, with a shorter name for ease of discovery, and no need for a `[fact (prime 2)]` argument.
-/

variables {R ι : Type*}

local attribute [instance] nat.fact_prime_two

namespace char_two

section semiring
variables [semiring R] [char_p R 2]

lemma two_eq_zero : (2 : R) = 0 :=
by rw [← nat.cast_two, char_p.cast_eq_zero]

lemma add_self_eq_zero (x : R) : x + x = 0 :=
by rw [←two_smul R x, two_eq_zero, zero_smul]

lemma bit0_eq_zero (x : R) : (bit0 x : R) = 0 :=
add_self_eq_zero x

lemma bit1_eq_one (x : R) : (bit1 x : R) = 1 :=
by rw [bit1, bit0_eq_zero, zero_add]

end semiring

section ring
variables [ring R] [char_p R 2]

lemma neg_eq (x : R) : -x = x :=
by rw [neg_eq_iff_add_eq_zero, ←two_smul R x, two_eq_zero, zero_smul]

lemma one_eq_neg_iff [nontrivial R] : (-1 : R) = 1 ↔ ring_char R = 2 :=
begin
  refine ⟨λ h, _, λ h, @@neg_eq _ (ring_char.of_eq h) 1⟩,
  rw [eq_comm, ←sub_eq_zero, sub_neg_eq_add, show (1 + 1 : R) = (1 + 1 : ℕ), by norm_cast] at h,
  have := nat.le_of_dvd zero_lt_two (ring_char.dvd h),
  interval_cases (ring_char R) with hrc,
  { haveI := ring_char.eq_iff.mp hrc,
    haveI := char_p.char_p_to_char_zero R,
    apply false.elim (@two_ne_zero' R _ _ _ _),
    exact_mod_cast h },
  { have := @char_p.ring_char_ne_one R _ _,
    contradiction },
  { assumption }
end

@[simp] lemma order_of_neg_one [nontrivial R] :
  order_of (-1 : R) = if ring_char R = 2 then 1 else 2 :=
begin
  split_ifs,
  { simpa [one_eq_neg_iff] using h },
  apply order_of_eq_prime,
  { simp },
  simpa [one_eq_neg_iff] using h
end

lemma neg_eq' : has_neg.neg = (id : R → R) :=
funext neg_eq

lemma sub_eq_add (x y : R) : x - y = x + y :=
by rw [sub_eq_add_neg, neg_eq]

lemma sub_eq_add' : has_sub.sub = ((+) : R → R → R) :=
funext $ λ x, funext $ λ y, sub_eq_add x y

end ring

section comm_semiring
variables [comm_semiring R] [char_p R 2]

lemma add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
add_pow_char _ _ _

lemma add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y :=
by rw [←pow_two, ←pow_two, ←pow_two, add_sq]

open_locale big_operators

lemma list_sum_sq (l : list R) : l.sum ^ 2 = (l.map (^ 2)).sum :=
list_sum_pow_char _ _

lemma list_sum_mul_self (l : list R) : l.sum * l.sum = (list.map (λ x, x * x) l).sum :=
by simp_rw [←pow_two, list_sum_sq]

lemma multiset_sum_sq (l : multiset R) : l.sum ^ 2 = (l.map (^ 2)).sum :=
multiset_sum_pow_char _ _

lemma multiset_sum_mul_self (l : multiset R) : l.sum * l.sum = (multiset.map (λ x, x * x) l).sum :=
by simp_rw [←pow_two, multiset_sum_sq]

lemma sum_sq (s : finset ι) (f : ι → R) :
  (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^ 2 :=
sum_pow_char _ _ _

lemma sum_mul_self (s : finset ι) (f : ι → R) :
  (∑ i in s, f i) * (∑ i in s, f i) = ∑ i in s, f i * f i :=
by simp_rw [←pow_two, sum_sq]

end comm_semiring

end char_two
