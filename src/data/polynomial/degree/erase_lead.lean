/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.degree.basic
import data.polynomial.degree.trailing_degree

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `erase_lead f`: the polynomial `f - leading term of f`

`erase_lead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/

noncomputable theory
open_locale classical

open polynomial finsupp finset

namespace polynomial

variables {R : Type*} [semiring R] {f : polynomial R}

/-- `erase_lead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def erase_lead (f : polynomial R) : polynomial R :=
finsupp.erase f.nat_degree f

section erase_lead

lemma erase_lead_support (f : polynomial R) :
  f.erase_lead.support = f.support.erase f.nat_degree :=
by convert rfl

lemma erase_lead_add_C_mul_X_pow (f : polynomial R) :
  f.erase_lead + (C f.leading_coeff) * X^f.nat_degree = f :=
begin
  ext i,
  simp only [erase_lead_coeff_eq, coeff_monomial, coeff_add, @eq_comm _ _ i],
  split_ifs with h,
  { subst i, simp only [leading_coeff, zero_add] },
  { exact add_zero _ }
end

@[simp] lemma sum_leading_C_mul_X_pow_ring {S : Type*} [ring S] (g : polynomial S)
 : g.erase_lead = g - (C g.leading_coeff) * X^g.nat_degree :=
eq_sub_iff_add_eq.mpr (erase_lead_add_C_mul_X_pow g)

lemma erase_lead_ne_zero (f0 : 2 ≤ f.support.card) : erase_lead f ≠ 0 :=
begin
  have fn0 : f ≠ 0,
  { rintro rfl, simpa only [card_empty, le_zero_iff_eq, support_zero, two_ne_zero] using f0 },
  rw [ne.def, ← support_eq_empty, erase_lead_support],
  apply @ne_empty_of_mem _ (nat_trailing_degree f),
  apply mem_erase_of_ne_of_mem _ (nat_trailing_degree_mem_support_of_nonzero fn0),
  rw [nat_degree_eq_support_max' fn0, nat_trailing_degree_eq_support_min' fn0],
  exact ne_of_lt (finset.min'_lt_max'_of_card _ f0)
end

@[simp] lemma nat_degree_not_mem_erase_lead_support : f.nat_degree ∉ (erase_lead f).support :=
by convert not_mem_erase _ _

@[simp] lemma ne_nat_degree_of_mem_erase_lead_support {a : ℕ} (h : a ∈ (erase_lead f).support) :
  a ≠ f.nat_degree :=
by { rintro rfl, exact nat_degree_not_mem_erase_lead_support h }

lemma erase_lead_nat_degree_lt (f0 : 2 ≤ f.support.card) : (erase_lead f).nat_degree < f.nat_degree :=
begin
  rw nat_degree_eq_support_max' (erase_lead_ne_zero f0),
  apply nat.lt_of_le_and_ne _
    (ne_nat_degree_of_mem_erase_lead_support
      ((erase_lead f).support.max'_mem (nonempty_support_iff.mpr _))),
  apply max'_le,
  intros i hi,
  apply le_nat_degree_of_ne_zero,
  rw ← mem_support_iff_coeff_ne_zero,
  simp only [erase_lead_support] at hi,
  exact erase_subset _ _ hi
end

lemma erase_lead_support_card_lt (h : f ≠ 0) : (erase_lead f).support.card < f.support.card :=
begin
  rw erase_lead_support,
  exact card_lt_card (erase_ssubset $ nat_degree_mem_support_of_nonzero h)
end

@[simp] lemma erase_lead_monomial (i : ℕ) (r : R) :
  erase_lead (monomial i r) = 0 :=
begin
  by_cases f0 : f = 0,
  { ext1,
    rw [f0, leading_coeff_zero, C_0, zero_mul], },
  { conv_lhs {rw ← erase_lead_add_C_mul_X_pow f},
    apply add_cancel,
    rw [← support_eq_empty, ← card_eq_zero],
    apply nat.eq_zero_of_le_zero (nat.lt_succ_iff.mp _),
    convert support_card_lt f0,
    apply le_antisymm _ h,
    exact card_le_of_subset (singleton_subset_iff.mpr (nat_degree_mem_support_of_nonzero f0)), },
end

@[simp] lemma erase_lead_C (r : R) : erase_lead (C r) = 0 :=
erase_lead_monomial _ _

@[simp] lemma erase_lead_X : erase_lead (X : polynomial R) = 0 :=
erase_lead_monomial _ _

@[simp] lemma erase_lead_X_pow (n : ℕ) : erase_lead (X ^ n : polynomial R) = 0 :=
by rw [X_pow_eq_monomial, erase_lead_monomial]

@[simp] lemma erase_lead_C_mul_X_pow (r : R) (n : ℕ) : erase_lead (C r * X ^ n) = 0 :=
by rw [C_mul_X_pow_eq_monomial, erase_lead_monomial]

lemma erase_lead_degree_le : (erase_lead f).degree ≤ f.degree :=
begin
  rw degree_le_iff_coeff_zero,
  intros i hi,
  rw erase_lead_coeff_eq,
  split_ifs with h, { refl },
  apply coeff_eq_zero_of_degree_lt hi
end

lemma erase_lead_nat_degree_le : (erase_lead f).nat_degree ≤ f.nat_degree :=
nat_degree_le_nat_degree erase_lead_degree_le

end erase_lead

end polynomial
