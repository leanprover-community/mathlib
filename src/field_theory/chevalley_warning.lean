/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.mv_polynomial
import field_theory.finite

/-!
# The Chevalley–Warning theorem

This file contains a proof of the Chevalley–Warning theorem.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Main results

1. Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
   such that the total degree of `f` is less than `(q-1)` times the cardinality of `σ`.
   Then the evaluation of `f` on all points of `σ → K` (aka `K^σ`) sums to `0`.
   (`sum_mv_polynomial_eq_zero`)
2. The Chevalley–Warning theorem (`char_dvd_card_solutions`).
   Let `f i` be a finite family of multivariate polynomials
   in finitely many variables (`X s`, `s : σ`) such that
   the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
   Then the number of common solutions of the `f i`
   is divisible by the characteristic of `K`.

## Notation

- `K` is a finite field
- `q` is notation for the cardinality of `K`
- `σ` is the indexing type for the variables of a multivariate polynomial ring over `K`

-/

universes u v

open_locale big_operators

namespace equiv

variables {X : Type*} {Y : Type*} [decidable_eq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def cofiber (f : {x' // x' ≠ x} → Y) : {g : X → Y // g ∘ coe = f} ≃ Y :=
(subtype_preimage _ f).trans (fun_unique _ _)

@[simp] lemma coe_cofiber (f : {x' // x' ≠ x} → Y) :
  (cofiber f : {g : X → Y // g ∘ coe = f} → Y) = λ g, (g : X → Y) x := rfl

@[simp] lemma cofiber_apply (f : {x' // x' ≠ x} → Y) (g : {g : X → Y // g ∘ coe = f}) :
  cofiber f g = (g : X → Y) x := rfl

lemma coe_cofiber_symm (f : {x' // x' ≠ x} → Y) :
  ((cofiber f).symm : Y → {g : X → Y // g ∘ coe = f}) =
  λ y, ⟨λ x', if h : x' ≠ x then f ⟨x', h⟩ else y,
    by { funext x', dsimp, erw [dif_pos x'.2, subtype.coe_eta] }⟩ := rfl

@[simp] lemma cofiber_symm_apply (f : {x' // x' ≠ x} → Y) (y : Y) (x' : X) :
  ((cofiber f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
rfl

@[simp] lemma cofiber_symm_apply_eq (f : {x' // x' ≠ x} → Y) (y : Y) :
  ((cofiber f).symm y : X → Y) x = y :=
dif_neg (not_not.mpr rfl)

@[simp] lemma cofiber_symm_apply_ne (f : {x' // x' ≠ x} → Y) (y : Y) (x' : X) (h : x' ≠ x) :
  ((cofiber f).symm y : X → Y) x' = f ⟨x', h⟩ :=
dif_pos h

end equiv

namespace finsupp

@[to_additive]
lemma prod_fintype {ι : Type*} {X : Type*} {M : Type*} [fintype ι] [has_zero X] [comm_monoid M]
  (f : ι →₀ X) (g : ι → X → M) (h : ∀ i, g i 0 = 1) :
  f.prod g = ∏ i, g i (f i) :=
begin
  classical,
  rw [finsupp.prod, ← fintype.prod_extend_by_one, finset.prod_congr rfl],
  intros i hi,
  split_ifs with hif hif,
  { refl },
  { rw finsupp.not_mem_support_iff at hif,
    rw [hif, h] }
end

end finsupp

namespace mv_polynomial
open finset
variables {R : Type*} {σ : Type*} [comm_semiring R]
variables {S : Type*} [comm_semiring S]

lemma eval_sum {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ R) (g : σ → R) :
  eval g (∑ i in s, f i) = ∑ i in s, eval g (f i) :=
eval₂_sum (ring_hom.id R) g s f

@[to_additive]
lemma eval_prod {ι : Type*} (s : finset ι) (f : ι → mv_polynomial σ R) (g : σ → R) :
  eval g (∏ i in s, f i) = ∏ i in s, eval g (f i) :=
eval₂_prod (ring_hom.id R) g s f

lemma eval₂_eq (g : R →+* S) (x : σ → S) (f : mv_polynomial σ R) :
  f.eval₂ g x = ∑ d in f.support, g (f.coeff d) * ∏ i in d.support, x i ^ d i :=
rfl

lemma eval_eq (x : σ → R) (f : mv_polynomial σ R) :
  f.eval x = ∑ d in f.support, f.coeff d * ∏ i in d.support, x i ^ d i :=
rfl

variables [fintype σ]

lemma eval₂_eq' (g : R →+* S) (x : σ → S) (f : mv_polynomial σ R) :
  f.eval₂ g x = ∑ d in f.support, g (f.coeff d) * ∏ i, x i ^ d i :=
by { simp only [eval₂_eq, ← finsupp.prod_pow], refl }

lemma eval_eq' (x : σ → R) (f : mv_polynomial σ R) :
  f.eval x = ∑ d in f.support, f.coeff d * ∏ i, x i ^ d i :=
eval₂_eq' (ring_hom.id R) x f

lemma exists_degree_lt (f : mv_polynomial σ R) (n : ℕ)
  (h : f.total_degree < n * fintype.card σ) {d : σ →₀ ℕ} (hd : d ∈ f.support) :
  ∃ i, d i < n :=
begin
  contrapose! h,
  calc n * fintype.card σ
        = ∑ s:σ, n         : by rw [sum_const, nat.smul_eq_mul, mul_comm, card_univ]
    ... ≤ ∑ s, d s         : sum_le_sum (λ s _, h s)
    ... ≤ d.sum (λ i e, e) : by { rw [finsupp.sum_fintype], intros, refl }
    ... ≤ f.total_degree   : finset.le_sup hd,
end

end mv_polynomial

section finite_field
open mv_polynomial function finset finite_field

variables {K : Type*} {σ : Type*} [fintype K] [field K] [fintype σ]
local notation `q` := fintype.card K

lemma mv_polynomial.sum_mv_polynomial_eq_zero [decidable_eq σ] (f : mv_polynomial σ K)
  (h : f.total_degree < (q - 1) * fintype.card σ) :
  (∑ x, f.eval x) = 0 :=
begin
  haveI : decidable_eq K := classical.dec_eq K,
  calc (∑ x, f.eval x)
        = ∑ x : σ → K, ∑ d in f.support, f.coeff d * ∏ i, x i ^ d i : by simp only [eval_eq']
    ... = ∑ d in f.support, ∑ x : σ → K, f.coeff d * ∏ i, x i ^ d i : sum_comm
    ... = 0 : sum_eq_zero _,
  intros d hd,
  obtain ⟨i, hi⟩ : ∃ i, d i < q - 1, from f.exists_degree_lt (q - 1) h hd,
  calc (∑ x : σ → K, f.coeff d * ∏ i, x i ^ d i)
        = f.coeff d * (∑ x : σ → K, ∏ i, x i ^ d i) : mul_sum.symm
    ... = 0                                         : (mul_eq_zero.mpr ∘ or.inr) _,
  calc (∑ x : σ → K, ∏ i, x i ^ d i)
        = ∑ (x₀ : {j // j ≠ i} → K) (x : {x : σ → K // x ∘ coe = x₀}), ∏ j, (x : σ → K) j ^ d j :
              (fintype.sum_fiberwise _ _).symm
    ... = 0 : fintype.sum_eq_zero _ _,
  intros x₀,
  let e : K ≃ {x // x ∘ coe = x₀} := (equiv.cofiber _).symm,
  calc (∑ x : {x : σ → K // x ∘ coe = x₀}, ∏ j, (x : σ → K) j ^ d j)
        = ∑ a : K, ∏ j : σ, (e a : σ → K) j ^ d j : (finset.sum_equiv e _).symm
    ... = ∑ a : K, (∏ j, x₀ j ^ d j) * a ^ d i    : fintype.sum_congr _ _ _
    ... = (∏ j, x₀ j ^ d j) * ∑ a : K, a ^ d i    : by rw mul_sum
    ... = 0                                       : by rw [sum_pow_lt_card_sub_one _ hi, mul_zero],
  intros a,
  let e' : {j // j = i} ⊕ {j // j ≠ i} ≃ σ := equiv.sum_compl _,
  calc (∏ j : σ, (e a : σ → K) j ^ d j)
        = (e a : σ → K) i ^ d i * (∏ (j : {j // j ≠ i}), (e a : σ → K) j ^ d j) :
        by { rw [← finset.prod_equiv e', fintype.prod_sum_type, univ_unique, prod_singleton], refl }
    ... = a ^ d i * (∏ (j : {j // j ≠ i}), (e a : σ → K) j ^ d j) : by rw equiv.cofiber_symm_apply_eq
    ... = a ^ d i * (∏ j, x₀ j ^ d j) : congr_arg _ (fintype.prod_congr _ _ _) -- see below
    ... = (∏ j, x₀ j ^ d j) * a ^ d i : mul_comm _ _,
  { -- the remaining step of the calculation above
    rintros ⟨j, hj⟩,
    show (e a : σ → K) j ^ d j = x₀ ⟨j, hj⟩ ^ d j,
    rw equiv.cofiber_symm_apply_ne, }
end

variables [decidable_eq K] [decidable_eq σ]

/-- The Chevalley–Warning theorem.
Let `(f i)` be a finite family of multivariate polynomials
in finitely many variables (`X s`, `s : σ`) over a finite field of characteristic `p`.
Assume that the sum of the total degrees of the `f i` is less than the cardinality of `σ`.
Then the number of common solutions of the `f i` is divisible by `p`. -/
theorem char_dvd_card_solutions_family (p : ℕ) [char_p K p]
  {ι : Type*} {s : finset ι} {f : ι → mv_polynomial σ K}
  (h : (∑ i in s, (f i).total_degree) < fintype.card σ) :
  p ∣ fintype.card {x : σ → K // ∀ i ∈ s, (f i).eval x = 0} :=
begin
  have hq : 0 < q - 1, { rw [← card_units, fintype.card_pos_iff], exact ⟨1⟩ },
  let S : finset (σ → K) := { x ∈ univ | ∀ i ∈ s, (f i).eval x = 0 },
  have hS : ∀ (x : σ → K), x ∈ S ↔ ∀ (i : ι), i ∈ s → eval x (f i) = 0,
  { intros x, simp only [S, true_and, sep_def, mem_filter, mem_univ], },
  /- The polynomial `F = ∏ i in s, (1 - (f i)^(q - 1))` has the nice property
  that it takes the value `1` on elements of `{x : σ → K // ∀ i ∈ s, (f i).eval x = 0}`
  while it is `0` outside that locus.
  Hence the sum of its values is equal to the cardinality of
  `{x : σ → K // ∀ i ∈ s, (f i).eval x = 0}` modulo `p`. -/
  let F : mv_polynomial σ K := ∏ i in s, (1 - (f i)^(q - 1)),
  have hF : ∀ x, F.eval x = if x ∈ S then 1 else 0,
  { intro x,
    calc F.eval x = ∏ i in s, (1 - f i ^ (q - 1)).eval x : eval_prod s _ x
              ... = if x ∈ S then 1 else 0 : _,
    simp only [eval_sub, eval_pow, eval_one],
    split_ifs with hx hx,
    { apply finset.prod_eq_one,
      intros i hi,
      rw hS at hx,
      rw [hx i hi, zero_pow hq, sub_zero], },
    { obtain ⟨i, hi, hx⟩ : ∃ (i : ι), i ∈ s ∧ (f i).eval x ≠ 0,
      { simpa only [hS, classical.not_forall, classical.not_imp] using hx },
      apply finset.prod_eq_zero hi,
      rw [pow_card_sub_one_eq_one ((f i).eval x) hx, sub_self], } },
  -- In particular, we can now show:
  have key : ∑ x, F.eval x = fintype.card {x : σ → K // ∀ i ∈ s, (f i).eval x = 0},
  rw [fintype.card_of_subtype S hS, card_eq_sum_ones, sum_nat_cast, nat.cast_one,
      ← fintype.sum_extend_by_zero S, sum_congr rfl (λ x hx, hF x)],
  -- With these preparations under our belt, we will approach the main goal.
  show p ∣ fintype.card {x // ∀ (i : ι), i ∈ s → (f i).eval x = 0},
  rw [← char_p.cast_eq_zero_iff K, ← key],
  show ∑ x, F.eval x = 0,
  -- We are now ready to apply the main machine, proven before.
  apply F.sum_mv_polynomial_eq_zero,
  -- It remains to verify the crucial assumption of this machine
  show F.total_degree < (q - 1) * fintype.card σ,
  calc F.total_degree ≤ ∑ i in s, (1 - (f i)^(q - 1)).total_degree : total_degree_finset_prod s _
                  ... ≤ ∑ i in s, (q - 1) * (f i).total_degree     : sum_le_sum $ λ i hi, _ -- see ↓
                  ... = (q - 1) * (∑ i in s, (f i).total_degree)   : mul_sum.symm
                  ... < (q - 1) * (fintype.card σ)                 : by rwa mul_lt_mul_left hq,
  -- Now we prove the remaining step from the preceding calculation
  show (1 - f i ^ (q - 1)).total_degree ≤ (q - 1) * (f i).total_degree,
  calc (1 - f i ^ (q - 1)).total_degree
        ≤ max (1 : mv_polynomial σ K).total_degree (f i ^ (q - 1)).total_degree : total_degree_sub _ _
    ... ≤ (f i ^ (q - 1)).total_degree : by simp only [max_eq_right, nat.zero_le, total_degree_one]
    ... ≤ (q - 1) * (f i).total_degree : total_degree_pow _ _
end

/-- The Chevalley–Warning theorem.
Let `f` be a multivariate polynomial in finitely many variables (`X s`, `s : σ`)
over a finite field of characteristic `p`.
Assume that the total degree of `f` is less than the cardinality of `σ`.
Then the number of solutions of `f` is divisible by `p`.
See `char_dvd_card_solutions_family` for a version that takes a family of polynomials `f i`. -/
theorem char_dvd_card_solutions (p : ℕ) [char_p K p]
  {f : mv_polynomial σ K} (h : f.total_degree < fintype.card σ) :
  p ∣ fintype.card {x : σ → K // f.eval x = 0} :=
begin
  let F : unit → mv_polynomial σ K := λ _, f,
  have : ∑ i : unit, (F i).total_degree < fintype.card σ,
  { simpa only [fintype.univ_punit, sum_singleton] using h, },
  have key := char_dvd_card_solutions_family p this,
  simp only [F, fintype.univ_punit, forall_eq, mem_singleton] at key,
  convert key,
end

end finite_field
