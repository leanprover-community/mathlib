/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/

import algebra.big_operators.fin
import algebra.big_operators.order
import data.nat.choose.sum
import data.nat.factorial.big_operators
import data.fin.vec_notation
import data.finset.sym
import data.finsupp.multiset

import tactic.linarith

/-!
# Multinomial

This file defines the multinomial coefficient and several small lemma's for manipulating it.

## Main declarations

- `nat.multinomial`: the multinomial coefficient

## Main results

- `nat.multinomial_theorem`: The expansion of `(s.sum x) ^ n` using multinomial coefficients

-/

open_locale big_operators nat
open_locale big_operators

namespace nat

variables {α : Type*} (s : finset α) (f : α → ℕ) {a b : α} (n : ℕ)

/-- The multinomial coefficient. Gives the number of strings consisting of symbols
from `s`, where `c ∈ s` appears with multiplicity `f c`.

Defined as `(∑ i in s, f i)! / ∏ i in s, (f i)!`.
-/
def multinomial : ℕ := (∑ i in s, f i)! / ∏ i in s, (f i)!

lemma multinomial_pos : 0 < multinomial s f := nat.div_pos
  (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f)) (prod_factorial_pos s f)

lemma multinomial_spec : (∏ i in s, (f i)!) * multinomial s f = (∑ i in s, f i)! :=
nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)

@[simp] lemma multinomial_nil : multinomial ∅ f = 1 := rfl

@[simp] lemma multinomial_singleton : multinomial {a} f = 1 :=
by simp [multinomial, nat.div_self (factorial_pos (f a))]

@[simp] lemma multinomial_insert_one [decidable_eq α] (h : a ∉ s) (h₁ : f a = 1) :
  multinomial (insert a s) f = (s.sum f).succ * multinomial s f :=
begin
  simp only [multinomial, one_mul, factorial],
  rw [finset.sum_insert h, finset.prod_insert h, h₁, add_comm, ←succ_eq_add_one, factorial_succ],
  simp only [factorial_one, one_mul, function.comp_app, factorial],
  rw nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _),
end

lemma multinomial_insert [decidable_eq α] (h : a ∉ s) :
  multinomial (insert a s) f = (f a + s.sum f).choose (f a) * multinomial s f :=
begin
  rw choose_eq_factorial_div_factorial (le.intro rfl),
  simp only [multinomial, nat.add_sub_cancel_left, finset.sum_insert h, finset.prod_insert h,
    function.comp_app],
  rw [div_mul_div_comm ((f a).factorial_mul_factorial_dvd_factorial_add (s.sum f))
    (prod_factorial_dvd_factorial_sum _ _), mul_comm (f a)! (s.sum f)!, mul_assoc,
    mul_comm _ (s.sum f)!, nat.mul_div_mul _ _ (factorial_pos _)],
end

lemma multinomial_congr {f g : α → ℕ} (h : ∀ a ∈ s, f a = g a) :
  multinomial s f = multinomial s g :=
begin
  simp only [multinomial], congr' 1,
  { rw finset.sum_congr rfl h },
  { exact finset.prod_congr rfl (λ a ha, by rw h a ha) },
end

/-! ### Connection to binomial coefficients -/

lemma binomial_eq [decidable_eq α] (h : a ≠ b) :
  multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) :=
by simp [multinomial, finset.sum_pair h, finset.prod_pair h]

lemma binomial_eq_choose [decidable_eq α] (h : a ≠ b) :
  multinomial {a, b} f = (f a + f b).choose (f a) :=
by simp [binomial_eq _ h, choose_eq_factorial_div_factorial (nat.le_add_right _ _)]

lemma binomial_spec [decidable_eq α] (hab : a ≠ b) :
  (f a)! * (f b)! * multinomial {a, b} f = (f a + f b)! :=
by simpa [finset.sum_pair hab, finset.prod_pair hab] using multinomial_spec {a, b} f

@[simp] lemma binomial_one [decidable_eq α] (h : a ≠ b) (h₁ : f a = 1) :
  multinomial {a, b} f = (f b).succ :=
by simp [multinomial_insert_one {b} f (finset.not_mem_singleton.mpr h) h₁]

lemma binomial_succ_succ [decidable_eq α] (h : a ≠ b) :
  multinomial {a, b} ((f.update a (f a).succ).update b (f b).succ) =
  multinomial {a, b} (f.update a (f a).succ) +
  multinomial {a, b} (f.update b (f b).succ) :=
begin
  simp only [binomial_eq_choose, function.update_apply, function.update_noteq,
    succ_add, add_succ, choose_succ_succ, h, ne.def, not_false_iff, function.update_same],
  rw if_neg h.symm,
  ring,
end

lemma succ_mul_binomial [decidable_eq α] (h : a ≠ b) :
  (f a + f b).succ * multinomial {a, b} f =
  (f a).succ * multinomial {a, b} (f.update a (f a).succ) :=
begin
  rw [binomial_eq_choose _ h, binomial_eq_choose _ h, mul_comm (f a).succ,
    function.update_same, function.update_noteq (ne_comm.mp h)],
  convert succ_mul_choose_eq (f a + f b) (f a),
  exact succ_add (f a) (f b),
end

/-! ### Simple cases -/

lemma multinomial_univ_two (a b : ℕ) : multinomial finset.univ ![a, b] = (a + b)! / (a! * b!) :=
by simp [multinomial, fin.sum_univ_two, fin.prod_univ_two]

lemma multinomial_univ_three (a b c : ℕ) : multinomial finset.univ ![a, b, c] =
  (a + b + c)! / (a! * b! * c!) :=
by simp [multinomial, fin.sum_univ_three, fin.prod_univ_three]

end nat

/-! ### Alternative definitions -/

namespace finsupp

variables {α : Type*}

/-- Alternative multinomial definition based on a finsupp, using the support
  for the big operations
-/
def multinomial (f : α →₀ ℕ) : ℕ := (f.sum $ λ _, id)! / f.prod (λ _ n, n!)

lemma multinomial_eq (f : α →₀ ℕ) : f.multinomial = nat.multinomial f.support f := rfl

lemma multinomial_update (a : α) (f : α →₀ ℕ) :
  f.multinomial = (f.sum $ λ _, id).choose (f a) * (f.update a 0).multinomial :=
begin
  simp only [multinomial_eq],
  classical,
  by_cases a ∈ f.support,
  { rw [← finset.insert_erase h, nat.multinomial_insert _ f (finset.not_mem_erase a _),
      finset.add_sum_erase _ f h, support_update_zero], congr' 1,
    exact nat.multinomial_congr _
      (λ _ h, (function.update_noteq (finset.mem_erase.1 h).1 0 f).symm) },
  rw not_mem_support_iff at h,
  rw [h, nat.choose_zero_right, one_mul, ← h, update_self],
end

end finsupp

namespace multiset

variables {α : Type*}

/-- Alternative definition of multinomial based on `multiset` delegating to the
  finsupp definition
-/
noncomputable def multinomial (m : multiset α) : ℕ := m.to_finsupp.multinomial

lemma multinomial_filter_ne [decidable_eq α] (a : α) (m : multiset α) :
  m.multinomial = m.card.choose (m.count a) * (m.filter ((≠) a)).multinomial :=
begin
  dsimp only [multinomial],
  convert finsupp.multinomial_update a _,
  { rw [← finsupp.card_to_multiset, m.to_finsupp_to_multiset] },
  { ext1 a', rw [to_finsupp_apply, count_filter, finsupp.coe_update],
    split_ifs,
    { rw [function.update_noteq h.symm, to_finsupp_apply] },
    { rw [not_ne_iff.1 h, function.update_same] } },
end

end multiset

namespace nat

/-! ### Multinomial theorem -/

variables {α : Type*} (s : finset α)

open finset
/--
  The multinomial theorem

  Proof is by induction on the number of summands.
-/
theorem finset.sum_pow [decidable_eq α] {R : Type*} [comm_semiring R] (x : α → R) :
  ∀ n, (s.sum x) ^ n = ∑ k in s.sym n, k.val.multinomial * (k.val.map x).prod :=
begin
  induction s using finset.induction with a s ha ih,
  { rw sum_empty,
    rintro (_ | n),
    { rw [pow_zero, sum_unique_nonempty],
      { convert (one_mul _).symm, apply nat.cast_one },
      { apply univ_nonempty } },
    { rw [pow_succ, zero_mul, sym_empty, sum_empty] } },
  intro n,
  simp_rw [sum_insert ha, add_pow, sum_range, ih, mul_sum, sum_mul, sum_sigma'],
  refine (sum_bij' (λ m _, sym.filter_ne a m) (λ m hm, mem_sigma.2 ⟨mem_univ _, _⟩)
    (λ m hm, _) (λ m _, m.2.fill a m.1) _ (λ m _, m.fill_filter_ne a) (λ m hm, _)).symm,
  { convert sym_filter_ne_mem a hm, rw erase_insert ha },
  { rw [m.1.multinomial_filter_ne a],
    dsimp only [sym.filter_ne, fin.coe_mk],
    conv in (m.1.map _) { rw [← m.1.filter_add_not ((=) a), multiset.map_add] },
    rw [multiset.prod_add, m.1.filter_eq, multiset.map_repeat, multiset.prod_repeat, m.2],
    rw [nat.cast_mul, mul_assoc, mul_comm],
    congr' 1, apply mul_left_comm },
  { exact λ m hm, sym_fill_mem a (mem_sigma.1 hm).2 },
  { exact sym.filter_ne_fill a m (mt (mem_sym_iff.1 (mem_sigma.1 hm).2 a) ha) },
end

end nat
