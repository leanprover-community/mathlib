/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.nat.prime
import data.nat.totient
import algebra.periodic
import data.finset.locally_finite
import data.nat.count


/-!
# The Prime Counting Function

In this file we define the prime counting function: the function on natural numbers that returns
the number of primes less than or equal to its input.

## Main Results

The main definitions for this file are

- `prime_counting`: The prime counting function π
- `prime_counting'`: π(n - 1)

We then prove that these are monotone. The last main theorem is an upper bound on `π'` which arises
by observing that all numbers greater than `k` and not coprime to `k` are not prime, and so only at
most `φ(k)/k` fraction of the numbers from `k` to `n` are prime.

## Notation

We use the standard notation `π` to represent the prime counting function (and `π'` to represent
the reindexed version).

-/

namespace nat
open finset

/--
A variant of the traditional prime counting function which gives the number of primes
*strictly* less than the input. More convenient for avoiding off-by-one errors.
-/
def prime_counting' : ℕ → ℕ := nat.count prime

/-- The prime counting function: Returns the number of primes less than or equal to the input. -/
def prime_counting (n : ℕ) : ℕ := prime_counting' (n + 1)

localized "notation `π` := nat.prime_counting" in nat
localized "notation `π'` := nat.prime_counting'" in nat

lemma monotone_prime_counting' : monotone prime_counting' := count_monotone prime

lemma monotone_prime_counting : monotone prime_counting :=
λ a b a_le_b, monotone_prime_counting' (add_le_add_right a_le_b 1)

private lemma Ico_filter_coprime_le (a k n : ℕ) (a_pos : 0 < a) :
  ((Ico k (k + n)).filter (coprime a)).card ≤ totient a * (n / a + 1) :=
begin
  conv_lhs { rw ←nat.mod_add_div n a },
  induction n / a with i ih,
  { simp only [zero_add, mul_one, mul_zero, le_of_lt (mod_lt n a_pos)],
    transitivity (filter a.coprime (Ico k (k + a))).card,
    { mono,
      refine monotone_filter_left a.coprime _,
      simp only [add_zero, finset.le_eq_subset],
      rw finset.subset_iff,
      intro x,
      simp only [and_imp, mem_Ico],
      intros h1 h2,
      refine ⟨h1, _⟩,
      linarith only [h2, mod_lt n a_pos], },
    { rw filter_coprime_Ico_eq_totient, }, },
  simp only [mul_succ],
  simp_rw ←add_assoc at ih ⊢,
  calc (filter a.coprime (Ico k (k + n % a + a * i + a))).card
      ≤ (filter a.coprime (Ico k (k + n % a + a * i)
                            ∪ Ico (k + n % a + a * i) (k + n % a + a * i + a))).card :
        begin
          apply card_le_of_subset,
          apply filter_subset_filter,
          rw [subset_iff],
          simp only [mem_Ico, and_imp, mem_union],
          intros x h1 h2,
          by_cases h : x < k + n % a + a * i,
          { left,
            exact ⟨h1, h⟩, },
          { right,
            exact ⟨le_of_not_lt h, h2⟩, },
        end
  ... ≤ (filter a.coprime (Ico k (k + n % a + a * i))).card + a.totient :
        begin
          rw [filter_union, ←filter_coprime_Ico_eq_totient a (k + n % a + a * i)],
          apply card_union_le,
        end
  ... ≤ a.totient * i + a.totient + a.totient : add_le_add_right ih (totient a),
end

/-- A linear upper bound on the size of the `prime_counting'` function -/
lemma prime_counting'_add_le (n k a : ℕ) (h0 : 0 < a) (h1 : a < k) :
  π' (k + n) ≤ π' k + nat.totient a * (n / a + 1) :=
calc π' (k + n)
    ≤ ((range k).filter (prime)).card + ((Ico k (k + n)).filter (prime)).card :
        begin
          rw [prime_counting', count_eq_card_filter_range, range_eq_Ico,
              ←Ico_union_Ico_eq_Ico (zero_le k) (le_self_add), filter_union],
          apply card_union_le,
        end
... ≤ π' k + ((Ico k (k + n)).filter (prime)).card :
        by rw [prime_counting', count_eq_card_filter_range]
... ≤ π' k + ((Ico k (k + n)).filter (coprime a)).card :
        begin
          refine add_le_add_left (card_le_of_subset _) k.prime_counting',
          simp only [subset_iff, and_imp, mem_filter, mem_Ico],
          intros p succ_k_le_p p_lt_n p_prime,
          split,
          { exact ⟨succ_k_le_p, p_lt_n⟩, },
          { rw coprime_comm,
            exact coprime_of_lt_prime h0 (gt_of_ge_of_gt succ_k_le_p h1) p_prime, },
        end
... ≤ π' k + totient a * (n / a + 1) :
        begin
          rw [add_le_add_iff_left],
          exact filter_coprime_bound a k n h0,
        end


end nat
