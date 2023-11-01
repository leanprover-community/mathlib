/-
Copyright (c) 2022 Bolton Bailey, Sean Golinski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Sean Golinski
-/

import data.fintype.basic
import group_theory.order_of_element
import tactic.zify
import data.nat.totient
import data.zmod.basic
import field_theory.finite.basic
import data.fintype.basic
import algebra.big_operators.intervals
import algebra.is_prime_pow

/-!
# Lemmas and definitions that will be used in proving the Miller-Rabin primality test.

Since we only need to test odd numbers for primality, let `n-1 = 2^e * k`, where
`e := (n-1).factorization 2` and `k := odd_part (n-1)`. Then we can factor the polynomial
`x^(n-1) - 1 = x^(2^e * k) - 1 = (x^k - 1) *  ∏ i in Ico 0 e, (x^(2^i * k) + 1)`.
For prime `n` and any `0 < x < n`, Fermat's Little Theorem gives `x^(n-1) - 1 = 0 (mod n)`,
so we have either `(x^k - 1) = 0 (mod n)` or `(x^(2^i * k) + 1) = 0 (mod n)` for some `0 ≤ i < e`.
Conversely, then, if there is an `0 < a < n` such that `(a^k - 1) ≠ 0 (mod n)` and
`(a^(2^i * k) + 1) ≠ 0 (mod n)` for all `0 ≤ i < e` then this demonstrates that `n` is not prime.
Such an `a` is called a **Miller–Rabin witness** for `n`.

Of course, the existence of a witness can only demonstrate that `n` is not prime. But if we check
several candidates — i.e. several numbers `0 < a < n` — and find that none of them are witnesses
then this increases our confidence that `n` is a prime. This confidence is supported by the
theorem that for any odd composite `n`, at least 3/4 of numbers `1 < a < n-1` are witnesses for `n`.
Thus if `n` is not a prime there is a high probability that randomly sampling these numbers will
produce a witness. For any given confidence threshold `P < 100%` we can repeatedly sample until
the probability of finding a witness (if one exists) is at least `P`. This is the essence of the
Miller-Rabin primality test.

-- TODO add reference to [this](https://kconrad.math.uconn.edu/blurbs/ugradnumthy/millerrabin.pdf)

-/

open nat finset zmod

open_locale big_operators
-- open_locale classical

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
-- Lemmas to PR elsewhere
---------------------------------------------------------------------------------------------------
lemma nat.succ_sub_self (x : ℕ) : x.succ - x = 1 :=
by simp [succ_sub rfl.le]

lemma square_roots_of_one {p : ℕ} [fact (p.prime)] {x : zmod p} (root : x^2 = 1) :
  x = 1 ∨ x = -1 :=
begin
  have diffsquare : (x + 1) * (x - 1) = 0, { ring_nf, simp [root] },
  have zeros : (x + 1 = 0) ∨ (x - 1 = 0) := mul_eq_zero.1 diffsquare,
  cases zeros with zero1 zero2,
  { right, exact eq_neg_of_add_eq_zero_left zero1 },
  { left, exact sub_eq_zero.mp zero2 },
end

/-- If an odd prime power `p^α` divides `x^2 - 1` then it divides `x-1` or `x+1`. -/
lemma square_roots_of_one_nat {p α x : ℕ} (pp : p.prime) (hp_odd : odd p) (root : p^α ∣ x^2 - 1) :
  (p^α ∣ x - 1) ∨ (p^α ∣ x + 1) :=
begin
  rcases x.eq_zero_or_pos with rfl | hx0, { simp },
  have diffsquare : p^α ∣ (x + 1) * (x - 1), { rw ←nat.sq_sub_sq, simpa },

  have h2 : ¬ p ∣ (x + 1) ∨ ¬ p ∣ (x - 1),
  { rw ←not_and_distrib,
    rintro ⟨hp1, hp2⟩,
    have h3 : p ∣ (x+1) - (x-1), { refine nat.dvd_sub _ hp1 hp2, linarith },
    have h4 : (x+1) - (x-1) = 2,
    { cases x, { cases hx0 },
      rw [succ_sub_succ_eq_sub, tsub_zero, nat.sub_add_comm (le_succ x), succ_sub rfl.le],
      simp },
    rw [h4, (nat.prime_dvd_prime_iff_eq pp prime_two)] at h3,
    rw [h3, odd_iff_not_even] at hp_odd,
    exact hp_odd even_two },

  cases h2 with h_plus h_minus,
  { left, exact (prime_iff.mp pp).pow_dvd_of_dvd_mul_left α h_plus diffsquare },
  { right, exact (prime_iff.mp pp).pow_dvd_of_dvd_mul_right α h_minus diffsquare },
end

/-- If an odd prime power `p^α` divides `x^2 - 1` then it divides `x-1` or `x+1`. -/
lemma square_roots_of_one_int {p α : ℕ} {x : ℤ} (pp : p.prime) (hp_odd : odd p)
  (root : ↑p^α ∣ x^2 - 1) :
  (↑p^α ∣ x - 1) ∨ (↑p^α ∣ x + 1) :=
begin
  have pp' := prime_iff_prime_int.1 pp,
  have diffsquare : ↑(p^α) ∣ (x-1) * (x+1), { ring_nf, simp [root] },
  have h2 : ¬ ↑p ∣ (x + 1) ∨ ¬ ↑p ∣ (x - 1),
  { rw ←not_and_distrib,
    rintro ⟨hp1, hp2⟩,
    have h3 : ↑p ∣ (x+1) - (x-1), { exact dvd_sub hp1 hp2 },
    have h4 : (x+1) - (x-1) = 2, { ring },
    rw h4 at h3,
    rw (show (2:ℤ) = 2*1^2, by linarith) at h3,
    have := prime_two_or_dvd_of_dvd_two_mul_pow_self_two pp h3,
    simp [pp.ne_one] at this,
    rw [this, odd_iff_not_even] at hp_odd,
    exact hp_odd even_two },
  cases h2 with h_plus h_minus,
  { left, apply prime.pow_dvd_of_dvd_mul_left pp' α h_plus, simpa [mul_comm] using diffsquare },
  { right, apply prime.pow_dvd_of_dvd_mul_right pp' α h_minus, simpa [mul_comm] using diffsquare },
end

/-- If `x : zmod (p^α)` (for odd prime `p`) satisfies `x^2 = 1` then `x = 1 ∨ x = -1` -/
lemma square_roots_of_one_zmod {p α : ℕ} (pp : p.prime) (hp_odd : odd p) {x : zmod (p^α)}
  (root : x^2 = 1) :
  x = 1 ∨ x = -1 :=
begin
  refine or.imp (λ h, _) (λ h, _) (@square_roots_of_one_int p α ↑x pp hp_odd _ ),
  { have := (int_coe_eq_int_coe_iff_dvd_sub 1 (x) (p^α)).2,
    push_cast at this,
    simp [this h] },
  { have := (int_coe_eq_int_coe_iff_dvd_sub (-1) (x) (p^α)).2,
    push_cast at this,
    simp [this h] },
  { have := (int_coe_eq_int_coe_iff_dvd_sub 1 (x^2) (p^α)).1,
    push_cast at this,
    apply this,
    simp [root.symm] },
end


lemma nat.even_two_pow_iff (n : ℕ) : even (2 ^ n) ↔ 0 < n :=
⟨λ h, zero_lt_iff.2 (even_pow.1 h).2, λ h, (even_pow' h.ne').2 even_two⟩

lemma even_not_dvd_odd {e o : ℕ} (he : even e) (ho : odd o) : ¬ e ∣ o :=
begin
  rintro ⟨d, hd⟩,
  rw [hd, odd_iff_not_even] at ho,
  cases ho (even.mul_right he d),
end

lemma sub_one_dvd_pow_sub_one (p a : ℕ) (hp_pos : 0 < p) : (p - 1) ∣ (p ^ a - 1) :=
begin
  induction a with a IH, { simp },
  rcases IH with ⟨c, hc⟩,
  use p^a + c,
  rw [pow_succ, mul_add, ←hc, tsub_mul, one_mul],
  apply tsub_eq_of_eq_add,
  rw add_assoc,
  have h1 : 1 ≤ p ^ a,
  { exact succ_le_iff.2 (pow_pos hp_pos a) },
  have h2 : p ^ a ≤ p * p ^ a,
  { exact (le_mul_iff_one_le_left (pow_pos hp_pos a)).2 (succ_le_iff.2 hp_pos) },
  rw tsub_add_cancel_of_le h1,
  rw tsub_add_cancel_of_le h2,
end

lemma coprime_succ (b : ℕ) : (b + 1).coprime b :=
by simp [nat.coprime_self_add_left]

lemma coprime_self_sub_one (a : ℕ) (ha : 0 < a) : a.coprime (a - 1) :=
begin
  nth_rewrite_lhs 0 ←tsub_add_cancel_of_le (succ_le_iff.2 ha),
  apply coprime_succ,
end

theorem nat.sq_sub_sq' (a b : ℕ) : a ^ 2 - b ^ 2 = (a - b) * (a + b) :=
by { rw [mul_comm, nat.sq_sub_sq] }

lemma factorise_pow_two_pow_sub_one (x m : ℕ) :
  x^(2^m) - 1 = (x - 1) *  ∏ i in Ico 0 m, (x^(2^i) + 1) :=
begin
  induction m with m IH, { simp },
  rcases eq_or_ne m 0 with rfl | he0, { simpa using nat.sq_sub_sq' x 1 },
  rw [pow_succ, Ico_succ_right_eq_insert_Ico zero_le', prod_insert right_not_mem_Ico],
  nth_rewrite_rhs 0 ←mul_assoc,
  nth_rewrite_rhs 0 ←mul_rotate,
  nth_rewrite_rhs 1 mul_comm,
  rw [←IH, ←nat.sq_sub_sq', one_pow, ←pow_mul, mul_comm],
end

-- TODO: Find a better name for this!
protected
lemma factorize_poly (x k e : ℕ) :
  x ^ (2^e * k) - 1 = (x^k - 1) *  ∏ i in Ico 0 e, (x^(2^i * k) + 1) :=
begin
  rw [mul_comm, pow_mul, factorise_pow_two_pow_sub_one (x^k) e],
  apply congr_arg,
  simp_rw [←pow_mul, mul_comm],
end

-- TODO: Find a better name for this!
protected
lemma factorize_poly' {R : Type*} [comm_ring R] (a : R) (k e : ℕ) :
  a ^ (2^e * k) - 1 = (a^k - 1) *  ∏ i in Ico 0 e, (a^(2^i * k) + 1) :=
begin
  simp_rw [mul_comm, pow_mul],
  set x := a^k with hx,
  induction e with m IH, { simp },
  rcases eq_or_ne m 0 with rfl | he0, { simp [mul_comm, ←sq_sub_sq x 1] },

  rw [pow_succ, Ico_succ_right_eq_insert_Ico zero_le', prod_insert right_not_mem_Ico],
  nth_rewrite_rhs 0 ←mul_assoc,
  nth_rewrite_rhs 0 ←mul_rotate,
  nth_rewrite_rhs 1 mul_comm,
  rw [←IH],
  rw [mul_comm, pow_mul, mul_comm],
  simpa using sq_sub_sq (x ^ 2 ^ m) 1,
end

lemma factorization_two_pos_of_even_of_pos {n : ℕ} (hn : even n) (hn0 : n ≠ 0) :
  0 < n.factorization 2 :=
begin
  rcases hn with ⟨k, rfl⟩,
  simp only [ne.def, add_self_eq_zero] at hn0,
  rw ←two_mul,
  simp [nat.factorization_mul _ hn0, prime_two.factorization],
end

lemma factorization_two_pos_sub_one {n : ℕ} (hn : odd n) (hn1 : n ≠ 1) :
  0 < (n - 1).factorization 2 :=
begin
  rcases hn with ⟨k, rfl⟩,
  simp only [ne.def, add_left_eq_self, nat.mul_eq_zero, bit0_eq_zero, nat.one_ne_zero, false_or]
    at hn1,
  simp [nat.factorization_mul _ hn1, prime_two.factorization],
end

-- TODO: Re-write the definition of MR_witness to remove the need for this
lemma pow_mul_eq_pow_pow_comm {n : ℕ} (a b : ℕ) (x : zmod n) : x ^ (a * b) = (x ^ b) ^ a :=
begin
  rw [←pow_mul, mul_comm],
end
---------------------------------------------------------------------------------------------------
-- PR'ed in #15793
---------------------------------------------------------------------------------------------------
lemma ord_compl_dvd_ord_compl_of_dvd {a b p : ℕ} (hab : a ∣ b) :
  ord_compl[p] a ∣ ord_compl[p] b :=
begin
  rcases em' p.prime with pp | pp, { simp [pp, hab] },
  rcases eq_or_ne b 0 with rfl | hb0, { simp },
  rcases eq_or_ne a 0 with rfl | ha0, { cases hb0 (zero_dvd_iff.1 hab) },
  have ha := (nat.div_pos (ord_proj_le p ha0) (ord_proj_pos a p)).ne',
  have hb := (nat.div_pos (ord_proj_le p hb0) (ord_proj_pos b p)).ne',
  rw [←factorization_le_iff_dvd ha hb, factorization_ord_compl a p, factorization_ord_compl b p],
  intro q,
  rcases eq_or_ne q p with rfl | hqp, { simp },
  simp_rw finsupp.erase_ne hqp,
  exact (factorization_le_iff_dvd ha0 hb0).2 hab q,
end

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
lemma nat.mul_pow_pred (k a : ℕ) (hk0 : k ≠ 0) : a * a ^ (k - 1) = a ^ k :=
begin
  nth_rewrite_lhs 0 ←pow_one a,
  rw ←pow_add,
  rw add_comm,
  rw tsub_add_cancel_of_le (one_le_iff_ne_zero.mpr hk0),
end


lemma zmod.mul_pow_pred (n k : ℕ) (hk0 : k ≠ 0) (a : zmod n) : a * a ^ (k - 1) = a ^ k :=
begin
  nth_rewrite_lhs 0 ←pow_one a,
  rw ←pow_add,
  rw add_comm,
  rw tsub_add_cancel_of_le (one_le_iff_ne_zero.mpr hk0),
end

-- TODO: Convenience lemma; Re-write the definition of MR_witness to remove the need for this
lemma nat.pow_mul_eq_pow_pow_comm (a b x : ℕ) : x ^ (a * b) = (x ^ b) ^ a :=
begin
  rw [←pow_mul, mul_comm],
end
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
/-- If `x = 1 (mod m)` then `x = 1 (mod d)` for any `d ∣ m`. -/
lemma zmod.eq_one_of_eq_one_modulus_dvd {d m : ℕ} (hpm : d ∣ m) [fact (1 < d)] [fact (1 < m)]
  {x : ℕ} (h : (x : zmod m) = 1) :
  (x : zmod d) = 1 :=
begin
  simp only [zmod.nat_coe_zmod_eq_iff, zmod.val_one] at h ⊢,
  cases h with k hk,
  cases hpm with d hd,
  rw [hk, hd, mul_assoc],
  use (d*k),
end

/-- If `x = -1 (mod m)` then `x = -1 (mod d)` for any `d ∣ m`. -/
lemma zmod.eq_neg_one_of_eq_neg_one_modulus_dvd {d m : ℕ} (hpm : d ∣ m) {x : ℕ}
  (h : (x : zmod m) = -1) :
  (x : zmod d) = -1 :=
begin
  have h' : (x : zmod m) + 1 = 0, { rw h, simp },
  suffices : (x : zmod d) + 1 = 0,
  { have : (x : zmod d) + 1 - 1 = -1, { rw this, simp },
    simpa using this },
  norm_cast at *,
  rw zmod.nat_coe_zmod_eq_zero_iff_dvd at *,
  exact dvd_trans hpm h',
end
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

/-- Version of Lagrange's theorem using the formalism of a closed subset.
If `α` is a finite group and `s : finset α` is closed under multiplication and inverses and
contains `1 : α`, then `|s|` divides `|α|`.
-/
lemma card_closed_subset_dvd_card {α : Type} [fintype α] [group α] (s : finset α)
  (closed_under_mul : ∀ a b ∈ s, a * b ∈ s) (closed_under_inv : ∀ a ∈ s, a⁻¹ ∈ s)
  (id_mem : (1 : α) ∈ s)  :
  finset.card s ∣ fintype.card α :=
begin
  let s_subgroup : subgroup α := subgroup.mk (s : set α) _ id_mem closed_under_inv,
  swap, { intros a b ha hb, simp only [finset.mem_coe] at *, solve_by_elim },
  classical,
  suffices : s.card = fintype.card s_subgroup,
  { rw this, convert subgroup.card_subgroup_dvd_card s_subgroup },
  refine (fintype.card_of_finset' _ (λ x, _)).symm,
  trivial,
end

noncomputable
instance fintype.of_subgroup {G : Type} [fintype G] [group G] {H : subgroup G} : fintype H :=
fintype.of_finite ↥H

/-- The cardinality of any proper subgroup `H` of `G` is at most half that of `G`. -/
lemma card_le_half_of_proper_subgroup {G : Type} [fintype G] [group G] {H : subgroup G}
  (x : G) (proper : x ∉ H) : (fintype.card H) * 2 ≤ (fintype.card G) :=
begin
  rcases subgroup.card_subgroup_dvd_card H with ⟨index, hindex⟩,
  by_cases h0 : index = 0,
  { exfalso, apply (@fintype.card_pos G _ _).ne', simp [hindex, h0] },
  by_cases h1 : index = 1,
  { rw [h1, mul_one] at hindex,
    contrapose! proper,
    rw subgroup.eq_top_of_card_eq H hindex.symm,
    simp },
  rw hindex,
  apply mul_le_mul_left',
  by_contra,
  rw [not_le] at h,
  interval_cases index; contradiction,
end

---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------

/-! ## Lemmas about `even_part` and `odd_part` which may be factored out in a later revision -/

/-- The greatest multiple of 2 that divides `n`. -/
def even_part (n : ℕ) := ord_proj[2] n

/-- The greatest odd divisor of `n`. -/
def odd_part (n : ℕ) := ord_compl[2] n

@[simp] lemma odd_part_zero : odd_part 0 = 0 := rfl

lemma odd_of_odd_part (n : ℕ) (hn0: n ≠ 0) : odd (odd_part n) :=
begin
  rw odd_iff_not_even,
  unfold odd_part,
  intro H,
  obtain ⟨k, hk⟩ := H,
  rw ←two_mul at hk,
  apply pow_succ_factorization_not_dvd hn0 prime_two,
  rw [pow_add, pow_one, dvd_iff_exists_eq_mul_left],
  use k,
  rw [mul_rotate', mul_comm, ←hk, mul_comm, nat.mul_div_cancel' (ord_proj_dvd n 2)],
end

lemma even_part_mul_odd_part (n : ℕ) : (even_part n) * (odd_part n) = n :=
begin
  simp only [even_part, odd_part, ord_proj_mul_ord_compl_eq_self n 2],
end

lemma mul_even_part (n m : ℕ) (hn0 : n ≠ 0) (hm0 : m ≠ 0) :
  even_part (n * m) = even_part(n) * even_part(m) :=
begin
  simp only [even_part, ord_proj_mul 2 hn0 hm0],
end

lemma mul_odd_part (n m : ℕ) : odd_part (n * m) = odd_part(n) * odd_part(m) :=
begin
  simp only [odd_part, ord_compl_mul n m 2],
end

/-! ## Lemmas about Fermat witnesses and Fermat candidate-primes -/

/-- Fermat's Little Theorem (`zmod.pow_card_sub_one_eq_one`) says that for prime `p` and for all
nonzero `a : zmod p` we have `a^(p-1) = 1`.  Thus for (odd) `n : ℕ` if we have nonzero `a : zmod n`
such that `a^(n-1) ≠ 1` then this demonstrates that `n` is not prime.  Such an `a` is called a
**Fermat witness** for `n`. -/
def nat.fermat_witness (n : ℕ) (a : zmod n) : Prop := a ^ (n - 1) ≠ 1

/-- `n` is a **Fermat candidate-prime** relative to base `a : zmod n` iff `a` is not a
Fermat witness for `n`. Note that Conrad calls these "Fermat pseudoprimes", but the word
"pseudoprime" is standarly reserved for *composite* numbers that pass some primality test. -/
def fermat_cprime (n : nat) (a : zmod n) : Prop := a ^ (n - 1) = 1

lemma fermat_cprime_iff_nonwitness (n : nat) (a : (zmod n)) :
  fermat_cprime n a ↔ ¬ n.fermat_witness a :=
by simp [fermat_cprime, nat.fermat_witness]

/-- The Fermat nonwitnesses are closed under multiplication. -/
lemma fermat_nonwitness_mul (n : ℕ) {a b : zmod n}
  (ha : ¬ n.fermat_witness a) (hb : ¬ n.fermat_witness b) : ¬ n.fermat_witness (a * b) :=
begin
  simp only [nat.fermat_witness, not_not] at *,
  simp [mul_pow, ha, hb],
end

lemma fermat_nonwitness_of_prime {p : ℕ} {a : zmod p} (hp : p.prime) (ha : a ≠ 0) :
  ¬ p.fermat_witness a :=
begin
  haveI := fact_iff.2 hp,
  simp only [nat.fermat_witness, not_not, pow_card_sub_one_eq_one ha],
end

/-! ## Lemmas about Miller–Rabin witnesses and strong probable primes -/

/-- Letting `k := odd_part (n-1)`, if there is an `0 < a < n` such that `(a^k - 1) ≠ 0 (mod n)` and
`(a^(2^i * k) + 1) ≠ 0 (mod n)` for all `0 ≤ i < (n-1).factorization 2` then this demonstrates
that `n` is not prime. Such an `a` is called a **Miller–Rabin witness** for `n`. We formulate this
in terms of `a : zmod n` to take care of the bounds on `a` and the congruences `mod n`. -/
def nat.miller_rabin_witness (n : ℕ) (a : zmod n) : Prop :=
  a^odd_part (n-1) ≠ 1 ∧
  ∀ i ∈ range ((n-1).factorization 2), a^(2^i * odd_part (n-1)) ≠ -1

instance decidable_witness (n : ℕ) : decidable_pred n.miller_rabin_witness :=
λ a, and.decidable

instance decidable_witness' (n : ℕ) : decidable_pred (λ a : ℕ, n.miller_rabin_witness ↑a) :=
λ a, and.decidable

/-- `n` is a **strong probable prime** relative to base `a : zmod n` iff
`a` is not a Miller-Rabin witness for `n`. -/
def strong_probable_prime (n : nat) (a : zmod n) : Prop :=
  a^(odd_part (n-1)) = 1 ∨
  (∃ r : ℕ, r < (n-1).factorization 2 ∧ a^(2^r * odd_part(n-1)) = -1)

lemma strong_probable_prime_iff_nonwitness (n : nat) (a : (zmod n)) :
  strong_probable_prime n a ↔ ¬ n.miller_rabin_witness a :=
by simp [nat.miller_rabin_witness, strong_probable_prime, not_and_distrib]

instance {n : ℕ} {a : zmod n} : decidable (strong_probable_prime n a) := or.decidable

/-- If `a : zmod n` is a Fermat witness for `n` then it is also a Miller-Rabin witness for `n`. -/
lemma nat.miller_rabin_witness_of_fermat_witness (n : ℕ) (a : zmod n) (h : n.fermat_witness a) :
  n.miller_rabin_witness a :=
begin
  simp only [nat.miller_rabin_witness, nat.fermat_witness] at *,
  refine ⟨_, _⟩,
  { contrapose! h, rw [←even_part_mul_odd_part (n-1), mul_comm, pow_mul, h, one_pow] },
  { rintros i hi,
    rw mem_range at hi,
    rcases exists_pos_add_of_lt hi with ⟨j, hj0, hj⟩,
    contrapose! h,
    rw [←even_part_mul_odd_part (n-1)],
    rw [mul_comm, pow_mul] at *,
    rw [even_part, ←hj, pow_add, pow_mul, h],
    exact even.neg_one_pow ((nat.even_two_pow_iff j).2 hj0) },
end

/-- If there is a base `a : zmod n` relative to which `n` is a strong probable prime
then `n` is a Fermat candidate-prime relative to base `a`. -/
lemma fermat_cprime_of_strong_probable_prime (n : ℕ) (a : zmod n)
  (h : strong_probable_prime n a) : fermat_cprime n a :=
begin
  have := mt (nat.miller_rabin_witness_of_fermat_witness n a),
  rw [←fermat_cprime_iff_nonwitness, ←strong_probable_prime_iff_nonwitness] at this,
  exact this h,
end


-- A proof of `strong_probable_prime_of_prime` using the factorisation of the
-- polymomial discussed in the introduction rather than `repeated_halving_of_exponent`.
/-- Every actual prime is a `strong_probable_prime` relative to any non-zero base `a`. -/
lemma strong_probable_prime_of_prime'' (p : ℕ) (pp : p.prime) (a : zmod p) (ha0 : a ≠ 0) :
  strong_probable_prime p a :=
begin
  haveI : fact (p.prime) := fact_iff.2 pp,
  have fermat := zmod.pow_card_sub_one_eq_one ha0,
  rw [←even_part_mul_odd_part (p-1), even_part] at fermat,
  set e := (p-1).factorization 2 with he,
  set k := odd_part (p-1) with hk,
  have h1 := factorize_poly' a k e,
  simp only [fermat, sub_self, Ico_zero_eq_range, zero_eq_mul] at h1,
  apply or.imp (λ h, sub_eq_zero.mp h) (λ h, _) h1,
  rcases finset.prod_eq_zero_iff.1 h with ⟨i, hi1, hi2⟩,
  refine ⟨i, mem_range.1 hi1, _⟩,
  have : a ^ (2 ^ i * k) + 1 - 1 = -1, { simp [hi2] },
  simpa using this,
end


/-! ## Lemmas about Miller–Rabin sequences -/

/-- Letting `e := (n-1).factorization 2` and `k := odd_part (n-1)`, the **Miller-Rabin sequence**
for `n` generated by `a : zmod n` is the sequence of values `[a^k, a^2k, a^4k, ..., a^(2^(e-1)*k)]`.
Read in reverse, it is the sequence obtained by repeatedly taking the square root of
`a^(n-1) = a^(2^e * k)` until we reach an odd power of `a`.
-/
def nat.miller_rabin_sequence (n : ℕ) (a : zmod n) : list (zmod n) :=
  list.map (λ i, a^(2^i * odd_part (n-1))) (list.range ((n-1).factorization 2))

-- #eval list.drop 2 (list.map (λ a, ((↑a : zmod 59)^(59-1))) (list.range 59))
-- #eval list.drop 2 (list.map (λ a, (a,(↑a : zmod 55)^(55-1))) (list.range 55))
-- #eval (to_bool (nat.miller_rabin_witness 35 ↑6), (6 : zmod 35)^34)
-- #eval nat.miller_rabin_sequence 1025 (41 : zmod 1025)
-- #eval nat.miller_rabin_sequence 57 (2 : zmod 57)    -- = [2^7, 2^14, 2^28] = [14, 25, 55]
-- #eval to_bool (1 ∈ nat.miller_rabin_sequence 57 (2 : zmod 57))
-- #eval to_bool (-1 ∈ nat.miller_rabin_sequence 57 (2 : zmod 57))
-- #eval to_bool (-1 ∈ nat.miller_rabin_sequence 1373653 (2 : zmod 1373653))

lemma length_miller_rabin_sequence (n : ℕ) (a : zmod n) :
  (n.miller_rabin_sequence a).length = (n-1).factorization 2 :=
by simp [nat.miller_rabin_sequence]

lemma nat.mem_miller_rabin_sequence (n : ℕ) (a b : zmod n) :
  b ∈ n.miller_rabin_sequence a ↔
  ∃ i ∈ range ((n-1).factorization 2), a^(2^i * odd_part (n-1)) = b :=
by simp [nat.miller_rabin_sequence]

/-- The Miller-Rabin sequence for `n` generated by `a` determines whether `a` is a witness for `n`.
Specifically, `a` is not a witness for `n` iff every element of the sequence is `1`
or if the sequence contains `-1`. -/
lemma MR_nonwitness_iff_miller_rabin_sequence {n : ℕ} (a : zmod n)
  (hn : odd n) (hn1 : n ≠ 1) :
  ¬ nat.miller_rabin_witness n a ↔
    (∀ x ∈ n.miller_rabin_sequence a, x = ↑1) ∨ ((-1 : zmod n) ∈ n.miller_rabin_sequence a) :=
begin
  simp only [nat.miller_rabin_witness, nat.miller_rabin_sequence],
  rw not_and_distrib,
  simp only [not_not, mem_range, not_forall, exists_prop, list.mem_map, list.mem_range,
    zmod.cast_one, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
  split,
  { apply or.imp_left,
    intros h x hx,
    simp [mul_comm, pow_mul, h] },
  { intros h,
    cases h with h3 h4,
    { left, simpa using h3 0 (factorization_two_pos_sub_one hn hn1) },
    { simp [h4] } },
end

/-- The Miller-Rabin sequence for `n` generated by `a` determines whether `a` is a witness for `n`.
Specifically, `a` is a witness for `n` iff the sequence contains an element that's not `1`
and does not contain `-1`. -/
lemma MR_witness_iff_miller_rabin_sequence {n : ℕ} (a : zmod n)
  (hn : odd n) (hn1 : n ≠ 1) :
  nat.miller_rabin_witness n a ↔
    (∃ x ∈ n.miller_rabin_sequence a, x ≠ ↑1) ∧ ((-1 : zmod n) ∉ n.miller_rabin_sequence a) :=
by simpa [not_or_distrib]
    using not_iff_not_of_iff (MR_nonwitness_iff_miller_rabin_sequence a hn hn1)

lemma one_not_miller_rabin_witness (n : ℕ) : ¬ n.miller_rabin_witness (1 : zmod n) :=
by simp [nat.miller_rabin_witness]

lemma minus_one_not_miller_rabin_witness {n : ℕ} (hn : odd n) (hn1 : n ≠ 1) :
  ¬ n.miller_rabin_witness (-1 : zmod n) :=
begin
  rw [MR_nonwitness_iff_miller_rabin_sequence (-1 : zmod n) hn hn1,
      nat.mem_miller_rabin_sequence],
  refine or.inr ⟨0, mem_range.2 (factorization_two_pos_sub_one hn hn1), _⟩,
  obtain ⟨k, rfl⟩ := hn,
  apply odd.neg_one_pow,
  simp only [pow_zero, add_succ_sub_one, add_zero, one_mul],
  apply odd_of_odd_part,
  simpa using hn1,
end


/-! ## An alternative route to proving that every prime is a strong probable prime -/

/-- Let `a^e = 1 (mod p)`. (e.g. for prime `p` we have `a^(p-1) = 1` by Fermat's Little Theorem.)
Let `s := e.factorization 2` and `d := odd_part e` as in the definition of `strong_probable_prime`.
Consider the sequence `⟨a^e = a^(2^(s)*d), a^(2^(s-1)*d), a^(2^(s-2)*d), ..., a^(2*d), a^(d)⟩`.
Each term is a square root of the prevous one. Since `a^e = 1`, the 2nd term is congruent to `±1`.
If it is `+1` then the next term, being a square root, is again congruent to `±1`.
By iteration, then, either all terms including `a^d` are congruent to `+1`,
or there is a member of the sequence congruent to `-1`, i.e. `∃ r < s` such that `a^(2^(r)*d) = -1`.
-/
lemma repeated_halving_of_exponent {p : ℕ} [fact (p.prime)] {a : zmod p} {e : ℕ} (h : a ^ e = 1) :
  a^(odd_part e) = 1 ∨
  (∃ r : ℕ, r < e.factorization 2 ∧ a^(2^r * odd_part e) = -1) :=
begin
  rw ←even_part_mul_odd_part e at h,
  rw even_part at h,
  revert h,
  set d := odd_part e with hd,
  induction e.factorization 2 with i IH,
  { simp },
  { intro h,
    rw [pow_succ, mul_assoc, pow_mul'] at h,
    cases (square_roots_of_one h) with h1 h2,
    { rcases (IH h1) with h3 | ⟨r', hr', har'⟩, { simp [h3] },
      exact or.inr ⟨r', nat.lt.step hr', har'⟩ },
    { exact or.inr ⟨i, lt_add_one i, h2⟩ } },
end


-- An alternative proof of `strong_probable_prime_of_prime` not using `repeated_halving_of_exponent`
/-- Every actual prime is a `strong_probable_prime` relative to any non-zero base `a`. -/
lemma strong_probable_prime_of_prime' (p : ℕ) (pp : p.prime) (a : zmod p) (ha0 : a ≠ 0) :
  strong_probable_prime p a :=
begin
  rcases prime.eq_two_or_odd' pp with rfl | hp,
  { fin_cases a,
    { simpa using ha0 },
    { simpa [strong_probable_prime, odd_part] } },
  haveI : fact (p.prime) := fact_iff.2 pp,
  have fermat := zmod.pow_card_sub_one_eq_one ha0,
  unfold strong_probable_prime,
  rw [←even_part_mul_odd_part (p-1), mul_comm, pow_mul, even_part] at fermat,
  revert fermat,
  induction (p-1).factorization 2 with i IH, { simp },
  intro fermat,
  rw [pow_succ, pow_mul'] at fermat,
  cases (square_roots_of_one fermat) with h1 h2,
  { rcases (IH h1) with h3 | ⟨r', hr', har'⟩, { simp [h3] },
    exact or.inr ⟨r', nat.lt.step hr', har'⟩ },
  { rw [←pow_mul, mul_comm] at h2,
    refine or.inr ⟨i, lt_add_one i, h2⟩ } ,
end

/-- Every actual prime is a `strong_probable_prime` relative to any non-zero base `a`. -/
lemma strong_probable_prime_of_prime (p : ℕ) [fact (p.prime)] (a : zmod p) (ha : a ≠ 0) :
  strong_probable_prime p a  :=
begin
  rw strong_probable_prime,
  apply repeated_halving_of_exponent (zmod.pow_card_sub_one_eq_one ha),
end



--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

/-! ## Lemmas about the proportion of Miller-Rabin witnesses -/

open_locale nat  -- to use `φ` for `nat.totient`

/-- Theorem 3.4 of Conrad:
For odd prime `p` and `α > 0`, the Miller–Rabin nonwitnesses for `p^α` are exactly
the solutions to `a^(p−1) ≡ 1 mod p^α`.
-/
lemma MR_nonwitness_for_prime_power_iff {p α : ℕ} (hp_odd : odd p) (hp : nat.prime p)
  (hα0 : 0 < α) (a : zmod (p^α)) :
  ¬ nat.miller_rabin_witness (p^α) a ↔ a^(p-1) = 1 :=
begin
  haveI : fact (p.prime) := fact_iff.2 hp,
  have two_le_p : 2 ≤ p := nat.prime.two_le hp,
  have one_lt_n : 1 < p ^ α :=
    nat.succ_le_iff.mp (two_le_p.trans (le_self_pow hp.one_lt.le (succ_le_iff.mpr hα0))),
  have zero_lt_n : 0 < p^α := pos_of_gt one_lt_n,
  haveI : fact (0 < p ^ α), { exact {out := zero_lt_n}, },
  have hp_sub1_dvd := sub_one_dvd_pow_sub_one p α hp.pos,

  split,
  { -- Given that `a` is a Miller-Rabin nonwitness for `n = p^α`, prove `a^(p-1) = 1`
    intro hspp,
    rw ←strong_probable_prime_iff_nonwitness at hspp,
    -- Euler's theorem tells us that `a^φ(n) = 1`.
    have euler : a ^ φ(p^α) = 1,
    { have a_unit : is_unit a,
      { apply is_unit_of_pow_eq_one _ (p^α - 1),
        { exact fermat_cprime_of_strong_probable_prime _ _ hspp },
        { simp only [tsub_pos_iff_lt, one_lt_n] } },
      have coe_this := congr_arg coe (zmod.pow_totient (is_unit.unit a_unit)),
      rw units.coe_one at coe_this,
      rw [←coe_this, units.coe_pow],
      congr },

    -- Since p^α is a strong probable prime to base a, we have a^(p^α - 1) = 1
    have h2 := fermat_cprime_of_strong_probable_prime (p^α) a hspp,
    rw fermat_cprime at h2,

    -- Thus the order of a mod n divides gcd(φ(n), n-1)
    rw ← order_of_dvd_iff_pow_eq_one at euler h2 ⊢,

    -- So all that remains is to show that this gcd(φ(n), n-1) is p-1
    suffices : (φ(p^α)).gcd (p^α - 1) = p - 1, { rw ←this, exact nat.dvd_gcd euler h2 },

    rw nat.totient_prime_pow hp hα0,
    refine nat.gcd_mul_of_coprime_of_dvd _ hp_sub1_dvd,

    -- p is relatively prime to p^α - 1
    apply nat.coprime.pow_left,
    rw ←nat.coprime_pow_left_iff hα0,
    exact coprime_self_sub_one (p^α) zero_lt_n },


  { -- Given that `a^(p-1) = 1`, prove `a` is a Miller-Rabin nonwitness for `n = p^α`
    intro h,
    rw ←strong_probable_prime_iff_nonwitness,
    set f := (p-1).factorization 2 with hf,
    set l := odd_part (p - 1) with hl,
    have hl_odd : odd l, { apply odd_of_odd_part, simp [hp.one_lt] },

    set e := (p^α - 1).factorization 2 with he,
    set k := odd_part (p^α - 1) with hk,
    have hk_odd : odd k, { apply odd_of_odd_part, simp [one_lt_n] },

    have hfe : f ≤ e,
    { refine (factorization_le_iff_dvd (by simp [hp.one_lt]) _).2 hp_sub1_dvd 2, simp [one_lt_n] },

    have hlk : l ∣ k,
    { simp_rw [hl, hk], apply ord_compl_dvd_ord_compl_of_dvd hp_sub1_dvd },

    -- Since (a^l)^(2^f) = 1, the order of (a^l) is 2^j for some 0 ≤ j ≤ f
    have H : ∃ (j : ℕ) (H : j ≤ f), order_of (a^l) = 2^j,
    { have H1 : (a^l)^(even_part (p-1)) = 1,
      { rw [← pow_mul, mul_comm, even_part_mul_odd_part (p-1), h],},
      rw ←nat.dvd_prime_pow nat.prime_two,
      exact order_of_dvd_of_pow_eq_one H1 },
    rcases H with ⟨j, hjf, hj⟩,
    rcases eq_or_ne j 0 with rfl | hj0,
    -- If j=0 then a^l = 1. So since l ∣ k, we have a^k = 1 and so `a` is a Miller-Rabin nonwitness.
    { rw [pow_zero, order_of_eq_one_iff] at hj,
      left,
      rcases hlk with ⟨q, hq⟩,
      rw [←hk, hq, pow_mul, hj, one_pow],},
    -- In the case where j ≥ 1 we will show that (a^k)^(2^(j-1)) = -1, and so `a` is a nonwitness.
    { have hj1 : 1 ≤ j := succ_le_iff.2 hj0.bot_lt,
      right,
      rw [←he, ←hk],

      -- Since j ≤ f ≤ e we have j-1 < e,
      -- so all that remains is to show that a ^ (2^(j-1) * k) = -1 (mod p^α)
      refine ⟨j-1, lt_of_lt_of_le (pred_lt hj0) (hjf.trans hfe), _⟩,

      -- Since l ∣ k and k is odd (so k/l is also odd) ...
      cases hlk with q hq,
      have hq_odd : odd q, { rw [hq, odd_mul] at hk_odd, exact hk_odd.2 },
      -- it suffices to show that a ^ (2^(j-1) * l) = -1 (mod p^α)
      suffices : a ^ (2^(j-1) * l) = -1,
      { rw [hq, ←mul_assoc, pow_mul, this], exact hq_odd.neg_one_pow },

      rw [mul_comm, pow_mul],
      set x := (a^l)^(2^(j-1)) with hx,

      have h_order : (a^l)^(2^j) = 1, { rw ←hj, apply pow_order_of_eq_one },

      have hx1 : ¬ x = 1,
      { apply pow_ne_one_of_lt_order_of',
        { apply pow_ne_zero, linarith },
        { rw [hj, pow_lt_iff_lt_right rfl.le], exact pred_lt hj0 } },

      have hx2 : x^2 = 1,
      { rw [hx, ←pow_mul, ←h_order],
        apply congr_arg,
        nth_rewrite_rhs 0 ←nat.sub_add_cancel hj1,
        rw [pow_add, pow_one] },

      refine (or_iff_right hx1).1 (square_roots_of_one_zmod hp hp_odd hx2) } }
end
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------

-- End of Theorem 3.4 of Conrad  ^^^^
-- For odd prime `p` and `α > 0`, the Miller–Rabin nonwitnesses for `p^α` are exactly
-- the solutions to `a^(p−1) ≡ 1 mod p^α`.
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------------






-- https://leanprover.zulipchat.com/#narrow/stream/217875/near/277098292
/-- The elements of `zmod n` whose `e`th power equals `1` form a subgroup -/
def pow_eq_one_subgroup (n e : ℕ) [fact (0 < n)] : subgroup ((zmod n)ˣ) :=
{ carrier := ((finset.univ : finset ((zmod n)ˣ)).filter (λ (a : (zmod n)ˣ), a^e = 1)),
  one_mem' := by simp,
  mul_mem' := by
  { simp only [coe_filter, coe_univ, set.sep_univ, set.mem_set_of_eq],
    intros a b ha hb,
    rw [mul_pow, ha, hb, mul_one] },
  inv_mem' := by simp }

/-- The elements of `zmod n` whose `e`th power equals `±1` form a subgroup -/
def pow_alt_subgroup (n e : ℕ) [fact (0 < n)] : subgroup ((zmod n)ˣ) :=
{ carrier := ((finset.univ : finset ((zmod n)ˣ)).filter (λ (a : (zmod n)ˣ), a^e = 1 ∨ a^e = -1)),
  one_mem' := by simp,
  mul_mem' := by
  { simp only [coe_filter, coe_univ, set.sep_univ, set.mem_set_of_eq],
    intros a b ha hb,
    simp_rw [mul_pow],
    cases ha with ha1 ha2,
    { simp_rw [ha1, one_mul], exact hb },
    { simp_rw [ha2],
      rw [neg_mul, one_mul, neg_inj, or_comm],
      apply or.imp id (λ h, _) hb,
      rw [h, neg_neg] } },
  inv_mem' := by
  { simp only [coe_filter, coe_univ, set.sep_univ, set.mem_set_of_eq, inv_pow, inv_eq_one],
    intros a ha,
    apply or.imp id (λ h, _) ha,
    rw [h, inv_neg', inv_one] } }

/-- Every positive natural is either a prime or a prime power or the product of two coprime numbers
both greater than 1 — i.e. it is of the form of one of the recursors of `rec_on_prime_coprime`. -/
lemma coprime_factorization_or_prime_power (n : ℕ) (h : 0 < n) :
  (∃ (n0 n1 : ℕ), nat.coprime n0 n1 ∧ n0 * n1 = n ∧ 1 < n0 ∧ 1 < n1) ∨
  (∃ (p k : ℕ), p.prime ∧ p^k = n) :=
begin
  revert h,
  refine nat.rec_on_prime_coprime _ _ _ n,
  { simp },
  { intros p k hp hn, exact or.inr ⟨p, k, hp, rfl⟩ },
  { intros n0 n1 hn0 hn1 hn0n1 hn0' hn1' hmul, exact or.inl ⟨n0, n1, hn0n1, rfl, hn0, hn1⟩ }
end

lemma one_or_coprime_factorization_or_prime_power (n : ℕ) (h : 0 < n) :
  (n = 1) ∨
  (∃ (n0 n1 : ℕ), nat.coprime n0 n1 ∧ n0 * n1 = n ∧ 1 < n0 ∧ 1 < n1) ∨
  (∃ (p k : ℕ), 1 ≤ k ∧ p.prime ∧ p^k = n) :=
begin
  by_cases hn1 : n = 1, { simp [hn1] },
  right,
  rcases coprime_factorization_or_prime_power n h with ⟨n0, n1, h01⟩ | ⟨p, k, pp, hpk'⟩,
  { exact or.inl ⟨n0, n1, h01⟩ },
  { refine or.inr ⟨p, k, _, pp, hpk'⟩,
    contrapose! hn1,
    rwa [lt_one_iff.1 hn1, pow_zero, eq_comm] at hpk' },
end

-- noncomputable instance subgroup_fintype {G : Type} [fintype G] [group G] {H : subgroup G} :
  -- fintype H := subgroup.fintype H
-- begin
--   -- library_search
--   tidy,
--   sorry,
-- end

-- lemma card_finite_subgroup_eq_card_carrier {α : Type} [fintype α] [group α] (s : finset α)
--   (hmul : ∀ a b ∈ s, a * b ∈ s) (hid : (1 : α) ∈ s)
--   (hinv : ∀ a ∈ s, a⁻¹ ∈ s)  :
--   finset.card s = fintype.card (subgroup.mk (s : set α) (by tidy) (by tidy) (by tidy)) :=
-- begin
--   -- simp, -- fails
--   -- rw subgroup.card_coe_sort, -- doesn't exist
--   tidy,
--   rw ← subgroup.mem_carrier,
--   sorry,
-- end


instance (n : ℕ) [hn_pos : fact (0 < n)] : decidable_pred (@is_unit (zmod n) _) :=
λ a, fintype.decidable_exists_fintype

/-- The finset of units of zmod n -/
def finset_units (n : ℕ) [hn_pos : fact (0 < n)] : finset (zmod n) :=
(finset.univ : finset (zmod n)).filter is_unit


-- -- finite subgroup

-- -- the cardinality of a subgroup is the cardinality of its carrier
-- lemma card_subgroup_eq_card_carrier {G : Type} [group G] [fintype G] {H : subgroup G} :
--   fintype.card H = finset.card (H.carrier : finset G) :=
-- begin

-- end

-- lemma foocard (n e : ℕ) [fact (0 < n)] :
--   (fintype.card (↥(pow_alt_subgroup n e)) : ℕ)
--   = finset.card ((finset.univ : finset ((zmod n)ˣ)).filter
  -- (λ (a : (zmod n)ˣ), a^e = 1 ∨ a^e = -1))
--   :=
-- begin
--   rw fintype.card,
--   -- simp,
-- end


-- lemma unlikely_strong_probable_prime_of_coprime_mul (n : ℕ) [hn_pos : fact (0 < n)]
--   (h : (∃ (n0 n1 : ℕ), nat.coprime n0 n1 ∧ n0 * n1 = n ∧ 1 < n0 ∧ 1 < n1))
--   (not_prime : ¬ n.prime) :
--   ((finset_units n).filter (λ a, strong_probable_prime n a)).card * 2 ≤ (finset_units n).card :=
-- begin
--   rcases h with ⟨n0, n1, h_coprime, h_mul, hn0, hn1⟩,
--   let i0 := ((finset.range (odd_part (n-1))).filter (λ i, ∃ a_0 : zmod n, a_0^(2^i) = -1)).max'
--   ( by
--     { rw finset.filter_nonempty_iff,
--       use 0,
--       simp only [finset.mem_range, pow_zero, pow_one, exists_apply_eq_apply, and_true],
--       by_contra,
--       simp at h,
--       have hn' : n - 1 ≠ 0,
--       { rw [ne.def, tsub_eq_zero_iff_le, not_le, ← h_mul],
--         exact one_lt_mul hn0.le hn1 },
--       apply hn',
--       clear hn',
--       rw ← even_part_mul_odd_part (n - 1),
--       rw [h, mul_zero] } ),
--   have h_proper : ∃ x, x ∉ (pow_alt_subgroup n (i0 * odd_part(n - 1))),
--   { -- nat.chinese_remainder'_lt_lcm
--     -- nat.chinese_remainder_lt_mul
--     sorry },
--   rcases h_proper with ⟨x, hx⟩,
--   have hsubgroup :
--     (finset.filter (λ (a : zmod n), strong_probable_prime n a) (finset_units n)).card * 2
--     ≤ fintype.card ↥(pow_alt_subgroup n (i0 * odd_part (n - 1))) * 2,
--   { simp [mul_le_mul_right],
--     -- rw foocard,
--     sorry,  },
--   apply trans hsubgroup,
--   clear hsubgroup,
--   convert card_le_half_of_proper_subgroup x hx using 1,
--   { -- TODO(Bolton):
--     sorry, },

-- end

-- lemma unlikely_strong_probable_prime_of_prime_power (n : ℕ) [hn_pos : fact (0 < n)] (h1 : 1 < n)
--   (h : (∃ (p k : ℕ), p.prime ∧ p^k = n)) (not_prime : ¬ n.prime) :
--   ((finset_units n).filter (λ a, strong_probable_prime n a)).card * 2 ≤ (finset_units n).card :=
-- begin
--   rcases h with ⟨p, k, p_prime, n_pow⟩,
--   have n_pos : 0 < n, exact hn_pos.out,
--   have one_lt_k : 1 < k,
--   { by_contra,
--     simp at h,
--     interval_cases k,
--     simp at n_pow,
--     rw n_pow at h1,
--     exact nat.lt_asymm h1 h1,
--     { apply not_prime,-- TODO(Sean)
--       sorry } },
--   sorry,
-- end


-- lemma unlikely_strong_probable_prime_of_composite (n : ℕ) [hn_pos : fact (0 < n)] (hn1 : 1 < n)
--   (not_prime : ¬ n.prime) :
--   ((finset_units n).filter (λ a, strong_probable_prime n a)).card * 2 ≤ (finset_units n).card :=
-- begin
--   cases one_or_coprime_factorization_or_prime_power n (hn_pos.out),
--   { exfalso,
--     -- TODO(Sean)
--     sorry },
--   -- clear hn1,
--   cases h,
--   { apply unlikely_strong_probable_prime_of_coprime_mul,
--     exact h,
--     exact not_prime },
--   { -- n is a prime power
--     -- TODO(Sean): unlikely_strong_probable_prime_of_prime_power should be able to finish this
--     sorry },
-- end
