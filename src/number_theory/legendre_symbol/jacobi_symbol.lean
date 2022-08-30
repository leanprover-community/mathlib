/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import number_theory.legendre_symbol.quadratic_reciprocity

/-!
# The Jacobi Symbol

We define the Jacobi symbol and prove its main properties.

## Main definitions

We define the Jacobi symbol, `jacobi_sym a b` for integers `a` and natural numbers `b`
as the product over the prime factors `p` of `b` of the Legendre symbols `zmod.legendre_sym p a`.
This agrees with the mathematical definition when `b` is odd.

The prime factors are obtained via `nat.factors`. Since `nat.factors 0 = []`,
this implies in particular that `jacobi_sym a 0 = 1` for all `a`.

## Main statements

We prove the main properties of the Legendre symbol, including the following.

* Multiplicativity in both arguments (`jacobi_sym_mul_left`, `jacobi_sym_mul_right`)

* The value of the symbol is `1` or `-1` when the arguments are coprime
  (`jacobi_sym_eq_one_or_neg_one`)

* The symbol vanishes if and only if `b ≠ 0` and the arguments are not coprime
  (`jacobi_sym_eq_zero_iff`)

* If the symbol has the value `-1`, then `a : zmod b` is not a square (`jacobi_sym_eq_neg_one`)

* Quadratic reciprocity (`jacobi_sym_quadratic_reciprocity`,
  `jacobi_sym_quadratic_reciprocity_one_mod_four`,
  `jacobi_sym_quadratic_reciprocity_threee_mod_four`)

* The supplementary laws for `a = -1`, `a = 2`, `a = -2` (`jacobi_sym_neg_one`, `jacobi_sym_two`,
  `jacobi_sym_neg_two`)

* The symbol depends on `a` only via its residue class mod `b` (`jacobi_sym_mod_left`)
  and on `b` only via its residue class mod `4*a` (`jacobi_sym_mod_right`)

## Notations

We define the notation `[a | b]ⱼ` for `legendre_sym a b`, localized to `number_theory_symbols`.

## Tags
Jacobi symbol, quadratic reciprocity
-/

/-!
### Some helpful lemmas

Once the dust has settled, these will be moved to the appropriate files.
-/

namespace nat

/-- If `a` is even, then `n` is odd iff `n % a` is odd. -/
lemma odd.mod_even_iff {n a : ℕ} (ha : even a) : odd n ↔ odd (n % a) :=
(even_sub' $ mod_le n a).mp $ even_iff_two_dvd.mpr $ (even_iff_two_dvd.mp ha).trans $ dvd_sub_mod n

/-- If `a` is even, then `n` is even iff `n % a` is even. -/
lemma even.mod_even_iff {n a : ℕ} (ha : even a) : even n ↔ even (n % a) :=
(even_sub $ mod_le n a).mp $ even_iff_two_dvd.mpr $ (even_iff_two_dvd.mp ha).trans $ dvd_sub_mod n

/-- If `n` is odd and `a` is even, then `n % a` is odd. -/
lemma odd.mod_even {n a : ℕ} (hn : odd n) (ha : even a) : odd (n % a) :=
(odd.mod_even_iff ha).mp hn

/-- If `n` is even and `a` is even, then `n % a` is even. -/
lemma even.mod_even {n a : ℕ} (hn : even n) (ha : even a) : even (n % a) :=
(even.mod_even_iff ha).mp hn

/-- If `a` is a nonzero natural number, then there are natural numbers `e` and `a'`
such that `a = 2^e * a'` and `a'` is odd. -/
lemma two_pow_mul_odd {a : ℕ} (ha : a ≠ 0) : ∃ e a' : ℕ, odd a' ∧ a = 2 ^ e * a' :=
⟨a.factorization 2, ord_compl[2] a,
 odd_iff.mpr $ two_dvd_ne_zero.mp $ not_dvd_ord_compl prime_two ha,
 (ord_proj_mul_ord_compl_eq_self a 2).symm⟩

end nat

namespace int

lemma dvd_nat_abs_iff_of_nat_dvd {a : ℕ} {z : ℤ} : a ∣ z.nat_abs ↔ (a : ℤ) ∣ z :=
⟨int.of_nat_dvd_of_dvd_nat_abs, int.dvd_nat_abs_of_of_nat_dvd⟩

/-- If `gcd a (m * n) ≠ 1`, then `gcd a m ≠ 1` or `gcd a n ≠ 1`. -/
lemma gcd_ne_one_iff_gcd_mul_right_ne_one {a : ℤ} {m n : ℕ} :
  a.gcd (m * n) ≠ 1 ↔ a.gcd m ≠ 1 ∨ a.gcd n ≠ 1 :=
by simp only [gcd_eq_one_iff_coprime, ← not_and_distrib, not_iff_not, is_coprime.mul_right_iff]

/-- If `gcd a (m * n) = 1`, then `gcd a m = 1`. -/
lemma gcd_eq_one_of_gcd_mul_right_eq_one_left {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
  a.gcd m = 1 :=
nat.dvd_one.mp $ trans_rel_left _ (gcd_dvd_gcd_mul_right_right a m n) h

/-- If `gcd a (m * n) = 1`, then `gcd a n = 1`. -/
lemma gcd_eq_one_of_gcd_mul_right_eq_one_right {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
  a.gcd n = 1 :=
nat.dvd_one.mp $ trans_rel_left _ (gcd_dvd_gcd_mul_left_right a n m) h

end int

namespace zmod

/-- If `p` is a prime and `a` is an integer, then `a : zmod p` is zero if and only if
`gcd a p ≠ 1`. -/
lemma eq_zero_iff_gcd_ne_one {a : ℤ} {p : ℕ} [pp : fact p.prime] : (a : zmod p) = 0 ↔ a.gcd p ≠ 1 :=
by rw [ne, int.gcd_comm, int.gcd_eq_one_iff_coprime,
       (nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd, not_not, int_coe_zmod_eq_zero_iff_dvd]

/-- If an integer `a` and a prime `p` satisfy `gcd a p = 1`, then `a : zmod p` is nonzero. -/
lemma ne_zero_of_gcd_eq_one {a : ℤ} {p : ℕ} (pp : p.prime) (h : a.gcd p = 1) :
  (a : zmod p) ≠ 0 :=
mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (not_not.mpr h)

/-- If an integer `a` and a prime `p` satisfy `gcd a p ≠ 1`, then `a : zmod p` is zero. -/
lemma eq_zero_of_gcd_ne_one {a : ℤ} {p : ℕ} (pp : p.prime) (h : a.gcd p ≠ 1) :
  (a : zmod p) = 0 :=
(@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h

end zmod

namespace list

lemma pmap_append {α β : Type*} {p : α → Prop} (f : Π (a : α), p a → β) (l₁ l₂ : list α)
  (h : ∀ (a : α), a ∈ l₁ ++ l₂ → p a) :
  (l₁ ++ l₂).pmap f h = l₁.pmap f (λ a ha, h a (mem_append_left l₂ ha)) ++
                        l₂.pmap f (λ a ha, h a (mem_append_right l₁ ha)) :=
begin
  induction l₁ with _ _ ih,
  { simp only [pmap, nil_append], },
  { simp only [pmap, cons_append, eq_self_iff_true, true_and, ih], }
end

end list

section jacobi

/-!
### Definition of the Jacobi symbol

We define the Jacobi symbol `(a / b)` for integers `a` and natural numbers `b` as the
product of the legendre symbols `(a / p)`, where `p` runs through the prime divisors
(with multiplicity) of `b`, as provided by `b.factors`. This agrees with the Jacobi symbol
when `b` is odd and gives less meaningful values when it is not (e.g., the symbol is `1`
when `b = 0`). This is called `jacobi_sym a b`.

We define localized notation (locale `number_theory_symbols`) `[a | b]ⱼ` for the Jacobi
symbol `jacobi_sym a b`. (Unfortunately, there is no subscript "J" in unicode.)
-/

open zmod nat

/-- The Jacobi symbol of `a` and `b` -/
-- Since we need the fact that the factors are prime, we use `list.pmap`.
def jacobi_sym (a : ℤ) (b : ℕ) : ℤ :=
(b.factors.pmap (λ p pp, @legendre_sym p ⟨pp⟩ a) (λ p pf, prime_of_mem_factors pf)).prod

-- Notation for the Jacobi symbol.
localized "notation `[` a ` | ` b `]ⱼ` := jacobi_sym a b" in number_theory_symbols

/-!
### Properties of the Jacobi symbol
-/

open_locale number_theory_symbols

/-- The Jacobi symbol `(a / 0)` has the value `1`. -/
lemma jacobi_sym_zero_right (a : ℤ) : [a | 0]ⱼ = 1 :=
by simp only [jacobi_sym, factors_zero, list.prod_nil, list.pmap]

/-- The Jacobi symbol `(a / 1)` has the value `1`. -/
lemma jacobi_sym_one_right (a : ℤ) : [a | 1]ⱼ = 1 :=
by simp only [jacobi_sym, factors_one, list.prod_nil, list.pmap]

/-- The Legendre symbol `(a / p)` with an integer `a` and a prime number `p`
is the same as the Jaocbi symbol `(a / p)`. -/
lemma legendre_sym.to_jacobi_sym {p : ℕ} [fp : fact p.prime] {a : ℤ} :
  legendre_sym p a = [a | p]ⱼ :=
by simp only [jacobi_sym, factors_prime fp.1, list.prod_cons, list.prod_nil, mul_one, list.pmap]

/-- The Jacobi symbol is multiplicative in its second argument. -/
lemma jacobi_sym_mul_right (a : ℤ) (b₁ b₂ : ℕ) [ne_zero b₁] [ne_zero b₂] :
  [a | b₁ * b₂]ⱼ = [a | b₁]ⱼ * [a | b₂]ⱼ :=
begin
  simp_rw [jacobi_sym],
  have h := λ p hp, (list.mem_append.mp hp).elim prime_of_mem_factors prime_of_mem_factors,
  rwa [list.perm.prod_eq (list.perm.pmap _ (perm_factors_mul (ne_zero.ne b₁) (ne_zero.ne b₂))),
       list.pmap_append, list.prod_append],
end

/-- The Jacobi symbol `(1 / b)` has the value `1`. -/
lemma jacobi_sym_one_left (b : ℕ) : [1 | b]ⱼ = 1 :=
begin
  refine rec_on_mul (jacobi_sym_zero_right 1) (jacobi_sym_one_right 1)
                    (λ p pp, _) (λ m n hm hn, _) b,
  { simp_rw [← @legendre_sym.to_jacobi_sym p ⟨pp⟩, @legendre_sym_one p ⟨pp⟩], },
  { by_cases hm0 : m = 0,
    { rw [hm0, zero_mul, jacobi_sym_zero_right], },
    by_cases hn0 : n = 0,
    { rw [hn0, mul_zero, jacobi_sym_zero_right], },
    rw [@jacobi_sym_mul_right _ _ _ ⟨hm0⟩ ⟨hn0⟩, hm, hn, one_mul], },
end

/-- The Jacobi symbol is multiplicative in its first argument. -/
lemma jacobi_sym_mul_left (a₁ a₂ : ℤ) (b : ℕ) : [a₁ * a₂ | b]ⱼ = [a₁ | b]ⱼ * [a₂ | b]ⱼ :=
begin
  have h0 : [a₁ * a₂ | 0]ⱼ = [a₁ | 0]ⱼ * [a₂ | 0]ⱼ :=
  by simp only [jacobi_sym, factors_zero, list.prod_nil, one_mul, list.pmap],
  refine rec_on_mul h0 _ (λ p pp, _) (λ m n hm hn, _) b,
  { simp only [jacobi_sym, factors_one, list.prod_nil, one_mul, list.pmap], },
  { simp_rw [← @legendre_sym.to_jacobi_sym p ⟨pp⟩, @legendre_sym_mul p ⟨pp⟩], },
  { by_cases hmz : m = 0,
    { rw [hmz, zero_mul], exact h0, },
    by_cases hnz : n = 0,
    { rw [hnz, mul_zero], exact h0, },
    simp_rw [@jacobi_sym_mul_right _ _ _ ⟨hmz⟩ ⟨hnz⟩],
    rw [hm, hn, mul_mul_mul_comm], },
end

/-- We have that `(a^e / b) = (a / b)^e` for the Jacobi symbol. -/
lemma jacobi_sym_pow_left (a : ℤ) (e b : ℕ) : [a ^ e | b]ⱼ = [a | b]ⱼ ^ e :=
begin
  induction e with e ih,
  { rw [pow_zero, pow_zero, jacobi_sym_one_left], },
  { rw [pow_succ, pow_succ, jacobi_sym_mul_left, ih], }
end

/-- We have that `(a / b^e) = (a / b)^e` for the Jacobi symbol. -/
lemma jacobi_sym_pow_right (a : ℤ) (b e : ℕ) : [a | b ^ e]ⱼ = [a | b]ⱼ ^ e :=
begin
  induction e with e ih,
  { rw [pow_zero, pow_zero, jacobi_sym_one_right], },
  { by_cases hb : b = 0,
    { rw [hb, zero_pow (succ_pos e), jacobi_sym_zero_right, one_pow], },
    { haveI : ne_zero b := ⟨hb⟩,
      haveI : ne_zero (b ^ e) := ⟨pow_ne_zero e hb⟩,
      rw [pow_succ, pow_succ, jacobi_sym_mul_right, ih], } }
end

/-- The Jacobi symbol `(a / b)` takes the value `1` or `-1` if `a` and `b` are coprime. -/
lemma jacobi_sym_eq_one_or_neg_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) :
  [a | b]ⱼ = 1 ∨ [a | b]ⱼ = -1 :=
begin
  refine rec_on_mul (λ _, or.inl $ jacobi_sym_zero_right a)
          (λ _, or.inl $ jacobi_sym_one_right a) (λ p pp hpg, _) (λ m n hm hn hmng, _) b h,
  { simp_rw [← @legendre_sym.to_jacobi_sym p ⟨pp⟩],
    exact @legendre_sym_eq_one_or_neg_one p ⟨pp⟩ _ (ne_zero_of_gcd_eq_one pp hpg), },
  { by_cases hm0 : m = 0,
    { rw [hm0, zero_mul],
      exact or.inl (jacobi_sym_zero_right a), },
    by_cases hn0 : n = 0,
    { rw [hn0, mul_zero],
      exact or.inl (jacobi_sym_zero_right a), },
    rw [nat.cast_mul] at hmng,
    have hng := hn (int.gcd_eq_one_of_gcd_mul_right_eq_one_right hmng),
    simp_rw [@jacobi_sym_mul_right _ _ _ ⟨hm0⟩ ⟨hn0⟩],
    cases hm (int.gcd_eq_one_of_gcd_mul_right_eq_one_left hmng) with hl hr,
    { rwa [hl, one_mul], },
    { rw [hr, neg_mul, one_mul, neg_inj, neg_eq_iff_neg_eq],
      exact or.dcases_on hng or.inr (λ hr', or.inl hr'.symm), } },
end

/-- The square of the Jacobi symbol `(a / b)` is `1` when `a` and `b` are coprime. -/
lemma jacobi_sym_sq_one {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : [a | b]ⱼ ^ 2 = 1 :=
by cases jacobi_sym_eq_one_or_neg_one h with h₁ h₁; rw h₁; refl

/-- The Jacobi symbol `(a^2 / b)` is `1` when `a` and `b` are coprime. -/
lemma jacobi_sym_sq_one' {a : ℤ} {b : ℕ} (h : a.gcd b = 1) : [a ^ 2 | b]ⱼ = 1 :=
by rw [pow_two, jacobi_sym_mul_left, ← pow_two, jacobi_sym_sq_one h]

/-- The Jacobi symbol `(a / b)` depends only on `a` mod `b`. -/
lemma jacobi_sym_mod_left (a : ℤ) (b : ℕ) : [a | b]ⱼ = [a % b | b]ⱼ :=
begin
  refine rec_on_mul (λ _, by simp_rw [jacobi_sym_zero_right])
                    (λ _, by simp_rw [jacobi_sym_one_right]) (λ p pp a, _) (λ m n hm hn a, _) b a,
  { simp_rw [← @legendre_sym.to_jacobi_sym p ⟨pp⟩, @legendre_sym_mod p ⟨pp⟩ a], },
  { by_cases hm0 : m = 0,
    { simp_rw [hm0, zero_mul, jacobi_sym_zero_right], },
    by_cases hn0 : n = 0,
    { simp_rw [hn0, mul_zero, jacobi_sym_zero_right], },
    simp_rw [nat.cast_mul, @jacobi_sym_mul_right _ _ _ ⟨hm0⟩ ⟨hn0⟩,
             hm a, hn a, hm (a % (m * n)), hn (a % (m * n))],
    rw [int.mod_mod_of_dvd a (dvd_mul_right ↑m ↑n), int.mod_mod_of_dvd a (dvd_mul_left ↑n ↑m)] },
end

/-- The Jacobi symbol `(a / b)` depends only on `a` mod `b`. -/
lemma jacobi_sym_mod_left' {a₁ a₂ : ℤ} {b : ℕ} (h : a₁ % b = a₂ % b) : [a₁ | b]ⱼ = [a₂ | b]ⱼ :=
by rw [jacobi_sym_mod_left, h, ← jacobi_sym_mod_left]

/-- The Jacobi symbol `(a / b)` vanishes when `a` and `b` are not coprime and `b ≠ 0`. -/
lemma jacobi_sym_eq_zero_if_not_coprime {a : ℤ} {b : ℕ} [hb : ne_zero b] (h : a.gcd b ≠ 1) :
  [a | b]ⱼ = 0 :=
begin
  refine rec_on_mul (λ hf _, false.rec _ (hf rfl)) (λ _ h₁, false.rec _ (h₁ a.gcd_one_right))
                    (λ p pp _ hg, _) (λ m n hm hn hmn0 hg, _) b (ne_zero.ne b) h,
  { rw [← @legendre_sym.to_jacobi_sym p ⟨pp⟩, @legendre_sym_eq_zero_iff p ⟨pp⟩],
    exact eq_zero_of_gcd_ne_one pp hg, },
  { haveI hm0 : ne_zero m := ⟨left_ne_zero_of_mul hmn0⟩,
    haveI hn0 : ne_zero n := ⟨right_ne_zero_of_mul hmn0⟩,
    rw [jacobi_sym_mul_right],
    cases int.gcd_ne_one_iff_gcd_mul_right_ne_one.mp hg with hgm hgn,
    { rw [hm hm0.1 hgm, zero_mul], },
    { rw [hn hn0.1 hgn, mul_zero], } },
end

/-- The Jacobi symbol `(a / b)` vanishes if and only if `b ≠ 0` and `a` and `b` are not coprime. -/
lemma jacobi_sym_eq_zero_iff {a : ℤ} {b : ℕ} : [a | b]ⱼ = 0 ↔ b ≠ 0 ∧ a.gcd b ≠ 1 :=
begin
  refine ⟨λ h, ⟨λ hf, _, λ hf, _⟩, λ h, @jacobi_sym_eq_zero_if_not_coprime a b ⟨h.left⟩ h.right⟩,
  { rw [hf, jacobi_sym_zero_right a] at h,
    exact one_ne_zero h, },
  { have h₁ := jacobi_sym_eq_one_or_neg_one hf,
    rw [h] at h₁,
    exact or.dcases_on h₁ zero_ne_one (int.zero_ne_neg_of_ne zero_ne_one), }
end

/-- The Jacobi symbol `(0 / b)` vanishes when `b > 1`. -/
lemma jacobi_sym_zero_left {b : ℕ} (hb : 1 < b) : [0 | b]ⱼ = 0 :=
begin
  refine @jacobi_sym_eq_zero_if_not_coprime 0 b ⟨ne_zero_of_lt hb⟩ _,
  rw [int.gcd_zero_left, int.nat_abs_of_nat],
  exact (ne_of_lt hb).symm,
end

/-- If the Jacobi symbol `(a / b)` is `-1`, then `a` is not a square modulo `b`. -/
lemma jacobi_sym_eq_neg_one {a : ℤ} {b : ℕ} (h : [a | b]ⱼ = -1) : ¬ is_square (a : zmod b) :=
begin
  haveI : fact (0 < b),
  { refine ⟨nat.pos_of_ne_zero (λ hf, _)⟩,
    have h₁ : [a | b]ⱼ ≠ 1 := by {rw h, dec_trivial},
    rw [hf, jacobi_sym_zero_right] at h₁,
    exact h₁ rfl, },
  rintro ⟨x, hx⟩,
  have hab : a % b = (x * x) % b,
  { have h₁ : (a : zmod b) = (x.val * x.val : ℤ),
    { simp only [hx, nat_cast_val, int.cast_mul, int_cast_cast, cast_id', id.def], },
    have h₂ := (zmod.int_coe_eq_int_coe_iff' a (x.val * x.val) b).mp h₁,
    rwa [zmod.nat_cast_val] at h₂, },
  have hj := jacobi_sym_mod_left' hab,
  rw [jacobi_sym_mul_left, h, ← pow_two] at hj,
  exact (-1 : ℤ).lt_irrefl (hj.substr (sq_nonneg [x | b]ⱼ)),
end

/-!
### Values at `-1`, `2` and `-2`
-/

/-- An induction principle that can be used for "multiplicative" induction to show
properties of odd natural numbers. -/
lemma nat.mul_induction_odd {P : ℕ → Prop} (h1 : P 1) (hp : ∀ p : ℕ, p.prime → p ≠ 2 → P p)
  (h : ∀ m n : ℕ, odd m → odd n → P m → P n → P (m * n)) (b : ℕ) (hb : odd b) : P b :=
rec_on_mul (λ h, false.rec _ (even_iff_not_odd.mp even_zero h)) (λ _, h1)
           (λ p pp p2, hp p pp ((@prime.mod_two_eq_one_iff_ne_two _ ⟨pp⟩).mp (odd_iff.mp p2)))
           (λ m n hm hn hmn, let hmo := odd.of_mul_left hmn in let hno := odd.of_mul_right hmn in
                             h m n hmo hno (hm hmo) (hn hno))
           b hb

/-- If `χ` is a multiplicative function such that `(a / p) = χ p` for all odd primes `p`,
then the Jacobi symbol `(a / b)` equals `χ b` for all odd natural numbers `b`. -/
lemma jacobi_sym_value (a : ℤ) {R : Type*} [comm_semiring R] (χ : R →* ℤ)
  (hp : ∀ (p : ℕ) (pp : p.prime) (h2 : p ≠ 2), @legendre_sym p ⟨pp⟩ a = χ p) {b : ℕ} (hb : odd b) :
  [a | b]ⱼ = χ b :=
begin
  refine nat.mul_induction_odd (by simp_rw [jacobi_sym_one_right, nat.cast_one, map_one]) _ _ b hb,
  { exact λ p pp p2, by simp_rw [← @legendre_sym.to_jacobi_sym p ⟨pp⟩, hp p pp p2], },
  { exact λ m n hmo hno hm hn,
    by rw [nat.cast_mul, @jacobi_sym_mul_right _ _ _ ⟨hmo.pos.ne'⟩ ⟨hno.pos.ne'⟩,
           hm, hn, map_mul], }
end

/-- If `b` is odd, then the Jacobi symbol `(-1 / b)` is given by `χ₄ b`. -/
lemma jacobi_sym_neg_one {b : ℕ} (hb : odd b) : [-1 | b]ⱼ = χ₄ b :=
jacobi_sym_value (-1) χ₄ (λ p pp h2, @legendre_sym_neg_one p ⟨pp⟩ h2) hb

/-- If `b` is odd, then `(-a / b) = χ₄ b * (a / b)`. -/
lemma jacobi_sym_neg (a : ℤ) {b : ℕ} (hb : odd b) : [-a | b]ⱼ = χ₄ b * [a | b]ⱼ :=
by rw [neg_eq_neg_one_mul, jacobi_sym_mul_left, jacobi_sym_neg_one hb]

/-- If `b` is odd, then the Jacobi symbol `(2 / b)` is given by `χ₈ b`. -/
lemma jacobi_sym_two {b : ℕ} (hb : odd b) : [2 | b]ⱼ = χ₈ b :=
jacobi_sym_value 2 χ₈ (λ p pp h2, @legendre_sym_two p ⟨pp⟩ h2) hb

/-- If `b` is odd, then the Jacobi symbol `(-2 / b)` is given by `χ₈' b`. -/
lemma jacobi_sym_neg_two {b : ℕ} (hb : odd b) : [-2 | b]ⱼ = χ₈' b :=
jacobi_sym_value (-2) χ₈' (λ p pp h2, @legendre_sym_neg_two p ⟨pp⟩ h2) hb


/-!
### Quadratic Reciprocity
-/

/-- The bi-multiplicative map giving the sign in the Law of Quadratic Reciprocity -/
def qr_sign (m n : ℕ) : ℤ := [χ₄ m | n]ⱼ

/-- We can express `qr_sign m n` as a power of `-1` when `m` and `n` are odd. -/
lemma qr_sign_neg_one_pow {m n : ℕ} (hm : odd m) (hn : odd n) :
  qr_sign m n = (-1) ^ ((m / 2) * (n / 2)) :=
begin
  rw [qr_sign, pow_mul, ← χ₄_eq_neg_one_pow (odd_iff.mp hm)],
  cases odd_mod_four_iff.mp (odd_iff.mp hm) with h h,
  { rw [χ₄_nat_one_mod_four h, jacobi_sym_one_left, one_pow], },
  { rw [χ₄_nat_three_mod_four h, ← χ₄_eq_neg_one_pow (odd_iff.mp hn), jacobi_sym_neg_one hn], }
end

/-- When `m` and `n` are odd, then the square of `qr_sign m n` is `1`. -/
lemma qr_sign_sq_eq_one {m n : ℕ} (hm : odd m) (hn : odd n) : (qr_sign m n) ^ 2 = 1 :=
by rw [qr_sign_neg_one_pow hm hn, ← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

/-- `qr_sign` is multiplicative in the first argument. -/
lemma qr_sign_mul_left (m₁ m₂ n : ℕ) : qr_sign (m₁ * m₂) n = qr_sign m₁ n * qr_sign m₂ n :=
by simp_rw [qr_sign, nat.cast_mul, map_mul, jacobi_sym_mul_left]

/-- `qr_sign` is multiplicative in the second argument. -/
lemma qr_sign_mul_right (m n₁ n₂ : ℕ) [ne_zero n₁] [ne_zero n₂] :
  qr_sign m (n₁ * n₂) = qr_sign m n₁ * qr_sign m n₂ :=
jacobi_sym_mul_right (χ₄ m) n₁ n₂

/-- `qr_sign` is symmetric when both arguments are odd. -/
lemma qr_sign_symm {m n : ℕ} (hm : odd m) (hn : odd n) : qr_sign m n = qr_sign n m :=
by rw [qr_sign_neg_one_pow hm hn, qr_sign_neg_one_pow hn hm, mul_comm (m / 2)]

/-- We can move `qr_sign m n` from one side of an equality to the other when `m` and `n` are odd. -/
lemma qr_sign_eq_iff_eq {m n : ℕ} (hm : odd m) (hn : odd n) (x y : ℤ) :
  qr_sign m n * x = y ↔ x = qr_sign m n * y :=
begin
  refine ⟨λ h', have h : _, from h'.symm, _, λ h, _⟩;
  rw [h, ← mul_assoc, ← pow_two, qr_sign_sq_eq_one hm hn, one_mul],
end

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
lemma jacobi_sym_quadratic_reciprocity' {a b : ℕ} (ha : odd a) (hb : odd b) :
  [a | b]ⱼ = qr_sign b a * [b | a]ⱼ :=
begin
  -- `jacobi_sym_value _ χ` with `χ : R →* ℤ` (`R` a commutative semiring) introduces
  -- a cast `coe : ℕ → R` even when `R = ℕ`. The following is used to get rid of that later.
  have coe_nat_nat : ∀ a : ℕ, (coe : ℕ → ℕ) a = a := λ a, rfl,
  -- define the right hand side for fixed `a` as a `ℕ →* ℤ`
  let rhs : Π a : ℕ, ℕ →* ℤ := λ a,
  { to_fun := λ x, qr_sign x a * [x | a]ⱼ,
    map_one' := by rw [nat.cast_one, qr_sign, χ₄_nat_one_mod_four (by norm_num : 1 % 4 = 1),
                       jacobi_sym_one_left, mul_one],
    map_mul' := λ x y, by rw [qr_sign_mul_left, nat.cast_mul, jacobi_sym_mul_left,
                              mul_mul_mul_comm] },
  have rhs_apply : ∀ (a b : ℕ), rhs a b = qr_sign b a * [b | a]ⱼ := λ a b, rfl,
  refine jacobi_sym_value a (rhs a) (λ p pp hp, eq.symm _) hb,
  have hpo := pp.eq_two_or_odd'.resolve_left hp,
  rw [@legendre_sym.to_jacobi_sym p ⟨pp⟩, rhs_apply, coe_nat_nat,
      qr_sign_eq_iff_eq hpo ha, qr_sign_symm hpo ha],
  refine jacobi_sym_value p (rhs p) (λ q pq hq, _) ha,
  have hqo := pq.eq_two_or_odd'.resolve_left hq,
  rw [rhs_apply, coe_nat_nat, ← @legendre_sym.to_jacobi_sym p ⟨pp⟩, qr_sign_symm hqo hpo,
      qr_sign_neg_one_pow hpo hqo, @quadratic_reciprocity' p q ⟨pp⟩ ⟨pq⟩ hp hq],
end

/-- The Law of Quadratic Reciprocity for the Jacobi symbol -/
lemma jacobi_sym_quadratic_reciprocity {a b : ℕ} (ha : odd a) (hb : odd b) :
  [a | b]ⱼ = (-1) ^ ((a / 2) * (b / 2)) * [b | a]ⱼ :=
by rw [← qr_sign_neg_one_pow ha hb, qr_sign_symm ha hb, jacobi_sym_quadratic_reciprocity' ha hb]

/-- The Law of Quadratic Reciprocity for the Jacobi symbol: if `a` and `b` are natural numbers
with `a % 4 = 1` and `b` odd, then `(a / b) = (b / a)`. -/
theorem jacobi_sym_quadratic_reciprocity_one_mod_four {a b : ℕ} (ha : a % 4 = 1) (hb : odd b) :
  [a | b]ⱼ = [b | a]ⱼ :=
by rw [jacobi_sym_quadratic_reciprocity (odd_iff.mpr (odd_of_mod_four_eq_one ha)) hb,
       pow_mul, neg_one_pow_div_two_of_one_mod_four ha, one_pow, one_mul]

/-- The Law of Quadratic Reciprocityfor the Jacobi symbol: if `a` and `b` are natural numbers
both congruent to `3` mod `4`, then `(a / b) = -(b / a)`. -/
theorem jacobi_sym_quadratic_reciprocity_three_mod_four
  {a b : ℕ} (ha : a % 4 = 3) (hb : b % 4 = 3) :
  [a | b]ⱼ = - [b | a]ⱼ :=
let nop := @neg_one_pow_div_two_of_three_mod_four in begin
  rw [jacobi_sym_quadratic_reciprocity, pow_mul, nop ha, nop hb, neg_one_mul];
  rwa [odd_iff, odd_of_mod_four_eq_three],
end

/-- The Jacobi symbol `(a / b)` depends only on `b` mod `4*a` (version for `a : ℕ`). -/
lemma jacobi_sym_mod_right' (a : ℕ) {b : ℕ} (hb : odd b) : [a | b]ⱼ = [a | b % (4 * a)]ⱼ :=
begin
  cases eq_or_ne a 0 with ha₀ ha₀,
  { rw [ha₀, mul_zero, mod_zero], },
  have hb' : odd (b % (4 * a)) := odd.mod_even hb (even.mul_right (by norm_num) _),
  rcases two_pow_mul_odd ha₀ with ⟨e, a', ha₁, ha₂⟩,
  nth_rewrite 1 [ha₂], nth_rewrite 0 [ha₂],
  rw [nat.cast_mul, jacobi_sym_mul_left, jacobi_sym_mul_left,
      jacobi_sym_quadratic_reciprocity' ha₁ hb, jacobi_sym_quadratic_reciprocity' ha₁ hb',
      nat.cast_pow, jacobi_sym_pow_left, jacobi_sym_pow_left,
      (by norm_cast : ((2 : ℕ) : ℤ) = 2), jacobi_sym_two hb, jacobi_sym_two hb'],
  have H : qr_sign b a' * [b | a']ⱼ = qr_sign (b % (4 * a)) a' * [b % (4 * a) | a']ⱼ,
  { simp_rw [qr_sign],
    have ha' : (a' : ℤ) ∣ 4 * a,
    { rw [ha₂, nat.cast_mul, ← mul_assoc],
      exact dvd_mul_left a' _, },
    rw [χ₄_nat_mod_four, χ₄_nat_mod_four (b % (4 * a)), mod_mod_of_dvd b (dvd_mul_right 4 a),
        jacobi_sym_mod_left b, jacobi_sym_mod_left (b % (4 * a)), int.mod_mod_of_dvd b ha'], },
  cases eq_or_ne e 0 with he he,
  { rwa [he, pow_zero, pow_zero, one_mul, one_mul], },
  { have h2 : 8 ∣ 4 * a,
    { rw [ha₂, ← nat.add_sub_of_le (nat.pos_of_ne_zero he), pow_add, pow_one,
          ← mul_assoc, ← mul_assoc, (by norm_num : 4 * 2 = 8), mul_assoc],
      exact dvd_mul_right 8 _, },
    rw [H, χ₈_nat_mod_eight, χ₈_nat_mod_eight (b % (4 * a)), mod_mod_of_dvd b h2],
    refl, }
end

/-- The Jacobi symbol `(a / b)` depends only on `b` mod `4*a`. -/
lemma jacobi_sym_mod_right (a : ℤ) {b : ℕ} (hb : odd b) : [a | b]ⱼ = [a | b % (4 * a.nat_abs)]ⱼ :=
begin
  cases int.nat_abs_eq a with ha ha; nth_rewrite 1 [ha]; nth_rewrite 0 [ha],
  { -- `a = a.nat_abs`
    exact jacobi_sym_mod_right' a.nat_abs hb, },
  { -- `a = - a.nat_abs`
    have hb' : odd (b % (4 * a.nat_abs)) := odd.mod_even hb (even.mul_right (by norm_num) _),
    rw [jacobi_sym_neg _ hb, jacobi_sym_neg _ hb', jacobi_sym_mod_right' _ hb, χ₄_nat_mod_four,
        χ₄_nat_mod_four (b % (4 * _)), mod_mod_of_dvd b (dvd_mul_right 4 _)], }
end

end jacobi
