/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kevin Buzzard
-/
import data.rat
import data.fintype.card
import algebra.big_operators.nat_antidiagonal
import ring_theory.power_series.well_known

/-!
# Bernoulli numbers

The Bernoulli numbers are a sequence of rational numbers that frequently show up in
number theory.

## Mathematical overview

The Bernoulli numbers $(B_0, B_1, B_2, \ldots)=(1, -1/2, 1/6, 0, -1/30, \ldots)$ are
a sequence of rational numbers. They show up in the formula for the sums of $k$th
powers. They are related to the Taylor series expansions of $x/\tan(x)$ and
of $\coth(x)$, and also show up in the values that the Riemann Zeta function
takes both at both negative and positive integers (and hence in the
theory of modular forms). For example, if $1 \leq n$ is even then

$$\zeta(2n)=\sum_{t\geq1}t^{-2n}=(-1)^{n+1}\frac{(2\pi)^{2n}B_{2n}}{2(2n)!}.$$

Note however that this result is not yet formalised in Lean.

The Bernoulli numbers can be formally defined using the power series

$$\sum B_n\frac{t^n}{n!}=\frac{t}{1-e^{-t}}$$

although that happens to not be the definition in mathlib (this is an *implementation
detail* though, and need not concern the mathematician).

Note that $B_1=-1/2$, meaning that we are using the $B_n^-$ of
[from Wikipedia](https://en.wikipedia.org/wiki/Bernoulli_number).

## Implementation detail

The Bernoulli numbers are defined using well-founded induction, by the formula
$$B_n=1-\sum_{k\lt n}\frac{\binom{n}{k}}{n-k+1}B_k.$$
This formula is true for all $n$ and in particular $B_0=1$. Note that this is the definition
for positive Bernoulli numbers, which we call `bernoulli'`. The negative Bernoulli numbers are
then defined as `bernoulli = (-1)^n * bernoulli'`.

## Main theorems

`sum_bernoulli : ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli k = 0`

-/

open_locale big_operators
open_locale nat
open nat
open finset

/-!

### Definitions

-/

/-- The Bernoulli numbers:
the $n$-th Bernoulli number $B_n$ is defined recursively via
$$B_n = 1 - \sum_{k < n} \binom{n}{k}\frac{B_k}{n+1-k}$$ -/
def bernoulli' : ℕ → ℚ :=
well_founded.fix lt_wf
  (λ n bernoulli', 1 - ∑ k : fin n, n.choose k / (n - k + 1) * bernoulli' k k.2)

lemma bernoulli'_def' (n : ℕ) :
  bernoulli' n = 1 - ∑ k : fin n, (n.choose k) / (n - k + 1) * bernoulli' k :=
well_founded.fix_eq _ _ _

lemma bernoulli'_def (n : ℕ) :
  bernoulli' n = 1 - ∑ k in range n, (n.choose k) / (n - k + 1) * bernoulli' k :=
by { rw [bernoulli'_def', ← fin.sum_univ_eq_sum_range], refl }

lemma bernoulli'_spec (n : ℕ) :
  ∑ k in range n.succ, (n.choose (n - k) : ℚ) / (n - k + 1) * bernoulli' k = 1 :=
begin
  rw [sum_range_succ, bernoulli'_def n, nat.sub_self],
  conv in (nat.choose _ (_ - _)) { rw choose_symm (le_of_lt (mem_range.1 H)) },
  simp only [one_mul, cast_one, sub_self, sub_add_cancel, choose_zero_right, zero_add, div_one],
end

lemma bernoulli'_spec' (n : ℕ) :
  ∑ k in nat.antidiagonal n,
  ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli' k.1 = 1 :=
begin
  refine ((nat.sum_antidiagonal_eq_sum_range_succ_mk _ n).trans _).trans (bernoulli'_spec n),
  refine sum_congr rfl (λ x hx, _),
  rw mem_range_succ_iff at hx,
  simp [nat.add_sub_cancel' hx, cast_sub hx],
end

/-!

### Examples

-/

section examples

open finset

@[simp] lemma bernoulli'_zero : bernoulli' 0 = 1 := rfl

@[simp] lemma bernoulli'_one : bernoulli' 1 = 1/2 :=
begin
    rw [bernoulli'_def, sum_range_one], norm_num
end

@[simp] lemma bernoulli'_two : bernoulli' 2 = 1/6 :=
begin
  rw [bernoulli'_def, sum_range_succ, sum_range_one], norm_num
end

@[simp] lemma bernoulli'_three : bernoulli' 3 = 0 :=
begin
  rw [bernoulli'_def, sum_range_succ, sum_range_succ, sum_range_one], norm_num
end

@[simp] lemma bernoulli'_four : bernoulli' 4 = -1/30 :=
begin
  rw [bernoulli'_def, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_one],
  rw (show nat.choose 4 2 = 6, from dec_trivial), -- shrug
  norm_num,
end

end examples

open nat finset

@[simp] lemma sum_bernoulli' (n : ℕ) :
  ∑ k in range n, (n.choose k : ℚ) * bernoulli' k = n :=
begin
  cases n with n, { simp },
  rw [sum_range_succ, bernoulli'_def],
  suffices : (n + 1 : ℚ) * ∑ k in range n, (n.choose k : ℚ) / (n - k + 1) * bernoulli' k =
    ∑ x in range n, (n.succ.choose x : ℚ) * bernoulli' x,
  { rw [← this, choose_succ_self_right], norm_cast, ring},
  simp_rw [mul_sum, ← mul_assoc],
  apply sum_congr rfl,
  intros k hk, replace hk := le_of_lt (mem_range.1 hk),
  rw ← cast_sub hk,
  congr',
  field_simp [show ((n - k : ℕ) : ℚ) + 1 ≠ 0, by {norm_cast, simp}],
  norm_cast,
  rw [mul_comm, nat.sub_add_eq_add_sub hk],
  exact choose_mul_succ_eq n k,
end

open power_series
variables (A : Type*) [comm_ring A] [algebra ℚ A]


/-- The exponential generating function for the Bernoulli numbers `bernoulli' n`. -/
def bernoulli'_power_series := power_series.mk (λ n, algebra_map ℚ A (bernoulli' n / n!))

theorem bernoulli'_power_series_mul_exp_sub_one :
  bernoulli'_power_series A * (exp A - 1) = X * exp A :=
begin
  ext n,
  -- constant coefficient is a special case
  cases n,
  { simp only [ring_hom.map_sub, constant_coeff_one, zero_mul, constant_coeff_exp, constant_coeff_X,
      coeff_zero_eq_constant_coeff, mul_zero, sub_self, ring_hom.map_mul] },
  rw [bernoulli'_power_series, coeff_mul, mul_comm X, coeff_succ_mul_X],
  simp only [coeff_mk, coeff_one, coeff_exp, linear_map.map_sub, factorial,
    rat.algebra_map_rat_rat, nat.sum_antidiagonal_succ', if_pos],
  simp only [factorial, prod.snd, one_div, cast_succ, cast_one, cast_mul, ring_hom.id_apply,
    sub_zero, add_eq_zero_iff, if_false, zero_add, one_ne_zero,
    factorial, div_one, mul_zero, and_false, sub_self],
  suffices : ∑ (p : ℕ × ℕ) in nat.antidiagonal n, (bernoulli' p.fst / ↑(p.fst)!)
                * ((↑(p.snd) + 1) * ↑(p.snd)!)⁻¹ = (↑n!)⁻¹,
  { convert congr_arg (algebra_map ℚ A) this,
    simp [ring_hom.map_sum] },
  apply eq_inv_of_mul_left_eq_one,
  rw sum_mul,
  convert bernoulli'_spec' n using 1,
  apply sum_congr rfl,
  rintro ⟨i, j⟩ hn,
  rw nat.mem_antidiagonal at hn,
  subst hn,
  dsimp only,
  have hj : (j : ℚ) + 1 ≠ 0, by { norm_cast, linarith },
  have hj' : j.succ ≠ 0, by { show j + 1 ≠ 0, by linarith },
  have hnz : (j + 1 : ℚ) * j! * i! ≠ 0,
  { norm_cast at *,
    exact mul_ne_zero (mul_ne_zero hj (factorial_ne_zero j)) (factorial_ne_zero _), },
  field_simp [hj, hnz],
  rw [mul_comm _ (bernoulli' i), mul_assoc],
  norm_cast,
  rw [mul_comm (j + 1) _, mul_div_assoc, ← mul_assoc, cast_mul, cast_mul, mul_div_mul_right _,
    add_choose, cast_dvd_char_zero],
  { apply factorial_mul_factorial_dvd_factorial_add, },
  { exact cast_ne_zero.mpr hj', },
end

open ring_hom

/-- Odd Bernoulli numbers (greater than 1) are zero. -/
theorem bernoulli'_odd_eq_zero {n : ℕ} (h_odd : odd n) (hlt : 1 < n) : bernoulli' n = 0 :=
begin
  --have f := bernoulli'_power_series,
  have f : power_series.mk (λ n, (bernoulli' n / n!)) * (exp ℚ - 1) = X * exp ℚ,
  { simpa [bernoulli'_power_series] using bernoulli'_power_series_mul_exp_sub_one ℚ },
  have g : eval_neg_hom (mk (λ (n : ℕ), bernoulli' n / ↑(n!)) * (exp ℚ - 1)) * (exp ℚ) =
    (eval_neg_hom (X * exp ℚ)) * (exp ℚ) := by congr',
  rw [map_mul, map_sub, map_one, map_mul, mul_assoc, sub_mul, mul_assoc (eval_neg_hom X) _ _,
    mul_comm (eval_neg_hom (exp ℚ)) (exp ℚ), exp_mul_exp_neg_eq_one, eval_neg_hom_X, mul_one,
    one_mul] at g,
  suffices h : (mk (λ (n : ℕ), bernoulli' n / ↑n!) - eval_neg_hom (mk (λ (n : ℕ),
    bernoulli' n / ↑n!)) ) * (exp ℚ - 1) = X * (exp ℚ - 1),
  { rw [mul_eq_mul_right_iff] at h,
    cases h,
    { simp only [eval_neg_hom, rescale, coeff_mk, coe_mk, power_series.ext_iff,
        coeff_mk, linear_map.map_sub] at h,
      specialize h n,
      rw coeff_X n at h,
      split_ifs at h with h2,
      { rw h2 at hlt, exfalso, exact lt_irrefl _ hlt, },
      have hn : (n! : ℚ) ≠ 0, { simp [factorial_ne_zero], },
      rw [←mul_div_assoc, sub_eq_zero_iff_eq, div_eq_iff hn, div_mul_cancel _ hn,
        neg_one_pow_of_odd h_odd, neg_mul_eq_neg_mul_symm, one_mul] at h,
      exact eq_zero_of_neg_eq h.symm, },
    { exfalso,
      rw [power_series.ext_iff] at h,
      specialize h 1,
      simpa using h, }, },
  { rw [sub_mul, f, mul_sub X, mul_one, sub_right_inj, ←neg_sub, ←neg_neg X, ←g,
      neg_mul_eq_mul_neg], },
end

/-- The Bernoulli numbers are defined to be `bernoulli'` with a parity sign. -/
def bernoulli (n : ℕ) : ℚ := (-1)^n * (bernoulli' n)

lemma bernoulli'_eq_bernoulli (n : ℕ) : bernoulli' n = (-1)^n * bernoulli n :=
by simp [bernoulli, ← mul_assoc, ← pow_two, ← pow_mul, mul_comm n 2, pow_mul]

@[simp] lemma bernoulli_zero : bernoulli 0 = 1 := rfl

@[simp] lemma bernoulli_one : bernoulli 1 = -1/2 :=
by norm_num [bernoulli, bernoulli'_one]

theorem bernoulli_eq_bernoulli'_of_ne_one {n : ℕ} (hn : n ≠ 1) : bernoulli n = bernoulli' n :=
begin
  by_cases n = 0,
  { rw [h, bernoulli'_zero, bernoulli_zero] },
  { rw [bernoulli, neg_one_pow_eq_pow_mod_two],
    by_cases k : n % 2 = 1,
    { have f : 1 < n := one_lt_iff_ne_zero_and_ne_one.2 ⟨h, hn⟩,
      simp [bernoulli'_odd_eq_zero (odd_iff.2 k) f] },
    rw mod_two_ne_one at k, simp [k] }
end

@[simp] theorem sum_bernoulli (n : ℕ):
  ∑ k in range n, (n.choose k : ℚ) * bernoulli k = if n = 1 then 1 else 0 :=
begin
  cases n, { simp only [sum_empty, range_zero, if_false, zero_ne_one], },
  cases n, { simp only [mul_one, cast_one, if_true, choose_succ_self_right, eq_self_iff_true,
    bernoulli_zero, sum_singleton, range_one], },
  rw [sum_range_succ', bernoulli_zero, mul_one, choose_zero_right, cast_one,
    sum_range_succ', bernoulli_one, choose_one_right],
  suffices : ∑ (i : ℕ) in range n, ↑((n + 2).choose (i + 2)) * bernoulli (i + 2) = n/2,
  { rw [this, cast_succ, cast_succ], ring },
  have f := sum_bernoulli' n.succ.succ,
  simp only [sum_range_succ', one_div, bernoulli'_one, cast_succ, mul_one, cast_one, add_left_inj,
    choose_zero_right, bernoulli'_zero, zero_add, choose_one_right, ← eq_sub_iff_add_eq] at f,
  convert f,
  { ext x, rw bernoulli_eq_bernoulli'_of_ne_one (succ_ne_zero x ∘ succ.inj) },
  { ring },
end

lemma bernoulli_spec' (n: ℕ) :
  ∑ k in nat.antidiagonal n,
  ((k.1 + k.2).choose k.2 : ℚ) / (k.2 + 1) * bernoulli k.1 = if n = 0 then 1 else 0 :=
begin
  cases n, { simp },
  rw if_neg (succ_ne_zero _),
  -- algebra facts
  have h₁ : (1, n) ∈ nat.antidiagonal n.succ := by simp [nat.mem_antidiagonal, add_comm],
  have h₂ : (n:ℚ) + 1 ≠ 0 := by exact_mod_cast succ_ne_zero _,
  have h₃ : (1 + n).choose n = n + 1 := by simp [add_comm],
  -- key equation: the corresponding fact for `bernoulli'`
  have H := bernoulli'_spec' n.succ,
  -- massage it to match the structure of the goal, then convert piece by piece
  rw ← add_sum_diff_singleton h₁ at H ⊢,
  apply add_eq_of_eq_sub',
  convert eq_sub_of_add_eq' H using 1,
  { apply sum_congr rfl,
    intros p h,
    obtain ⟨h', h''⟩ : p ∈ _ ∧ p ≠ _ := by rwa [mem_sdiff, mem_singleton] at h,
    have : p.fst ≠ (1, n).fst := by simpa [h''] using nat.antidiagonal_congr h' h₁,
    simp [this, bernoulli_eq_bernoulli'_of_ne_one] },
  { field_simp [h₃],
    norm_num },
end

/-- The exponential generating function for the Bernoulli numbers `bernoulli n`. -/
def bernoulli_power_series := power_series.mk (λ n, algebra_map ℚ A (bernoulli n / n!))

theorem bernoulli_power_series_mul_exp_sub_one :
  bernoulli_power_series A * (exp A - 1) = X :=
begin
  ext n,
  -- constant coefficient is a special case
  cases n, { simp },
  simp only [bernoulli_power_series, coeff_mul, coeff_X, nat.sum_antidiagonal_succ', one_div,
    coeff_mk, coeff_one, coeff_exp, linear_map.map_sub, factorial, if_pos, cast_succ, cast_one,
    cast_mul, sub_zero, map_one, add_eq_zero_iff, if_false, inv_one, zero_add, one_ne_zero,
    mul_zero, and_false, sub_self, ←map_mul, ←map_sum],
  suffices : ∑ x in nat.antidiagonal n, bernoulli x.fst / ↑x.fst! * ((↑x.snd + 1) * ↑x.snd!)⁻¹
           = if n.succ = 1 then 1 else 0, { split_ifs; simp [h, this] },
  cases n, { simp },
  have hfact : ∀ m, (m! : ℚ) ≠ 0 := λ m, by exact_mod_cast factorial_ne_zero m,
  have hn : n.succ.succ ≠ 1, by { show n + 2 ≠ 1, by linarith },
  have hite1 : ite (n.succ.succ = 1) 1 0 = (0 / n.succ! : ℚ) := by simp [hn],
  have hite2 : ite (n.succ = 0) 1 0 = (0 : ℚ) := by simp [succ_ne_zero],
  rw [hite1, eq_div_iff (hfact n.succ), ←hite2, ←bernoulli_spec', sum_mul],
  apply sum_congr rfl,
  rintro ⟨i, j⟩ h,
  rw nat.mem_antidiagonal at h,
  have hj : (j.succ : ℚ) ≠ 0 := by exact_mod_cast succ_ne_zero j,
  field_simp [←h, mul_ne_zero hj (hfact j), hfact i, mul_comm _ (bernoulli i), mul_assoc],
  rw_mod_cast [mul_comm (j + 1), mul_div_assoc, ← mul_assoc],
  rw [cast_mul, cast_mul, mul_div_mul_right _ _ hj, add_choose, cast_dvd_char_zero],
  exact factorial_mul_factorial_dvd_factorial_add i j,
end


section faulhaber

/-- Faulhaber's theorem relating the sum of of p-th powers to the Bernoulli numbers.
See https://proofwiki.org/wiki/Faulhaber%27s_Formula and [orosi2018faulhaber] for
the proof provided here. -/
theorem sum_range_pow (n p : ℕ) :
  ∑ k in range n, (k : ℚ) ^ p =
    ∑ i in range (p + 1), bernoulli i * (p + 1).choose i * n ^ (p + 1 - i) / (p + 1) :=
begin
  -- trivial fact about cast factorials
  have hne : ∀ m : ℕ, (m! : ℚ) ≠ 0 := λ m, by exact_mod_cast factorial_ne_zero m,
  -- the Cauchy product of two power series
  have h_cauchy : mk (λ p, bernoulli p / ↑p!) * mk (λ q, coeff ℚ (q + 1) (exp ℚ ^ n))
                = mk (λ p, ∑ i in range (p + 1),
                      bernoulli i * ↑((p + 1).choose i) * ↑n ^ (p + 1 - i) / ↑(p + 1)!),
  { ext q,
    let f := λ a, λ b, bernoulli a / ↑a! * coeff ℚ (b + 1) (exp ℚ ^ n),
    -- key step: using `power_series.coeff_mul` and then rewriting sums
    simp only [coeff_mul, coeff_mk, cast_mul, nat.sum_antidiagonal_eq_sum_range_succ f],
    refine sum_congr rfl _,
    simp_intros m h only [finset.mem_range],
    simp only [f, exp_pow_eq_rescale_exp, rescale, one_div, coeff_mk, ring_hom.coe_mk, coeff_exp,
              ring_hom.id_apply, cast_mul, rat.algebra_map_rat_rat],
    -- manipulate factorials and binomial coefficients
    rw [choose_eq_factorial_div_factorial h.le, eq_comm, div_eq_iff (hne q.succ), succ_eq_add_one,
        mul_assoc _ _ ↑q.succ!, mul_comm _ ↑q.succ!, ←mul_assoc, div_mul_eq_mul_div,
        mul_comm (n ^ (q - m + 1) : ℚ), ←mul_assoc _ _ (n ^ (q - m + 1) : ℚ), ←one_div, mul_one_div,
        div_div_eq_div_mul, ←nat.sub_add_comm (le_of_lt_succ h), cast_dvd, cast_mul],
    { ring },
    { exact factorial_mul_factorial_dvd_factorial h.le },
    { simp [hne] } },
  -- same as our goal except we pull out `p!` for convenience
  have hps : ∑ k in range n, ↑k ^ p
          = (∑ i in range (p + 1), bernoulli i * ↑((p + 1).choose i) * ↑n ^ (p + 1 - i) / ↑(p + 1)!)
            * ↑p!,
  { suffices : power_series.mk (λ p, ∑ k in range n, ↑k ^ p * algebra_map ℚ ℚ (↑p!)⁻¹)
             = power_series.mk (λ p, ∑ i in range (p + 1),
                                bernoulli i * ↑((p + 1).choose i) * ↑n ^ (p + 1 - i) / ↑(p + 1)!),
    { rw [← div_eq_iff (hne p), div_eq_mul_inv, sum_mul],
      rw power_series.ext_iff at this,
      simpa using this p },
    -- the power series `exp ℚ - 1` is non-zero, a fact we need in order to use `mul_right_inj'`
    have hexp : exp ℚ - 1 ≠ 0,
    { simp only [exp, power_series.ext_iff, ne, not_forall],
      use 1,
      simp },
    have h_r : exp ℚ ^ n - 1 = X * mk (λ p, coeff ℚ (p + 1) (exp ℚ ^ n)),
    { have h_const : C ℚ (constant_coeff ℚ (exp ℚ ^ n)) = 1 := by simp,
      rw [←h_const, sub_const_eq_X_mul_shift] },
    -- key step: a chain of equalities of power series
    rw [←mul_right_inj' hexp, mul_comm, ←exp_pow_sum, ←geom_series_def, geom_sum_mul, h_r,
        ←bernoulli_power_series_mul_exp_sub_one, bernoulli_power_series, mul_right_comm],
    simp [h_cauchy, mul_comm] },
  -- the rest is showing that `hps` can be massaged into our goal
  rw [hps, sum_mul],
  refine sum_congr rfl (λ x hx, _),
  field_simp [mul_right_comm _ ↑p!, ←mul_assoc _ _ ↑p!, cast_add_one_ne_zero, hne],
end

/-- Alternate form of Faulhaber's theorem, relating the sum of p-th powers to the Bernoulli numbers.
Deduced from `sum_range_pow`. -/
theorem sum_range_pow' (n p : ℕ) :
  ∑ k in Ico 1 (n + 1), (k : ℚ) ^ p =
    ∑ i in range (p + 1), bernoulli' i * (p + 1).choose i * n ^ (p + 1 - i) / (p + 1) :=
begin
  -- dispose of the trivial case
  cases p, { simp },
  let f := λ i, bernoulli i * p.succ.succ.choose i * n ^ (p.succ.succ - i) / p.succ.succ,
  let f' := λ i, bernoulli' i * p.succ.succ.choose i * n ^ (p.succ.succ - i) / p.succ.succ,
  suffices : ∑ k in Ico 1 n.succ, ↑k ^ p.succ = ∑ i in range p.succ.succ, f' i, { convert this },
  -- prove some algebraic facts that will make things easier for us later on
  have hle := le_add_left 1 n,
  have hne : (p + 1 + 1 : ℚ) ≠ 0 := by exact_mod_cast succ_ne_zero p.succ,
  have h1 : ∀ r : ℚ, r * (p + 1 + 1 : ℚ) * n ^ p.succ / (p + 1 + 1 : ℚ) = r * n ^ p.succ :=
    λ r, by rw [mul_div_right_comm, mul_div_cancel _ hne],
  have h2 : f 1 + n ^ p.succ = 1 / 2 * n ^ p.succ,
  { simp_rw [f, bernoulli_one, choose_one_right, succ_sub_succ_eq_sub, cast_succ, nat.sub_zero, h1],
    ring },
  have : ∑ i in range p, bernoulli (i + 2) * ↑((p + 2).choose (i + 2)) * ↑n ^ (p - i) / ↑(p + 2)
       = ∑ i in range p, bernoulli' (i + 2) * ↑((p + 2).choose (i + 2)) * ↑n ^ (p - i) / ↑(p + 2) :=
    sum_congr rfl (λ i h, by rw bernoulli_eq_bernoulli'_of_ne_one (succ_succ_ne_one i)),
  calc  ∑ k in Ico 1 n.succ, ↑k ^ p.succ
        -- replace sum over `Ico` with sum over `range` and simplify
      = ∑ k in range n.succ, ↑k ^ p.succ : by simp [sum_Ico_eq_sub _ hle, succ_ne_zero]
        -- extract the last term of the sum
  ... = ∑ k in range n, (k : ℚ) ^ p.succ + n ^ p.succ : by rw [sum_range_succ, add_comm]
        -- apply the key lemma, `sum_range_pow`
  ... = ∑ i in range p.succ.succ, f i + n ^ p.succ : by simp [f, sum_range_pow]
        -- extract the first two terms of the sum
  ... = ∑ i in range p, f i.succ.succ + f 1 + f 0 + n ^ p.succ : by simp_rw [sum_range_succ']
  ... = ∑ i in range p, f i.succ.succ + (f 1 + n ^ p.succ) + f 0 : by ring
  ... = ∑ i in range p, f i.succ.succ + 1 / 2 * n ^ p.succ + f 0 : by rw h2
        -- convert from `bernoulli` to `bernoulli'`
  ... = ∑ i in range p, f' i.succ.succ + f' 1 + f' 0 : by { simp only [f, f'], simpa [h1] }
        -- rejoin the first two terms of the sum
  ... = ∑ i in range p.succ.succ, f' i : by simp_rw [sum_range_succ'],
end

end faulhaber
