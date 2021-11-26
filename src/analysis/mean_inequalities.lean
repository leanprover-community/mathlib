/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import analysis.convex.specific_functions
import data.real.conjugate_exponents

/-!
# Mean value inequalities

In this file we prove several inequalities for finite sums, including AM-GM inequality,
Young's inequality, Hölder inequality, and Minkowski inequality. Versions for integrals of some of
these inequalities are available in `measure_theory.mean_inequalities`.

## Main theorems

### AM-GM inequality:

The inequality says that the geometric mean of a tuple of non-negative numbers is less than or equal
to their arithmetic mean. We prove the weighted version of this inequality: if $w$ and $z$
are two non-negative vectors and $\sum_{i\in s} w_i=1$, then
$$
\prod_{i\in s} z_i^{w_i} ≤ \sum_{i\in s} w_iz_i.
$$
The classical version is a special case of this inequality for $w_i=\frac{1}{n}$.

We prove a few versions of this inequality. Each of the following lemmas comes in two versions:
a version for real-valued non-negative functions is in the `real` namespace, and a version for
`nnreal`-valued functions is in the `nnreal` namespace.

- `geom_mean_le_arith_mean_weighted` : weighted version for functions on `finset`s;
- `geom_mean_le_arith_mean2_weighted` : weighted version for two numbers;
- `geom_mean_le_arith_mean3_weighted` : weighted version for three numbers;
- `geom_mean_le_arith_mean4_weighted` : weighted version for four numbers.

### Young's inequality

Young's inequality says that for non-negative numbers `a`, `b`, `p`, `q` such that
$\frac{1}{p}+\frac{1}{q}=1$ we have
$$
ab ≤ \frac{a^p}{p} + \frac{b^q}{q}.
$$

This inequality is a special case of the AM-GM inequality. It is then used to prove Hölder's
inequality (see below).

### Hölder's inequality

The inequality says that for two conjugate exponents `p` and `q` (i.e., for two positive numbers
such that $\frac{1}{p}+\frac{1}{q}=1$) and any two non-negative vectors their inner product is
less than or equal to the product of the $L_p$ norm of the first vector and the $L_q$ norm of the
second vector:
$$
\sum_{i\in s} a_ib_i ≤ \sqrt[p]{\sum_{i\in s} a_i^p}\sqrt[q]{\sum_{i\in s} b_i^q}.
$$

We give versions of this result in `ℝ`, `ℝ≥0` and `ℝ≥0∞`.

There are at least two short proofs of this inequality. In our proof we prenormalize both vectors,
then apply Young's inequality to each $a_ib_i$. Another possible proof would be to deduce this
inequality from the generalized mean inequality for well-chosen vectors and weights.

### Minkowski's inequality

The inequality says that for `p ≥ 1` the function
$$
\|a\|_p=\sqrt[p]{\sum_{i\in s} a_i^p}
$$
satisfies the triangle inequality $\|a+b\|_p\le \|a\|_p+\|b\|_p$.

We give versions of this result in `real`, `ℝ≥0` and `ℝ≥0∞`.

We deduce this inequality from Hölder's inequality. Namely, Hölder inequality implies that $\|a\|_p$
is the maximum of the inner product $\sum_{i\in s}a_ib_i$ over `b` such that $\|b\|_q\le 1$. Now
Minkowski's inequality follows from the fact that the maximum value of the sum of two functions is
less than or equal to the sum of the maximum values of the summands.

## TODO

- each inequality `A ≤ B` should come with a theorem `A = B ↔ _`; one of the ways to prove them
  is to define `strict_convex_on` functions.
- generalized mean inequality with any `p ≤ q`, including negative numbers;
- prove that the power mean tends to the geometric mean as the exponent tends to zero.

-/

universes u v

open finset
open_locale classical big_operators nnreal ennreal
noncomputable theory

variables {ι : Type u} (s : finset ι)

section geom_mean_le_arith_mean

/-! ### AM-GM inequality -/

namespace real

/-- AM-GM inequality: the **geometric mean is less than or equal to the arithmetic mean**, weighted
version for real-valued nonnegative functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
  (∏ i in s, (z i) ^ (w i)) ≤ ∑ i in s, w i * z i :=
begin
  -- If some number `z i` equals zero and has non-zero weight, then LHS is 0 and RHS is nonnegative.
  by_cases A : ∃ i ∈ s, z i = 0 ∧ w i ≠ 0,
  { rcases A with ⟨i, his, hzi, hwi⟩,
    rw [prod_eq_zero his],
    { exact sum_nonneg (λ j hj, mul_nonneg (hw j hj) (hz j hj)) },
    { rw hzi, exact zero_rpow hwi } },
  -- If all numbers `z i` with non-zero weight are positive, then we apply Jensen's inequality
  -- for `exp` and numbers `log (z i)` with weights `w i`.
  { simp only [not_exists, not_and, ne.def, not_not] at A,
    have := convex_on_exp.map_sum_le hw hw' (λ i _, set.mem_univ $ log (z i)),
    simp only [exp_sum, (∘), smul_eq_mul, mul_comm (w _) (log _)] at this,
    convert this using 1; [apply prod_congr rfl, apply sum_congr rfl]; intros i hi,
    { cases eq_or_lt_of_le (hz i hi) with hz hz,
      { simp [A i hi hz.symm] },
      { exact rpow_def_of_pos hz _ } },
    { cases eq_or_lt_of_le (hz i hi) with hz hz,
      { simp [A i hi hz.symm] },
      { rw [exp_log hz] } } }
end

end real

namespace nnreal

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for `nnreal`-valued functions. -/
theorem geom_mean_le_arith_mean_weighted (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) :
  (∏ i in s, (z i) ^ (w i:ℝ)) ≤ ∑ i in s, w i * z i :=
by exact_mod_cast real.geom_mean_le_arith_mean_weighted _ _ _ (λ i _, (w i).coe_nonneg)
  (by assumption_mod_cast) (λ i _, (z i).coe_nonneg)

/-- The geometric mean is less than or equal to the arithmetic mean, weighted version
for two `nnreal` numbers. -/
theorem geom_mean_le_arith_mean2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) :
  w₁ + w₂ = 1 → p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) ≤ w₁ * p₁ + w₂ * p₂ :=
by simpa only [fin.prod_univ_succ, fin.sum_univ_succ, finset.prod_empty, finset.sum_empty,
  fintype.univ_of_is_empty, fin.cons_succ, fin.cons_zero, add_zero, mul_one]
using geom_mean_le_arith_mean_weighted (univ : finset (fin 2))
  (fin.cons w₁ $ fin.cons w₂ fin_zero_elim) (fin.cons p₁ $ fin.cons p₂ $ fin_zero_elim)

theorem geom_mean_le_arith_mean3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) :
  w₁ + w₂ + w₃ = 1 → p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) * p₃ ^ (w₃:ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
by simpa only  [fin.prod_univ_succ, fin.sum_univ_succ, finset.prod_empty, finset.sum_empty,
  fintype.univ_of_is_empty, fin.cons_succ, fin.cons_zero, add_zero, mul_one, ← add_assoc, mul_assoc]
using geom_mean_le_arith_mean_weighted (univ : finset (fin 3))
  (fin.cons w₁ $ fin.cons w₂ $ fin.cons w₃ fin_zero_elim)
  (fin.cons p₁ $ fin.cons p₂ $ fin.cons p₃ fin_zero_elim)

theorem geom_mean_le_arith_mean4_weighted (w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ≥0) :
  w₁ + w₂ + w₃ + w₄ = 1 → p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) * p₃ ^ (w₃:ℝ)* p₄ ^ (w₄:ℝ) ≤
    w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
by simpa only  [fin.prod_univ_succ, fin.sum_univ_succ, finset.prod_empty, finset.sum_empty,
  fintype.univ_of_is_empty, fin.cons_succ, fin.cons_zero, add_zero, mul_one, ← add_assoc, mul_assoc]
using geom_mean_le_arith_mean_weighted (univ : finset (fin 4))
  (fin.cons w₁ $ fin.cons w₂ $ fin.cons w₃ $ fin.cons w₄ fin_zero_elim)
  (fin.cons p₁ $ fin.cons p₂ $ fin.cons p₃ $ fin.cons p₄ fin_zero_elim)

end nnreal

namespace real

theorem geom_mean_le_arith_mean2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
  (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
nnreal.geom_mean_le_arith_mean2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ $
  nnreal.coe_eq.1 $ by assumption

theorem geom_mean_le_arith_mean3_weighted {w₁ w₂ w₃ p₁ p₂ p₃ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
  (hw₃ : 0 ≤ w₃) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃) (hw : w₁ + w₂ + w₃ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ :=
nnreal.geom_mean_le_arith_mean3_weighted
  ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ $ nnreal.coe_eq.1 hw

theorem geom_mean_le_arith_mean4_weighted {w₁ w₂ w₃ w₄ p₁ p₂ p₃ p₄ : ℝ} (hw₁ : 0 ≤ w₁)
  (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hw₄ : 0 ≤ w₄) (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
  (hp₄ : 0 ≤ p₄) (hw : w₁ + w₂ + w₃ + w₄ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ * p₄ ^ w₄ ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃ + w₄ * p₄ :=
nnreal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩
  ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩ $ nnreal.coe_eq.1 $ by assumption

end real

end geom_mean_le_arith_mean

section young

/-! ### Young's inequality -/

namespace real

/-- Young's inequality, a version for nonnegative real numbers. -/
theorem young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
  (hpq : p.is_conjugate_exponent q) :
  a * b ≤ a^p / p + b^q / q :=
by simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul]
  using geom_mean_le_arith_mean2_weighted hpq.one_div_nonneg hpq.symm.one_div_nonneg
    (rpow_nonneg_of_nonneg ha p) (rpow_nonneg_of_nonneg hb q) hpq.inv_add_inv_conj

/-- Young's inequality, a version for arbitrary real numbers. -/
theorem young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  a * b ≤ |a|^p / p + |b|^q / q :=
calc a * b ≤ |a * b|                   : le_abs_self (a * b)
       ... = |a| * |b|                 : abs_mul a b
       ... ≤ |a|^p / p + |b|^q / q :
  real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

end real

namespace nnreal

/-- Young's inequality, `ℝ≥0` version. We use `{p q : ℝ≥0}` in order to avoid constructing
witnesses of `0 ≤ p` and `0 ≤ q` for the denominators.  -/
theorem young_inequality (a b : ℝ≥0) {p q : ℝ≥0} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
  a * b ≤ a^(p:ℝ) / p + b^(q:ℝ) / q :=
real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg ⟨hp, nnreal.coe_eq.2 hpq⟩

/-- Young's inequality, `ℝ≥0` version with real conjugate exponents. -/
theorem young_inequality_real (a b : ℝ≥0) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  a * b ≤ a ^ p / real.to_nnreal p + b ^ q / real.to_nnreal q :=
begin
  nth_rewrite 0 ← real.coe_to_nnreal p hpq.nonneg,
  nth_rewrite 0 ← real.coe_to_nnreal q hpq.symm.nonneg,
  exact young_inequality a b hpq.one_lt_nnreal hpq.inv_add_inv_conj_nnreal,
end

end nnreal

namespace ennreal

/-- Young's inequality, `ℝ≥0∞` version with real conjugate exponents. -/
theorem young_inequality (a b : ℝ≥0∞) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  a * b ≤ a ^ p / ennreal.of_real p + b ^ q / ennreal.of_real q :=
begin
  by_cases h : a = ⊤ ∨ b = ⊤,
  { refine le_trans le_top (le_of_eq _),
    repeat { rw div_eq_mul_inv },
    cases h; rw h; simp [h, hpq.pos, hpq.symm.pos], },
  push_neg at h, -- if a ≠ ⊤ and b ≠ ⊤, use the nnreal version: nnreal.young_inequality_real
  rw [←coe_to_nnreal h.left, ←coe_to_nnreal h.right, ←coe_mul,
    coe_rpow_of_nonneg _ hpq.nonneg, coe_rpow_of_nonneg _ hpq.symm.nonneg, ennreal.of_real,
    ennreal.of_real, ←@coe_div (real.to_nnreal p) _ (by simp [hpq.pos]),
    ←@coe_div (real.to_nnreal q) _ (by simp [hpq.symm.pos]), ←coe_add, coe_le_coe],
  exact nnreal.young_inequality_real a.to_nnreal b.to_nnreal hpq,
end

end ennreal

end young

section holder_minkowski

/-! ### Hölder's and Minkowski's inequalities -/

namespace nnreal

private lemma inner_le_Lp_mul_Lp_of_norm_le_one (f g : ι → ℝ≥0) {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) (hf : ∑ i in s, (f i) ^ p ≤ 1) (hg : ∑ i in s, (g i) ^ q ≤ 1) :
  ∑ i in s, f i * g i ≤ 1 :=
begin
  have hp_ne_zero : real.to_nnreal p ≠ 0, from (zero_lt_one.trans hpq.one_lt_nnreal).ne.symm,
  have hq_ne_zero : real.to_nnreal q ≠ 0, from (zero_lt_one.trans hpq.symm.one_lt_nnreal).ne.symm,
  calc ∑ i in s, f i * g i
      ≤ ∑ i in s, ((f i) ^ p / real.to_nnreal p + (g i) ^ q / real.to_nnreal q) :
    finset.sum_le_sum (λ i his, young_inequality_real (f i) (g i) hpq)
  ... = (∑ i in s, (f i) ^ p) / real.to_nnreal p + (∑ i in s, (g i) ^ q) / real.to_nnreal q :
    by rw [sum_add_distrib, sum_div, sum_div]
  ... ≤ 1 / real.to_nnreal p + 1 / real.to_nnreal q :
    by { refine add_le_add _ _,
      { rwa [div_le_iff hp_ne_zero, div_mul_cancel _ hp_ne_zero], },
      { rwa [div_le_iff hq_ne_zero, div_mul_cancel _ hq_ne_zero], }, }
  ... = 1 : hpq.inv_add_inv_conj_nnreal,
end

private lemma inner_le_Lp_mul_Lp_of_norm_eq_zero (f g : ι → ℝ≥0) {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) (hf : ∑ i in s, (f i) ^ p = 0) :
  ∑ i in s, f i * g i ≤ (∑ i in s, (f i) ^ p) ^ (1 / p) * (∑ i in s, (g i) ^ q) ^ (1 / q) :=
begin
  simp only [hf, hpq.ne_zero, one_div, sum_eq_zero_iff, zero_rpow, zero_mul, inv_eq_zero,
    ne.def, not_false_iff, le_zero_iff, mul_eq_zero],
  intros i his,
  left,
  rw sum_eq_zero_iff at hf,
  exact (rpow_eq_zero_iff.mp (hf i his)).left,
end

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0`-valued functions. -/
theorem inner_le_Lp_mul_Lq (f g : ι → ℝ≥0) {p q : ℝ}
  (hpq : p.is_conjugate_exponent q) :
  ∑ i in s, f i * g i ≤ (∑ i in s, (f i) ^ p) ^ (1 / p) * (∑ i in s, (g i) ^ q) ^ (1 / q) :=
begin
  by_cases hF_zero : ∑ i in s, (f i) ^ p = 0,
  { exact inner_le_Lp_mul_Lp_of_norm_eq_zero s f g hpq hF_zero, },
  by_cases hG_zero : ∑ i in s, (g i) ^ q = 0,
  { calc ∑ i in s, f i * g i
        = ∑ i in s, g i * f i : by { congr' with i, rw mul_comm, }
    ... ≤ (∑ i in s, (g i) ^ q) ^ (1 / q) * (∑ i in s, (f i) ^ p) ^ (1 / p) :
      inner_le_Lp_mul_Lp_of_norm_eq_zero s g f hpq.symm hG_zero
    ... = (∑ i in s, (f i) ^ p) ^ (1 / p) * (∑ i in s, (g i) ^ q) ^ (1 / q) : mul_comm _ _, },
  let f' := λ i, (f i) / (∑ i in s, (f i) ^ p) ^ (1 / p),
  let g' := λ i, (g i) / (∑ i in s, (g i) ^ q) ^ (1 / q),
  suffices : ∑ i in s, f' i * g' i ≤ 1,
  { simp_rw [f', g', div_mul_div, ← sum_div] at this,
    rwa [div_le_iff, one_mul] at this,
    refine mul_ne_zero _ _,
    { rw [ne.def, rpow_eq_zero_iff, auto.not_and_eq], exact or.inl hF_zero, },
    { rw [ne.def, rpow_eq_zero_iff, auto.not_and_eq], exact or.inl hG_zero, }, },
  refine inner_le_Lp_mul_Lp_of_norm_le_one s f' g' hpq (le_of_eq _) (le_of_eq _),
  { simp_rw [f', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel hpq.ne_zero, rpow_one,
      div_self hF_zero], },
  { simp_rw [g', div_rpow, ← sum_div, ← rpow_mul, one_div, inv_mul_cancel hpq.symm.ne_zero,
    rpow_one, div_self hG_zero], },
end

/-- The `L_p` seminorm of a vector `f` is the greatest value of the inner product
`∑ i in s, f i * g i` over functions `g` of `L_q` seminorm less than or equal to one. -/
theorem is_greatest_Lp (f : ι → ℝ≥0) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  is_greatest ((λ g : ι → ℝ≥0, ∑ i in s, f i * g i) ''
    {g | ∑ i in s, (g i)^q ≤ 1}) ((∑ i in s, (f i)^p) ^ (1 / p)) :=
begin
  split,
  { use λ i, ((f i) ^ p / f i / (∑ i in s, (f i) ^ p) ^ (1 / q)),
    by_cases hf : ∑ i in s, (f i)^p = 0,
    { simp [hf, hpq.ne_zero, hpq.symm.ne_zero] },
    { have A : p + q - q ≠ 0, by simp [hpq.ne_zero],
      have B : ∀ y : ℝ≥0, y * y^p / y = y^p,
      { refine λ y, mul_div_cancel_left_of_imp (λ h, _),
        simpa [h, hpq.ne_zero] },
      simp only [set.mem_set_of_eq, div_rpow, ← sum_div, ← rpow_mul,
        div_mul_cancel _ hpq.symm.ne_zero, rpow_one, div_le_iff hf, one_mul, hpq.mul_eq_add,
        ← rpow_sub' _ A, _root_.add_sub_cancel, le_refl, true_and, ← mul_div_assoc, B],
      rw [div_eq_iff, ← rpow_add hf, hpq.inv_add_inv_conj, rpow_one],
      simpa [hpq.symm.ne_zero] using hf } },
  { rintros _ ⟨g, hg, rfl⟩,
    apply le_trans (inner_le_Lp_mul_Lq s f g hpq),
    simpa only [mul_one] using mul_le_mul_left'
      (nnreal.rpow_le_one hg (le_of_lt hpq.symm.one_div_pos)) _ }
end

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `nnreal`-valued functions. -/
theorem Lp_add_le (f g : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) :
  (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤
    (∑ i in s, (f i) ^ p) ^ (1 / p) + (∑ i in s, (g i) ^ p) ^ (1 / p) :=
begin
  -- The result is trivial when `p = 1`, so we can assume `1 < p`.
  rcases eq_or_lt_of_le hp with rfl|hp, { simp [finset.sum_add_distrib] },
  have hpq := real.is_conjugate_exponent_conjugate_exponent hp,
  have := is_greatest_Lp s (f + g) hpq,
  simp only [pi.add_apply, add_mul, sum_add_distrib] at this,
  rcases this.1 with ⟨φ, hφ, H⟩,
  rw ← H,
  exact add_le_add ((is_greatest_Lp s f hpq).2 ⟨φ, hφ, rfl⟩)
    ((is_greatest_Lp s g hpq).2 ⟨φ, hφ, rfl⟩)
end

end nnreal

namespace real

variables (f g : ι → ℝ)  {p q : ℝ}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : is_conjugate_exponent p q) :
  ∑ i in s, f i * g i ≤ (∑ i in s, (abs $ f i)^p) ^ (1 / p) *
  (∑ i in s, (abs $ g i)^q) ^ (1 / q) :=
begin
  have := nnreal.coe_le_coe.2 (nnreal.inner_le_Lp_mul_Lq s (λ i, ⟨_, abs_nonneg (f i)⟩)
    (λ i, ⟨_, abs_nonneg (g i)⟩) hpq),
  push_cast at this,
  refine le_trans (sum_le_sum $ λ i hi, _) this,
  simp only [← abs_mul, le_abs_self]
end

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `real`-valued functions. -/
theorem Lp_add_le (hp : 1 ≤ p) :
  (∑ i in s, (abs $ f i + g i) ^ p) ^ (1 / p) ≤
    (∑ i in s, (abs $ f i) ^ p) ^ (1 / p) + (∑ i in s, (abs $ g i) ^ p) ^ (1 / p) :=
begin
  have := nnreal.coe_le_coe.2 (nnreal.Lp_add_le s (λ i, ⟨_, abs_nonneg (f i)⟩)
    (λ i, ⟨_, abs_nonneg (g i)⟩) hp),
  push_cast at this,
  refine le_trans (rpow_le_rpow _ (sum_le_sum $ λ i hi, _) _) this;
    simp [sum_nonneg, rpow_nonneg_of_nonneg, abs_nonneg, le_trans zero_le_one hp, abs_add,
      rpow_le_rpow]
end

variables {f g}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with real-valued nonnegative functions. -/
theorem inner_le_Lp_mul_Lq_of_nonneg (hpq : is_conjugate_exponent p q)
  (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
  ∑ i in s, f i * g i ≤ (∑ i in s, (f i)^p) ^ (1 / p) * (∑ i in s, (g i)^q) ^ (1 / q) :=
by convert inner_le_Lp_mul_Lq s f g hpq using 3; apply sum_congr rfl; intros i hi;
  simp only [abs_of_nonneg, hf i hi, hg i hi]

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `real`-valued nonnegative
functions. -/
theorem Lp_add_le_of_nonneg (hp : 1 ≤ p) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
  (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤
    (∑ i in s, (f i) ^ p) ^ (1 / p) + (∑ i in s, (g i) ^ p) ^ (1 / p) :=
by convert Lp_add_le s f g hp using 2 ; [skip, congr' 1, congr' 1];
  apply sum_congr rfl; intros i hi; simp only [abs_of_nonneg, hf i hi, hg i hi, add_nonneg]

end real

namespace ennreal

variables (f g : ι → ℝ≥0∞)  {p q : ℝ}

/-- Hölder inequality: the scalar product of two functions is bounded by the product of their
`L^p` and `L^q` norms when `p` and `q` are conjugate exponents. Version for sums over finite sets,
with `ℝ≥0∞`-valued functions. -/
theorem inner_le_Lp_mul_Lq (hpq : p.is_conjugate_exponent q) :
  (∑ i in s, f i * g i) ≤ (∑ i in s, (f i)^p) ^ (1/p) * (∑ i in s, (g i)^q) ^ (1/q) :=
begin
  by_cases H : (∑ i in s, (f i)^p) ^ (1/p) = 0 ∨ (∑ i in s, (g i)^q) ^ (1/q) = 0,
  { replace H : (∀ i ∈ s, f i = 0) ∨ (∀ i ∈ s, g i = 0),
      by simpa [ennreal.rpow_eq_zero_iff, hpq.pos, hpq.symm.pos, asymm hpq.pos, asymm hpq.symm.pos,
                sum_eq_zero_iff_of_nonneg] using H,
    have : ∀ i ∈ s, f i * g i = 0 := λ i hi, by cases H; simp [H i hi],
    have : (∑ i in s, f i * g i) = (∑ i in s, 0) := sum_congr rfl this,
    simp [this] },
  push_neg at H,
  by_cases H' : (∑ i in s, (f i)^p) ^ (1/p) = ⊤ ∨ (∑ i in s, (g i)^q) ^ (1/q) = ⊤,
  { cases H'; simp [H', -one_div, H] },
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ (∀ i ∈ s, g i ≠ ⊤),
    by simpa [ennreal.rpow_eq_top_iff, asymm hpq.pos, asymm hpq.symm.pos, hpq.pos, hpq.symm.pos,
              ennreal.sum_eq_top_iff, not_or_distrib] using H',
  have := ennreal.coe_le_coe.2 (@nnreal.inner_le_Lp_mul_Lq _ s (λ i, ennreal.to_nnreal (f i))
              (λ i, ennreal.to_nnreal (g i)) _ _ hpq),
  simp [← ennreal.coe_rpow_of_nonneg, le_of_lt (hpq.pos), le_of_lt (hpq.one_div_pos),
             le_of_lt (hpq.symm.pos), le_of_lt (hpq.symm.one_div_pos)] at this,
  convert this using 1;
  [skip, congr' 2];
  [skip, skip, simp, skip, simp];
  { apply finset.sum_congr rfl (λ i hi, _), simp [H'.1 i hi, H'.2 i hi, -with_zero.coe_mul,
    with_top.coe_mul.symm] },
end

/-- Minkowski inequality: the `L_p` seminorm of the sum of two vectors is less than or equal
to the sum of the `L_p`-seminorms of the summands. A version for `ℝ≥0∞` valued nonnegative
functions. -/
theorem Lp_add_le (hp : 1 ≤ p) :
  (∑ i in s, (f i + g i) ^ p)^(1/p) ≤ (∑ i in s, (f i)^p) ^ (1/p) + (∑ i in s, (g i)^p) ^ (1/p) :=
begin
  by_cases H' : (∑ i in s, (f i)^p) ^ (1/p) = ⊤ ∨ (∑ i in s, (g i)^p) ^ (1/p) = ⊤,
  { cases H'; simp [H', -one_div] },
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  replace H' : (∀ i ∈ s, f i ≠ ⊤) ∧ (∀ i ∈ s, g i ≠ ⊤),
    by simpa [ennreal.rpow_eq_top_iff, asymm pos, pos, ennreal.sum_eq_top_iff,
              not_or_distrib] using H',
  have := ennreal.coe_le_coe.2 (@nnreal.Lp_add_le _ s (λ i, ennreal.to_nnreal (f i))
              (λ i, ennreal.to_nnreal (g i)) _  hp),
  push_cast [← ennreal.coe_rpow_of_nonneg, le_of_lt (pos), le_of_lt (one_div_pos.2 pos)] at this,
  convert this using 2;
  [skip, congr' 1, congr' 1];
  { apply finset.sum_congr rfl (λ i hi, _), simp [H'.1 i hi, H'.2 i hi] }
end

end ennreal

end holder_minkowski
