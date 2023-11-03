/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.convolution
import analysis.special_functions.trigonometric.euler_sine_prod
import analysis.special_functions.gamma.bohr_mollerup
import analysis.analytic.isolated_zeros

/-!
# The Beta function, and further properties of the Gamma function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the Beta integral, relate Beta and Gamma functions, and prove some
refined properties of the Gamma function using these relations.

## Results on the Beta function

* `complex.beta_integral`: the Beta function `Β(u, v)`, where `u`, `v` are complex with positive
  real part.
* `complex.Gamma_mul_Gamma_eq_beta_integral`: the formula
  `Gamma u * Gamma v = Gamma (u + v) * beta_integral u v`.

## Results on the Gamma function

* `complex.Gamma_ne_zero`: for all `s : ℂ` with `s ∉ {-n : n ∈ ℕ}` we have `Γ s ≠ 0`.
* `complex.Gamma_seq_tendsto_Gamma`: for all `s`, the limit as `n → ∞` of the sequence
  `n ↦ n ^ s * n! / (s * (s + 1) * ... * (s + n))` is `Γ(s)`.
* `complex.Gamma_mul_Gamma_one_sub`: Euler's reflection formula
  `Gamma s * Gamma (1 - s) = π / sin π s`.
* `complex.differentiable_one_div_Gamma`: the function `1 / Γ(s)` is differentiable everywhere.
* `complex.Gamma_mul_Gamma_add_half`: Legendre's duplication formula
  `Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * sqrt π`.
* `real.Gamma_ne_zero`, `real.Gamma_seq_tendsto_Gamma`,
  `real.Gamma_mul_Gamma_one_sub`, `real.Gamma_mul_Gamma_add_half`: real versions of the above.
-/

noncomputable theory
open filter interval_integral set real measure_theory
open_locale nat topology big_operators real

section beta_integral

/-! ## The Beta function -/

namespace complex

notation `cexp` := complex.exp

/-- The Beta function `Β (u, v)`, defined as `∫_{0}^{1} x:ℝ, x ^ (u - 1) * (1 - x) ^ (v - 1)`. -/
noncomputable def beta_integral (u v : ℂ) : ℂ :=
∫_{0}^{1} x, x ^ (u - 1) * (1 - x) ^ (v - 1)

/-- Auxiliary lemma for `beta_integral_convergent`, showing convergence at the left endpoint. -/
lemma beta_integral_convergent_left {u : ℂ} (hu : 0 < re u) (v : ℂ) :
  interval_integrable (λ x, x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ → ℂ) volume 0 (1 / 2) :=
begin
  apply interval_integrable.mul_continuous_on,
  { refine interval_integral.interval_integrable_cpow' _,
    rwa [sub_re, one_re, ←zero_sub, sub_lt_sub_iff_right] },
  { apply continuous_at.continuous_on,
    intros x hx,
    rw uIcc_of_le (by positivity: (0:ℝ) ≤ 1/2) at hx,
    apply continuous_at.cpow,
    { exact (continuous_const.sub continuous_of_real).continuous_at },
    { exact continuous_at_const },
    { rw [sub_re, one_re, of_real_re, sub_pos],
      exact or.inl (hx.2.trans_lt (by norm_num : (1/2:ℝ) < 1)) } }
end

/-- The Beta integral is convergent for all `u, v` of positive real part. -/
lemma beta_integral_convergent {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
  interval_integrable (λ x, x ^ (u - 1) * (1 - x) ^ (v - 1) : ℝ → ℂ) volume 0 1 :=
begin
  refine (beta_integral_convergent_left hu v).trans _,
  rw interval_integrable.iff_comp_neg,
  convert ((beta_integral_convergent_left hv u).comp_add_right 1).symm,
  { ext1 x,
    conv_lhs { rw mul_comm },
    congr' 2;
    { push_cast, ring } },
  { norm_num },
  { norm_num }
end

lemma beta_integral_symm (u v : ℂ) :
  beta_integral v u = beta_integral u v :=
begin
  rw [beta_integral, beta_integral],
  have := interval_integral.integral_comp_mul_add
    (λ x:ℝ, (x:ℂ) ^ (u - 1) * (1 - ↑x) ^ (v - 1)) (neg_one_lt_zero.ne) 1,
  rw [inv_neg, inv_one, neg_one_smul, ←interval_integral.integral_symm] at this,
  convert this,
  { ext1 x, rw mul_comm, congr;
    { push_cast, ring } },
  { ring }, { ring }
end

lemma beta_integral_eval_one_right {u : ℂ} (hu : 0 < re u) :
  beta_integral u 1 = 1 / u :=
begin
  simp_rw [beta_integral, sub_self, cpow_zero, mul_one],
  rw integral_cpow (or.inl _),
  { rw [of_real_zero, of_real_one, one_cpow, zero_cpow,
    sub_zero, sub_add_cancel],
    rw sub_add_cancel,
    contrapose! hu, rw [hu, zero_re] },
  { rwa [sub_re, one_re, ←sub_pos, sub_neg_eq_add, sub_add_cancel] },
end

lemma beta_integral_scaled (s t : ℂ) {a : ℝ} (ha : 0 < a) :
  ∫_{0}^{a} x, (x:ℂ) ^ (s - 1) * (a - x) ^ (t - 1) = a ^ (s + t - 1) * beta_integral s t :=
begin
  have ha' : (a:ℂ) ≠ 0, from of_real_ne_zero.mpr ha.ne',
  rw beta_integral,
  have A : (a:ℂ) ^ (s + t - 1) = a * (a ^ (s - 1) * a ^ (t - 1)),
  { rw [(by abel : s + t - 1 = 1 + (s - 1) + (t - 1)),
      cpow_add _ _ ha', cpow_add 1 _ ha', cpow_one, mul_assoc] },
  rw [A, mul_assoc, ←interval_integral.integral_const_mul ((↑a) ^ _ * _),
    ←real_smul, ←(zero_div a), ←div_self ha.ne',
    ←interval_integral.integral_comp_div _ ha.ne', zero_div],
  simp_rw interval_integral.integral_of_le ha.le,
  refine set_integral_congr measurable_set_Ioc (λ x hx, _),
  dsimp only,
  rw mul_mul_mul_comm,
  congr' 1,
  { rw [←mul_cpow_of_real_nonneg ha.le (div_pos hx.1 ha).le, of_real_div, mul_div_cancel' _ ha'] },
  { rw [(by push_cast : (1:ℂ) - ↑(x / a) = ↑(1 - x / a)),
      ←mul_cpow_of_real_nonneg ha.le (sub_nonneg.mpr $ (div_le_one ha).mpr hx.2)],
    push_cast,
    rw [mul_sub, mul_one, mul_div_cancel' _ ha'] }
end

/-- Relation between Beta integral and Gamma function.  -/
lemma Gamma_mul_Gamma_eq_beta_integral {s t : ℂ} (hs : 0 < re s) (ht : 0 < re t) :
  Gamma s * Gamma t = Gamma (s + t) * beta_integral s t :=
begin
  -- Note that we haven't proved (yet) that the Gamma function has no zeroes, so we can't formulate
  -- this as a formula for the Beta function.
  have conv_int := integral_pos_convolution (Gamma_integral_convergent hs)
    (Gamma_integral_convergent ht) (continuous_linear_map.mul ℝ ℂ),
  simp_rw continuous_linear_map.mul_apply' at conv_int,
  have hst : 0 < re (s + t),
  { rw add_re, exact add_pos hs ht },
  rw [Gamma_eq_integral hs, Gamma_eq_integral ht, Gamma_eq_integral hst, Gamma_integral,
    Gamma_integral, Gamma_integral, ←conv_int, ←integral_mul_right (beta_integral _ _)],
  refine set_integral_congr measurable_set_Ioi (λ x hx, _),
  dsimp only,
  rw [mul_assoc, ←beta_integral_scaled s t hx, ←interval_integral.integral_const_mul],
  congr' 1 with y:1,
  push_cast,
  suffices : cexp (-x) = cexp (-y) * cexp (-(x - y)),
  { rw this, ring },
  { rw ←complex.exp_add, congr' 1, abel },
end

/-- Recurrence formula for the Beta function. -/
lemma beta_integral_recurrence {u v : ℂ} (hu : 0 < re u) (hv : 0 < re v) :
  u * beta_integral u (v + 1) = v * beta_integral (u + 1) v :=
begin
  -- NB: If we knew `Gamma (u + v + 1) ≠ 0` this would be an easy consequence of
  -- `Gamma_mul_Gamma_eq_beta_integral`; but we don't know that yet. We will prove it later, but
  -- this lemma is needed in the proof. So we give a (somewhat laborious) direct argument.
  let F : ℝ → ℂ := λ x, x ^ u * (1 - x) ^ v,
  have hu' : 0 < re (u + 1), by { rw [add_re, one_re], positivity },
  have hv' : 0 < re (v + 1), by { rw [add_re, one_re], positivity },
  have hc : continuous_on F (Icc 0 1),
  { refine (continuous_at.continuous_on (λ x hx, _)).mul (continuous_at.continuous_on (λ x hx, _)),
    { refine (continuous_at_cpow_const_of_re_pos (or.inl _) hu).comp
        continuous_of_real.continuous_at,
      rw of_real_re, exact hx.1 },
    { refine (continuous_at_cpow_const_of_re_pos (or.inl _) hv).comp
        (continuous_const.sub continuous_of_real).continuous_at,
      rw [sub_re, one_re, of_real_re, sub_nonneg],
      exact hx.2 } },
  have hder : ∀ (x : ℝ), x ∈ Ioo (0:ℝ) 1 → has_deriv_at F
    (u * (↑x ^ (u - 1) * (1 - ↑x) ^ v) - v * (↑x ^ u * (1 - ↑x) ^ (v - 1))) x,
  { intros x hx,
    have U : has_deriv_at (λ y:ℂ, y ^ u) (u * ↑x ^ (u - 1)) ↑x,
    { have := has_deriv_at.cpow_const (has_deriv_at_id ↑x) (or.inl _),
      { rw mul_one at this, exact this },
      { rw [id.def, of_real_re], exact hx.1 } },
    have V : has_deriv_at (λ y:ℂ, (1 - y) ^ v) (-v * (1 - ↑x) ^ (v - 1)) ↑x,
    { have A := has_deriv_at.cpow_const (has_deriv_at_id (1 - ↑x)) (or.inl _),
      rotate, { exact v },
      { rw [id.def, sub_re, one_re, of_real_re, sub_pos], exact hx.2 },
      simp_rw [id.def] at A,
      have B : has_deriv_at (λ y:ℂ, 1 - y) (-1) ↑x,
      { apply has_deriv_at.const_sub, apply has_deriv_at_id },
      convert has_deriv_at.comp ↑x A B using 1,
      ring },
    convert (U.mul V).comp_of_real,
    ring },
  have h_int := ((beta_integral_convergent hu hv').const_mul u).sub
    ((beta_integral_convergent hu' hv).const_mul v),
  dsimp only at h_int,
  rw [add_sub_cancel, add_sub_cancel] at h_int,
  have int_ev := interval_integral.integral_eq_sub_of_has_deriv_at_of_le zero_le_one hc hder h_int,
  have hF0 : F 0 = 0,
  { simp only [mul_eq_zero, of_real_zero, cpow_eq_zero_iff, eq_self_iff_true,
      ne.def, true_and, sub_zero, one_cpow, one_ne_zero, or_false],
    contrapose! hu, rw [hu, zero_re] },
  have hF1 : F 1 = 0,
  { simp only [mul_eq_zero, of_real_one, one_cpow, one_ne_zero, sub_self,
      cpow_eq_zero_iff, eq_self_iff_true, ne.def, true_and, false_or],
    contrapose! hv, rw [hv, zero_re] },
  rw [hF0, hF1, sub_zero, interval_integral.integral_sub,
    interval_integral.integral_const_mul, interval_integral.integral_const_mul] at int_ev,
  { rw [beta_integral, beta_integral, ←sub_eq_zero],
    convert int_ev;
    { ext1 x, congr, abel } },
  { apply interval_integrable.const_mul,
    convert beta_integral_convergent hu hv',
    ext1 x, rw add_sub_cancel },
  { apply interval_integrable.const_mul,
    convert beta_integral_convergent hu' hv,
    ext1 x, rw add_sub_cancel },
end

/-- Explicit formula for the Beta function when second argument is a positive integer. -/
lemma beta_integral_eval_nat_add_one_right {u : ℂ} (hu : 0 < re u) (n : ℕ) :
  beta_integral u (n + 1) = n! / ∏ (j:ℕ) in finset.range (n + 1), (u + j) :=
begin
  induction n with n IH generalizing u,
  { rw [nat.cast_zero, zero_add, beta_integral_eval_one_right hu,
      nat.factorial_zero, nat.cast_one, zero_add, finset.prod_range_one, nat.cast_zero, add_zero] },
  { have := beta_integral_recurrence hu (_ : 0 < re n.succ),
    swap, { rw [←of_real_nat_cast, of_real_re], positivity },
    rw [mul_comm u _, ←eq_div_iff] at this,
    swap, { contrapose! hu, rw [hu, zero_re] },
    rw [this, finset.prod_range_succ', nat.cast_succ, IH],
    swap, { rw [add_re, one_re], positivity },
    rw [nat.factorial_succ, nat.cast_mul, nat.cast_add, nat.cast_one, nat.cast_zero, add_zero,
      ←mul_div_assoc, ←div_div],
    congr' 3 with j:1,
    push_cast, abel }
end

end complex

end beta_integral

section limit_formula

/-! ## The Euler limit formula -/

namespace complex

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for complex `s`.
We will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def Gamma_seq (s : ℂ) (n : ℕ) :=
(n:ℂ) ^ s * n! / ∏ (j:ℕ) in finset.range (n + 1), (s + j)

lemma Gamma_seq_eq_beta_integral_of_re_pos {s : ℂ} (hs : 0 < re s) (n : ℕ) :
  Gamma_seq s n = n ^ s * beta_integral s (n + 1) :=
by rw [Gamma_seq, beta_integral_eval_nat_add_one_right hs n, ←mul_div_assoc]

lemma Gamma_seq_add_one_left (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
  (Gamma_seq (s + 1) n) / s = n / (n + 1 + s) * Gamma_seq s n :=
begin
  conv_lhs { rw [Gamma_seq, finset.prod_range_succ, div_div] },
  conv_rhs { rw [Gamma_seq, finset.prod_range_succ', nat.cast_zero, add_zero, div_mul_div_comm,
    ←mul_assoc, ←mul_assoc, mul_comm _ (finset.prod _ _)] },
  congr' 3,
  { rw [cpow_add _ _ (nat.cast_ne_zero.mpr hn), cpow_one, mul_comm] },
  { refine finset.prod_congr (by refl) (λ x hx, _),
    push_cast, ring },
  { abel }
end

lemma Gamma_seq_eq_approx_Gamma_integral {s : ℂ} (hs : 0 < re s) {n : ℕ} (hn : n ≠ 0) :
  Gamma_seq s n = ∫_{0}^{n} x:ℝ, ↑((1 - x / n) ^ n) * (x:ℂ) ^ (s - 1) :=
begin
  have : ∀ (x : ℝ), x = x / n * n, by { intro x, rw div_mul_cancel, exact nat.cast_ne_zero.mpr hn },
  conv in (↑_ ^ _) { congr, rw this x },
  rw Gamma_seq_eq_beta_integral_of_re_pos hs,
  rw [beta_integral, @interval_integral.integral_comp_div _ _ _ _ 0 n _
    (λ x, ↑((1 - x) ^ n) * ↑(x * ↑n) ^ (s - 1) : ℝ → ℂ) (nat.cast_ne_zero.mpr hn),
    real_smul, zero_div, div_self, add_sub_cancel, ←interval_integral.integral_const_mul,
    ←interval_integral.integral_const_mul],
  swap, { exact nat.cast_ne_zero.mpr hn },
  simp_rw interval_integral.integral_of_le zero_le_one,
  refine set_integral_congr measurable_set_Ioc (λ x hx, _),
  push_cast,
  have hn' : (n : ℂ) ≠ 0, from nat.cast_ne_zero.mpr hn,
  have A : (n : ℂ) ^ s = (n : ℂ) ^ (s - 1)  * n,
  { conv_lhs { rw [(by ring : s = (s - 1) + 1), cpow_add _ _ hn'] },
    simp },
  have B : ((x : ℂ) * ↑n) ^ (s - 1) = (x : ℂ) ^ (s - 1) * ↑n ^ (s - 1),
  { rw [←of_real_nat_cast,
      mul_cpow_of_real_nonneg hx.1.le (nat.cast_pos.mpr (nat.pos_of_ne_zero hn)).le] },
  rw [A, B, cpow_nat_cast], ring,
end

/-- The main techical lemma for `Gamma_seq_tendsto_Gamma`, expressing the integral defining the
Gamma function for `0 < re s` as the limit of a sequence of integrals over finite intervals. -/
lemma approx_Gamma_integral_tendsto_Gamma_integral {s : ℂ} (hs : 0 < re s) :
  tendsto (λ n:ℕ, ∫_{0}^{n} x:ℝ, ↑((1 - x / n) ^ n) * (x:ℂ) ^ (s - 1)) at_top (𝓝 $ Gamma s) :=
begin
  rw [Gamma_eq_integral hs],
  -- We apply dominated convergence to the following function, which we will show is uniformly
  -- bounded above by the Gamma integrand `exp (-x) * x ^ (re s - 1)`.
  let f : ℕ → ℝ → ℂ := λ n, indicator (Ioc 0 (n:ℝ))
    (λ x:ℝ, ↑((1 - x / n) ^ n) * (x:ℂ) ^ (s - 1)),
  -- integrability of f
  have f_ible : ∀ (n:ℕ), integrable (f n) (volume.restrict (Ioi 0)),
  { intro n,
    rw [integrable_indicator_iff (measurable_set_Ioc : measurable_set (Ioc (_:ℝ) _)),
      integrable_on, measure.restrict_restrict_of_subset Ioc_subset_Ioi_self, ←integrable_on,
      ←interval_integrable_iff_integrable_Ioc_of_le (by positivity : (0:ℝ) ≤ n)],
    apply interval_integrable.continuous_on_mul,
    { refine interval_integral.interval_integrable_cpow' _,
      rwa [sub_re, one_re, ←zero_sub, sub_lt_sub_iff_right] },
    { apply continuous.continuous_on, continuity } },
  -- pointwise limit of f
  have f_tends : ∀ x:ℝ, x ∈ Ioi (0:ℝ) →
    tendsto (λ n:ℕ, f n x) at_top (𝓝 $ ↑(real.exp (-x)) * (x:ℂ) ^ (s - 1)),
  { intros x hx,
    apply tendsto.congr',
    show ∀ᶠ n:ℕ in at_top, ↑((1 - x / n) ^ n) * (x:ℂ) ^ (s - 1) = f n x,
    { refine eventually.mp (eventually_ge_at_top ⌈x⌉₊) (eventually_of_forall (λ n hn, _)),
      rw nat.ceil_le at hn,
      dsimp only [f],
      rw indicator_of_mem,
      exact ⟨hx, hn⟩ },
    { simp_rw mul_comm _ (↑x ^ _),
      refine (tendsto.comp (continuous_of_real.tendsto _) _).const_mul _,
      convert tendsto_one_plus_div_pow_exp (-x),
      ext1 n,
      rw [neg_div, ←sub_eq_add_neg] } },
  -- let `convert` identify the remaining goals
  convert tendsto_integral_of_dominated_convergence _ (λ n, (f_ible n).1)
    (real.Gamma_integral_convergent hs) _
    ((ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ f_tends)),
  -- limit of f is the integrand we want
  { ext1 n,
    rw [integral_indicator (measurable_set_Ioc : measurable_set (Ioc (_:ℝ) _)),
      interval_integral.integral_of_le (by positivity: 0 ≤ (n:ℝ)),
      measure.restrict_restrict_of_subset Ioc_subset_Ioi_self] },
  -- f is uniformly bounded by the Gamma integrand
  { intro n,
    refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    dsimp only [f],
    rcases lt_or_le (n:ℝ) x with hxn | hxn,
    { rw [indicator_of_not_mem (not_mem_Ioc_of_gt hxn), norm_zero,
        mul_nonneg_iff_right_nonneg_of_pos (exp_pos _)],
      exact rpow_nonneg_of_nonneg (le_of_lt hx) _ },
    { rw [indicator_of_mem (mem_Ioc.mpr ⟨hx, hxn⟩), norm_mul, complex.norm_eq_abs,
        complex.abs_of_nonneg
          (pow_nonneg (sub_nonneg.mpr $ div_le_one_of_le hxn $ by positivity) _),
        complex.norm_eq_abs, abs_cpow_eq_rpow_re_of_pos hx, sub_re, one_re,
        mul_le_mul_right (rpow_pos_of_pos hx _ )],
      exact one_sub_div_pow_le_exp_neg hxn } }
end

/-- Euler's limit formula for the complex Gamma function. -/
lemma Gamma_seq_tendsto_Gamma (s : ℂ) :
  tendsto (Gamma_seq s) at_top (𝓝 $ Gamma s) :=
begin
  suffices : ∀ m : ℕ, (-↑m < re s) → tendsto (Gamma_seq s) at_top (𝓝 $ Gamma_aux m s),
  { rw Gamma,
    apply this,
    rw neg_lt,
    rcases lt_or_le 0 (re s) with hs | hs,
    { exact (neg_neg_of_pos hs).trans_le (nat.cast_nonneg _), },
    { refine (nat.lt_floor_add_one _).trans_le _,
      rw [sub_eq_neg_add, nat.floor_add_one (neg_nonneg.mpr hs), nat.cast_add_one] } },
  intro m,
  induction m with m IH generalizing s,
  { -- Base case: `0 < re s`, so Gamma is given by the integral formula
    intro hs,
    rw [nat.cast_zero, neg_zero] at hs,
    rw [←Gamma_eq_Gamma_aux],
    { refine tendsto.congr' _ (approx_Gamma_integral_tendsto_Gamma_integral hs),
      refine (eventually_ne_at_top 0).mp (eventually_of_forall (λ n hn, _)),
      exact (Gamma_seq_eq_approx_Gamma_integral hs hn).symm },
    { rwa [nat.cast_zero, neg_lt_zero] } },
  { -- Induction step: use recurrence formulae in `s` for Gamma and Gamma_seq
    intro hs,
    rw [nat.cast_succ, neg_add, ←sub_eq_add_neg, sub_lt_iff_lt_add, ←one_re, ←add_re] at hs,
    rw Gamma_aux,
    have := tendsto.congr' ((eventually_ne_at_top 0).mp (eventually_of_forall (λ n hn, _)))
      ((IH _ hs).div_const s),
    swap 3, { exact Gamma_seq_add_one_left s hn }, -- doesn't work if inlined?
    conv at this in (_ / _ * _) { rw mul_comm },
    rwa [←mul_one (Gamma_aux m (s + 1) / s), tendsto_mul_iff_of_ne_zero _ (one_ne_zero' ℂ)] at this,
    simp_rw add_assoc,
    exact tendsto_coe_nat_div_add_at_top (1 + s) }
end

end complex

end limit_formula

section gamma_reflection
/-! ## The reflection formula -/

namespace complex

lemma Gamma_seq_mul (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
  Gamma_seq z n * Gamma_seq (1 - z) n =
  n / (n + 1 - z) * (1 / (z * ∏ j in finset.range n, (1 - z ^ 2 / (j + 1) ^ 2))) :=
begin
  -- also true for n = 0 but we don't need it
  have aux : ∀ (a b c d : ℂ), a * b * (c * d) = a * c * (b * d), by { intros, ring },
  rw [Gamma_seq, Gamma_seq, div_mul_div_comm, aux, ←pow_two],
  have : (n : ℂ) ^ z * n ^ (1 - z) = n,
  { rw [←cpow_add _ _ (nat.cast_ne_zero.mpr hn), add_sub_cancel'_right, cpow_one] },
  rw [this, finset.prod_range_succ', finset.prod_range_succ, aux, ←finset.prod_mul_distrib,
    nat.cast_zero, add_zero, add_comm (1 - z) n, ←add_sub_assoc],
  have : ∀ (j : ℕ), (z + ↑(j + 1)) * (1 - z + ↑j) = ↑((j + 1) ^ 2) * (1 - z ^ 2 / (↑j + 1) ^ 2),
  { intro j,
    push_cast,
    have : (j:ℂ) + 1 ≠ 0, by { rw [←nat.cast_succ, nat.cast_ne_zero], exact nat.succ_ne_zero j },
    field_simp, ring },
  simp_rw this,
  rw [finset.prod_mul_distrib, ←nat.cast_prod, finset.prod_pow,
    finset.prod_range_add_one_eq_factorial, nat.cast_pow,
    (by {intros, ring} : ∀ (a b c d : ℂ), a * b * (c * d) = a * (d * (b * c))),
    ←div_div, mul_div_cancel, ←div_div, mul_comm z _, mul_one_div],
  exact pow_ne_zero 2 (nat.cast_ne_zero.mpr $ nat.factorial_ne_zero n),
end

/-- Euler's reflection formula for the complex Gamma function. -/
theorem Gamma_mul_Gamma_one_sub (z : ℂ) : Gamma z * Gamma (1 - z) = π / sin (π * z) :=
begin
  have pi_ne : (π : ℂ) ≠ 0, from complex.of_real_ne_zero.mpr pi_ne_zero,
  by_cases hs : sin (↑π * z) = 0,
  { -- first deal with silly case z = integer
    rw [hs, div_zero],
    rw [←neg_eq_zero, ←complex.sin_neg, ←mul_neg, complex.sin_eq_zero_iff, mul_comm] at hs,
    obtain ⟨k, hk⟩ := hs,
    rw [mul_eq_mul_right_iff, eq_false_intro (of_real_ne_zero.mpr pi_pos.ne'), or_false,
      neg_eq_iff_eq_neg] at hk,
    rw hk,
    cases k,
    { rw [int.cast_of_nat, complex.Gamma_neg_nat_eq_zero, zero_mul] },
    { rw [int.cast_neg_succ_of_nat, neg_neg, nat.cast_add, nat.cast_one, add_comm, sub_add_cancel',
        complex.Gamma_neg_nat_eq_zero, mul_zero] } },
  refine tendsto_nhds_unique ((Gamma_seq_tendsto_Gamma z).mul (Gamma_seq_tendsto_Gamma $ 1 - z)) _,
  have : ↑π / sin (↑π * z) = 1 * (π / sin (π * z)), by rw one_mul, rw this,
  refine tendsto.congr' ((eventually_ne_at_top 0).mp
    (eventually_of_forall (λ n hn, (Gamma_seq_mul z hn).symm))) (tendsto.mul _ _),
  { convert tendsto_coe_nat_div_add_at_top (1 - z), ext1 n, rw add_sub_assoc },
  { have : ↑π / sin (↑π * z) = 1 / (sin (π * z) / π), by field_simp, rw this,
    refine tendsto_const_nhds.div _ (div_ne_zero hs pi_ne),
    rw [←tendsto_mul_iff_of_ne_zero tendsto_const_nhds pi_ne, div_mul_cancel _ pi_ne],
    convert tendsto_euler_sin_prod z,
    ext1 n, rw [mul_comm, ←mul_assoc] },
end

/-- The Gamma function does not vanish on `ℂ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
theorem Gamma_ne_zero {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 :=
begin
  by_cases h_im : s.im = 0,
  { have : s = ↑s.re,
    { conv_lhs { rw ←complex.re_add_im s }, rw [h_im, of_real_zero, zero_mul, add_zero] },
    rw [this, Gamma_of_real, of_real_ne_zero],
    refine real.Gamma_ne_zero (λ n, _),
    specialize hs n,
    contrapose! hs,
    rwa [this, ←of_real_nat_cast, ←of_real_neg, of_real_inj] },
  { have : sin (↑π * s) ≠ 0,
    { rw complex.sin_ne_zero_iff,
      intro k,
      apply_fun im,
      rw [of_real_mul_im, ←of_real_int_cast, ←of_real_mul, of_real_im],
      exact mul_ne_zero real.pi_pos.ne' h_im },
    have A := div_ne_zero (of_real_ne_zero.mpr real.pi_pos.ne') this,
    rw [←complex.Gamma_mul_Gamma_one_sub s, mul_ne_zero_iff] at A,
    exact A.1 }
end

lemma Gamma_eq_zero_iff (s : ℂ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
begin
  split,
  { contrapose!, exact Gamma_ne_zero },
  { rintro ⟨m, rfl⟩, exact Gamma_neg_nat_eq_zero m },
end

/-- A weaker, but easier-to-apply, version of `complex.Gamma_ne_zero`. -/
lemma Gamma_ne_zero_of_re_pos {s : ℂ} (hs : 0 < re s) : Gamma s ≠ 0 :=
begin
  refine Gamma_ne_zero (λ m, _),
  contrapose! hs,
  simpa only [hs, neg_re, ←of_real_nat_cast, of_real_re, neg_nonpos] using nat.cast_nonneg _,
end

end complex

namespace real

/-- The sequence with `n`-th term `n ^ s * n! / (s * (s + 1) * ... * (s + n))`, for real `s`. We
will show that this tends to `Γ(s)` as `n → ∞`. -/
noncomputable def Gamma_seq (s : ℝ) (n : ℕ) :=
(n : ℝ) ^ s * n! / ∏ (j : ℕ) in finset.range (n + 1), (s + j)

/-- Euler's limit formula for the real Gamma function. -/
lemma Gamma_seq_tendsto_Gamma (s : ℝ) : tendsto (Gamma_seq s) at_top (𝓝 $ Gamma s) :=
begin
  suffices : tendsto (coe ∘ Gamma_seq s : ℕ → ℂ) at_top (𝓝 $ complex.Gamma s),
    from (complex.continuous_re.tendsto (complex.Gamma ↑s)).comp this,
  convert complex.Gamma_seq_tendsto_Gamma s,
  ext1 n,
  dsimp only [Gamma_seq, function.comp_app, complex.Gamma_seq],
  push_cast,
  rw [complex.of_real_cpow n.cast_nonneg, complex.of_real_nat_cast]
end

/-- Euler's reflection formula for the real Gamma function. -/
lemma Gamma_mul_Gamma_one_sub (s : ℝ) : Gamma s * Gamma (1 - s) = π / sin (π * s) :=
begin
  simp_rw [←complex.of_real_inj, complex.of_real_div, complex.of_real_sin,
    complex.of_real_mul, ←complex.Gamma_of_real, complex.of_real_sub, complex.of_real_one],
  exact complex.Gamma_mul_Gamma_one_sub s
end

end real

end gamma_reflection

section inv_gamma
open_locale real

namespace complex
/-! ## The reciprocal Gamma function

We show that the reciprocal Gamma function `1 / Γ(s)` is entire. These lemmas show that (in this
case at least) mathlib's conventions for division by zero do actually give a mathematically useful
answer! (These results are useful in the theory of zeta and L-functions.) -/

/-- A reformulation of the Gamma recurrence relation which is true for `s = 0` as well. -/
lemma one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s : ℂ) :
  (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹ :=
begin
  rcases ne_or_eq s 0 with h | rfl,
  { rw [Gamma_add_one s h, mul_inv, mul_inv_cancel_left₀ h] },
  { rw [zero_add, Gamma_zero, inv_zero, zero_mul] }
end

/-- The reciprocal of the Gamma function is differentiable everywhere (including the points where
Gamma itself is not). -/
lemma differentiable_one_div_Gamma : differentiable ℂ (λ s : ℂ, (Gamma s)⁻¹) :=
begin
  suffices : ∀ (n : ℕ), ∀ (s : ℂ) (hs : -s.re < n), differentiable_at ℂ (λ u : ℂ, (Gamma u)⁻¹) s,
    from λ s, let ⟨n, h⟩ := exists_nat_gt (-s.re) in this n s h,
  intro n,
  induction n with m hm,
  { intros s hs,
    rw [nat.cast_zero, neg_lt_zero] at hs,
    suffices : ∀ (m : ℕ), s ≠ -↑m, from (differentiable_at_Gamma _ this).inv (Gamma_ne_zero this),
    contrapose! hs,
    rcases hs with ⟨m, rfl⟩,
    simpa only [neg_re, ←of_real_nat_cast, of_real_re, neg_nonpos] using nat.cast_nonneg m },
  { intros s hs,
    rw funext one_div_Gamma_eq_self_mul_one_div_Gamma_add_one,
    specialize hm (s + 1) (by rwa [add_re, one_re, neg_add', sub_lt_iff_lt_add, ←nat.cast_succ]),
    refine differentiable_at_id.mul (hm.comp s _),
    exact differentiable_at_id.add (differentiable_at_const _) }
end

end complex

end inv_gamma

section doubling
/-!
## The doubling formula for Gamma

We prove the doubling formula for arbitrary real or complex arguments, by analytic continuation from
the positive real case. (Knowing that `Γ⁻¹` is analytic everywhere makes this much simpler, since we
do not have to do any special-case handling for the poles of `Γ`.)
-/

namespace complex

theorem Gamma_mul_Gamma_add_half (s : ℂ) :
  Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * ↑(real.sqrt π) :=
begin
  suffices : (λ z, (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) =
    (λ z, (Gamma (2 * z))⁻¹  * 2 ^ (2 * z - 1) / ↑(real.sqrt π)),
  { convert congr_arg has_inv.inv (congr_fun this s) using 1,
    { rw [mul_inv, inv_inv, inv_inv] },
    { rw [div_eq_mul_inv, mul_inv, mul_inv, inv_inv, inv_inv, ←cpow_neg, neg_sub] } },
  have h1 : analytic_on ℂ (λ z : ℂ, (Gamma z)⁻¹ * (Gamma (z + 1 / 2))⁻¹) univ,
  { refine differentiable_on.analytic_on _ is_open_univ,
    refine (differentiable_one_div_Gamma.mul _).differentiable_on,
    exact differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _)) },
  have h2 : analytic_on ℂ (λ z, (Gamma (2 * z))⁻¹  * 2 ^ (2 * z - 1) / ↑(real.sqrt π)) univ,
  { refine differentiable_on.analytic_on _ is_open_univ,
    refine (differentiable.mul _ (differentiable_const _)).differentiable_on,
    apply differentiable.mul,
    { exact differentiable_one_div_Gamma.comp (differentiable_id'.const_mul _) },
    { refine λ t, differentiable_at.const_cpow _ (or.inl two_ne_zero),
      refine differentiable_at.sub_const (differentiable_at_id.const_mul _) _ } },
  have h3 : tendsto (coe : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1),
  { rw tendsto_nhds_within_iff, split,
    { exact tendsto_nhds_within_of_tendsto_nhds continuous_of_real.continuous_at },
    { exact eventually_nhds_within_iff.mpr (eventually_of_forall $ λ t ht, of_real_ne_one.mpr ht)}},
  refine analytic_on.eq_of_frequently_eq h1 h2 (h3.frequently _),
  refine ((eventually.filter_mono nhds_within_le_nhds) _).frequently,
  refine (eventually_gt_nhds zero_lt_one).mp (eventually_of_forall $ λ t ht, _),
  rw [←mul_inv, Gamma_of_real, (by push_cast : (t : ℂ) + 1 / 2 = ↑(t + 1 / 2)), Gamma_of_real,
    ←of_real_mul, Gamma_mul_Gamma_add_half_of_pos ht, of_real_mul, of_real_mul, ←Gamma_of_real,
    mul_inv, mul_inv, (by push_cast : 2 * (t : ℂ) = ↑(2 * t)), Gamma_of_real,
    of_real_cpow zero_le_two, of_real_bit0, of_real_one, ←cpow_neg, of_real_sub, of_real_one,
    neg_sub, ←div_eq_mul_inv]
end

end complex

namespace real
open complex

lemma Gamma_mul_Gamma_add_half (s : ℝ) :
  Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * sqrt π :=
begin
  rw [←of_real_inj],
  simpa only [←Gamma_of_real, of_real_cpow zero_le_two, of_real_mul, of_real_add, of_real_div,
    of_real_bit0, of_real_one, of_real_sub] using complex.Gamma_mul_Gamma_add_half ↑s
end

end real

end doubling
