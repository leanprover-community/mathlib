/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import measure_theory.integral.exp_decay
import analysis.special_functions.improper_integrals
import analysis.mellin_transform

/-!
# The Gamma function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `Γ` function (of a real or complex variable `s`). We define this by Euler's
integral `Γ(s) = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)` in the range where this integral converges
(i.e., for `0 < s` in the real case, and `0 < re s` in the complex case).

We show that this integral satisfies `Γ(1) = 1` and `Γ(s + 1) = s * Γ(s)`; hence we can define
`Γ(s)` for all `s` as the unique function satisfying this recurrence and agreeing with Euler's
integral in the convergence range. (If `s = -n` for `n ∈ ℕ`, then the function is undefined, and we
set it to be `0` by convention.)

## Gamma function: main statements (complex case)

* `complex.Gamma`: the `Γ` function (of a complex variable).
* `complex.Gamma_eq_integral`: for `0 < re s`, `Γ(s)` agrees with Euler's integral.
* `complex.Gamma_add_one`: for all `s : ℂ` with `s ≠ 0`, we have `Γ (s + 1) = s Γ(s)`.
* `complex.Gamma_nat_eq_factorial`: for all `n : ℕ` we have `Γ (n + 1) = n!`.
* `complex.differentiable_at_Gamma`: `Γ` is complex-differentiable at all `s : ℂ` with
  `s ∉ {-n : n ∈ ℕ}`.

## Gamma function: main statements (real case)

* `real.Gamma`: the `Γ` function (of a real variable).
* Real counterparts of all the properties of the complex Gamma function listed above:
  `real.Gamma_eq_integral`, `real.Gamma_add_one`, `real.Gamma_nat_eq_factorial`,
  `real.differentiable_at_Gamma`.

## Tags

Gamma
-/

noncomputable theory
open filter interval_integral set real measure_theory asymptotics
open_locale nat topology complex_conjugate

namespace real

/-- Asymptotic bound for the `Γ` function integrand. -/
lemma Gamma_integrand_is_o (s : ℝ) :
  (λ x:ℝ, exp (-x) * x ^ s) =o[at_top] (λ x:ℝ, exp (-(1/2) * x)) :=
begin
  refine is_o_of_tendsto (λ x hx, _) _,
  { exfalso, exact (exp_pos (-(1 / 2) * x)).ne' hx },
  have : (λ (x:ℝ), exp (-x) * x ^ s / exp (-(1 / 2) * x)) = (λ (x:ℝ), exp ((1 / 2) * x) / x ^ s )⁻¹,
  { ext1 x,
    field_simp [exp_ne_zero, exp_neg, ← real.exp_add],
    left,
    ring },
  rw this,
  exact (tendsto_exp_mul_div_rpow_at_top s (1 / 2) one_half_pos).inv_tendsto_at_top,
end

/-- The Euler integral for the `Γ` function converges for positive real `s`. -/
lemma Gamma_integral_convergent {s : ℝ} (h : 0 < s) :
  integrable_on (λ x:ℝ, exp (-x) * x ^ (s - 1)) (Ioi 0) :=
begin
  rw [←Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrable_on_union],
  split,
  { rw ←integrable_on_Icc_iff_integrable_on_Ioc,
    refine integrable_on.continuous_on_mul continuous_on_id.neg.exp _ is_compact_Icc,
    refine (interval_integrable_iff_integrable_Icc_of_le zero_le_one).mp _,
    exact interval_integrable_rpow' (by linarith), },
  { refine integrable_of_is_O_exp_neg one_half_pos _ (Gamma_integrand_is_o _ ).is_O,
    refine continuous_on_id.neg.exp.mul (continuous_on_id.rpow_const _),
    intros x hx,
    exact or.inl ((zero_lt_one : (0 : ℝ) < 1).trans_le hx).ne' }
end

end real

namespace complex
/- Technical note: In defining the Gamma integrand exp (-x) * x ^ (s - 1) for s complex, we have to
make a choice between ↑(real.exp (-x)), complex.exp (↑(-x)), and complex.exp (-↑x), all of which are
equal but not definitionally so. We use the first of these throughout. -/


/-- The integral defining the `Γ` function converges for complex `s` with `0 < re s`.

This is proved by reduction to the real case. -/
lemma Gamma_integral_convergent {s : ℂ} (hs : 0 < s.re) :
  integrable_on (λ x, (-x).exp * x ^ (s - 1) : ℝ → ℂ) (Ioi 0) :=
begin
  split,
  { refine continuous_on.ae_strongly_measurable _ measurable_set_Ioi,
    apply (continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on,
    intros x hx,
    have : continuous_at (λ x:ℂ, x ^ (s - 1)) ↑x,
    { apply continuous_at_cpow_const, rw of_real_re, exact or.inl hx, },
    exact continuous_at.comp this continuous_of_real.continuous_at },
  { rw ←has_finite_integral_norm_iff,
    refine has_finite_integral.congr (real.Gamma_integral_convergent hs).2 _,
    refine (ae_restrict_iff' measurable_set_Ioi).mpr (ae_of_all _ (λ x hx, _)),
    dsimp only,
    rw [norm_eq_abs, map_mul, abs_of_nonneg $ le_of_lt $ exp_pos $ -x,
      abs_cpow_eq_rpow_re_of_pos hx _],
    simp }
end

/-- Euler's integral for the `Γ` function (of a complex variable `s`), defined as
`∫ x in Ioi 0, exp (-x) * x ^ (s - 1)`.

See `complex.Gamma_integral_convergent` for a proof of the convergence of the integral for
`0 < re s`. -/
def Gamma_integral (s : ℂ) : ℂ := ∫ x in Ioi (0:ℝ), ↑(-x).exp * ↑x ^ (s - 1)

lemma Gamma_integral_conj (s : ℂ) : Gamma_integral (conj s) = conj (Gamma_integral s) :=
begin
  rw [Gamma_integral, Gamma_integral, ←integral_conj],
  refine set_integral_congr measurable_set_Ioi (λ x hx, _),
  dsimp only,
  rw [ring_hom.map_mul, conj_of_real, cpow_def_of_ne_zero (of_real_ne_zero.mpr (ne_of_gt hx)),
    cpow_def_of_ne_zero (of_real_ne_zero.mpr (ne_of_gt hx)), ←exp_conj, ring_hom.map_mul,
    ←of_real_log (le_of_lt hx), conj_of_real, ring_hom.map_sub, ring_hom.map_one],
end

lemma Gamma_integral_of_real (s : ℝ) :
  Gamma_integral ↑s = ↑(∫ x:ℝ in Ioi 0, real.exp (-x) * x ^ (s - 1)) :=
begin
  rw [Gamma_integral, ←_root_.integral_of_real],
  refine set_integral_congr measurable_set_Ioi _,
  intros x hx, dsimp only,
  rw [of_real_mul, of_real_cpow (mem_Ioi.mp hx).le],
  simp,
end

lemma Gamma_integral_one : Gamma_integral 1 = 1 :=
by simpa only [←of_real_one, Gamma_integral_of_real, of_real_inj, sub_self,
  rpow_zero, mul_one] using integral_exp_neg_Ioi_zero

end complex

/-! Now we establish the recurrence relation `Γ(s + 1) = s * Γ(s)` using integration by parts. -/

namespace complex

section Gamma_recurrence

/-- The indefinite version of the `Γ` function, `Γ(s, X) = ∫ x ∈ 0..X, exp(-x) x ^ (s - 1)`. -/
def partial_Gamma (s : ℂ) (X : ℝ) : ℂ := ∫_{0}^{X} x, (-x).exp * x ^ (s - 1)

lemma tendsto_partial_Gamma {s : ℂ} (hs: 0 < s.re) :
  tendsto (λ X:ℝ, partial_Gamma s X) at_top (𝓝 $ Gamma_integral s) :=
interval_integral_tendsto_integral_Ioi 0 (Gamma_integral_convergent hs) tendsto_id

private lemma Gamma_integrand_interval_integrable (s : ℂ) {X : ℝ} (hs : 0 < s.re) (hX : 0 ≤ X):
  interval_integrable (λ x, (-x).exp * x ^ (s - 1) : ℝ → ℂ) volume 0 X :=
begin
  rw interval_integrable_iff_integrable_Ioc_of_le hX,
  exact integrable_on.mono_set (Gamma_integral_convergent hs) Ioc_subset_Ioi_self
end

private lemma Gamma_integrand_deriv_integrable_A {s : ℂ} (hs : 0 < s.re) {X : ℝ} (hX : 0 ≤ X):
 interval_integrable (λ x, -((-x).exp * x ^ s) : ℝ → ℂ) volume 0 X :=
begin
  convert (Gamma_integrand_interval_integrable (s+1) _ hX).neg,
  { ext1, simp only [add_sub_cancel, pi.neg_apply] },
  { simp only [add_re, one_re], linarith,},
end

private lemma Gamma_integrand_deriv_integrable_B {s : ℂ} (hs : 0 < s.re) {Y : ℝ} (hY : 0 ≤ Y) :
  interval_integrable (λ (x : ℝ), (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) volume 0 Y :=
begin
  have : (λ x, (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) =
    (λ x, s * ((-x).exp * x ^ (s - 1)) : ℝ → ℂ),
  { ext1, ring, },
  rw [this, interval_integrable_iff_integrable_Ioc_of_le hY],
  split,
  { refine (continuous_on_const.mul _).ae_strongly_measurable measurable_set_Ioc,
    apply (continuous_of_real.comp continuous_neg.exp).continuous_on.mul,
    apply continuous_at.continuous_on,
    intros x hx,
    refine (_ : continuous_at (λ x:ℂ, x ^ (s - 1)) _).comp continuous_of_real.continuous_at,
    apply continuous_at_cpow_const, rw of_real_re, exact or.inl hx.1, },
  rw ←has_finite_integral_norm_iff,
  simp_rw [norm_eq_abs, map_mul],
  refine (((real.Gamma_integral_convergent hs).mono_set
    Ioc_subset_Ioi_self).has_finite_integral.congr _).const_mul _,
  rw [eventually_eq, ae_restrict_iff'],
  { apply ae_of_all, intros x hx,
    rw [abs_of_nonneg (exp_pos _).le,abs_cpow_eq_rpow_re_of_pos hx.1],
    simp },
  { exact measurable_set_Ioc},
end

/-- The recurrence relation for the indefinite version of the `Γ` function. -/
lemma partial_Gamma_add_one {s : ℂ} (hs: 0 < s.re) {X : ℝ} (hX : 0 ≤ X) :
  partial_Gamma (s + 1) X = s * partial_Gamma s X - (-X).exp * X ^ s :=
begin
  rw [partial_Gamma, partial_Gamma, add_sub_cancel],
  have F_der_I: (∀ (x:ℝ), (x ∈ Ioo 0 X) → has_deriv_at (λ x, (-x).exp * x ^ s : ℝ → ℂ)
    ( -((-x).exp * x ^ s) + (-x).exp * (s * x ^ (s - 1))) x),
  { intros x hx,
    have d1 : has_deriv_at (λ (y: ℝ), (-y).exp) (-(-x).exp) x,
    { simpa using (has_deriv_at_neg x).exp },
    have d2 : has_deriv_at (λ (y : ℝ), ↑y ^ s) (s * x ^ (s - 1)) x,
    { have t := @has_deriv_at.cpow_const _ _ _ s (has_deriv_at_id ↑x) _,
      simpa only [mul_one] using t.comp_of_real,
      simpa only [id.def, of_real_re, of_real_im,
        ne.def, eq_self_iff_true, not_true, or_false, mul_one] using hx.1, },
    simpa only [of_real_neg, neg_mul] using d1.of_real_comp.mul d2 },
  have cont := (continuous_of_real.comp continuous_neg.exp).mul
    (continuous_of_real_cpow_const hs),
  have der_ible := (Gamma_integrand_deriv_integrable_A hs hX).add
    (Gamma_integrand_deriv_integrable_B hs hX),
  have int_eval := integral_eq_sub_of_has_deriv_at_of_le hX cont.continuous_on F_der_I der_ible,
  -- We are basically done here but manipulating the output into the right form is fiddly.
  apply_fun (λ x:ℂ, -x) at int_eval,
  rw [interval_integral.integral_add (Gamma_integrand_deriv_integrable_A hs hX)
    (Gamma_integrand_deriv_integrable_B hs hX), interval_integral.integral_neg, neg_add, neg_neg]
    at int_eval,
  rw [eq_sub_of_add_eq int_eval, sub_neg_eq_add, neg_sub, add_comm, add_sub],
  simp only [sub_left_inj, add_left_inj],
  have : (λ x, (-x).exp * (s * x ^ (s - 1)) : ℝ → ℂ) = (λ x, s * (-x).exp * x ^ (s - 1) : ℝ → ℂ),
  { ext1, ring,},
  rw this,
  have t := @integral_const_mul 0 X volume _ _ s (λ x:ℝ, (-x).exp * x ^ (s - 1)),
  dsimp at t, rw [←t, of_real_zero, zero_cpow],
  { rw [mul_zero, add_zero], congr', ext1, ring },
  { contrapose! hs, rw [hs, zero_re] }
end

/-- The recurrence relation for the `Γ` integral. -/
theorem Gamma_integral_add_one {s : ℂ} (hs: 0 < s.re) :
  Gamma_integral (s + 1) = s * Gamma_integral s :=
begin
  suffices : tendsto (s+1).partial_Gamma at_top (𝓝 $ s * Gamma_integral s),
  { refine tendsto_nhds_unique _ this,
    apply tendsto_partial_Gamma, rw [add_re, one_re], linarith, },
  have : (λ X:ℝ, s * partial_Gamma s X - X ^ s * (-X).exp) =ᶠ[at_top] (s+1).partial_Gamma,
  { apply eventually_eq_of_mem (Ici_mem_at_top (0:ℝ)),
    intros X hX,
    rw partial_Gamma_add_one hs (mem_Ici.mp hX),
    ring_nf, },
  refine tendsto.congr' this _,
  suffices : tendsto (λ X, -X ^ s * (-X).exp : ℝ → ℂ) at_top (𝓝 0),
  { simpa using tendsto.add (tendsto.const_mul s (tendsto_partial_Gamma hs)) this },
  rw tendsto_zero_iff_norm_tendsto_zero,
  have : (λ (e : ℝ), ‖-(e:ℂ) ^ s * (-e).exp‖ ) =ᶠ[at_top] (λ (e : ℝ), e ^ s.re * (-1 * e).exp ),
  { refine eventually_eq_of_mem (Ioi_mem_at_top 0) _,
    intros x hx, dsimp only,
    rw [norm_eq_abs, map_mul, abs.map_neg, abs_cpow_eq_rpow_re_of_pos hx,
      abs_of_nonneg (exp_pos(-x)).le, neg_mul, one_mul],},
  exact (tendsto_congr' this).mpr (tendsto_rpow_mul_exp_neg_mul_at_top_nhds_0 _ _ zero_lt_one),
end

end Gamma_recurrence

/-! Now we define `Γ(s)` on the whole complex plane, by recursion. -/

section Gamma_def

/-- The `n`th function in this family is `Γ(s)` if `-n < s.re`, and junk otherwise. -/
noncomputable def Gamma_aux : ℕ → (ℂ → ℂ)
| 0      := Gamma_integral
| (n+1)  := λ s:ℂ, (Gamma_aux n (s+1)) / s

lemma Gamma_aux_recurrence1 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
  Gamma_aux n s = Gamma_aux n (s+1) / s :=
begin
  induction n with n hn generalizing s,
  { simp only [nat.cast_zero, neg_lt_zero] at h1,
    dsimp only [Gamma_aux], rw Gamma_integral_add_one h1,
    rw [mul_comm, mul_div_cancel], contrapose! h1, rw h1,
    simp },
  { dsimp only [Gamma_aux],
    have hh1 : -(s+1).re < n,
    { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one] at h1,
      rw [add_re, one_re], linarith, },
    rw ←(hn (s+1) hh1) }
end

lemma Gamma_aux_recurrence2 (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) :
  Gamma_aux n s = Gamma_aux (n+1) s :=
begin
  cases n,
  { simp only [nat.cast_zero, neg_lt_zero] at h1,
    dsimp only [Gamma_aux],
    rw [Gamma_integral_add_one h1, mul_div_cancel_left],
    rintro rfl,
    rw [zero_re] at h1,
    exact h1.false },
  { dsimp only [Gamma_aux],
    have : (Gamma_aux n (s + 1 + 1)) / (s+1) = Gamma_aux n (s + 1),
    { have hh1 : -(s+1).re < n,
      { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one] at h1,
        rw [add_re, one_re], linarith, },
      rw Gamma_aux_recurrence1 (s+1) n hh1, },
    rw this },
end

/-- The `Γ` function (of a complex variable `s`). -/
@[pp_nodot] def Gamma (s : ℂ) : ℂ := Gamma_aux ⌊1 - s.re⌋₊ s

lemma Gamma_eq_Gamma_aux (s : ℂ) (n : ℕ) (h1 : -s.re < ↑n) : Gamma s = Gamma_aux n s :=
begin
  have u : ∀ (k : ℕ), Gamma_aux (⌊1 - s.re⌋₊ + k) s = Gamma s,
  { intro k, induction k with k hk,
    { simp [Gamma],},
    { rw [←hk, nat.succ_eq_add_one, ←add_assoc],
      refine (Gamma_aux_recurrence2 s (⌊1 - s.re⌋₊ + k) _).symm,
      rw nat.cast_add,
      have i0 := nat.sub_one_lt_floor (1 - s.re),
      simp only [sub_sub_cancel_left] at i0,
      refine lt_add_of_lt_of_nonneg i0 _,
      rw [←nat.cast_zero, nat.cast_le], exact nat.zero_le k, } },
  convert (u $ n - ⌊1 - s.re⌋₊).symm, rw nat.add_sub_of_le,
  by_cases (0 ≤ 1 - s.re),
  { apply nat.le_of_lt_succ,
    exact_mod_cast lt_of_le_of_lt (nat.floor_le h) (by linarith : 1 - s.re < n + 1) },
  { rw nat.floor_of_nonpos, linarith, linarith },
end

/-- The recurrence relation for the `Γ` function. -/
theorem Gamma_add_one (s : ℂ) (h2 : s ≠ 0) : Gamma (s+1) = s * Gamma s :=
begin
  let n := ⌊1 - s.re⌋₊,
  have t1 : -s.re < n,
  { simpa only [sub_sub_cancel_left] using nat.sub_one_lt_floor (1 - s.re) },
  have t2 : -(s+1).re < n,
  { rw [add_re, one_re], linarith, },
  rw [Gamma_eq_Gamma_aux s n t1, Gamma_eq_Gamma_aux (s+1) n t2, Gamma_aux_recurrence1 s n t1],
  field_simp, ring,
end

theorem Gamma_eq_integral {s : ℂ} (hs : 0 < s.re) : Gamma s = Gamma_integral s :=
Gamma_eq_Gamma_aux s 0 (by { norm_cast, linarith })

lemma Gamma_one : Gamma 1 = 1 :=
by { rw Gamma_eq_integral, simpa using Gamma_integral_one, simp }

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n+1) = n! :=
begin
  induction n with n hn,
  { simpa using Gamma_one },
  { rw (Gamma_add_one n.succ $ nat.cast_ne_zero.mpr $ nat.succ_ne_zero n),
    simp only [nat.cast_succ, nat.factorial_succ, nat.cast_mul], congr, exact hn },
end

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
lemma Gamma_zero : Gamma 0 = 0 :=
by simp_rw [Gamma, zero_re, sub_zero, nat.floor_one, Gamma_aux, div_zero]

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value 0. -/
lemma Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 :=
begin
  induction n with n IH,
  { rw [nat.cast_zero, neg_zero, Gamma_zero] },
  { have A : -(n.succ : ℂ) ≠ 0,
    { rw [neg_ne_zero, nat.cast_ne_zero],
      apply nat.succ_ne_zero },
    have : -(n:ℂ) = -↑n.succ + 1, by simp,
    rw [this, Gamma_add_one _ A] at IH,
    contrapose! IH,
    exact mul_ne_zero A IH }
end

lemma Gamma_conj (s : ℂ) : Gamma (conj s) = conj (Gamma s) :=
begin
  suffices : ∀ (n:ℕ) (s:ℂ) , Gamma_aux n (conj s) = conj (Gamma_aux n s), from this _ _,
  intro n,
  induction n with n IH,
  { rw Gamma_aux, exact Gamma_integral_conj, },
  { intro s,
    rw Gamma_aux,
    dsimp only,
    rw [div_eq_mul_inv _ s, ring_hom.map_mul, conj_inv, ←div_eq_mul_inv],
    suffices : conj s + 1 = conj (s + 1), by rw [this, IH],
    rw [ring_hom.map_add, ring_hom.map_one] }
end

end Gamma_def

/-! Now check that the `Γ` function is differentiable, wherever this makes sense. -/

section Gamma_has_deriv

/-- Rewrite the Gamma integral as an example of a Mellin transform. -/
lemma Gamma_integral_eq_mellin :  Gamma_integral = mellin (λ x, real.exp (-x)) :=
funext (λ s, by simp only [mellin, Gamma_integral, smul_eq_mul, mul_comm])

/-- The derivative of the `Γ` integral, at any `s ∈ ℂ` with `1 < re s`, is given by the Melllin
transform of `log t * exp (-t)`. -/
theorem has_deriv_at_Gamma_integral {s : ℂ} (hs : 0 < s.re) :
  has_deriv_at Gamma_integral (∫ (t : ℝ) in Ioi 0, t ^ (s - 1) * (real.log t * real.exp (-t))) s :=
begin
  rw Gamma_integral_eq_mellin,
  convert (mellin_has_deriv_of_is_O_rpow _ _ (lt_add_one _) _ hs).2,
  { refine (continuous.continuous_on _).locally_integrable_on measurable_set_Ioi,
    exact continuous_of_real.comp (real.continuous_exp.comp continuous_neg), },
  { rw [←is_O_norm_left],
    simp_rw [complex.norm_eq_abs, abs_of_real, ←real.norm_eq_abs, is_O_norm_left],
    simpa only [neg_one_mul] using (is_o_exp_neg_mul_rpow_at_top zero_lt_one _).is_O },
  { simp_rw [neg_zero, rpow_zero],
    refine is_O_const_of_tendsto (_ : tendsto _ _ (𝓝 1)) one_ne_zero,
    rw (by simp : (1 : ℂ) = real.exp (-0)),
    exact (continuous_of_real.comp (real.continuous_exp.comp continuous_neg)).continuous_within_at }
end

lemma differentiable_at_Gamma_aux (s : ℂ) (n : ℕ) (h1 : (1 - s.re) < n ) (h2 : ∀ m : ℕ, s ≠ -m) :
  differentiable_at ℂ (Gamma_aux n) s :=
begin
  induction n with n hn generalizing s,
  { refine (has_deriv_at_Gamma_integral _).differentiable_at,
    rw nat.cast_zero at h1, linarith },
  { dsimp only [Gamma_aux],
    specialize hn (s + 1),
    have a : 1 - (s + 1).re < ↑n,
    { rw nat.cast_succ at h1, rw [complex.add_re, complex.one_re], linarith },
    have b : ∀ m : ℕ, s + 1 ≠ -m,
    { intro m, have := h2 (1 + m),
      contrapose! this,
      rw ←eq_sub_iff_add_eq at this,
      simpa using this },
    refine differentiable_at.div (differentiable_at.comp _ (hn a b) _) _ _,
    simp, simp, simpa using h2 0 }
end

theorem differentiable_at_Gamma (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) : differentiable_at ℂ Gamma s :=
begin
  let n := ⌊1 - s.re⌋₊ + 1,
  have hn : 1 - s.re < n := by exact_mod_cast nat.lt_floor_add_one (1 - s.re),
  apply (differentiable_at_Gamma_aux s n hn hs).congr_of_eventually_eq,
  let S := { t : ℂ | 1 - t.re < n },
  have : S ∈ 𝓝 s,
  { rw mem_nhds_iff, use S,
    refine ⟨subset.rfl, _, hn⟩,
    have : S = re⁻¹' Ioi (1 - n : ℝ),
    { ext, rw [preimage,Ioi, mem_set_of_eq, mem_set_of_eq, mem_set_of_eq], exact sub_lt_comm },
    rw this,
    refine continuous.is_open_preimage continuous_re _ is_open_Ioi, },
  apply eventually_eq_of_mem this,
  intros t ht, rw mem_set_of_eq at ht,
  apply Gamma_eq_Gamma_aux, linarith,
end

end Gamma_has_deriv

/-- At `s = 0`, the Gamma function has a simple pole with residue 1. -/
lemma tendsto_self_mul_Gamma_nhds_zero : tendsto (λ z : ℂ, z * Gamma z) (𝓝[≠] 0) (𝓝 1) :=
begin
  rw (show 𝓝 (1 : ℂ) = 𝓝 (Gamma (0 + 1)), by simp only [zero_add, complex.Gamma_one]),
  convert (tendsto.mono_left _ nhds_within_le_nhds).congr'
    (eventually_eq_of_mem self_mem_nhds_within complex.Gamma_add_one),
  refine continuous_at.comp _ (continuous_id.add continuous_const).continuous_at,
  refine (complex.differentiable_at_Gamma _ (λ m, _)).continuous_at,
  rw [zero_add, ←of_real_nat_cast, ←of_real_neg, ←of_real_one, ne.def, of_real_inj],
  refine (lt_of_le_of_lt _ zero_lt_one).ne',
  exact neg_nonpos.mpr (nat.cast_nonneg _),
end

end complex

namespace real

/-- The `Γ` function (of a real variable `s`). -/
@[pp_nodot] def Gamma (s : ℝ) : ℝ := (complex.Gamma s).re

lemma Gamma_eq_integral {s : ℝ} (hs : 0 < s) : Gamma s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1) :=
begin
  rw [Gamma, complex.Gamma_eq_integral (by rwa complex.of_real_re : 0 < complex.re s)],
  dsimp only [complex.Gamma_integral],
  simp_rw [←complex.of_real_one, ←complex.of_real_sub],
  suffices : ∫ (x : ℝ) in Ioi 0, ↑(exp (-x)) * (x : ℂ) ^ ((s - 1 : ℝ) : ℂ) =
    ∫ (x : ℝ) in Ioi 0, ((exp (-x) * x ^ (s - 1) : ℝ) : ℂ),
  { rw [this, _root_.integral_of_real, complex.of_real_re], },
  refine set_integral_congr measurable_set_Ioi (λ x hx, _),
  push_cast,
  rw complex.of_real_cpow (le_of_lt hx),
  push_cast,
end

lemma Gamma_add_one {s : ℝ} (hs : s ≠ 0) : Gamma (s + 1) = s * Gamma s :=
begin
  simp_rw Gamma,
  rw [complex.of_real_add, complex.of_real_one, complex.Gamma_add_one, complex.of_real_mul_re],
  rwa complex.of_real_ne_zero,
end

lemma Gamma_one : Gamma 1 = 1 :=
by rw [Gamma, complex.of_real_one, complex.Gamma_one, complex.one_re]

lemma _root_.complex.Gamma_of_real (s : ℝ) : complex.Gamma (s : ℂ) = Gamma s :=
by rw [Gamma, eq_comm, ←complex.conj_eq_iff_re, ←complex.Gamma_conj, complex.conj_of_real]

theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n! :=
by rw [Gamma, complex.of_real_add, complex.of_real_nat_cast, complex.of_real_one,
  complex.Gamma_nat_eq_factorial, ←complex.of_real_nat_cast, complex.of_real_re]

/-- At `0` the Gamma function is undefined; by convention we assign it the value `0`. -/
lemma Gamma_zero : Gamma 0 = 0 :=
by simpa only [←complex.of_real_zero, complex.Gamma_of_real, complex.of_real_inj]
  using complex.Gamma_zero

/-- At `-n` for `n ∈ ℕ`, the Gamma function is undefined; by convention we assign it the value `0`.
-/
lemma Gamma_neg_nat_eq_zero (n : ℕ) : Gamma (-n) = 0 :=
begin
  simpa only [←complex.of_real_nat_cast, ←complex.of_real_neg, complex.Gamma_of_real,
    complex.of_real_eq_zero] using complex.Gamma_neg_nat_eq_zero n,
end

lemma Gamma_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Gamma s :=
begin
  rw Gamma_eq_integral hs,
  have : function.support (λ (x : ℝ), exp (-x) * x ^ (s - 1)) ∩ Ioi 0 = Ioi 0,
  { rw inter_eq_right_iff_subset,
    intros x hx,
    rw function.mem_support,
    exact mul_ne_zero (exp_pos _).ne' (rpow_pos_of_pos hx _).ne' },
  rw set_integral_pos_iff_support_of_nonneg_ae,
  { rw [this, volume_Ioi, ←ennreal.of_real_zero],
    exact ennreal.of_real_lt_top },
  { refine eventually_of_mem (self_mem_ae_restrict measurable_set_Ioi) _,
    exact λ x hx, (mul_pos (exp_pos _) (rpow_pos_of_pos hx _)).le },
  { exact Gamma_integral_convergent hs },
end

/-- The Gamma function does not vanish on `ℝ` (except at non-positive integers, where the function
is mathematically undefined and we set it to `0` by convention). -/
lemma Gamma_ne_zero {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : Gamma s ≠ 0 :=
begin
  suffices : ∀ {n : ℕ}, (-(n:ℝ) < s) → Gamma s ≠ 0,
  { apply this,
    swap, use (⌊-s⌋₊ + 1),
    rw [neg_lt, nat.cast_add, nat.cast_one],
    exact nat.lt_floor_add_one _ },
  intro n,
  induction n generalizing s,
  { intro hs,
    refine (Gamma_pos_of_pos _).ne',
    rwa [nat.cast_zero, neg_zero] at hs },
  { intro hs',
    have : Gamma (s + 1) ≠ 0,
    { apply n_ih,
      { intro m,
        specialize hs (1 + m),
        contrapose! hs,
        rw ←eq_sub_iff_add_eq at hs,
        rw hs,
        push_cast,
        ring },
      { rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one, neg_add] at hs',
        linarith }  },
    rw [Gamma_add_one, mul_ne_zero_iff] at this,
    { exact this.2 },
    { simpa using hs 0 } },
end

lemma Gamma_eq_zero_iff (s : ℝ) : Gamma s = 0 ↔ ∃ m : ℕ, s = -m :=
⟨by { contrapose!, exact Gamma_ne_zero }, by { rintro ⟨m, rfl⟩, exact Gamma_neg_nat_eq_zero m }⟩

lemma differentiable_at_Gamma {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) : differentiable_at ℝ Gamma s :=
begin
  refine ((complex.differentiable_at_Gamma _ _).has_deriv_at).real_of_complex.differentiable_at,
  simp_rw [←complex.of_real_nat_cast, ←complex.of_real_neg, ne.def, complex.of_real_inj],
  exact hs,
end

end real
