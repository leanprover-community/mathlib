/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.trigonometric.inverse

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returing a real number in the range (-π, π],
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/

noncomputable theory

namespace complex

open_locale real topological_space
open filter

/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
if 0 ≤ x.re
then real.arcsin (x.im / x.abs)
else if 0 ≤ x.im
then real.arcsin ((-x).im / x.abs) + π
else real.arcsin ((-x).im / x.abs) - π

lemma arg_le_pi (x : ℂ) : arg x ≤ π :=
if hx₁ : 0 ≤ x.re
then by rw [arg, if_pos hx₁];
  exact le_trans (real.arcsin_le_pi_div_two _) (le_of_lt (half_lt_self real.pi_pos))
else
  if hx₂ : 0 ≤ x.im
  then by rw [arg, if_neg hx₁, if_pos hx₂, ← le_sub_iff_add_le, sub_self, real.arcsin_nonpos,
    neg_im, neg_div, neg_nonpos];
        exact div_nonneg hx₂ (abs_nonneg _)
  else by rw [arg, if_neg hx₁, if_neg hx₂];
      exact sub_le_iff_le_add.2 (le_trans (real.arcsin_le_pi_div_two _)
        (by linarith [real.pi_pos]))

lemma neg_pi_lt_arg (x : ℂ) : -π < arg x :=
if hx₁ : 0 ≤ x.re
then by rw [arg, if_pos hx₁];
  exact lt_of_lt_of_le (neg_lt_neg (half_lt_self real.pi_pos)) (real.neg_pi_div_two_le_arcsin _)
else
  have hx : x ≠ 0, from λ h, by simpa [h, lt_irrefl] using hx₁,
  if hx₂ : 0 ≤ x.im
  then by { rw [arg, if_neg hx₁, if_pos hx₂, ← sub_lt_iff_lt_add'],
    refine lt_of_lt_of_le _ real.pi_pos.le,
    rw [neg_im, sub_lt_iff_lt_add', add_zero, neg_lt, neg_div, real.arcsin_neg, neg_neg],
    exact (real.arcsin_le_pi_div_two _).trans_lt (half_lt_self real.pi_pos) }
  else by rw [arg, if_neg hx₁, if_neg hx₂, lt_sub_iff_add_lt, neg_add_self, real.arcsin_pos,
    neg_im];
      exact div_pos (neg_pos.2 (lt_of_not_ge hx₂)) (abs_pos.2 hx)

lemma arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : 0 ≤ x.im) :
  arg x = arg (-x) + π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_pos this, if_pos hxi, abs_neg]

lemma arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg {x : ℂ} (hxr : x.re < 0) (hxi : x.im < 0) :
  arg x = arg (-x) - π :=
have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos],
by rw [arg, arg, if_neg (not_le.2 hxr), if_neg (not_le.2 hxi), if_pos this, abs_neg]

@[simp] lemma arg_zero : arg 0 = 0 :=
by simp [arg, le_refl]

@[simp] lemma arg_one : arg 1 = 0 :=
by simp [arg, zero_le_one]

@[simp] lemma arg_neg_one : arg (-1) = π :=
by simp [arg, le_refl, not_le.2 (@zero_lt_one ℝ _ _)]

@[simp] lemma arg_I : arg I = π / 2 :=
by simp [arg, le_refl]

@[simp] lemma arg_neg_I : arg (-I) = -(π / 2) :=
by simp [arg, le_refl]

lemma sin_arg (x : ℂ) : real.sin (arg x) = x.im / x.abs :=
by unfold arg; split_ifs;
  simp [sub_eq_add_neg, arg, real.sin_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1
    (abs_le.1 (abs_im_div_abs_le_one x)).2, real.sin_add, neg_div, real.arcsin_neg,
    real.sin_neg]

private lemma cos_arg_of_re_nonneg {x : ℂ} (hx : x ≠ 0) (hxr : 0 ≤ x.re) :
  real.cos (arg x) = x.re / x.abs :=
have 0 ≤ 1 - (x.im / abs x) ^ 2,
  from sub_nonneg.2 $ by rw [sq, ← _root_.abs_mul_self, _root_.abs_mul, ← sq];
  exact pow_le_one _ (_root_.abs_nonneg _) (abs_im_div_abs_le_one _),
by rw [eq_div_iff_mul_eq (mt abs_eq_zero.1 hx), ← real.mul_self_sqrt (abs_nonneg x),
    arg, if_pos hxr, real.cos_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1
    (abs_le.1 (abs_im_div_abs_le_one x)).2, ← real.sqrt_mul (abs_nonneg _), ← real.sqrt_mul this,
    sub_mul, div_pow, ← sq, div_mul_cancel _ (pow_ne_zero 2 (mt abs_eq_zero.1 hx)),
    one_mul, sq, mul_self_abs, norm_sq_apply, sq, add_sub_cancel, real.sqrt_mul_self hxr]

lemma cos_arg {x : ℂ} (hx : x ≠ 0) : real.cos (arg x) = x.re / x.abs :=
if hxr : 0 ≤ x.re then cos_arg_of_re_nonneg hx hxr
else
  have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos] using hxr,
  if hxi : 0 ≤ x.im
  then have 0 ≤ (-x).re, from le_of_lt $ by simpa [neg_pos] using hxr,
    by rw [arg_eq_arg_neg_add_pi_of_im_nonneg_of_re_neg (not_le.1 hxr) hxi, real.cos_add_pi,
        cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this];
      simp [neg_div]
  else by rw [arg_eq_arg_neg_sub_pi_of_im_neg_of_re_neg (not_le.1 hxr) (not_le.1 hxi)];
    simp [sub_eq_add_neg, real.cos_add, neg_div, cos_arg_of_re_nonneg (neg_ne_zero.2 hx) this]

lemma tan_arg {x : ℂ} : real.tan (arg x) = x.im / x.re :=
begin
  by_cases h : x = 0,
  { simp only [h, zero_div, complex.zero_im, complex.arg_zero, real.tan_zero, complex.zero_re] },
  rw [real.tan_eq_sin_div_cos, sin_arg, cos_arg h,
      div_div_div_cancel_right _ (mt abs_eq_zero.1 h)]
end

lemma arg_cos_add_sin_mul_I {x : ℝ} (hx₁ : -π < x) (hx₂ : x ≤ π) :
  arg (cos x + sin x * I) = x :=
if hx₃ : -(π / 2) ≤ x ∧ x ≤ π / 2
then
  have hx₄ : 0 ≤ (cos x + sin x * I).re,
    by simp; exact real.cos_nonneg_of_mem_Icc hx₃,
  by rw [arg, if_pos hx₄];
    simp [abs_cos_add_sin_mul_I, sin_of_real_re, real.arcsin_sin hx₃.1 hx₃.2]
else if hx₄ : x < -(π / 2)
then
  have hx₅ : ¬0 ≤ (cos x + sin x * I).re :=
    suffices ¬ 0 ≤ real.cos x, by simpa,
    not_le.2 $ by rw ← real.cos_neg;
      apply real.cos_neg_of_pi_div_two_lt_of_lt; linarith,
  have hx₆ : ¬0 ≤ (cos ↑x + sin ↑x * I).im :=
    suffices real.sin x < 0, by simpa,
    by apply real.sin_neg_of_neg_of_neg_pi_lt; linarith,
  suffices -π + -real.arcsin (real.sin x) = x,
    by rw [arg, if_neg hx₅, if_neg hx₆];
    simpa [sub_eq_add_neg, add_comm, abs_cos_add_sin_mul_I, sin_of_real_re],
  by rw [← real.arcsin_neg, ← real.sin_add_pi, real.arcsin_sin]; try {simp [add_left_comm]};
    linarith
else
  have hx₅ : π / 2 < x, by cases not_and_distrib.1 hx₃; linarith,
  have hx₆ : ¬0 ≤ (cos x + sin x * I).re :=
    suffices ¬0 ≤ real.cos x, by simpa,
    not_le.2 $ by apply real.cos_neg_of_pi_div_two_lt_of_lt; linarith,
  have hx₇ : 0 ≤ (cos x + sin x * I).im :=
    suffices 0 ≤ real.sin x, by simpa,
    by apply real.sin_nonneg_of_nonneg_of_le_pi; linarith,
  suffices π - real.arcsin (real.sin x) = x,
    by rw [arg, if_neg hx₆, if_pos hx₇];
      simpa [sub_eq_add_neg, add_comm, abs_cos_add_sin_mul_I, sin_of_real_re],
  by rw [← real.sin_pi_sub, real.arcsin_sin]; simp [sub_eq_add_neg]; linarith

lemma arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
  arg x = arg y ↔ (abs y / abs x : ℂ) * x = y :=
have hax : abs x ≠ 0, from (mt abs_eq_zero.1 hx),
have hay : abs y ≠ 0, from (mt abs_eq_zero.1 hy),
⟨λ h,
  begin
    have hcos := congr_arg real.cos h,
    rw [cos_arg hx, cos_arg hy, div_eq_div_iff hax hay] at hcos,
    have hsin := congr_arg real.sin h,
    rw [sin_arg, sin_arg, div_eq_div_iff hax hay] at hsin,
    apply complex.ext,
    { rw [mul_re, ← of_real_div, of_real_re, of_real_im, zero_mul, sub_zero, mul_comm,
        ← mul_div_assoc, hcos, mul_div_cancel _ hax] },
    { rw [mul_im, ← of_real_div, of_real_re, of_real_im, zero_mul, add_zero,
        mul_comm, ← mul_div_assoc, hsin, mul_div_cancel _ hax] }
  end,
λ h,
  have hre : abs (y / x) * x.re = y.re,
    by rw ← of_real_div at h;
      simpa [-of_real_div, -is_R_or_C.of_real_div] using congr_arg re h,
  have hre' : abs (x / y) * y.re = x.re,
    by rw [← hre, abs_div, abs_div, ← mul_assoc, div_mul_div,
      mul_comm (abs _), div_self (mul_ne_zero hay hax), one_mul],
  have him : abs (y / x) * x.im = y.im,
    by rw ← of_real_div at h;
      simpa [-of_real_div, -is_R_or_C.of_real_div] using congr_arg im h,
  have him' : abs (x / y) * y.im = x.im,
    by rw [← him, abs_div, abs_div, ← mul_assoc, div_mul_div,
      mul_comm (abs _), div_self (mul_ne_zero hay hax), one_mul],
  have hxya : x.im / abs x = y.im / abs y,
    by rw [← him, abs_div, mul_comm, ← mul_div_comm, mul_div_cancel_left _ hay],
  have hnxya : (-x).im / abs x = (-y).im / abs y,
    by rw [neg_im, neg_im, neg_div, neg_div, hxya],
  if hxr : 0 ≤ x.re
  then
    have hyr : 0 ≤ y.re, from hre ▸ mul_nonneg (abs_nonneg _) hxr,
    by simp [arg, *] at *
  else
    have hyr : ¬ 0 ≤ y.re, from λ hyr, hxr $ hre' ▸ mul_nonneg (abs_nonneg _) hyr,
    if hxi : 0 ≤ x.im
    then
      have hyi : 0 ≤ y.im, from him ▸ mul_nonneg (abs_nonneg _) hxi,
      by simp [arg, *] at *
    else
      have hyi : ¬ 0 ≤ y.im, from λ hyi, hxi $ him' ▸ mul_nonneg (abs_nonneg _) hyi,
      by simp [arg, *] at *⟩

lemma arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x :=
if hx : x = 0 then by simp [hx]
else (arg_eq_arg_iff (mul_ne_zero (of_real_ne_zero.2 (ne_of_lt hr).symm) hx) hx).2 $
  by rw [abs_mul, abs_of_nonneg (le_of_lt hr), ← mul_assoc,
    of_real_mul, mul_comm (r : ℂ), ← div_div_eq_div_mul,
    div_mul_cancel _ (of_real_ne_zero.2 (ne_of_lt hr).symm),
    div_self (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), one_mul]

lemma ext_abs_arg {x y : ℂ} (h₁ : x.abs = y.abs) (h₂ : x.arg = y.arg) : x = y :=
if hy : y = 0 then by simp * at *
else have hx : x ≠ 0, from λ hx, by simp [*, eq_comm] at *,
  by rwa [arg_eq_arg_iff hx hy, h₁, div_self (of_real_ne_zero.2 (mt abs_eq_zero.1 hy)), one_mul]
    at h₂

lemma arg_of_real_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 :=
by simp [arg, hx]

lemma arg_eq_pi_iff {z : ℂ} : arg z = π ↔ z.re < 0 ∧ z.im = 0 :=
begin
  by_cases h₀ : z = 0, { simp [h₀, lt_irrefl, real.pi_ne_zero.symm] },
  have h₀' : (abs z : ℂ) ≠ 0, by simpa,
  rw [← arg_neg_one, arg_eq_arg_iff h₀ (neg_ne_zero.2 one_ne_zero), abs_neg, abs_one,
    of_real_one, one_div, ← div_eq_inv_mul, div_eq_iff_mul_eq h₀', neg_one_mul,
    ext_iff, neg_im, of_real_im, neg_zero, @eq_comm _ z.im, and.congr_left_iff],
  rcases z with ⟨x, y⟩, simp only,
  rintro rfl,
  simp only [← of_real_def, of_real_eq_zero] at *,
  simp [← ne.le_iff_lt h₀, @neg_eq_iff_neg_eq _ _ _ x, @eq_comm _ (-x)]
end

lemma arg_of_real_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
arg_eq_pi_iff.2 ⟨hx, rfl⟩

lemma arg_of_re_nonneg {x : ℂ} (hx : 0 ≤ x.re) : arg x = real.arcsin (x.im / x.abs) :=
if_pos hx

lemma arg_of_re_zero_of_im_pos {x : ℂ} (h_re : x.re = 0) (h_im : 0 < x.im) :
  arg x = π / 2 :=
begin
  rw arg_of_re_nonneg h_re.symm.le,
  have h_im_eq_abs : x.im = abs x,
  { refine le_antisymm (im_le_abs x) _,
    refine (abs_le_abs_re_add_abs_im x).trans (le_of_eq _),
    rw [h_re, _root_.abs_zero, zero_add, _root_.abs_eq_self],
    exact h_im.le, },
  rw [h_im_eq_abs, div_self],
  { exact real.arcsin_one, },
  { rw [ne.def, complex.abs_eq_zero], intro hx, rw hx at h_im, simpa using h_im, },
end

lemma arg_of_re_zero_of_im_neg {x : ℂ} (h_re : x.re = 0) (h_im : x.im < 0) :
  arg x = - π / 2 :=
begin
  rw arg_of_re_nonneg h_re.symm.le,
  have h_im_eq_abs : x.im = - abs x,
  { rw eq_neg_iff_eq_neg,
    have : - x.im = |x.im|,
    { symmetry, rw _root_.abs_eq_neg_self.mpr h_im.le, },
    rw this,
    refine le_antisymm ((abs_le_abs_re_add_abs_im x).trans (le_of_eq _)) (abs_im_le_abs x),
    rw [h_re, _root_.abs_zero, zero_add], },
  rw [h_im_eq_abs, neg_div, div_self, neg_div],
  { exact real.arcsin_neg_one, },
  { rw [ne.def, complex.abs_eq_zero], intro hx, rw hx at h_im, simpa using h_im, },
end

lemma arg_of_re_neg_of_im_nonneg {x : ℂ} (hx_re : x.re < 0) (hx_im : 0 ≤ x.im) :
  arg x = real.arcsin ((-x).im / x.abs) + π :=
by simp only [arg, hx_re.not_le, hx_im, if_true, if_false]

lemma arg_of_re_neg_of_im_neg {x : ℂ} (hx_re : x.re < 0) (hx_im : x.im < 0) :
  arg x = real.arcsin ((-x).im / x.abs) - π :=
by simp only [arg, hx_re.not_le, hx_im.not_le, if_false]

section continuity

variables {x z : ℂ}

lemma arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] λ x, real.arcsin (x.im / x.abs) :=
begin
  suffices h_forall_nhds : ∀ᶠ (y : ℂ) in (𝓝 x), 0 < y.re,
    from h_forall_nhds.mono (λ y hy, arg_of_re_nonneg hy.le),
  exact is_open.eventually_mem (is_open_lt continuous_zero continuous_re) hx,
end

lemma arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) :
  arg =ᶠ[𝓝 x] λ x, real.arcsin ((-x).im / x.abs) + π :=
begin
  suffices h_forall_nhds : ∀ᶠ (y : ℂ) in (𝓝 x), y.re < 0 ∧ 0 < y.im,
    from h_forall_nhds.mono (λ y hy, arg_of_re_neg_of_im_nonneg hy.1 hy.2.le),
  refine is_open.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im),
  exact is_open.and (is_open_lt continuous_re continuous_zero)
    (is_open_lt continuous_zero continuous_im),
end

lemma arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) :
  arg =ᶠ[𝓝 x] λ x, real.arcsin ((-x).im / x.abs) - π :=
begin
  suffices h_forall_nhds : ∀ᶠ (y : ℂ) in (𝓝 x), y.re < 0 ∧ y.im < 0,
    from h_forall_nhds.mono (λ y hy, arg_of_re_neg_of_im_neg hy.1 hy.2),
  refine is_open.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0),
  exact is_open.and (is_open_lt continuous_re continuous_zero)
    (is_open_lt continuous_im continuous_zero),
end

/-- Auxiliary lemma for `continuous_at_arg`. -/
lemma continuous_at_arg_of_re_pos (h : 0 < x.re) : continuous_at arg x :=
begin
  rw continuous_at_congr (arg_eq_nhds_of_re_pos h),
  refine real.continuous_arcsin.continuous_at.comp _,
  refine continuous_at.div continuous_im.continuous_at complex.continuous_abs.continuous_at _,
  rw abs_ne_zero,
  intro hx,
  rw hx at h,
  simpa using h,
end

/-- Auxiliary lemma for `continuous_at_arg`. -/
lemma continuous_at_arg_of_re_neg_of_im_pos (h_re : x.re < 0) (h_im : 0 < x.im) :
  continuous_at arg x :=
begin
  rw continuous_at_congr (arg_eq_nhds_of_re_neg_of_im_pos h_re h_im),
  refine continuous_at.add (real.continuous_arcsin.continuous_at.comp _) continuous_at_const,
  refine continuous_at.div (continuous.continuous_at _) complex.continuous_abs.continuous_at _,
  { continuity, },
  { rw abs_ne_zero, intro hx, rw hx at h_re, simpa using h_re, },
end

/-- Auxiliary lemma for `continuous_at_arg`. -/
lemma continuous_at_arg_of_re_neg_of_im_neg (h_re : x.re < 0) (h_im : x.im < 0) :
  continuous_at arg x :=
begin
  rw continuous_at_congr (arg_eq_nhds_of_re_neg_of_im_neg h_re h_im),
  refine continuous_at.add (real.continuous_arcsin.continuous_at.comp _) continuous_at_const,
  refine continuous_at.div (continuous.continuous_at _) complex.continuous_abs.continuous_at _,
  { continuity, },
  { rw abs_ne_zero, intro hx, rw hx at h_re, simpa using h_re, },
end

private lemma continuous_at_arcsin_im_div_abs (h : x ≠ 0) :
  continuous_at (λ y : ℂ, real.arcsin (y.im / abs y)) x :=
begin
  refine real.continuous_arcsin.continuous_at.comp _,
  refine continuous_at.div (continuous.continuous_at _) complex.continuous_abs.continuous_at _,
  { continuity, },
  { rw abs_ne_zero, exact λ hx, h hx, },
end

private lemma continuous_at_arcsin_im_neg_div_abs_add (h : x ≠ 0) {r : ℝ} :
  continuous_at (λ y : ℂ, real.arcsin ((-y).im / abs y) + r) x :=
begin
  refine continuous_at.add _ continuous_at_const,
  have : (λ (y : ℂ), real.arcsin ((-y).im / abs y)) =
      (λ (y : ℂ), real.arcsin (y.im / abs y)) ∘ (λ y, - y),
    by { ext1 y, simp, },
  rw this,
  exact continuous_at.comp (continuous_at_arcsin_im_div_abs (neg_ne_zero.mpr h)) continuous_at_neg,
end

/-- Auxiliary lemma for `continuous_at_arg`. -/
lemma continuous_at_arg_of_re_zero (h_re : x.re = 0) (h_im : x.im ≠ 0) : continuous_at arg x :=
begin
  have hx_ne_zero : x ≠ 0, by { intro hx, rw hx at h_im, simpa using h_im, },
  have hx_abs : 0 < |x.im|, by rwa _root_.abs_pos,
  have h_cont_1 : continuous_at (λ y : ℂ, real.arcsin (y.im / abs y)) x,
    from continuous_at_arcsin_im_div_abs hx_ne_zero,
  have h_cont_2 : continuous_at (λ y : ℂ, real.arcsin ((-y).im / abs y) + real.pi) x,
    from continuous_at_arcsin_im_neg_div_abs_add hx_ne_zero,
  have h_cont_3 : continuous_at (λ y : ℂ, real.arcsin ((-y).im / abs y) - real.pi) x,
    by { simp_rw sub_eq_add_neg, exact continuous_at_arcsin_im_neg_div_abs_add hx_ne_zero, },
  have h_val1_x_pos : 0 < x.im → real.arcsin (x.im / abs x) = π / 2,
    by { rw ← arg_of_re_nonneg h_re.symm.le, exact arg_of_re_zero_of_im_pos h_re, },
  have h_val1_x_neg : x.im < 0 → real.arcsin (x.im / abs x) = - π / 2,
    by { rw ← arg_of_re_nonneg h_re.symm.le, exact arg_of_re_zero_of_im_neg h_re, },
  have h_val2_x : 0 < x.im → real.arcsin ((-x).im / abs x) + π = π / 2,
  { intro h_im_pos,
    rw [complex.neg_im, neg_div, real.arcsin_neg, ← arg_of_re_nonneg h_re.symm.le,
      arg_of_re_zero_of_im_pos h_re h_im_pos],
    ring, },
  have h_val3_x : x.im < 0 → real.arcsin ((-x).im / abs x) - π = - π / 2,
  { intro h_im_neg,
    rw [complex.neg_im, neg_div, real.arcsin_neg, ← arg_of_re_nonneg h_re.symm.le,
      arg_of_re_zero_of_im_neg h_re h_im_neg],
    ring, },
  rw metric.continuous_at_iff at ⊢ h_cont_1 h_cont_2 h_cont_3,
  intros ε hε_pos,
  rcases h_cont_1 ε hε_pos with ⟨δ₁, hδ₁, h1_x⟩,
  rcases h_cont_2 ε hε_pos with ⟨δ₂, hδ₂, h2_x⟩,
  rcases h_cont_3 ε hε_pos with ⟨δ₃, hδ₃, h3_x⟩,
  refine ⟨min (min δ₁ δ₂) (min δ₃ (|x.im|)), lt_min (lt_min hδ₁ hδ₂) (lt_min hδ₃ hx_abs),
    λ y hy, _⟩,
  specialize h1_x (hy.trans_le ((min_le_left _ _).trans (min_le_left _ _))),
  specialize h2_x (hy.trans_le ((min_le_left _ _).trans (min_le_right _ _))),
  specialize h3_x (hy.trans_le ((min_le_right _ _).trans (min_le_left _ _))),
  have hy_lt_abs : abs (y - x) < |x.im|,
  { refine (le_of_eq _).trans_lt (hy.trans_le ((min_le_right _ _).trans (min_le_right _ _))),
    rw dist_eq, },
  rw arg_of_re_nonneg h_re.symm.le,
  by_cases hy_re : 0 ≤ y.re,
  { rwa arg_of_re_nonneg hy_re, },
  push_neg at hy_re,
  rw ne_iff_lt_or_gt at h_im,
  cases h_im,
  { have hy_im : y.im < 0,
      calc y.im = x.im + (y - x).im : by simp
      ... ≤ x.im + abs (y - x) : add_le_add_left (im_le_abs _) _
      ... < x.im + |x.im| : add_lt_add_left hy_lt_abs _
      ... = x.im - x.im : by { rw [abs_eq_neg_self.mpr, ← sub_eq_add_neg], exact h_im.le, }
      ... = 0 : sub_self x.im,
    rw [arg_of_re_neg_of_im_neg hy_re hy_im, h_val1_x_neg h_im],
    rwa h_val3_x h_im at h3_x, },
  { have hy_im : 0 < y.im,
      calc 0 = x.im - x.im : (sub_self x.im).symm
      ... = x.im - |x.im| : by { rw [abs_eq_self.mpr], exact h_im.lt.le, }
      ... < x.im - abs (y - x) : sub_lt_sub_left hy_lt_abs _
      ... = x.im - abs (x - y) : by rw complex.abs_sub_comm _ _
      ... ≤ x.im - (x - y).im : sub_le_sub_left (im_le_abs _) _
      ... = y.im : by simp,
    rw [arg_of_re_neg_of_im_nonneg hy_re hy_im.le, h_val1_x_pos h_im],
    rwa h_val2_x h_im at h2_x, },
end

lemma continuous_at_arg (h : 0 < x.re ∨ x.im ≠ 0) : continuous_at arg x :=
begin
  by_cases h_re : 0 < x.re,
  { exact continuous_at_arg_of_re_pos h_re, },
  have h_im : x.im ≠ 0, by simpa [h_re] using h,
  rw not_lt_iff_eq_or_lt at h_re,
  cases h_re,
  { exact continuous_at_arg_of_re_zero h_re.symm h_im, },
  { rw ne_iff_lt_or_gt at h_im,
    cases h_im,
    { exact continuous_at_arg_of_re_neg_of_im_neg h_re h_im, },
    { exact continuous_at_arg_of_re_neg_of_im_pos h_re h_im, }, },
end

lemma tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero
  {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  tendsto arg (𝓝[{z : ℂ | z.im < 0}] z) (𝓝 (-π)) :=
begin
  suffices H :
    tendsto (λ x : ℂ, real.arcsin ((-x).im / x.abs) - π) (𝓝[{z : ℂ | z.im < 0}] z) (𝓝 (-π)),
  { refine H.congr' _,
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0, from continuous_re.tendsto z (gt_mem_nhds hre),
    filter_upwards [self_mem_nhds_within, mem_nhds_within_of_mem_nhds this],
    intros w him hre,
    rw [arg, if_neg hre.not_le, if_neg him.not_le] },
  convert (real.continuous_at_arcsin.comp_continuous_within_at
    ((continuous_im.continuous_at.comp_continuous_within_at continuous_within_at_neg).div
      continuous_abs.continuous_within_at _)).sub tendsto_const_nhds,
  { simp [him] },
  { lift z to ℝ using him, simpa using hre.ne }
end

lemma continuous_within_at_arg_of_re_neg_of_im_zero
  {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  continuous_within_at arg {z : ℂ | 0 ≤ z.im} z :=
begin
  have : arg =ᶠ[𝓝[{z : ℂ | 0 ≤ z.im}] z] λ x, real.arcsin ((-x).im / x.abs) + π,
  { have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0, from continuous_re.tendsto z (gt_mem_nhds hre),
    filter_upwards [self_mem_nhds_within, mem_nhds_within_of_mem_nhds this],
    intros w him hre,
    rw [arg, if_neg hre.not_le, if_pos him] },
  refine continuous_within_at.congr_of_eventually_eq _ this _,
  { refine (real.continuous_at_arcsin.comp_continuous_within_at
      ((continuous_im.continuous_at.comp_continuous_within_at continuous_within_at_neg).div
        continuous_abs.continuous_within_at _)).add tendsto_const_nhds,
    lift z to ℝ using him, simpa using hre.ne },
  { rw [arg, if_neg hre.not_le, if_pos him.ge] }
end

lemma tendsto_arg_nhds_within_im_nonneg_of_re_neg_of_im_zero
  {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  tendsto arg (𝓝[{z : ℂ | 0 ≤ z.im}] z) (𝓝 π) :=
by simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩]
  using (continuous_within_at_arg_of_re_neg_of_im_zero hre him).tendsto

end continuity

end complex
