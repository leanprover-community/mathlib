/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.complex.arg

/-!
# The complex `log` function

Basic properties, relationship with `exp`, and differentiability.
-/

noncomputable theory

namespace complex

open set filter

open_locale real

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
@[pp_nodot] noncomputable def log (x : ℂ) : ℂ := x.abs.log + arg x * I

lemma log_re (x : ℂ) : x.log.re = x.abs.log := by simp [log]

lemma log_im (x : ℂ) : x.log.im = x.arg := by simp [log]

lemma neg_pi_lt_log_im (x : ℂ) : -π < (log x).im := by simp only [log_im, neg_pi_lt_arg]
lemma log_im_le_pi (x : ℂ) : (log x).im ≤ π := by simp only [log_im, arg_le_pi]

lemma exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x :=
by rw [log, exp_add_mul_I, ← of_real_sin, sin_arg, ← of_real_cos, cos_arg hx,
  ← of_real_exp, real.exp_log (abs_pos.2 hx), mul_add, of_real_div, of_real_div,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), ← mul_assoc,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), re_add_im]

lemma range_exp : range exp = {x | x ≠ 0} :=
set.ext $ λ x, ⟨by { rintro ⟨x, rfl⟩, exact exp_ne_zero x }, λ hx, ⟨log x, exp_log hx⟩⟩

lemma exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π)
  (hy₁ : - π < y.im) (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y :=
by rw [exp_eq_exp_re_mul_sin_add_cos, exp_eq_exp_re_mul_sin_add_cos y] at hxy;
  exact complex.ext
    (real.exp_injective $
      by simpa [abs_mul, abs_cos_add_sin_mul_I] using congr_arg complex.abs hxy)
    (by simpa [(of_real_exp _).symm, - of_real_exp, arg_real_mul _ (real.exp_pos _),
      arg_cos_add_sin_mul_I hx₁ hx₂, arg_cos_add_sin_mul_I hy₁ hy₂] using congr_arg arg hxy)

lemma log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂: x.im ≤ π) : log (exp x) = x :=
exp_inj_of_neg_pi_lt_of_le_pi
  (by rw log_im; exact neg_pi_lt_arg _)
  (by rw log_im; exact arg_le_pi _)
  hx₁ hx₂ (by rw [exp_log (exp_ne_zero _)])

lemma of_real_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
complex.ext
  (by rw [log_re, of_real_re, abs_of_nonneg hx])
  (by rw [of_real_im, log_im, arg_of_real_of_nonneg hx])

lemma log_of_real_re (x : ℝ) : (log (x : ℂ)).re = real.log x := by simp [log_re]

@[simp] lemma log_zero : log 0 = 0 := by simp [log]

@[simp] lemma log_one : log 1 = 0 := by simp [log]

lemma log_neg_one : log (-1) = π * I := by simp [log]

lemma log_I : log I = π / 2 * I := by simp [log]

lemma log_neg_I : log (-I) = -(π / 2) * I := by simp [log]

lemma exists_pow_nat_eq (x : ℂ) {n : ℕ} (hn : 0 < n) : ∃ z, z ^ n = x :=
begin
  by_cases hx : x = 0,
  { use 0, simp only [hx, zero_pow_eq_zero, hn] },
  { use exp (log x / n),
    rw [← exp_nat_mul, mul_div_cancel', exp_log hx],
    exact_mod_cast (pos_iff_ne_zero.mp hn) }
end

lemma exists_eq_mul_self (x : ℂ) : ∃ z, x = z * z :=
begin
  obtain ⟨z, rfl⟩ := exists_pow_nat_eq x zero_lt_two,
  exact ⟨z, sq z⟩
end

lemma two_pi_I_ne_zero : (2 * π * I : ℂ) ≠ 0 :=
by norm_num [real.pi_ne_zero, I_ne_zero]

lemma exp_eq_one_iff {x : ℂ} : exp x = 1 ↔ ∃ n : ℤ, x = n * ((2 * π) * I) :=
have real.exp (x.re) * real.cos (x.im) = 1 → real.cos x.im ≠ -1,
  from λ h₁ h₂, begin
    rw [h₂, mul_neg_eq_neg_mul_symm, mul_one, neg_eq_iff_neg_eq] at h₁,
    have := real.exp_pos x.re,
    rw ← h₁ at this,
    exact absurd this (by norm_num)
  end,
calc exp x = 1 ↔ (exp x).re = 1 ∧ (exp x).im = 0 : by simp [complex.ext_iff]
  ... ↔ real.cos x.im = 1 ∧ real.sin x.im = 0 ∧ x.re = 0 :
    begin
      rw exp_eq_exp_re_mul_sin_add_cos,
      simp [complex.ext_iff, cos_of_real_re, sin_of_real_re, exp_of_real_re,
        real.exp_ne_zero],
      split; finish [real.sin_eq_zero_iff_cos_eq]
    end
  ... ↔ (∃ n : ℤ, ↑n * (2 * π) = x.im) ∧ (∃ n : ℤ, ↑n * π = x.im) ∧ x.re = 0 :
    by rw [real.sin_eq_zero_iff, real.cos_eq_one_iff]
  ... ↔ ∃ n : ℤ, x = n * ((2 * π) * I) :
    ⟨λ ⟨⟨n, hn⟩, ⟨m, hm⟩, h⟩, ⟨n, by simp [complex.ext_iff, hn.symm, h]⟩,
      λ ⟨n, hn⟩, ⟨⟨n, by simp [hn]⟩, ⟨2 * n, by simp [hn, mul_comm, mul_assoc, mul_left_comm]⟩,
        by simp [hn]⟩⟩

lemma exp_eq_exp_iff_exp_sub_eq_one {x y : ℂ} : exp x = exp y ↔ exp (x - y) = 1 :=
by rw [exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]

lemma exp_eq_exp_iff_exists_int {x y : ℂ} : exp x = exp y ↔ ∃ n : ℤ, x = y + n * ((2 * π) * I) :=
by simp only [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff, sub_eq_iff_eq_add']

/-- `complex.exp` as a `local_homeomorph` with `source = {z | -π < im z < π}` and
`target = {z | 0 < re z} ∪ {z | im z ≠ 0}`. This definition is used to prove that `complex.log`
is complex differentiable at all points but the negative real semi-axis. -/
def exp_local_homeomorph : local_homeomorph ℂ ℂ :=
local_homeomorph.of_continuous_open
{ to_fun := exp,
  inv_fun := log,
  source := {z : ℂ | z.im ∈ Ioo (- π) π},
  target := {z : ℂ | 0 < z.re} ∪ {z : ℂ | z.im ≠ 0},
  map_source' :=
    begin
      rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩,
      refine (not_or_of_imp $ λ hz, _).symm,
      obtain rfl : y = 0,
      { rw exp_im at hz,
        simpa [(real.exp_pos _).ne', real.sin_eq_zero_iff_of_lt_of_lt h₁ h₂] using hz },
      rw [mem_set_of_eq, ← of_real_def, exp_of_real_re],
      exact real.exp_pos x
    end,
  map_target' := λ z h,
    suffices 0 ≤ z.re ∨ z.im ≠ 0,
      by simpa [log_im, neg_pi_lt_arg, (arg_le_pi _).lt_iff_ne, arg_eq_pi_iff, not_and_distrib],
    h.imp (λ h, le_of_lt h) id,
  left_inv' := λ x hx, log_exp hx.1 (le_of_lt hx.2),
  right_inv' := λ x hx, exp_log $ by { rintro rfl, simpa [lt_irrefl] using hx } }
continuous_exp.continuous_on is_open_map_exp (is_open_Ioo.preimage continuous_im)

lemma has_strict_deriv_at_log {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) :
  has_strict_deriv_at log x⁻¹ x :=
have h0 :  x ≠ 0, by { rintro rfl, simpa [lt_irrefl] using h },
exp_local_homeomorph.has_strict_deriv_at_symm h h0 $
  by simpa [exp_log h0] using has_strict_deriv_at_exp (log x)

lemma times_cont_diff_at_log {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) {n : with_top ℕ} :
  times_cont_diff_at ℂ n log x :=
exp_local_homeomorph.times_cont_diff_at_symm_deriv (exp_ne_zero $ log x) h
  (has_deriv_at_exp _) times_cont_diff_exp.times_cont_diff_at

end complex

section log_deriv

open complex filter
open_locale topological_space

variables {α : Type*}

lemma filter.tendsto.clog {l : filter α} {f : α → ℂ} {x : ℂ} (h : tendsto f l (𝓝 x))
  (hx : 0 < x.re ∨ x.im ≠ 0) :
  tendsto (λ t, log (f t)) l (𝓝 $ log x) :=
(has_strict_deriv_at_log hx).continuous_at.tendsto.comp h

variables [topological_space α]

lemma continuous_at.clog {f : α → ℂ} {x : α} (h₁ : continuous_at f x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  continuous_at (λ t, log (f t)) x :=
h₁.clog h₂

lemma continuous_within_at.clog {f : α → ℂ} {s : set α} {x : α} (h₁ : continuous_within_at f s x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  continuous_within_at (λ t, log (f t)) s x :=
h₁.clog h₂

lemma continuous_on.clog {f : α → ℂ} {s : set α} (h₁ : continuous_on f s)
  (h₂ : ∀ x ∈ s, 0 < (f x).re ∨ (f x).im ≠ 0) :
  continuous_on (λ t, log (f t)) s :=
λ x hx, (h₁ x hx).clog (h₂ x hx)

lemma continuous.clog {f : α → ℂ} (h₁ : continuous f) (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) :
  continuous (λ t, log (f t)) :=
continuous_iff_continuous_at.2 $ λ x, h₁.continuous_at.clog (h₂ x)

variables {E : Type*} [normed_group E] [normed_space ℂ E]

lemma has_strict_fderiv_at.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
  (h₁ : has_strict_fderiv_at f f' x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_fderiv_at (λ t, log (f t)) ((f x)⁻¹ • f') x :=
(has_strict_deriv_at_log h₂).comp_has_strict_fderiv_at x h₁

lemma has_strict_deriv_at.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : has_strict_deriv_at f f' x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_deriv_at (λ t, log (f t)) (f' / f x) x :=
by { rw div_eq_inv_mul, exact (has_strict_deriv_at_log h₂).comp x h₁ }

lemma has_fderiv_at.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
  (h₁ : has_fderiv_at f f' x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_fderiv_at (λ t, log (f t)) ((f x)⁻¹ • f') x :=
(has_strict_deriv_at_log h₂).has_deriv_at.comp_has_fderiv_at x h₁

lemma has_deriv_at.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : has_deriv_at f f' x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_at (λ t, log (f t)) (f' / f x) x :=
by { rw div_eq_inv_mul, exact (has_strict_deriv_at_log h₂).has_deriv_at.comp x h₁ }

lemma differentiable_at.clog {f : E → ℂ} {x : E} (h₁ : differentiable_at ℂ f x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_at ℂ (λ t, log (f t)) x :=
(h₁.has_fderiv_at.clog h₂).differentiable_at

lemma has_fderiv_within_at.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {s : set E} {x : E}
  (h₁ : has_fderiv_within_at f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_fderiv_within_at (λ t, log (f t)) ((f x)⁻¹ • f') s x :=
(has_strict_deriv_at_log h₂).has_deriv_at.comp_has_fderiv_within_at x h₁

lemma has_deriv_within_at.clog {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}
  (h₁ : has_deriv_within_at f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_within_at (λ t, log (f t)) (f' / f x) s x :=
by { rw div_eq_inv_mul,
     exact (has_strict_deriv_at_log h₂).has_deriv_at.comp_has_deriv_within_at x h₁ }

lemma differentiable_within_at.clog {f : E → ℂ} {s : set E} {x : E}
  (h₁ : differentiable_within_at ℂ f s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_within_at ℂ (λ t, log (f t)) s x :=
(h₁.has_fderiv_within_at.clog h₂).differentiable_within_at

lemma differentiable_on.clog {f : E → ℂ} {s : set E}
  (h₁ : differentiable_on ℂ f s) (h₂ : ∀ x ∈ s, 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_on ℂ (λ t, log (f t)) s :=
λ x hx, (h₁ x hx).clog (h₂ x hx)

lemma differentiable.clog {f : E → ℂ} (h₁ : differentiable ℂ f)
  (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable ℂ (λ t, log (f t)) :=
λ x, (h₁ x).clog (h₂ x)

end log_deriv
