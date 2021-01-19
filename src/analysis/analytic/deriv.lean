import analysis.calculus.deriv
import analysis.analytic.basic

open filter asymptotics
open_locale topological_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]

section fderiv

variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {f : E → F} {p : formal_multilinear_series 𝕜 E F} {s : set E} {x : E} {r : ennreal}

lemma has_fpower_series_at.has_strict_fderiv_at (h : has_fpower_series_at f p x) :
  has_strict_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p 1)) x :=
begin
  refine h.is_O_image_sub_norm_mul_norm_sub.trans_is_o (is_o.of_norm_right _),
  refine is_o_iff_exists_eq_mul.2 ⟨λ y, ∥y - (x, x)∥, _, eventually_eq.rfl⟩,
  refine (continuous_id.sub continuous_const).norm.tendsto' _ _ _,
  rw [id, sub_self, norm_zero]
end

lemma has_fpower_series_at.has_fderiv_at (h : has_fpower_series_at f p x) :
  has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p 1)) x :=
h.has_strict_fderiv_at.has_fderiv_at

lemma has_fpower_series_at.differentiable_at (h : has_fpower_series_at f p x) :
  differentiable_at 𝕜 f x :=
h.has_fderiv_at.differentiable_at

lemma analytic_at.differentiable_at : analytic_at 𝕜 f x → differentiable_at 𝕜 f x
| ⟨p, hp⟩ := hp.differentiable_at

lemma analytic_at.differentiable_within_at (h : analytic_at 𝕜 f x) :
  differentiable_within_at 𝕜 f s x :=
h.differentiable_at.differentiable_within_at

lemma has_fpower_series_on_ball.differentiable_on [complete_space F]
  (h : has_fpower_series_on_ball f p x r) :
  differentiable_on 𝕜 f (emetric.ball x r) :=
λ y hy, (h.analytic_at_of_mem hy).differentiable_within_at

end fderiv

variables {f : 𝕜 → 𝕜} {p : formal_multilinear_series 𝕜 𝕜 𝕜} {s : set 𝕜} {x : 𝕜} {r : ennreal}

lemma has_fpower_series_at.has_strict_deriv_at (h : has_fpower_series_at f p x) :
  has_strict_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_fderiv_at.has_strict_deriv_at

lemma has_fpower_series_at.has_deriv_at (h : has_fpower_series_at f p x) :
  has_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_deriv_at.has_deriv_at
