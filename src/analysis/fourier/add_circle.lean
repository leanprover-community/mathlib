/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, David Loeffler
-/
import analysis.special_functions.exp_deriv
import analysis.special_functions.complex.circle
import analysis.inner_product_space.l2_space
import measure_theory.function.continuous_map_dense
import measure_theory.function.l2_space
import measure_theory.group.integration
import measure_theory.integral.periodic
import topology.continuous_function.stone_weierstrass
import measure_theory.integral.fund_thm_calculus

/-!

# Fourier analysis on the additive circle

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains basic results on Fourier series for functions on the additive circle
`add_circle T = ℝ / ℤ • T`.

## Main definitions

* `haar_add_circle`, Haar measure on `add_circle T`, normalized to have total measure `1`. (Note
  that this is not the same normalisation as the standard measure defined in `integral.periodic`,
  so we do not declare it as a `measure_space` instance, to avoid confusion.)
* for `n : ℤ`, `fourier n` is the monomial `λ x, exp (2 π i n x / T)`, bundled as a continuous map
  from `add_circle T` to `ℂ`.
* `fourier_basis` is the Hilbert basis of `Lp ℂ 2 haar_add_circle` given by the images of the
  monomials `fourier n`.
* `fourier_coeff f n`, for `f : add_circle T → E` (with `E` a complete normed `ℂ`-vector space), is
  the `n`-th Fourier coefficient of `f`, defined as an integral over `add_circle T`. The lemma
  `fourier_coeff_eq_interval_integral` expresses this as an integral over `[a, a + T]` for any real
  `a`.
* `fourier_coeff_on`, for `f : ℝ → E` and `a < b` reals, is the `n`-th Fourier
  coefficient of the unique periodic function of period `b - a` which agrees with `f` on `(a, b]`.
  The lemma `fourier_coeff_on_eq_integral` expresses this as an integral over `[a, b]`.

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(add_circle T, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows
from the Stone-Weierstrass theorem after checking that the span is a subalgebra, is closed under
conjugation, and separates points.

Using this and general theory on approximation of Lᵖ functions by continuous functions, we deduce
(`span_fourier_Lp_closure_eq_top`) that for any `1 ≤ p < ∞`, the span of the Fourier monomials is
dense in the Lᵖ space of `add_circle T`. For `p = 2` we show (`orthonormal_fourier`) that the
monomials are also orthonormal, so they form a Hilbert basis for L², which is named as
`fourier_basis`; in particular, for `L²` functions `f`, the Fourier series of `f` converges to `f`
in the `L²` topology (`has_sum_fourier_series_L2`). Parseval's identity, `tsum_sq_fourier_coeff`, is
a direct consequence.

For continuous maps `f : add_circle T → ℂ`, the theorem
`continuous_map.has_sum_fourier_series_of_summable` states that if the sequence of Fourier
coefficients of `f` is summable, then the Fourier series `∑ (i:ℤ), f.fourier_coeff i * fourier i`
converges to `f` in the uniform-convergence topology of `C(add_circle T, ℂ)`.
-/

noncomputable theory
open_locale ennreal complex_conjugate real
open topological_space continuous_map measure_theory measure_theory.measure algebra submodule set

variables {T : ℝ}

namespace add_circle

/-! ### Map from `add_circle` to `circle` -/

lemma scaled_exp_map_periodic :
  function.periodic (λ x, exp_map_circle (2 * π / T * x)) T :=
begin
  -- The case T = 0 is not interesting, but it is true, so we prove it to save hypotheses
  rcases eq_or_ne T 0 with rfl | hT,
  { intro x, simp },
  { intro x, simp_rw mul_add, rw [div_mul_cancel _ hT, periodic_exp_map_circle] }
end

/-- The canonical map `λ x, exp (2 π i x / T)` from `ℝ / ℤ • T` to the unit circle in `ℂ`.
If `T = 0` we understand this as the constant function 1. -/
def to_circle : add_circle T → circle := (@scaled_exp_map_periodic T).lift

lemma to_circle_add (x : add_circle T) (y : add_circle T) :
  to_circle (x + y) = to_circle x * to_circle y :=
begin
  induction x using quotient_add_group.induction_on',
  induction y using quotient_add_group.induction_on',
  simp_rw [←quotient_add_group.coe_add, to_circle, function.periodic.lift_coe,
    mul_add, exp_map_circle_add],
end

lemma continuous_to_circle : continuous (@to_circle T) :=
continuous_coinduced_dom.mpr (exp_map_circle.continuous.comp $ continuous_const.mul continuous_id')

lemma injective_to_circle (hT : T ≠ 0) : function.injective (@to_circle T) :=
begin
  intros a b h,
  induction a using quotient_add_group.induction_on',
  induction b using quotient_add_group.induction_on',
  simp_rw [to_circle, function.periodic.lift_coe] at h,
  obtain ⟨m, hm⟩ := exp_map_circle_eq_exp_map_circle.mp h.symm,
  simp_rw [quotient_add_group.eq, add_subgroup.mem_zmultiples_iff, zsmul_eq_mul],
  use m,
  field_simp [real.two_pi_pos.ne'] at hm,
  rw ← mul_right_inj' real.two_pi_pos.ne',
  linarith
end

/-! ### Measure on `add_circle T`

In this file we use the Haar measure on `add_circle T` normalised to have total measure 1 (which is
**not** the same as the standard measure defined in `topology.instances.add_circle`). -/

variables [hT : fact (0 < T)]
include hT

/-- Haar measure on the additive circle, normalised to have total measure 1. -/
@[derive is_add_haar_measure]
def haar_add_circle : measure (add_circle T) := add_haar_measure ⊤

instance : is_probability_measure (@haar_add_circle T _) :=
  is_probability_measure.mk add_haar_measure_self

lemma volume_eq_smul_haar_add_circle :
  (volume : measure (add_circle T)) = ennreal.of_real T • haar_add_circle := rfl

end add_circle

open add_circle

section monomials

/-- The family of exponential monomials `λ x, exp (2 π i n x / T)`, parametrized by `n : ℤ` and
considered as bundled continuous maps from `ℝ / ℤ • T` to `ℂ`. -/
def fourier (n : ℤ) : C(add_circle T, ℂ) :=
{ to_fun := λ x, to_circle (n • x),
  continuous_to_fun := continuous_induced_dom.comp $ continuous_to_circle.comp $ continuous_zsmul _}

@[simp] lemma fourier_apply {n : ℤ} {x : add_circle T} : fourier n x = to_circle (n • x) := rfl

@[simp] lemma fourier_coe_apply {n : ℤ} {x : ℝ} :
  fourier n (x : add_circle T) = complex.exp (2 * π * complex.I * n * x / T) :=
begin
  rw [fourier_apply, ←quotient_add_group.coe_zsmul, to_circle, function.periodic.lift_coe,
    exp_map_circle_apply, complex.of_real_mul, complex.of_real_div, complex.of_real_mul,
    zsmul_eq_mul, complex.of_real_mul, complex.of_real_int_cast, complex.of_real_bit0,
    complex.of_real_one],
  congr' 1, ring,
end

@[simp] lemma fourier_zero {x : add_circle T} : fourier 0 x = 1 :=
begin
  induction x using quotient_add_group.induction_on',
  simp only [fourier_coe_apply, algebra_map.coe_zero, mul_zero, zero_mul,
    zero_div, complex.exp_zero],
end

@[simp] lemma fourier_eval_zero (n : ℤ) : fourier n (0 : add_circle T) = 1 :=
by rw [←quotient_add_group.coe_zero, fourier_coe_apply, complex.of_real_zero,
  mul_zero, zero_div, complex.exp_zero]

@[simp] lemma fourier_one {x : add_circle T} : fourier 1 x = to_circle x :=
by rw [fourier_apply, one_zsmul]

@[simp] lemma fourier_neg {n : ℤ} {x : add_circle T} : fourier (-n) x = conj (fourier n x) :=
begin
  induction x using quotient_add_group.induction_on',
  simp_rw [fourier_apply, to_circle, ←quotient_add_group.coe_zsmul,
    function.periodic.lift_coe, ←coe_inv_circle_eq_conj, ←exp_map_circle_neg, neg_smul, mul_neg],
end

@[simp] lemma fourier_add {m n : ℤ} {x : add_circle T} :
  fourier (m + n) x = fourier m x * fourier n x :=
by simp_rw [fourier_apply, add_zsmul, to_circle_add, coe_mul_unit_sphere]

lemma fourier_norm [fact (0 < T)] (n : ℤ) : ‖@fourier T n‖ = 1 :=
begin
  rw continuous_map.norm_eq_supr_norm,
  have : ∀ (x : add_circle T), ‖fourier n x‖ = 1 := λ x, abs_coe_circle _,
  simp_rw this,
  exact @csupr_const _ _ _ has_zero.nonempty _,
end

/-- For `n ≠ 0`, a translation by `T / 2 / n` negates the function `fourier n`. -/
lemma fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (hT : 0 < T) (x : add_circle T) :
  fourier n (x + ((T / 2 / n) : ℝ)) = - fourier n x :=
begin
  rw [fourier_apply, zsmul_add, ←quotient_add_group.coe_zsmul, to_circle_add, coe_mul_unit_sphere],
  have : (n : ℂ) ≠ 0 := by simpa using hn,
  have : ((@to_circle T ((n • (T / 2 / n)) : ℝ)) : ℂ) = -1,
  { rw [zsmul_eq_mul, to_circle, function.periodic.lift_coe, exp_map_circle_apply],
    replace hT := complex.of_real_ne_zero.mpr hT.ne',
    convert complex.exp_pi_mul_I using 3,
    field_simp, ring, },
  rw this, simp,
end

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` . -/
def fourier_subalgebra : subalgebra ℂ C(add_circle T, ℂ) := algebra.adjoin ℂ (range fourier)

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is in fact the
linear span of these functions. -/
lemma fourier_subalgebra_coe : (@fourier_subalgebra T).to_submodule = span ℂ (range fourier) :=
begin
  apply adjoin_eq_span_of_subset,
  refine subset.trans _ submodule.subset_span,
  intros x hx,
  apply submonoid.closure_induction hx (λ _, id) ⟨0, _⟩,
  { rintros _ _ ⟨m, rfl⟩ ⟨n, rfl⟩,
    refine ⟨m + n, _⟩,
    ext1 z,
    exact fourier_add },
  { ext1 z, exact fourier_zero }
end

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is invariant under
complex conjugation. -/
lemma fourier_subalgebra_conj_invariant :
  conj_invariant_subalgebra ((@fourier_subalgebra T).restrict_scalars ℝ) :=
begin
  apply subalgebra_conj_invariant,
  rintros _ ⟨n, rfl⟩,
  exact ⟨-n, ext (λ _, fourier_neg)⟩
end

variables [hT : fact (0 < T)]
include hT

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ`
separates points. -/
lemma fourier_subalgebra_separates_points : (@fourier_subalgebra T).separates_points :=
begin
  intros x y hxy,
  refine ⟨_, ⟨fourier 1, subset_adjoin ⟨1, rfl⟩, rfl⟩, _⟩,
  dsimp only, rw [fourier_one, fourier_one],
  contrapose! hxy,
  rw subtype.coe_inj at hxy,
  exact injective_to_circle hT.elim.ne' hxy,
end

/-- The subalgebra of `C(add_circle T, ℂ)` generated by `fourier n` for `n ∈ ℤ` is dense. -/
lemma fourier_subalgebra_closure_eq_top : (@fourier_subalgebra T).topological_closure = ⊤ :=
continuous_map.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points
  fourier_subalgebra fourier_subalgebra_separates_points fourier_subalgebra_conj_invariant

/-- The linear span of the monomials `fourier n` is dense in `C(add_circle T, ℂ)`. -/
lemma span_fourier_closure_eq_top : (span ℂ (range $ @fourier T)).topological_closure = ⊤ :=
begin
  rw ← fourier_subalgebra_coe,
  exact congr_arg subalgebra.to_submodule fourier_subalgebra_closure_eq_top,
end

/-- The family of monomials `fourier n`, parametrized by `n : ℤ` and considered as
elements of the `Lp` space of functions `add_circle T → ℂ`. -/
abbreviation fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) : Lp ℂ p (@haar_add_circle T hT) :=
to_Lp p haar_add_circle ℂ (fourier n)

lemma coe_fn_fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) :
  (@fourier_Lp T hT p _ n) =ᵐ[haar_add_circle] fourier n := coe_fn_to_Lp haar_add_circle (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `fourier n` is dense in
`Lp ℂ p haar_circle`. -/
lemma span_fourier_Lp_closure_eq_top {p : ℝ≥0∞} [fact (1 ≤ p)] (hp : p ≠ ∞) :
  (span ℂ (range (@fourier_Lp T _ p _))).topological_closure = ⊤ :=
begin
  convert (continuous_map.to_Lp_dense_range ℂ (@haar_add_circle T hT) hp ℂ
    ).topological_closure_map_submodule (span_fourier_closure_eq_top),
  rw [map_span, range_comp],
  simp only [continuous_linear_map.coe_coe],
end

/-- The monomials `fourier n` are an orthonormal set with respect to normalised Haar measure. -/
lemma orthonormal_fourier : orthonormal ℂ (@fourier_Lp T _ 2 _) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp (@haar_add_circle T hT) (fourier i) (fourier j),
  simp_rw [←fourier_neg, ←fourier_add],
  split_ifs,
  { simp_rw [h, neg_add_self],
    have : ⇑(@fourier T 0) = (λ x, 1 : (add_circle T) → ℂ),
    { ext1, exact fourier_zero },
    rw [this, integral_const, measure_univ, ennreal.one_to_real, complex.real_smul,
      complex.of_real_one, mul_one] },
  have hij : -i + j ≠ 0,
  { rw add_comm,
    exact sub_ne_zero.mpr (ne.symm h) },
  convert integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hij hT.elim),
  exact is_add_left_invariant.is_add_right_invariant
end

end monomials

section scope_hT -- everything from here on needs `0 < T`
variables [hT : fact (0 < T)]
include hT


section fourier_coeff
variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]

/-- The `n`-th Fourier coefficient of a function `add_circle T → E`, for `E` a complete normed
`ℂ`-vector space, defined as the integral over `add_circle T` of `fourier (-n) t • f t`. -/
def fourier_coeff (f : add_circle T → E) (n : ℤ) : E :=
∫ (t : add_circle T), fourier (-n) t • f t ∂ haar_add_circle

/-- The Fourier coefficients of a function on `add_circle T` can be computed as an integral
over `[a, a + T]`, for any real `a`. -/
lemma fourier_coeff_eq_interval_integral (f : add_circle T → E) (n : ℤ) (a : ℝ) :
  fourier_coeff f n = (1 / T) • ∫_{a}^{a + T} x, @fourier T (-n) x • f x :=
begin
  have : ∀ (x : ℝ), @fourier T (-n) x • f x = (λ (z : add_circle T), @fourier T (-n) z • f z) x,
  { intro x, refl, },
  simp_rw this,
  rw [fourier_coeff, add_circle.interval_integral_preimage T a,
    volume_eq_smul_haar_add_circle, integral_smul_measure, ennreal.to_real_of_real hT.out.le,
    ←smul_assoc, smul_eq_mul, one_div_mul_cancel hT.out.ne', one_smul],
end

lemma fourier_coeff.const_smul (f : add_circle T → E) (c : ℂ) (n : ℤ) :
  fourier_coeff (c • f) n = c • fourier_coeff f n :=
by simp_rw [fourier_coeff, pi.smul_apply, ←smul_assoc, smul_eq_mul, mul_comm, ←smul_eq_mul,
  smul_assoc, integral_smul]

lemma fourier_coeff.const_mul (f : add_circle T → ℂ) (c : ℂ) (n : ℤ) :
  fourier_coeff (λ x, c * f x) n = c * fourier_coeff f n :=
fourier_coeff.const_smul f c n

omit hT

/-- For a function on `ℝ`, the Fourier coefficients of `f` on `[a, b]` are defined as the
Fourier coefficients of the unique periodic function agreeing with `f` on `Ioc a b`. -/
def fourier_coeff_on {a b : ℝ} (hab : a < b) (f : ℝ → E) (n : ℤ) : E :=
begin
  haveI := fact.mk (by linarith : 0 < b - a),
  exact fourier_coeff (add_circle.lift_Ioc (b - a) a f) n
end

lemma fourier_coeff_on_eq_integral {a b : ℝ} (f : ℝ → E) (n : ℤ) (hab : a < b) :
  fourier_coeff_on hab f n =
  (1 / (b - a)) • ∫_{a}^{b} x, fourier (-n) (x : add_circle (b - a)) • f x :=
begin
  rw [fourier_coeff_on, fourier_coeff_eq_interval_integral _ _ a],
  congr' 1,
  rw [add_sub, add_sub_cancel'],
  simp_rw interval_integral.integral_of_le hab.le,
  refine set_integral_congr measurable_set_Ioc (λ x hx, _),
  dsimp only,
  rwa [lift_Ioc_coe_apply],
  rwa [add_sub, add_sub_cancel'],
end

lemma fourier_coeff_on.const_smul {a b : ℝ} (f : ℝ → E) (c : ℂ) (n : ℤ) (hab : a < b) :
  fourier_coeff_on hab (c • f) n = c • fourier_coeff_on hab f n :=
by apply fourier_coeff.const_smul

lemma fourier_coeff_on.const_mul {a b : ℝ} (f : ℝ → ℂ) (c : ℂ) (n : ℤ) (hab : a < b) :
  fourier_coeff_on hab (λ x, c * f x) n = c * fourier_coeff_on hab f n :=
fourier_coeff_on.const_smul _ _ _ _

include hT

lemma fourier_coeff_lift_Ioc_eq {a : ℝ} (f : ℝ → ℂ) (n : ℤ) :
  fourier_coeff (add_circle.lift_Ioc T a f) n =
  fourier_coeff_on (lt_add_of_pos_right a hT.out) f n :=
begin
  rw [fourier_coeff_on_eq_integral, fourier_coeff_eq_interval_integral, add_sub_cancel' a T],
  congr' 1,
  refine interval_integral.integral_congr_ae (ae_of_all _ (λ x hx, _)),
  rw lift_Ioc_coe_apply,
  rwa uIoc_of_le (lt_add_of_pos_right a hT.out).le at hx,
end

lemma fourier_coeff_lift_Ico_eq {a : ℝ} (f : ℝ → ℂ) (n : ℤ) :
  fourier_coeff (add_circle.lift_Ico T a f) n =
  fourier_coeff_on (lt_add_of_pos_right a hT.out) f n :=
begin
  rw [fourier_coeff_on_eq_integral, fourier_coeff_eq_interval_integral _ _ a, add_sub_cancel' a T],
  congr' 1,
  simp_rw [interval_integral.integral_of_le (lt_add_of_pos_right a hT.out).le,
    integral_Ioc_eq_integral_Ioo],
  refine set_integral_congr measurable_set_Ioo (λ x hx, _),
  dsimp only,
  rw lift_Ico_coe_apply (Ioo_subset_Ico_self hx),
end

end fourier_coeff

section fourier_L2

/-- We define `fourier_basis` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haar_add_circle`,
which by definition is an isometric isomorphism from `Lp ℂ 2 haar_add_circle` to `ℓ²(ℤ, ℂ)`. -/
def fourier_basis : hilbert_basis ℤ ℂ (Lp ℂ 2 $ @haar_add_circle T hT) :=
hilbert_basis.mk orthonormal_fourier (span_fourier_Lp_closure_eq_top (by norm_num)).ge

/-- The elements of the Hilbert basis `fourier_basis` are the functions `fourier_Lp 2`, i.e. the
monomials `fourier n` on the circle considered as elements of `L²`. -/
@[simp] lemma coe_fourier_basis : ⇑(@fourier_basis _ hT) = fourier_Lp 2 := hilbert_basis.coe_mk _ _

/-- Under the isometric isomorphism `fourier_basis` from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is `fourier_coeff f i`, i.e., the integral over `add_circle T` of
`λ t, fourier (-i) t * f t` with respect to the Haar measure of total mass 1. -/
lemma fourier_basis_repr (f : Lp ℂ 2 $ @haar_add_circle T hT) (i : ℤ) :
  fourier_basis.repr f i = fourier_coeff f i :=
begin
  transitivity ∫ (t : add_circle T),
    conj (((@fourier_Lp T hT 2 _ i) : add_circle T → ℂ) t) * f t ∂ haar_add_circle,
  { simp [fourier_basis.repr_apply_apply f i, measure_theory.L2.inner_def] },
  { apply integral_congr_ae,
    filter_upwards [coe_fn_fourier_Lp 2 i] with _ ht,
    rw [ht, ←fourier_neg, smul_eq_mul], }
end

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L²` space of `add_circle T`. -/
lemma has_sum_fourier_series_L2 (f : Lp ℂ 2 $ @haar_add_circle T hT) :
  has_sum (λ i, fourier_coeff f i • fourier_Lp 2 i) f :=
by { simp_rw ←fourier_basis_repr, simpa using hilbert_basis.has_sum_repr fourier_basis f }

/-- **Parseval's identity**: for an `L²` function `f` on `add_circle T`, the sum of the squared
norms of the Fourier coefficients equals the `L²` norm of `f`. -/
lemma tsum_sq_fourier_coeff (f : Lp ℂ 2 $ @haar_add_circle T hT) :
  ∑' i : ℤ, ‖fourier_coeff f i‖ ^ 2 = ∫ (t : add_circle T), ‖f t‖ ^ 2 ∂ haar_add_circle :=
begin
  simp_rw ←fourier_basis_repr,
  have H₁ : ‖fourier_basis.repr f‖ ^ 2 = ∑' i, ‖fourier_basis.repr f i‖ ^ 2,
  { exact_mod_cast lp.norm_rpow_eq_tsum _ (fourier_basis.repr f),
    norm_num },
  have H₂ : ‖fourier_basis.repr f‖ ^ 2 = ‖f‖ ^ 2 := by simp,
  have H₃ := congr_arg is_R_or_C.re (@L2.inner_def (add_circle T) ℂ ℂ _ _ _ _ _ f f),
  rw ← integral_re at H₃,
  { simp only [← norm_sq_eq_inner] at H₃,
    rw [← H₁, H₂, H₃], },
  { exact L2.integrable_inner f f },
end

end fourier_L2

section convergence

variables (f : C(add_circle T, ℂ))

lemma fourier_coeff_to_Lp (n : ℤ) :
  fourier_coeff (to_Lp 2 haar_add_circle ℂ f) n = fourier_coeff f n :=
integral_congr_ae (filter.eventually_eq.mul
  (filter.eventually_of_forall (by tauto))
  (continuous_map.coe_fn_to_ae_eq_fun haar_add_circle f))

variables {f}

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series converges
uniformly to `f`. -/
lemma has_sum_fourier_series_of_summable (h : summable (fourier_coeff f)) :
  has_sum (λ i, fourier_coeff f i • fourier i) f :=
begin
  have sum_L2 := has_sum_fourier_series_L2 (to_Lp 2 haar_add_circle ℂ f),
  simp_rw fourier_coeff_to_Lp at sum_L2,
  refine continuous_map.has_sum_of_has_sum_Lp (summable_of_summable_norm _) sum_L2,
  simp_rw [norm_smul, fourier_norm, mul_one, summable_norm_iff],
  exact h,
end

/-- If the sequence of Fourier coefficients of `f` is summable, then the Fourier series of `f`
converges everywhere pointwise to `f`. -/
lemma has_pointwise_sum_fourier_series_of_summable
  (h : summable (fourier_coeff f)) (x : add_circle T) :
  has_sum (λ i, fourier_coeff f i • fourier i x) (f x) :=
(continuous_map.eval_clm ℂ x).has_sum (has_sum_fourier_series_of_summable h)

end convergence

end scope_hT


section deriv

open complex interval_integral
open_locale interval

variables (T)

lemma has_deriv_at_fourier (n : ℤ) (x : ℝ) : has_deriv_at (λ y:ℝ, fourier n (y : add_circle T))
  (2 * π * I * n / T * fourier n (x : add_circle T)) x :=
begin
  simp_rw [fourier_coe_apply],
  refine (_ : has_deriv_at (λ y, exp (2 * π * I * n * y / T)) _ _).comp_of_real,
  rw (λ α β, by ring : ∀ (α β : ℂ), α * exp β = exp β * α),
  refine (has_deriv_at_exp _).comp x _,
  convert has_deriv_at_mul_const (2 * ↑π * I * ↑n / T),
  ext1 y, ring,
end

lemma has_deriv_at_fourier_neg (n : ℤ) (x : ℝ) :
  has_deriv_at (λ y:ℝ, fourier (-n) (y : add_circle T))
  (-2 * π * I * n / T * fourier (-n) (x : add_circle T)) x :=
by simpa using has_deriv_at_fourier T (-n) x

variables {T}

lemma has_antideriv_at_fourier_neg (hT : fact (0 < T)) {n : ℤ} (hn : n ≠ 0) (x : ℝ) :
  has_deriv_at (λ (y : ℝ), (T : ℂ) / (-2 * π * I * n) * fourier (-n) (y : add_circle T))
  (fourier (-n) (x : add_circle T)) x :=
begin
  convert (has_deriv_at_fourier_neg T n x).div_const (-2 * π * I * n / T) using 1,
  { ext1 y, rw div_div_eq_mul_div, ring, },
  { rw mul_div_cancel_left,
    simp only [ne.def, div_eq_zero_iff, neg_eq_zero, mul_eq_zero, bit0_eq_zero, one_ne_zero,
      of_real_eq_zero, false_or, int.cast_eq_zero, not_or_distrib],
    exact ⟨⟨⟨real.pi_ne_zero, I_ne_zero⟩, hn⟩, hT.out.ne'⟩ },
end

/-- Express Fourier coefficients of `f` on an interval in terms of those of its derivative. -/
lemma fourier_coeff_on_of_has_deriv_at {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ} {n : ℤ}
  (hn : n ≠ 0) (hf : ∀ x, x ∈ [a, b] → has_deriv_at f (f' x) x)
  (hf' : interval_integrable f' volume a b) :
  fourier_coeff_on hab f n =
  1 / (-2 * π * I * n) * (fourier (-n) (a : add_circle (b - a)) * (f b - f a)
    - (b - a) * fourier_coeff_on hab f' n) :=
begin
  rw ←of_real_sub,
  have hT : fact (0 < b - a) := ⟨by linarith⟩,
  simp_rw [fourier_coeff_on_eq_integral, smul_eq_mul, real_smul, of_real_div, of_real_one],
  conv { for (fourier _ _ * _) [1, 2, 3] { rw mul_comm } },
  rw integral_mul_deriv_eq_deriv_mul hf (λ x hx, has_antideriv_at_fourier_neg hT hn x) hf'
    (((map_continuous (fourier (-n))).comp (add_circle.continuous_mk' _)).interval_integrable _ _),
  dsimp only,
  have : ∀ (u v w : ℂ), u * ( (b - a : ℝ) / v * w) = (b - a : ℝ) / v * (u * w) := by {intros, ring},
  conv in (interval_integral _ _ _ _) { congr, funext, rw this, },
  rw (by ring : ((b - a : ℝ) : ℂ) / ((-2) * π * I * n)
    = ((b - a : ℝ) : ℂ) * (1 / ((-2) * π * I * n))),
  have s2 : (b : add_circle (b - a)) = (a : add_circle (b - a)),
  { simpa using coe_add_period (b - a) a, },
  rw [s2, integral_const_mul, ←sub_mul, mul_sub, mul_sub],
  congr' 1,
  { conv_lhs {rw [mul_comm, mul_div, mul_one]},
    rw [div_eq_iff (of_real_ne_zero.mpr hT.out.ne')],
    ring, },
  { ring, },
end

end deriv
