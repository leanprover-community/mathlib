/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.complex.circle
import analysis.inner_product_space.l2_space
import measure_theory.function.continuous_map_dense
import measure_theory.function.l2_space
import measure_theory.measure.haar
import topology.metric_space.emetric_paracompact
import topology.continuous_function.stone_weierstrass

/-!

# Fourier analysis on the circle

This file contains basic results on Fourier series.

## Main definitions

* `haar_circle`, Haar measure on the circle, normalized to have total measure `1`
* instances `measure_space`, `is_probability_measure` for the circle with respect to this measure
* for `n : ℤ`, `fourier n` is the monomial `λ z, z ^ n`, bundled as a continuous map from `circle`
  to `ℂ`
* for `n : ℤ` and `p : ℝ≥0∞`, `fourier_Lp p n` is an abbreviation for the monomial `fourier n`
  considered as an element of the Lᵖ-space `Lp ℂ p haar_circle`, via the embedding
  `continuous_map.to_Lp`
* `fourier_series` is the canonical isometric isomorphism from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`
  induced by taking Fourier series

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(circle, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows from
the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation, and
separates points.

The theorem `span_fourier_Lp_closure_eq_top` states that for `1 ≤ p < ∞` the span of the monomials
`fourier_Lp` is dense in `Lp ℂ p haar_circle`, i.e. that its `submodule.topological_closure` is
`⊤`.  This follows from the previous theorem using general theory on approximation of Lᵖ functions
by continuous functions.

The theorem `orthonormal_fourier` states that the monomials `fourier_Lp 2 n` form an orthonormal
set (in the L² space of the circle).

The last two results together provide that the functions `fourier_Lp 2 n` form a Hilbert basis for
L²; this is named as `fourier_series`.

Parseval's identity, `tsum_sq_fourier_series_repr`, is a direct consequence of the construction of
this Hilbert basis.
-/

noncomputable theory
open_locale ennreal complex_conjugate classical
open topological_space continuous_map measure_theory measure_theory.measure algebra submodule set

local attribute [instance] fact_one_le_two_ennreal

/-! ### Choice of measure on the circle -/

section haar_circle
/-! We make the circle into a measure space, using the Haar measure normalized to have total
measure 1. -/

instance : measurable_space circle := borel circle
instance : borel_space circle := ⟨rfl⟩

/-- Haar measure on the circle, normalized to have total measure 1. -/
def haar_circle : measure circle := haar_measure positive_compacts_univ

instance : is_probability_measure haar_circle := ⟨haar_measure_self⟩

instance : measure_space circle :=
{ volume := haar_circle,
  .. circle.measurable_space }

end haar_circle

/-! ### Monomials on the circle -/

section monomials

/-- The family of monomials `λ z, z ^ n`, parametrized by `n : ℤ` and considered as bundled
continuous maps from `circle` to `ℂ`. -/
@[simps] def fourier (n : ℤ) : C(circle, ℂ) :=
{ to_fun := λ z, z ^ n,
  continuous_to_fun := continuous_subtype_coe.zpow n $ λ z, or.inl (nonzero_of_mem_circle z) }

@[simp] lemma fourier_zero {z : circle} : fourier 0 z = 1 := rfl

@[simp] lemma fourier_neg {n : ℤ} {z : circle} : fourier (-n) z = conj (fourier n z) :=
by simp [← coe_inv_circle_eq_conj z]

@[simp] lemma fourier_add {m n : ℤ} {z : circle} :
  fourier (m + n) z = (fourier m z) * (fourier n z) :=
by simp [zpow_add₀ (nonzero_of_mem_circle z)]

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ`; equivalently, polynomials in
`z` and `conj z`. -/
def fourier_subalgebra : subalgebra ℂ C(circle, ℂ) := algebra.adjoin ℂ (range fourier)

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is in fact the linear span of
these functions. -/
lemma fourier_subalgebra_coe : fourier_subalgebra.to_submodule = span ℂ (range fourier) :=
begin
  apply adjoin_eq_span_of_subset,
  refine subset.trans _ submodule.subset_span,
  intros x hx,
  apply submonoid.closure_induction hx (λ _, id) ⟨0, rfl⟩,
  rintros _ _ ⟨m, rfl⟩ ⟨n, rfl⟩,
  refine ⟨m + n, _⟩,
  ext1 z,
  exact fourier_add,
end

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` separates points. -/
lemma fourier_subalgebra_separates_points : fourier_subalgebra.separates_points :=
begin
  intros x y hxy,
  refine ⟨_, ⟨fourier 1, _, rfl⟩, _⟩,
  { exact subset_adjoin ⟨1, rfl⟩ },
  { simp [hxy] }
end

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is invariant under complex
conjugation. -/
lemma fourier_subalgebra_conj_invariant :
  conj_invariant_subalgebra (fourier_subalgebra.restrict_scalars ℝ) :=
begin
  rintros _ ⟨f, hf, rfl⟩,
  change _ ∈ fourier_subalgebra,
  change _ ∈ fourier_subalgebra at hf,
  apply adjoin_induction hf,
  { rintros _ ⟨n, rfl⟩,
    suffices : fourier (-n) ∈ fourier_subalgebra,
    { convert this,
      ext1,
      simp },
    exact subset_adjoin ⟨-n, rfl⟩ },
  { intros c,
    exact fourier_subalgebra.algebra_map_mem (conj c) },
  { intros f g hf hg,
    convert fourier_subalgebra.add_mem hf hg,
    exact alg_hom.map_add _ f g, },
  { intros f g hf hg,
    convert fourier_subalgebra.mul_mem hf hg,
    exact alg_hom.map_mul _ f g, }
end

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is dense. -/
lemma fourier_subalgebra_closure_eq_top : fourier_subalgebra.topological_closure = ⊤ :=
continuous_map.subalgebra_complex_topological_closure_eq_top_of_separates_points
  fourier_subalgebra
  fourier_subalgebra_separates_points
  fourier_subalgebra_conj_invariant

/-- The linear span of the monomials `z ^ n` is dense in `C(circle, ℂ)`. -/
lemma span_fourier_closure_eq_top : (span ℂ (range fourier)).topological_closure = ⊤ :=
begin
  rw ← fourier_subalgebra_coe,
  exact congr_arg subalgebra.to_submodule fourier_subalgebra_closure_eq_top,
end

/-- The family of monomials `λ z, z ^ n`, parametrized by `n : ℤ` and considered as elements of
the `Lp` space of functions on `circle` taking values in `ℂ`. -/
abbreviation fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) : Lp ℂ p haar_circle :=
to_Lp p haar_circle ℂ (fourier n)

lemma coe_fn_fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) :
  ⇑(fourier_Lp p n) =ᵐ[haar_circle] fourier n :=
coe_fn_to_Lp haar_circle (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `z ^ n` is dense in
`Lp ℂ p haar_circle`. -/
lemma span_fourier_Lp_closure_eq_top {p : ℝ≥0∞} [fact (1 ≤ p)] (hp : p ≠ ∞) :
  (span ℂ (range (fourier_Lp p))).topological_closure = ⊤ :=
begin
  convert (continuous_map.to_Lp_dense_range ℂ hp haar_circle ℂ).topological_closure_map_submodule
    span_fourier_closure_eq_top,
  rw [map_span, range_comp],
  simp
end

/-- For `n ≠ 0`, a rotation by `n⁻¹ * real.pi` negates the monomial `z ^ n`. -/
lemma fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (z : circle) :
  fourier n ((exp_map_circle (n⁻¹ * real.pi) * z)) = - fourier n z :=
begin
  have : ↑n * ((↑n)⁻¹ * ↑real.pi * complex.I) = ↑real.pi * complex.I,
  { have : (n:ℂ) ≠ 0 := by exact_mod_cast hn,
    field_simp,
    ring },
  simp [mul_zpow₀, ← complex.exp_int_mul, complex.exp_pi_mul_I, this]
end

/-- The monomials `z ^ n` are an orthonormal set with respect to Haar measure on the circle. -/
lemma orthonormal_fourier : orthonormal ℂ (fourier_Lp 2) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp haar_circle (fourier i) (fourier j),
  split_ifs,
  { simp [h, is_probability_measure.measure_univ, ← fourier_neg, ← fourier_add, -fourier_to_fun] },
  simp only [← fourier_add, ← fourier_neg],
  have hij : -i + j ≠ 0,
  { rw add_comm,
    exact sub_ne_zero.mpr (ne.symm h) },
  exact integral_zero_of_mul_left_eq_neg (is_mul_left_invariant_haar_measure _)
    (fourier_add_half_inv_index hij)
end

end monomials

section fourier

/-- We define `fourier_series` to be a `ℤ`-indexed Hilbert basis for `Lp ℂ 2 haar_circle`, which by
definition is an isometric isomorphism from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`. -/
def fourier_series : hilbert_basis ℤ ℂ (Lp ℂ 2 haar_circle) :=
hilbert_basis.mk orthonormal_fourier (span_fourier_Lp_closure_eq_top (by norm_num))

/-- The elements of the Hilbert basis `fourier_series` for `Lp ℂ 2 haar_circle` are the functions
`fourier_Lp 2`, the monomials `λ z, z ^ n` on the circle considered as elements of `L2`. -/
@[simp] lemma coe_fourier_series : ⇑fourier_series = fourier_Lp 2 := hilbert_basis.coe_mk _ _

/-- Under the isometric isomorphism `fourier_series` from `Lp ℂ 2 haar_circle` to `ℓ²(ℤ, ℂ)`, the
`i`-th coefficient is the integral over the circle of `λ t, t ^ (-i) * f t`. -/
lemma fourier_series_repr (f : Lp ℂ 2 haar_circle) (i : ℤ) :
  fourier_series.repr f i = ∫ t : circle, t ^ (-i) * f t ∂ haar_circle :=
begin
  transitivity ∫ t : circle, conj ((fourier_Lp 2 i : circle → ℂ) t) * f t ∂ haar_circle,
  { simp [fourier_series.repr_apply_apply f i, measure_theory.L2.inner_def] },
  apply integral_congr_ae,
  filter_upwards [coe_fn_fourier_Lp 2 i],
  intros t ht,
  rw [ht, ← fourier_neg],
  simp [-fourier_neg]
end

/-- The Fourier series of an `L2` function `f` sums to `f`, in the `L2` topology on the circle. -/
lemma has_sum_fourier_series (f : Lp ℂ 2 haar_circle) :
  has_sum (λ i, fourier_series.repr f i • fourier_Lp 2 i) f :=
by simpa using hilbert_basis.has_sum_repr fourier_series f

/-- **Parseval's identity**: the sum of the squared norms of the Fourier coefficients equals the
`L2` norm of the function. -/
lemma tsum_sq_fourier_series_repr (f : Lp ℂ 2 haar_circle) :
  ∑' i : ℤ, ∥fourier_series.repr f i∥ ^ 2 = ∫ t : circle, ∥f t∥ ^ 2 ∂ haar_circle :=
begin
  have H₁ : ∥fourier_series.repr f∥ ^ 2 = ∑' i, ∥fourier_series.repr f i∥ ^ 2,
  { exact_mod_cast lp.norm_rpow_eq_tsum _ (fourier_series.repr f),
    norm_num },
  have H₂ : ∥fourier_series.repr f∥ ^ 2 = ∥f∥ ^2 := by simp,
  have H₃ := congr_arg is_R_or_C.re (@L2.inner_def circle ℂ ℂ _ _ _ _ _ _ _ f f),
  rw ← integral_re at H₃,
  { simp only [← norm_sq_eq_inner] at H₃,
    rw [← H₁, H₂],
    exact H₃ },
  { exact L2.integrable_inner f f },
end

end fourier
