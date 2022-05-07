/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Eric Wieser
-/
import analysis.specific_limits.basic
import analysis.analytic.basic
import analysis.complex.basic
import data.nat.choose.cast
import data.finset.noncomm_prod

/-!
# Exponential in a Banach algebra

In this file, we define `exp : 𝔸 → 𝔸`, the exponential map in a topological algebra `𝔸` over a
field `𝕂`.

While for most interesting results we need `𝔸` to be normed algebra, we do not require this in the
definition in order to make `exp` independent of a particular choice of norm. The definition also
does not require that `𝔸` be complete, but we need to assume it for most results.

We then prove some basic results, but we avoid importing derivatives here to minimize dependencies.
Results involving derivatives and comparisons with `real.exp` and `complex.exp` can be found in
`analysis/special_functions/exponential`.

## Main results

We prove most result for an arbitrary field `𝕂`, and then specialize to `𝕂 = ℝ` or `𝕂 = ℂ`.

### General case

- `exp_add_of_commute_of_mem_ball` : if `𝕂` has characteristic zero, then given two commuting
  elements `x` and `y` in the disk of convergence, we have
  `exp (x+y) = (exp x) * (exp y)`
- `exp_add_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is commutative, then given two
  elements `x` and `y` in the disk of convergence, we have
  `exp (x+y) = (exp x) * (exp y)`
- `exp_neg_of_mem_ball` : if `𝕂` has characteristic zero and `𝔸` is a division ring, then given an
  element `x` in the disk of convergence, we have `exp (-x) = (exp x)⁻¹`.

### `𝕂 = ℝ` or `𝕂 = ℂ`

- `exp_series_radius_eq_top` : the `formal_multilinear_series` defining `exp` has infinite
  radius of convergence
- `exp_add_of_commute` : given two commuting elements `x` and `y`, we have
  `exp (x+y) = (exp x) * (exp y)`
- `exp_add` : if `𝔸` is commutative, then we have `exp (x+y) = (exp x) * (exp y)`
  for any `x` and `y`
- `exp_neg` : if `𝔸` is a division ring, then we have `exp (-x) = (exp x)⁻¹`.
- `exp_sum_of_commute` : the analogous result to `exp_add_of_commute` for `finset.sum`.
- `exp_sum` : the analogous result to `exp_add` for `finset.sum`.
- `exp_nsmul` : repeated addition in the domain corresponds to repeated multiplication in the
  codomain.
- `exp_zsmul` : repeated addition in the domain corresponds to repeated multiplication in the
  codomain.

### Other useful compatibility results

- `exp_eq_exp` : if `𝔸` is a normed algebra over two fields `𝕂` and `𝕂'`, then `exp = exp' 𝔸`

-/

open filter is_R_or_C continuous_multilinear_map normed_field asymptotics
open_locale nat topological_space big_operators ennreal

section topological_algebra

variables (𝔸 : Type*) [ring 𝔸] [algebra ℚ 𝔸] [topological_space 𝔸] [topological_ring 𝔸]

/-- `exp_series 𝔸` is the `formal_multilinear_series` whose `n`-th term is the map
`(xᵢ) : 𝔸ⁿ ↦ (1/n! : 𝕂) • ∏ xᵢ`. Its sum is the exponential map `exp : 𝔸 → 𝔸`. -/
noncomputable def exp_series : formal_multilinear_series ℚ 𝔸 𝔸 :=
λ n, (n!⁻¹ : ℚ) • continuous_multilinear_map.mk_pi_algebra_fin ℚ n 𝔸

variables {𝔸}

/-- `exp : 𝔸 → 𝔸` is the exponential map determined by the action of `𝕂` on `𝔸`.
It is defined as the sum of the `formal_multilinear_series` `exp_series 𝔸`. -/
noncomputable def exp (x : 𝔸) : 𝔸 := (exp_series 𝔸).sum x

variables {𝔸}

lemma exp_series_apply_eq (x : 𝔸) (n : ℕ) : exp_series 𝔸 n (λ _, x) = (n!⁻¹ : ℚ) • x^n :=
by simp [exp_series]

lemma exp_series_apply_eq' (x : 𝔸) :
  (λ n, exp_series 𝔸 n (λ _, x)) = (λ n, (n!⁻¹ : ℚ) • x^n) :=
funext (exp_series_apply_eq x)

lemma exp_series_sum_eq (x : 𝔸) : (exp_series 𝔸).sum x = ∑' (n : ℕ), (n!⁻¹ : ℚ) • x^n :=
tsum_congr (λ n, exp_series_apply_eq x n)

lemma exp_eq_tsum : exp = (λ x : 𝔸, ∑' (n : ℕ), (n!⁻¹ : ℚ) • x^n) :=
funext exp_series_sum_eq

@[simp] lemma exp_zero [t2_space 𝔸] : exp (0 : 𝔸) = 1 :=
begin
  suffices : (λ x : 𝔸, ∑' (n : ℕ), (n!⁻¹ : ℚ) • x^n) 0 = ∑' (n : ℕ), if n = 0 then 1 else 0,
  { have key : ∀ n ∉ ({0} : finset ℕ), (if n = 0 then (1 : 𝔸) else 0) = 0,
      from λ n hn, if_neg (finset.not_mem_singleton.mp hn),
    rw [exp_eq_tsum, this, tsum_eq_sum key, finset.sum_singleton],
    simp },
  refine tsum_congr (λ n, _),
  split_ifs with h h;
  simp [h]
end

lemma commute.exp_right [t2_space 𝔸] {x y : 𝔸} (h : commute x y) :
  commute x (exp y) :=
begin
  rw exp_eq_tsum,
  exact commute.tsum_right x (λ n, (h.pow_right n).smul_right _),
end

lemma commute.exp_left [t2_space 𝔸] {x y : 𝔸} (h : commute x y) :
  commute (exp x) y :=
h.symm.exp_right.symm

lemma commute.exp [t2_space 𝔸] {x y : 𝔸} (h : commute x y) :
  commute (exp x) (exp y) :=
h.exp_left.exp_right

end topological_algebra

section topological_division_algebra
variables {𝔸 : Type*} [division_ring 𝔸] [algebra ℚ 𝔸] [topological_space 𝔸]
  [topological_ring 𝔸]

lemma exp_series_apply_eq_div (x : 𝔸) (n : ℕ) : exp_series 𝔸 n (λ _, x) = x^n / n! :=
by rw [div_eq_mul_inv, ←(nat.cast_commute n! (x ^ n)).inv_left₀.eq, ←smul_eq_mul,
    exp_series_apply_eq, inv_nat_cast_smul_eq _ _ _ _]

lemma exp_series_apply_eq_div' (x : 𝔸) : (λ n, exp_series 𝔸 n (λ _, x)) = (λ n, x^n / n!) :=
funext (exp_series_apply_eq_div x)

lemma exp_series_sum_eq_div (x : 𝔸) : (exp_series 𝔸).sum x = ∑' (n : ℕ), x^n / n! :=
tsum_congr (exp_series_apply_eq_div x)

lemma exp_eq_tsum_div : exp = (λ x : 𝔸, ∑' (n : ℕ), x^n / n!) :=
funext exp_series_sum_eq_div

end topological_division_algebra

section normed

section any_field_any_algebra

variables {𝕂 𝔸 𝔹 : Type*}
variables [normed_ring 𝔸] [normed_ring 𝔹] [normed_algebra ℚ 𝔸] [normed_algebra ℚ 𝔹]

lemma norm_exp_series_summable_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  summable (λ n, ∥exp_series 𝔸 n (λ _, x)∥) :=
(exp_series 𝔸).summable_norm_apply hx

lemma norm_exp_series_summable_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  summable (λ n, ∥(n!⁻¹ : ℚ) • x^n∥) :=
begin
  change summable (norm ∘ _),
  rw ← exp_series_apply_eq',
  exact norm_exp_series_summable_of_mem_ball x hx
end

section complete_algebra

variables [complete_space 𝔸]

lemma exp_series_summable_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  summable (λ n, exp_series 𝔸 n (λ _, x)) :=
summable_of_summable_norm (norm_exp_series_summable_of_mem_ball x hx)

lemma exp_series_summable_of_mem_ball' (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  summable (λ n, (n!⁻¹ : ℚ) • x^n) :=
summable_of_summable_norm (norm_exp_series_summable_of_mem_ball' x hx)

lemma exp_series_has_sum_exp_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  has_sum (λ n, exp_series 𝔸 n (λ _, x)) (exp x) :=
formal_multilinear_series.has_sum (exp_series 𝔸) hx

lemma exp_series_has_sum_exp_of_mem_ball'  (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  has_sum (λ n, (n!⁻¹ : ℚ) • x^n) (exp x) :=
begin
  rw ← exp_series_apply_eq',
  exact exp_series_has_sum_exp_of_mem_ball x hx
end

lemma has_fpower_series_on_ball_exp_of_radius_pos (h : 0 < (exp_series 𝔸).radius) :
  has_fpower_series_on_ball (exp) (exp_series 𝔸) 0 (exp_series 𝔸).radius :=
(exp_series 𝔸).has_fpower_series_on_ball h

lemma has_fpower_series_at_exp_zero_of_radius_pos (h : 0 < (exp_series 𝔸).radius) :
  has_fpower_series_at (exp) (exp_series 𝔸) 0 :=
(has_fpower_series_on_ball_exp_of_radius_pos h).has_fpower_series_at

lemma continuous_on_exp :
  continuous_on (exp : 𝔸 → 𝔸) (emetric.ball 0 (exp_series 𝔸).radius) :=
formal_multilinear_series.continuous_on

lemma analytic_at_exp_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  analytic_at ℚ (exp) x:=
begin
  by_cases h : (exp_series 𝔸).radius = 0,
  { rw h at hx, exact (ennreal.not_lt_zero hx).elim },
  { have h := pos_iff_ne_zero.mpr h,
    exact (has_fpower_series_on_ball_exp_of_radius_pos h).analytic_at_of_mem hx }
end

/-- In a Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero, if `x` and `y` are
in the disk of convergence and commute, then `exp (x + y) = (exp x) * (exp y)`. -/
lemma exp_add_of_commute_of_mem_ball
  {x y : 𝔸} (hxy : commute x y) (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius)
  (hy : y ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  exp (x + y) = (exp x) * (exp y) :=
begin
  rw [exp_eq_tsum, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
        (norm_exp_series_summable_of_mem_ball' x hx) (norm_exp_series_summable_of_mem_ball' y hy)],
  dsimp only,
  conv_lhs {congr, funext, rw [hxy.add_pow' _, finset.smul_sum]},
  refine tsum_congr (λ n, finset.sum_congr rfl $ λ kl hkl, _),
  rw [nsmul_eq_smul_cast ℚ, smul_smul, smul_mul_smul, ← (finset.nat.mem_antidiagonal.mp hkl),
      nat.cast_add_choose, (finset.nat.mem_antidiagonal.mp hkl)],
  congr' 1,
  have : (n! : ℚ) ≠ 0 := nat.cast_ne_zero.mpr n.factorial_ne_zero,
  field_simp [this]
end

/-- `exp x` has explicit two-sided inverse `exp (-x)`. -/
noncomputable def invertible_exp_of_mem_ball {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) : invertible (exp x) :=
{ inv_of := exp (-x),
  inv_of_mul_self := begin
    have hnx : -x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius,
    { rw [emetric.mem_ball, ←neg_zero, edist_neg_neg],
      exact hx },
    rw [←exp_add_of_commute_of_mem_ball (commute.neg_left $ commute.refl x) hnx hx, neg_add_self,
      exp_zero],
  end,
  mul_inv_of_self := begin
    have hnx : -x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius,
    { rw [emetric.mem_ball, ←neg_zero, edist_neg_neg],
      exact hx },
    rw [←exp_add_of_commute_of_mem_ball (commute.neg_right $ commute.refl x) hx hnx, add_neg_self,
      exp_zero],
  end }

lemma is_unit_exp_of_mem_ball {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) : is_unit (exp x) :=
@is_unit_of_invertible _ _ _ (invertible_exp_of_mem_ball hx)

lemma inv_of_exp_of_mem_ball {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) [invertible (exp x)] :
  ⅟(exp x) = exp (-x) :=
by { letI := invertible_exp_of_mem_ball hx, convert (rfl : ⅟(exp x) = _) }

/-- Any continuous ring homomorphism commutes with `exp`. -/
lemma map_exp_of_mem_ball {F} [ring_hom_class F 𝔸 𝔹] (f : F) (hf : continuous f) (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  f (exp x) = exp (f x) :=
begin
  rw [exp_eq_tsum, exp_eq_tsum],
  refine ((exp_series_summable_of_mem_ball' _ hx).has_sum.map f hf).tsum_eq.symm.trans _,
  dsimp only [function.comp],
  simp_rw [one_div, map_inv_nat_cast_smul f ℚ ℚ, map_pow],
end

end complete_algebra

lemma algebra_map_exp_comm_of_mem_ball [nondiscrete_normed_field 𝕂] [complete_space 𝕂]
  [normed_algebra 𝕂 𝔸] [normed_algebra ℚ 𝕂] (x : 𝕂)
  (hx : x ∈ emetric.ball (0 : 𝕂) (exp_series 𝕂).radius) :
  algebra_map 𝕂 𝔸 (exp x) = exp (algebra_map 𝕂 𝔸 x) :=
map_exp_of_mem_ball _ (algebra_map_clm _ _).continuous _ hx

end any_field_any_algebra

section any_field_division_algebra

variables {𝕂 𝔸 : Type*} [nondiscrete_normed_field 𝕂] [normed_division_ring 𝔸] [normed_algebra ℚ 𝔸]

variables (𝕂)

lemma norm_exp_series_div_summable_of_mem_ball (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  summable (λ n, ∥x^n / n!∥) :=
begin
  change summable (norm ∘ _),
  rw ← exp_series_apply_eq_div' x,
  exact norm_exp_series_summable_of_mem_ball x hx
end

lemma exp_series_div_summable_of_mem_ball [complete_space 𝔸] (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) : summable (λ n, x^n / n!) :=
summable_of_summable_norm (norm_exp_series_div_summable_of_mem_ball x hx)

lemma exp_series_div_has_sum_exp_of_mem_ball [complete_space 𝔸] (x : 𝔸)
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) : has_sum (λ n, x^n / n!) (exp x) :=
begin
  rw ← exp_series_apply_eq_div' x,
  exact exp_series_has_sum_exp_of_mem_ball x hx
end

variables {𝕂}

lemma exp_neg_of_mem_ball [complete_space 𝔸] {x : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  exp (-x) = (exp x)⁻¹ :=
begin
  letI := invertible_exp_of_mem_ball hx,
  exact inv_of_eq_inv (exp x),
end

end any_field_division_algebra


section any_field_comm_algebra

variables {𝕂 𝔸 : Type*} [nondiscrete_normed_field 𝕂] [normed_comm_ring 𝔸] [normed_algebra ℚ 𝔸]
  [complete_space 𝔸]

/-- In a commutative Banach-algebra `𝔸` over a normed field `𝕂` of characteristic zero,
`exp (x+y) = (exp x) * (exp y)` for all `x`, `y` in the disk of convergence. -/
lemma exp_add_of_mem_ball {x y : 𝔸}
  (hx : x ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius)
  (hy : y ∈ emetric.ball (0 : 𝔸) (exp_series 𝔸).radius) :
  exp (x + y) = (exp x) * (exp y) :=
exp_add_of_commute_of_mem_ball (commute.all x y) hx hy

end any_field_comm_algebra

section is_R_or_C

section any_algebra

variables (𝕂 𝔸 𝔹 : Type*) [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra ℚ 𝔸]
variables [normed_ring 𝔹] [normed_algebra ℚ 𝔹]

/-- In a normed algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, the series defining the exponential map
has an infinite radius of convergence. -/
lemma exp_series_radius_eq_top : (exp_series 𝔸).radius = ∞ :=
begin
  refine (exp_series 𝔸).radius_eq_top_of_summable_norm (λ r, _),
  refine summable_of_norm_bounded_eventually _ (real.summable_pow_div_factorial r) _,
  filter_upwards [eventually_cofinite_ne 0] with n hn,
  rw [norm_mul, norm_norm (exp_series 𝔸 n), exp_series, norm_smul, norm_inv, norm_pow,
      nnreal.norm_eq, ←rat.norm_cast_real, rat.cast_coe_nat, norm_eq_abs, abs_cast_nat, mul_comm,
      ←mul_assoc, ←div_eq_mul_inv],
  have : ∥continuous_multilinear_map.mk_pi_algebra_fin ℚ n 𝔸∥ ≤ 1 :=
    norm_mk_pi_algebra_fin_le_of_pos (nat.pos_of_ne_zero hn),
  exact mul_le_of_le_one_right (div_nonneg (pow_nonneg r.coe_nonneg n) n!.cast_nonneg) this
end

lemma exp_series_radius_pos : 0 < (exp_series 𝔸).radius :=
begin
  rw exp_series_radius_eq_top,
  exact with_top.zero_lt_top
end

variables {𝕂 𝔸 𝔹}

lemma norm_exp_series_summable (x : 𝔸) : summable (λ n, ∥exp_series 𝔸 n (λ _, x)∥) :=
norm_exp_series_summable_of_mem_ball x ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)

lemma norm_exp_series_summable' (x : 𝔸) : summable (λ n, ∥(n!⁻¹ : ℚ) • x^n∥) :=
norm_exp_series_summable_of_mem_ball' x ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)

section complete_algebra

variables [complete_space 𝔸]

lemma exp_series_summable (x : 𝔸) : summable (λ n, exp_series 𝔸 n (λ _, x)) :=
summable_of_summable_norm (norm_exp_series_summable x)

lemma exp_series_summable' (x : 𝔸) : summable (λ n, (n!⁻¹ : ℚ) • x^n) :=
summable_of_summable_norm (norm_exp_series_summable' x)

lemma exp_series_has_sum_exp (x : 𝔸) :
  has_sum (λ n, exp_series 𝔸 n (λ _, x)) (exp x) :=
exp_series_has_sum_exp_of_mem_ball x ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)

lemma exp_series_has_sum_exp' (x : 𝔸) :
  has_sum (λ n, (n!⁻¹ : ℚ) • x^n) (exp x):=
exp_series_has_sum_exp_of_mem_ball' x ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)

lemma exp_has_fpower_series_on_ball :
  has_fpower_series_on_ball (exp) (exp_series 𝔸) 0 ∞ :=
exp_series_radius_eq_top 𝔸 ▸
  has_fpower_series_on_ball_exp_of_radius_pos (exp_series_radius_pos _)

lemma exp_has_fpower_series_at_zero :
  has_fpower_series_at (exp) (exp_series 𝔸) 0 :=
exp_has_fpower_series_on_ball.has_fpower_series_at

lemma exp_continuous : continuous (exp : 𝔸 → 𝔸) :=
begin
  rw [continuous_iff_continuous_on_univ, ← metric.eball_top_eq_univ (0 : 𝔸),
      ← exp_series_radius_eq_top 𝔸],
  exact continuous_on_exp
end

lemma exp_analytic (x : 𝔸) :
  analytic_at ℚ (exp) x :=
analytic_at_exp_of_mem_ball x ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if `x` and `y` commute, then
`exp (x+y) = (exp x) * (exp y)`. -/
lemma exp_add_of_commute
  {x y : 𝔸} (hxy : commute x y) :
  exp (x + y) = (exp x) * (exp y) :=
exp_add_of_commute_of_mem_ball hxy ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)
  ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)

section
variables (𝕂)

/-- `exp x` has explicit two-sided inverse `exp (-x)`. -/
noncomputable def invertible_exp (x : 𝔸) : invertible (exp x) :=
invertible_exp_of_mem_ball $ (exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _

lemma is_unit_exp (x : 𝔸) : is_unit (exp x) :=
is_unit_exp_of_mem_ball $ (exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _

lemma inv_of_exp (x : 𝔸) [invertible (exp x)] :
  ⅟(exp x) = exp (-x) :=
inv_of_exp_of_mem_ball $ (exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _

lemma ring.inverse_exp (x : 𝔸) : ring.inverse (exp x) = exp (-x) :=
begin
  letI := invertible_exp x,
  exact ring.inverse_invertible _,
end

end

/-- In a Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`, if a family of elements `f i` mutually
commute then `exp (∑ i, f i) = ∏ i, exp (f i)`. -/
lemma exp_sum_of_commute {ι} (s : finset ι) (f : ι → 𝔸)
  (h : ∀ (i ∈ s) (j ∈ s), commute (f i) (f j)) :
  exp (∑ i in s, f i) = s.noncomm_prod (λ i, exp (f i))
    (λ i hi j hj, (h i hi j hj).exp) :=
begin
  classical,
  induction s using finset.induction_on with a s ha ih,
  { simp },
  rw [finset.noncomm_prod_insert_of_not_mem _ _ _ _ ha, finset.sum_insert ha,
      exp_add_of_commute, ih],
  refine commute.sum_right _ _ _ _,
  intros i hi,
  exact h _ (finset.mem_insert_self _ _) _ (finset.mem_insert_of_mem hi),
end

lemma exp_nsmul (n : ℕ) (x : 𝔸) :
  exp (n • x) = exp x ^ n :=
begin
  induction n with n ih,
  { rw [zero_smul, pow_zero, exp_zero], },
  { rw [succ_nsmul, pow_succ, exp_add_of_commute ((commute.refl x).smul_right n), ih] }
end

variables (𝕂)

/-- Any continuous ring homomorphism commutes with `exp`. -/
lemma map_exp {F} [ring_hom_class F 𝔸 𝔹] (f : F) (hf : continuous f) (x : 𝔸) :
  f (exp x) = exp (f x) :=
map_exp_of_mem_ball f hf x $ (exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _

lemma exp_smul {G} [monoid G] [mul_semiring_action G 𝔸] [has_continuous_const_smul G 𝔸]
  (g : G) (x : 𝔸) :
  exp (g • x) = g • exp x :=
(map_exp (mul_semiring_action.to_ring_hom G 𝔸 g) (continuous_const_smul _) x).symm

lemma exp_units_conj (y : 𝔸ˣ) (x : 𝔸)  :
  exp (y * x * ↑(y⁻¹) : 𝔸) = y * exp x * ↑(y⁻¹) :=
exp_smul (conj_act.to_conj_act y) x

lemma exp_units_conj' (y : 𝔸ˣ) (x : 𝔸)  :
  exp (↑(y⁻¹) * x * y) = ↑(y⁻¹) * exp x * y :=
exp_units_conj _ _

@[simp] lemma prod.fst_exp [complete_space 𝔹] (x : 𝔸 × 𝔹) : (exp x).fst = exp x.fst :=
map_exp (ring_hom.fst 𝔸 𝔹) continuous_fst x

@[simp] lemma prod.snd_exp [complete_space 𝔹] (x : 𝔸 × 𝔹) : (exp x).snd = exp x.snd :=
map_exp (ring_hom.snd 𝔸 𝔹) continuous_snd x

@[simp] lemma pi.exp_apply {ι : Type*} {𝔸 : ι → Type*} [fintype ι]
  [Π i, normed_ring (𝔸 i)] [Π i, normed_algebra ℚ (𝔸 i)] [Π i, complete_space (𝔸 i)]
  (x : Π i, 𝔸 i) (i : ι) :
  exp x i = exp (x i) :=
begin
  -- Lean struggles to infer this instance due to it wanting `[Π i, semi_normed_ring (𝔸 i)]`
  letI : normed_algebra ℚ (Π i, 𝔸 i) := pi.normed_algebra _,
  exact map_exp (pi.eval_ring_hom 𝔸 i) (continuous_apply _) x
end

lemma pi.exp_def {ι : Type*} {𝔸 : ι → Type*} [fintype ι]
  [Π i, normed_ring (𝔸 i)] [Π i, normed_algebra ℚ (𝔸 i)] [Π i, complete_space (𝔸 i)]
  (x : Π i, 𝔸 i) :
  exp x = λ i, exp (x i) :=
funext $ pi.exp_apply x

lemma function.update_exp {ι : Type*} {𝔸 : ι → Type*} [fintype ι] [decidable_eq ι]
  [Π i, normed_ring (𝔸 i)] [Π i, normed_algebra ℚ (𝔸 i)] [Π i, complete_space (𝔸 i)]
  (x : Π i, 𝔸 i) (j : ι) (xj : 𝔸 j) :
  function.update (exp x) j (exp xj) = exp (function.update x j xj) :=
begin
  ext i,
  simp_rw [pi.exp_def],
  exact (function.apply_update (λ i, exp) x j xj i).symm,
end

end complete_algebra

lemma algebra_map_exp_comm [normed_algebra 𝕂 𝔸] (x : 𝕂) :
  algebra_map 𝕂 𝔸 (exp x) = exp (algebra_map 𝕂 𝔸 x) :=
algebra_map_exp_comm_of_mem_ball x $
  (exp_series_radius_eq_top 𝕂).symm ▸ edist_lt_top _ _

end any_algebra

section division_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_division_ring 𝔸] [normed_algebra ℚ 𝔸]

variables (𝕂)

lemma norm_exp_series_div_summable (x : 𝔸) : summable (λ n, ∥x^n / n!∥) :=
norm_exp_series_div_summable_of_mem_ball x
  ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)

variables [complete_space 𝔸]

lemma exp_series_div_summable (x : 𝔸) : summable (λ n, x^n / n!) :=
summable_of_summable_norm (norm_exp_series_div_summable x)

lemma exp_series_div_has_sum_exp (x : 𝔸) : has_sum (λ n, x^n / n!) (exp x):=
exp_series_div_has_sum_exp_of_mem_ball x
  ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)

variables {𝕂}

lemma exp_neg (x : 𝔸) : exp (-x) = (exp x)⁻¹ :=
exp_neg_of_mem_ball $ (exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _

lemma exp_zsmul (z : ℤ) (x : 𝔸) : exp (z • x) = (exp x) ^ z :=
begin
  obtain ⟨n, rfl | rfl⟩ := z.eq_coe_or_neg,
  { rw [zpow_coe_nat, coe_nat_zsmul, exp_nsmul] },
  { rw [zpow_neg₀, zpow_coe_nat, neg_smul, exp_neg, coe_nat_zsmul, exp_nsmul] },
end

lemma exp_conj (y : 𝔸) (x : 𝔸) (hy : y ≠ 0) :
  exp (y * x * y⁻¹) = y * exp x * y⁻¹ :=
exp_units_conj (units.mk0 y hy) x

lemma exp_conj' (y : 𝔸) (x : 𝔸)  (hy : y ≠ 0) :
  exp (y⁻¹ * x * y) = y⁻¹ * exp x * y :=
exp_units_conj' (units.mk0 y hy) x

end division_algebra

section comm_algebra

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_comm_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

variables [normed_algebra ℚ 𝔸]

/-- In a commutative Banach-algebra `𝔸` over `𝕂 = ℝ` or `𝕂 = ℂ`,
`exp (x+y) = (exp x) * (exp y)`. -/
lemma exp_add {x y : 𝔸} : exp (x + y) = (exp x) * (exp y) :=
exp_add_of_mem_ball ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)
  ((exp_series_radius_eq_top 𝔸).symm ▸ edist_lt_top _ _)

/-- A version of `exp_sum_of_commute` for a commutative Banach-algebra. -/
lemma exp_sum {ι} (s : finset ι) (f : ι → 𝔸) :
  exp (∑ i in s, f i) = ∏ i in s, exp (f i) :=
begin
  rw [exp_sum_of_commute, finset.noncomm_prod_eq_prod],
  exact λ i hi j hj, commute.all _ _,
end

end comm_algebra

end is_R_or_C

end normed

lemma star_exp {A : Type*} [normed_ring A]
  [star_ring A] [normed_star_group A] [complete_space A] [normed_algebra ℚ A]
  (a : A) : star (exp a) = exp (star a) :=
begin
  rw exp_eq_tsum,
  dsimp only,
  simp_rw [←star_pow, ←star_rat_smul, ←star_add_equiv_apply],
  have := 
  apply tsum_equiv

  have := continuous_linear_map.map_tsum
    (starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A).to_linear_isometry.to_continuous_linear_map
    (exp_series_summable' a),
  dsimp at this,
  convert this,
  funext,
  simp only [star_smul, star_pow, one_div, star_inv', star_rat_smul],
end

#check continuous_linear_map.map_tsum
