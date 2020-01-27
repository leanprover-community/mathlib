/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.normed_space.operator_norm topology.algebra.multilinear

/-!
# Operator norm on the space of continuous multilinear maps

When `f` is a continuous multilinear map in finitely many variables, we define its norm `∥f∥` as the
smallest number such that `∥f m∥ ≤ ∥f∥ * univ.prod (λi, ∥m i∥)` for all `m`.

We show that it is indeed a norm, and prove its basic properties.

## Main results

Let `f` be a multilinear map.
* `exists_bound_of_continuous` asserts that, if `f` is continuous, then there exists `C > 0`
  with `∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)` for all `m`.
* `continuous_of_bound`, conversely, asserts that this bound implies continuity.
* `mk_continuous` constructs the associated continuous multilinear map.

Let `f` be a continuous multilinear map.
* `∥f∥` is its norm, i.e., the smallest number such that `∥f m∥ ≤ ∥f∥ * univ.prod (λi, ∥m i∥)` for
  all `m`.
* `le_op_norm f m` asserts the fundamental inequality `∥f m∥ ≤ ∥f∥ * univ.prod (λi, ∥m i∥)`.
* `norm_image_sub_le_of_bound f m₁ m₂` gives a control of the difference `f m₁ - f m₂` in terms of
  `∥f∥` and `∥m₁ - m₂∥`.

We also register canonical isomorphisms corresponding to singling out a variable.
* `linear_to_multilinear_equiv_multilinear_cont 𝕜 E E₂`: The space of continuous multilinear maps on
  `Π(i : fin (n+1)), E i` is canonically isomorphic to the space of continuous linear maps from
  `E 0` to the space of continuous multilinear maps on `Π(i : fin n), E i.succ `, by separating the
  first variable. We register this isomorphism in
  `linear_to_multilinear_equiv_multilinear_cont 𝕜 E E₂`, as a continuous linear equiv.

## Implementation notes

We mostly follow the API (and the proofs) of `operator_norm.lean`, with the additional complexity
that we should deal with multilinear maps in several variables.
-/

noncomputable theory
open_locale classical
open finset

set_option class.instance_max_depth 45

universes u v w w₁ w₂
variables {𝕜 : Type u} {ι : Type v} {n : ℕ}
{E : fin n.succ → Type w } {E₁ : ι → Type w₁} {E₂ : Type w₂}
[decidable_eq ι] [fintype ι] [nondiscrete_normed_field 𝕜]
[∀i, normed_group (E i)]  [∀i, normed_group (E₁ i)] [normed_group E₂]
[∀i, normed_space 𝕜 (E i)] [∀i, normed_space 𝕜 (E₁ i)] [normed_space 𝕜 E₂]

/-!
### Continuity properties of multilinear maps

We relate continuity of multilinear maps to the inequality ``∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)`, in
both directions. Along the way, we prove useful bounds on the difference `∥f m₁ - f m₂∥`.
-/
namespace multilinear_map

variable (f : multilinear_map 𝕜 E₁ E₂)

/-- If a multilinear map in finitely many variables on normed spaces is continuous, then it
satisfies the inequality `∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)`, for some `C` which can be chosen to be
positive. -/
theorem exists_bound_of_continuous (hf : continuous f) :
  ∃ (C : ℝ), 0 < C ∧ (∀ m, ∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)) :=
begin
  /- The proof only uses the continuity at `0`. Then, given a general point `m`, rescale each of
  its coordinates to bring it to a shell of fixed width around `0`, on which one knows that `f` is
  bounded, and then use the multiplicativity of `f` along each coordinate to deduce the desired
  bound.-/
  have : continuous_at f 0 := continuous_iff_continuous_at.1 hf _,
  rcases metric.tendsto_nhds_nhds.1 this 1 zero_lt_one with ⟨ε, ε_pos, hε⟩,
  let δ := ε/2,
  have δ_pos : δ > 0 := half_pos ε_pos,
  /- On points of size at most `δ`, `f` is bounded (by `1 + ∥f 0∥`). -/
  have H : ∀{a}, ∥a∥ ≤ δ → ∥f a∥ ≤ 1 + ∥f 0∥,
  { assume a ha,
    have : dist (f a) (f 0) ≤ 1,
    { apply le_of_lt (hε _),
      rw [dist_eq_norm, sub_zero],
      exact lt_of_le_of_lt ha (half_lt_self ε_pos) },
    calc ∥f a∥ = dist (f a) 0 : (dist_zero_right _).symm
      ... ≤ dist (f a) (f 0) + dist (f 0) 0 : dist_triangle _ _ _
      ... ≤ 1 + ∥f 0∥ : by { rw dist_zero_right, exact add_le_add_right this _ } },
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  set C := (1 + ∥f 0∥) * univ.prod (λ(i : ι), δ⁻¹ * ∥c∥),
  have C_pos : 0 < C :=
    mul_pos (lt_of_lt_of_le zero_lt_one (by simp))
      (prod_pos (λi hi, mul_pos (inv_pos δ_pos) (lt_of_le_of_lt zero_le_one hc))),
  refine ⟨C, C_pos, λm, _⟩,
  /- Given a general point `m`, rescale each coordinate to bring it to `[δ/∥c∥, δ]` by multiplication
  by a power of a scalar `c` with norm `∥c∥ > 1`.-/
  by_cases h : ∃i, m i = 0,
  { rcases h with ⟨i, hi⟩,
    rw [f.map_coord_zero i hi, _root_.norm_zero],
    exact mul_nonneg'  (le_of_lt C_pos) (prod_nonneg (λi hi, norm_nonneg _)) },
  { push_neg at h,
    have : ∀i, ∃d:𝕜, d ≠ 0 ∧ ∥d • (m i)∥ ≤ δ ∧ (δ/∥c∥ ≤ ∥d • m i∥) ∧ (∥d∥⁻¹ ≤ δ⁻¹ * ∥c∥ * ∥m i∥) :=
      λi, rescale_to_shell hc δ_pos (h i),
    choose d hd using this,
    have A : 0 ≤ 1 + ∥f 0∥ := add_nonneg zero_le_one (norm_nonneg _),
    have B : ∀ (i : ι), i ∈ univ → 0 ≤ ∥d i∥⁻¹ := λi hi, by simp,
    -- use the bound on `f` on the ball of size `δ` to conclude.
    calc
      ∥f m∥ = ∥f (λi, (d i)⁻¹ • (d i • m i))∥ :
        by { unfold_coes, congr, ext i, rw [← mul_smul, inv_mul_cancel (hd i).1, one_smul] }
      ... = ∥univ.prod (λi, (d i)⁻¹) • f (λi, d i • m i)∥ : by rw f.map_smul_univ
      ... = univ.prod (λi, ∥d i∥⁻¹) * ∥f (λi, d i • m i)∥ :
        by { rw [norm_smul, normed_field.norm_prod], congr, ext i, rw normed_field.norm_inv }
      ... ≤ univ.prod (λi, ∥d i∥⁻¹) * (1 + ∥f 0∥) :
        mul_le_mul_of_nonneg_left (H ((pi_norm_le_iff (le_of_lt δ_pos)).2 (λi, (hd i).2.1)))
          (prod_nonneg B)
      ... ≤ univ.prod (λi, δ⁻¹ * ∥c∥ * ∥m i∥) * (1 + ∥f 0∥) :
        mul_le_mul_of_nonneg_right (prod_le_prod B (λi hi, (hd i).2.2.2)) A
      ... = univ.prod (λ(i : ι), δ⁻¹ * ∥c∥) * univ.prod (λi, ∥m i∥) * (1 + ∥f 0∥) :
        by rw prod_mul_distrib
      ... = C * univ.prod (λ (i : ι), ∥m i∥) :
        by rw [mul_comm, ← mul_assoc] }
end

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a precise but hard to use version. See
`norm_image_sub_le_of_bound` for a less precise but more usable version. -/
lemma norm_image_sub_le_of_bound' {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)) (m₁ m₂ : Πi, E₁ i) :
  ∥f m₁ - f m₂∥ ≤
  C * univ.sum (λi, univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)) :=
begin
  have A : ∀(s : finset ι), ∥f m₁ - f (s.piecewise m₂ m₁)∥
    ≤ C * s.sum (λi, univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)),
  { refine finset.induction (by simp) _,
    assume i s his Hrec,
    have I : ∥f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)∥
      ≤ C * univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥),
    { have A : ((insert i s).piecewise m₂ m₁)
            = function.update (s.piecewise m₂ m₁) i (m₂ i) := s.piecewise_insert _ _ _,
      have B : s.piecewise m₂ m₁ = function.update (s.piecewise m₂ m₁) i (m₁ i),
      { ext j,
        by_cases h : j = i,
        { rw h, simp [his] },
        { simp [h] } },
      rw [B, A, ← f.map_sub],
      apply le_trans (H _) (mul_le_mul_of_nonneg_left _ hC),
      refine prod_le_prod (λj hj, norm_nonneg _) (λj hj, _),
      by_cases h : j = i,
      { rw h, simp },
      { by_cases h' : j ∈ s;
        simp [h', h, le_refl] } },
    calc ∥f m₁ - f ((insert i s).piecewise m₂ m₁)∥ ≤
      ∥f m₁ - f (s.piecewise m₂ m₁)∥
        + ∥f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)∥ :
          by { rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm], exact dist_triangle _ _ _ }
      ... ≤ C * s.sum (λi, univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥))
            + C * univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥) :
        add_le_add Hrec I
      ... = C * (insert i s).sum (λi, univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)) :
        by simp [his, left_distrib] },
  convert A univ,
  simp
end

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a usable but not very precise version. See
`norm_image_sub_le_of_bound'` for a more precise but less usable version. -/
lemma norm_image_sub_le_of_bound {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)) (m₁ m₂ : Πi, E₁ i) :
  ∥f m₁ - f m₂∥ ≤ C * (fintype.card ι) * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1) * ∥m₁ - m₂∥ :=
begin
  have A : ∀ (i : ι), univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)
    ≤ ∥m₁ - m₂∥ * (max ∥m₁∥ ∥m₂∥)^(fintype.card ι - 1),
  { assume i,
    calc univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)
    ≤ (univ : finset ι).prod (piecewise (finset.singleton i) (λ j, ∥m₁ - m₂∥) (λ j, max ∥m₁∥ ∥m₂∥)) :
      begin
        apply prod_le_prod,
        { assume j hj, by_cases h : j = i; simp [h, norm_nonneg] },
        { assume j hj,
          by_cases h : j = i,
          { simp [h], exact norm_le_pi_norm (m₁ - m₂) i },
          { simp [h,  max_le_max, norm_le_pi_norm] } }
      end
    ... = ∥m₁ - m₂∥ ^ (card (finset.singleton i))
          * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - card (finset.singleton i)) :
      by { rw prod_piecewise, simp [card_univ_diff] }
    ... = ∥m₁ - m₂∥ * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1) : by simp },
  calc
  ∥f m₁ - f m₂∥
  ≤ C * univ.sum (λi, univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)) :
    f.norm_image_sub_le_of_bound' hC H m₁ m₂
  ... ≤ C * univ.sum (λ (i : ι), ∥m₁ - m₂∥ * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1)) :
    mul_le_mul_of_nonneg_left (sum_le_sum (λi hi, A i)) hC
  ... = C * (fintype.card ι) * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1) * ∥m₁ - m₂∥ :
    by { rw [sum_const, card_univ, add_monoid.smul_eq_mul], ring }
end

/-- If a multilinear map satisfies an inequality `∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)`, then it is
continuous. -/
theorem continuous_of_bound (C : ℝ) (H : ∀ m, ∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)) :
  continuous f :=
begin
  let D := max C 1,
  have D_pos : 0 ≤ D := le_trans zero_le_one (le_max_right _ _),
  replace H : ∀ m, ∥f m∥ ≤ D * univ.prod (λi, ∥m i∥),
  { assume m,
    apply le_trans (H m) (mul_le_mul_of_nonneg_right (le_max_left _ _) _),
    exact prod_nonneg (λ(i : ι) hi, norm_nonneg (m i)) },
  refine continuous_iff_continuous_at.2 (λm, _),
  refine continuous_at_of_locally_lipschitz zero_lt_one (D * (fintype.card ι) * (∥m∥ + 1) ^ (fintype.card ι - 1))
    (λm' h', _),
  rw [dist_eq_norm, dist_eq_norm],
  have : 0 ≤ (max ∥m'∥ ∥m∥), by simp,
  have : ∥m'∥ ≤ 1 + ∥m∥, from calc
    ∥m'∥ = ∥(m' - m) + m∥ : by { congr' 1, abel }
    ... ≤ ∥m' - m∥ + ∥m∥ : norm_add_le _ _
    ... ≤ 1 + ∥m∥ : begin
      apply add_le_add_right,
      rw ← dist_eq_norm,
      exact le_of_lt h'
    end,
  have : (max ∥m'∥ ∥m∥) ≤ ∥m∥ + 1, by simp [zero_le_one, this],
  calc
    ∥f m' - f m∥
    ≤ D * (fintype.card ι) * (max ∥m'∥ ∥m∥) ^ (fintype.card ι - 1) * ∥m' - m∥ :
      f.norm_image_sub_le_of_bound D_pos H m' m
    ... ≤ D * (fintype.card ι) * (∥m∥ + 1) ^ (fintype.card ι - 1) * ∥m' - m∥ :
      by apply_rules [mul_le_mul_of_nonneg_right, mul_le_mul_of_nonneg_left, mul_nonneg',
        norm_nonneg, nat.cast_nonneg, pow_le_pow_of_le_left]
end

/-- Constructing a continuous multilinear map from a multilinear map satisfying a boundedness
condition. -/
def mk_continuous (C : ℝ) (H : ∀ m, ∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)) :
  continuous_multilinear_map 𝕜 E₁ E₂ :=
{ cont := f.continuous_of_bound C H,
  ..f }

end multilinear_map

/-!
### Continuous multilinear maps

We define the norm `∥f∥` of a continuous multilinear map `f` in finitely many variables, as the
smallest number such that `∥f m∥ ≤ ∥f∥ * univ.prod (λi, ∥m i∥)` for all `m`. We show that this
defines a normed space structure on `continuous_multilinear_map 𝕜 E₁ E₂`.
-/
namespace continuous_multilinear_map

variables (c : 𝕜) (f g : continuous_multilinear_map 𝕜 E₁ E₂) (m : Πi, E₁ i)

theorem bound : ∃ (C : ℝ), 0 < C ∧ (∀ m, ∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)) :=
f.to_multilinear_map.exists_bound_of_continuous f.2

open real

/-- The operator norm of a continuous multilinear map is the inf of all its bounds. -/
def op_norm := Inf {c | 0 ≤ (c : ℝ) ∧ ∀ m, ∥f m∥ ≤ c * finset.univ.prod (λi, ∥m i∥)}
instance has_op_norm : has_norm (continuous_multilinear_map 𝕜 E₁ E₂) := ⟨op_norm⟩

-- So that invocations of `real.Inf_le` make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : continuous_multilinear_map 𝕜 E₁ E₂} :
  ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ m, ∥f m∥ ≤ c * finset.univ.prod (λi, ∥m i∥)} :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : continuous_multilinear_map 𝕜 E₁ E₂} :
  bdd_below {c | 0 ≤ c ∧ ∀ m, ∥f m∥ ≤ c * finset.univ.prod (λi, ∥m i∥)} :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ∥f∥ :=
lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm of a continuous multilinear map:
`∥f m∥` is bounded by `∥f∥` times the product of the `∥m i∥`. -/
theorem le_op_norm : ∥f m∥ ≤ ∥f∥ * finset.univ.prod (λi, ∥m i∥) :=
begin
  have A : 0 ≤ finset.univ.prod (λi, ∥m i∥) := prod_nonneg (λj hj, norm_nonneg _),
  by_cases h : finset.univ.prod (λi, ∥m i∥) = 0,
  { rcases prod_eq_zero_iff.1 h with ⟨i, _, hi⟩,
    rw norm_eq_zero at hi,
    have : f m = 0 := f.map_coord_zero i hi,
    rw [this, norm_zero],
    exact mul_nonneg' (op_norm_nonneg f) A },
  { have hlt : 0 < finset.univ.prod (λi, ∥m i∥) := lt_of_le_of_ne A (ne.symm h),
    exact le_mul_of_div_le hlt ((le_Inf _ bounds_nonempty bounds_bdd_below).2
      (λ c ⟨_, hc⟩, div_le_of_le_mul hlt (begin rw mul_comm, apply hc, end))) }
end

lemma ratio_le_op_norm : ∥f m∥ / finset.univ.prod (λi, ∥m i∥) ≤ ∥f∥ :=
begin
  have A : 0 ≤ finset.univ.prod (λi, ∥m i∥) := prod_nonneg (λj hj, norm_nonneg _),
  by_cases h : finset.univ.prod (λi, ∥m i∥) = 0,
  { simp [h, op_norm_nonneg f] },
  { have hlt : 0 < finset.univ.prod (λi, ∥m i∥) := lt_of_le_of_ne A (ne.symm h),
    rw div_le_iff hlt,
    exact le_op_norm f m }
end

/-- The image of the unit ball under a continuous multilinear map is bounded. -/
lemma unit_le_op_norm (h : ∥m∥ ≤ 1) : ∥f m∥ ≤ ∥f∥ :=
calc
  ∥f m∥ ≤ ∥f∥ * finset.univ.prod (λi, ∥m i∥) : f.le_op_norm m
  ... ≤ ∥f∥ * finset.univ.prod (λ (i : ι), 1) :
    mul_le_mul_of_nonneg_left (prod_le_prod (λi hi, norm_nonneg _) (λi hi, le_trans (norm_le_pi_norm _ _) h))
      (op_norm_nonneg f)
  ... = ∥f∥ : by simp

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
lemma op_norm_le_bound {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ m, ∥f m∥ ≤ M * finset.univ.prod (λi, ∥m i∥)) :
  ∥f∥ ≤ M :=
Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
Inf_le _ bounds_bdd_below
  ⟨add_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x, by { rw add_mul,
    exact norm_add_le_of_le (le_op_norm _ _) (le_op_norm _ _) }⟩

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
begin
  split,
  { assume h,
    ext m,
    simpa [h, (norm_le_zero_iff _).symm] using f.le_op_norm m },
  { assume h,
    apply le_antisymm (op_norm_le_bound f (le_refl _) (λm, _)) (op_norm_nonneg _),
    rw h,
    simp }
end

@[simp] lemma norm_zero : ∥(0 : continuous_multilinear_map 𝕜 E₁ E₂)∥ = 0 :=
by rw op_norm_zero_iff

/-- The operator norm is homogeneous. -/
lemma op_norm_smul : ∥c • f∥ = ∥c∥ * ∥f∥ :=
le_antisymm
  (Inf_le _ bounds_bdd_below
    ⟨mul_nonneg (norm_nonneg _) (op_norm_nonneg _), λ _,
    begin
      erw [norm_smul, mul_assoc],
      exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
    end⟩)
  (lb_le_Inf _ bounds_nonempty (λ _ ⟨hn, hc⟩,
    (or.elim (lt_or_eq_of_le (norm_nonneg c))
      (λ hlt,
        begin
          rw mul_comm,
          exact mul_le_of_le_div hlt (Inf_le _ bounds_bdd_below
          ⟨div_nonneg hn hlt, λ _,
          (by { rw div_mul_eq_mul_div, exact le_div_of_mul_le hlt
          (by { rw [ mul_comm, ←norm_smul ], exact hc _ }) })⟩)
        end)
      (λ heq, by { rw [←heq, zero_mul], exact hn }))))

lemma op_norm_neg : ∥-f∥ = ∥f∥ := calc
  ∥-f∥ = ∥(-1:𝕜) • f∥ : by rw neg_one_smul
  ... = ∥(-1:𝕜)∥ * ∥f∥ : by rw op_norm_smul
  ... = ∥f∥ : by simp

/-- Continuous multilinear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_group : normed_group (continuous_multilinear_map 𝕜 E₁ E₂) :=
normed_group.of_core _ ⟨op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

instance to_normed_space : normed_space 𝕜 (continuous_multilinear_map 𝕜 E₁ E₂) :=
⟨op_norm_smul⟩

/-- The difference `f m₁ - f m₂` is controlled in terms of `∥f∥` and `∥m₁ - m₂∥`, precise version.
For a less precise but more usable version, see `norm_image_sub_le_of_bound`. -/
lemma norm_image_sub_le_of_bound' (m₁ m₂ : Πi, E₁ i) :
  ∥f m₁ - f m₂∥ ≤
  ∥f∥ * univ.sum (λi, univ.prod (λj, if j = i then ∥m₁ i - m₂ i∥ else max ∥m₁ j∥ ∥m₂ j∥)) :=
f.to_multilinear_map.norm_image_sub_le_of_bound' (norm_nonneg _) f.le_op_norm _ _

/-- The difference `f m₁ - f m₂` is controlled in terms of `∥f∥` and `∥m₁ - m₂∥`, less precise
version. For a more precise but less usable version, see `norm_image_sub_le_of_bound'`. -/
lemma norm_image_sub_le_of_bound (m₁ m₂ : Πi, E₁ i) :
  ∥f m₁ - f m₂∥ ≤ ∥f∥ * (fintype.card ι) * (max ∥m₁∥ ∥m₂∥) ^ (fintype.card ι - 1) * ∥m₁ - m₂∥ :=
f.to_multilinear_map.norm_image_sub_le_of_bound (norm_nonneg _) f.le_op_norm _ _

end continuous_multilinear_map

lemma multilinear_map.mk_continuous_norm_le (f : multilinear_map 𝕜 E₁ E₂) {C : ℝ} (hC : 0 ≤ C)
  (H : ∀ m, ∥f m∥ ≤ C * univ.prod (λi, ∥m i∥)) :
  ∥f.mk_continuous C H∥ ≤ C :=
continuous_multilinear_map.op_norm_le_bound _ hC (λm, H m)

section isomorphisms

set_option class.instance_max_depth 200
open fin function

lemma continuous_linear_map.norm_image_tail_le
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) (m : Πi, E i) :
  ∥f (m 0) (tail m)∥ ≤ ∥f∥ * univ.prod (λi, ∥m i∥) :=
calc
  ∥f (m 0) (tail m)∥ ≤ ∥f (m 0)∥ * univ.prod (λi, ∥(tail m) i∥) : (f (m 0)).le_op_norm _
  ... ≤ (∥f∥ * ∥m 0∥) * univ.prod (λi, ∥(tail m) i∥) :
    mul_le_mul_of_nonneg_right (f.le_op_norm _) (prod_nonneg (λi hi, norm_nonneg _))
  ... = ∥f∥ * (∥m 0∥ * univ.prod (λi, ∥(tail m) i∥)) : by ring
  ... = ∥f∥ * univ.prod (λi, ∥m i∥) : by { rw prod_univ_succ, refl }

lemma continuous_multilinear_map.norm_image_cons_le
  (f : continuous_multilinear_map 𝕜 E E₂) (x : E 0) (m : Π(i : fin n), E i.succ) :
  ∥f (cons x m)∥ ≤ ∥f∥ * ∥x∥ * univ.prod (λi, ∥m i∥) :=
calc
  ∥f (cons x m)∥ ≤ ∥f∥ * univ.prod (λ(i : fin n.succ), ∥cons x m i∥) : f.le_op_norm _
  ... = (∥f∥ * ∥x∥) * univ.prod (λi, ∥m i∥) :
    by { rw prod_univ_succ, simp [mul_assoc] }

/-- Given a continuous linear map `f` from `E 0` to continuous multilinear maps on `n` variables,
construct the corresponding continuous multilinear map on `n+1` variables obtained by concatenating
the variables, given by `f (m 0) (tail m)`-/
def continuous_linear_map.merge_variables
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) :
  continuous_multilinear_map 𝕜 E E₂ :=
(linear_to_multilinear_equiv_multilinear 𝕜 E E₂
    (continuous_multilinear_map.to_multilinear_map_linear.comp f.to_linear_map)).mk_continuous
      (∥f∥) (λm, continuous_linear_map.norm_image_tail_le f m)

@[simp] lemma continuous_linear_map.merge_variables_apply
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂))
  (m : Πi, E i) :
  f.merge_variables m = f (m 0) (tail m) := rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous multilinear maps in `n` variables, given by `f (cons x m)`.
-/
def continuous_multilinear_map.split_variables
  (f : continuous_multilinear_map 𝕜 E E₂) :
  E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂) :=
linear_map.mk_continuous
{ -- define a linear map into `n` continuous multilinear maps from an `n+1` continuous multilinear map
  to_fun := λx,
    ((linear_to_multilinear_equiv_multilinear 𝕜 E E₂).symm
      f.to_multilinear_map x).mk_continuous (∥f∥ * ∥x∥) (f.norm_image_cons_le x),
  add    := λx y, by { ext m, exact f.cons_add m x y },
  smul   := λc x, by { ext m, exact f.cons_smul m c x } }
  -- then register its continuity thanks to its boundedness properties.
(∥f∥) (λx, multilinear_map.mk_continuous_norm_le _ (mul_nonneg' (norm_nonneg _) (norm_nonneg _)) _)

@[simp] lemma continuous_multilinear_map.split_variables_apply
  (f : continuous_multilinear_map 𝕜 E E₂) (x : E 0) (m : Π(i : fin n), E i.succ) :
  f.split_variables x m = f (cons x m) := rfl

lemma continuous_multilinear_map.split_variables_norm_aux (f : continuous_multilinear_map 𝕜 E E₂) :
  ∥f.split_variables∥ ≤ ∥f∥ :=
begin
  apply linear_map.mk_continuous_norm_le,
end

lemma continuous_linear_map.merge_variables_norm_aux
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) :
  ∥f.merge_variables∥ ≤ ∥f∥ :=
multilinear_map.mk_continuous_norm_le _ (norm_nonneg _) _,

#exit

@[simp] lemma continuous_linear_map.split_variables_merge_variables
  (f : E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) :
  f.merge_variables.split_variables = f :=
begin
  ext m x,
  simp only [tail_cons, continuous_linear_map.merge_variables_apply, continuous_multilinear_map.split_variables_apply],
  rw cons_zero
end

@[simp] lemma continuous_multilinear_map.merge_variables_split_variables
  (f : continuous_multilinear_map 𝕜 E E₂) :
  f.split_variables.merge_variables = f :=
by { ext m, simp }

variables (𝕜 E E₂)

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : fin n), E i.succ `, by separating the first variable. We register this isomorphism as a
linear isomorphism in `linear_to_multilinear_equiv_multilinear_cont_aux 𝕜 E E₂`.
The algebraic version (without continuity assumption on the maps) is
`linear_to_multilinear_equiv_multilinear 𝕜 E E₂`, and the topological isomorphism (registering
additionally that the isomorphism is continuous) is
`linear_to_multilinear_equiv_multilinear_cont 𝕜 E E₂`.-/
def linear_to_multilinear_equiv_multilinear_cont_aux :
  (E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) ≃ₗ[𝕜]
  (continuous_multilinear_map 𝕜 E E₂) :=
{ to_fun  := continuous_linear_map.merge_variables,
  add     := λf₁ f₂, by { ext m, refl },
  smul    := λc f, by { ext m, refl },
  inv_fun := continuous_multilinear_map.split_variables,
  left_inv := continuous_linear_map.split_variables_merge_variables,
  right_inv := continuous_multilinear_map.merge_variables_split_variables }

/-- The space of continuous multilinear maps on `Π(i : fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`Π(i : fin n), E i.succ `, by separating the first variable. We register this isomorphism in
`linear_to_multilinear_equiv_multilinear_cont 𝕜 E E₂`. We build on the algebraic version (without
topology) given in `linear_to_multilinear_equiv_multilinear 𝕜 E E₂`. -/
def linear_to_multilinear_equiv_multilinear_cont :
  (E 0 →L[𝕜] (continuous_multilinear_map 𝕜 (λ(i : fin n), E i.succ) E₂)) ≃L[𝕜]
  (continuous_multilinear_map 𝕜 E E₂) :=
{ continuous_to_fun := begin
    refine (linear_to_multilinear_equiv_multilinear_cont_aux 𝕜 E E₂).to_linear_map.continuous_of_bound (1 : ℝ) (λf, _),
    rw one_mul,
    apply continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (λm, _),
    apply continuous_multilinear_map.norm_image_tail_le f
  end,
  continuous_inv_fun := begin
    refine (linear_to_multilinear_equiv_multilinear_cont_aux 𝕜 E E₂).symm.to_linear_map.continuous_of_bound (1 : ℝ) (λf, _),
    rw one_mul,
    apply continuous_linear_map.op_norm_le_bound _ (norm_nonneg _ ) (λx, _),
    apply continuous_multilinear_map.op_norm_le_bound _
      ((mul_nonneg' (norm_nonneg _) (norm_nonneg _))) (λm, _),
    exact f.norm_image_cons_le x m
  end,
  .. linear_to_multilinear_equiv_multilinear_cont_aux 𝕜 E E₂ }

end isomorphisms
