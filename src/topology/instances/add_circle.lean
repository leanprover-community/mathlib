/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import data.nat.totient
import algebra.ring.add_aut
import group_theory.divisible
import group_theory.order_of_element
import ring_theory.int.basic
import algebra.order.floor
import algebra.order.to_interval_mod
import topology.instances.real

/-!
# The additive circle

We define the additive circle `add_circle p` as the quotient `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`.

See also `circle` and `real.angle`.  For the normed group structure on `add_circle`, see
`add_circle.normed_add_comm_group` in a later file.

## Main definitions and results:

 * `add_circle`: the additive circle `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`
 * `unit_add_circle`: the special case `ℝ ⧸ ℤ`
 * `add_circle.equiv_add_circle`: the rescaling equivalence `add_circle p ≃+ add_circle q`
 * `add_circle.equiv_Ico`: the natural equivalence `add_circle p ≃ Ico a (a + p)`
 * `add_circle.add_order_of_div_of_gcd_eq_one`: rational points have finite order
 * `add_circle.exists_gcd_eq_one_of_is_of_fin_add_order`: finite-order points are rational
 * `add_circle.homeo_Icc_quot`: the natural topological equivalence between `add_circle p` and
   `Icc a (a + p)` with its endpoints identified.
 * `add_circle.lift_Ico_continuous`: if `f : ℝ → B` is continuous, and `f a = f (a + p)` for
   some `a`, then there is a continuous function `add_circle p → B` which agrees with `f` on
   `Icc a (a + p)`.

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `add_circle (1 : ℚ)`, and so we set things up more generally.

## TODO

 * Link with periodicity
 * Lie group structure
 * Exponential equivalence to `circle`

-/

noncomputable theory

open set function add_subgroup topological_space

variables {𝕜 : Type*} {B : Type*}

/-- The "additive circle": `𝕜 ⧸ (ℤ ∙ p)`. See also `circle` and `real.angle`. -/
@[derive [add_comm_group, topological_space, topological_add_group, inhabited, has_coe_t 𝕜],
  nolint unused_arguments]
def add_circle [linear_ordered_add_comm_group 𝕜] [topological_space 𝕜] [order_topology 𝕜] (p : 𝕜) :=
𝕜 ⧸ zmultiples p

namespace add_circle

section linear_ordered_add_comm_group
variables [linear_ordered_add_comm_group 𝕜] [topological_space 𝕜] [order_topology 𝕜] (p : 𝕜)

lemma coe_nsmul {n : ℕ} {x : 𝕜} : (↑(n • x) : add_circle p) = n • (x : add_circle p) := rfl

lemma coe_zsmul {n : ℤ} {x : 𝕜} : (↑(n • x) : add_circle p) = n • (x : add_circle p) := rfl

lemma coe_add (x y : 𝕜) : (↑(x + y) : add_circle p) = (x : add_circle p) + (y : add_circle p) := rfl

lemma coe_sub (x y : 𝕜) : (↑(x - y) : add_circle p) = (x : add_circle p) - (y : add_circle p) := rfl

lemma coe_neg {x : 𝕜} : (↑(-x) : add_circle p) = -(x : add_circle p) := rfl

lemma coe_eq_zero_iff {x : 𝕜} : (x : add_circle p) = 0 ↔ ∃ (n : ℤ), n • p = x :=
by simp [add_subgroup.mem_zmultiples_iff]

lemma coe_eq_zero_of_pos_iff (hp : 0 < p) {x : 𝕜} (hx : 0 < x) :
  (x : add_circle p) = 0 ↔ ∃ (n : ℕ), n • p = x :=
begin
  rw coe_eq_zero_iff,
  split;
  rintros ⟨n, rfl⟩,
  { replace hx : 0 < n,
    { contrapose! hx,
      simpa only [←neg_nonneg, ←zsmul_neg, zsmul_neg'] using zsmul_nonneg hp.le (neg_nonneg.2 hx) },
    exact ⟨n.to_nat, by rw [← coe_nat_zsmul, int.to_nat_of_nonneg hx.le]⟩, },
  { exact ⟨(n : ℤ), by simp⟩, },
end

@[simp] lemma coe_add_period (x : 𝕜) : (((x + p) : 𝕜) : add_circle p) = x :=
begin
  rw [quotient_add_group.coe_add, ←eq_sub_iff_add_eq', sub_self, quotient_add_group.eq_zero_iff],
  exact mem_zmultiples p,
end

@[continuity, nolint unused_arguments] protected lemma continuous_mk' :
  continuous (quotient_add_group.mk' (zmultiples p) : 𝕜 → add_circle p) :=
continuous_coinduced_rng

variables [hp : fact (0 < p)]
include hp

variables (a : 𝕜) [archimedean 𝕜]

/-- The natural equivalence between `add_circle p` and the half-open interval `[a, a + p)`. -/
def equiv_Ico : add_circle p ≃ Ico a (a + p) := quotient_add_group.equiv_Ico_mod a hp.out

/-- Given a function on `[a, a + p)`, lift it to `add_circle p`. -/
def lift_Ico (f : 𝕜 → B) : add_circle p → B := restrict _ f ∘ add_circle.equiv_Ico p a

variables {p a}

lemma coe_eq_coe_iff_of_mem_Ico {x y : 𝕜}
  (hx : x ∈ Ico a (a + p)) (hy : y ∈ Ico a (a + p)) : (x : add_circle p) = y ↔ x = y :=
begin
  refine ⟨λ h, _, by tauto⟩,
  suffices : (⟨x, hx⟩ : Ico a (a + p)) = ⟨y, hy⟩, by exact subtype.mk.inj this,
  apply_fun equiv_Ico p a at h,
  rw [←(equiv_Ico p a).right_inv ⟨x, hx⟩, ←(equiv_Ico p a).right_inv ⟨y, hy⟩],
  exact h
end

lemma lift_Ico_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico a (a + p)) : lift_Ico p a f ↑x = f x :=
begin
  have : (equiv_Ico p a) x = ⟨x, hx⟩,
  { rw equiv.apply_eq_iff_eq_symm_apply,
    refl, },
  rw [lift_Ico, comp_apply, this],
  refl,
end

variables (p a)

@[continuity] lemma continuous_equiv_Ico_symm : continuous (equiv_Ico p a).symm :=
continuous_quotient_mk.comp continuous_subtype_coe

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → add_circle p` is
the entire space. -/
@[simp] lemma coe_image_Ico_eq : (coe : 𝕜 → add_circle p) '' Ico a (a + p) = univ :=
by { rw image_eq_range, exact (equiv_Ico p a).symm.range_eq_univ }

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp] lemma coe_image_Icc_eq : (coe : 𝕜 → add_circle p) '' Icc a (a + p) = univ :=
eq_top_mono (image_subset _ Ico_subset_Icc_self) $ coe_image_Ico_eq _ _

end linear_ordered_add_comm_group

section linear_ordered_field
variables [linear_ordered_field 𝕜] [topological_space 𝕜] [order_topology 𝕜] (p q : 𝕜)

/-- The rescaling equivalence between additive circles with different periods. -/
def equiv_add_circle (hp : p ≠ 0) (hq : q ≠ 0) : add_circle p ≃+ add_circle q :=
quotient_add_group.congr _ _ (add_aut.mul_right $ (units.mk0 p hp)⁻¹ * units.mk0 q hq) $
  by rw [add_monoid_hom.map_zmultiples, add_monoid_hom.coe_coe, add_aut.mul_right_apply,
    units.coe_mul, units.coe_mk0, units.coe_inv, units.coe_mk0, mul_inv_cancel_left₀ hp]

@[simp] lemma equiv_add_circle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
  equiv_add_circle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
rfl

@[simp] lemma equiv_add_circle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
  (equiv_add_circle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
rfl

variables [hp : fact (0 < p)]
include hp

section floor_ring

variables [floor_ring 𝕜]

@[simp] lemma coe_equiv_Ico_mk_apply (x : 𝕜) :
  (equiv_Ico p 0 $ quotient_add_group.mk x : 𝕜) = int.fract (x / p) * p :=
to_Ico_mod_eq_fract_mul _ x

instance : divisible_by (add_circle p) ℤ :=
{ div := λ x n, (↑(((n : 𝕜)⁻¹) * (equiv_Ico p 0 x : 𝕜)) : add_circle p),
  div_zero := λ x,
    by simp only [algebra_map.coe_zero, quotient_add_group.coe_zero, inv_zero, zero_mul],
  div_cancel := λ n x hn,
  begin
    replace hn : (n : 𝕜) ≠ 0, { norm_cast, assumption, },
    change n • quotient_add_group.mk' _ ((n : 𝕜)⁻¹ * ↑(equiv_Ico p 0 x)) = x,
    rw [← map_zsmul, ← smul_mul_assoc, zsmul_eq_mul, mul_inv_cancel hn, one_mul],
    exact (equiv_Ico p 0).symm_apply_apply x,
  end, }

end floor_ring

section finite_order_points

variables {p}

lemma add_order_of_one_div {n : ℕ} (hn : 0 < n) : add_order_of ((p / n : 𝕜) : add_circle p) = n :=
begin

end

lemma add_order_of_div_of_gcd_eq_one {m n : ℕ} (hn : 0 < n) (h : gcd m n = 1) :
  add_order_of (↑(↑m / ↑n * p) : add_circle p) = n :=
begin
  rcases m.eq_zero_or_pos with rfl | hm, { rw [gcd_zero_left, normalize_eq] at h, simp [h], },
  set x : add_circle p := ↑(↑m / ↑n * p),
  have hn₀ : (n : 𝕜) ≠ 0, { norm_cast, exact ne_of_gt hn, },
  have hnx : n • x = 0,
  { rw [← coe_nsmul, nsmul_eq_mul, ← mul_assoc, mul_div, mul_div_cancel_left _ hn₀,
      ← nsmul_eq_mul, quotient_add_group.eq_zero_iff],
    exact nsmul_mem_zmultiples p m, },
  apply nat.dvd_antisymm (add_order_of_dvd_of_nsmul_eq_zero hnx),
  suffices : ∃ (z : ℕ), z * n = (add_order_of x) * m,
  { obtain ⟨z, hz⟩ := this,
    simpa only [h, mul_one, gcd_comm n] using dvd_mul_gcd_of_dvd_mul (dvd.intro_left z hz), },
  replace hp := hp.out,
  have : 0 < add_order_of x • (↑m / ↑n * p) := smul_pos
    (add_order_of_pos' $ (is_of_fin_add_order_iff_nsmul_eq_zero _).2 ⟨n, hn, hnx⟩) (by positivity),
  obtain ⟨z, hz⟩ := (coe_eq_zero_of_pos_iff p hp this).mp (add_order_of_nsmul_eq_zero x),
  rw [← smul_mul_assoc, nsmul_eq_mul, nsmul_eq_mul, mul_left_inj' hp.ne.symm, mul_div,
    eq_div_iff hn₀] at hz,
  norm_cast at hz,
  exact ⟨z, hz⟩,
end

lemma add_order_of_div_of_gcd_eq_one' {m : ℤ} {n : ℕ} (hn : 0 < n) (h : gcd m.nat_abs n = 1) :
  add_order_of (↑(↑m / ↑n * p) : add_circle p) = n :=
begin
  induction m,
  { simp only [int.of_nat_eq_coe, int.cast_coe_nat, int.nat_abs_of_nat] at h ⊢,
    exact add_order_of_div_of_gcd_eq_one hn h, },
  { simp only [int.cast_neg_succ_of_nat, neg_div, neg_mul, coe_neg, order_of_neg],
    exact add_order_of_div_of_gcd_eq_one hn h, },
end

lemma add_order_of_coe_rat {q : ℚ} : add_order_of (↑(↑q * p) : add_circle p) = q.denom :=
begin
  have : (↑(q.denom : ℤ) : 𝕜) ≠ 0, { norm_cast, exact q.pos.ne.symm, },
  rw [← @rat.num_denom q, rat.cast_mk_of_ne_zero _ _ this, int.cast_coe_nat, rat.num_denom,
    add_order_of_div_of_gcd_eq_one' q.pos q.cop],
  apply_instance,
end

variables (p)

lemma gcd_mul_add_order_of_div_eq {n : ℕ} (m : ℕ) (hn : 0 < n) :
  gcd m n * add_order_of (↑(↑m / ↑n * p) : add_circle p) = n :=
begin
  let n' := n / gcd m n,
  let m' := m / gcd m n,
  have h₀ : 0 < gcd m n,
  { rw zero_lt_iff at hn ⊢, contrapose! hn, exact ((gcd_eq_zero_iff m n).mp hn).2, },
  have hk' : 0 < n' := nat.div_pos (nat.le_of_dvd hn $ gcd_dvd_right m n) h₀,
  have hgcd : gcd m' n' = 1 := nat.coprime_div_gcd_div_gcd h₀,
  simp only [mul_left_inj' hp.out.ne.symm,
    ← nat.cast_div_div_div_cancel_right (gcd_dvd_right m n) (gcd_dvd_left m n),
    add_order_of_div_of_gcd_eq_one hk' hgcd, mul_comm _ n', nat.div_mul_cancel (gcd_dvd_right m n)],
end

variables {p} [floor_ring 𝕜]

lemma exists_gcd_eq_one_of_is_of_fin_add_order {u : add_circle p} (h : is_of_fin_add_order u) :
  ∃ m, gcd m (add_order_of u) = 1 ∧
       m < (add_order_of u) ∧
       ↑(((m : 𝕜) / add_order_of u) * p) = u :=
begin
  rcases eq_or_ne u 0 with rfl | hu, { exact ⟨0, by simp⟩, },
  set n := add_order_of u,
  change ∃ m, gcd m n = 1 ∧ m < n ∧ ↑((↑m / ↑n) * p) = u,
  have hn : 0 < n := add_order_of_pos' h,
  have hn₀ : (n : 𝕜) ≠ 0, { norm_cast, exact ne_of_gt hn, },
  let x := (equiv_Ico p 0 u : 𝕜),
  have hxu : (x : add_circle p) = u := (equiv_Ico p 0).symm_apply_apply u,
  have hx₀ : 0 < (add_order_of (x : add_circle p)), { rw ← hxu at h, exact add_order_of_pos' h, },
  have hx₁ : 0 < x,
  { refine lt_of_le_of_ne (equiv_Ico p 0 u).2.1 _,
    contrapose! hu,
    rw [← hxu, ← hu, quotient_add_group.coe_zero], },
  obtain ⟨m, hm : m • p = add_order_of ↑x • x⟩ := (coe_eq_zero_of_pos_iff p hp.out
    (by positivity)).mp (add_order_of_nsmul_eq_zero (x : add_circle p)),
  replace hm : ↑m * p = ↑n * x, { simpa only [hxu, nsmul_eq_mul] using hm, },
  have hux : ↑(↑m / ↑n * p) = u,
  { rw [← hxu, ← mul_div_right_comm, hm, mul_comm _ x, mul_div_cancel x hn₀], },
  refine ⟨m, (_ : gcd m n = 1), (_ : m < n), hux⟩,
  { have := gcd_mul_add_order_of_div_eq p m hn,
    rwa [hux, nat.mul_left_eq_self_iff hn] at this, },
  { have : n • x < n • p := smul_lt_smul_of_pos _ hn,
    rwa [nsmul_eq_mul, nsmul_eq_mul, ← hm, mul_lt_mul_right hp.out, nat.cast_lt] at this,
    simpa [zero_add] using (equiv_Ico p 0 u).2.2, },
end

lemma add_order_of_eq_pos_iff {u : add_circle p} {n : ℕ} (h : 0 < n) :
  add_order_of u = n ↔ ∃ m < n, gcd m n = 1 ∧ ↑(↑m / ↑n * p) = u :=
begin
  refine ⟨λ hu, _, _⟩,
  { rw ← hu at h,
    obtain ⟨m, h₀, h₁, h₂⟩ := exists_gcd_eq_one_of_is_of_fin_add_order (add_order_of_pos_iff.mp h),
    refine ⟨m, _, _, _⟩;
    rwa ← hu, },
  { rintros ⟨m, h₀, h₁, rfl⟩,
    exact add_order_of_div_of_gcd_eq_one h h₁, },
end

variables (p)

/-- The natural bijection between points of order `n` and natural numbers less than and coprime to
`n`. The inverse of the map sends `m ↦ (m/n * p : add_circle p)` where `m` is coprime to `n` and
satisfies `0 ≤ m < n`. -/
def set_add_order_of_equiv {n : ℕ} (hn : 0 < n) :
  {u : add_circle p | add_order_of u = n} ≃ {m | m < n ∧ gcd m n = 1} :=
{ to_fun := λ u, by
  { let h := (add_order_of_eq_pos_iff hn).mp u.property,
    exact ⟨classical.some h, classical.some (classical.some_spec h),
      (classical.some_spec (classical.some_spec h)).1⟩, },
  inv_fun := λ m, ⟨↑((m : 𝕜) / n * p), add_order_of_div_of_gcd_eq_one hn (m.property.2)⟩,
  left_inv := λ u, subtype.ext
    (classical.some_spec (classical.some_spec $ (add_order_of_eq_pos_iff hn).mp u.2)).2,
  right_inv :=
  begin
    rintros ⟨m, hm₁, hm₂⟩,
    let u : {u : add_circle p | add_order_of u = n} :=
      ⟨↑((m : 𝕜) / n * p), add_order_of_div_of_gcd_eq_one hn hm₂⟩,
    let h := (add_order_of_eq_pos_iff hn).mp u.property,
    ext,
    let m' := classical.some h,
    change m' = m,
    obtain ⟨h₁ : m' < n, h₂ : gcd m' n = 1, h₃ : quotient_add_group.mk ((m' : 𝕜) / n * p) =
      quotient_add_group.mk ((m : 𝕜) / n * p)⟩ := classical.some_spec h,
    replace h₃ := congr_arg (coe : Ico 0 (0 + p) → 𝕜) (congr_arg (equiv_Ico p 0) h₃),
    simpa only [coe_equiv_Ico_mk_apply, mul_left_inj' hp.out.ne', mul_div_cancel _ hp.out.ne',
      int.fract_div_nat_cast_eq_div_nat_cast_mod,
      div_left_inj' (nat.cast_ne_zero.mpr hn.ne' : (n : 𝕜) ≠ 0), nat.cast_inj,
      (nat.mod_eq_iff_lt hn.ne').mpr hm₁, (nat.mod_eq_iff_lt hn.ne').mpr h₁] using h₃,
  end }

@[simp] lemma card_add_order_of_eq_totient {n : ℕ} :
  nat.card {u : add_circle p // add_order_of u = n} = n.totient :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp only [nat.totient_zero, add_order_of_eq_zero_iff],
    rcases em (∃ (u : add_circle p), ¬ is_of_fin_add_order u) with ⟨u, hu⟩ | h,
    { haveI : infinite {u : add_circle p // ¬is_of_fin_add_order u},
      { erw infinite_coe_iff,
        exact infinite_not_is_of_fin_add_order hu, },
      exact nat.card_eq_zero_of_infinite, },
    { haveI : is_empty {u : add_circle p // ¬is_of_fin_add_order u}, { simpa using h, },
      exact nat.card_of_is_empty, }, },
  { rw [← coe_set_of, nat.card_congr (set_add_order_of_equiv p hn),
      n.totient_eq_card_lt_and_coprime],
    simpa only [@nat.coprime_comm _ n], },
end

lemma finite_set_of_add_order_eq {n : ℕ} (hn : 0 < n) :
  {u : add_circle p | add_order_of u = n}.finite :=
finite_coe_iff.mp $ nat.finite_of_card_ne_zero $ by simpa only [coe_set_of,
  card_add_order_of_eq_totient p] using (nat.totient_pos hn).ne'

end finite_order_points

end linear_ordered_field

variables (p : ℝ)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is compact. -/
instance compact_space [fact (0 < p)] : compact_space $ add_circle p :=
begin
  rw [← is_compact_univ_iff, ← coe_image_Icc_eq p 0],
  exact is_compact_Icc.image (add_circle.continuous_mk' p),
end

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples p` (the multiples of
`p:ℝ`) is properly discontinuous. -/
instance : properly_discontinuous_vadd (zmultiples p).opposite ℝ :=
(zmultiples p).properly_discontinuous_vadd_opposite_of_tendsto_cofinite
  (add_subgroup.tendsto_zmultiples_subtype_cofinite p)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is Hausdorff. -/
instance : t2_space (add_circle p) := t2_space_of_properly_discontinuous_vadd_of_t2_space

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is normal. -/
instance [fact (0 < p)] : normal_space (add_circle p) := normal_of_compact_t2

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is second-countable. -/
instance : second_countable_topology (add_circle p) := quotient_add_group.second_countable_topology

end add_circle

private lemma fact_zero_lt_one : fact ((0:ℝ) < 1) := ⟨zero_lt_one⟩
local attribute [instance] fact_zero_lt_one

/-- The unit circle `ℝ ⧸ ℤ`. -/
@[derive [compact_space, normal_space, second_countable_topology]]
abbreviation unit_add_circle := add_circle (1 : ℝ)

section identify_Icc_ends
/-! This section proves that for any `a`, the natural map from `[a, a + p] ⊂ ℝ` to `add_circle p`
gives an identification of `add_circle p`, as a topological space, with the quotient of `[a, a + p]`
by the equivalence relation identifying the endpoints. -/

namespace add_circle

section linear_ordered_add_comm_group

variables [linear_ordered_add_comm_group 𝕜] [topological_space 𝕜] [order_topology 𝕜]
(p a : 𝕜) [hp : fact (0 < p)]

include hp

local notation `𝕋` := add_circle p

/-- The relation identifying the endpoints of `Icc a (a + p)`. -/
inductive endpoint_ident : Icc a (a + p) → Icc a (a + p) → Prop
| mk : endpoint_ident
    ⟨a,      left_mem_Icc.mpr $ le_add_of_nonneg_right hp.out.le⟩
    ⟨a + p, right_mem_Icc.mpr $ le_add_of_nonneg_right hp.out.le⟩

variables [archimedean 𝕜]

/-- The equivalence between `add_circle p` and the quotient of `[a, a + p]` by the relation
identifying the endpoints. -/
def equiv_Icc_quot : 𝕋 ≃ quot (endpoint_ident p a) :=
{ to_fun := λ x, quot.mk _ $ subtype.map id Ico_subset_Icc_self (equiv_Ico _ _ x),
  inv_fun := λ x, quot.lift_on x coe $ by { rintro _ _ ⟨_⟩, exact (coe_add_period p a).symm },
  left_inv := (equiv_Ico p a).symm_apply_apply,
  right_inv := quot.ind $ by
  { rintro ⟨x, hx⟩,
    have := _,
    rcases ne_or_eq x (a + p) with h | rfl,
    { revert x, exact this },
    { rw ← quot.sound endpoint_ident.mk, exact this _ _ (lt_add_of_pos_right a hp.out).ne },
    intros x hx h,
    congr, ext1,
    apply congr_arg subtype.val ((equiv_Ico p a).right_inv ⟨x, hx.1, hx.2.lt_of_ne h⟩) } }

end linear_ordered_add_comm_group

section real

variables {p a : ℝ} [hp : fact (0 < p)]
include hp

local notation `𝕋` := add_circle p

/- doesn't work if inlined in `homeo_of_equiv_compact_to_t2` -- why? -/
private lemma continuous_equiv_Icc_quot_symm : continuous (equiv_Icc_quot p a).symm :=
continuous_quot_lift _ $ (add_circle.continuous_mk' p).comp continuous_subtype_coe

/-- The natural map from `[a, a + p] ⊂ ℝ` with endpoints identified to `ℝ / ℤ • p`, as a
homeomorphism of topological spaces. -/
def homeo_Icc_quot : 𝕋  ≃ₜ quot (endpoint_ident p a) :=
(continuous.homeo_of_equiv_compact_to_t2 continuous_equiv_Icc_quot_symm).symm

/-! We now show that a continuous function on `[a, a + p]` satisfying `f a = f (a + p)` is
the pullback of a continuous function on `unit_add_circle`. -/

lemma eq_of_end_ident {f : ℝ → B} (hf : f a = f (a + p)) (x y : Icc a (a + p)) :
  endpoint_ident p a x y → f x = f y := by { rintro ⟨_⟩, exact hf }

lemma lift_Ico_eq_lift_Icc {f : ℝ → B} (h : f a = f (a + p)) :
  lift_Ico p a f = (quot.lift (restrict (Icc a $ a + p) f) $ eq_of_end_ident h)
  ∘ equiv_Icc_quot p a :=
funext (λ x, by refl)

lemma lift_Ico_continuous [topological_space B] {f : ℝ → B} (hf : f a = f (a + p))
  (hc : continuous_on f $ Icc a (a + p)) : continuous (lift_Ico p a f) :=
begin
  rw lift_Ico_eq_lift_Icc hf,
  refine continuous.comp _ homeo_Icc_quot.continuous_to_fun,
  exact continuous_coinduced_dom.mpr (continuous_on_iff_continuous_restrict.mp hc),
end

end real

section zero_based

variables {p : ℝ} [hp : fact (0 < p)]
include hp

lemma lift_Ico_zero_coe_apply {f : ℝ → B} {x : ℝ} (hx : x ∈ Ico 0 p) :
  lift_Ico p 0 f ↑x = f x := lift_Ico_coe_apply (by rwa zero_add)

lemma lift_Ico_zero_continuous [topological_space B] {f : ℝ → B}
  (hf : f 0 = f p) (hc : continuous_on f $ Icc 0 p) : continuous (lift_Ico p 0 f) :=
lift_Ico_continuous (by rwa zero_add : f 0 = f (0 + p)) (by rwa zero_add)

end zero_based

end add_circle

end identify_Icc_ends
