/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
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

variables {𝕜 B : Type*}

section continuity

variables [linear_ordered_add_comm_group 𝕜] [archimedean 𝕜]
  [topological_space 𝕜] [order_topology 𝕜] (a : 𝕜) {p : 𝕜} (hp : 0 < p) (x : 𝕜)

lemma continuous_right_to_Ico_mod : continuous_within_at (to_Ico_mod a hp) (Ici x) x :=
begin
  intros s h,
  rw [filter.mem_map, mem_nhds_within_iff_exists_mem_nhds_inter],
  haveI : nontrivial 𝕜 := ⟨⟨0, p, hp.ne⟩⟩,
  simp_rw mem_nhds_iff_exists_Ioo_subset at h ⊢,
  obtain ⟨l, u, hxI, hIs⟩ := h,
  let d := to_Ico_div a hp x • p,
  have hd := to_Ico_mod_mem_Ico a hp x,
  simp_rw [subset_def, mem_inter_iff],
  refine ⟨_, ⟨l - d, min (a + p) u - d, _, λ x, id⟩, λ y, _⟩;
    simp_rw [← add_mem_Ioo_iff_left, mem_Ioo, lt_min_iff],
  { exact ⟨hxI.1, hd.2, hxI.2⟩ },
  { rintro ⟨h, h'⟩, apply hIs,
    rw [← to_Ico_mod_add_zsmul, (to_Ico_mod_eq_self _).2],
    exacts [⟨h.1, h.2.2⟩, ⟨hd.1.trans (add_le_add_right h' _), h.2.1⟩] },
end

lemma continuous_left_to_Ioc_mod : continuous_within_at (to_Ioc_mod a hp) (Iic x) x :=
begin
  rw (funext (λ y, eq.trans (by rw neg_neg) $ to_Ioc_mod_neg _ _ _) :
    to_Ioc_mod a hp = (λ x, p - x) ∘ to_Ico_mod (-a) hp ∘ has_neg.neg),
  exact ((continuous_sub_left _).continuous_at.comp_continuous_within_at $
    (continuous_right_to_Ico_mod _ _ _).comp continuous_neg.continuous_within_at $ λ y, neg_le_neg),
end

variables {x} (hx : (x : 𝕜 ⧸ zmultiples p) ≠ a)

lemma to_Ico_mod_eventually_eq_to_Ioc_mod : to_Ico_mod a hp =ᶠ[nhds x] to_Ioc_mod a hp :=
is_open.mem_nhds (by {rw Ico_eq_locus_Ioc_eq_Union_Ioo, exact is_open_Union (λ i, is_open_Ioo)}) $
  ((tfae_to_Ico_eq_to_Ioc a hp x).out 8 2).1 hx

lemma continuous_at_to_Ico_mod : continuous_at (to_Ico_mod a hp) x :=
let h := to_Ico_mod_eventually_eq_to_Ioc_mod a hp hx in continuous_at_iff_continuous_left_right.2 $
  ⟨(continuous_left_to_Ioc_mod a hp x).congr_of_eventually_eq
    (h.filter_mono nhds_within_le_nhds) h.eq_of_nhds, continuous_right_to_Ico_mod a hp x⟩

lemma continuous_at_to_Ioc_mod : continuous_at (to_Ioc_mod a hp) x :=
let h := to_Ico_mod_eventually_eq_to_Ioc_mod a hp hx in continuous_at_iff_continuous_left_right.2 $
  ⟨continuous_left_to_Ioc_mod a hp x, (continuous_right_to_Ico_mod a hp x).congr_of_eventually_eq
    (h.symm.filter_mono nhds_within_le_nhds) h.symm.eq_of_nhds⟩

end continuity

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

@[simp] lemma coe_add_period (x : 𝕜) : ((x + p : 𝕜) : add_circle p) = x :=
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

/-- The equivalence between `add_circle p` and the half-open interval `[a, a + p)`, whose inverse
is the natural quotient map. -/
def equiv_Ico : add_circle p ≃ Ico a (a + p) := quotient_add_group.equiv_Ico_mod a hp.out

/-- The equivalence between `add_circle p` and the half-open interval `(a, a + p]`, whose inverse
is the natural quotient map. -/
def equiv_Ioc : add_circle p ≃ Ioc a (a + p) := quotient_add_group.equiv_Ioc_mod a hp.out

/-- Given a function on `𝕜`, return the unique function on `add_circle p` agreeing with `f` on
`[a, a + p)`. -/
def lift_Ico (f : 𝕜 → B) : add_circle p → B := restrict _ f ∘ add_circle.equiv_Ico p a

/-- Given a function on `𝕜`, return the unique function on `add_circle p` agreeing with `f` on
`(a, a + p]`. -/
def lift_Ioc (f : 𝕜 → B) : add_circle p → B := restrict _ f ∘ add_circle.equiv_Ioc p a

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

lemma lift_Ioc_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ioc a (a + p)) : lift_Ioc p a f ↑x = f x :=
begin
  have : (equiv_Ioc p a) x = ⟨x, hx⟩,
  { rw equiv.apply_eq_iff_eq_symm_apply,
    refl, },
  rw [lift_Ioc, comp_apply, this],
  refl,
end

variables (p a)

section continuity

@[continuity] lemma continuous_equiv_Ico_symm : continuous (equiv_Ico p a).symm :=
continuous_quotient_mk.comp continuous_subtype_coe

@[continuity] lemma continuous_equiv_Ioc_symm : continuous (equiv_Ioc p a).symm :=
continuous_quotient_mk.comp continuous_subtype_coe

variables {x : 𝕜} (hx : (x : add_circle p) ≠ a)
include hx

lemma continuous_at_equiv_Ico : continuous_at (equiv_Ico p a) x :=
begin
  rw [continuous_at, filter.tendsto, quotient_add_group.nhds_eq, filter.map_map],
  apply continuous_at.cod_restrict, exact continuous_at_to_Ico_mod a hp.out hx,
end

lemma continuous_at_equiv_Ioc : continuous_at (equiv_Ioc p a) x :=
begin
  rw [continuous_at, filter.tendsto, quotient_add_group.nhds_eq, filter.map_map],
  apply continuous_at.cod_restrict, exact continuous_at_to_Ioc_mod a hp.out hx,
end

end continuity

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → add_circle p` is
the entire space. -/
@[simp] lemma coe_image_Ico_eq : (coe : 𝕜 → add_circle p) '' Ico a (a + p) = univ :=
by { rw image_eq_range, exact (equiv_Ico p a).symm.range_eq_univ }

/-- The image of the closed-open interval `[a, a + p)` under the quotient map `𝕜 → add_circle p` is
the entire space. -/
@[simp] lemma coe_image_Ioc_eq : (coe : 𝕜 → add_circle p) '' Ioc a (a + p) = univ :=
by { rw image_eq_range, exact (equiv_Ioc p a).symm.range_eq_univ }

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
/-! This section proves that for any `a`, the natural map from `[a, a + p] ⊂ 𝕜` to `add_circle p`
gives an identification of `add_circle p`, as a topological space, with the quotient of `[a, a + p]`
by the equivalence relation identifying the endpoints. -/

namespace add_circle

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
{ to_fun := λ x, quot.mk _ $ inclusion Ico_subset_Icc_self (equiv_Ico _ _ x),
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

lemma equiv_Icc_quot_comp_mk_eq_to_Ico_mod : equiv_Icc_quot p a ∘ quotient.mk' =
  λ x, quot.mk _ ⟨to_Ico_mod a hp.out x, Ico_subset_Icc_self $ to_Ico_mod_mem_Ico a _ x⟩ := rfl

lemma equiv_Icc_quot_comp_mk_eq_to_Ioc_mod : equiv_Icc_quot p a ∘ quotient.mk' =
  λ x, quot.mk _ ⟨to_Ioc_mod a hp.out x, Ioc_subset_Icc_self $ to_Ioc_mod_mem_Ioc a _ x⟩ :=
begin
  rw equiv_Icc_quot_comp_mk_eq_to_Ico_mod, funext,
  have := tfae_to_Ico_eq_to_Ioc a hp.out x,
  by_cases to_Ioc_mod a hp.out x = a + p,
  { simp_rw [h, not_imp_not.1 (this.out 4 5).2 h], exact quot.sound endpoint_ident.mk },
  { simp_rw (this.out 4 2).1 h },
end

/-- The natural map from `[a, a + p] ⊂ ℝ` with endpoints identified to `ℝ / ℤ • p`, as a
homeomorphism of topological spaces. -/
def homeo_Icc_quot : 𝕋 ≃ₜ quot (endpoint_ident p a) :=
{ to_equiv := equiv_Icc_quot p a,
  continuous_to_fun := begin
    simp_rw [quotient_map_quotient_mk.continuous_iff,
      continuous_iff_continuous_at, continuous_at_iff_continuous_left_right],
    intro x, split,
    work_on_goal 1 { erw equiv_Icc_quot_comp_mk_eq_to_Ioc_mod },
    work_on_goal 2 { erw equiv_Icc_quot_comp_mk_eq_to_Ico_mod },
    all_goals { apply continuous_quot_mk.continuous_at.comp_continuous_within_at,
      rw inducing_coe.continuous_within_at_iff },
    { apply continuous_left_to_Ioc_mod },
    { apply continuous_right_to_Ico_mod },
  end,
  continuous_inv_fun := continuous_quot_lift _
    ((add_circle.continuous_mk' p).comp continuous_subtype_coe) }

/-! We now show that a continuous function on `[a, a + p]` satisfying `f a = f (a + p)` is the
pullback of a continuous function on `add_circle p`. -/

variables {p a}

lemma lift_Ico_eq_lift_Icc {f : 𝕜 → B} (h : f a = f (a + p)) : lift_Ico p a f =
  quot.lift (restrict (Icc a $ a + p) f) (by { rintro _ _ ⟨_⟩, exact h }) ∘ equiv_Icc_quot p a :=
rfl

lemma lift_Ico_continuous [topological_space B] {f : 𝕜 → B} (hf : f a = f (a + p))
  (hc : continuous_on f $ Icc a (a + p)) : continuous (lift_Ico p a f) :=
begin
  rw lift_Ico_eq_lift_Icc hf,
  refine continuous.comp _ (homeo_Icc_quot p a).continuous_to_fun,
  exact continuous_coinduced_dom.mpr (continuous_on_iff_continuous_restrict.mp hc),
end

section zero_based

lemma lift_Ico_zero_coe_apply {f : 𝕜 → B} {x : 𝕜} (hx : x ∈ Ico 0 p) :
  lift_Ico p 0 f ↑x = f x := lift_Ico_coe_apply (by rwa zero_add)

lemma lift_Ico_zero_continuous [topological_space B] {f : 𝕜 → B}
  (hf : f 0 = f p) (hc : continuous_on f $ Icc 0 p) : continuous (lift_Ico p 0 f) :=
lift_Ico_continuous (by rwa zero_add : f 0 = f (0 + p)) (by rwa zero_add)

end zero_based

end add_circle

end identify_Icc_ends
