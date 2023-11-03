/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
import measure_theory.measure.lebesgue.eq_haar
import measure_theory.measure.haar.quotient
import measure_theory.constructions.polish
import measure_theory.integral.interval_integral
import topology.algebra.order.floor

/-!
# Integrals of periodic functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that the half-open interval `Ioc t (t + T)` in `ℝ` is a fundamental domain of
the action of the subgroup `ℤ ∙ T` on `ℝ`.

A consequence is `add_circle.measure_preserving_mk`: the covering map from `ℝ` to the "additive
circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving, with respect to the restriction of Lebesgue measure to
`Ioc t (t + T)` (upstairs) and with respect to Haar measure (downstairs).

Another consequence (`function.periodic.interval_integral_add_eq` and related declarations) is that
`∫_{t}^{t + T} x, f x = ∫_{s}^{s + T} x, f x` for any (not necessarily measurable) function with
period `T`.
-/

open set function measure_theory measure_theory.measure topological_space add_subgroup
  interval_integral

open_locale measure_theory nnreal ennreal

noncomputable instance add_circle.measurable_space {a : ℝ} : measurable_space (add_circle a) :=
quotient_add_group.measurable_space _

instance add_circle.borel_space {a : ℝ} : borel_space (add_circle a) :=
quotient_add_group.borel_space

@[measurability] protected lemma add_circle.measurable_mk' {a : ℝ} :
  measurable (coe : ℝ → add_circle a) :=
continuous.measurable $ add_circle.continuous_mk' a

lemma is_add_fundamental_domain_Ioc {T : ℝ} (hT : 0 < T) (t : ℝ) (μ : measure ℝ . volume_tac) :
  is_add_fundamental_domain (add_subgroup.zmultiples T) (Ioc t (t + T)) μ :=
begin
  refine is_add_fundamental_domain.mk' measurable_set_Ioc.null_measurable_set (λ x, _),
  have : bijective (cod_restrict (λ n : ℤ, n • T) (add_subgroup.zmultiples T) _),
    from (equiv.of_injective (λ n : ℤ, n • T) (zsmul_strict_mono_left hT).injective).bijective,
  refine this.exists_unique_iff.2 _,
  simpa only [add_comm x] using exists_unique_add_zsmul_mem_Ioc hT x t
end

lemma is_add_fundamental_domain_Ioc' {T : ℝ} (hT : 0 < T) (t : ℝ) (μ : measure ℝ . volume_tac) :
  is_add_fundamental_domain (add_subgroup.zmultiples T).opposite (Ioc t (t + T)) μ :=
begin
  refine is_add_fundamental_domain.mk' measurable_set_Ioc.null_measurable_set (λ x, _),
  have : bijective (cod_restrict (λ n : ℤ, n • T) (add_subgroup.zmultiples T) _),
    from (equiv.of_injective (λ n : ℤ, n • T) (zsmul_strict_mono_left hT).injective).bijective,
  refine this.exists_unique_iff.2 _,
  simpa using exists_unique_add_zsmul_mem_Ioc hT x t,
end

namespace add_circle
variables (T : ℝ) [hT : fact (0 < T)]
include hT

/-- Equip the "additive circle" `ℝ ⧸ (ℤ ∙ T)` with, as a standard measure, the Haar measure of total
mass `T` -/
noncomputable instance measure_space : measure_space (add_circle T) :=
{ volume := (ennreal.of_real T) • add_haar_measure ⊤,
  .. add_circle.measurable_space }

@[simp] protected lemma measure_univ : volume (set.univ : set (add_circle T)) = ennreal.of_real T :=
begin
  dsimp [(volume)],
  rw ← positive_compacts.coe_top,
  simp [add_haar_measure_self, -positive_compacts.coe_top],
end

instance : is_add_haar_measure (volume : measure (add_circle T)) :=
is_add_haar_measure.smul _ (by simp [hT.out]) ennreal.of_real_ne_top

instance is_finite_measure : is_finite_measure (volume : measure (add_circle T)) :=
{ measure_univ_lt_top := by simp }

/-- The covering map from `ℝ` to the "additive circle" `ℝ ⧸ (ℤ ∙ T)` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass `T`)
on the additive circle, and with respect to the restriction of Lebsegue measure on `ℝ` to an
interval (t, t + T]. -/
protected lemma measure_preserving_mk (t : ℝ) :
  measure_preserving (coe : ℝ → add_circle T) (volume.restrict (Ioc t (t + T))) :=
measure_preserving_quotient_add_group.mk'
  (is_add_fundamental_domain_Ioc' hT.out t)
  (⊤ : positive_compacts (add_circle T))
  (by simp)
  T.to_nnreal
  (by simp [← ennreal.of_real_coe_nnreal, real.coe_to_nnreal T hT.out.le])

lemma volume_closed_ball {x : add_circle T} (ε : ℝ) :
  volume (metric.closed_ball x ε) = ennreal.of_real (min T (2 * ε)) :=
begin
  have hT' : |T| = T := abs_eq_self.mpr hT.out.le,
  let I := Ioc (-(T / 2)) (T / 2),
  have h₁ : ε < T/2 → (metric.closed_ball (0 : ℝ) ε) ∩ I = metric.closed_ball (0 : ℝ) ε,
  { intros hε,
    rw [inter_eq_left_iff_subset, real.closed_ball_eq_Icc, zero_sub, zero_add],
    rintros y ⟨hy₁, hy₂⟩, split; linarith, },
  have h₂ : coe⁻¹' metric.closed_ball (0 : add_circle T) ε ∩ I =
    if ε < T/2 then metric.closed_ball (0 : ℝ) ε else I,
  { conv_rhs { rw [← if_ctx_congr (iff.rfl : ε < T/2 ↔ ε < T/2) h₁ (λ _, rfl), ← hT'], },
    apply coe_real_preimage_closed_ball_inter_eq,
    simpa only [hT', real.closed_ball_eq_Icc, zero_add, zero_sub] using Ioc_subset_Icc_self, },
  rw add_haar_closed_ball_center,
  simp only [restrict_apply' measurable_set_Ioc, (by linarith : -(T/2) + T = T/2), h₂,
    ← (add_circle.measure_preserving_mk T (-(T/2))).measure_preimage measurable_set_closed_ball],
  by_cases hε : ε < T/2,
  { simp [hε, min_eq_right (by linarith : 2 * ε ≤ T)], },
  { simp [hε, min_eq_left (by linarith : T ≤ 2 * ε)], },
end

instance : is_unif_loc_doubling_measure (volume : measure (add_circle T)) :=
begin
  refine ⟨⟨real.to_nnreal 2, filter.eventually_of_forall $ λ ε x, _⟩⟩,
  simp only [volume_closed_ball],
  erw ← ennreal.of_real_mul zero_le_two,
  apply ennreal.of_real_le_of_real,
  rw mul_min_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2),
  exact min_le_min (by linarith [hT.out]) (le_refl _),
end

/-- The isomorphism `add_circle T ≃ Ioc a (a + T)` whose inverse is the natural quotient map,
  as an equivalence of measurable spaces. -/
noncomputable def measurable_equiv_Ioc (a : ℝ) : add_circle T ≃ᵐ Ioc a (a + T) :=
{ measurable_to_fun   := measurable_of_measurable_on_compl_singleton _
                          (continuous_on_iff_continuous_restrict.mp $ continuous_at.continuous_on $
                          λ x hx, continuous_at_equiv_Ioc T a hx).measurable,
  measurable_inv_fun  := add_circle.measurable_mk'.comp measurable_subtype_coe,
                      .. equiv_Ioc T a }

/-- The isomorphism `add_circle T ≃ Ico a (a + T)` whose inverse is the natural quotient map,
  as an equivalence of measurable spaces. -/
noncomputable def measurable_equiv_Ico (a : ℝ) : add_circle T ≃ᵐ Ico a (a + T) :=
{ measurable_to_fun   := measurable_of_measurable_on_compl_singleton _
                          (continuous_on_iff_continuous_restrict.mp $ continuous_at.continuous_on $
                          λ x hx, continuous_at_equiv_Ico T a hx).measurable,
  measurable_inv_fun  := add_circle.measurable_mk'.comp measurable_subtype_coe,
                      .. equiv_Ico T a }

/-- The lower integral of a function over `add_circle T` is equal to the lower integral over an
interval (t, t + T] in `ℝ` of its lift to `ℝ`. -/
protected lemma lintegral_preimage (t : ℝ) (f : add_circle T → ℝ≥0∞) :
  ∫⁻ a in Ioc t (t + T), f a = ∫⁻ b : add_circle T, f b :=
begin
  have m : measurable_set (Ioc t (t + T)) := measurable_set_Ioc,
  have := lintegral_map_equiv f (measurable_equiv_Ioc T t).symm,
  swap, exact volume,
  simp only [measurable_equiv_Ioc, equiv_Ioc, quotient_add_group.equiv_Ioc_mod,
    measurable_equiv.symm_mk, measurable_equiv.coe_mk, equiv.coe_fn_symm_mk] at this,
  rw ←(add_circle.measure_preserving_mk T t).map_eq,
  convert this.symm using 1, -- TODO : there is no "set_lintegral_eq_subtype"?
  { rw ←(map_comap_subtype_coe m _),
    exact measurable_embedding.lintegral_map (measurable_embedding.subtype_coe m) _, },
  { congr' 1,
    have : (coe : Ioc t (t + T) → add_circle T) = (coe : ℝ → add_circle T) ∘ (coe : _ → ℝ),
    { ext1 x, refl, },
    simp_rw [this, ←map_map add_circle.measurable_mk' measurable_subtype_coe,
      ←map_comap_subtype_coe m],
    refl, }
end

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

/-- The integral of an almost-everywhere strongly measurable function over `add_circle T` is equal
to the integral over an interval (t, t + T] in `ℝ` of its lift to `ℝ`. -/
protected lemma integral_preimage (t : ℝ) (f : add_circle T → E) :
  ∫ a in Ioc t (t + T), f a = ∫ b : add_circle T, f b :=
begin
  have m : measurable_set (Ioc t (t + T)) := measurable_set_Ioc,
  have := integral_map_equiv (measurable_equiv_Ioc T t).symm f,
  simp only [measurable_equiv_Ioc, equiv_Ioc, quotient_add_group.equiv_Ioc_mod,
    measurable_equiv.symm_mk, measurable_equiv.coe_mk, equiv.coe_fn_symm_mk, coe_coe] at this,
  rw [←(add_circle.measure_preserving_mk T t).map_eq, set_integral_eq_subtype m, ←this],
  have : (coe : Ioc t (t + T) → add_circle T) = (coe : ℝ → add_circle T) ∘ (coe : _ → ℝ),
  { ext1 x, refl, },
  simp_rw [this, ←map_map add_circle.measurable_mk' measurable_subtype_coe,
    ←map_comap_subtype_coe m],
  refl,
end

/-- The integral of an almost-everywhere strongly measurable function over `add_circle T` is equal
to the integral over an interval (t, t + T] in `ℝ` of its lift to `ℝ`. -/
protected lemma interval_integral_preimage (t : ℝ) (f : add_circle T → E) :
  ∫_{t}^{(t + T)} a, f a = ∫ b : add_circle T, f b :=
begin
  rw [integral_of_le, add_circle.integral_preimage T t f],
  linarith [hT.out],
end

end add_circle

namespace unit_add_circle
local attribute [instance] real.fact_zero_lt_one

noncomputable instance measure_space : measure_space unit_add_circle := add_circle.measure_space 1

@[simp] protected lemma measure_univ : volume (set.univ : set unit_add_circle) = 1 := by simp

instance is_finite_measure : is_finite_measure (volume : measure unit_add_circle) :=
add_circle.is_finite_measure 1

/-- The covering map from `ℝ` to the "unit additive circle" `ℝ ⧸ ℤ` is measure-preserving,
considered with respect to the standard measure (defined to be the Haar measure of total mass 1)
on the additive circle, and with respect to the restriction of Lebsegue measure on `ℝ` to an
interval (t, t + 1]. -/
protected lemma measure_preserving_mk (t : ℝ) :
  measure_preserving (coe : ℝ → unit_add_circle) (volume.restrict (Ioc t (t + 1))) :=
add_circle.measure_preserving_mk 1 t

/-- The integral of a measurable function over `unit_add_circle` is equal to the integral over an
interval (t, t + 1] in `ℝ` of its lift to `ℝ`. -/
protected lemma lintegral_preimage (t : ℝ) (f : unit_add_circle → ℝ≥0∞) :
  ∫⁻ a in Ioc t (t + 1), f a = ∫⁻ b : unit_add_circle, f b :=
add_circle.lintegral_preimage 1 t f

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

/-- The integral of an almost-everywhere strongly measurable function over `unit_add_circle` is
equal to the integral over an interval (t, t + 1] in `ℝ` of its lift to `ℝ`. -/
protected lemma integral_preimage (t : ℝ) (f : unit_add_circle → E) :
  ∫ a in Ioc t (t + 1), f a = ∫ b : unit_add_circle, f b :=
add_circle.integral_preimage 1 t f

/-- The integral of an almost-everywhere strongly measurable function over `unit_add_circle` is
equal to the integral over an interval (t, t + 1] in `ℝ` of its lift to `ℝ`. -/
protected lemma interval_integral_preimage (t : ℝ) (f : unit_add_circle → E) :
  ∫_{t}^{(t + 1)} a, f a = ∫ b : unit_add_circle, f b :=
add_circle.interval_integral_preimage 1 t f

end unit_add_circle

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]

namespace function

namespace periodic

variables {f : ℝ → E} {T : ℝ}

/-- An auxiliary lemma for a more general `function.periodic.interval_integral_add_eq`. -/
lemma interval_integral_add_eq_of_pos (hf : periodic f T)
  (hT : 0 < T) (t s : ℝ) : ∫_{t}^{t + T} x, f x = ∫_{s}^{s + T} x, f x :=
begin
  simp only [integral_of_le, hT.le, le_add_iff_nonneg_right],
  haveI : vadd_invariant_measure (add_subgroup.zmultiples T) ℝ volume :=
    ⟨λ c s hs, measure_preimage_add _ _ _⟩,
  exact (is_add_fundamental_domain_Ioc hT t).set_integral_eq
    (is_add_fundamental_domain_Ioc hT s) hf.map_vadd_zmultiples
end

/-- If `f` is a periodic function with period `T`, then its integral over `[t, t + T]` does not
depend on `t`. -/
lemma interval_integral_add_eq (hf : periodic f T)
  (t s : ℝ) : ∫_{t}^{t + T} x, f x = ∫_{s}^{s + T} x, f x :=
begin
  rcases lt_trichotomy 0 T with (hT|rfl|hT),
  { exact hf.interval_integral_add_eq_of_pos hT t s },
  { simp },
  { rw [← neg_inj, ← integral_symm, ← integral_symm],
    simpa only [← sub_eq_add_neg, add_sub_cancel]
      using (hf.neg.interval_integral_add_eq_of_pos (neg_pos.2 hT) (t + T) (s + T)) }
end

/-- If `f` is an integrable periodic function with period `T`, then its integral over `[t, s + T]`
is the sum of its integrals over the intervals `[t, s]` and `[t, t + T]`. -/
lemma interval_integral_add_eq_add (hf : periodic f T) (t s : ℝ)
  (h_int : ∀ t₁ t₂, interval_integrable f measure_space.volume t₁ t₂) :
  ∫_{t}^{s+T} x, f x = (∫_{t}^{s} x, f x) + ∫_{t}^{t + T} x, f x :=
by rw [hf.interval_integral_add_eq t s, integral_add_adjacent_intervals (h_int t s) (h_int s _)]

/-- If `f` is an integrable periodic function with period `T`, and `n` is an integer, then its
integral over `[t, t + n • T]` is `n` times its integral over `[t, t + T]`. -/
lemma interval_integral_add_zsmul_eq (hf : periodic f T) (n : ℤ) (t : ℝ)
  (h_int : ∀ t₁ t₂, interval_integrable f measure_space.volume t₁ t₂) :
  ∫_{t}^{t + n • T} x, f x = n • ∫_{t}^{t + T} x, f x :=
begin
  -- Reduce to the case `b = 0`
  suffices : ∫_{0}^{n • T} x, f x = n • ∫_{0}^{T} x, f x,
  { simp only [hf.interval_integral_add_eq t 0, (hf.zsmul n).interval_integral_add_eq t 0, zero_add,
      this], },
  -- First prove it for natural numbers
  have : ∀ (m : ℕ), ∫_{0}^{m • T} x, f x = m • ∫_{0}^{T} x, f x,
  { intros,
    induction m with m ih,
    { simp, },
    { simp only [succ_nsmul', hf.interval_integral_add_eq_add 0 (m • T) h_int, ih, zero_add], }, },
  -- Then prove it for all integers
  cases n with n n,
  { simp [← this n], },
  { conv_rhs { rw zsmul_neg_succ_of_nat, },
    have h₀ : (int.neg_succ_of_nat n) • T + (n + 1) • T = 0, { simp, linarith, },
    rw [integral_symm, ← (hf.nsmul (n+1)).funext, neg_inj],
    simp_rw [integral_comp_add_right, h₀, zero_add, this (n+1),
      add_comm T, hf.interval_integral_add_eq ((n+1) • T) 0, zero_add], },
end

section real_valued

open filter

variables {g : ℝ → ℝ}
variables (hg : periodic g T) (h_int : ∀ t₁ t₂, interval_integrable g measure_space.volume t₁ t₂)
include hg h_int

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫_{0}^{t} x, g x` is bounded below by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
lemma Inf_add_zsmul_le_integral_of_pos (hT : 0 < T) (t : ℝ) :
  Inf ((λ t, ∫_{0}^{t} x, g x) '' (Icc 0 T)) + ⌊t/T⌋ • (∫_{0}^{T} x, g x) ≤ ∫_{0}^{t} x, g x :=
begin
  let ε := int.fract (t/T) * T,
  conv_rhs { rw [← int.fract_div_mul_self_add_zsmul_eq T t (by linarith),
    ← integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)] },
  rw [hg.interval_integral_add_zsmul_eq ⌊t/T⌋ ε h_int, hg.interval_integral_add_eq ε 0, zero_add,
    add_le_add_iff_right],
  exact (continuous_primitive h_int 0).continuous_on.Inf_image_Icc_le
    (mem_Icc_of_Ico (int.fract_div_mul_self_mem_Ico T t hT)),
end

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫_{0}^{t} x, g x` is bounded above by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
lemma integral_le_Sup_add_zsmul_of_pos (hT : 0 < T) (t : ℝ) :
  ∫_{0}^{t} x, g x ≤ Sup ((λ t, ∫_{0}^{t} x, g x) '' (Icc 0 T)) + ⌊t/T⌋ • (∫_{0}^{T} x, g x) :=
begin
  let ε := int.fract (t/T) * T,
  conv_lhs { rw [← int.fract_div_mul_self_add_zsmul_eq T t (by linarith),
    ← integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)] },
  rw [hg.interval_integral_add_zsmul_eq ⌊t/T⌋ ε h_int, hg.interval_integral_add_eq ε 0, zero_add,
    add_le_add_iff_right],
  exact (continuous_primitive h_int 0).continuous_on.le_Sup_image_Icc
    (mem_Icc_of_Ico (int.fract_div_mul_self_mem_Ico T t hT)),
end

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫_{0}^{T} x, g x`, then
`t ↦ ∫_{0}^{t} x, g x` tends to `∞` as `t` tends to `∞`. -/
lemma tendsto_at_top_interval_integral_of_pos (h₀ : 0 < ∫_{0}^{T} x, g x) (hT : 0 < T) :
  tendsto (λ t, ∫_{0}^{t} x, g x) at_top at_top :=
begin
  apply tendsto_at_top_mono (hg.Inf_add_zsmul_le_integral_of_pos h_int hT),
  apply at_top.tendsto_at_top_add_const_left (Inf $ (λ t, ∫_{0}^{t} x, g x) '' (Icc 0 T)),
  apply tendsto.at_top_zsmul_const h₀,
  exact tendsto_floor_at_top.comp (tendsto_id.at_top_mul_const (inv_pos.mpr hT)),
end

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫_{0}^{T} x, g x`, then
`t ↦ ∫_{0}^{t} x, g x` tends to `-∞` as `t` tends to `-∞`. -/
lemma tendsto_at_bot_interval_integral_of_pos (h₀ : 0 < ∫_{0}^{T} x, g x) (hT : 0 < T) :
  tendsto (λ t, ∫_{0}^{t} x, g x) at_bot at_bot :=
begin
  apply tendsto_at_bot_mono (hg.integral_le_Sup_add_zsmul_of_pos h_int hT),
  apply at_bot.tendsto_at_bot_add_const_left (Sup $ (λ t, ∫_{0}^{t} x, g x) '' (Icc 0 T)),
  apply tendsto.at_bot_zsmul_const h₀,
  exact tendsto_floor_at_bot.comp (tendsto_id.at_bot_mul_const (inv_pos.mpr hT)),
end

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫_{0}^{t} x, g x`
tends to `∞` as `t` tends to `∞`. -/
lemma tendsto_at_top_interval_integral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
  tendsto (λ t, ∫_{0}^{t} x, g x) at_top at_top :=
hg.tendsto_at_top_interval_integral_of_pos h_int (interval_integral_pos_of_pos (h_int 0 T) h₀ hT) hT

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫_{0}^{t} x, g x`
tends to `-∞` as `t` tends to `-∞`. -/
lemma tendsto_at_bot_interval_integral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
  tendsto (λ t, ∫_{0}^{t} x, g x) at_bot at_bot :=
hg.tendsto_at_bot_interval_integral_of_pos h_int (interval_integral_pos_of_pos (h_int 0 T) h₀ hT) hT

end real_valued

end periodic

end function
