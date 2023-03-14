/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.calculus.cont_diff
/-import analysis.locally_convex.with_seminorms
import topology.algebra.uniform_filter_basis
import topology.continuous_function.bounded
import tactic.positivity
import analysis.special_functions.pow
import analysis.inner_product_space.calculus
import analysis.special_functions.exp_deriv-/

/-!
# Schwartz space

This file defines the Schwartz space. Usually, the Schwartz space is defined as the set of smooth
functions $f : ℝ^n → ℂ$ such that there exists $C_{αβ} > 0$ with $$|x^α ∂^β f(x)| < C_{αβ}$$ for
all $x ∈ ℝ^n$ and for all multiindices $α, β$.
In mathlib, we use a slightly different approach and define define the Schwartz space as all
smooth functions `f : E → F`, where `E` and `F` are real normed vector spaces such that for all
natural numbers `k` and `n` we have uniform bounds `‖x‖^k * ‖iterated_fderiv ℝ n f x‖ < C`.
This approach completely avoids using partial derivatives as well as polynomials.
We construct the topology on the Schwartz space by a family of seminorms, which are the best
constants in the above estimates, which is by abstract theory from
`seminorm_family.module_filter_basis` and `with_seminorms.to_locally_convex_space` turns the
Schwartz space into a locally convex topological vector space.

## Main definitions

* `schwartz_map`: The Schwartz space is the space of smooth functions such that all derivatives
decay faster than any power of `‖x‖`.
* `schwartz_map.seminorm`: The family of seminorms as described above
* `schwartz_map.fderiv_clm`: The differential as a continuous linear map
`𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`

## Main statements

* `schwartz_map.uniform_add_group` and `schwartz_map.locally_convex`: The Schwartz space is a
locally convex topological vector space.

## Implementation details

The implementation of the seminorms is taken almost literally from `continuous_linear_map.op_norm`.

## Notation

* `𝓢(E, F)`: The Schwartz space `schwartz_map E F` localized in `schwartz_space`

## Tags

Schwartz space, tempered distributions
-/

noncomputable theory

universe u
variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] {Eu Fu Gu Hu : Type u}
  [normed_add_comm_group Eu] [normed_space 𝕜 Eu]
  [normed_add_comm_group Fu] [normed_space 𝕜 Fu]
  [normed_add_comm_group Gu] [normed_space 𝕜 Gu]
  [normed_add_comm_group Hu] [normed_space 𝕜 Hu]

open_locale big_operators


section

open finset

lemma sum_choose_succ_mul_mul_sub {R : Type*} [comm_semiring R] (a b : ℕ → R) (n : ℕ) :
  ∑ i in range (n+2), ((n+1).choose i : R) * a i * b (n + 1 - i) =
    ∑ i in range (n+1), (n.choose i : R) * a i * b (n + 1 - i)
      + ∑ i in range (n+1), (n.choose i : R) * a (i + 1) * b (n - i) :=
begin
  have A : ∑ i in range (n + 1), (n.choose (i+1) : R) * a (i + 1) * b (n - i) + a 0 * b (n + 1)
  = ∑ i in range (n+1), n.choose i * a i * b (n + 1 - i),
  { rw [finset.sum_range_succ, finset.sum_range_succ'],
    simp only [nat.choose_succ_self, algebra_map.coe_zero, zero_mul, add_zero,
      nat.succ_sub_succ_eq_sub, nat.choose_zero_right, algebra_map.coe_one, one_mul, tsub_zero] },
  calc
  ∑ i in finset.range (n+2), ((n+1).choose i : R) * a i * b (n + 1 - i)
  = ∑ i in finset.range (n+1), ((n+1).choose (i+1) : R) * a (i+1) * b (n + 1 - (i+1))
      + a 0 * b (n + 1 - 0) :
    begin
      rw finset.sum_range_succ',
      simp only [nat.choose_zero_right, algebra_map.coe_one, one_mul],
    end
  ... = ∑ i in finset.range (n+1), (n.choose i : R) * a i * b (n + 1 - i)
  + ∑ i in finset.range (n+1), n.choose i * a (i + 1) * b (n - i) :
    begin
      simp only [nat.choose_succ_succ, nat.cast_add, nat.succ_sub_succ_eq_sub, tsub_zero, add_mul],
      rw [finset.sum_add_distrib, ← A],
      abel,
    end
end

end

lemma continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear_aux
  (B : Eu →L[𝕜] Fu →L[𝕜] Gu) {f : Hu → Eu} {g : Hu → Fu} {n : ℕ} {s : set Hu} {x : Hu}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  ‖iterated_fderiv_within 𝕜 n (λ y, B (f y) (g y)) s x‖
  ≤ ‖B‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n-i) g s x‖ :=
begin
  unfreezingI { induction n with n IH generalizing Eu Fu Gu},
  { simp only [←mul_assoc, norm_iterated_fderiv_within_zero, finset.range_one, finset.sum_singleton,
      nat.choose_self, algebra_map.coe_one, one_mul],
    apply ((B (f x)).le_op_norm (g x)).trans,
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
    exact B.le_op_norm (f x) },
  { have In : (n : with_top ℕ) + 1 ≤ n.succ, by simp only [nat.cast_succ, le_refl],
    have I1 :
      ‖iterated_fderiv_within 𝕜 n (λ (y : Hu), B.precompR Hu (f y) (fderiv_within 𝕜 g s y)) s x‖ ≤
      ‖B‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i *
        ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n + 1 - i) g s x‖ := calc
      ‖iterated_fderiv_within 𝕜 n (λ (y : Hu), B.precompR Hu (f y) (fderiv_within 𝕜 g s y)) s x‖
          ≤ ‖B.precompR Hu‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i
            * ‖iterated_fderiv_within 𝕜 i f s x‖
            * ‖iterated_fderiv_within 𝕜 (n - i) (fderiv_within 𝕜 g s) s x‖ :
        IH _ (hf.of_le (nat.cast_le.2 (nat.le_succ n))) (hg.fderiv_within hs In)
      ... ≤ ‖B‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i
            * ‖iterated_fderiv_within 𝕜 i f s x‖
            * ‖iterated_fderiv_within 𝕜 (n - i) (fderiv_within 𝕜 g s) s x‖ :
        mul_le_mul_of_nonneg_right (B.norm_precompR_le Hu) (finset.sum_nonneg' (λ i, by positivity))
      ... = _ :
        begin
          congr' 1,
          apply finset.sum_congr rfl (λ i hi, _ ),
          rw [nat.succ_sub (nat.lt_succ_iff.1 (finset.mem_range.1 hi)),
            iterated_fderiv_within_succ_eq_comp_right hs hx, linear_isometry_equiv.norm_map],
        end,
    have I2 :
      ‖iterated_fderiv_within 𝕜 n (λ (y : Hu), B.precompL Hu (fderiv_within 𝕜 f s y) (g y)) s x‖ ≤
      ‖B‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i *
        ‖iterated_fderiv_within 𝕜 (i + 1) f s x‖ * ‖iterated_fderiv_within 𝕜 (n - i) g s x‖ := calc
      ‖iterated_fderiv_within 𝕜 n (λ (y : Hu), B.precompL Hu (fderiv_within 𝕜 f s y) (g y)) s x‖
          ≤ ‖B.precompL Hu‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i
            * ‖iterated_fderiv_within 𝕜 i (fderiv_within 𝕜 f s) s x‖
            * ‖iterated_fderiv_within 𝕜 (n - i) g s x‖ :
        IH _ (hf.fderiv_within hs In) (hg.of_le (nat.cast_le.2 (nat.le_succ n)))
      ... ≤ ‖B‖ * ∑ (i : ℕ) in finset.range (n + 1), n.choose i
            * ‖iterated_fderiv_within 𝕜 i (fderiv_within 𝕜 f s) s x‖
            * ‖iterated_fderiv_within 𝕜 (n - i) g s x‖ :
        mul_le_mul_of_nonneg_right (B.norm_precompL_le Hu) (finset.sum_nonneg' (λ i, by positivity))
      ... = _ :
        begin
          congr' 1,
          apply finset.sum_congr rfl (λ i hi, _ ),
          rw [iterated_fderiv_within_succ_eq_comp_right hs hx, linear_isometry_equiv.norm_map],
        end,
    have J : iterated_fderiv_within 𝕜 n
      (λ (y : Hu), fderiv_within 𝕜 (λ (y : Hu), B (f y) (g y)) s y) s x
      = iterated_fderiv_within 𝕜 n (λ y, B.precompR Hu (f y) (fderiv_within 𝕜 g s y)
        + B.precompL Hu (fderiv_within 𝕜 f s y) (g y)) s x,
    { apply iterated_fderiv_within_congr hs (λ y hy, _) hx,
      have L : (1 : with_top ℕ) ≤ n.succ,
        by simpa only [enat.coe_one, nat.one_le_cast] using nat.succ_pos n,
      exact B.fderiv_within_of_bilinear (hf.differentiable_on L y hy)
        (hg.differentiable_on L y hy) (hs y hy) },
    rw [iterated_fderiv_within_succ_eq_comp_right hs hx, linear_isometry_equiv.norm_map, J],
    have A : cont_diff_on 𝕜 n (λ y, B.precompR Hu (f y) (fderiv_within 𝕜 g s y)) s,
      from (B.precompR Hu).is_bounded_bilinear_map.cont_diff.comp_cont_diff_on₂
        (hf.of_le (nat.cast_le.2 (nat.le_succ n))) (hg.fderiv_within hs In),
    have A' : cont_diff_on 𝕜 n (λ y, B.precompL Hu (fderiv_within 𝕜 f s y) (g y)) s,
      from (B.precompL Hu).is_bounded_bilinear_map.cont_diff.comp_cont_diff_on₂
        (hf.fderiv_within hs In) (hg.of_le (nat.cast_le.2 (nat.le_succ n))),
    rw iterated_fderiv_within_add_apply' A A' hs hx,
    apply (norm_add_le _ _).trans ((add_le_add I1 I2).trans (le_of_eq _)),
    rw ← mul_add,
    congr' 1,
    exact (sum_choose_succ_mul_mul_sub (λ i, ‖iterated_fderiv_within 𝕜 i f s x‖)
      (λ i, ‖iterated_fderiv_within 𝕜 i g s x‖) n).symm }
end

universes uE uF uG uH
variables {E : Type uE}  {F : Type uF} {G : Type uG} {H : Type uH}
  [normed_add_comm_group E] [normed_space 𝕜 E]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [normed_add_comm_group G] [normed_space 𝕜 G]
  [normed_add_comm_group H] [normed_space 𝕜 H]

lemma continuous_linear_map.norm_iterated_fderiv_within_le_of_bilinear
  (B : E →L[𝕜] F →L[𝕜] G) {f : H → E} {g : H → F} {n : ℕ} {s : set H} {x : H}
  (hf : cont_diff_on 𝕜 n f s) (hg : cont_diff_on 𝕜 n g s) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  ‖iterated_fderiv_within 𝕜 n (λ y, B (f y) (g y)) s x‖
  ≤ ‖B‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i f s x‖ * ‖iterated_fderiv_within 𝕜 (n-i) g s x‖ :=
begin
  let Eu : Type (max uE uF uG uH) := ulift E,
  let Fu : Type (max uE uF uG uH) := ulift.{(max uE uG uH) uF} F,
  let Gu : Type (max uE uF uG uH) := ulift.{(max uE uF uH) uG} G,
  let Hu : Type (max uE uF uG uH) := ulift.{(max uE uF uG) uH} H,
  have isoE : Eu ≃ₗᵢ[𝕜] E := linear_isometry_equiv.ulift 𝕜 E,
  have isoF : Fu ≃ₗᵢ[𝕜] F := linear_isometry_equiv.ulift 𝕜 F,
  have isoG : Gu ≃ₗᵢ[𝕜] G := linear_isometry_equiv.ulift 𝕜 G,
  have isoH : Hu ≃ₗᵢ[𝕜] H := linear_isometry_equiv.ulift 𝕜 H,
  let fu : Hu → Eu := isoE.symm ∘ f ∘ isoH,
  let gu : Hu → Fu := isoF.symm ∘ g ∘ isoH,
  let Bu : Eu →L[𝕜] Fu →L[𝕜] Gu, sorry,
  let su := isoH ⁻¹' s,
  have hsu : unique_diff_on 𝕜 su,
    from isoH.to_continuous_linear_equiv.unique_diff_on_preimage_iff.2 hs,
  let xu := isoH.symm x,
  have hxu : xu ∈ su,
    by simpa only [set.mem_preimage, linear_isometry_equiv.apply_symm_apply] using hx,
  have hfu : cont_diff_on 𝕜 n fu su,
    from isoE.symm.cont_diff.comp_cont_diff_on (hf.comp_continuous_linear_map (isoH : Hu →L[𝕜] H)),
  have hgu : cont_diff_on 𝕜 n gu su,
    from isoF.symm.cont_diff.comp_cont_diff_on (hg.comp_continuous_linear_map (isoH : Hu →L[𝕜] H)),
  have : ∀ i ≤ n, ‖iterated_fderiv_within 𝕜 i fu su xu‖ = ‖iterated_fderiv_within 𝕜 i f s x‖,
  { assume i hi,
    simp [fu],

  },

  have : ‖iterated_fderiv_within 𝕜 n (λ y, Bu (fu y) (gu y)) su xu‖
    ≤ ‖Bu‖ * ∑ i in finset.range (n+1), (n.choose i : ℝ)
      * ‖iterated_fderiv_within 𝕜 i fu su xu‖ * ‖iterated_fderiv_within 𝕜 (n-i) gu su xu‖,
    from Bu.norm_iterated_fderiv_within_le_of_bilinear_aux hfu hgu hsu hxu,

end

#exit

  let eG : Type (max uG uE' uF uP) := ulift G,
  borelize eG,
  let eE' : Type (max uE' uG uF uP) := ulift E',
  let eF : Type (max uF uG uE' uP) := ulift F,
  let eP : Type (max uP uG uE' uF) := ulift P,
  have isoG : eG ≃L[𝕜] G := continuous_linear_equiv.ulift,
  have isoE' : eE' ≃L[𝕜] E' := continuous_linear_equiv.ulift,
  have isoF : eF ≃L[𝕜] F := continuous_linear_equiv.ulift,
  have isoP : eP ≃L[𝕜] P := continuous_linear_equiv.ulift,
  let ef := f ∘ isoG,
  let eμ : measure eG := measure.map isoG.symm μ,
  let eg : eP → eG → eE' := λ ep ex, isoE'.symm (g (isoP ep) (isoG ex)),
  let eL := continuous_linear_map.comp
    ((continuous_linear_equiv.arrow_congr isoE' isoF).symm : (E' →L[𝕜] F) →L[𝕜] eE' →L[𝕜] eF) L,
  let R := (λ (q : eP × eG), (ef ⋆[eL, eμ] eg q.1) q.2),
  have R_contdiff : cont_diff_on 𝕜 n R ((isoP ⁻¹' s) ×ˢ univ),
  { have hek : is_compact (isoG ⁻¹' k),
      from isoG.to_homeomorph.closed_embedding.is_compact_preimage hk,
    have hes : is_open (isoP ⁻¹' s), from isoP.continuous.is_open_preimage _ hs,
    refine cont_diff_on_convolution_right_with_param_aux eL hes hek _ _ _,
    { assume p x hp hx,
      simp only [comp_app, continuous_linear_equiv.prod_apply, linear_isometry_equiv.coe_coe,
        continuous_linear_equiv.map_eq_zero_iff],
      exact hgs _ _ hp hx },
    { apply (locally_integrable_map_homeomorph isoG.symm.to_homeomorph).2,
      convert hf,
      ext1 x,
      simp only [ef, continuous_linear_equiv.coe_to_homeomorph, comp_app,
        continuous_linear_equiv.apply_symm_apply], },
    { apply isoE'.symm.cont_diff.comp_cont_diff_on,
      apply hg.comp ((isoP.prod isoG).cont_diff).cont_diff_on,
      rintros ⟨p, x⟩ ⟨hp, hx⟩,
      simpa only [mem_preimage, continuous_linear_equiv.prod_apply, prod_mk_mem_set_prod_eq,
        mem_univ, and_true] using hp } },
  have A : cont_diff_on 𝕜 n (isoF ∘ R ∘ (isoP.prod isoG).symm) (s ×ˢ univ),
  { apply isoF.cont_diff.comp_cont_diff_on,
    apply R_contdiff.comp (continuous_linear_equiv.cont_diff _).cont_diff_on,
    rintros ⟨p, x⟩ ⟨hp, hx⟩,
    simpa only [mem_preimage, mem_prod, mem_univ, and_true, continuous_linear_equiv.prod_symm,
      continuous_linear_equiv.prod_apply, continuous_linear_equiv.apply_symm_apply] using hp },
  have : isoF ∘ R ∘ (isoP.prod isoG).symm = (λ (q : P × G), (f ⋆[L, μ] g q.1) q.2),
  { apply funext,
    rintros ⟨p, x⟩,
    simp only [R, linear_isometry_equiv.coe_coe, comp_app, continuous_linear_equiv.prod_symm,
      continuous_linear_equiv.prod_apply],
    simp only [convolution, eL, coe_comp', continuous_linear_equiv.coe_coe, comp_app, eμ],
    rw [closed_embedding.integral_map, ← isoF.integral_comp_comm],
    swap, { exact isoG.symm.to_homeomorph.closed_embedding },
    congr' 1,
    ext1 a,
    simp only [ef, eg, comp_app, continuous_linear_equiv.apply_symm_apply, coe_comp',
      continuous_linear_equiv.prod_apply, continuous_linear_equiv.map_sub,
      continuous_linear_equiv.arrow_congr, continuous_linear_equiv.arrow_congrSL_symm_apply,
      continuous_linear_equiv.coe_coe, comp_app, continuous_linear_equiv.apply_symm_apply] },
  simp_rw [this] at A,
  exact A,
end

lemma glou {E : Type*} [inner_product_space ℝ E] (k n : ℕ) :
  cont_diff ℝ ⊤ (λ (y : E), real.exp (- ‖y‖^2)) :=
cont_diff_norm_sq.neg.exp


lemma glou {E : Type*} [inner_product_space ℝ E] (k n : ℕ) :
  ‖iterated_fderiv ℝ n (λ y, real.exp (- ‖y‖^2)) x‖ ≤ 1 :=
begin
  induction n with n IH,
  sorry,
  refine ⟨1, λ x, _⟩,
  rw nat.succ_eq_add_one,
  simp_rw [iterated_fderiv_succ_eq_comp_right],
  simp,

end


#exit


variables {𝕜 𝕜' E F : Type*}

variables [normed_add_comm_group E] [normed_space ℝ E]
variables [normed_add_comm_group F] [normed_space ℝ F]

variables (E F)

/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of `‖x‖`. -/
structure schwartz_map :=
  (to_fun : E → F)
  (smooth' : cont_diff ℝ ⊤ to_fun)
  (decay' : ∀ (k n : ℕ), ∃ (C : ℝ), ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n to_fun x‖ ≤ C)

localized "notation `𝓢(` E `, ` F `)` := schwartz_map E F" in schwartz_space

variables {E F}

namespace schwartz_map

instance : has_coe 𝓢(E, F) (E → F) := ⟨to_fun⟩

instance fun_like : fun_like 𝓢(E, F) E (λ _, F) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : has_coe_to_fun 𝓢(E, F) (λ _, E → F) := ⟨λ p, p.to_fun⟩

/-- All derivatives of a Schwartz function are rapidly decaying. -/
lemma decay (f : 𝓢(E, F)) (k n : ℕ) : ∃ (C : ℝ) (hC : 0 < C),
  ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ C :=
begin
  rcases f.decay' k n with ⟨C, hC⟩,
  exact ⟨max C 1, by positivity, λ x, (hC x).trans (le_max_left _ _)⟩,
end

/-- Every Schwartz function is smooth. -/
lemma smooth (f : 𝓢(E, F)) (n : ℕ∞) : cont_diff ℝ n f := f.smooth'.of_le le_top

/-- Every Schwartz function is continuous. -/
@[continuity, protected] lemma continuous (f : 𝓢(E, F)) : continuous f := (f.smooth 0).continuous

/-- Every Schwartz function is differentiable. -/
@[protected] lemma differentiable (f : 𝓢(E, F)) : differentiable ℝ f :=
(f.smooth 1).differentiable rfl.le

@[ext] lemma ext {f g : 𝓢(E, F)} (h : ∀ x, (f : E → F) x = g x) : f = g := fun_like.ext f g h

section is_O

variables (f : 𝓢(E, F))

/-- Auxiliary lemma, used in proving the more general result `is_O_cocompact_zpow`. -/
lemma is_O_cocompact_zpow_neg_nat (k : ℕ) :
  asymptotics.is_O (filter.cocompact E) f (λ x, ‖x‖ ^ (-k : ℤ)) :=
begin
  obtain ⟨d, hd, hd'⟩ := f.decay k 0,
  simp_rw norm_iterated_fderiv_zero at hd',
  simp_rw [asymptotics.is_O, asymptotics.is_O_with],
  refine ⟨d, filter.eventually.filter_mono filter.cocompact_le_cofinite _⟩,
  refine (filter.eventually_cofinite_ne 0).mp (filter.eventually_of_forall (λ x hx, _)),
  rwa [real.norm_of_nonneg (zpow_nonneg (norm_nonneg _) _), zpow_neg, ←div_eq_mul_inv, le_div_iff'],
  exacts [hd' x, zpow_pos_of_pos (norm_pos_iff.mpr hx) _],
end

lemma is_O_cocompact_rpow [proper_space E] (s : ℝ) :
  asymptotics.is_O (filter.cocompact E) f (λ x, ‖x‖ ^ s) :=
begin
  let k := ⌈-s⌉₊,
  have hk : -(k : ℝ) ≤ s, from neg_le.mp (nat.le_ceil (-s)),
  refine (is_O_cocompact_zpow_neg_nat f k).trans _,
  refine (_ : asymptotics.is_O filter.at_top
    (λ x:ℝ, x ^ (-k : ℤ)) (λ x:ℝ, x ^ s)).comp_tendsto tendsto_norm_cocompact_at_top,
  simp_rw [asymptotics.is_O, asymptotics.is_O_with],
  refine ⟨1, filter.eventually_of_mem (filter.eventually_ge_at_top 1) (λ x hx, _)⟩,
  rw [one_mul, real.norm_of_nonneg (real.rpow_nonneg_of_nonneg (zero_le_one.trans hx) _),
    real.norm_of_nonneg (zpow_nonneg (zero_le_one.trans hx) _), ←real.rpow_int_cast, int.cast_neg,
    int.cast_coe_nat],
  exact real.rpow_le_rpow_of_exponent_le hx hk,
end

lemma is_O_cocompact_zpow [proper_space E] (k : ℤ) :
  asymptotics.is_O (filter.cocompact E) f (λ x, ‖x‖ ^ k) :=
by simpa only [real.rpow_int_cast] using is_O_cocompact_rpow f k

end is_O

section aux

lemma bounds_nonempty (k n : ℕ) (f : 𝓢(E, F)) :
  ∃ (c : ℝ), c ∈ {c : ℝ | 0 ≤ c ∧ ∀ (x : E), ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ c} :=
let ⟨M, hMp, hMb⟩ := f.decay k n in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below (k n : ℕ) (f : 𝓢(E, F)) :
  bdd_below {c | 0 ≤ c ∧ ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ c} :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma decay_add_le_aux (k n : ℕ) (f g : 𝓢(E, F)) (x : E) :
  ‖x‖^k * ‖iterated_fderiv ℝ n (f+g) x‖ ≤
  ‖x‖^k * ‖iterated_fderiv ℝ n f x‖
  + ‖x‖^k * ‖iterated_fderiv ℝ n g x‖ :=
begin
  rw ←mul_add,
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  convert norm_add_le _ _,
  exact iterated_fderiv_add_apply (f.smooth _) (g.smooth _),
end

lemma decay_neg_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
  ‖x‖ ^ k * ‖iterated_fderiv ℝ n (-f) x‖ = ‖x‖ ^ k * ‖iterated_fderiv ℝ n f x‖ :=
begin
  nth_rewrite 3 ←norm_neg,
  congr,
  exact iterated_fderiv_neg_apply,
end

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]

lemma decay_smul_aux (k n : ℕ) (f : 𝓢(E, F)) (c : 𝕜) (x : E) :
  ‖x‖ ^ k * ‖iterated_fderiv ℝ n (c • f) x‖ =
  ‖c‖ * ‖x‖ ^ k * ‖iterated_fderiv ℝ n f x‖ :=
by rw [mul_comm (‖c‖), mul_assoc, iterated_fderiv_const_smul_apply (f.smooth _), norm_smul]

end aux

section seminorm_aux

/-- Helper definition for the seminorms of the Schwartz space. -/
@[protected]
def seminorm_aux (k n : ℕ) (f : 𝓢(E, F)) : ℝ :=
Inf {c | 0 ≤ c ∧ ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ c}

lemma seminorm_aux_nonneg (k n : ℕ) (f : 𝓢(E, F)) : 0 ≤ f.seminorm_aux k n :=
le_cInf (bounds_nonempty k n f) (λ _ ⟨hx, _⟩, hx)

lemma le_seminorm_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
  ‖x‖ ^ k * ‖iterated_fderiv ℝ n ⇑f x‖ ≤ f.seminorm_aux k n :=
le_cInf (bounds_nonempty k n f) (λ y ⟨_, h⟩, h x)

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma seminorm_aux_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp: 0 ≤ M)
  (hM : ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ M) :
  f.seminorm_aux k n ≤ M :=
cInf_le (bounds_bdd_below k n f) ⟨hMp, hM⟩

end seminorm_aux

/-! ### Algebraic properties -/

section smul

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]
  [normed_field 𝕜'] [normed_space 𝕜' F] [smul_comm_class ℝ 𝕜' F]

instance : has_smul 𝕜 𝓢(E, F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := (f.smooth _).const_smul c,
  decay' := λ k n, begin
    refine ⟨f.seminorm_aux k n * (‖c‖+1), λ x, _⟩,
    have hc : 0 ≤ ‖c‖ := by positivity,
    refine le_trans _ ((mul_le_mul_of_nonneg_right (f.le_seminorm_aux k n x) hc).trans _),
    { apply eq.le,
      rw [mul_comm _ (‖c‖), ← mul_assoc],
      exact decay_smul_aux k n f c x },
    { apply mul_le_mul_of_nonneg_left _ (f.seminorm_aux_nonneg k n),
      linarith }
  end}⟩

@[simp] lemma smul_apply {f : 𝓢(E, F)} {c : 𝕜} {x : E} : (c • f) x = c • (f x) := rfl

instance
[has_smul 𝕜 𝕜'] [is_scalar_tower 𝕜 𝕜' F] : is_scalar_tower 𝕜 𝕜' 𝓢(E, F) :=
⟨λ a b f, ext $ λ x, smul_assoc a b (f x)⟩

instance [smul_comm_class 𝕜 𝕜' F] : smul_comm_class 𝕜 𝕜' 𝓢(E, F) :=
⟨λ a b f, ext $ λ x, smul_comm a b (f x)⟩

lemma seminorm_aux_smul_le (k n : ℕ) (c : 𝕜) (f : 𝓢(E, F)) :
  (c • f).seminorm_aux k n ≤ ‖c‖ * f.seminorm_aux k n :=
begin
  refine (c • f).seminorm_aux_le_bound k n (mul_nonneg (norm_nonneg _) (seminorm_aux_nonneg _ _ _))
    (λ x, (decay_smul_aux k n f c x).le.trans _),
  rw mul_assoc,
  exact mul_le_mul_of_nonneg_left (f.le_seminorm_aux k n x) (norm_nonneg _),
end

instance has_nsmul : has_smul ℕ 𝓢(E, F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := (f.smooth _).const_smul c,
  decay' := begin
    have : c • (f : E → F) = (c : ℝ) • f,
    { ext x, simp only [pi.smul_apply, ← nsmul_eq_smul_cast] },
    simp only [this],
    exact ((c : ℝ) • f).decay',
  end}⟩

instance has_zsmul : has_smul ℤ 𝓢(E, F) :=
⟨λ c f, { to_fun := c • f,
  smooth' := (f.smooth _).const_smul c,
  decay' := begin
    have : c • (f : E → F) = (c : ℝ) • f,
    { ext x, simp only [pi.smul_apply, ← zsmul_eq_smul_cast] },
    simp only [this],
    exact ((c : ℝ) • f).decay',
  end}⟩

end smul

section zero

instance : has_zero 𝓢(E, F) :=
⟨{ to_fun := λ _, 0,
  smooth' := cont_diff_const,
  decay' := λ _ _, ⟨1, λ _, by simp⟩ }⟩

instance : inhabited 𝓢(E, F) := ⟨0⟩

lemma coe_zero : ↑(0 : 𝓢(E, F)) = (0 : E → F) := rfl

@[simp] lemma coe_fn_zero : coe_fn (0 : 𝓢(E, F)) = (0 : E → F) := rfl

@[simp] lemma zero_apply {x : E} : (0 : 𝓢(E, F)) x = 0 := rfl

lemma seminorm_aux_zero (k n : ℕ) :
  (0 : 𝓢(E, F)).seminorm_aux k n = 0 :=
le_antisymm (seminorm_aux_le_bound k n _ rfl.le (λ _, by simp [pi.zero_def]))
  (seminorm_aux_nonneg _ _ _)

end zero

section neg

instance : has_neg 𝓢(E, F) :=
⟨λ f, ⟨-f, (f.smooth _).neg, λ k n,
  ⟨f.seminorm_aux k n, λ x, (decay_neg_aux k n f x).le.trans (f.le_seminorm_aux k n x)⟩⟩⟩

end neg

section add

instance : has_add 𝓢(E, F) :=
⟨λ f g, ⟨f + g, (f.smooth _).add (g.smooth _), λ k n,
  ⟨f.seminorm_aux k n + g.seminorm_aux k n, λ x, (decay_add_le_aux k n f g x).trans
    (add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x))⟩⟩⟩

@[simp] lemma add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x := rfl

lemma seminorm_aux_add_le (k n : ℕ) (f g : 𝓢(E, F)) :
  (f + g).seminorm_aux k n ≤ f.seminorm_aux k n + g.seminorm_aux k n :=
(f + g).seminorm_aux_le_bound k n
  (add_nonneg (seminorm_aux_nonneg _ _ _) (seminorm_aux_nonneg _ _ _)) $
  λ x, (decay_add_le_aux k n f g x).trans $
  add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x)

end add

section sub

instance : has_sub 𝓢(E, F) :=
⟨λ f g, ⟨f - g, (f.smooth _).sub (g.smooth _),
  begin
    intros k n,
    refine ⟨f.seminorm_aux k n + g.seminorm_aux k n, λ x, _⟩,
    refine le_trans _ (add_le_add (f.le_seminorm_aux k n x) (g.le_seminorm_aux k n x)),
    rw sub_eq_add_neg,
    rw ←decay_neg_aux k n g x,
    convert decay_add_le_aux k n f (-g) x,
    -- exact fails with deterministic timeout
  end⟩ ⟩

@[simp] lemma sub_apply {f g : 𝓢(E, F)} {x : E} : (f - g) x = f x - g x := rfl

end sub

section add_comm_group

instance : add_comm_group 𝓢(E, F) :=
fun_like.coe_injective.add_comm_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
  (λ _ _, rfl)

variables (E F)

/-- Coercion as an additive homomorphism. -/
def coe_hom : 𝓢(E, F) →+ (E → F) :=
{ to_fun := λ f, f, map_zero' := coe_zero, map_add' := λ _ _, rfl }

variables {E F}

lemma coe_coe_hom : (coe_hom E F : 𝓢(E, F) → (E → F)) = coe_fn := rfl

lemma coe_hom_injective : function.injective (coe_hom E F) :=
by { rw coe_coe_hom, exact fun_like.coe_injective }

end add_comm_group

section module

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]

instance : module 𝕜 𝓢(E, F) :=
coe_hom_injective.module 𝕜 (coe_hom E F) (λ _ _, rfl)

end module

section seminorms

/-! ### Seminorms on Schwartz space-/

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]
variable (𝕜)

/-- The seminorms of the Schwartz space given by the best constants in the definition of
`𝓢(E, F)`. -/
@[protected]
def seminorm (k n : ℕ) : seminorm 𝕜 𝓢(E, F) := seminorm.of_smul_le (seminorm_aux k n)
  (seminorm_aux_zero k n) (seminorm_aux_add_le k n) (seminorm_aux_smul_le k n)

/-- If one controls the seminorm for every `x`, then one controls the seminorm. -/
lemma seminorm_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp: 0 ≤ M)
  (hM : ∀ x, ‖x‖^k * ‖iterated_fderiv ℝ n f x‖ ≤ M) : seminorm 𝕜 k n f ≤ M :=
f.seminorm_aux_le_bound k n hMp hM

/-- The seminorm controls the Schwartz estimate for any fixed `x`. -/
lemma le_seminorm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
  ‖x‖ ^ k * ‖iterated_fderiv ℝ n f x‖ ≤ seminorm 𝕜 k n f :=
f.le_seminorm_aux k n x

lemma norm_iterated_fderiv_le_seminorm (f : 𝓢(E, F)) (n : ℕ) (x₀ : E) :
  ‖iterated_fderiv ℝ n f x₀‖ ≤ (schwartz_map.seminorm 𝕜 0 n) f :=
begin
  have := schwartz_map.le_seminorm 𝕜 0 n f x₀,
  rwa [pow_zero, one_mul] at this,
end

lemma norm_pow_mul_le_seminorm (f : 𝓢(E, F)) (k : ℕ) (x₀ : E) :
  ‖x₀‖^k * ‖f x₀‖ ≤ (schwartz_map.seminorm 𝕜 k 0) f :=
begin
  have := schwartz_map.le_seminorm 𝕜 k 0 f x₀,
  rwa norm_iterated_fderiv_zero at this,
end

lemma norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) :
  ‖f x₀‖ ≤ (schwartz_map.seminorm 𝕜 0 0) f :=
begin
  have := norm_pow_mul_le_seminorm 𝕜 f 0 x₀,
  rwa [pow_zero, one_mul] at this,
end

end seminorms

section topology

/-! ### The topology on the Schwartz space-/

variables [normed_field 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]
variables (𝕜 E F)

/-- The family of Schwartz seminorms. -/
def _root_.schwartz_seminorm_family : seminorm_family 𝕜 𝓢(E, F) (ℕ × ℕ) :=
λ n, seminorm 𝕜 n.1 n.2

@[simp] lemma schwartz_seminorm_family_apply (n k : ℕ) :
  schwartz_seminorm_family 𝕜 E F (n,k) = schwartz_map.seminorm 𝕜 n k := rfl

@[simp] lemma schwartz_seminorm_family_apply_zero :
  schwartz_seminorm_family 𝕜 E F 0 = schwartz_map.seminorm 𝕜 0 0 := rfl

instance : topological_space 𝓢(E, F) :=
(schwartz_seminorm_family ℝ E F).module_filter_basis.topology'

lemma _root_.schwartz_with_seminorms : with_seminorms (schwartz_seminorm_family 𝕜 E F) :=
begin
  have A : with_seminorms (schwartz_seminorm_family ℝ E F) := ⟨rfl⟩,
  rw seminorm_family.with_seminorms_iff_nhds_eq_infi at ⊢ A,
  rw A,
  refl
end

variables {𝕜 E F}

instance : has_continuous_smul 𝕜 𝓢(E, F) :=
begin
  rw (schwartz_with_seminorms 𝕜 E F).with_seminorms_eq,
  exact (schwartz_seminorm_family 𝕜 E F).module_filter_basis.has_continuous_smul,
end

instance : topological_add_group 𝓢(E, F) :=
(schwartz_seminorm_family ℝ E F).add_group_filter_basis.is_topological_add_group

instance : uniform_space 𝓢(E, F) :=
(schwartz_seminorm_family ℝ E F).add_group_filter_basis.uniform_space

instance : uniform_add_group 𝓢(E, F) :=
(schwartz_seminorm_family ℝ E F).add_group_filter_basis.uniform_add_group

instance : locally_convex_space ℝ 𝓢(E, F) :=
(schwartz_with_seminorms ℝ E F).to_locally_convex_space

instance : topological_space.first_countable_topology (𝓢(E, F)) :=
(schwartz_with_seminorms ℝ E F).first_countable

end topology

section fderiv

/-! ### Derivatives of Schwartz functions -/

variables {E F}

/-- The derivative of a Schwartz function as a Schwartz function with values in the
continuous linear maps `E→L[ℝ] F`. -/
@[protected] def fderiv (f : 𝓢(E, F)) : 𝓢(E, E →L[ℝ] F) :=
{ to_fun := fderiv ℝ f,
  smooth' := (cont_diff_top_iff_fderiv.mp f.smooth').2,
  decay' :=
  begin
    intros k n,
    cases f.decay' k (n+1) with C hC,
    use C,
    intros x,
    rw norm_iterated_fderiv_fderiv,
    exact hC x,
  end }

@[simp, norm_cast] lemma coe_fderiv (f : 𝓢(E, F)) : ⇑f.fderiv = fderiv ℝ f := rfl
@[simp] lemma fderiv_apply (f : 𝓢(E, F)) (x : E) : f.fderiv x = fderiv ℝ f x := rfl

variables (𝕜)
variables [is_R_or_C 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]

/-- The derivative on Schwartz space as a linear map. -/
def fderiv_lm : 𝓢(E, F) →ₗ[𝕜] 𝓢(E, E →L[ℝ] F) :=
{ to_fun := schwartz_map.fderiv,
  map_add' := λ f g, ext $ λ _, fderiv_add
    f.differentiable.differentiable_at
    g.differentiable.differentiable_at,
  map_smul' := λ a f, ext $ λ _, fderiv_const_smul f.differentiable.differentiable_at a }

@[simp, norm_cast] lemma fderiv_lm_apply (f : 𝓢(E, F)) : fderiv_lm 𝕜 f = schwartz_map.fderiv f :=
rfl

/-- The derivative on Schwartz space as a continuous linear map. -/
def fderiv_clm : 𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F) :=
{ cont :=
  begin
    change continuous (fderiv_lm 𝕜 : 𝓢(E, F) →ₗ[𝕜] 𝓢(E, E →L[ℝ] F)),
    refine seminorm.continuous_from_bounded (schwartz_with_seminorms 𝕜 E F)
      (schwartz_with_seminorms 𝕜 E (E →L[ℝ] F)) _ _,
    rintros ⟨k, n⟩,
    use [{⟨k, n+1⟩}, 1, one_ne_zero],
    intros f,
    simp only [schwartz_seminorm_family_apply, seminorm.comp_apply, finset.sup_singleton, one_smul],
    refine (fderiv_lm 𝕜 f).seminorm_le_bound 𝕜 k n (by positivity) _,
    intros x,
    rw [fderiv_lm_apply, coe_fderiv, norm_iterated_fderiv_fderiv],
    exact f.le_seminorm 𝕜 k (n+1) x,
  end,
  to_linear_map := fderiv_lm 𝕜 }

@[simp, norm_cast] lemma fderiv_clm_apply (f : 𝓢(E, F)) : fderiv_clm 𝕜 f = schwartz_map.fderiv f :=
rfl

end fderiv

section bounded_continuous_function

/-! ### Inclusion into the space of bounded continuous functions -/

open_locale bounded_continuous_function

/-- Schwartz functions as bounded continuous functions -/
def to_bounded_continuous_function (f : 𝓢(E, F)) : E →ᵇ F :=
bounded_continuous_function.of_normed_add_comm_group f (schwartz_map.continuous f)
  (schwartz_map.seminorm ℝ 0 0 f) (norm_le_seminorm ℝ f)

@[simp] lemma to_bounded_continuous_function_apply (f : 𝓢(E, F)) (x : E) :
  f.to_bounded_continuous_function x = f x := rfl

/-- Schwartz functions as continuous functions -/
def to_continuous_map (f : 𝓢(E, F)) : C(E, F) :=
f.to_bounded_continuous_function.to_continuous_map

variables (𝕜 E F)
variables [is_R_or_C 𝕜] [normed_space 𝕜 F] [smul_comm_class ℝ 𝕜 F]

/-- The inclusion map from Schwartz functions to bounded continuous functions as a linear map. -/
def to_bounded_continuous_function_lm : 𝓢(E, F) →ₗ[𝕜] E →ᵇ F :=
{ to_fun := λ f, f.to_bounded_continuous_function,
  map_add' := λ f g, by { ext, exact add_apply },
  map_smul' := λ a f, by { ext, exact smul_apply } }

@[simp] lemma to_bounded_continuous_function_lm_apply (f : 𝓢(E, F)) (x : E) :
  to_bounded_continuous_function_lm 𝕜 E F f x = f x := rfl

/-- The inclusion map from Schwartz functions to bounded continuous functions as a continuous linear
map. -/
def to_bounded_continuous_function_clm : 𝓢(E, F) →L[𝕜] E →ᵇ F :=
{ cont :=
  begin
    change continuous (to_bounded_continuous_function_lm 𝕜 E F),
    refine seminorm.continuous_from_bounded (schwartz_with_seminorms 𝕜 E F)
      (norm_with_seminorms 𝕜 (E →ᵇ F)) _ (λ i, ⟨{0}, 1, one_ne_zero, λ f, _⟩),
    rw [finset.sup_singleton, one_smul , seminorm.comp_apply, coe_norm_seminorm,
        schwartz_seminorm_family_apply_zero, bounded_continuous_function.norm_le (map_nonneg _ _)],
    intros x,
    exact norm_le_seminorm 𝕜 _ _,
  end,
  .. to_bounded_continuous_function_lm 𝕜 E F}

@[simp] lemma to_bounded_continuous_function_clm_apply (f : 𝓢(E, F)) (x : E) :
  to_bounded_continuous_function_clm 𝕜 E F f x = f x := rfl

variables {E}

/-- The Dirac delta distribution -/
def delta (x : E) : 𝓢(E, F) →L[𝕜] F :=
(bounded_continuous_function.eval_clm 𝕜 x).comp (to_bounded_continuous_function_clm 𝕜 E F)

@[simp] lemma delta_apply (x₀ : E) (f : 𝓢(E, F)) : delta 𝕜 F x₀ f = f x₀ := rfl

end bounded_continuous_function

end schwartz_map
