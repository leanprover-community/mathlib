/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import tactic.induction
import analysis.normed_space.basic
import analysis.normed_space.finite_dimension
import measure_theory.measure.haar_lebesgue

/-!
# Besicovitch covering lemma

We prove the Besicovitch covering lemma.

-/

universe u
open metric set finite_dimensional measure_theory filter

open_locale ennreal topological_space

lemma ball_subset_ball' {E : Type*} [normed_group E]
  (x y : E) (rx ry : ℝ) (h : rx + dist x y ≤ ry) :
  ball x rx ⊆ ball y ry :=
begin
  assume z hz,
  calc dist z y ≤ dist z x + dist x y : dist_triangle _ _ _
  ... < rx + dist x y : add_lt_add_right hz _
  ... ≤ ry : h
end

namespace ennreal

@[simp, norm_cast] lemma to_nnreal_nat (n : ℕ) : (n : ℝ≥0∞).to_nnreal = n :=
by conv_lhs { rw [← ennreal.coe_nat n, ennreal.to_nnreal_coe] }

@[simp, norm_cast] lemma to_real_nat (n : ℕ) : (n : ℝ≥0∞).to_real = n :=
by conv_lhs { rw [← ennreal.of_real_coe_nat n, ennreal.to_real_of_real (nat.cast_nonneg _)] }

end ennreal

namespace fin

lemma exists_injective_of_le_card_fintype
  {α : Type*} [fintype α] {k : ℕ} (hk : k ≤ fintype.card α) :
  ∃ (f : fin k → α), function.injective f :=
⟨_, (fintype.equiv_fin α).symm.injective.comp (fin.cast_le hk).injective⟩

lemma exists_injective_of_le_card_finset {α : Type*} {s : finset α} {k : ℕ} (hk : k ≤ s.card) :
  ∃ (f : fin k → α), function.injective f ∧ range f ⊆ s :=
begin
  rw ← fintype.card_coe at hk,
  rcases fin.exists_injective_of_le_card_fintype hk with ⟨f, hf⟩,
  exact ⟨(λ x, (f x : α)), function.injective.comp subtype.coe_injective hf,
    by simp [range_subset_iff]⟩
end

end fin

noncomputable theory

namespace besicovitch

def multiplicity (E : Type*) [normed_group E] :=
Sup {N | ∃ s : finset E, s.card = N ∧ (∀ c ∈ s, ∥c∥ ≤ 2) ∧ (∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ∥c - d∥)}

variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]

lemma card_le_of_separated
  (s : finset E) (hs : ∀ c ∈ s, ∥c∥ ≤ 2) (h : ∀ (c ∈ s) (d ∈ s), c ≠ d → 1 ≤ ∥c - d∥) :
  s.card ≤ 5 ^ (finrank ℝ E) :=
begin
  /- We consider balls of radius `1/2` around the points in `s`. They are disjoint, and all
  contained in the ball of radius `5/2`. A volume argument gives `s.card * (1/2)^dim ≤ (5/2)^dim`,
  i.e., `s.card ≤ 5^dim`. -/
  letI : measurable_space E := borel E,
  letI : borel_space E := ⟨rfl⟩,
  let μ : measure E := measure.add_haar,
  let δ : ℝ := (1 : ℝ)/2,
  let ρ : ℝ := (5 : ℝ)/2,
  have ρpos : 0 < ρ := by norm_num [ρ],
  set A := ⋃ (c ∈ s), ball (c : E) δ with hA,
  have D : set.pairwise_on (s : set E) (disjoint on (λ c, ball (c : E) δ)),
  { rintros c hc d hd hcd,
    apply ball_disjoint_ball,
    rw dist_eq_norm,
    convert h c hc d hd hcd,
    norm_num },
  have A_subset : A ⊆ ball (0 : E) ρ,
  { refine bUnion_subset (λ x hx, _),
    apply ball_subset_ball',
    calc δ + dist x 0 ≤ δ + 2 : by { rw dist_zero_right, exact add_le_add le_rfl (hs x hx) }
    ... = 5 / 2 : by norm_num [δ] },
  have I : (s.card : ℝ≥0∞) * ennreal.of_real (δ ^ (finrank ℝ E)) * μ (ball 0 1) ≤
    ennreal.of_real (ρ ^ (finrank ℝ E)) * μ (ball 0 1) := calc
  (s.card : ℝ≥0∞) * ennreal.of_real (δ ^ (finrank ℝ E)) * μ (ball 0 1) = μ A :
    begin
      rw [hA, measure_bUnion_finset D (λ c hc, measurable_set_ball)],
      have I : 0 < δ, by norm_num [δ],
      simp only [μ.add_haar_ball_of_pos _ I, one_div, one_pow, finset.sum_const,
        nsmul_eq_mul, div_pow, mul_assoc]
    end
  ... ≤ μ (ball (0 : E) ρ) : measure_mono A_subset
  ... = ennreal.of_real (ρ ^ (finrank ℝ E)) * μ (ball 0 1) :
    by simp only [μ.add_haar_ball_of_pos _ ρpos],
  have J : (s.card : ℝ≥0∞) * ennreal.of_real (δ ^ (finrank ℝ E))
    ≤ ennreal.of_real (ρ ^ (finrank ℝ E)) :=
      (ennreal.mul_le_mul_right (μ.add_haar_ball_pos _ zero_lt_one).ne'
        (μ.add_haar_ball_lt_top _ _).ne).1 I,
  have K : (s.card : ℝ) ≤ (5 : ℝ) ^ finrank ℝ E,
    by simpa [ennreal.to_real_mul, div_eq_mul_inv] using
      ennreal.to_real_le_of_le_of_real (pow_nonneg ρpos.le _) J,
  exact_mod_cast K,
end

lemma multiplicity_le : multiplicity E ≤ 5 ^ (finrank ℝ E) :=
begin
  apply cSup_le,
  { refine ⟨0, ⟨∅, by simp⟩⟩ },
  { rintros _ ⟨s, ⟨rfl, h⟩⟩,
    exact besicovitch.card_le_of_separated s h.1 h.2 }
end

lemma card_le_multiplicity
  {s : finset E} (hs : ∀ c ∈ s, ∥c∥ ≤ 2) (h's : ∀ (c ∈ s) (d ∈ s), c ≠ d → 1 ≤ ∥c - d∥) :
  s.card ≤ multiplicity E :=
begin
  apply le_cSup,
  { refine ⟨5 ^ (finrank ℝ E), _⟩,
    rintros _ ⟨s, ⟨rfl, h⟩⟩,
    exact besicovitch.card_le_of_separated s h.1 h.2 },
  { simp only [mem_set_of_eq, ne.def],
    exact ⟨s, rfl, hs, h's⟩ }
end

variable (E)
lemma exists_good_δ : ∃ (δ : ℝ), 0 < δ ∧ δ ≤ 1 ∧ ∀ (s : finset E), (∀ c ∈ s, ∥c∥ ≤ 2) →
  (∀ (c ∈ s) (d ∈ s), c ≠ d → 1 - δ ≤ ∥c - d∥) → s.card ≤ multiplicity E :=
begin
  classical,
  by_contradiction h,
  push_neg at h,
  set N := multiplicity E + 1 with hN,
  have : ∀ (δ : ℝ), 0 < δ → ∃ f : fin N → E, (∀ (i : fin N), ∥f i∥ ≤ 2)
    ∧ (∀ i j, i ≠ j → 1 - δ ≤ ∥f i - f j∥),
  { assume δ hδ,
    rcases le_total δ 1 with hδ'|hδ',
    { rcases h δ hδ hδ' with ⟨s, hs, h's, s_card⟩,
      obtain ⟨f, f_inj, hfs⟩ : ∃ (f : fin N → E), function.injective f ∧ range f ⊆ ↑s :=
        fin.exists_injective_of_le_card_finset s_card,
      simp only [range_subset_iff, finset.mem_coe] at hfs,
      refine ⟨f, λ i, hs _ (hfs i), λ i j hij, h's _ (hfs i) _ (hfs j) (f_inj.ne hij)⟩ },
    { exact ⟨λ i, 0, λ i, by simp, λ i j hij, by simpa only [norm_zero, sub_nonpos, sub_self]⟩ } },
  choose! F hF using this,
  have : ∃ f : fin N → E, (∀ (i : fin N), ∥f i∥ ≤ 2) ∧ (∀ i j, i ≠ j → 1 ≤ ∥f i - f j∥),
  { obtain ⟨u, u_mono, zero_lt_u, hu⟩ : ∃ (u : ℕ → ℝ), (∀ (m n : ℕ), m < n → u n < u m)
      ∧ (∀ (n : ℕ), 0 < u n) ∧ filter.tendsto u filter.at_top (𝓝 0) :=
        exists_seq_strict_antimono_tendsto (0 : ℝ),
    have A : ∀ n, F (u n) ∈ closed_ball (0 : fin N → E) 2,
    { assume n,
      simp only [pi_norm_le_iff zero_le_two, mem_closed_ball, dist_zero_right,
                 (hF (u n) (zero_lt_u n)).left, forall_const], },
    obtain ⟨f, fmem, φ, φ_mono, hf⟩ : ∃ (f ∈ closed_ball (0 : fin N → E) 2) (φ : ℕ → ℕ),
      strict_mono φ ∧ tendsto ((F ∘ u) ∘ φ) at_top (𝓝 f) :=
        is_compact.tendsto_subseq (proper_space.is_compact_closed_ball _ _) A,
    refine ⟨f, λ i, _, λ i j hij, _⟩,
    { simp only [pi_norm_le_iff zero_le_two, mem_closed_ball, dist_zero_right] at fmem,
      exact fmem i },
    { have A : tendsto (λ n, ∥F (u (φ n)) i - F (u (φ n)) j∥) at_top (𝓝 (∥f i - f j∥)) :=
        ((hf.apply i).sub (hf.apply j)).norm,
      have B : tendsto (λ n, 1 - u (φ n)) at_top (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (hu.comp φ_mono.tendsto_at_top),
      rw sub_zero at B,
      exact le_of_tendsto_of_tendsto' B A (λ n, (hF (u (φ n)) (zero_lt_u _)).2 i j hij) } },
  rcases this with ⟨f, hf, h'f⟩,
  have finj : function.injective f,
  { assume i j hij,
    by_contra,
    have : 1 ≤ ∥f i - f j∥ := h'f i j h,
    simp only [hij, norm_zero, sub_self] at this,
    exact lt_irrefl _ (this.trans_lt zero_lt_one) },
  let s := finset.image f finset.univ,
  have s_card : s.card = N,
    by { rw finset.card_image_of_injective _ finj, exact finset.card_fin N },
  have hs : ∀ c ∈ s, ∥c∥ ≤ 2,
    by simp only [hf, forall_apply_eq_imp_iff', forall_const, forall_exists_index, finset.mem_univ,
                  finset.mem_image],
  have h's : ∀ (c ∈ s) (d ∈ s), c ≠ d → 1 ≤ ∥c - d∥,
  { simp only [s, forall_apply_eq_imp_iff', forall_exists_index, finset.mem_univ, finset.mem_image,
      ne.def, exists_true_left, forall_apply_eq_imp_iff', forall_true_left],
    assume i j hij,
    have : i ≠ j := λ h, by { rw h at hij, exact hij rfl },
    exact h'f i j this },
  have : s.card ≤ multiplicity E := card_le_multiplicity hs h's,
  rw [s_card, hN] at this,
  exact lt_irrefl _ ((nat.lt_succ_self (multiplicity E)).trans_le this),
end

def good_δ : ℝ := classical.some (exists_good_δ E)

def good_τ : ℝ := 1 + classical.some (exists_good_δ E) / 4

lemma one_lt_good_τ : 1 < good_τ E :=
by { dsimp [good_τ], linarith [(classical.some_spec (exists_good_δ E)).1] }

lemma card_le_multiplicity_τ {s : finset E} (hs : ∀ c ∈ s, ∥c∥ ≤ 2)
  (h's : ∀ (c ∈ s) (d ∈ s), c ≠ d → 1 - good_δ E ≤ ∥c - d∥) :
  s.card ≤ multiplicity E :=
(classical.some_spec (exists_good_δ E)).2.2 s hs h's

open fin

structure satellite_config (N : ℕ) (τ : ℝ) :=
(c : fin N.succ → E)
(r : fin N.succ → ℝ )
(rpos : ∀ i, 0 < r i)
(h : ∀ i j, i ≠ j → (r i ≤ dist (c i) (c j) ∧ r j ≤ τ * r i) ∨
                    (r j ≤ dist (c j) (c i) ∧ r i ≤ τ * r j))
(hlast : ∀ i < last N, r i ≤ dist (c i) (c (last N)) ∧ r (last N) ≤ τ * r i)
(inter : ∀ i < last N, dist (c i) (c (last N)) ≤ r i + r (last N))
(oneτ : 1 ≤ τ)

namespace satellite_config
variables {E} {N : ℕ} {τ : ℝ} (a : satellite_config E N τ)

/-- Rescaling a satellite configuration in a vector space, to put the basepoint at `0` and the base
radius at `1`. -/
def center_and_rescale :
  satellite_config E N τ :=
{ c := λ i, (a.r (last N))⁻¹ • (a.c i - a.c (last N)),
  r := λ i, (a.r (last N))⁻¹ * a.r i,
  rpos := λ i, mul_pos (inv_pos.2 (a.rpos _)) (a.rpos _),
  h := λ i j hij, begin
    rcases a.h i j hij with H|H,
    { left,
      split,
      { rw [dist_eq_norm, ← smul_sub, norm_smul, real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.2 ((a.rpos _)).le)],
        refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ((a.rpos _)).le),
        rw [dist_eq_norm] at H,
        convert H.1 using 2,
        abel },
      { rw [← mul_assoc, mul_comm τ, mul_assoc],
        refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ((a.rpos _)).le),
        exact H.2 } },
    { right,
      split,
      { rw [dist_eq_norm, ← smul_sub, norm_smul, real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.2 ((a.rpos _)).le)],
        refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ((a.rpos _)).le),
        rw [dist_eq_norm] at H,
        convert H.1 using 2,
        abel },
      { rw [← mul_assoc, mul_comm τ, mul_assoc],
        refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ((a.rpos _)).le),
        exact H.2 } },
  end,
  hlast := λ i hi, begin
    have H := a.hlast i hi,
    split,
    { rw [dist_eq_norm, ← smul_sub, norm_smul, real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.2 ((a.rpos _)).le)],
      refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ((a.rpos _)).le),
      rw [dist_eq_norm] at H,
      convert H.1 using 2,
      abel },
    { rw [← mul_assoc, mul_comm τ, mul_assoc],
      refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ((a.rpos _)).le),
      exact H.2 }
  end,
  inter := λ i hi, begin
    have H := a.inter i hi,
    rw [dist_eq_norm, ← smul_sub, norm_smul, real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.2 ((a.rpos _)).le), ← mul_add],
    refine mul_le_mul_of_nonneg_left _ (inv_nonneg.2 ((a.rpos _)).le),
    rw dist_eq_norm at H,
    convert H using 2,
    abel
  end,
  oneτ := a.oneτ }

lemma center_and_rescale_center :
  a.center_and_rescale.c (last N) = 0 :=
by simp [satellite_config.center_and_rescale]

lemma center_and_rescale_radius {N : ℕ} {τ : ℝ} (a : satellite_config E N τ) :
  a.center_and_rescale.r (last N) = 1 :=
by simp [satellite_config.center_and_rescale, inv_mul_cancel (a.rpos _).ne']

lemma inter' (i : fin N.succ) : dist (a.c i) (a.c (last N)) ≤ a.r i + a.r (last N) :=
begin
  rcases lt_or_le i (last N) with H|H,
  { exact a.inter i H },
  { have I : i = last N := top_le_iff.1 H,
    have := (a.rpos (last N)).le,
    simp only [I, add_nonneg this this, dist_self] }
end

lemma hlast' (i : fin N.succ) : a.r (last N) ≤ τ * a.r i :=
begin
  rcases lt_or_le i (last N) with H|H,
  { exact (a.hlast i H).2 },
  { have : i = last N := top_le_iff.1 H,
    rw this,
    exact le_mul_of_one_le_left (a.rpos _).le a.oneτ }
end

lemma exists_normalized_aux1 {N : ℕ} {τ : ℝ} (a : satellite_config E N τ)
  (lastr : a.r (last N) = 1) (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4) (hδ2 : δ ≤ 1)
  (i j : fin N.succ) (inej : i ≠ j) :
  1 - δ ≤ ∥a.c i - a.c j∥ :=
begin
  have ah : ∀ i j, i ≠ j → (a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ * a.r i) ∨
                          (a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ * a.r j),
    by simpa only [dist_eq_norm] using a.h,
  have δnonneg : 0 ≤ δ := by linarith only [a.oneτ, hδ1],
  have D : 0 ≤ 1 - δ / 4, by linarith only [hδ2],
  have τpos : 0 < τ := zero_lt_one.trans_le a.oneτ,
  have I : (1 - δ / 4) * τ ≤ 1 := calc
    (1 - δ / 4) * τ ≤ (1 - δ / 4) * (1 + δ / 4) : mul_le_mul_of_nonneg_left hδ1 D
    ... = 1 - δ^2 / 16 : by ring
    ... ≤ 1 : (by linarith only [sq_nonneg δ]),
  have J : 1 - δ ≤ 1 - δ / 4, by linarith only [δnonneg],
  have K : 1 - δ / 4 ≤ τ⁻¹, by { rw [inv_eq_one_div, le_div_iff τpos], exact I },
  suffices L : τ⁻¹ ≤ ∥a.c i - a.c j∥, by linarith only [J, K, L],
  have hτ' : ∀ k, τ⁻¹ ≤ a.r k,
  { assume k,
    rw [inv_eq_one_div, div_le_iff τpos, ← lastr, mul_comm],
    exact a.hlast' k },
  rcases ah i j inej with H|H,
  { apply le_trans _ H.1,
    exact hτ' i },
  { rw norm_sub_rev,
    apply le_trans _ H.1,
    exact hτ' j }
end

lemma exists_normalized_aux2 {N : ℕ} {τ : ℝ} (a : satellite_config E N τ)
  (lastc : a.c (last N) = 0) (lastr : a.r (last N) = 1)
  (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4) (hδ2 : δ ≤ 1)
  (i j : fin N.succ) (inej : i ≠ j) (hi : ∥a.c i∥ ≤ 2) (hj : 2 < ∥a.c j∥) :
  1 - δ ≤ ∥a.c i - (2 / ∥a.c j∥) • a.c j∥ :=
begin
  have ah : ∀ i j, i ≠ j → (a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ * a.r i) ∨
                          (a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ * a.r j),
    by simpa only [dist_eq_norm] using a.h,
  have δnonneg : 0 ≤ δ := by linarith only [a.oneτ, hδ1],
  have D : 0 ≤ 1 - δ / 4, by linarith only [hδ2],
  have τpos : 0 < τ := zero_lt_one.trans_le a.oneτ,
  have hcrj : ∥a.c j∥ ≤ a.r j + 1,
    by simpa only [lastc, lastr, dist_zero_right] using a.inter' j,
  have I : a.r i ≤ 2,
  { rcases lt_or_le i (last N) with H|H,
    { apply (a.hlast i H).1.trans,
      simpa only [dist_eq_norm, lastc, sub_zero] using hi },
    { have : i = last N := top_le_iff.1 H,
      rw [this, lastr],
      exact one_le_two } },
  have J : (1 - δ / 4) * τ ≤ 1 := calc
    (1 - δ / 4) * τ ≤ (1 - δ / 4) * (1 + δ / 4) : mul_le_mul_of_nonneg_left hδ1 D
    ... = 1 - δ^2 / 16 : by ring
    ... ≤ 1 : (by linarith only [sq_nonneg δ]),
  have A : a.r j - δ ≤ ∥a.c i - a.c j∥,
  { rcases ah j i inej.symm with H|H, { rw norm_sub_rev, linarith [H.1] },
    have C : a.r j ≤ 4 := calc
      a.r j ≤ τ * a.r i : H.2
      ... ≤ τ * 2 : mul_le_mul_of_nonneg_left I τpos.le
      ... ≤ (5/4) * 2 : mul_le_mul_of_nonneg_right (by linarith only [hδ1, hδ2]) zero_le_two
      ... ≤ 4 : by norm_num,
    calc a.r j - δ ≤ a.r j - (a.r j / 4) * δ : begin
        refine sub_le_sub le_rfl _,
        refine mul_le_of_le_one_left δnonneg _,
        linarith only [C],
      end
    ... = (1 - δ / 4) * a.r j : by ring
    ... ≤ (1 - δ / 4) * (τ * a.r i) :
      mul_le_mul_of_nonneg_left (H.2) D
    ... ≤ 1 * a.r i : by { rw [← mul_assoc], apply mul_le_mul_of_nonneg_right J (a.rpos _).le }
    ... ≤ ∥a.c i - a.c j∥ : by { rw [one_mul], exact H.1 } },
  set d := (2 / ∥a.c j∥) • a.c j with hd,
  have : a.r j - δ ≤ ∥a.c i - d∥ + (a.r j - 1) := calc
    a.r j - δ ≤ ∥a.c i - a.c j∥ : A
    ... ≤ ∥a.c i - d∥ + ∥d - a.c j∥ : by simp only [← dist_eq_norm, dist_triangle]
    ... ≤ ∥a.c i - d∥ + (a.r j - 1) : begin
      apply add_le_add_left,
      have A : 0 ≤ 1 - 2 / ∥a.c j∥, by simpa [div_le_iff (zero_le_two.trans_lt hj)] using hj.le,
      rw [← one_smul ℝ (a.c j), hd, ← sub_smul, norm_smul, norm_sub_rev, real.norm_eq_abs,
          abs_of_nonneg A, sub_mul],
      field_simp [(zero_le_two.trans_lt hj).ne'],
      linarith only [hcrj]
    end,
  linarith only [this]
end

lemma exists_normalized_aux3 {N : ℕ} {τ : ℝ} (a : satellite_config E N τ)
  (lastc : a.c (last N) = 0) (lastr : a.r (last N) = 1)
  (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4)
  (i j : fin N.succ) (inej : i ≠ j) (hi : 2 < ∥a.c i∥) (hij : ∥a.c i∥ ≤ ∥a.c j∥) :
  1 - δ ≤ ∥(2 / ∥a.c i∥) • a.c i - (2 / ∥a.c j∥) • a.c j∥ :=
begin
  have ah : ∀ i j, i ≠ j → (a.r i ≤ ∥a.c i - a.c j∥ ∧ a.r j ≤ τ * a.r i) ∨
                          (a.r j ≤ ∥a.c j - a.c i∥ ∧ a.r i ≤ τ * a.r j),
    by simpa only [dist_eq_norm] using a.h,
  have δnonneg : 0 ≤ δ := by linarith only [a.oneτ, hδ1],
  have τpos : 0 < τ := zero_lt_one.trans_le a.oneτ,
  have hcrj : ∥a.c j∥ ≤ a.r j + 1,
    by simpa only [lastc, lastr, dist_zero_right] using a.inter' j,
  have A : a.r i ≤ ∥a.c i∥,
  { have : i < last N,
    { apply lt_top_iff_ne_top.2,
      assume iN,
      change i = last N at iN,
      rw [iN, lastc, norm_zero] at hi,
      exact lt_irrefl _ (zero_le_two.trans_lt hi) },
    convert (a.hlast i this).1,
    rw [dist_eq_norm, lastc, sub_zero] },
  have hj : 2 < ∥a.c j∥ := hi.trans_le hij,
  set s := ∥a.c i∥ with hs,
  have spos : 0 < s := zero_lt_two.trans hi,
  set d := (s/∥a.c j∥) • a.c j with hd,
  have I : ∥a.c j - a.c i∥ ≤ ∥a.c j∥ - s + ∥d - a.c i∥ := calc
    ∥a.c j - a.c i∥ ≤ ∥a.c j - d∥ + ∥d - a.c i∥ : by simp [← dist_eq_norm, dist_triangle]
    ... = ∥a.c j∥ - ∥a.c i∥ + ∥d - a.c i∥ : begin
      nth_rewrite 0 ← one_smul ℝ (a.c j),
      rw [add_left_inj, hd, ← sub_smul, norm_smul, real.norm_eq_abs, abs_of_nonneg, sub_mul,
          one_mul, div_mul_cancel _ (zero_le_two.trans_lt hj).ne'],
      rwa [sub_nonneg, div_le_iff (zero_lt_two.trans hj), one_mul],
    end,
  have J : a.r j - ∥a.c j - a.c i∥ ≤ s / 2 * δ := calc
    a.r j - ∥a.c j - a.c i∥ ≤ s * (τ - 1) : begin
      rcases ah j i inej.symm with H|H,
      { calc a.r j - ∥a.c j - a.c i∥ ≤ 0 : sub_nonpos.2 H.1
        ... ≤ s * (τ - 1) : mul_nonneg spos.le (sub_nonneg.2 a.oneτ) },
      { rw norm_sub_rev at H,
        calc a.r j - ∥a.c j - a.c i∥ ≤ τ * a.r i - a.r i : sub_le_sub H.2 H.1
        ... = a.r i * (τ - 1) : by ring
        ... ≤ s * (τ - 1) : mul_le_mul_of_nonneg_right A (sub_nonneg.2 a.oneτ) }
    end
    ... ≤ s * (δ / 2) : mul_le_mul_of_nonneg_left (by linarith only [δnonneg, hδ1]) spos.le
    ... = s / 2 * δ : by ring,
  have invs_nonneg : 0 ≤ 2 / s := (div_nonneg zero_le_two (zero_le_two.trans hi.le)),
  calc 1 - δ = (2 / s) * (s / 2 - (s / 2) * δ) : by { field_simp [spos.ne'], ring }
  ... ≤ (2 / s) * ∥d - a.c i∥ :
    mul_le_mul_of_nonneg_left (by linarith only [hcrj, I, J, hi]) invs_nonneg
  ... = ∥(2 / s) • a.c i - (2 / ∥a.c j∥) • a.c j∥ : begin
    conv_lhs { rw [norm_sub_rev, ← abs_of_nonneg invs_nonneg] },
    rw [← real.norm_eq_abs, ← norm_smul, smul_sub, hd, smul_smul],
    congr' 3,
    field_simp [spos.ne'],
  end
end

lemma exists_normalized {N : ℕ} {τ : ℝ} (a : satellite_config E N τ)
  (lastc : a.c (last N) = 0) (lastr : a.r (last N) = 1)
  (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4) (hδ2 : δ ≤ 1) :
  ∃ (c' : fin N.succ → E), (∀ n, ∥c' n∥ ≤ 2) ∧ (∀ i j, i ≠ j → 1 - δ ≤ ∥c' i - c' j∥) :=
begin
  let c' : fin N.succ → E := λ i, if ∥a.c i∥ ≤ 2 then a.c i else (2 / ∥a.c i∥) • a.c i,
  have norm_c'_le : ∀ i, ∥c' i∥ ≤ 2,
  { assume i,
    simp only [c'],
    split_ifs, { exact h },
    by_cases hi : ∥a.c i∥ = 0;
    field_simp [norm_smul, hi] },
  refine ⟨c', λ n, norm_c'_le n, λ i j inej, _⟩,
  -- up to exchanging `i` and `j`, one can assume `∥c i∥ ≤ ∥c j∥`.
  wlog hij : ∥a.c i∥ ≤ ∥a.c j∥ := le_total (∥a.c i∥) (∥a.c j∥) using [i j, j i] tactic.skip, swap,
  { assume i_ne_j,
    rw norm_sub_rev,
    exact this i_ne_j.symm },
  rcases le_or_lt (∥a.c j∥) 2 with Hj|Hj,
  -- case `∥c j∥ ≤ 2` (and therefore also `∥c i∥ ≤ 2`)
  { simp_rw [c', Hj, hij.trans Hj, if_true],
    exact exists_normalized_aux1 a lastr δ hδ1 hδ2 i j inej },
  -- case `2 < ∥c j∥`
  { have H'j : (∥a.c j∥ ≤ 2) ↔ false, by simpa only [not_le, iff_false] using Hj,
    rcases le_or_lt (∥a.c i∥) 2 with Hi|Hi,
    { -- case `∥c i∥ ≤ 2`
      simp_rw [c', Hi, if_true, H'j, if_false],
      exact exists_normalized_aux2 a lastc lastr δ hδ1 hδ2 i j inej Hi Hj },
    { -- case `2 < ∥c i∥`
      have H'i : (∥a.c i∥ ≤ 2) ↔ false, by simpa only [not_le, iff_false] using Hi,
      simp_rw [c', H'i, if_false, H'j, if_false],
      exact exists_normalized_aux3 a lastc lastr δ hδ1 i j inej Hi hij } }
end


#exit


namespace besicovitch

structure package (β : Type*) (α : Type*) [metric_space α] :=
(c : β → α)
(r : β → ℝ)
(r_pos : ∀ b, 0 < r b)
(r_bound : ℝ)
(r_le : ∀ b, r b ≤ r_bound)
(τ : ℝ)
(one_lt_tau : 1 < τ)
(N : ℕ)
(no_satellite : ∀ (c' : ℕ → α) (r' : ℕ → ℝ)
  (h_inter : ∀ i < N, (closed_ball (c' i) (r' i) ∩ closed_ball (c' N) (r' N)).nonempty)
  (h : ∀ i ≤ N, ∀ j ≤ N, i ≠ j → (r' i < dist (c' i) (c' j) ∧ r' j ≤ τ * r' i) ∨
    (r' j < dist (c' j) (c' i) ∧ r' i ≤ τ * r' j)),
  false)


variables {α : Type*} [metric_space α] {β : Type u} [nonempty β]
(p : package β α)
include p

namespace package

/-- Define inductively centers of large balls that are not contained in the union of already
chosen balls. -/
noncomputable def f : ordinal.{u} → β
| i :=
    -- `Z` is the set of points that are covered by already constructed balls
    let Z := ⋃ (j : {j // j < i}), closed_ball (p.c (f j)) (p.r (f j)),
    -- `R` is the supremum of the radii of balls with centers not in `Z`
    R := supr (λ b : {b : β // p.c b ∉ Z}, p.r b) in
    -- return an index `b` for which the center `c b` is not in `Z`, and the radius is at
    -- least `R / τ`, if such an index exists (and garbage otherwise).
    classical.epsilon (λ b : β, p.c b ∉ Z ∧ R ≤ p.τ * p.r b)
using_well_founded {dec_tac := `[exact j.2]}

/-- The set of points that are covered by the union of balls selected at steps `< i`. -/
def Union_up_to (i : ordinal.{u}) : set α :=
⋃ (j : {j // j < i}), closed_ball (p.c (p.f j)) (p.r (p.f j))

lemma monotone_Union_up_to : monotone p.Union_up_to :=
begin
  assume i j hij,
  simp only [Union_up_to],
  apply Union_subset_Union2,
  assume r,
  exact ⟨⟨r, r.2.trans_le hij⟩, subset.refl _⟩,
end

/-- Supremum of the radii of balls whose centers are not yet covered at step `i`. -/
def R (i : ordinal.{u}) : ℝ :=
supr (λ b : {b : β // p.c b ∉ p.Union_up_to i}, p.r b)

/-- Group the balls into disjoint families -/
noncomputable def index : ordinal.{u} → ℕ
| i := let A : set ℕ := ⋃ (j : {j // j < i})
          (hj : (closed_ball (p.c (p.f j)) (p.r (p.f j))
            ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty), {index j} in
       Inf (univ \ A)
using_well_founded {dec_tac := `[exact j.2]}

/-- `p.last_step` is the first ordinal where the construction stops making sense. We will only
use ordinals before this step. -/
def last_step : ordinal.{u} :=
Inf {i | ¬ ∃ (b : β), p.c b ∉ p.Union_up_to i ∧ p.R i ≤ p.τ * p.r b}

lemma index_lt (i : ordinal.{u}) (hi : i < p.last_step) :
  p.index i < p.N :=
begin
  induction i using ordinal.induction with i IH,
  let A : set ℕ := ⋃ (j : {j // j < i})
         (hj : (closed_ball (p.c (p.f j)) (p.r (p.f j))
            ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty), {p.index j},
  have index_i : p.index i = Inf (univ \ A), by rw [index],
  rw index_i,
  have N_mem : p.N ∈ univ \ A,
  { simp only [not_exists, true_and, exists_prop, mem_Union, mem_singleton_iff, mem_closed_ball,
      not_and, mem_univ, mem_diff, subtype.exists, subtype.coe_mk],
    assume j ji hj,
    exact (IH j ji (ji.trans hi)).ne' },
  suffices : Inf (univ \ A) ≠ p.N,
  { rcases (cInf_le (order_bot.bdd_below (univ \ A)) N_mem).lt_or_eq with H|H,
    { exact H },
    { exact (this H).elim } },
  assume Inf_eq_N,
  have : ∀ k, k < p.N → ∃ j, j < i
    ∧ (closed_ball (p.c (p.f j)) (p.r (p.f j)) ∩ closed_ball (p.c (p.f i)) (p.r (p.f i))).nonempty
    ∧ k = p.index j,
  { assume k hk,
    rw ← Inf_eq_N at hk,
    have : k ∈ A,
      by simpa only [true_and, mem_univ, not_not, mem_diff] using nat.not_mem_of_lt_Inf hk,
    simp at this,
    simpa only [exists_prop, mem_Union, mem_singleton_iff, mem_closed_ball, subtype.exists,
      subtype.coe_mk] },
  choose! g hg using this,
  let G : ℕ → ordinal := λ n, if n = p.N then i else g n,
  have index_G : ∀ n, n ≤ p.N → p.index (G n) = n,
  { assume n hn,
    rcases hn.eq_or_lt with rfl|H,
    { simp only [G], simp only [index_i, Inf_eq_N, if_true, eq_self_iff_true] },
    { simp only [G], simp only [H.ne, (hg n H).right.right.symm, if_false] } },
  have G_lt_last : ∀ n, n ≤ p.N → G n < p.last_step,
  { assume n hn,
    rcases hn.eq_or_lt with rfl|H,
    { simp only [G], simp only [hi, if_true, eq_self_iff_true], },
    { simp only [G], simp only [H.ne, (hg n H).left.trans hi, if_false] } },
  have fGn : ∀ n, n ≤ p.N →
    p.c (p.f (G n)) ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r (p.f (G n)),
  { assume n hn,
    have: p.f (G n) = classical.epsilon
      (λ t, p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t), by { rw f, refl },
    rw this,
    have : ∃ t, p.c t ∉ p.Union_up_to (G n) ∧ p.R (G n) ≤ p.τ * p.r t,
      by simpa only [not_exists, exists_prop, not_and, not_lt, not_le, mem_set_of_eq,
        not_forall] using not_mem_of_lt_cInf (G_lt_last n hn) (order_bot.bdd_below _),
    exact classical.epsilon_spec this },
  apply p.no_satellite (p.c ∘ p.f ∘ G) (p.r ∘ p.f ∘ G),
  { assume a ha,
    have A : G a = g a, by simp only [ha.ne, forall_false_left, ite_eq_right_iff],
    have B : G p.N = i,
      by simp only [forall_false_left, eq_self_iff_true, not_true, ite_eq_left_iff],
    simp only [A, B, function.comp_app],
    exact (hg a ha).2.1 },
  { assume a ha b hb a_ne_b,
    wlog G_le : G a ≤ G b := le_total (G a) (G b) using [a b, b a] tactic.skip,
    { have G_lt : G a < G b,
      { rcases G_le.lt_or_eq with H|H, { exact H },
        rw [← index_G a ha, ← index_G b hb, H] at a_ne_b,
        exact (a_ne_b rfl).elim },
      left,
      split,
      { have := (fGn b hb).1,
        simp only [Union_up_to, not_exists, exists_prop, mem_Union, mem_closed_ball, not_and,
          not_le, subtype.exists, subtype.coe_mk] at this,
        simpa only [dist_comm] using this (G a) G_lt },
      { apply le_trans _ (fGn a ha).2,
        have B : p.c (p.f (G b)) ∉ p.Union_up_to (G a),
        { assume H, exact (fGn b hb).1 (p.monotone_Union_up_to G_le H) },
        let b' : {t // p.c t ∉ p.Union_up_to (G a)} := ⟨p.f (G b), B⟩,
        apply @le_csupr _ _ _ (λ t : {t // p.c t ∉ p.Union_up_to (G a)}, p.r t) _ b',
        refine ⟨p.r_bound, λ t ht, _⟩,
        simp only [exists_prop, mem_range, subtype.exists, subtype.coe_mk] at ht,
        rcases ht with ⟨u, hu⟩,
        rw ← hu.2,
        exact p.r_le _ } },
    { assume ha hb a_ne_b,
      rw or_comm,
      exact this hb ha a_ne_b.symm } },
end

end package

end besicovitch
