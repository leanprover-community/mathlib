/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.integral.set_integral

/-!
# Uniform integrability

This file will be used in the future to define uniform integrability. Uniform integrability
is an important notion in both measure theory as well as probability theory. So far this file
only contains the Egorov theorem which will be used to prove the Vitali convergence theorem
which is one of the main results about uniform integrability.

## Main results

* `measure_theory.egorov`: Egorov's theorem which shows that a sequence of almost everywhere
  convergent functions converges uniformly except on an arbitrarily small set.

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space

namespace measure_theory

open set filter topological_space

variables {α β ι : Type*} {m : measurable_space α} [metric_space β]

section

/-! We will in this section prove Egorov's theorem. -/

namespace egorov

/-- Given a sequence of functions `f` and a function `g`, `not_convergent_seq f g i j` is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (i + 1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem. -/
def not_convergent_seq (f : ℕ → α → β) (g : α → β) (i j : ℕ) : set α :=
⋃ k (hk : j ≤ k), {x | (1 / (i + 1 : ℝ)) < dist (f k x) (g x)}

variables {f : ℕ → α → β} {g : α → β} {μ : measure α}

lemma mem_not_convergent_seq_iff {i j : ℕ} {x : α} : x ∈ not_convergent_seq f g i j ↔
  ∃ k (hk : j ≤ k), (1 / (i + 1 : ℝ)) < dist (f k x) (g x) :=
by { simp_rw [not_convergent_seq, mem_Union], refl }

lemma not_convergent_seq_antitone {i : ℕ} :
  antitone (not_convergent_seq f g i) :=
λ j k hjk, bUnion_subset_bUnion (λ l hl, ⟨l, le_trans hjk hl, subset.refl _⟩)

lemma measure_inter_not_convergent_seq_eq_zero {s : set α}
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  μ (s ∩ ⋂ j, not_convergent_seq f g i j) = 0 :=
begin
  simp_rw [metric.tendsto_at_top, ae_iff] at hfg,
  rw [← nonpos_iff_eq_zero, ← hfg],
  refine measure_mono (λ x, _),
  simp only [mem_inter_eq, mem_Inter, ge_iff_le, mem_not_convergent_seq_iff],
  push_neg,
  rintro ⟨hmem, hx⟩,
  refine ⟨hmem, 1 / (i + 1 : ℝ), nat.one_div_pos_of_nat, λ N, _⟩,
  obtain ⟨n, hn₁, hn₂⟩ := hx N,
  exact ⟨n, hn₁, hn₂.le⟩
end

variables [second_countable_topology β] [measurable_space β] [borel_space β]

lemma not_convergent_seq_measurable_set
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {i j : ℕ} : measurable_set (not_convergent_seq f g i j) :=
measurable_set.Union (λ k, measurable_set.Union_Prop $ λ hk,
  measurable_set_lt measurable_const $ (hf k).dist hg)

lemma measure_not_convergent_seq_tendsto_zero
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {s : set α} (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  tendsto (λ j, μ (s ∩ not_convergent_seq f g i j)) at_top (𝓝 0) :=
begin
  rw [← measure_inter_not_convergent_seq_eq_zero hfg, inter_Inter],
  exact tendsto_measure_Inter (λ n, hsm.inter $ not_convergent_seq_measurable_set hf hg)
    (λ k l hkl, inter_subset_inter_right _ $ not_convergent_seq_antitone hkl)
    ⟨0, (lt_of_le_of_lt (measure_mono $ inter_subset_left _ _) (lt_top_iff_ne_top.2 hs)).ne⟩
end

lemma exists_not_convergent_seq_lt {ε : ℝ} (hε : 0 < ε)
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {s : set α} (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  ∃ j : ℕ, μ (s ∩ not_convergent_seq f g i j) ≤ ennreal.of_real (ε * 2⁻¹ ^ i) :=
begin
  obtain ⟨N, hN⟩ := (ennreal.tendsto_at_top ennreal.zero_ne_top).1
    (measure_not_convergent_seq_tendsto_zero hf hg hsm hs hfg i)
    (ennreal.of_real (ε * 2⁻¹ ^ i)) _,
  { rw zero_add at hN,
    exact ⟨N, (hN N le_rfl).2⟩ },
  { rw [gt_iff_lt, ennreal.of_real_pos],
    exact mul_pos hε (pow_pos (by norm_num) _) }
end

/-- Given some `ε > 0`, `not_convergent_seq_lt_index` provides the index such that
`not_convergent_seq` (intersected with a set of finite measure) has measure less than
`ε * 2⁻¹ ^ i`.

This definition is useful for Egorov's theorem. -/
def not_convergent_seq_lt_index {ε : ℝ} (hε : 0 < ε)
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {s : set α} (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) : ℕ :=
classical.some $ exists_not_convergent_seq_lt hε hf hg hsm hs hfg i

lemma not_convergent_seq_lt_index_spec {ε : ℝ} (hε : 0 < ε)
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {s : set α} (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  μ (s ∩ not_convergent_seq f g i (not_convergent_seq_lt_index hε hf hg hsm hs hfg i)) ≤
  ennreal.of_real (ε * 2⁻¹ ^ i) :=
classical.some_spec $ exists_not_convergent_seq_lt hε hf hg hsm hs hfg i

/-- Given some `ε > 0`, `Union_not_convergent_seq` is the union of `not_convergent_seq` with
specific indicies such that `Union_not_convergent_seq` has measure less equal than `ε`.

This definition is useful for Egorov's theorem. -/
def Union_not_convergent_seq {ε : ℝ} (hε : 0 < ε)
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {s : set α} (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) : set α :=
⋃ i, s ∩ not_convergent_seq f g i (not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg i)

lemma measure_Union_not_convergent_seq {ε : ℝ} (hε : 0 < ε)
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {s : set α} (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  μ (Union_not_convergent_seq hε hf hg hsm hs hfg) ≤ ennreal.of_real ε :=
begin
  refine le_trans (measure_Union_le _)
    (le_trans (ennreal.tsum_le_tsum $ not_convergent_seq_lt_index_spec
    (half_pos hε) hf hg hsm hs hfg) _),
  simp_rw [ennreal.of_real_mul (half_pos hε).le],
  rw [ennreal.tsum_mul_left, ← ennreal.of_real_tsum_of_nonneg, inv_eq_one_div,
      tsum_geometric_two, ← ennreal.of_real_mul (half_pos hε).le, div_mul_cancel ε two_ne_zero],
  { exact le_rfl },
  { exact λ n, pow_nonneg (by norm_num) _ },
  { rw [inv_eq_one_div],
    exact summable_geometric_two },
end

lemma Union_not_convergent_seq_subset {ε : ℝ} (hε : 0 < ε)
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {s : set α} (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  Union_not_convergent_seq hε hf hg hsm hs hfg ⊆ s :=
begin
  rw [Union_not_convergent_seq, ← inter_Union],
  exact inter_subset_left _ _,
end

end egorov

variables [second_countable_topology β] [measurable_space β] [borel_space β]
  {μ : measure α} {f : ℕ → α → β} {g : α → β}

/-- **Egorov's theorem**: If `f : ℕ → α → β` is a sequence of measurable functions that converges
to `g : α → β` almost everywhere on a measurable set `s` of finite measure, then for all `ε > 0`,
there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g` uniformly on `s \ t`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
theorem tendsto_uniformly_on_of_ae_tendsto (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  {s : set α} (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
  ∃ t ⊆ s, μ t ≤ ennreal.of_real ε ∧ tendsto_uniformly_on f g at_top (s \ t) :=
begin
  refine ⟨egorov.Union_not_convergent_seq hε hf hg hsm hs hfg,
    egorov.Union_not_convergent_seq_subset hε hf hg hsm hs hfg,
    egorov.measure_Union_not_convergent_seq hε hf hg hsm hs hfg, _⟩,
  rw metric.tendsto_uniformly_on_iff,
  intros δ hδ,
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ,
  rw eventually_iff_exists_mem,
  refine ⟨Ioi (egorov.not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg N),
    Ioi_mem_at_top _, λ n hn x hx, _⟩,
  simp only [mem_diff, egorov.Union_not_convergent_seq, not_exists, mem_Union, mem_inter_eq,
    not_and, exists_and_distrib_left] at hx,
  obtain ⟨hxs, hx⟩ := hx,
  specialize hx hxs N,
  rw egorov.mem_not_convergent_seq_iff at hx,
  push_neg at hx,
  rw dist_comm,
  exact lt_of_le_of_lt (hx n (mem_Ioi.1 hn).le) hN,
end

/-- Egorov's theorem for finite measure spaces. -/
lemma tendsto_uniformly_on_of_ae_tendsto' [is_finite_measure μ]
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
  ∃ t, μ t ≤ ennreal.of_real ε ∧ tendsto_uniformly_on f g at_top tᶜ :=
begin
  obtain ⟨t, _, ht, htendsto⟩ :=
    tendsto_uniformly_on_of_ae_tendsto hf hg measurable_set.univ (measure_ne_top μ univ) _ hε,
  { refine ⟨t, ht, _⟩,
    rwa compl_eq_univ_diff },
  { filter_upwards [hfg],
    intros,
    assumption }
end

end

variables [normed_group β] [measurable_space β]

/-- Also known as uniformly absolutely continuous integrals. -/
def unif_integrable {m : measurable_space α} (f : ι → α → β) (p : ℝ≥0∞) (μ : measure α) : Prop :=
∀ (ε : ℝ) (hε : 0 < ε), ∃ (δ : ℝ) (hδ : 0 < δ), ∀ i s, measurable_set s → μ s < ennreal.of_real δ →
snorm (set.indicator s (f i)) p μ < ennreal.of_real ε

section unif_integrable

variables [borel_space β] [second_countable_topology β]
  {μ : measure α} [is_finite_measure μ] {p : ℝ≥0∞}

#check snorm_ess_sup_lt_top_of_ae_bound
#check snorm_le_of_ae_bound

lemma foo {f : α → β} (hf : mem_ℒp f p μ) {ε : ℝ} (hε : 0 < ε) :
  ∃ (δ : ℝ) (hδ : 0 < δ), ∀ s, measurable_set s → μ s < ennreal.of_real δ →
  snorm (set.indicator s f) p μ < ennreal.of_real ε :=
begin
  sorry
end

lemma unif_integrable_subsingleton [subsingleton ι] {f : ι → α → β} (hf : ∀ i, mem_ℒp (f i) p μ) :
  unif_integrable f p μ :=
begin
  sorry
end

lemma unif_integrable_finite [fintype ι] {f : ι → α → β} (hf : ∀ i, mem_ℒp (f i) p μ) :
  unif_integrable f p μ :=
begin
  sorry
end

/- The next three lemmas together is known as **the Vitali convergence theorem**. -/

lemma tendsto_Lp_of_unif_integrable {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, mem_ℒp (f n) p μ) (hg : mem_ℒp g p μ) (hui : unif_integrable f p μ)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0) :=
begin
  rw ennreal.tendsto_at_top ennreal.zero_ne_top,
  swap, apply_instance,
  intros ε hε,
end

lemma unif_integrable_of_tendsto_Lp {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, mem_ℒp (f n) p μ) (hg : mem_ℒp g p μ)
  (hfg : tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0)) :
  unif_integrable f p μ :=
begin
  sorry
end

-- should be a standard result
lemma ae_tendsto_of_tendsto_Lp {f : ℕ → α → β} {g : α → β}
  (hf : ∀ n, mem_ℒp (f n) p μ) (hg : mem_ℒp g p μ)
  (hfg : tendsto (λ n, snorm (f n - g) p μ) at_top (𝓝 0)) :
  ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x)) :=
sorry

end unif_integrable

/-- In probability theory, a family of functions is uniformly integrable if it is uniformly
integrable in the measure theory sense and is uniformly bounded. -/
def uniform_integrable {m : measurable_space α}
  (μ : measure α) (f : ι → α → β) (p : ℝ≥0∞) : Prop :=
(∀ i, measurable (f i)) ∧ unif_integrable f p μ ∧ ∃ C : ℝ≥0, ∀ i, snorm (f i) p μ < C

variables {μ : measure α} {f : ι → α → β} {p : ℝ≥0∞}

lemma uniform_integrable.mem_ℒp (hf : uniform_integrable μ f p) (i : ι) :
  mem_ℒp (f i) p μ :=
⟨(hf.1 i).ae_measurable, let ⟨_, _, hC⟩ := hf.2 in lt_trans (hC i) ennreal.coe_lt_top⟩

end measure_theory
