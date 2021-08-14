/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.jordan

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} [measurable_space α]

namespace measure_theory

namespace signed_measure

open vector_measure measure

lemma measure.exists_measure_pos_of_measure_Union_pos (μ : measure α)
  (f : ℕ → set α) (hf : 0 < μ (⋃ n, f n)) :
  ∃ n, 0 < μ (f n) :=
begin
  by_contra, push_neg at h,
  simp_rw nonpos_iff_eq_zero at h,
  refine pos_iff_ne_zero.1 hf _,
  rw ← nonpos_iff_eq_zero,
  refine le_trans (measure_Union_le (λ (i : ℕ), f i)) _,
  rw nonpos_iff_eq_zero,
  convert tsum_zero,
  { ext1 n, exact h n },
  { apply_instance },
end

lemma nnreal.eq_zero_of_le_pos (a : ℝ≥0) (ha : ∀ b : ℝ≥0, 0 < b → a ≤ b) : a = 0 :=
begin
  by_contra,
  have := ha (a / 2) (nnreal.half_pos (zero_lt_iff.2 h)),
  rw ← @not_not (a ≤ a / 2) at this,
  exact this (not_le.2 (nnreal.half_lt_self h)),
end

lemma nnreal.eq_zero_of_le_one_div_nat_plus_one {a b : ℝ≥0}
  (h : ∀ n : ℕ, a ≤ (1 / (n + 1)) * b) : a = 0 :=
begin
  by_cases hb : 0 < b,
  { have hb₁ : (0 : ℝ) < b⁻¹, { rw _root_.inv_pos, exact hb },
    apply nnreal.eq_zero_of_le_pos,
    intros c hc,
    have : ∃ n : ℕ, 1 / (n + 1 : ℝ) < c * b⁻¹, refine exists_nat_one_div_lt _,
    { refine mul_pos hc _,
      rw _root_.inv_pos, exact hb },
    rcases this with ⟨n, hn⟩,
    have h' : 1 / (↑n + 1) * b < c,
    { rw [← nnreal.coe_lt_coe, ← mul_lt_mul_right hb₁, nnreal.coe_mul, mul_assoc,
          ← nnreal.coe_inv, ← nnreal.coe_mul, _root_.mul_inv_cancel, ← nnreal.coe_mul,
          mul_one, nnreal.coe_inv],
      { convert hn, simp },
      { exact ne.symm (ne_of_lt hb) } },
    exact le_trans (h n) (le_of_lt h') },
  { rw [not_lt, le_zero_iff] at hb,
    specialize h 0,
    rw [hb, mul_zero] at h,
    exact le_zero_iff.1 h }
end

lemma ennreal.eq_zero_of_le_one_div_nat_plus_one {a b : ℝ≥0∞}
  (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
  (h : ∀ n : ℕ, a ≤ (1 / (n + 1)) * b) : a = 0 :=
begin
  lift a to ℝ≥0 using hat,
  lift b to ℝ≥0 using hbt,
  rw ennreal.coe_eq_zero,
  apply nnreal.eq_zero_of_le_one_div_nat_plus_one,
  intro n,
  rw [← ennreal.coe_le_coe, ennreal.coe_mul],
  convert h n, simp,
end

lemma exists_positive_of_sub_measure
  (μ ν : measure α) [finite_measure μ] [finite_measure ν] (h : ¬ μ ⊥ₘ ν) :
  ∃ (ε : ℝ≥0) (hε : 0 < ε), ∃ (E : set α) (hE : measurable_set E) (hνE : 0 < ν E),
  0 ≤[E] (μ.to_signed_measure - (ε • ν).to_signed_measure) :=
begin
  have : ∀ n : ℕ, ∃ i : set α, measurable_set i ∧
    0 ≤[i] (μ.to_signed_measure - ((1 / (n + 1) : ℝ≥0) • ν).to_signed_measure) ∧
    (μ.to_signed_measure - ((1 / (n + 1) : ℝ≥0) • ν).to_signed_measure) ≤[iᶜ] 0,
  { intro, exact exists_compl_positive_negative _ },
  choose f hf₁ hf₂ hf₃ using this,
  set A := ⋂ n, (f n)ᶜ with hA₁,
  have hAmeas : measurable_set A,
  { exact measurable_set.Inter (λ n, measurable_set.compl (hf₁ n)) },
  have hA₂ : ∀ n : ℕ, (μ.to_signed_measure - ((1 / (n + 1) : ℝ≥0) • ν).to_signed_measure) ≤[A] 0,
  { intro n, exact restrict_le_restrict_subset _ _ (hf₁ n).compl (hf₃ n) (set.Inter_subset _ _) },
  have hA₃ : ∀ n : ℕ, μ A ≤ (1 / (n + 1) : ℝ≥0) * ν A,
  { intro n,
    have := nonpos_of_restrict_le_zero _ (hA₂ n),
    rwa [to_signed_measure_sub_apply hAmeas, sub_nonpos, ennreal.to_real_le_to_real] at this,
    exacts [ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)] },
  have hμ : μ A = 0,
  { apply @ennreal.eq_zero_of_le_one_div_nat_plus_one (μ A) (ν A) _ _,
    { intro n, convert hA₃ n, simp },
    { exact ne_of_lt (measure_lt_top _ _) },
    { exact ne_of_lt (measure_lt_top _ _) } },
  rw mutually_singular at h,
  push_neg at h,
  have := h _ hAmeas hμ,
  simp_rw [hA₁, set.compl_Inter, compl_compl] at this,
  obtain ⟨n, hn⟩ := measure.exists_measure_pos_of_measure_Union_pos ν _
    (pos_iff_ne_zero.mpr this),
  exact ⟨1 / (n + 1), by simp, f n, hf₁ n, hn, hf₂ n⟩,
end

section

/-- Given two measures `μ` and `ν`, `measurable_le μ ν` is the set of measurable
functions `f`, such that, for all measurable sets `A`, `∫⁻ x in A, f x ∂μ ≤ ν A`.

This is useful for the Lebesgue decomposition theorem. -/
def measurable_le (μ ν : measure α) : set (α → ℝ≥0∞) :=
{ f | measurable f ∧ ∀ (A : set α) (hA : measurable_set A), ∫⁻ x in A, f x ∂μ ≤ ν A }

variables {μ ν : measure α}

lemma zero_mem_measurable_le : (0 : α → ℝ≥0∞) ∈ measurable_le μ ν :=
⟨measurable_zero, λ A hA, by simp⟩

-- lemma min_mem_measurable_le (f g : α → ℝ≥0∞)
--   (hf : f ∈ measurable_le μ ν) (hg : measurable g) :
--   (λ a, min (f a) (g a)) ∈ measurable_le μ ν :=
-- ⟨measurable.min hf.1 hg,
--   λ A hA, le_trans (lintegral_mono (λ _, min_le_left _ _)) (hf.2 A hA)⟩

-- lemma min_mem_measurable_le' (f g : α → ℝ≥0∞)
--   (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν) :
--   (λ a, min (f a) (g a)) ∈ measurable_le μ ν :=
-- min_mem_measurable_le f g hf hg.1

lemma max_mem_measurable_le (f g : α → ℝ≥0∞)
  (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν)
  (A : set α) (hA : measurable_set A):
  ∫⁻ a in A, max (f a) (g a) ∂μ
    ≤ ∫⁻ a in A ∩ { a | f a ≤ g a }, g a ∂μ
    + ∫⁻ a in A ∩ { a | g a < f a }, f a ∂μ :=
begin
  rw [← lintegral_indicator _ hA, ← lintegral_indicator f,
      ← lintegral_indicator g, ← lintegral_add],
  { refine lintegral_mono (λ a, _),
    by_cases haA : a ∈ A,
    { by_cases f a ≤ g a,
      { simp only,
        rw [set.indicator_of_mem haA, set.indicator_of_mem, set.indicator_of_not_mem, add_zero],
        simp only [le_refl, max_le_iff, and_true, h],
        { rintro ⟨_, hc⟩,
          exact false.elim ((not_lt.2 h) hc) },
        { exact ⟨haA, h⟩ } },
      { simp only,
        rw [set.indicator_of_mem haA, set.indicator_of_mem _ f,
            set.indicator_of_not_mem, zero_add],
        simp only [true_and, le_refl, max_le_iff, le_of_lt (not_le.1 h)],
        { rintro ⟨_, hc⟩,
          exact false.elim (h hc) },
        { exact ⟨haA, not_le.1 h⟩ } } },
    { simp [set.indicator_of_not_mem haA] } },
  { exact measurable.indicator hg.1 (measurable_set.inter hA (measurable_set_le hf.1 hg.1)) },
  { exact measurable.indicator hf.1 (measurable_set.inter hA (measurable_set_lt hg.1 hf.1)) },
  { exact measurable_set.inter hA (measurable_set_le hf.1 hg.1) },
  { exact measurable_set.inter hA (measurable_set_lt hg.1 hf.1) },
end

lemma sup_mem_measurable_le {f g : α → ℝ≥0∞}
  (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν) :
  (λ a, f a ⊔ g a) ∈ measurable_le μ ν :=
begin
  simp_rw ennreal.sup_eq_max,
  refine ⟨measurable.max hf.1 hg.1, λ A hA, _⟩,
  have h₁ := measurable_set.inter hA (measurable_set_le hf.1 hg.1),
  have h₂ := measurable_set.inter hA (measurable_set_lt hg.1 hf.1),
  refine le_trans (max_mem_measurable_le f g hf hg A hA) _,
  refine le_trans (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)) _,
  { rw [← measure_union _ h₁ h₂],
    { refine le_of_eq _,
      congr, convert set.inter_union_compl A _,
      ext a, simpa },
    rintro x ⟨⟨-, hx₁⟩, -, hx₂⟩,
    exact (not_le.2 hx₂) hx₁ }
end

lemma supr_succ_eq_sup {α} (f : ℕ → α → ℝ≥0∞) (m : ℕ) (a : α) :
  (⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) = f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a :=
begin
  ext x,
  simp only [option.mem_def, ennreal.some_eq_coe],
  split; intro h; rw ← h, symmetry,
  all_goals {
    set c := (⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) with hc, -- What is going on?
    set d := (f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a) with hd,
    suffices : c ≤ d ∧ d ≤ c,
    { change c = d, -- commenting this breaks?
      exact le_antisymm this.1 this.2 },
    rw [hc, hd],
    refine ⟨_, _⟩,
    { refine bsupr_le (λ n hn, _),
      rcases nat.of_le_succ hn with (h | h),
      { exact le_sup_of_le_right (le_bsupr n h) },
      { exact h ▸ le_sup_left } },
    { refine sup_le _ _,
      { convert @le_bsupr _ _ _ (λ i, i ≤ m + 1) _ m.succ (le_refl _), refl },
      { refine bsupr_le (λ n hn, _),
        have := (le_trans hn (nat.le_succ m)), -- repacing this breaks?
        exact (le_bsupr n this) } } },
end

lemma supr_mem_measurable_le
  (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurable_le μ ν) (n : ℕ) :
  (λ x, ⨆ k (hk : k ≤ n), f k x) ∈ measurable_le μ ν :=
begin
  induction n with m hm,
  { refine ⟨_, _⟩,
    { simp [(hf 0).1] },
    { intros A hA, simp [(hf 0).2 A hA] } },
  { have : (λ (a : α), ⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) =
      (λ a, f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a),
    { exact funext (λ _, supr_succ_eq_sup _ _ _) },
    refine ⟨measurable_supr (λ n, measurable.supr_Prop _ (hf n).1), λ A hA, _⟩,
    rw this, exact (sup_mem_measurable_le (hf m.succ) hm).2 A hA }
end

lemma supr_mem_measurable_le'
  (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurable_le μ ν) (n : ℕ) :
  (⨆ k (hk : k ≤ n), f k) ∈ measurable_le μ ν :=
begin
  convert supr_mem_measurable_le f hf n,
  ext, simp
end

lemma supr_monotone (f : ℕ → α → ℝ≥0∞) :
  monotone (λ n x, ⨆ k (hk : k ≤ n), f k x) :=
begin
  intros n m hnm x,
  simp only,
  refine bsupr_le (λ k hk, _),
  have : k ≤ m, exact le_trans hk hnm, -- same problem here
  exact le_bsupr k this,
end

lemma supr_monotone' (f : ℕ → α → ℝ≥0∞) (x : α) :
  monotone (λ n, ⨆ k (hk : k ≤ n), f k x) :=
λ n m hnm, supr_monotone f hnm x

lemma supr_le_le (f : ℕ → α → ℝ≥0∞) (n k : ℕ) (hk : k ≤ n) :
  f k ≤ λ x, ⨆ k (hk : k ≤ n), f k x :=
λ x, le_bsupr k hk

def M (μ ν : measure α) := (λ f : α → ℝ≥0∞, ∫⁻ x, f x ∂μ) '' measurable_le μ ν

end

variables {μ ν : measure α} [finite_measure μ] [finite_measure ν]

local infix ` . `:max := measure.with_density

section

open filter

lemma tendsto_supr_le (f : ℕ → α → ℝ≥0∞) (x : α) :
  tendsto (λ n, ⨆ k (hk : k ≤ n), f k x) at_top (nhds  ⨆ n k (hk : k ≤ n), f k x) :=
tendsto_at_top_supr (supr_monotone' f x)

end

lemma ennreal.to_real_sub_of_le {a b : ℝ≥0∞} (h : b ≤ a) (ha : a ≠ ∞):
  (a - b).to_real = a.to_real - b.to_real :=
begin
  lift b to ℝ≥0 using ne_top_of_le_ne_top ha h,
  lift a to ℝ≥0 using ha,
  simp only [← ennreal.coe_sub, ennreal.coe_to_real, nnreal.coe_sub (ennreal.coe_le_coe.mp h)],
end

lemma ennreal.lt_add_of_pos_right {a b : ℝ≥0∞} (hb : 0 < b) (ha : a ≠ ⊤): a < a + b :=
begin
  lift a to ℝ≥0 using ha,
  by_cases b = ⊤,
  { rw [h, ennreal.add_top],
    exact ennreal.coe_lt_top },
  { lift b to ℝ≥0 using h,
    rw [← ennreal.coe_add, ennreal.coe_lt_coe],
    refine lt_add_of_pos_right a (ennreal.coe_pos.mp hb) }
end

/-- The Lebesgue decomposition theorem: Given finite measures `μ` and `ν`, there exists
measures `ν₁`, `ν₂` such that `ν₁` is mutually singular to `μ` and there exists some
`f : α → ℝ≥0∞` such that `ν₂ = μ.with_density f`. -/
theorem exists_singular_with_density (μ ν : measure α) [finite_measure μ] [finite_measure ν] :
  ∃ (ν₁ ν₂ : measure α) [finite_measure ν₁] [finite_measure ν₂] (hν : ν = ν₁ + ν₂),
  ν₁ ⊥ₘ μ ∧ ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν₂ = μ . f :=
begin
  have h := @exists_seq_tendsto_Sup _ _ _ _ _ (M μ ν)
    ⟨0, 0, zero_mem_measurable_le, by simp⟩ (order_top.bdd_above (M μ ν)),
  { choose g hmono hg₂ hg₁ using h,
    choose f hf₁ hf₂ using hg₁,

    set ζ := ⨆ n k (hk : k ≤ n), f k with hζ,
    have hζ₁ : Sup (M μ ν) = ∫⁻ a, ζ a ∂μ,
    { have := @lintegral_tendsto_of_tendsto_of_monotone _ _ μ
        (λ n, ⨆ k (hk : k ≤ n), f k) (⨆ n k (hk : k ≤ n), f k) _ _ _,
      { refine tendsto_nhds_unique _ this,
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ tendsto_const_nhds _ _,
        { intro n, rw ← hf₂ n,
          apply lintegral_mono,
          simp only [supr_apply, supr_le_le f n n (le_refl _)] },
        { intro n,
          exact le_Sup ⟨⨆ (k : ℕ) (hk : k ≤ n), f k, supr_mem_measurable_le' _ hf₁ _, rfl⟩ } },
      { intro n,
        refine measurable.ae_measurable _,
        convert (supr_mem_measurable_le _ hf₁ n).1,
        ext, simp },
      { refine filter.eventually_of_forall (λ a, _),
        simp [supr_monotone' f _] },
      { refine filter.eventually_of_forall (λ a, _),
        simp [tendsto_supr_le _ _] } },
    have hζm : measurable ζ,
      { convert measurable_supr (λ n, (supr_mem_measurable_le _ hf₁ n).1),
        ext, simp [hζ] },

    set ν₁ := ν - μ . ζ with hν₁,

    have hle : μ . ζ ≤ ν,
      { intros B hB,
        rw [hζ, with_density_apply _ hB],
        simp_rw [supr_apply],
        rw lintegral_supr (λ i, (supr_mem_measurable_le _ hf₁ i).1) (supr_monotone _),
        exact supr_le (λ i, (supr_mem_measurable_le _ hf₁ i).2 B hB) },
    haveI : finite_measure (μ . ζ) := by
      { refine finite_measure_with_density _,
        have hle' := hle set.univ measurable_set.univ,
        rw [with_density_apply _ measurable_set.univ, measure.restrict_univ] at hle',
        exact lt_of_le_of_lt hle' (measure_lt_top _ _) },

    refine ⟨ν₁, μ . ζ, infer_instance, infer_instance, _, _, ζ, hζm, rfl⟩,
    { rw hν₁, ext1 A hA,
      rw [measure.coe_add, pi.add_apply, measure.sub_apply hA hle,
          add_comm, ennreal.add_sub_cancel_of_le (hle A hA)] },

    { by_contra,
      have hle : μ . ζ ≤ ν,
      { intros B hB,
        rw [hζ, with_density_apply _ hB],
        simp_rw [supr_apply],
        rw lintegral_supr (λ i, (supr_mem_measurable_le _ hf₁ i).1) (supr_monotone _),
        exact supr_le (λ i, (supr_mem_measurable_le _ hf₁ i).2 B hB) },

      obtain ⟨ε, hε₁, E, hE₁, hE₂, hE₃⟩ := exists_positive_of_sub_measure ν₁ μ h,
      simp_rw hν₁ at hE₃,

      have hζle : ∀ A, measurable_set A → ∫⁻ a in A, ζ a ∂μ ≤ ν A,
      { intros A hA, rw hζ,
        simp_rw [supr_apply],
        rw lintegral_supr (λ n, (supr_mem_measurable_le _ hf₁ n).1) (supr_monotone _),
        exact supr_le (λ n, (supr_mem_measurable_le _ hf₁ n).2 A hA) },

      have hε₂ : ∀ A : set α, measurable_set A →
        ∫⁻ a in A ∩ E, ε + ζ a ∂μ ≤ ν (A ∩ E),
      { intros A hA,
        have := subset_le_of_restrict_le_restrict _ _ hE₁ hE₃ (set.inter_subset_right A E),
        rwa [zero_apply, to_signed_measure_sub_apply (hA.inter hE₁),
             measure.sub_apply (hA.inter hE₁) hle,
             ennreal.to_real_sub_of_le _ (ne_of_lt (measure_lt_top _ _)), sub_nonneg,
             le_sub_iff_add_le, ← ennreal.to_real_add, ennreal.to_real_le_to_real,
             measure.coe_nnreal_smul, pi.smul_apply, with_density_apply _ (hA.inter hE₁),
             show ε • μ (A ∩ E) = (ε : ℝ≥0∞) * μ (A ∩ E), by refl,
             ← set_lintegral_const, ← lintegral_add measurable_const hζm] at this,
        { rw [ne.def, ennreal.add_eq_top, not_or_distrib],
          exact ⟨ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)⟩ },
        { exact ne_of_lt (measure_lt_top _ _) },
        { exact ne_of_lt (measure_lt_top _ _) },
        { exact ne_of_lt (measure_lt_top _ _) },
        { rw with_density_apply _ (measurable_set.inter hA hE₁),
          exact hζle (A ∩ E) (measurable_set.inter hA hE₁) },
        { apply_instance } },

      have hζε : ζ + E.indicator (λ _, ε) ∈ measurable_le μ ν,
      { refine ⟨measurable.add hζm (measurable.indicator measurable_const hE₁), λ A hA, _⟩,
        have : ∫⁻ a in A, (ζ + E.indicator (λ _, ε)) a ∂μ =
              ∫⁻ a in A ∩ E, ε + ζ a ∂μ + ∫⁻ a in A ∩ Eᶜ, ζ a ∂μ,
        { rw [lintegral_add measurable_const hζm, add_assoc,
              ← lintegral_union (measurable_set.inter hA hE₁)
                (measurable_set.inter hA (measurable_set.compl hE₁))
                (disjoint.mono (set.inter_subset_right _ _) (set.inter_subset_right _ _)
                disjoint_compl_right), set.inter_union_compl],
          simp_rw [pi.add_apply],
          rw [lintegral_add hζm (measurable.indicator measurable_const hE₁), add_comm],
          refine congr_fun (congr_arg has_add.add _) _,
          rw [set_lintegral_const, lintegral_indicator _ hE₁, set_lintegral_const,
              measure.restrict_apply hE₁, set.inter_comm] },
        conv_rhs { rw ← set.inter_union_compl A E },
        rw [this, measure_union _ (measurable_set.inter hA hE₁)
            (measurable_set.inter hA (measurable_set.compl hE₁))],
        { exact add_le_add (hε₂ A hA)
            (hζle (A ∩ Eᶜ) (measurable_set.inter hA (measurable_set.compl hE₁))) },
        { exact disjoint.mono (set.inter_subset_right _ _) (set.inter_subset_right _ _)
            disjoint_compl_right } },

      have : ∫⁻ a, ζ a + E.indicator (λ _, ε) a ∂μ ≤ Sup (M μ ν),
      { exact le_Sup ⟨ζ + E.indicator (λ _, ε), hζε, rfl⟩ },

      refine not_lt.2 this _,
      rw [hζ₁, lintegral_add hζm (measurable.indicator (measurable_const) hE₁),
          lintegral_indicator _ hE₁, set_lintegral_const],
      refine ennreal.lt_add_of_pos_right (ennreal.mul_pos.2 ⟨ennreal.coe_pos.2 hε₁, hE₂⟩) _,

      have := ne_of_lt (measure_lt_top (μ . ζ) set.univ),
      rwa [with_density_apply _ measurable_set.univ, measure.restrict_univ] at this } },
end

lemma measure.eq_of_sub_measure_eq_zero (μ ν : measure α) [finite_measure μ] [finite_measure ν]
  (h : μ.to_signed_measure - ν.to_signed_measure = 0) : μ = ν :=
by rwa [← to_signed_measure_eq_to_signed_measure_iff, ← sub_eq_zero]

-- remove
lemma with_density.absolutely_continuous (f : α → ℝ≥0∞) : μ . f ≪ μ :=
begin
  exact with_density_absolutely_continuous μ f,
end

#exit
/-- The Lebesgue decomposition is unique. -/
theorem singular_with_density_unique
  (ν₁ ν₂ μ₁ μ₂ : measure α)
  [finite_measure ν₁] [finite_measure ν₂] [finite_measure μ₁] [finite_measure μ₂]
  (hν : ν = ν₁ + ν₂) (hμ : ν = μ₁ + μ₂)
  (h₁ : ν₁ ⊥ₘ μ ∧ ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν₂ = μ . f)
  (h₂ : μ₁ ⊥ₘ μ ∧ ∃ (f : α → ℝ≥0∞) (hf : measurable f), μ₂ = μ . f) :
  ν₁ = μ₁ ∧ ν₂ = μ₂ :=
begin
  obtain ⟨S, hS₁, hS₂, hS₃⟩ := h₁.1,
  obtain ⟨T, hT₁, hT₂, hT₃⟩ := h₂.1,

  have hsub : of_sub_measure ν₁ μ₁ = of_sub_measure μ₂ ν₂,
  { ext i hi,
    rw [of_sub_measure_apply hi, of_sub_measure_apply hi],
    suffices : (ν₁ i).to_real + (ν₂ i).to_real = (μ₁ i).to_real + (μ₂ i).to_real,
    { linarith },
    rw [← ennreal.to_real_add, ← ennreal.to_real_add, ennreal.to_real_eq_to_real,
        ← measure.add_apply, ← measure.add_apply, ← hν, ← hμ],
    { exact (ennreal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩) },
    { exact (ennreal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩) },
    all_goals { exact ne_of_lt (measure_lt_top _ _) } },
  have heq : ∀ A (hA : measurable_set A),
    of_sub_measure ν₁ μ₁ A = of_sub_measure ν₁ μ₁ (A ∩ (S ∩ T)ᶜ),
  { intros A hA,
    have : A = (A ∩ (S ∩ T)ᶜ) ∪ (A ∩ (S ∩ T)),
    { rw [← set.inter_union_distrib_left, set.compl_union_self, set.inter_univ] },
    conv_lhs { rw this },
    rw measure_of_union (disjoint.comm.1 (set.disjoint_inter_compl A (S ∩ T))),
    suffices : (of_sub_measure ν₁ μ₁) (A ∩ (S ∩ T)) = 0,
    { rw [this, add_zero] },
    rw [of_sub_measure_apply, sub_eq_zero, ennreal.to_real_eq_to_real],
    refine eq.trans (nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono _))
      (eq.symm ((nonpos_iff_eq_zero.1 (hT₂ ▸ measure_mono _)))),
    { rw [set.inter_comm, set.inter_assoc],
      exact set.inter_subset_left _ _ },
    { rw ← set.inter_assoc, exact set.inter_subset_right _ _ },
    { exact measure_lt_top _ _ },
    { exact measure_lt_top _ _ },
    measurability },
  have hν₂ : ν₂ ≪ μ,
  { obtain ⟨-, f, -, hf⟩ := h₁, rw hf,
    exact with_density.absolutely_continuous _ },
  have hμ₂ : μ₂ ≪ μ,
  { obtain ⟨-, f, -, hf⟩ := h₂, rw hf,
    exact with_density.absolutely_continuous _ },
  have hμinter : μ (S ∩ T)ᶜ = 0,
    { rw set.compl_inter,
      refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _),
      rw [hS₃, hT₃, add_zero],
      exact le_refl _ },

  suffices : of_sub_measure ν₁ μ₁ = 0,
  { refine ⟨measure.eq_of_sub_measure_eq_zero _ _ this,
            eq.symm (measure.eq_of_sub_measure_eq_zero _ _ _)⟩,
    rwa ← hsub },

  ext A hA,
  rw [heq A hA, hsub, of_sub_measure_apply, hν₂, hμ₂, ennreal.zero_to_real,
      sub_zero, zero_apply],
  { exact nonpos_iff_eq_zero.1 (hμinter ▸ measure_mono (set.inter_subset_right _ _)) },
  { exact nonpos_iff_eq_zero.1 (hμinter ▸ measure_mono (set.inter_subset_right _ _)) },
  { measurability }
end

-- ↓ go in another file
-- /-- The Radon-Nikodym theorem: Given two finite measures `μ` and `ν`, if `ν` is absolutely
-- continuous with respect to `μ`, then there exists a measurable function `f` such that
-- `f` is the derivative of `ν` with respect to `μ`. -/
-- theorem exists_with_density_of_absolute_continuous
--   (μ ν : measure α) [finite_measure μ] [finite_measure ν] (h : ν ≪ μ) :
--   ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν = μ . f :=
-- begin
--   obtain ⟨ν₁, ν₂, _, _, hν, ⟨E, hE₁, hE₂, hE₃⟩, f, hf₁, hf₂⟩ :=
--     exists_singular_with_density μ ν,
--   have : ν₁ = 0,
--   { apply le_antisymm,
--     { intros A hA,
--       suffices : ν₁ set.univ = 0,
--       { rw [measure.coe_zero, pi.zero_apply, ← this],
--         exact measure_mono (set.subset_univ _) },
--       rw [← set.union_compl_self E, measure_union (set.disjoint_compl E) hE₁
--             (measurable_set.compl hE₁), hE₂, zero_add],
--       have : (ν₁ + ν₂) Eᶜ = ν Eᶜ, { rw hν },
--       rw [measure.coe_add, pi.add_apply, h hE₃] at this,
--       exact (add_eq_zero_iff.1 this).1 },
--     { exact measure.zero_le _} },
--   rw [this, zero_add] at hν,
--   exact ⟨f, hf₁, hν.symm ▸ hf₂⟩,
-- end

end signed_measure

end measure_theory
