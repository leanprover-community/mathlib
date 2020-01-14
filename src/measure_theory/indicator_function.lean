/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/

import data.indicator_function
import measure_theory.measure_space
import analysis.normed_space.basic

/-!
# Indicator function

Properties of indicator functions.

## Tags
indicator, characteristic
-/

noncomputable theory
open_locale classical

open set measure_theory filter

universes u v
variables {α : Type u} {β : Type v}

section has_zero
variables [has_zero β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_congr_ae [measure_space α] (h : ∀ₘ a, a ∈ s → f a = g a) :
  ∀ₘ a, indicator s f a = indicator s g a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq, indicator],
  assume a ha,
  split_ifs,
  { exact ha h_1 },
  refl
end

lemma indicator_congr_of_set [measure_space α] (h : ∀ₘ a, a ∈ s ↔ a ∈ t) :
  ∀ₘ a, indicator s f a = indicator t f a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq, indicator],
  assume a ha,
  split_ifs,
  { refl },
  { have := ha.1 h_1, contradiction },
  { have := ha.2 h_2, contradiction },
  refl
end

end has_zero

section has_add
variables [add_monoid β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_union_ae [measure_space α] {β : Type*} [add_monoid β]
  (h : ∀ₘ a, a ∉ s ∩ t) (f : α → β) :
  ∀ₘ a, indicator (s ∪ t) f a = indicator s f a + indicator t f a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq],
  assume a ha,
  exact indicator_union_of_not_mem_inter ha _
end

end has_add

section norm
variables [normed_group β] {s t : set α} {f g : α → β} {a : α}

lemma norm_indicator_le_of_subset (h : s ⊆ t) (f : α → β) (a : α) :
  ∥indicator s f a∥ ≤ ∥indicator t f a∥ :=
begin
  simp only [indicator],
  split_ifs with h₁ h₂,
  { refl },
  { exact absurd (h h₁) h₂ },
  { simp only [norm_zero, norm_nonneg] },
  refl
end

lemma norm_indicator_le_norm_self (f : α → β) (a : α) : ∥indicator s f a∥ ≤ ∥f a∥ :=
by { convert norm_indicator_le_of_subset (subset_univ s) f a, rw indicator_univ }

lemma norm_indicator_eq_indicator_norm (f : α → β) (a : α) :∥indicator s f a∥ = indicator s (λa, ∥f a∥) a :=
by { simp only [indicator], split_ifs, { refl }, rw norm_zero }

end norm

section order
variables [has_zero β] [preorder β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_le_indicator_ae [measure_space α] (h : ∀ₘ a, a ∈ s → f a ≤ g a) :
  ∀ₘ a, indicator s f a ≤ indicator s g a :=
begin
  filter_upwards [h],
  simp only [mem_set_of_eq, indicator],
  assume a h,
  split_ifs with ha,
  { exact h ha },
  refl
end

end order

section tendsto
variables [has_zero β] [topological_space β]

lemma tendsto_indicator_of_monotone (s : ℕ → set α) (hs : monotone s) (f : α → β)
  (a : α) : tendsto (λi, indicator (s i) f a) at_top (nhds $ indicator (Union s) f a) :=
begin
  by_cases h : ∃i, a ∈ s i,
  { rcases h with ⟨i, hi⟩,
    refine tendsto_nhds.mpr (λ t ht hf, _),
    simp only [mem_at_top_sets, mem_preimage],
    use i, assume n hn,
    have : indicator (s n) f a = f a := indicator_of_mem (hs hn hi) _,
    rw this,
    have : indicator (Union s) f a = f a := indicator_of_mem ((subset_Union _ _) hi) _,
    rwa this at hf },
  { rw [not_exists] at h,
    have : (λi, indicator (s i) f a) = λi, 0 := funext (λi, indicator_of_not_mem (h i) _),
    rw this,
    have : indicator (Union s) f a = 0,
      { apply indicator_of_not_mem, simpa only [not_exists, mem_Union] },
    rw this,
    exact tendsto_const_nhds }
end

lemma tendsto_indicator_of_decreasing (s : ℕ → set α) (hs : ∀i j, i ≤ j → s j ⊆ s i) (f : α → β)
  (a : α) : tendsto (λi, indicator (s i) f a) at_top (nhds $ indicator (Inter s) f a) :=
begin
  by_cases h : ∃i, a ∉ s i,
  { rcases h with ⟨i, hi⟩,
    refine tendsto_nhds.mpr (λ t ht hf, _),
    simp only [mem_at_top_sets, mem_preimage],
    use i, assume n hn,
    have : indicator (s n) f a = 0 := indicator_of_not_mem _ _,
    rw this,
    have : indicator (Inter s) f a = 0 := indicator_of_not_mem _ _,
    rwa this at hf,
    { simp only [mem_Inter, not_forall], exact ⟨i, hi⟩ },
    { assume h, have := hs i _ hn h, contradiction } },
  { simp only [not_exists, not_not_mem] at h,
    have : (λi, indicator (s i) f a) = λi, f a := funext (λi, indicator_of_mem (h i) _),
    rw this,
    have : indicator (Inter s) f a = f a,
      { apply indicator_of_mem, simpa only [mem_Inter] },
    rw this,
    exact tendsto_const_nhds }
end

end tendsto
