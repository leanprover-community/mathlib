/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import measure_theory.probability_mass_function.constructions

/-!
# Uniform probability mass functions

This file defines a number of uniform `pmf` distributions from various inputs.

`uniform_of_finset` gives each element in the set equal probability,
  with `0` probability for elements not in the set.

`uniform_of_fintype` gives all elements equal probability,
  equal to the inverse of the size of the `fintype`.

-/

namespace pmf

noncomputable theory
variables {α β γ : Type*}
open_locale classical big_operators nnreal ennreal

section uniform_of_finset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniform_of_finset (s : finset α) (hs : s.nonempty) : pmf α :=
of_finset (λ a, if a ∈ s then (s.card : ℝ≥0)⁻¹ else 0) s (Exists.rec_on hs (λ x hx,
  calc ∑ (a : α) in s, ite (a ∈ s) (s.card : ℝ≥0)⁻¹ 0
    = ∑ (a : α) in s, (s.card : ℝ≥0)⁻¹ : finset.sum_congr rfl (λ x hx, by simp [hx])
    ... = s.card • (s.card : ℝ≥0)⁻¹ : finset.sum_const _
    ... = (s.card : ℝ≥0) * (s.card : ℝ≥0)⁻¹ : by rw nsmul_eq_mul
    ... = 1 : div_self (nat.cast_ne_zero.2 $ finset.card_ne_zero_of_mem hx)
  )) (λ x hx, by simp only [hx, if_false])

variables {s : finset α} (hs : s.nonempty) {a : α}

@[simp] lemma uniform_of_finset_apply (a : α) :
  uniform_of_finset s hs a = if a ∈ s then (s.card : ℝ≥0)⁻¹ else 0 := rfl

lemma uniform_of_finset_apply_of_mem (ha : a ∈ s) : uniform_of_finset s hs a = (s.card)⁻¹ :=
by simp [ha]

lemma uniform_of_finset_apply_of_not_mem (ha : a ∉ s) : uniform_of_finset s hs a = 0 :=
by simp [ha]

@[simp] lemma support_uniform_of_finset : (uniform_of_finset s hs).support = s :=
set.ext (let ⟨a, ha⟩ := hs in by simp [mem_support_iff, finset.ne_empty_of_mem ha])

lemma mem_support_uniform_of_finset_iff (a : α) : a ∈ (uniform_of_finset s hs).support ↔ a ∈ s :=
by simp

section measure

variable (t : set α)

@[simp] lemma to_outer_measure_uniform_of_finset_apply :
  (uniform_of_finset s hs).to_outer_measure t = (s.filter (∈ t)).card / s.card :=
calc (uniform_of_finset s hs).to_outer_measure t
  = ↑(∑' x, if x ∈ t then (uniform_of_finset s hs x) else 0) :
    to_outer_measure_apply' (uniform_of_finset s hs) t
  ... = ↑(∑' x, if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0)⁻¹ else 0) :
    begin
      refine (ennreal.coe_eq_coe.2 $ tsum_congr (λ x, _)),
      by_cases hxt : x ∈ t,
      { by_cases hxs : x ∈ s; simp [hxt, hxs] },
      { simp [hxt] }
    end
  ... = ↑(∑ x in (s.filter (∈ t)), if x ∈ s ∧ x ∈ t then (s.card : ℝ≥0)⁻¹ else 0) :
    begin
      refine ennreal.coe_eq_coe.2 (tsum_eq_sum (λ x hx, _)),
      have : ¬ (x ∈ s ∧ x ∈ t) := λ h, hx (finset.mem_filter.2 h),
      simp [this]
    end
  ... = ↑(∑ x in (s.filter (∈ t)), (s.card : ℝ≥0)⁻¹) :
    ennreal.coe_eq_coe.2 (finset.sum_congr rfl $
      λ x hx, let this : x ∈ s ∧ x ∈ t := by simpa using hx in by simp [this])
  ... = (s.filter (∈ t)).card / s.card :
    let this : (s.card : ℝ≥0) ≠ 0 := nat.cast_ne_zero.2
      (hs.rec_on $ λ _, finset.card_ne_zero_of_mem) in
    by simp [div_eq_mul_inv, ennreal.coe_inv this]

@[simp] lemma to_measure_uniform_of_finset_apply [measurable_space α] (ht : measurable_set t) :
  (uniform_of_finset s hs).to_measure t = (s.filter (∈ t)).card / s.card :=
(to_measure_apply_eq_to_outer_measure_apply _ t ht).trans
  (to_outer_measure_uniform_of_finset_apply hs t)

end measure

end uniform_of_finset

section uniform_of_fintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniform_of_fintype (α : Type*) [fintype α] [nonempty α] : pmf α :=
  uniform_of_finset (finset.univ) (finset.univ_nonempty)

variables [fintype α] [nonempty α]

@[simp] lemma uniform_of_fintype_apply (a : α) : uniform_of_fintype α a = (fintype.card α)⁻¹ :=
by simpa only [uniform_of_fintype, finset.mem_univ, if_true, uniform_of_finset_apply]

@[simp] lemma support_uniform_of_fintype (α : Type*) [fintype α] [nonempty α] :
  (uniform_of_fintype α).support = ⊤ :=
set.ext (λ x, by simpa [mem_support_iff] using fintype.card_ne_zero)

lemma mem_support_uniform_of_fintype (a : α) : a ∈ (uniform_of_fintype α).support := by simp

section measure

variable (s : set α)

lemma to_outer_measure_uniform_of_fintype_apply :
  (uniform_of_fintype α).to_outer_measure s = fintype.card s / fintype.card α :=
by simpa [uniform_of_fintype]

lemma to_measure_uniform_of_fintype_apply [measurable_space α] (hs : measurable_set s) :
  (uniform_of_fintype α).to_measure s = fintype.card s / fintype.card α :=
by simpa [uniform_of_fintype, hs]

end measure

end uniform_of_fintype

end pmf
