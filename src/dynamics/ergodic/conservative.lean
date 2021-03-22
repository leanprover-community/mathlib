/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import dynamics.ergodic.measure_preserving

/-!
# Conservative systems

In this file we define `f : α → α` to be a *conservative* system w.r.t a measure `μ` if `f` is
non-singular (`measure_theory.quasi_measure_preserving`) and for every measurable set `s` of
positive measure at least one point `x ∈ s` returns back to `s` after some number of iterations of
`f`.
-/

noncomputable theory

open classical set filter measure_theory finset function topological_space
open_locale classical topological_space

variables {ι : Type*} {α : Type*} [measurable_space α] {f : α → α} {s : set α} {μ : measure α}

namespace measure_theory

open measure

structure conservative (f : α → α) (μ : measure α . volume_tac)
  extends quasi_measure_preserving f μ μ : Prop :=
(exists_mem_image_mem : ∀ ⦃s⦄, measurable_set s → μ s ≠ 0 → ∃ (x ∈ s) (m ≠ 0), f^[m] x ∈ s)

protected lemma measure_preserving.conservative [finite_measure μ] (h : measure_preserving f μ μ) : conservative f μ :=
⟨h.quasi_measure_preserving, λ s hsm h0, h.exists_mem_image_mem hsm h0⟩

/-- The set of points `x ∈ s` such that do not return to `s` after `n` iterations is measurable.  -/
lemma measurable_set_not_recurrent (hf : measurable f) (hs : measurable_set s) (n : ℕ) :
  measurable_set {x ∈ s | ∀ m ≥ n, f^[m] x ∉ s} :=
begin
  simp only [set.sep_def, set_of_forall, ← compl_set_of],
  exact hs.inter (measurable_set.Inter $ λ m, measurable_set.Inter_Prop $
    λ hm, hf.iterate m hs.compl)
end

namespace conservative

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for infinitely many values of `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
lemma frequently_measure_inter_ne_zero (hf : conservative f μ) (hs : measurable_set s)
  (h0 : μ s ≠ 0) :
  ∃ᶠ m in at_top, μ (s ∩ (f^[m]) ⁻¹' s) ≠ 0 :=
begin
  by_contra H, simp only [not_frequently, eventually_at_top, ne.def, not_not] at H,
  rcases H with ⟨N, hN⟩,
  induction N with N ihN,
  { apply h0, simpa using hN 0 le_rfl },
  rw [imp_false] at ihN, push_neg at ihN,
  rcases ihN with ⟨n, hn, hμn⟩,
  set T := s ∩ ⋃ n ≥ N + 1, (f^[n]) ⁻¹' s,
  have hT : measurable_set T,
    from hs.inter (measurable_set.bUnion (countable_encodable _)
      (λ _ _, hf.measurable.iterate _ hs)),
  have hμT : μ T = 0,
  { convert (measure_bUnion_null_iff $ countable_encodable _).2 hN,
    rw ← set.inter_bUnion, refl },
  have : μ ((s ∩ (f^[n]) ⁻¹' s) \ T) ≠ 0, by rwa [measure_diff_null hμT],
  rcases hf.exists_mem_image_mem ((hs.inter (hf.measurable.iterate n hs)).diff hT) this
    with ⟨x, ⟨⟨hxs, hxn⟩, hxT⟩, m, hm0, ⟨hxms, hxm⟩, hxx⟩,
  refine hxT ⟨hxs, mem_bUnion_iff.2 ⟨n + m, _, _⟩⟩,
  { exact add_le_add hn (nat.one_le_of_lt $ pos_iff_ne_zero.2 hm0) },
  { rwa [set.mem_preimage, ← iterate_add_apply] at hxm }
end

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for an arbitrafily large `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
lemma exists_gt_measure_inter_ne_zero (hf : conservative f μ) (hs : measurable_set s) (h0 : μ s ≠ 0)
  (N : ℕ) :
  ∃ m > N, μ (s ∩ (f^[m]) ⁻¹' s) ≠ 0 :=
let ⟨m, hm, hmN⟩ :=
  ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_at_top N)).exists
in ⟨m, hmN, hm⟩

lemma measure_mem_forall_ge_image_not_mem_eq_zero (hf : conservative f μ) (hs : measurable_set s)
  (n : ℕ) :
  μ {x ∈ s | ∀ m ≥ n, f^[m] x ∉ s} = 0 :=
begin
  by_contradiction H,
  rcases (hf.exists_gt_measure_inter_ne_zero (measurable_set_not_recurrent hf.measurable hs n) H) n
    with ⟨m, hmn, hm⟩,
  rcases nonempty_of_measure_ne_zero hm with ⟨x, ⟨hxs, hxn⟩, hxm, -⟩,
  exact hxn m hmn.lt.le hxm
end

/-- Poincaré recurrence theorem: given a volume preserving map `f` and a measurable set `s`,
almost every point `x ∈ s`-/
lemma ae_mem_imp_frequently_image_mem (hf : conservative f μ) (hs : measurable_set s) :
  ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in at_top, (f^[n] x) ∈ s :=
begin
  simp only [frequently_at_top, @forall_swap (_ ∈ s), ae_all_iff],
  intro n,
  filter_upwards [measure_zero_iff_ae_nmem.1 (hf.measure_mem_forall_ge_image_not_mem_eq_zero hs n)],
  simp
end

/-- Poincaré recurrence theorem. Let `f : α → α` be a conservative dynamical system on a topological
space with second countable topology and measurable open sets. Then almost every point `x : α`
is recurrent: it visits every neighborhood `s ∈ 𝓝 x` infinitely many times. -/
lemma ae_frequently_mem_of_mem_nhds [topological_space α] [second_countable_topology α]
  [opens_measurable_space α] {f : α → α} {μ : measure α} (h : conservative f μ) :
  ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, ∃ᶠ n in at_top, f^[n] x ∈ s :=
begin
  rcases is_open_generated_countable_inter α with ⟨S, hSc, he, hSb⟩,
  have : ∀ s ∈ S, ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in at_top, (f^[n] x) ∈ s,
    from λ s hs, h.ae_mem_imp_frequently_image_mem
      (is_open_of_is_topological_basis hSb hs).measurable_set,
  refine ((ae_ball_iff hSc).2 this).mono (λ x hx s hs, _),
  rcases (mem_nhds_of_is_topological_basis hSb).1 hs with ⟨o, hoS, hxo, hos⟩,
  exact (hx o hoS hxo).mono (λ n hn, hos hn)
end

end conservative

end measure_theory
