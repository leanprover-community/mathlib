/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Sébastien Gouëzel
-/
import analysis.normed.field.basic

/-!
# Completeness in terms of `cauchy` filters vs `is_cau_seq` sequences

In this file we apply `metric.complete_of_cauchy_seq_tendsto` to prove that a `normed_ring`
is complete in terms of `cauchy` filter if and only if it is complete in terms
of `cau_seq` Cauchy sequences.
-/

universes u v
open set filter
open_locale topological_space classical

variable {β : Type v}

lemma cau_seq.tendsto_limit [normed_ring β] [hn : is_absolute_value (norm : β → ℝ)]
  (f : cau_seq β norm) [cau_seq.is_complete β norm] :
  tendsto f at_top (𝓝 f.lim) :=
_root_.tendsto_nhds.mpr
begin
  intros s os lfs,
  suffices : ∃ (a : ℕ), ∀ (b : ℕ), b ≥ a → f b ∈ s, by simpa using this,
  rcases metric.is_open_iff.1 os _ lfs with ⟨ε, ⟨hε, hεs⟩⟩,
  cases setoid.symm (cau_seq.equiv_lim f) _ hε with N hN,
  existsi N,
  intros b hb,
  apply hεs,
  dsimp [metric.ball], rw [dist_comm, dist_eq_norm],
  solve_by_elim
end

variables [normed_field β]

/-
 This section shows that if we have a uniform space generated by an absolute value, topological
 completeness and Cauchy sequence completeness coincide. The problem is that there isn't
 a good notion of "uniform space generated by an absolute value", so right now this is
 specific to norm. Furthermore, norm only instantiates is_absolute_value on normed_field.
 This needs to be fixed, since it prevents showing that ℤ_[hp] is complete
-/

open metric

lemma cauchy_seq.is_cau_seq {f : ℕ → β} (hf : cauchy_seq f) :
  is_cau_seq norm f :=
begin
  cases cauchy_iff.1 hf with hf1 hf2,
  intros ε hε,
  rcases hf2 {x | dist x.1 x.2 < ε} (dist_mem_uniformity hε) with ⟨t, ⟨ht, htsub⟩⟩,
  simp at ht, cases ht with N hN,
  existsi N,
  intros j hj,
  rw ←dist_eq_norm,
  apply @htsub (f j, f N),
  apply set.mk_mem_prod; solve_by_elim [le_refl]
end

lemma cau_seq.cauchy_seq (f : cau_seq β norm) : cauchy_seq f :=
begin
  refine cauchy_iff.2 ⟨by apply_instance, λ s hs, _⟩,
  rcases mem_uniformity_dist.1 hs with ⟨ε, ⟨hε, hεs⟩⟩,
  cases cau_seq.cauchy₂ f hε with N hN,
  existsi {n | n ≥ N}.image f,
  simp only [exists_prop, mem_at_top_sets, mem_map, mem_image, ge_iff_le, mem_set_of_eq],
  split,
  { existsi N, intros b hb, existsi b, simp [hb] },
  { rintros ⟨a, b⟩ ⟨⟨a', ⟨ha'1, ha'2⟩⟩, ⟨b', ⟨hb'1, hb'2⟩⟩⟩,
    dsimp at ha'1 ha'2 hb'1 hb'2,
    rw [←ha'2, ←hb'2],
    apply hεs,
    rw dist_eq_norm,
    apply hN; assumption }
end

/-- In a normed field, `cau_seq` coincides with the usual notion of Cauchy sequences. -/
lemma cau_seq_iff_cauchy_seq {α : Type u} [normed_field α] {u : ℕ → α} :
  is_cau_seq norm u ↔ cauchy_seq u :=
⟨λh, cau_seq.cauchy_seq ⟨u, h⟩,
 λh, h.is_cau_seq⟩

/-- A complete normed field is complete as a metric space, as Cauchy sequences converge by
assumption and this suffices to characterize completeness. -/
@[priority 100] -- see Note [lower instance priority]
instance complete_space_of_cau_seq_complete [cau_seq.is_complete β norm] : complete_space β :=
begin
  apply complete_of_cauchy_seq_tendsto,
  assume u hu,
  have C : is_cau_seq norm u := cau_seq_iff_cauchy_seq.2 hu,
  existsi cau_seq.lim ⟨u, C⟩,
  rw metric.tendsto_at_top,
  assume ε εpos,
  cases (cau_seq.equiv_lim ⟨u, C⟩) _ εpos with N hN,
  existsi N,
  simpa [dist_eq_norm] using hN
end
