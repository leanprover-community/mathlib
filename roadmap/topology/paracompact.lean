import roadmap.todo
import topology.subset_properties
import topology.separation
import topology.metric_space.basic

open set filter

universe u

class paracompact_space (X : Type u) [topological_space X] : Prop :=
(locally_finite_refinement :
  ∀ {α : Type u} (u : α → set X) (uo : ∀ a, is_open (u a)) (uc : Union u = univ),
  ∃ {β : Type u} (v : β → set X) (vo : ∀ b, is_open (v b)) (vc : Union v = univ),
  locally_finite v ∧ ∀ b, ∃ a, v b ⊆ u a)

/-- Any open cover of a paracompact space has a locally finite *precise* refinement, that is,
 one indexed on the same type with each open set contained in the corresponding original one. -/
lemma paracompact_space.precise_refinement {X : Type u} [topological_space X] [paracompact_space X]
  {α : Type u} (u : α → set X) (uo : ∀ a, is_open (u a)) (uc : Union u = univ) :
  ∃ v : α → set X, (∀ a, is_open (v a)) ∧ Union v = univ ∧ locally_finite v ∧ (∀ a, v a ⊆ u a) :=
begin
  obtain ⟨β, w, wo, wc, lfw, wr⟩ := paracompact_space.locally_finite_refinement u uo uc,
  choose f hf using wr,
  refine ⟨λ a, ⋃₀ {s | ∃ b, f b = a ∧ s = w b}, λ a, _, _, _, λ a, _⟩,
  { apply is_open_sUnion _,
    rintros t ⟨b, rfl, rfl⟩,
    apply wo },
  { exact todo },
  { exact todo },
  { apply sUnion_subset,
    rintros t ⟨b, rfl, rfl⟩,
    apply hf }
end

lemma paracompact_of_compact {X : Type u} [topological_space X] [compact_space X] :
  paracompact_space X :=
begin
  refine ⟨λ α u uo uc, _⟩,
  obtain ⟨s, _, sf, sc⟩ :=
    compact_univ.elim_finite_subcover_image (λ a _, uo a) (by rwa [univ_subset_iff, bUnion_univ]),
  refine ⟨s, λ b, u b.val, λ b, uo b.val, _, _, λ b, ⟨b.val, subset.refl _⟩⟩,
  { exact todo },
  { intro x,
    refine ⟨univ, univ_mem_sets, _⟩,
    exact todo },
end

lemma normal_of_paracompact_t2 {X : Type u} [topological_space X] [t2_space X]
  [paracompact_space X] : normal_space X :=
todo
/-
Similar to the proof of `generalized_tube_lemma`, but different enough not to merge them.
Lemma: if `s : set X` is closed and can be separated from any point by open sets,
then `s` can also be separated from any closed set by open sets. Apply twice.

See
* Bourbaki, General Topology, Chapter IX, §4.4
* https://ncatlab.org/nlab/show/paracompact+Hausdorff+spaces+are+normal
-/

lemma paracompact_of_metric {X : Type u} [metric_space X] : paracompact_space X :=
todo
/-
See Mary Ellen Rudin, A new proof that metric spaces are paracompact.
https://www.ams.org/journals/proc/1969-020-02/S0002-9939-1969-0236876-3/S0002-9939-1969-0236876-3.pdf
-/
