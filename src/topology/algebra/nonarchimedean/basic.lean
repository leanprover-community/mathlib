/-
Copyright (c) 2021 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard, Johan Commelin, Ashwin Iyengar, Patrick Massot.
-/
import topology.algebra.ring
import topology.algebra.open_subgroup
import data.set.basic
import group_theory.subgroup
import algebra.ring.prod

/-!
# Nonarchimedean Topology

In this file we set up the theory of nonarchimedean topological groups and rings.

A nonarchimedean group is a topological group whose topology admits a basis of
open neighborhoods of the identity element in the group consisting of open subgroups.
A nonarchimedean ring is a topological ring whose underlying topological (additive)
group is nonarchimedean.

## Definitions

- `nonarchimedean_add_group`: nonarchimedean additive group.
- `nonarchimedean_group`: nonarchimedean multiplicative group.
- `nonarchimedean_ring`: nonarchimedean ring.

-/

namespace set

variables {α : Type*} {β : Type*}
variables {s s₁ : set α} {t t₁ : set β}

/-- If a product of s and t are subsets of P then the product of
  two subsets of s and t (respectively) is a subset of P. -/
lemma prod_subset_of_subsets {P : set (α × β)}:
  s.prod t ⊆ P → s₁ ⊆ s → t₁ ⊆ t → s₁.prod t₁ ⊆ P :=
begin
  intros hP hs ht,
  rw prod_subset_iff,
  intros x hx y hy,
  apply hP,
  rw prod_mk_mem_set_prod_eq,
  exact ⟨hs hx, ht hy⟩
end

end set

/-- The cartesian product of two topological rings acquires a natural topology. -/
instance (R S : Type*) [ring R] [ring S] [topological_space R] [topological_space S]
  [topological_ring R] [topological_ring S] : topological_ring (R × S) :=
{ continuous_neg := continuous_neg }

/-- An topological additive group is nonarchimedean if every neighborhood of 0
  contains an open subgroup. -/
class nonarchimedean_add_group (G : Type*)
  [add_group G] [topological_space G] extends topological_add_group G : Prop :=
(is_nonarchimedean : ∀ U ∈ nhds (0 : G), ∃ V : open_add_subgroup G, (V : set G) ⊆ U)

/-- A topological group is nonarchimedean if every neighborhood of 1 contains an open subgroup. -/
@[to_additive]
class nonarchimedean_group (G : Type*)
  [group G] [topological_space G] extends topological_group G : Prop :=
(is_nonarchimedean : ∀ U ∈ nhds (1 : G), ∃ V : open_subgroup G, (V : set G) ⊆ U)

/-- An topological ring is non-archimedean if its underlying topological additive
  group is nonarchimedean. -/
class nonarchimedean_ring (R : Type*)
  [ring R] [topological_space R] extends topological_ring R : Prop :=
(is_nonarchimedean : ∀ U ∈ nhds (0 : R), ∃ V : open_add_subgroup R, (V : set R) ⊆ U)

export nonarchimedean_add_group (is_nonarchimedean)
export nonarchimedean_group (is_nonarchimedean)
export nonarchimedean_ring (is_nonarchimedean)

/-- Every nonarchimedean ring is naturally a nonarchimedean additive group. -/
instance nonarchimedean_ring.to_nonarchimedean_add_group
  (R : Type*) [ring R] [topological_space R] [t: nonarchimedean_ring R] :
nonarchimedean_add_group R := {..t}

namespace nonarchimedean_group

variables {G : Type*} [group G] [topological_space G] [nonarchimedean_group G]
variables {H : Type*} [group H] [topological_space H] [topological_group H]
variables {K : Type*} [group K] [topological_space K] [nonarchimedean_group K]

/-- If a topological group embeds into a nonarchimedean group, then it
  is nonarchimedean. -/
@[to_additive nonarchimedean_add_group.emb_of_nonarchimedean]
lemma emb_of_nonarchimedean (f : G →* H) (emb : open_embedding f) : nonarchimedean_group H :=
{ is_nonarchimedean := λ U hU, have h₁ : (f ⁻¹' U) ∈ nhds (1 : G), from
    by {apply emb.continuous.tendsto, rwa is_group_hom.map_one f},
  let ⟨V, hV⟩ := is_nonarchimedean (f ⁻¹' U) h₁ in
    ⟨{is_open' := emb.is_open_map _ V.is_open, ..subgroup.map f V},
      set.image_subset_iff.2 hV⟩ }

/-- An open neighborhood of the identity in the cartesian product of two nonarchimedean groups
  contains the cartesian product of an open neighborhood in each group. -/
@[to_additive nonarchimedean_add_group.prod_subset]
lemma prod_subset :
  ∀ U ∈ nhds (1 : G × K), ∃ (V : open_subgroup G) (W : open_subgroup K),
    (V : set G).prod (W : set K) ⊆ U :=
begin
  intros U hU,
  erw [nhds_prod_eq, filter.mem_prod_iff] at hU,
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩,
  cases is_nonarchimedean _ hU₁ with V hV,
  cases is_nonarchimedean _ hU₂ with W hW,
  use V, use W,
  rw set.prod_subset_iff,
  intros x hX y hY,
  refine set.prod_subset_of_subsets h hV hW _,
  exact set.mem_sep hX hY,
end

/-- An open neighborhood of the identity in the cartesian square of two nonarchimedean groups
  contains the cartesian product of an open neighborhood in each group. -/
@[to_additive nonarchimedean_add_group.prod_self_subset]
lemma prod_self_subset :
  ∀ U ∈ nhds (1 : G × G), ∃ (V : open_subgroup G), (V : set G).prod (V : set G) ⊆ U :=
λ U hU, let ⟨V, W, h⟩ := prod_subset U hU in
  ⟨V ⊓ W, by {refine set.subset.trans (set.prod_mono _ _) ‹_›; simp}⟩

/-- The cartesian product of two nonarchimedean groups is nonarchimedean. -/
@[to_additive]
instance : nonarchimedean_group (G × K) :=
{ is_nonarchimedean := λ U hU, let ⟨V, W, h⟩ := prod_subset U hU in ⟨V.prod W, ‹_›⟩ }

end nonarchimedean_group

namespace nonarchimedean_ring

open nonarchimedean_ring
open nonarchimedean_add_group

variables {R S : Type*}
variables [ring R] [topological_space R] [nonarchimedean_ring R]
variables [ring S] [topological_space S] [nonarchimedean_ring S]

/-- The cartesian product of two nonarchimedean rings is nonarchimedean. -/
instance : nonarchimedean_ring (R × S) :=
{ is_nonarchimedean := nonarchimedean_add_group.is_nonarchimedean }

/-- If you multiply an element of a nonarchimedean ring by an open subgroup,
  the product still contains an open subgroup. -/
lemma left_mul_subset (U : open_add_subgroup R) (r : R) :
  ∃ V : open_add_subgroup R, r • (V : set R) ⊆ U :=
⟨{is_open' := is_open.preimage (continuous_mul_left r) U.is_open,
  ..add_subgroup.comap (add_monoid_hom.mul_left r) U},
set.image_preimage_subset (λ x, (add_monoid_hom.mul_left r) x) U⟩

/-- An open subset of a topological ring contains the square of another one. -/
lemma mul_subset (U : open_add_subgroup R) :
  ∃ V : open_add_subgroup R, (V : set R) * V ⊆ U :=
let ⟨V, H⟩ := prod_self_subset ((λ r : R × R, r.1 * r.2) ⁻¹' ↑U)
  (mem_nhds_sets (is_open.preimage continuous_mul U.is_open)
  begin
    simpa only [set.mem_preimage, open_add_subgroup.mem_coe, prod.snd_zero, mul_zero]
      using U.zero_mem,
  end) in
begin
  use V,
  intros v hv,
  rcases hv with ⟨a, b, ha, hb, hv⟩,
  have hy := H (set.mk_mem_prod ha hb),
  simp only [set.mem_preimage, open_add_subgroup.mem_coe] at hy,
  rwa hv at hy
end

end nonarchimedean_ring
