/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import order.upper_lower
import topology.separation

/-!
# Lower topology

This file introduces the lower topology on a preorder. It is shown that the lower topology on a
partial order is T₀ and the complements of the upper closures of finite subsets form a basis.

## Implementation notes

Approach inspired by `order_topology`.

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

lower topology, preorder
-/

universe u

variable (α : Type u)

open set topological_space

section preorder

variable [preorder α]

/--
Type synonym for a preorder equipped with the lower topology
-/
@[derive preorder, nolint unused_arguments]
def with_lower_topology := α

instance [p : nonempty α] : nonempty (with_lower_topology α) := p
instance [p : inhabited α] : inhabited (with_lower_topology α) := p

/--
The lower topology is the topology generated by the complements of the closed intervals to infinity.
-/
def lower_topology : topological_space α := generate_from {s | ∃ a, (Ici a)ᶜ = s}

instance : topological_space (with_lower_topology α) := lower_topology (with_lower_topology α)

namespace lower_topology

variable {α}

lemma is_open_iff_generate_Ici_comp {s : set (with_lower_topology α)} :
  is_open s ↔ generate_open {s | ∃ a, (Ici a)ᶜ = s} s := iff.rfl

/--
Left-closed right-infinite intervals [a,∞) are closed in the lower topology
-/
lemma is_closed_Ici (a : with_lower_topology α) : is_closed (Ici a) :=
is_open_compl_iff.1 $ generate_open.basic _ ⟨a, rfl⟩

/--
The upper closure of a finite subset is closed in the lower topology.
-/
lemma is_closed_upper_closure (F : set (with_lower_topology α)) (h : F.finite) :
  is_closed (upper_closure F : set (with_lower_topology α)) :=
begin
  simp only [← upper_set.infi_Ici, upper_set.coe_infi],
  exact is_closed_bUnion h (λ a h₁, is_closed_Ici a),
end

/--
Every subset open in the lower topology is a lower set.
-/
lemma is_lower_set_of_is_open {s : set (with_lower_topology α)} (h : is_open s) : is_lower_set s :=
begin
  rw is_open_iff_generate_Ici_comp at h,
  induction h,
  case generate_open.basic : u h { obtain ⟨a, rfl⟩ := h, exact (is_upper_set_Ici a).compl },
  case univ : { exact is_lower_set_univ },
  case inter : u v hu1 hv1 hu2 hv2 { exact hu2.inter hv2 },
  case sUnion : _ _ ih { exact is_lower_set_sUnion ih },
end

lemma is_upper_set_of_is_closed {s : set (with_lower_topology α)} (h : is_closed s) :
  is_upper_set s := is_lower_set_compl.1 $ is_lower_set_of_is_open h.is_open_compl

/--
The closure of a singleton {a} in the lower topology is the left-closed right-infinite interval
[a,∞).
-/
@[simp] lemma closure_singleton (a : with_lower_topology α) : closure {a} = Ici a :=
subset_antisymm (closure_minimal (λ b h, h.ge) $ is_closed_Ici a) $
  (is_upper_set_of_is_closed is_closed_closure).Ici_subset (subset_closure rfl)

/--
The complements of the upper closures of finite subsets are a collection of lower sets
which form a basis for the lower topology.
-/
def lower_basis (α : Type u) [preorder α] :=
{s : set α | ∃ (F : set α), F.finite ∧ ↑(upper_closure F).compl = s}

lemma is_topological_basis : is_topological_basis (lower_basis (with_lower_topology α)) :=
begin
  convert is_topological_basis_of_subbasis rfl,
  simp_rw [lower_basis, upper_set.coe_compl, coe_upper_closure, compl_set_of],
  push_neg, simp_rw set_of_forall,
  ext s, split,
  { rintro ⟨F, hF, rfl⟩,
    refine ⟨(λ a, (Ici a)ᶜ) '' F, ⟨hF.image _, image_subset_iff.2 $ λ _ _, ⟨_, rfl⟩⟩, _⟩,
    rw sInter_image, refl },
  { rintro ⟨F, ⟨hF, hs⟩, rfl⟩,
    haveI := hF.to_subtype,
    rw [subset_def, subtype.forall'] at hs,
    choose f he using hs,
    refine ⟨_, finite_range f, set.ext $ λ a, _⟩,
    simp_rw [bInter_range, Inter_subtype, ←compl_set_of, Ici_def, he, mem_Inter₂],
    refl },
end

end lower_topology

end preorder

section partial_order

variables (α) [partial_order α]

instance : partial_order (with_lower_topology α) := ‹partial_order α›

/-
The lower topology on a partial order is T₀.
-/
@[priority 90] -- see Note [lower instance priority]
instance : t0_space (with_lower_topology α) :=
(t0_space_iff_inseparable _).2 $ λ x y h, by simpa only
  [inseparable_iff_closure_eq, lower_topology.closure_singleton, Ici_inj] using h

end partial_order
