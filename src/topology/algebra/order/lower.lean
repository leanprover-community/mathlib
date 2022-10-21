/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import topology.basic
import topology.order
import topology.separation
import data.set.intervals.basic
import order.upper_lower

/-!
# Lower topology

This file introduces the lower topology on a preorder. It is shown that the lower topology on a
partial order is T₀ and the non-empty complements of the upper closures of finite subsets form a
basis.

## Implementation notes

Approach inspired by `order_topology` from topology.algebra.order.basic

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

lower topology, preorder
-/

universes u
variable {α : Type u}

open  set topological_space

/--
The lower topology is the topology generated by the complements of the closed intervals to infinity
-/
class lower_topology (α : Type u) [t : topological_space α] [preorder α] : Prop :=
(topology_eq_generate_Ici_comp : t = generate_from {s | ∃a, (Ici a)ᶜ = s })

section pre_order

variables [preorder α] [topological_space α] [t: lower_topology α]

include t

lemma is_open_iff_generate_Ici_comp {s : set α} :
  is_open s ↔ generate_open {s | ∃a, (Ici a)ᶜ = s } s :=
by rw [t.topology_eq_generate_Ici_comp]; refl

/-
Left-closed right-infinite intervals [a,∞) are closed in the lower topology
-/
lemma ici_is_closed (a : α) :
  is_closed (Ici a)  :=
begin
  rw [← is_open_compl_iff, is_open_iff_generate_Ici_comp],
  fconstructor,
  rw mem_set_of_eq,
  use a,
end

/-
The upper closure of a finite subset is closed in the lower topology
-/
lemma upper_closure_is_closed (F : set α) (h : F.finite) : is_closed (upper_closure F : set α) :=
begin
  rw ← upper_set.infi_Ici,
  simp only [upper_set.coe_infi, upper_set.coe_Ici],
  apply is_closed_bUnion h,
  intros a h₁,
  apply ici_is_closed,
end

/-
Every subset open in the lower topology is a lower set
-/
lemma lower_open_is_lower {s : set α} (h: is_open s) : is_lower_set s :=
begin
  rw is_open_iff_generate_Ici_comp at h,
  induction h,
  case topological_space.generate_open.basic : u
  { rw mem_set_of_eq at h_H,
    choose a h_H using h_H,
    rw ← h_H,
    apply is_upper_set.compl,
    apply is_upper_set_Ici, },
  case topological_space.generate_open.univ : { exact is_lower_set_univ },
  case topological_space.generate_open.inter : u v hu1 hv1 hu2 hv2
    { apply is_lower_set.inter hu2 hv2 },
  case topological_space.generate_open.sUnion : { apply is_lower_set_sUnion h_ih, },
end

/-
The closure of a singleton {a} in the lower topology is the left-closed right-infinite interval
[a,∞)
-/
lemma singleton_closure (a : α) : closure {a} = Ici a :=
begin
  rw subset_antisymm_iff,
  split,
  { apply closure_minimal _ (ici_is_closed a), rw [singleton_subset_iff, mem_Ici], },
  { unfold closure,
    refine subset_sInter _,
    intro u,
    intro h,
    rw mem_set_of_eq at h,
    intro b,
    intro hb,
    rw mem_Ici at hb,
    rw [singleton_subset_iff, ← is_open_compl_iff] at h,
    by_contradiction H,
    rw ← mem_compl_iff at H,
    have h1: a ∈ uᶜ, from lower_open_is_lower h.left hb H,
    rw mem_compl_iff at h1,
    rw ← not_not_mem at h,
    apply absurd h1 h.right, },
end

end pre_order

section partial_order

variable [partial_order α]

lemma Ici_eq (a b : α) : Ici a = Ici b ↔  a = b :=
begin
  split,
  { intro h,
    rw le_antisymm_iff,
    rw subset_antisymm_iff at h,
    split,
    { rw ← Ici_subset_Ici, exact h.2, },
    { rw ← Ici_subset_Ici, exact h.1, } },
  { apply congr_arg, }
end

/--
The non-empty complements of the upper closures of finite subsets are a collection of lower sets
which form a basis for the lower topology
-/
def lower_basis (α : Type u) [preorder α] :=
  {s : set α | ∃ (F : set α),  F.finite ∧
  (upper_closure F).compl.carrier = s ∧
  (upper_closure F).compl.carrier.nonempty }

variables [topological_space α] [t: lower_topology α]

include t

lemma lower_basis_is_basis : is_topological_basis  (lower_basis α) :=
begin
  convert is_topological_basis_of_subbasis t.topology_eq_generate_Ici_comp,
  rw image,
  ext,
  rw mem_set_of_eq,
  unfold lower_basis,
  rw mem_set_of_eq,
  let g := (⟨λ a, (Ici a)ᶜ,
  begin
    intros a b,
    simp only [compl_inj_iff],
    rw Ici_eq,
    exact congr_arg (λ ⦃a : α⦄, a),
  end⟩ : α ↪ set α),
  split,
  { intro h,
    cases h with F,
    let f := {s : set α | ∃ a ∈ F,  (Ici a)ᶜ = s},
    have ef: f = {s : set α | ∃ a ∈ F, (Ici a)ᶜ = s} := by refl,
    have efn: (⋂₀ f) = (upper_closure F).compl :=
    begin
      rw [upper_set.coe_compl, ← upper_set.infi_Ici, upper_set.coe_infi],
      simp only [upper_set.coe_infi, upper_set.coe_Ici, compl_Union],
      rw ← sInter_image,
      rw ef,
      apply congr_arg,
      rw image,
      simp_rw [exists_prop],
    end,
    have ef2: f = g '' F :=
    begin
      rw [ef, image],
      simp only [exists_prop, function.embedding.coe_fn_mk],
    end,
    use f,
    rw mem_set_of_eq,
    split,
    { split,
      { rw ef2,
      rw ← finite_coe_iff,
      rw ← finite_coe_iff at h_h,
      cases h_h,
      casesI nonempty_fintype F,
      apply_instance, },
      { split,
        { simp only [set_of_subset_set_of, forall_exists_index, forall_apply_eq_imp_iff₂,
            implies_true_iff, exists_apply_eq_apply], },
        { rw efn, exact h_h.2.2 } }, },
    { rw [← h_h.2.1, efn],
      simp only [lower_set.carrier_eq_coe, upper_set.coe_compl], } },
  { intro h,
    cases h with f,
    rw mem_set_of_eq at h_h,
    let F := { a : α | (Ici a)ᶜ ∈ f },
    have eF' : F =  g ⁻¹' f := by refl,
    have eF: (⋂₀ f) = (upper_closure F).compl :=
    begin
      rw [upper_set.coe_compl, ← upper_set.infi_Ici, upper_set.coe_infi],
      simp only [upper_set.coe_infi, upper_set.coe_Ici, compl_Union],
      rw ← sInter_image,
      apply congr_arg,
      rw image,
      ext s,
      split,
      { rw mem_set_of_eq,
      intro hs,
      have es: ∃ (a : α), (Ici a)ᶜ = s := by exact h_h.1.2.1 hs,
      cases es with a,
      use a,
      split,
      { rw ← es_h at hs, rw mem_set_of_eq, exact hs, },
      { exact es_h, }, },
      { intros h,
        rw mem_set_of_eq at h,
        cases h with a,
        rw ← h_h_1.2,
        apply h_h_1.1, }
    end,
    use F,
    split,
    { cases h_h,
      cases h_h_left with hf,
      rw eF',
      apply finite.preimage_embedding,
      exact hf, },
    { split,
      { rw [← h_h.2, eF], refl, },
      { convert h_h.1.2.2,
        rw eF,
        simp only [lower_set.carrier_eq_coe], } } }
end

/-
The lower topology on a partial order is T₀.
-/
@[priority 90] -- see Note [lower instance priority]
instance lower_topology.to_t0_space : t0_space α :=
begin
  rw t0_space_iff_inseparable,
  intros x y h,
  rw [inseparable_iff_closure_eq, singleton_closure, singleton_closure, subset_antisymm_iff] at h,
  rw le_antisymm_iff,
  split,
  { rw ← Ici_subset_Ici, apply h.2, },
  { rw ← Ici_subset_Ici, apply h.1, }
end

end partial_order

section complete_semilattice_Sup

variables [topological_space α] [complete_semilattice_Sup α] [t : lower_topology α]

lemma sUnion_Ici_compl  (s : set α):
  ⋃₀ { (Ici a)ᶜ | a ∈ s } = (Ici (Sup s))ᶜ :=
begin
  rw subset_antisymm_iff,
  split,
  { rw sUnion_subset_iff,
    simp only [mem_set_of_eq, forall_exists_index, forall_apply_eq_imp_iff₂, compl_subset_compl],
    rintro a h,
    rw Ici_subset_Ici,
    apply le_Sup h, },
  { rintro a h,
    simp only [exists_prop, mem_sUnion, mem_set_of_eq, exists_exists_and_eq_and, mem_compl_iff, mem_Ici],
    simp only [mem_compl_iff, mem_Ici, Sup_le_iff, not_forall, exists_prop] at h,
    exact h, }
end

end complete_semilattice_Sup


section prod

universes v

-- c.f. topology.stone_cech
def upper_closure_prod_basis (α : Type u) (β : Type v) [partial_order α] [partial_order β] : set (set (α × β)):=
{ S : set (α × β) | ∃ (F₁ : set α) (F₂ : set β), F₁.finite
  ∧ F₂.finite ∧ ((upper_closure F₁ : set α)ᶜ ×ˢ (upper_closure F₂ : set β)ᶜ = S)
  ∧ (upper_closure F₁ : set α)ᶜ.nonempty ∧ (upper_closure F₂ : set β)ᶜ.nonempty}

variable {β : Type v}

variables [partial_order α] [topological_space α] [t: lower_topology α]
variables [topological_space β] [partial_order β] [s : lower_topology β]

include s

variables [p : lower_topology (α×β)]

#check is_topological_basis (upper_closure_prod_basis α β)

include p

lemma upper_closure_prod_basis_is_basis : is_topological_basis (upper_closure_prod_basis α β)  :=
⟨ sorry, sorry, sorry ⟩


/-
lemma prod_basis
   :
  is_topological_basis (image2 (×ˢ) S T) := sorry
-/

lemma upper_closure_prod_upper_closure (F₁ : set α) (F₂ : set β) :
  (upper_closure F₁).prod (upper_closure F₂)  =
  (⊥ : upper_set α).prod (upper_closure F₂) ⊔ (upper_closure F₁).prod (⊥ : upper_set β) :=
upper_set.ext begin
  rw subset_antisymm_iff,
  split,
  { rintros x h,
    finish, },
  { rintros x h,
    finish, },
end

lemma upper_closure_set_prod (F₁ : set α) (F₂ : set β) :
  upper_closure (F₁ ×ˢ F₂)  =
  (⊥ : upper_set α).prod (upper_closure F₂) ⊔ (upper_closure F₁).prod (⊥ : upper_set β) :=
by rw [upper_closure_prod, upper_closure_prod_upper_closure]

lemma prod_Ici (a : α) (b : β) : upper_set.Ici (a,b) =
    (⊥ : upper_set α).prod (upper_set.Ici b) ⊔ (upper_set.Ici a).prod (⊥ : upper_set β) :=
by rw [← upper_set.Ici_prod_Ici, ← upper_closure_singleton, ← upper_closure_singleton,
    upper_closure_prod_upper_closure]

lemma upper_closure_compl_prod_upper_closure_compl (F₁ : set α) (F₂ : set β)
  : ((upper_closure F₁).compl.prod (upper_closure F₂).compl)  =
  (((⊥ : upper_set α).prod (upper_closure F₂)).compl ⊓ ((upper_closure F₁).prod (⊥ : upper_set β)).compl) :=
lower_set.ext begin
  rw subset_antisymm_iff,
  split,
  { rintros x h,
    finish, },
  { rintros x h,
    simp,
    simp at h,
    rw and_comm,
    exact h, }
end

include t

instance : lower_topology (α × β) :=
{ topology_eq_generate_Ici_comp :=
  begin
    rw le_antisymm_iff,
    split,
    { apply le_generate_from,
      intros,
      rw mem_set_of_eq at H,
      rcases H,
      cases H_w,
      rw [← H_h, ← upper_set.coe_Ici, is_open_compl_iff, prod_Ici],
      apply is_closed.inter,
      { apply is_closed.prod is_closed_univ, apply ici_is_closed, },
      { apply is_closed.prod, apply ici_is_closed, apply is_closed_univ, } },
    { sorry }
  end }

end prod

section prime

variables [has_inf α] [has_le α]

/--
An element `a` is said to be prime if whenever `a ≤ b ⊓ c` at least one of `a ≤ b`, `a ≤ c` holds.
-/
def is_prime (a : α) : Prop := ∀ b c, a ≤ b ⊓ c → a ≤ b ∨ a ≤ c

/-
The subtype of prime elements of a partial order with inf
-/
-- def prime (β : Type u) [has_inf β] [has_le β] := {a : β // is_prime a}

end prime
