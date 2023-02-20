/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import logic.equiv.defs
import order.directed
import order.upper_lower.basic
import topology.basic
import topology.order
import topology.continuous_function.basic

/-!
# Scott topology

This file introduces the Scott topology on a preorder.

## Main definitions

- `preserve_lub_on_directed` - a function between preorders which preserves least upper bounds.
- `directed_lub_mem_implies_tail_subset` - the topological space where a set `u` is open if, when
  the least upper bound of a directed set `d` lies in `u` then there is a tail of `d` which is a
  subset of `u`.
- `with_scott_topology.topological_space` - the Scott topology is defined as the join of the
  `directed_lub_mem_implies_tail_subset` topology and the topology of upper sets.

## Main statements

- `with_scott_topology.is_open_is_upper` - Scott open sets are upper
- `with_scott_topology.is_closed_is_lower` - Scott closed sets are lower
- `with_scott_topology.continuous_monotone` - Scott continuous functions are monotone.
- `preserve_lub_on_directed_iff_scott_continuity` - a function preserves least upper bounds of
  directed sets if and only if it is Scott continuous
- `with_scott_topology.t0_space` - the Scott topology on a partial order is T₀

## Implementation notes

A type synonym `with_scott_topology` is introduced and for a preorder `α`, `with_scott_topology α`
is made an instance of `topological_space` by the topology generated by the complements of the
closed intervals to infinity.

A class `Scott` is defined in `topology.omega_complete_partial_order` and made an instance of a
topological space by defining the open sets to be those which have characteristic functions which
are monotone and preserve limits of countable chains. Whilst this definition of the Scott topology
coincides with the one given here in some special cases, in general they are not the same
[Domain Theory, 2.2.4][abramsky_gabbay_maibaum_1994].

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]
* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]

## Tags

Scott topology, preorder

-/

variables (α β : Type*)

open set

section preorder

variables {α} {β}

variables [preorder α] [preorder β]

lemma is_upper_set_iff_forall_le  {s : set α} : is_upper_set s ↔ ∀ ⦃a b : α⦄, a ≤ b →
  a ∈ s → b ∈ s := iff.rfl

/--
The set of upper sets forms a topology
-/
def upper_set_topology : topological_space α :=
{ is_open := is_upper_set,
  is_open_univ := is_upper_set_univ,
  is_open_inter := λ _ _, is_upper_set.inter,
  is_open_sUnion := λ _, is_upper_set_sUnion }

/--
The set of sets satisfying "property (S)" ([GierzEtAl1980] p100) form a topology
-/
def directed_lub_mem_implies_tail_subset : topological_space α :=
{ is_open := λ u, ∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → a ∈ u →
               ∃ b ∈ d, (Ici b)∩ d ⊆ u,
  is_open_univ := begin
    intros d a hd₁ hd₂ hd₃ ha,
    cases hd₁ with b hb,
    use b,
    split,
    { exact hb, },
    { exact (Ici b ∩ d).subset_univ, },
  end,
  is_open_inter := begin
    rintros s t,
    intros hs,
    intro ht,
    intros d a hd₁ hd₂ hd₃ ha,
    cases (hs d a hd₁ hd₂ hd₃ ha.1) with b₁ hb₁,
    cases (ht d a hd₁ hd₂ hd₃ ha.2) with b₂ hb₂,
    cases hb₁,
    cases hb₂,
    rw directed_on at hd₂,
    cases (hd₂ b₁ hb₁_w b₂ hb₂_w) with c hc,
    cases hc,
    use c,
    split,
    { exact hc_w, },
    { calc Ici c ∩ d ⊆ (Ici b₁ ∩ Ici b₂)∩d : by
        { apply inter_subset_inter_left d,
          apply subset_inter (Ici_subset_Ici.mpr hc_h.1) (Ici_subset_Ici.mpr hc_h.2), }
        ... = ((Ici b₁)∩d) ∩ ((Ici b₂)∩d) : by rw inter_inter_distrib_right
        ... ⊆ s ∩ t : by { exact inter_subset_inter hb₁_h hb₂_h } }
  end,
  is_open_sUnion := begin
  intros s h,
  intros d a hd₁ hd₂ hd₃ ha,
  rw mem_sUnion at ha,
  cases ha with s₀ hs₀,
  cases hs₀,
  cases (h s₀ hs₀_w d a hd₁ hd₂ hd₃ hs₀_h) with b hb,
  use b,
  cases hb,
  split,
  { exact hb_w, },
  { exact subset_sUnion_of_subset s s₀ hb_h hs₀_w, }
  end, }

lemma pair_is_chain (a b : α) (hab: a ≤ b) : is_chain (≤) ({a, b} : set α) :=
begin
  apply is_chain.insert (set.subsingleton.is_chain subsingleton_singleton),
  intros c h₁ h₂,
  rw mem_singleton_iff at h₁,
  rw h₁,
  exact or.inl hab,
end

lemma directed_on_pair (a b : α) (hab: a ≤ b) : directed_on (≤) ({a, b} : set α) :=
  (pair_is_chain _ _ hab).directed_on

/--
A function which preserves lub on directed sets
-/
def preserve_lub_on_directed (f : α → β) := ∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d →
  is_lub d a → is_lub (f '' d) (f(a))

lemma preserve_lub_on_directed_montotone (f : α → β) (h: preserve_lub_on_directed f): monotone f :=
begin
  intros a b hab,
  rw preserve_lub_on_directed at h,
  let d := ({a, b} : set α),
  have e1: is_lub (f '' d) (f b),
  { apply h,
    { exact insert_nonempty a {b} },
    { exact directed_on_pair a b hab },
    { rw is_lub,
      split,
      { simp only [upper_bounds_insert, upper_bounds_singleton, mem_inter_iff, mem_Ici, le_refl,
          and_true],
        exact hab, },
      { simp only [upper_bounds_insert, upper_bounds_singleton],
        rw (inter_eq_self_of_subset_right (Ici_subset_Ici.mpr hab)),
        exact λ {x : α}, mem_Ici.mpr, } }, },
  rw [is_lub, is_least] at e1,
  cases e1,
  apply e1_left,
  rw mem_image,
  use a,
  simp only [mem_insert_iff, eq_self_iff_true, true_or, and_self],
end

end preorder

/--
Type synonym for a preorder equipped with the Scott topology
-/
def with_scott_topology := α

variables {α β}

namespace with_scott_topology

/-- `to_scott` is the identity function to the `with_scott_topology` of a type.  -/
@[pattern] def to_scott : α ≃ with_scott_topology α := equiv.refl _

/-- `of_scott` is the identity function from the `with_scott_topology` of a type.  -/
@[pattern] def of_scott : with_scott_topology α ≃ α := equiv.refl _

@[simp] lemma to_scott_symm_eq : (@to_scott α).symm = of_scott := rfl
@[simp] lemma of_scott_symm_eq : (@of_scott α).symm = to_scott := rfl
@[simp] lemma to_scott_of_scott (a : with_scott_topology α) : to_scott (of_scott a) = a := rfl
@[simp] lemma of_scott_to_scott (a : α) : of_scott (to_scott a) = a := rfl
@[simp] lemma to_scott_inj {a b : α} : to_scott a = to_scott b ↔ a = b := iff.rfl
@[simp] lemma of_scott_inj {a b : with_scott_topology α} : of_scott a = of_scott b ↔ a = b :=
iff.rfl

/-- A recursor for `with_scott_topology`. Use as `induction x using with_scott_topology.rec`. -/
protected def rec {β : with_scott_topology α → Sort*}
  (h : Π a, β (to_scott a)) : Π a, β a := λ a, h (of_scott a)


instance [nonempty α] : nonempty (with_scott_topology α) := ‹nonempty α›
instance [inhabited α] : inhabited (with_scott_topology α) := ‹inhabited α›

end with_scott_topology

section preorder

variables [preorder α] [preorder β]

instance : preorder (with_scott_topology α) := ‹preorder α›

instance : topological_space (with_scott_topology α) :=
  (upper_set_topology ⊔ directed_lub_mem_implies_tail_subset)

namespace with_scott_topology

lemma is_open_eq_upper_and_lub_mem_implies_tail_subset (u : set (with_scott_topology α)) : is_open u
= (is_upper_set u ∧ ∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → a ∈ u
  → ∃ b ∈ d, (Ici b) ∩ d ⊆ u) := rfl

lemma is_open_eq_upper_and_lub_mem_implies_inter_nonempty (u : set (with_scott_topology α)) :
is_open u = (is_upper_set u ∧
∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → a ∈ u → (d∩u).nonempty) :=
begin
  rw [is_open_eq_upper_and_lub_mem_implies_tail_subset, eq_iff_iff],
  split,
  { refine and.imp_right _,
    intros h d a d₁ d₂ d₃ ha,
    cases (h d a d₁ d₂ d₃ ha) with b,
    rw inter_nonempty_iff_exists_left,
    use b,
    cases h_1,
    split,
    { exact h_1_w, },
    { apply mem_of_subset_of_mem h_1_h,
      rw mem_inter_iff,
      split,
      { exact left_mem_Ici, },
      { exact h_1_w, } } },
  { intros h,
    split,
    { exact h.1, },
    { intros d a d₁ d₂ d₃ ha,
      have e1 : (d ∩ u).nonempty := by exact h.2 d a d₁ d₂ d₃ ha,
      rw inter_nonempty_iff_exists_left at e1,
      cases e1 with b,
      cases e1_h,
      use b,
      split,
      { exact e1_h_w, },
      { have e2 : Ici b ⊆ u := by exact is_upper_set_iff_Ici_subset.mp h.1 e1_h_h,
      apply subset.trans _ e2,
      apply inter_subset_left, }, }, }
end

lemma is_closed_eq_lower_and_subset_implies_lub_mem (s : set (with_scott_topology α)) : is_closed s
  = (is_lower_set s ∧
  ∀ (d : set α) (a : α), d.nonempty → directed_on (≤) d → is_lub d a → d ⊆ s → a ∈ s ) :=
begin
  rw [← is_open_compl_iff, is_open_eq_upper_and_lub_mem_implies_inter_nonempty,
    is_lower_set_compl.symm, compl_compl],
  refine let_value_eq (and (is_lower_set s)) _,
  rw eq_iff_iff,
  split,
  { intros h d a d₁ d₂ d₃ d₄,
    by_contra h',
    rw ← mem_compl_iff at h',
    have c1: (d ∩ sᶜ).nonempty := by exact h d a d₁ d₂ d₃ h',
    have c2: (d ∩ sᶜ) =  ∅,
    { rw [← subset_empty_iff, ← inter_compl_self s],
      exact inter_subset_inter_left _ d₄, },
    rw c2 at c1,
    simp only [not_nonempty_empty] at c1,
    exact c1, },
  { intros h d a d₁ d₂ d₃ d₄,
    by_contra h',
    rw [inter_compl_nonempty_iff, not_not] at h',
    have c1: a ∈ s := by exact h d a d₁ d₂ d₃ h',
    contradiction, }
end

lemma is_open_is_upper {s : set (with_scott_topology α)} : is_open s → is_upper_set s :=
begin
  intros h,
  rw is_open_eq_upper_and_lub_mem_implies_tail_subset at h,
  exact h.1,
end

lemma is_closed_is_lower {s : set (with_scott_topology α)} : is_closed s → is_lower_set s :=
begin
  intro h,
  rw is_closed_eq_lower_and_subset_implies_lub_mem at h,
  exact h.1,
end

/--
The closure of a singleton `{a}` in the Scott topology is the right-closed left-infinite interval
(-∞,a].
-/
@[simp] lemma closure_singleton (a : with_scott_topology α) : closure {a} = Iic a :=
begin
  rw ← lower_set.coe_Iic,
  rw ← lower_closure_singleton,
  refine subset_antisymm _ _,
  { apply closure_minimal subset_lower_closure,
    rw is_closed_eq_lower_and_subset_implies_lub_mem,
    split,
    { exact (lower_closure {a}).lower },
    { rw lower_closure_singleton,
      intros d b d₁ d₂ d₃ d₄,
      rw [lower_set.coe_Iic, mem_Iic],
      exact (is_lub_le_iff d₃).mpr d₄, } },
  { apply lower_closure_min subset_closure (is_closed_is_lower _),
    apply is_closed_closure, }
end

lemma continuous_monotone {f : with_scott_topology α → with_scott_topology β}
  (hf : continuous f) : monotone f :=
begin
  rw monotone,
  intros a b hab,
  let u := (Iic (f b))ᶜ,
  by_contra,
  have u2 : a ∈ (f⁻¹'  u) := h,
  have s1 : is_open u,
  { rw [is_open_compl_iff, ← closure_singleton],
    exact is_closed_closure, },
  have s2 :  is_open (f⁻¹'  u) := is_open.preimage hf s1,
  have u3 : b ∈ (f⁻¹'  u) := is_upper_set_iff_forall_le.mp s2.1 hab u2,
  have c1 : f b ∈ (Iic (f b))ᶜ,
  { simp only [mem_compl_iff, mem_preimage, mem_Iic, le_refl, not_true] at u3,
    simp only [mem_compl_iff, mem_Iic, le_refl, not_true],
    exact u3, },
  simp only [mem_compl_iff, mem_Iic, le_refl, not_true] at c1,
  exact c1,
end

end with_scott_topology

lemma preserve_lub_on_directed_iff_scott_continuity
  (f : (with_scott_topology α) → (with_scott_topology β)) :
  preserve_lub_on_directed f ↔ continuous f :=
begin
  split,
  { intro h,
    rw continuous_def,
    intros u hu,
    rw with_scott_topology.is_open_eq_upper_and_lub_mem_implies_inter_nonempty,
    split,
    { apply is_upper_set.preimage (with_scott_topology.is_open_is_upper hu),
      apply preserve_lub_on_directed_montotone,
      exact h, },
    { intros d a hd₁ hd₂ hd₃ ha,
    have e1: is_lub (f '' d) (f(a)),
    { apply h,
      apply hd₁,
      apply hd₂,
      apply hd₃, },
    rw with_scott_topology.is_open_eq_upper_and_lub_mem_implies_inter_nonempty at hu,
    have e2: ((f '' d) ∩ u).nonempty,
    { apply hu.2,
      exact nonempty.image f hd₁,
      have e3: monotone f := begin
        apply preserve_lub_on_directed_montotone,
        exact h,
      end,
      apply directed_on_image.mpr,
      exact directed_on.mono hd₂ e3,
      apply e1,
      exact ha, },
    exact image_inter_nonempty_iff.mp e2, } },
  { intros hf d a d₁ d₂ d₃,
    rw is_lub,
      split,
  { apply monotone.mem_upper_bounds_image (with_scott_topology.continuous_monotone hf),
    rw ← is_lub_le_iff,
    exact d₃, },
  { rw [lower_bounds, mem_set_of_eq],
    intros b hb,
    let u := (Iic b)ᶜ,
    by_contra,
    have e1: a ∈ (f⁻¹'  u) := h,
    have s1 : is_open u,
    { rw [is_open_compl_iff, ← with_scott_topology.closure_singleton],
      exact is_closed_closure, },
    have s2 : is_open (f⁻¹'  u) := is_open.preimage hf s1,
    rw with_scott_topology.is_open_eq_upper_and_lub_mem_implies_inter_nonempty at s2,
    cases s2,
    cases s2_right d a d₁ d₂ d₃ e1 with c,
    cases h_1,
    simp at h_1_right,
    rw upper_bounds at hb,
    simp at hb,
    have c1: f c ≤ b,
    { apply hb,
      exact h_1_left, },
    contradiction, }, }
end

end preorder

section partial_order
variables [partial_order α]

instance : partial_order (with_scott_topology α) := ‹partial_order α›

/--
The Scott topology on a partial order is T₀.
-/
@[priority 90] -- see Note [lower instance priority]
instance : t0_space (with_scott_topology α) :=
(t0_space_iff_inseparable (with_scott_topology α)).2 $ λ x y h, Iic_injective $
  by simpa only [inseparable_iff_closure_eq, with_scott_topology.closure_singleton] using h

end partial_order

section complete_lattice

lemma is_open_eq_upper_and_Sup_mem_implies_tail_subset [complete_lattice α]
(u : set (with_scott_topology α)) : is_open u =
(is_upper_set u ∧
  ∀ (d : set α), d.nonempty → directed_on (≤) d → Sup d ∈ u → ∃ b ∈ d, (Ici b) ∩ d ⊆ u) :=
begin
  rw with_scott_topology.is_open_eq_upper_and_lub_mem_implies_tail_subset,
  refine let_value_eq (and (is_upper_set u)) _,
  rw eq_iff_iff,
  split,
  { intros h d hd₁ hd₂ hd₃,
      exact h d (Sup d) hd₁ hd₂ (is_lub_Sup d) hd₃, },
  { intros h d a hd₁ hd₂ hd₃ ha,
      apply h d hd₁ hd₂,
      { rw (is_lub.Sup_eq hd₃), exact ha, } }
end

lemma is_open_eq_upper_and_Sup_mem_implies_inter_nonempty [complete_lattice α]
(u : set (with_scott_topology α)) : is_open u =
(is_upper_set u ∧  ∀ (d : set α), d.nonempty → directed_on (≤) d → Sup d ∈ u → (d∩u).nonempty) :=
begin
  rw with_scott_topology.is_open_eq_upper_and_lub_mem_implies_inter_nonempty,
  refine let_value_eq (and (is_upper_set u)) _,
  rw eq_iff_iff,
  split,
  { intros h d hd₁ hd₂ hd₃,
      exact h d (Sup d) hd₁ hd₂ (is_lub_Sup d) hd₃, },
  { intros h d a hd₁ hd₂ hd₃ ha,
      apply h d hd₁ hd₂,
      { rw (is_lub.Sup_eq hd₃), exact ha, } }
end

end complete_lattice
