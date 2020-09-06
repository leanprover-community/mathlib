/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import topology.basic
import order.omega_complete_partial_order

/-!
# Scott Topological Spaces

I don't know what they're good for but their notion
of continuity is equivalent to continuity in ωCPOs.

## Reference

 * https://ncatlab.org/nlab/show/Scott+topology

-/

open omega_complete_partial_order
open_locale classical

universes u
namespace scott_topological_space

/--  -/
def is_ωSup {α : Type u} [preorder α] (c : chain α) (x : α) : Prop :=
(∀ i, c i ≤ x) ∧ (∀ y, (∀ i, c i ≤ y) → x ≤ y)

variables (α : Type u) [omega_complete_partial_order α]

/-- The characteristic function of open sets is monotone and preserves
the limits of chains. -/
def is_open (s : set α) : Prop :=
continuous' (s : α → Prop)

theorem is_open_univ : is_open α set.univ :=
⟨λ x y h, le_refl _,
  show omega_complete_partial_order.continuous ⊤,
    from complete_lattice.top_continuous ⟩

theorem is_open_inter (s t : set α) : is_open α s → is_open α t → is_open α (s ∩ t) :=
begin
  simp only [is_open, exists_imp_distrib, continuous'],
  intros h₀ h₁ h₂ h₃,
  rw ← set.inf_eq_inter,
  let s' : α →ₘ Prop := ⟨s, h₀⟩,
  let t' : α →ₘ Prop := ⟨t, h₂⟩,
  split, change omega_complete_partial_order.continuous (s' ⊓ t'),
  haveI : is_total Prop (≤) := ⟨ @le_total Prop _ ⟩,
  apply complete_lattice.inf_continuous; assumption
end

theorem is_open_sUnion : ∀s, (∀t∈s, is_open α t) → is_open α (⋃₀ s) :=
begin
  introv h₀,
  suffices : is_open α (Sup s : α → Prop),
  { convert this, ext,
    simp only [set.sUnion, Sup, set_of, supr, conditionally_complete_lattice.Sup,
               complete_lattice.Sup, exists_prop, set.mem_range,
               set_coe.exists, eq_iff_iff, subtype.coe_mk],
    tauto, },
  apply complete_lattice.Sup_continuous' _ h₀,
end

end scott_topological_space

/-- A Scott topological space is defined on preorders
such that their open sets, seen as a function `α → Prop`,
preserves the joins of ω-chains  -/
@[reducible]
def Scott (α : Type u) := α

instance scott_topological_space (α : Type u) [omega_complete_partial_order α] : topological_space (Scott α) :=
{ is_open := scott_topological_space.is_open α,
  is_open_univ := scott_topological_space.is_open_univ α,
  is_open_inter := scott_topological_space.is_open_inter α,
  is_open_sUnion := scott_topological_space.is_open_sUnion α }

@[simp]
lemma set_of_apply {α} (p : α → Prop) (x : α) : set_of p x ↔ p x := iff.rfl

@[simp]
lemma le_iff_imp {p q : Prop} : p ≤ q ↔ (p → q) := by refl

section not_below
variables {α : Type*} [omega_complete_partial_order α] (y : Scott α)

/-- `not_below` is an open set in `Scott α` used
to prove the monotonicity of continuous functions -/
def not_below := { x | ¬ x ≤ y }

lemma not_below_is_open : is_open (not_below y) :=
begin
  have h : monotone (not_below y),
  { intros x y' h,
    simp only [not_below, set_of, le_iff_imp],
    intros h₀ h₁, apply h₀ (le_trans h h₁) },
  existsi h, rintros c,
  apply eq_of_forall_ge_iff, intro z,
  rw ωSup_le_iff,
  simp only [ωSup_le_iff, not_below, set_of_apply, le_iff_imp, preorder_hom.coe_fun_mk,
             chain.map_to_fun, function.comp_app, exists_imp_distrib, not_forall],
end

end not_below

open scott_topological_space (hiding is_open)
open omega_complete_partial_order

lemma is_ωSup_ωSup {α} [omega_complete_partial_order α] (c : chain α) :
  is_ωSup c (ωSup c) :=
begin
  split,
  { apply le_ωSup, },
  { apply ωSup_le, },
end

lemma Scott_continuous_of_continuous {α β}
  [omega_complete_partial_order α]
  [omega_complete_partial_order β]
  (f : Scott α → Scott β) (hf : continuous f) :
  omega_complete_partial_order.continuous' f :=
begin
  dsimp [_root_.continuous, (⁻¹')] at hf,
  have h : monotone f,
  { intros x y h,
    cases (hf {x | ¬ x ≤ f y} (not_below_is_open _)) with hf hf', clear hf',
    specialize hf h, simp only [set.preimage, set_of, (∈), set.mem, le_iff_imp] at hf,
    by_contradiction, apply hf a (le_refl (f y)) },
  existsi h, intro c,
  apply eq_of_forall_ge_iff, intro z,
  specialize (hf _ (not_below_is_open z)),
  cases hf, specialize hf_h c,
  simp only [not_below, preorder_hom.coe_fun_mk, eq_iff_iff, set.mem_set_of_eq, set_of_apply] at hf_h,
  rw [← not_iff_not],
  simp only [ωSup_le_iff, hf_h, ωSup, supr, Sup, complete_lattice.Sup, exists_prop, set.mem_range, preorder_hom.coe_fun_mk,
             chain.map_to_fun, function.comp_app, eq_iff_iff, set_of_apply, not_forall],
  tauto,
end

lemma continuous_of_Scott_continuous {α β}
  [omega_complete_partial_order α]
  [omega_complete_partial_order β]
  (f : Scott α → Scott β) (hf : omega_complete_partial_order.continuous' f) :
  continuous f :=
begin
  intros s hs,
  change continuous' (s ∘ f),
  cases hs with hs hs',
  cases hf with hf hf',
  apply continuous.of_bundled,
  apply continuous_comp _ _ hf' hs',
end
