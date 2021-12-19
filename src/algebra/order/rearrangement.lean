/-
Copyright (c) 2021 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.order.module
import group_theory.perm.sign
import order.monovary
import tactic.abel
import algebra.big_operators.basic

/-!
# Rearrangement inequality

This file proves the rearrangement inequality.

The rearrangement inequality tells you that for two functions `f g : ι → α`, the sum
`∑ i, f i * g (σ i)` is maximized over all `σ : perm ι` when `g ∘ σ` monovaries with `f` and
minimized when `g ∘ σ` antivaries with `f`.

The case for `monotone` pairs of functions over a `linear_order` is deduced.

Note : I'm currently very unsure if this theorem should have it's own file, please feel free to
comment on this
-/

variables {ι ι' α β γ : Type*}

section vary
variables [preorder α] [preorder β] {f : ι → α} {g : ι → β}

open equiv

end vary

open order_dual equiv
open_locale big_operators

namespace finset

lemma sum_comp_perm_smul_eq_smul_comp_inv_perm [fintype ι] [decidable_eq ι] [add_comm_monoid α]
  [decidable_eq β] [add_comm_monoid β] [has_scalar α β] {σ : perm ι} {s : finset ι} {f : ι → α}
  {g : ι → β} (hσ : σ.support ⊆ s) :
  ∑ i in s, f (σ i) • g i = ∑ i in s, f i • g (σ⁻¹ i) :=
begin
  sorry
end

end finset

open finset equiv equiv.perm order_dual
open_locale big_operators

/-- **Rearrangement Inequality** -/
theorem monovary_on.sum_smul_comp_perm_le_sum_smul [decidable_eq ι] [fintype ι]
  [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β] [ordered_smul α β]
  {s : finset ι} {f : ι → α} {g : ι → β} (hfg : monovary_on f g s) (σ : perm ι)
  (hσ : σ.support ⊆ s) :
  ∑ i in s, f i • g (σ i) ≤ ∑ i in s, f i • g i :=
begin
  revert hσ σ hfg,
  apply finset.induction_on_max_value₂ g f s,
  { simp only [le_refl, finset.sum_empty, implies_true_iff] },
  intros a s has hamax hind hfg σ hσ,
  set k := σ a with hk,
  set j := σ⁻¹ a with hj,
  set p : ι → ι := λ x, if x = a then a else if x = j then k else σ x with hp,
  set q : ι → ι := λ x, if x = a then a else if x = k then j else σ⁻¹ x with hq,
  have hqpleft : function.left_inverse q p,
  { intro x,
    simp only [hp, hq],
    split_ifs with h₁ h₂ h₃ h₄ h₅,
    { rw h₁ },
    { rw [h₂, hj, eq_inv_iff_eq, ← hk, h₃] },
    { rw h₂ },
    { exfalso,
      apply h₂,
      rw [hj, eq_inv_iff_eq, h₄] },
    { exfalso,
      apply h₁,
      simp only [←inv_eq_iff_eq, inv_apply_self] at h₅,
      exact h₅ },
    { simp only [inv_apply_self] } },
  set τ : perm ι :=
  begin
    use [p, q, hqpleft],
    apply fintype.left_inverse_of_right_inverse_of_card_le hqpleft (by simp only [le_of_eq])
  end with hτ,
  have hτs : τ.support ⊆ s,
  { intros x hx,
    simp only [coe_fn_mk, mem_support, hp] at hx,
    split_ifs at hx with h₁ h₂ h₃,
    { tauto },
    { rw h₂,
      rw h₂ at h₁,
      have hjs : σ j ≠ j, { simp only [ne.def, apply_inv_self]; tauto },
      rw ← mem_support at hjs,
      specialize hσ hjs,
      simp only [mem_insert] at hσ,
      cases hσ; tauto },
    { rw ←mem_support at hx,
      specialize hσ hx,
      rw mem_insert at hσ,
      cases hσ; tauto } },
  specialize hind (hfg.subset _ ) τ hτs,
  { simp only [coe_insert, set.subset_insert] },
  replace hind := add_le_add_left hind (f a • g a),
  rw ← sum_insert has at hind,
  apply le_trans _ hind,
  obtain hja | hja := eq_or_ne j a,
  { rw sum_insert has,
    simp only [←hja, coe_fn_mk, coe_fn_mk, add_le_add_iff_left, apply_inv_self],
    refine (sum_congr rfl $ λ x hx, _).le,
    congr,
    simp only [hp],
    rw [hja, if_neg (ne_of_mem_of_not_mem hx has), if_neg (ne_of_mem_of_not_mem hx has)] },
  have hjs : j ∈ s,
  { suffices : j ∈ σ.support,
    { specialize hσ this,
      rw mem_insert at hσ,
      cases hσ; tauto },
    rw mem_support,
    simp only [ne.def, apply_inv_self]; tauto },
  simp only [sum_insert has, ← s.sum_erase_add _ hjs, coe_fn_mk, add_comm],
  rw [← add_assoc, ← add_assoc],
  refine add_le_add _ (sum_congr rfl $ λ x hx, _).le,
  { have hpj : p j = k,
    { simp only [hp],
      rw [if_pos rfl, if_neg hja] },
    simp only [← hk, apply_inv_self, hpj],
    suffices : 0 ≤ (f a - f j) • (g a - g k),
    { rw ← sub_nonneg,
      convert this,
      simp only [smul_sub, sub_smul],
      abel },
    have hks : k ∈ s,
    { suffices : k ∈ σ.support,
      { specialize hσ this,
        rw mem_insert at hσ,
        cases hσ,
        { exfalso,
          simp only [← eq_inv_iff_eq] at hσ,
          rw ← hj at hσ,
          apply hja,
          rw hσ },
        { exact hσ } },
      simp only [mem_support, ne.def, ← eq_inv_iff_eq, inv_apply_self],
      intro hka,
      apply hja,
      rw [hka, hj] },
    apply smul_nonneg,
    { rw sub_nonneg,
      specialize hamax j hjs,
      cases hamax,
      { apply hfg _ _ hamax,
        { simp only [hjs, coe_insert, set.mem_insert_iff, mem_coe, or_true] },
        { simp only [coe_insert, set.mem_insert_iff, true_or, eq_self_iff_true] }},
      { exact hamax.2 } },
    { rw sub_nonneg,
      specialize hamax k hks,
      cases hamax,
      { exact hamax.le },
      { exact hamax.1.le } } },
  { congr,
    simp only [hp],
    rw [if_neg (ne_of_mem_of_not_mem (mem_of_mem_erase hx) has), if_neg (ne_of_mem_erase hx)] }
end

/-- **Rearrangement Inequality** -/
theorem monovary_on.sum_comp_perm_smul_le_sum_smul [decidable_eq ι] [fintype ι]
  [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β] [ordered_smul α β]
  {s : finset ι} {f : ι → α} {g : ι → β} (hfg : monovary_on f g s) (σ : perm ι)
  (hσ : σ.support ⊆ s) :
  ∑ i in s, f (σ i) • g i ≤ ∑ i in s, f i • g i :=
begin
  convert (monovary_on.sum_smul_comp_perm_le_sum_smul hfg σ⁻¹ (support_inv σ⁻¹ ▸ hσ)) using 1,
  exact sum_comp_perm_smul_eq_smul_comp_inv_perm hσ
end

/-- **Rearrangement Inequality** -/
theorem antivary_on.sum_smul_le_sum_smul_comp_perm [decidable_eq ι] [fintype ι]
  [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β] [ordered_smul α β]
  {s : finset ι} {f : ι → α} {g : ι → β} (hfg : antivary_on f g s) (σ : perm ι)
  (hσ : σ.support ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f i • g (σ i) :=
hfg.dual_right.sum_smul_comp_perm_le_sum_smul _ hσ

/-- **Rearrangement Inequality** -/
theorem antivary_on.sum_smul_le_sum_comp_perm_smul [decidable_eq ι] [fintype ι]
  [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β] [ordered_smul α β]
  {s : finset ι} {f : ι → α} {g : ι → β} (hfg : antivary_on f g s) (σ : perm ι)
  (hσ : σ.support ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f (σ i) • g i :=
begin
  convert (antivary_on.sum_smul_le_sum_smul_comp_perm hfg σ⁻¹ (support_inv σ⁻¹ ▸ hσ)) using 1,
  exact sum_comp_perm_smul_eq_smul_comp_inv_perm hσ
end

/-- **Rearrangement Inequality** : statement over a `finset` of a `linear order` -/
theorem sum_smul_comp_perm_le_sum_smul [linear_order ι] [linear_ordered_ring α]
  [linear_ordered_add_comm_group β] [module α β] [ordered_smul α β] {f : ι → α} {g : ι → β}
  (s : finset ι) (hf : monotone_on f s) (hg : monotone_on g s) (σ : perm ι)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g (σ i) ≤ ∑ i in s, f i • g i :=
begin
  set f' : s → α := λ n, f n with hf',
  set g' : s → β := λ n, g n with hg',
  have hf'm : monotone f',
  { intros a b hab,
    simp only [hf'],
    apply hf,
    { simp only [coe_mem, mem_coe] },
    { simp only [coe_mem, mem_coe] },
    { exact subtype.mono_coe (λ (x : ι), x ∈ s) hab} },
  have hg'm : monotone g',
  { intros a b hab,
    simp only [hg'],
    apply hg _ _ (subtype.mono_coe (λ (x : ι), x ∈ s) hab),
    { simp only [coe_mem, mem_coe] },
    { simp only [coe_mem, mem_coe] } },
  have hfg : monovary_on f' g' ↑univ,
  { convert (monovary_on.univ_iff_monovary).mpr (hf'm.monovary hg'm),
    exact coe_univ },
  have hσsupp: ∀ (y : ι), y ∈ {x | σ x ≠ x} ↔ σ y ∈ {x | σ x ≠ x},
  { intro y,
    simp only [ne.def, set.mem_set_of_eq, apply_eq_iff_eq] },
  have hσs : ∀ (x : ι), x ∈ s ↔ σ x ∈ s,
  { intro y,
    by_cases hy : y ∈ {x | σ x ≠ x},
    { refine ⟨λ hs, hσ _, λ hσx, hσ hy⟩,
      rw ← hσsupp,
      exact hy },
    { simp only [not_not, set.mem_set_of_eq] at hy,
      rw hy } },
  set τ : perm s := perm.subtype_perm σ hσs with hτs,
  convert (monovary_on.sum_smul_comp_perm_le_sum_smul hfg τ _) using 1,
  { rw @sum_subtype α ι _ (λ x, x ∈ s) _ s _,
    { congr },
    { simp only [iff_self, implies_true_iff] } },
  { rw @sum_subtype α ι _ (λ x, x ∈ s) _ s _,
    { congr },
    { simp only [iff_self, implies_true_iff] } }
  { },
end

lemma swap_extend_domain_eq_self [decidable_eq ι] (s : finset ι) (x y : s) :
  (@extend_domain s ι (swap x y) (λ x, x ∈ s) _ 1) = swap ↑x ↑y :=
begin
  ext a,
  by_cases ha : a ∈ s,
  { rw extend_domain_apply_subtype, swap, exact ha,
    simp only [coe_one, id.def, one_symm],
    obtain rfl | hax := eq_or_ne x ⟨a, ha⟩,
    { rw [swap_apply_left, swap, coe_fn_mk, swap_core, subtype.coe_mk],
      exact (if_pos rfl).symm },
    obtain rfl | hay := eq_or_ne y ⟨a, ha⟩,
    { rw [swap_apply_right, swap, coe_fn_mk, swap_core, subtype.coe_mk, if_pos rfl],
      exact (ite_eq_right_iff.2 id).symm },
    { rw swap_apply_of_ne_of_ne hax.symm hay.symm,
      exact (swap_apply_of_ne_of_ne (subtype.coe_injective.ne hax.symm) $
        subtype.coe_injective.ne hay.symm).symm } },
  { rw [extend_domain_apply_not_subtype, swap_apply_of_ne_of_ne
      (ne_of_mem_of_not_mem x.prop ha).symm (ne_of_mem_of_not_mem y.prop ha).symm],
    exact ha }
end

theorem equiv.perm.swap_induction_on'_support {ι : Type*} [decidable_eq ι] [fintype ι]
  (s : finset ι) {P : (perm ι) → Prop} (σ : perm ι) (hσ : σ.support ⊆ s ) :
  P 1 → (∀ (f : perm ι) x y, x ≠ y → x ∈ s → y ∈ s → (f.support ⊆ s → P f) →
    ((f * swap x y).support ⊆ s → P (f * swap x y))) → P σ :=
begin
  have hσ1 : ∀ x, x ∈ s ↔ σ x ∈ s,
  { intro x,
    by_cases hx : x ∈ σ.support,
    { exact ⟨λ hs, hσ $ perm.apply_mem_support.2 hx, λ hσx, hσ hx⟩ },
    { rw not_mem_support.1 hx } },
    set τ : perm s := perm.subtype_perm σ hσ1 with hτs,
    intros h1 hind,
    suffices : P (@extend_domain s ι τ (λ x, x ∈ s) _ 1),
    { convert this,
      ext x,
      by_cases hx : x ∈ s,
      { rw [hτs, extend_domain_apply_subtype],
        { simp only [subtype_perm_apply, coe_one, id.def, one_symm, subtype.coe_mk] },
        { exact hx } },
      { rw [hτs, not_mem_support.1 (λ h, hx $ hσ h), extend_domain_apply_not_subtype],
        exact hx } },
    suffices : (P ∘ λ (f : perm s), (@extend_domain s ι f (λ x, x ∈ s) _ 1)) τ, { exact this },
    apply swap_induction_on' τ,
    { simp only [extend_domain_one, function.comp_app, h1] },
    { intros π x y hxy hπ,
      specialize hind (@extend_domain s ι π (λ x, x ∈ s) _ 1) x y,
      suffices : P ((@extend_domain s ι π (λ x, x ∈ s) _ 1) * swap x y),
      { rw function.comp_apply,
        convert this,
        rw ← extend_domain_mul,
        congr,
        exact swap_extend_domain_eq_self s x y},
      apply hind,
      { simp only [ne.def, ← subtype.ext_iff, hxy, not_false_iff] },
      { exact coe_mem x },
      { exact coe_mem y },
      { intro,
        exact hπ },
      { apply subset.trans (support_mul_le _ _),
        apply union_subset,
        { intros z hz,
          rw mem_support at hz,
          by_cases hzs : z ∈ s, {exact hzs},
          exfalso,
          apply hz,
          rw extend_domain_apply_not_subtype,
          exact hzs },
        { intros z hz,
          replace hxy : (x : ι) ≠ y,
          { intro hyx,
            apply hxy,
            rw [subtype.ext_iff, hyx] },
          simp only [(support_swap hxy), mem_insert, mem_singleton] at hz,
          cases hz,
          { subst z,
            exact coe_mem x},
          { subst z,
            exact coe_mem y} } } }
end

lemma equiv.perm.mul_swap_support_subset {ι : Type*} [decidable_eq ι] [fintype ι] (s : finset ι)
  {x y : ι} (hx : x ∈ s) (hy : y ∈ s) (σ : perm ι) (hσ : (σ * swap x y).support ⊆ s) :
  σ.support ⊆ s :=
begin
  contrapose hσ,
  rw subset_iff at hσ,
  push_neg at hσ,
  cases hσ with z hz,
  rw subset_iff,
  push_neg,
  use z,
  refine ⟨_, hz.2⟩,
  rw mem_support,
  simp only [equiv.perm.coe_mul, function.comp_app],
  rw swap_apply_of_ne_of_ne,
  { simp only [← mem_support, hz.1] },
  { intro hxz,
    rw ← hxz at hx,
    apply hz.2 hx },
  { intro hyz,
    rw ← hyz at hy,
    apply hz.2 hy }
end
