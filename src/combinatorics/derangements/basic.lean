/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import dynamics.fixed_points.basic
import group_theory.perm.option

/-!
# Derangements on types

In this file we define `derangements α`, the set of derangements on a type `α`.

We also define:

* some related predicates: e.g.,

  - `only_possible_fixed_point f a`: either `f` has no fixed points, or `a` is the only fixed point;

  - `exactly_one_fixed_point f a`: `f` has exactly one fixed point, which is `a`;

* equivalences involving various subtypes of `perm α` and `derangements α`: e.g.,

  - `derangements_equiv_sigma_opfp`: an equivalence between `derangements (option α)` and the
    sigma-type `Σ a : α, {f : perm α // only_possible_fixed_point f a}`.
-/

lemma function.mem_fixed_points_iff {α : Type*} {f : α → α} {x : α} :
  x ∈ function.fixed_points f ↔ f x = x :=
by refl

lemma function.mem_fixed_points_apply {α : Type*} (f : α → α) {x : α}
  (hx : x ∈ function.fixed_points f) :
  f x ∈ function.fixed_points f :=
by convert hx

@[simp] lemma function.injective.mem_fixed_points_apply_iff {α : Type*} {f : α → α}
  (hf : function.injective f) {x : α} :
  f x ∈ function.fixed_points f ↔ x ∈ function.fixed_points f :=
⟨λ h, hf h, function.mem_fixed_points_apply f⟩

open equiv function

/- Same as `(equiv.refl _)^.set.compl .symm.trans (subtype_equiv_right $ by simp)` but with better
unfolding -/
/-- Permutations on `sᶜ` are equivalent to permutations that fix `s` pointwise. -/
protected def perm.compl_equiv {α : Type*} (s : set α) [decidable_pred (∈ s)] :
  perm (sᶜ : set α) ≃ {f : perm α // ∀ a ∈ s, f a = a} :=
{ to_fun := λ f, ⟨f.of_subtype, λ a ha, f.of_subtype_apply_of_not_mem (λ h, h ha)⟩,
  inv_fun := λ ⟨f, hf⟩, (f : perm α).subtype_perm
    (λ a, ⟨λ ha hfa, ha (f.injective (hf _ hfa) ▸ hfa),  λ hfa ha, (hf a ha ▸ hfa) ha⟩),
  left_inv := equiv.perm.subtype_perm_of_subtype,
  right_inv := begin
    rintro ⟨f, hf⟩,
    exact subtype.ext (equiv.perm.of_subtype_subtype_perm _ $ λ a hfa ha, hfa $ hf _ ha),
  end }

/-- Permutations on a subtype are equivalent to permutations on the original type that fix pointwise
the rest. -/
protected def perm.subtype_equiv {α : Type*} (p : α → Prop) [decidable_pred p] :
  perm (subtype p) ≃ {f : perm α // ∀ a, ¬p a → f a = a} :=
{ to_fun := λ f, ⟨f.of_subtype, λ a, f.of_subtype_apply_of_not_mem⟩,
  inv_fun := λ ⟨f, hf⟩, (f : perm α).subtype_perm
    (λ a, ⟨decidable.not_imp_not.1 $ λ hfa, (f.injective (hf _ hfa) ▸ hfa),
    decidable.not_imp_not.1 $ λ ha hfa, ha (hf a ha ▸ hfa)⟩),
  left_inv := equiv.perm.subtype_perm_of_subtype,
  right_inv := begin
    rintro ⟨f, hf⟩,
    exact subtype.ext (equiv.perm.of_subtype_subtype_perm _ $ λ a, not.decidable_imp_symm $ hf a),
  end }

/-- A permutation is a derangement if it has no fixed points. -/
def derangements (α : Type*) : set (perm α) := {f : perm α | ∀ x : α, f x ≠ x}

variables {α β : Type*}

lemma mem_derangements_iff_fixed_points_eq_empty {f : perm α} :
  f ∈ derangements α ↔ fixed_points f = ∅ :=
set.eq_empty_iff_forall_not_mem.symm

/-- If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangements β`. -/
def equiv.derangements_congr (e : α ≃ β) : (derangements α ≃ derangements β) :=
e.perm_congr.subtype_equiv $ λ f, e.forall_congr $ λ x, by simp

namespace derangements

/-- Derangements on a subtype are equivalent to permutations on the original type whose set of fixed
points is the rest. -/
protected def subtype_equiv  (p : α → Prop) [decidable_pred p] :
  derangements (subtype p) ≃ {f : perm α // ∀ a, ¬p a ↔ a ∈ fixed_points f} :=
calc
  derangements (subtype p)
      ≃ {f : {f : perm α // ∀ a, ¬p a → a ∈ fixed_points f} // ∀ a, a ∈ fixed_points f → ¬p a}
      : begin
        refine (perm.subtype_equiv p).subtype_equiv (λ f, ⟨λ hf a hfa ha, _, _⟩),
        { refine hf ⟨a, ha⟩ (subtype.ext _),
          rw [mem_fixed_points, is_fixed_pt, perm.subtype_equiv] at hfa,
          dsimp at hfa,
          rwa equiv.perm.of_subtype_apply_of_mem at hfa },
        rintro hf ⟨a, ha⟩ hfa,
        refine hf _ _ ha,
        rw [mem_fixed_points, is_fixed_pt, perm.subtype_equiv],
        dsimp,
        rw [equiv.perm.of_subtype_apply_of_mem _, hfa, subtype.coe_mk],
      end
  ... ≃ {f : perm α // ∃ (h : ∀ a, ¬p a → a ∈ fixed_points f), ∀ a, a ∈ fixed_points f → ¬p a}
      : subtype_subtype_equiv_subtype_exists _ _
  ... ≃ {f : perm α // ∀ a, ¬p a ↔ a ∈ fixed_points f}
      : subtype_equiv_right (λ f, by simp_rw [exists_prop, ←forall_and_distrib,
        ←iff_iff_implies_and_implies])

/-- The set of permutations that fix at most `a` is equivalent to the sum of:
    - derangements on `α`
    - derangements on `α` minus `a`. -/
def at_most_one_fixed_point_equiv_sum_derangements [decidable_eq α] (a : α) :
  {f : perm α // fixed_points f ⊆ {a}} ≃ (derangements ({a}ᶜ : set α)) ⊕ derangements α :=
calc
  {f : perm α // fixed_points f ⊆ {a}}
      ≃ {f : {f : perm α // fixed_points f ⊆ {a}} // a ∈ fixed_points f}
        ⊕ {f : {f : perm α // fixed_points f ⊆ {a}} // a ∉ fixed_points f}
      : (equiv.sum_compl _).symm
  ... ≃ {f : perm α // fixed_points f ⊆ {a} ∧ a ∈ fixed_points f}
        ⊕ {f : perm α // fixed_points f ⊆ {a} ∧ a ∉ fixed_points f}
      : begin
        refine equiv.sum_congr _ _;
        { convert subtype_subtype_equiv_subtype_inter _ _, ext f, refl }
      end
  ... ≃ {f : perm α // fixed_points f = {a}} ⊕ {f : perm α // fixed_points f = ∅}
      : begin
        refine equiv.sum_congr (subtype_equiv_right $ λ f, _) (subtype_equiv_right $ λ f, _),
        { rw [set.eq_singleton_iff_unique_mem, and_comm],
          refl },
        { rw set.eq_empty_iff_forall_not_mem,
          refine ⟨λ h x hx, h.2 (h.1 hx ▸ hx), λ h, ⟨λ x hx, (h _ hx).elim, h _⟩⟩ }
      end
  ... ≃ (derangements _) ⊕ derangements α
      : begin
        refine equiv.sum_congr ((derangements.subtype_equiv _).trans $ subtype_equiv_right $ λ x,
          _).symm (subtype_equiv_right $ λ f, mem_derangements_iff_fixed_points_eq_empty.symm),
        rw [eq_comm, set.ext_iff],
        simp_rw [set.mem_compl_iff, not_not],
      end

section option
variables [decidable_eq α]

/-- The set of permutations `f` such that the preimage of `(a, f)` under
    `equiv.perm.decompose_option` is a derangement. -/
def remove_none.fiber (a : option α) : set (perm α) :=
  {f : perm α | (a, f) ∈ equiv.perm.decompose_option '' derangements (option α)}

lemma remove_none.mem_fiber (a : option α) (f : perm α) :
  f ∈ remove_none.fiber a ↔
  ∃ F : perm (option α), F ∈ derangements (option α) ∧ F none = a ∧ remove_none F = f :=
by simp [remove_none.fiber, derangements]

lemma remove_none.fiber_none_eq_empty : remove_none.fiber (@none α) = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros f hyp,
  rw remove_none.mem_fiber at hyp,
  rcases hyp with ⟨F, F_derangement, F_none, _⟩,
  exact F_derangement none F_none
end

/-- For any `a : α`, the fiber over `some a` is the set of permutations
    where `a` is the only possible fixed point. -/
lemma remove_none.fiber_eq_opfp (a : α) :
  (remove_none.fiber (some a)) = {f : perm α | fixed_points f ⊆ {a}} :=
begin
  ext f,
  split,
  { rw remove_none.mem_fiber,
    rintro ⟨F, F_derangement, F_none, rfl⟩ x x_fixed,
    rw mem_fixed_points_iff at x_fixed,
    apply_fun some at x_fixed,
    cases Fx : F (some x) with y,
    { rwa [remove_none_none F Fx, F_none, option.some_inj, eq_comm] at x_fixed },
    { exfalso, rw remove_none_some F ⟨y, Fx⟩ at x_fixed, exact F_derangement _ x_fixed } },
  { intro h_opfp,
    use equiv.perm.decompose_option.symm (some a, f),
    split,
    { simp only [equiv.perm.decompose_option_symm_apply],
      intro x,
      apply_fun (swap none (some a)),
      simp only [equiv.swap_apply_self, equiv.perm.coe_mul],
      cases x,
      { simp },
      { simp only [equiv_functor.map_equiv_apply, equiv_functor.map,
                    option.map_eq_map, option.map_some'],
        by_cases x_vs_a : x = a,
        { rw [x_vs_a, swap_apply_right], apply option.some_ne_none },
        { have ne_1 : some x ≠ none := option.some_ne_none _,
          have ne_2 : some x ≠ some a := (option.some_injective α).ne_iff.mpr x_vs_a,
          rw swap_apply_of_ne_of_ne ne_1 ne_2,
          rw (option.some_injective α).ne_iff,
          intro contra,
          exact x_vs_a (h_opfp contra) } } },
    { rw apply_symm_apply } }
end

/-- The set of derangements on `option α` is equivalent to the union over `a : α`
    of "permutations with `a` the only possible fixed point". -/
def derangements_equiv_sigma_opfp :
  derangements (option α) ≃ Σ a : α, {f : perm α | fixed_points f ⊆ {a}} :=
begin
  have fiber_none_is_false : (remove_none.fiber (@none α)) -> false,
  { rw remove_none.fiber_none_eq_empty, exact is_empty.false },

  calc derangements (option α)
      ≃ equiv.perm.decompose_option '' derangements (option α)   : equiv.image _ _
  ... ≃ Σ (a : option α), ↥(remove_none.fiber a)                 : set_prod_equiv_sigma _
  ... ≃ Σ (a : α), ↥(remove_none.fiber (some a))
          : sigma_option_equiv_of_some _ fiber_none_is_false
  ... ≃ Σ (a : α), {f : perm α | fixed_points f ⊆ {a}}
          : by simp_rw remove_none.fiber_eq_opfp,
end

/-- The set of derangements on `option α` is equivalent to the union over all `a : α` of
    "derangements on `α` ⊕ derangements on `{a}ᶜ`". -/
def derangements_recursion_equiv :
  derangements (option α) ≃ Σ a : α, (derangements (({a}ᶜ : set α) : Type _) ⊕ derangements α) :=
derangements_equiv_sigma_opfp.trans (sigma_congr_right
  at_most_one_fixed_point_equiv_sum_derangements)

end option

end derangements
