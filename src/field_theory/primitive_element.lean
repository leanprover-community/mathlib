/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.adjoin
import field_theory.separable

/-!
# Primitive Element Theorem

In this file we prove the primitive element theorem.

## Main results

- `primitive_element`: a finite separable extension has a primitive element:
  there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`".

-/

noncomputable theory
open_locale classical

open finite_dimensional
open polynomial

namespace field

section primitive_element_finite
variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E]

/-! ### Primitive element theorem for finite fields -/

/-- Primitive element theorem assuming E is finite. -/
lemma primitive_element_of_fintype_top [fintype E] : ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  obtain ⟨α, hα⟩ := is_cyclic.exists_generator (units E),
  use α,
  apply eq_top_iff.mpr,
  rintros x -,
  by_cases hx : x = 0,
  { rw hx,
    exact F⟮α.val⟯.zero_mem },
  { obtain ⟨n, hn⟩ := set.mem_range.mp (hα (units.mk0 x hx)),
    rw (show x = α^n, by { norm_cast, rw [hn, units.coe_mk0] }),
    exact @is_subfield.pow_mem E _ α.val n F⟮α.val⟯ _ (field.mem_adjoin_simple_self F α.val) },
end

/-- Primitive element theorem for finite dimensional extension of a finite field. -/
theorem primitive_element_of_fintype_bot [fintype F] [finite_dimensional F E] :
  ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  haveI : fintype E := fintype_of_fintype F E,
  exact primitive_element_of_fintype_top F,
end

end primitive_element_finite

section primitive_element_theorem
variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

section primitive_element_inf_lemmas
open multiset
variables {E' : Type*} [field E'] (ϕ : F →+* E')

/-! ### Primitive element theorem for infinite fields -/

lemma primitive_element_two_inf_exists_c [infinite F] (α β : E') (f g : polynomial F) :
  ∃ c : F, ∀ (α' ∈ (f.map ϕ).roots) (β' ∈ (g.map ϕ).roots), -(α' - α)/(β' - β) ≠ ϕ c :=
begin
  let sf := (f.map ϕ).roots,
  let sg := (g.map ϕ).roots,
  let s := (sf.bind (λ α', sg.map (λ β', -(α' - α) / (β' - β)))).to_finset,
  let s' := s.preimage ϕ (λ x hx y hy h, ϕ.injective h),
  obtain ⟨c, hc⟩ := infinite.exists_not_mem_finset s',
  simp_rw [finset.mem_preimage, mem_to_finset, mem_bind, mem_map] at hc,
  push_neg at hc,
  exact ⟨c, hc⟩,
end

end primitive_element_inf_lemmas

-- This is the heart of the proof of the primitive element theorem. It shows that if `F` is
-- infinite and `α` and `β` are algebraic over `F` then `F⟮α, β⟯` is generated by a single element.
lemma primitive_element_two_inf [infinite F] (α β : E) (F_sep : is_separable F E) :
  ∃ γ : E, (F⟮α, β⟯ : set E) ⊆ (F⟮γ⟯ : set E) :=
begin
  obtain ⟨hα, hf⟩ := F_sep α,
  obtain ⟨hβ, hg⟩ := F_sep β,
  let f := minimal_polynomial hα,
  let g := minimal_polynomial hβ,
  let ιFE := algebra_map F E,
  let ιEE' := algebra_map E (polynomial.splitting_field (g.map ιFE)),
  let ιFE' := ιEE'.comp ιFE,
  obtain ⟨c, hc⟩ := primitive_element_two_inf_exists_c ιFE' (ιEE' α) (ιEE' β) f g,
  let γ := α + c • β,
  use γ,
  apply (field.adjoin_subset_iff F {α, β}).mp,
  suffices β_in_Fγ : β ∈ F⟮γ⟯,
  { have γ_in_Fγ : γ ∈ F⟮γ⟯ := field.mem_adjoin_simple_self F γ,
    have cβ_in_Fγ : c • β ∈ (F⟮γ⟯ : set E) := F⟮γ⟯.smul_mem β_in_Fγ c,
    have α_in_Fγ : α ∈ (F⟮γ⟯ : set E),
    { rw (show α = γ - c • β, by exact (add_sub_cancel α (c • β)).symm),
      exact is_add_subgroup.sub_mem F⟮γ⟯ γ (c • β) γ_in_Fγ cβ_in_Fγ },
    exact λ x hx, by cases hx; cases hx; cases hx; assumption },
  let p := euclidean_domain.gcd ((f.map (algebra_map F F⟮γ⟯)).comp
    (C (adjoin_simple.gen F γ) - (C ↑c * X))) (g.map (algebra_map F F⟮γ⟯)),
  let h := euclidean_domain.gcd ((f.map ιFE).comp (C γ - (C (ιFE c) * X))) (g.map ιFE),
  have g_ne_zero := minimal_polynomial.ne_zero hβ,
  have h_ne_zero : h ≠ 0 := by simp [euclidean_domain.gcd_eq_zero_iff, map_eq_zero, g_ne_zero],
  have h_leading_coeff_ne_zero : h.leading_coeff ≠ 0 := mt leading_coeff_eq_zero.mp h_ne_zero,
  suffices p_linear : p.map (algebra_map F⟮γ⟯ E) = (C h.leading_coeff) * (X - C β),
  { have finale : β = algebra_map F⟮γ⟯ E (-p.coeff 0 / p.coeff 1),
    { rw [ring_hom.map_div, ring_hom.map_neg, ←coeff_map, ←coeff_map, p_linear],
      simp [mul_sub, coeff_C, mul_comm _ β, mul_div_cancel β h_leading_coeff_ne_zero] },
    rw finale,
    exact subtype.mem (-p.coeff 0 / p.coeff 1) },
  have s1 : p.map (algebra_map F⟮γ⟯ E) = euclidean_domain.gcd (_ : polynomial E) (_ : polynomial E),
  { dsimp only [p],
    convert (gcd_map (algebra_map F⟮γ⟯ E)).symm },
  have s2 : p.map (algebra_map F⟮γ⟯ E) = h,
  { rw [s1, map_comp, map_map, map_map, ←is_scalar_tower.algebra_map_eq],
    simp [h],
    refl },
  rw s2,
  have h_sep : h.separable := separable_gcd_right _ (separable.map hg),
  have h_root : h.eval β = 0,
  { apply eval_gcd_eq_zero,
    { rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map, ←aeval_def,
          ←algebra.smul_def, add_sub_cancel, minimal_polynomial.aeval] },
    { rw [eval_map, ←aeval_def, minimal_polynomial.aeval] } },
  have h_splits : splits ιEE' h := splits_of_splits_gcd_right
    ιEE' (map_ne_zero g_ne_zero) (splitting_field.splits _),
  apply eq_X_sub_C_of_separable_of_root_eq ιEE' h_ne_zero h_sep h_root h_splits,
  intros x hx,
  rw mem_roots_map h_ne_zero at hx,
  specialize hc ((ιEE' γ) - (ιFE' c) * x) (begin
    have f_root := root_left_of_root_gcd hx,
    rw [eval₂_comp, eval₂_sub, eval₂_mul,eval₂_C, eval₂_C,eval₂_X, eval₂_map] at f_root,
    exact (mem_roots_map (minimal_polynomial.ne_zero hα)).mpr f_root,
  end),
  specialize hc x (begin
    rw [mem_roots_map (minimal_polynomial.ne_zero hβ), ←eval₂_map],
    exact root_right_of_root_gcd hx,
  end),
  by_contradiction a,
  apply hc,
  symmetry,
  apply (eq_div_iff (sub_ne_zero.mpr a)).mpr,
  simp only [algebra.smul_def, ring_hom.map_add, ring_hom.map_mul, ring_hom.comp_apply],
  ring,
end

section primitive_element_same_universe
universe u

/-- Primitive element theorem for infinite fields. -/
theorem primitive_element_inf {F E : Type u} [field F] [field E] [algebra F E]
  [finite_dimensional F E] (F_sep : is_separable F E) (F_inf : infinite F)
  (n : ℕ) (hn : findim F E = n) : ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  tactic.unfreeze_local_instances,
  revert F,
  apply nat.strong_induction_on n,
  clear n,
  rintros n ih F hF hFE F_findim F_sep F_inf rfl,
  by_cases key : ∃ α : E, findim F F⟮α⟯ > 1,
  { cases key with α hα,
    haveI Fα_findim : finite_dimensional F⟮α⟯ E := finite_dimensional.right F F⟮α⟯ E,
    have Fα_dim_lt_F_dim : findim F⟮α⟯ E < findim F E,
    { rw ← findim_mul_findim F F⟮α⟯ E,
      nlinarith [show 0 < findim F⟮α⟯ E, from findim_pos, show 0 < findim F F⟮α⟯, from findim_pos], },
    have Fα_inf : infinite F⟮α⟯ := infinite.of_injective _ (algebra_map F F⟮α⟯).injective,
    have Fα_sep : is_separable F⟮α⟯ E := is_separable_tower_top_of_is_separable_tower F F⟮α⟯ E F_sep,
    obtain ⟨β, hβ⟩ := ih _ Fα_dim_lt_F_dim Fα_sep Fα_inf rfl,
    obtain ⟨γ, hγ⟩ := primitive_element_two_inf α β F_sep,
    simp only [←adjoin_simple_adjoin_simple, subalgebra.ext_iff, algebra.mem_top, iff_true, *] at *,
    exact ⟨γ, λ x, hγ algebra.mem_top⟩, },
  { push_neg at key,
    rw ← bot_eq_top_of_findim_adjoin_le_one key,
    exact ⟨0, by rw adjoin_zero⟩, },
end

/-- Primitive element theorem in same universe. -/
theorem primitive_element_aux (F E : Type u) [field F] [field E] [algebra F E]
  [finite_dimensional F E] (F_sep : is_separable F E) : ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  by_cases F_finite : nonempty (fintype F),
  { exact nonempty.elim F_finite (λ h : fintype F, @primitive_element_of_fintype_bot F _ E _ _ h _), },
  { exact primitive_element_inf F_sep (not_nonempty_fintype.mp F_finite) (findim F E) rfl, },
end

end primitive_element_same_universe

/-- Complete primitive element theorem. -/
theorem primitive_element [finite_dimensional F E] (F_sep : is_separable F E) :
  ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  let F' := F⟮(0 : E)⟯,
  have F'_sep : is_separable F' E := is_separable_tower_top_of_is_separable_tower F F' E F_sep,
  haveI : finite_dimensional F' E := finite_dimensional.right F F' E,
  obtain ⟨α, hα⟩ := primitive_element_aux F' E F'_sep,
  have : (F'⟮α⟯ : set E) = F⟮α⟯,
  { rw [adjoin_simple_comm, adjoin_zero, adjoin_eq_range_algebra_map_adjoin],
    simp [set.ext_iff, algebra.mem_bot], },
  exact ⟨α, by simp [subalgebra.ext_iff, set.ext_iff, algebra.mem_top, *] at *⟩,
end

end primitive_element_theorem

end field
