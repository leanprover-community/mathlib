/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.algebra.module.strong_topology
import topology.algebra.module.locally_convex

/-!
# Local convexity of the strong topology

In this file we prove that the strong topology on `E →L[ℝ] F` is locally convex provided that `F` is
locally convex.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Todo

* Characterization in terms of seminorms

## Tags

locally convex, bounded convergence
-/

open_locale topology uniform_convergence

variables {𝕜₁ 𝕜₂ E F : Type*}

namespace continuous_linear_map

variables [add_comm_group E] [topological_space E]
  [add_comm_group F] [topological_space F] [topological_add_group F]

section general

variables [normed_field 𝕜₁] [normed_field 𝕜₂] [module 𝕜₁ E] [module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂}
variables [module ℝ F] [has_continuous_const_smul ℝ F] [locally_convex_space ℝ F]
  [smul_comm_class 𝕜₂ ℝ F]

lemma strong_topology.locally_convex_space (𝔖 : set (set E)) (h𝔖₁ : 𝔖.nonempty)
  (h𝔖₂ : directed_on (⊆) 𝔖) :
  @locally_convex_space ℝ (E →SL[σ] F) _ _ _ (strong_topology σ F 𝔖) :=
begin
  letI : topological_space (E →SL[σ] F) := strong_topology σ F 𝔖,
  haveI : topological_add_group (E →SL[σ] F) := strong_topology.topological_add_group _ _ _,
  refine locally_convex_space.of_basis_zero _ _ _ _
    (strong_topology.has_basis_nhds_zero_of_basis _ _ _ h𝔖₁ h𝔖₂
      (locally_convex_space.convex_basis_zero ℝ F)) _,
  rintros ⟨S, V⟩ ⟨hS, hVmem, hVconvex⟩ f hf g hg a b ha hb hab x hx,
  exact hVconvex (hf x hx) (hg x hx) ha hb hab,
end

end general

section bounded_sets

variables [normed_field 𝕜₁] [normed_field 𝕜₂] [module 𝕜₁ E] [module 𝕜₂ F] {σ : 𝕜₁ →+* 𝕜₂}
variables [module ℝ F] [has_continuous_const_smul ℝ F] [locally_convex_space ℝ F]
  [smul_comm_class 𝕜₂ ℝ F]

instance : locally_convex_space ℝ (E →SL[σ] F) :=
strong_topology.locally_convex_space _ ⟨∅, bornology.is_vonN_bounded_empty 𝕜₁ E⟩
  (directed_on_of_sup_mem $ λ _ _, bornology.is_vonN_bounded.union)

end bounded_sets

end continuous_linear_map
