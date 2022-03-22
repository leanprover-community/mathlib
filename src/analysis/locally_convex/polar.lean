/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Kalle Kytölä
-/

import analysis.normed.normed_field
import analysis.convex.basic

/-!
# Polar set

## Main definitions

* `polar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


variables {𝕜 E F : Type*}

namespace linear_map

section normed_ring

variables [normed_comm_ring 𝕜] [add_comm_monoid E] [add_comm_monoid F]
variables [module 𝕜 E] [module 𝕜 F]
variables (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

def polar (M : set E) : set F :=
  {y : F | ∀ (x ∈ M), ∥B x y∥ ≤ 1 }

lemma polar_mem_iff (s : set E) (y : F) :
  y ∈ B.polar s ↔ ∀ x ∈ s, ∥B x y∥ ≤ 1 := iff.rfl

lemma polar_mem (s : set E) (y : F) (hy : y ∈ B.polar s) :
  ∀ x ∈ s, ∥B x y∥ ≤ 1 := hy

@[simp] lemma zero_mem_polar (s : set E) :
  (0 : F) ∈ B.polar s :=
λ _ _, by simp only [map_zero, norm_zero, zero_le_one]

lemma polar_eq_Inter {s : set E} :
  B.polar s = ⋂ x ∈ s, {y : F | ∥B x y∥ ≤ 1} :=
by { ext, simp only [polar_mem_iff, set.mem_Inter, set.mem_set_of_eq] }

/-- The map `B.polar : set E → set F` forms an order-reversing Galois connection with
`B.flip.polar : set F → set E`. We use `order_dual.to_dual` and `order_dual.of_dual` to express
that `polar` is order-reversing. -/
lemma polar_gc : galois_connection (order_dual.to_dual ∘ B.polar)
  (B.flip.polar ∘ order_dual.of_dual) :=
λ s t, ⟨λ h _ hx _ hy, h hy _ hx, λ h _ hx _ hy, h hy _ hx⟩

@[simp] lemma polar_Union {ι} {s : ι → set E} : B.polar (⋃ i, s i) = ⋂ i, B.polar (s i) :=
B.polar_gc.l_supr

@[simp] lemma polar_union {s t : set E} : B.polar (s ∪ t) = B.polar s ∩ B.polar t :=
B.polar_gc.l_sup

lemma polar_antitone : antitone (B.polar : set E → set F) := B.polar_gc.monotone_l

@[simp] lemma polar_empty : B.polar ∅ = set.univ := B.polar_gc.l_bot

@[simp] lemma polar_zero : B.polar ({0} : set E) = set.univ :=
begin
  refine set.eq_univ_iff_forall.mpr (λ y x hx, _),
  rw [set.mem_singleton_iff.mp hx, map_zero, linear_map.zero_apply, norm_zero],
  exact zero_le_one,
end

lemma subset_bipolar (s : set E) : s ⊆ B.flip.polar (B.polar s) :=
λ x hx y hy, by { rw B.flip_apply, exact hy x hx }

@[simp] lemma tripolar_eq_polar (s : set E) : B.polar (B.flip.polar (B.polar s)) = B.polar s :=
begin
  refine (B.polar_antitone (B.subset_bipolar s)).antisymm _,
  convert subset_bipolar B.flip (B.polar s),
  exact B.flip_flip.symm,
end

end normed_ring

section nondiscrete_normed_field

variables [nondiscrete_normed_field 𝕜] [add_comm_monoid E] [add_comm_monoid F]
variables [module 𝕜 E] [module 𝕜 F]
variables (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

def separating_right (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Prop :=
∀ y : F, (∀ x : E, B x y = 0) → y = 0

lemma polar_univ (h : separating_right B) :
  B.polar set.univ = {(0 : F)} :=
begin
  rw set.eq_singleton_iff_unique_mem,
  refine ⟨by simp only [zero_mem_polar], λ y hy, h _ (λ x, _)⟩,
  refine norm_le_zero_iff.mp (le_of_forall_le_of_dense $ λ ε hε, _),
  rcases normed_field.exists_norm_lt 𝕜 hε with ⟨c, hc, hcε⟩,
  calc ∥B x y∥ = ∥c∥ * ∥B (c⁻¹ • x) y∥ :
    by rw [B.map_smul, linear_map.smul_apply, algebra.id.smul_eq_mul, norm_mul, norm_inv,
      mul_inv_cancel_left₀ hc.ne']
  ... ≤ ε * 1 : mul_le_mul hcε.le (hy _ trivial) (norm_nonneg _) hε.le
  ... = ε : mul_one _
end

end nondiscrete_normed_field

end linear_map
