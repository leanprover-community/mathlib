/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Anne Baanen
-/
import linear_algebra.basis
import ring_theory.localization.fraction_ring
import ring_theory.localization.integer

/-!
# Modules / vector spaces over localizations / fraction fields

This file contains some results about vector spaces over the field of fractions of a ring.

## Main results

 * `linear_independent.localization`: `b` is linear independent over a localization of `R`
   if it is linear independent over `R` itself
 * `basis.localization`: promote an `R`-basis `b` to an `Rₛ`-basis,
   where `Rₛ` is a localization of `R`
 * `linear_independent.iff_fraction_ring`: `b` is linear independent over `R` iff it is
   linear independent over `Frac(R)`
-/

open_locale big_operators
open_locale non_zero_divisors

section localization

variables {R : Type*} (Rₛ : Type*) [comm_ring R] [comm_ring Rₛ] [algebra R Rₛ]
variables (S : submonoid R) [hT : is_localization S Rₛ]

include hT

section add_comm_monoid
variables {M : Type*} [add_comm_monoid M] [module R M] [module Rₛ M] [is_scalar_tower R Rₛ M]

lemma linear_independent.localization {ι : Type*} {b : ι → M} (hli : linear_independent R b) :
  linear_independent Rₛ b :=
begin
  rw linear_independent_iff' at ⊢ hli,
  intros s g hg i hi,
  choose a g' hg' using is_localization.exist_integer_multiples S s g,
  letI := λ i, classical.prop_decidable (i ∈ s),
  specialize hli s (λ i, if hi : i ∈ s then g' i hi else 0) _ i hi,
  { rw [← @smul_zero _ M _ _ (a : R), ← hg, finset.smul_sum],
    refine finset.sum_congr rfl (λ i hi, _),
    dsimp only,
    rw [dif_pos hi, ← is_scalar_tower.algebra_map_smul Rₛ, hg' i hi, smul_assoc],
    apply_instance },
  refine ((is_localization.map_units Rₛ a).mul_right_eq_zero).mp _,
  rw [← algebra.smul_def, ← map_zero (algebra_map R Rₛ), ← hli],
  simp [hi, hg']
end
end add_comm_monoid

section add_comm_group
variables {M : Type*} [add_comm_group M] [module R M] [module Rₛ M] [is_scalar_tower R Rₛ M]

/-- Promote a basis for `M` over `R` to a basis for `M` over the localization `Rₛ`.

See `basis.localization_localization` for a similar result localizing both `R` and `A`,
an `R`-algebra.
-/
noncomputable def basis.localization {ι : Type*} (b : basis ι R M) : basis ι Rₛ M :=
basis.mk (b.linear_independent.localization Rₛ S) $
by { rw [← eq_top_iff, ← @submodule.restrict_scalars_eq_top_iff Rₛ R, eq_top_iff, ← b.span_eq],
     apply submodule.span_le_restrict_scalars }

end add_comm_group

section localization_localization

variables {A : Type*} [comm_ring A] [algebra R A]
variables (Aₛ : Type*) [comm_ring Aₛ] [algebra A Aₛ]
variables [algebra Rₛ Aₛ] [algebra R Aₛ] [is_scalar_tower R Rₛ Aₛ] [is_scalar_tower R A Aₛ]
variables [hA : is_localization (algebra.algebra_map_submonoid A S) Aₛ]
include hA

open submodule

lemma linear_independent.localization_localization {ι : Type*}
  {v : ι → A} (hv : linear_independent R v) (hS : algebra.algebra_map_submonoid A S ≤ A⁰) :
  linear_independent Rₛ (algebra_map A Aₛ ∘ v) :=
begin
  refine (hv.map' ((algebra.linear_map A Aₛ).restrict_scalars R) _).localization Rₛ S,
  rw [linear_map.ker_restrict_scalars, restrict_scalars_eq_bot_iff, linear_map.ker_eq_bot,
      algebra.coe_linear_map],
  exact is_localization.injective Aₛ hS
end

lemma span_eq_top.localization_localization {v : set A} (hv : span R v = ⊤) :
  span Rₛ (algebra_map A Aₛ '' v) = ⊤ :=
begin
  rw eq_top_iff,
  rintros a' -,
  obtain ⟨a, ⟨_, s, hs, rfl⟩, rfl⟩ := is_localization.mk'_surjective
    (algebra.algebra_map_submonoid A S) a',
  rw [is_localization.mk'_eq_mul_mk'_one, mul_comm, ← map_one (algebra_map R A)],
  erw ← is_localization.algebra_map_mk' S A Rₛ Aₛ 1 ⟨s, hs⟩, -- `erw` needed to unify `⟨s, hs⟩`
  rw ← algebra.smul_def,
  refine smul_mem _ _ (span_subset_span R _ _ _),
  rw [← algebra.coe_linear_map, ← linear_map.coe_restrict_scalars R, ← linear_map.map_span],
  exact mem_map_of_mem (hv.symm ▸ mem_top),
  { apply_instance }
end

/-- If `A` has an `R`-basis, then localizing `A` at `S` has a basis over `R` localized at `S`.

A suitable instance for `[algebra A Aₛ]` is `localization_algebra`.
-/
noncomputable def basis.localization_localization {ι : Type*} (b : basis ι R A)
  (hS : algebra.algebra_map_submonoid A S ≤ A⁰) :
  basis ι Rₛ Aₛ :=
basis.mk
  (b.linear_independent.localization_localization _ S _ hS)
  (by { rw [set.range_comp, span_eq_top.localization_localization Rₛ S Aₛ b.span_eq],
        exact le_rfl })

@[simp] lemma basis.localization_localization_apply {ι : Type*} (b : basis ι R A)
  (hS : algebra.algebra_map_submonoid A S ≤ A⁰) (i) :
  b.localization_localization Rₛ S Aₛ hS i = algebra_map A Aₛ (b i) :=
basis.mk_apply _ _ _

@[simp] lemma basis.localization_localization_repr_algebra_map {ι : Type*} (b : basis ι R A)
  (hS : algebra.algebra_map_submonoid A S ≤ A⁰) (x i) :
  (b.localization_localization Rₛ S Aₛ hS).repr (algebra_map A Aₛ x) i =
    algebra_map R Rₛ (b.repr x i) :=
calc (b.localization_localization Rₛ S Aₛ hS).repr (algebra_map A Aₛ x) i
    = (b.localization_localization Rₛ S Aₛ hS).repr
        ((b.repr x).sum (λ j c, algebra_map R Rₛ c • algebra_map A Aₛ (b j))) i :
  by simp_rw [is_scalar_tower.algebra_map_smul, algebra.smul_def,
              is_scalar_tower.algebra_map_apply R A Aₛ, ← _root_.map_mul, ← map_finsupp_sum,
              ← algebra.smul_def, ← finsupp.total_apply, basis.total_repr]
... = (b.repr x).sum (λ j c, algebra_map R Rₛ c • finsupp.single j 1 i) :
  by simp_rw [← b.localization_localization_apply Rₛ S Aₛ hS, map_finsupp_sum,
              linear_equiv.map_smul, basis.repr_self, finsupp.sum_apply, finsupp.smul_apply]
... = _ : finset.sum_eq_single i
            (λ j _ hj, by simp [hj])
            (λ hi, by simp [finsupp.not_mem_support_iff.mp hi])
... = algebra_map R Rₛ (b.repr x i) : by simp [algebra.smul_def]

end localization_localization

end localization

section fraction_ring

variables (R K : Type*) [comm_ring R] [field K] [algebra R K] [is_fraction_ring R K]
variables {V : Type*} [add_comm_group V] [module R V] [module K V] [is_scalar_tower R K V]

lemma linear_independent.iff_fraction_ring {ι : Type*} {b : ι → V} :
  linear_independent R b ↔ linear_independent K b :=
⟨linear_independent.localization K (R⁰),
 linear_independent.restrict_scalars (smul_left_injective R one_ne_zero)⟩

end fraction_ring
