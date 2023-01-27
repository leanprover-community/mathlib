/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.dedekind_domain.dvr
import ring_theory.dedekind_domain.ideal

/-!
# Proving a Dedekind domain is a PID

This file contains some results that we can use to show all ideals in a Dedekind domain are
principal.

## Main results

 * `is_principal_ideal_ring.of_finite_primes`: if a Dedekind domain has finitely many prime ideals,
   it is a principal ideal domain.
-/

variables {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R]

open ideal
open unique_factorization_monoid
open_locale big_operators
open_locale non_zero_divisors

open unique_factorization_monoid

/-- Let `P` be a prime ideal, `x ∈ P \ P²` and `x ∉ Q` for all prime ideals `Q ≠ P`.
Then `P` is generated by `x`. -/
lemma ideal.eq_span_singleton_of_mem_of_not_mem_sq_of_not_mem_prime_ne
  {P : ideal R} (hP : P.is_prime)
  {x : R} (x_mem : x ∈ P) (hxP2 : x ∉ P^2)
  (hxQ : ∀ (Q : ideal R), is_prime Q → Q ≠ P → x ∉ Q) :
  P = ideal.span {x} :=
begin
  letI := classical.dec_eq (ideal R),
  have hx0 : x ≠ 0,
  { rintro rfl,
    exact hxP2 (zero_mem _) },
  by_cases hP0 : P = ⊥,
  { unfreezingI { subst hP0 },
    simpa using hxP2 },
  have hspan0 : span ({x} : set R) ≠ ⊥,
  { refine mt ideal.span_eq_bot.mp _,
    simpa only [not_forall, set.mem_singleton_iff, exists_prop, exists_eq_left] using hx0 },
  have span_le := (ideal.span_singleton_le_iff_mem _).mpr x_mem,
  refine associated_iff_eq.mp
    ((associated_iff_normalized_factors_eq_normalized_factors hP0 hspan0).mpr
      (le_antisymm ((dvd_iff_normalized_factors_le_normalized_factors hP0 hspan0).mp _) _)),
  { rwa [ideal.dvd_iff_le, ideal.span_singleton_le_iff_mem] },
  simp only [normalized_factors_irreducible ((ideal.prime_of_is_prime hP0 hP).irreducible),
      normalize_eq, multiset.le_iff_count, multiset.count_singleton],
  intros Q,
  split_ifs with hQ,
  { unfreezingI { subst hQ },
    refine (ideal.count_normalized_factors_eq _ _).le;
      simp only [ideal.span_singleton_le_iff_mem, pow_one];
      assumption },
  by_cases hQp : is_prime Q,
  { resetI,
    refine (ideal.count_normalized_factors_eq _ _).le;
      simp only [ideal.span_singleton_le_iff_mem, pow_one, pow_zero, one_eq_top, submodule.mem_top],
    exact hxQ _ hQp hQ },
  { exact (multiset.count_eq_zero.mpr (λ hQi, hQp (is_prime_of_prime (irreducible_iff_prime.mp
      (irreducible_of_normalized_factor _ hQi))))).le }
end

/-- A Dedekind domain is a PID if its set of primes is finite. -/
theorem is_principal_ideal_ring.of_finite_primes
  (h : set.finite {I : ideal R | is_prime I}) :
  is_principal_ideal_ring R :=
begin
  letI := classical.dec_eq (ideal R),
  refine is_principal_ideal_ring.of_prime (λ P hP, _),
  by_cases hP0 : P = ⊥,
  { subst hP0,
    exact ⟨⟨0, ideal.span_zero.symm⟩⟩ },
  obtain ⟨p, hp_mem, hp_nmem⟩ := ideal.exists_mem_pow_not_mem_pow_succ P hP0 hP.ne_top 1,
  let primes := h.to_finset.filter (λ Q, Q ≠ ⊥),
  have mem_primes : ∀ {Q : ideal R}, Q ∈ primes ↔ Q.is_prime ∧ Q ≠ ⊥ :=
    λ Q, finset.mem_filter.trans (and_congr_left (λ _, h.mem_to_finset)),
  obtain ⟨y, hy⟩ := is_dedekind_domain.exists_forall_sub_mem_ideal
    (λ Q, Q)
    (λ Q, if Q = P then 2 else 1)
    (λ Q (hQ : Q ∈ primes), ideal.prime_of_is_prime (mem_primes.mp hQ).2 (mem_primes.mp hQ).1)
    _
    (λ Q, if ↑Q = P then p else 1),
  have y_nmem : y ∉ P^2,
  { specialize hy P (mem_primes.mpr ⟨hP, hP0⟩),
    dsimp at hy,
    rw [if_pos rfl, if_pos rfl, sub_eq_add_neg] at hy,
    exact λ hy', hp_nmem (neg_mem_iff.mp ((add_mem_cancel_left hy').mp hy)) },
  refine ⟨⟨y, ideal.eq_span_singleton_of_mem_of_not_mem_sq_of_not_mem_prime_ne hP _ y_nmem _⟩⟩,
  { specialize hy P (mem_primes.mpr ⟨hP, hP0⟩),
    dsimp at hy,
    rw [if_pos rfl, if_pos rfl, sub_eq_add_neg] at hy,
    simp only [pow_one] at hp_mem,
    exact (add_mem_cancel_right (neg_mem hp_mem)).mp (ideal.pow_le_self (by norm_num) hy) },
  { intros Q hQ hQP hyQ,
    by_cases hQ0 : Q = ⊥,
    { subst hQ0,
      rw ideal.mem_bot.mp hyQ at y_nmem,
      exact y_nmem (zero_mem _) },
    specialize hy Q (mem_primes.mpr ⟨hQ, hQ0⟩),
    dsimp only at hy,
    rw [if_neg hQP, subtype.coe_mk, if_neg hQP, pow_one, sub_eq_add_neg] at hy,
    refine hQ.ne_top _,
    rwa [ideal.eq_top_iff_one, ← neg_mem_iff, ← add_mem_cancel_left],
    assumption },
  { intros Q hQ Q' hQ' hne,
    assumption },
end

variables (S : Type*) [comm_ring S] [is_domain S]
variables [algebra R S] [module.free R S] [module.finite R S]
variables (p : ideal R) (hp0 : p ≠ ⊥) [is_prime p]
variables {Sₚ : Type*} [comm_ring Sₚ] [algebra S Sₚ]
variables [is_localization (algebra.algebra_map_submonoid S p.prime_compl) Sₚ]
variables [algebra R Sₚ] [is_scalar_tower R S Sₚ]
/- These hypotheses follow from properties of the localization but are needed for the statement,
so we leave them to the user to provide (automatically). -/
variables [is_domain Sₚ] [is_dedekind_domain Sₚ]

include S hp0

/-- If `p` is a prime in the Dedekind domain `R`, `S` an extension of `R` and `Sₚ` the localization
of `S` at `p`, then all primes in `Sₚ` are factors of the image of `p` in `Sₚ`. -/
lemma is_localization.over_prime.mem_normalized_factors_of_is_prime [decidable_eq (ideal Sₚ)]
  {P : ideal Sₚ} (hP : is_prime P) (hP0 : P ≠ ⊥) :
  P ∈ normalized_factors (ideal.map (algebra_map R Sₚ) p) :=
begin
  have non_zero_div : algebra.algebra_map_submonoid S p.prime_compl ≤ S⁰ :=
    map_le_non_zero_divisors_of_injective _ (no_zero_smul_divisors.algebra_map_injective _ _)
      p.prime_compl_le_non_zero_divisors,
  letI : algebra (localization.at_prime p) Sₚ := localization_algebra p.prime_compl S,
  haveI : is_scalar_tower R (localization.at_prime p) Sₚ :=
    is_scalar_tower.of_algebra_map_eq _,
  obtain ⟨pid, p', ⟨hp'0, hp'p⟩, hpu⟩ :=
    (discrete_valuation_ring.iff_pid_with_one_nonzero_prime (localization.at_prime p)).mp
      (is_localization.at_prime.discrete_valuation_ring_of_dedekind_domain R hp0 _),
  have : local_ring.maximal_ideal (localization.at_prime p) ≠ ⊥,
  { rw submodule.ne_bot_iff at ⊢ hp0,
    obtain ⟨x, x_mem, x_ne⟩ := hp0,
    exact ⟨algebra_map _ _ x,
      (is_localization.at_prime.to_map_mem_maximal_iff _ _ _).mpr x_mem,
      is_localization.to_map_ne_zero_of_mem_non_zero_divisors _ p.prime_compl_le_non_zero_divisors
        (mem_non_zero_divisors_of_ne_zero x_ne)⟩ },
  rw [← multiset.singleton_le, ← normalize_eq P,
      ← normalized_factors_irreducible (ideal.prime_of_is_prime hP0 hP).irreducible,
      ← dvd_iff_normalized_factors_le_normalized_factors hP0, dvd_iff_le,
      is_scalar_tower.algebra_map_eq R (localization.at_prime p) Sₚ, ← ideal.map_map,
      localization.at_prime.map_eq_maximal_ideal, ideal.map_le_iff_le_comap,
      hpu (local_ring.maximal_ideal _) ⟨this, _⟩, hpu (comap _ _) ⟨_, _⟩],
  { exact le_rfl },
  { have hRS : algebra.is_integral R S := is_integral_of_noetherian
      (is_noetherian_of_fg_of_noetherian' module.finite.out),
    exact mt (ideal.eq_bot_of_comap_eq_bot (is_integral_localization hRS)) hP0 },
  { exact ideal.comap_is_prime (algebra_map (localization.at_prime p) Sₚ) P },
  { exact (local_ring.maximal_ideal.is_maximal _).is_prime },
  { rw [ne.def, zero_eq_bot, ideal.map_eq_bot_iff_of_injective],
    { assumption },
    rw is_scalar_tower.algebra_map_eq R S Sₚ,
    exact (is_localization.injective Sₚ non_zero_div).comp
      (no_zero_smul_divisors.algebra_map_injective _ _) },
  { intros x,
    erw [is_localization.map_eq, is_scalar_tower.algebra_map_apply R S] },
end

/-- Let `p` be a prime in the Dedekind domain `R` and `S` be an integral extension of `R`,
then the localization `Sₚ` of `S` at `p` is a PID. -/
theorem is_dedekind_domain.is_principal_ideal_ring_localization_over_prime :
  is_principal_ideal_ring Sₚ :=
begin
  letI := classical.dec_eq (ideal Sₚ),
  letI := classical.dec_pred (λ (P : ideal Sₚ), P.is_prime),
  refine is_principal_ideal_ring.of_finite_primes
    (set.finite.of_finset (finset.filter (λ P, P.is_prime)
      ({⊥} ∪ (normalized_factors (ideal.map (algebra_map R Sₚ) p)).to_finset))
      (λ P, _)),
  rw [finset.mem_filter, finset.mem_union, finset.mem_singleton, set.mem_set_of,
      multiset.mem_to_finset],
  exact and_iff_right_of_imp (λ hP, or_iff_not_imp_left.mpr
    (is_localization.over_prime.mem_normalized_factors_of_is_prime S p hp0 hP))
end
