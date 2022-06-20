/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import algebra.is_prime_pow
import field_theory.separable
import linear_algebra.free_module.finite.rank
import linear_algebra.free_module.pid
import linear_algebra.matrix.nonsingular_inverse
import ring_theory.dedekind_domain.ideal
import ring_theory.localization.module

/-!
# Ramification index and inertia degree

If `P : ideal S` lies over `p : ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed).
The **ramification index** `ramification_idx f p P` is the multiplicity of `P` in `map f p`,
and the **inertia degree** `inertia_deg f p P` is the degree of the field extension
`(S / P) : (R / p)`.

## TODO (#12287)

The main theorem `sum_ramification_inertia` states that for all coprime `P` lying over `p`,
`Σ P, ramification_idx f p P * inertia_deg f p P` equals the degree of the field extension
`Frac(S) : Frac(R)`.

## Implementation notes

Often the above theory is set up in the case where:
 * `R` is the ring of integers of a number field `K`,
 * `L` is a finite separable extension of `K`,
 * `S` is the integral closure of `R` in `L`,
 * `p` and `P` are maximal ideals,
 * `P` is an ideal lying over `p`
We will try to relax the above hypotheses as much as possible.

-/

universes u v

variables {R : Type u} [comm_ring R]
variables {S : Type v} [comm_ring S] (f : R →+* S)
variables (p : ideal R) (P : ideal S)

open finite_dimensional
open ideal
open unique_factorization_monoid

section dec_eq

open_locale classical

/-- The ramification index of `P` over `p` is the largest exponent `n` such that
`p` is contained in `P^n`.

In particular, if `p` is not contained in `P^n`, then the ramification index is 0.

If there is no largest such `n` (e.g. because `p = ⊥`), then `ramification_idx` is
defined to be 0.
-/
noncomputable def ramification_idx : ℕ :=
if h : ∃ n, map f p ≤ P ^ n ∧ ¬ map f p ≤ P ^ (n + 1)
then nat.find h
else 0

lemma ramification_idx_eq_find (h : ∃ n, map f p ≤ P ^ n ∧ ¬ map f p ≤ P ^ (n + 1)) :
  ramification_idx f p P = nat.find h :=
dif_pos h

lemma ramification_idx_spec (n : ℕ) (hle : map f p ≤ P ^ n) (hgt : ¬ map f p ≤ P ^ (n + 1)) :
  ramification_idx f p P = n :=
begin
  rw ramification_idx_eq_find f p P ⟨n, hle, hgt⟩,
  refine le_antisymm (nat.find_min' _ ⟨hle, hgt⟩) (le_of_not_gt (λ (h : nat.find _ < n), _)),
  obtain ⟨hle', hgt'⟩ := nat.find_spec ⟨n, and.intro hle hgt⟩,
  exact hgt' (hle.trans (ideal.pow_le_pow h))
end

@[simp] lemma ramification_idx_bot : ramification_idx f ⊥ P = 0 :=
dif_neg $ not_exists.mpr $ λ n hn, hn.2 (ideal.map_bot.le.trans bot_le)

@[simp] lemma ramification_idx_of_not_le (h : ¬ map f p ≤ P) : ramification_idx f p P = 0 :=
begin
  rw [ramification_idx, dif_pos, nat.find_eq_zero ⟨0, _⟩];
    rw [zero_add, pow_zero, pow_one, ideal.one_eq_top];
    exact ⟨le_top, h⟩
end

lemma ramification_idx_ne_zero {e : ℕ} (he : e ≠ 0)
  (hle : map f p ≤ P ^ e) (hnle : ¬ map f p ≤ P ^ (e + 1)):
  ramification_idx f p P ≠ 0 :=
by rwa ramification_idx_spec f p P e hle hnle

variables {f p P}

lemma le_pow_ramification_idx_of_ne_zero (h : ramification_idx f p P ≠ 0) :
  map f p ≤ P ^ ramification_idx f p P :=
begin
  rw ramification_idx at ⊢ h, split_ifs at ⊢ h with hex,
  swap, contradiction,
  exact (nat.find_spec hex).1
end

namespace is_dedekind_domain

variables [is_domain S] [is_dedekind_domain S]

lemma ramification_idx_eq_normalized_factors_count
  (hp0 : map f p ≠ ⊥) (hP : P.is_prime) (hP0 : P ≠ ⊥) :
  ramification_idx f p P = (normalized_factors (map f p)).count P :=
begin
  have hPirr := (ideal.prime_of_is_prime hP0 hP).irreducible,
  refine ramification_idx_spec _ _ _ _ (ideal.le_of_dvd _) (mt ideal.dvd_iff_le.mpr _);
    rw [dvd_iff_normalized_factors_le_normalized_factors (pow_ne_zero _ hP0) hp0,
        normalized_factors_pow, normalized_factors_irreducible hPirr, normalize_eq,
        multiset.nsmul_singleton, ← multiset.le_count_iff_repeat_le],
  { exact (nat.lt_succ_self _).not_le },
end

lemma ramification_idx_eq_factors_count (hp0 : map f p ≠ ⊥) (hP : P.is_prime) (hP0 : P ≠ ⊥) :
  ramification_idx f p P = (factors (map f p)).count P :=
by rw [is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0,
       factors_eq_normalized_factors]

lemma ramification_idx_ne_zero (hp0 : map f p ≠ ⊥) (hP : P.is_prime) (le : map f p ≤ P) :
  ramification_idx f p P ≠ 0 :=
begin
  have hP0 : P ≠ ⊥,
  { unfreezingI { rintro rfl },
    have := le_bot_iff.mp le,
    contradiction },
  have hPirr := (ideal.prime_of_is_prime hP0 hP).irreducible,
  rw is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0,
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalized_factors_of_dvd hp0 hPirr (ideal.dvd_iff_le.mpr le),
  rwa [multiset.count_ne_zero, associated_iff_eq.mp P'_eq],
end

lemma le_pow_ramification_idx (hp0 : map f p ≠ ⊥) (hP : P.is_prime) (le : map f p ≤ P) :
  map f p ≤ P ^ ramification_idx f p P :=
le_pow_ramification_idx_of_ne_zero (is_dedekind_domain.ramification_idx_ne_zero hp0 hP le)

end is_dedekind_domain

variables (f p P)

local attribute [instance] ideal.quotient.field

/-- The inertia degree of `P : ideal S` lying over `p : ideal R` is the degree of the
extension `(S / P) : (R / p)`.

We do not assume `P` lies over `p` in the definition; we return `0` instead.

See `inertia_deg_algebra_map` for the common case where `f = algebra_map R S`
and there is an algebra structure `R / p → S / P`.
-/
noncomputable def inertia_deg [hp : p.is_maximal] : ℕ :=
if hPp : comap f P = p
then @finrank (R ⧸ p) (S ⧸ P) _ _ $ @algebra.to_module _ _ _ _ $ ring_hom.to_algebra $
  ideal.quotient.lift p (P^.quotient.mk^.comp f) $
  λ a ha, quotient.eq_zero_iff_mem.mpr $ mem_comap.mp $ hPp.symm ▸ ha
else 0

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp] lemma inertia_deg_of_subsingleton [hp : p.is_maximal] [hQ : subsingleton (S ⧸ P)] :
  inertia_deg f p P = 0 :=
begin
  have := ideal.quotient.subsingleton_iff.mp hQ,
  unfreezingI { subst this },
  exact dif_neg (λ h, hp.ne_top $ h.symm.trans comap_top)
end

@[simp] lemma inertia_deg_algebra_map [algebra R S] [algebra (R ⧸ p) (S ⧸ P)]
  [is_scalar_tower R (R ⧸ p) (S ⧸ P)]
  [hp : p.is_maximal] :
  inertia_deg (algebra_map R S) p P = finrank (R ⧸ p) (S ⧸ P) :=
begin
  nontriviality (S ⧸ P) using [inertia_deg_of_subsingleton, finrank_zero_of_subsingleton],
  have := comap_eq_of_scalar_tower_quotient (algebra_map (R ⧸ p) (S ⧸ P)).injective,
  rw [inertia_deg, dif_pos this],
  congr,
  refine algebra.algebra_ext _ _ (λ x', quotient.induction_on' x' $ λ x, _),
  change ideal.quotient.lift p _ _ (ideal.quotient.mk p x) =
    algebra_map _ _ (ideal.quotient.mk p x),
  rw [ideal.quotient.lift_mk, ← ideal.quotient.algebra_map_eq, ← is_scalar_tower.algebra_map_eq,
      ← ideal.quotient.algebra_map_eq, ← is_scalar_tower.algebra_map_apply]
end

end dec_eq
