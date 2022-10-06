/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/

import ring_theory.adjoin_root
import ring_theory.dedekind_domain.ideal
import ring_theory.algebra_tower

/-!
# Kummer-Dedekind theorem

This file proves the monogenic version of the Kummer-Dedekind theorem on the splitting of prime
ideals in an extension of the ring of integers. This states that if `I` is a prime ideal of
Dedekind domain `R` and `S = R[α]` for some `α` that is integral over `R` with minimal polynomial
`f`, then the prime factorisations of `I * S` and `f mod I` have the same shape, i.e. they have the
same number of prime factors, and each prime factors of `I * S` can be paired with a prime factor
of `f mod I` in a way that ensures multiplicities match (in fact, this pairing can be made explicit
with a formula).

## Main definitions

 * `normalized_factors_map_equiv_normalized_factors_min_poly_mk` : The bijection in the
    Kummer-Dedekind theorem. This is the pairing between the prime factors of `I * S` and the prime
    factors of `f mod I`.

## Main results

 * `normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map` : The Kummer-Dedekind
    theorem.
 * `ideal.irreducible_map_of_irreducible_minpoly` : `I.map (algebra_map R S)` is irreducible if
    `(map I^.quotient.mk (minpoly R pb.gen))` is irreducible, where `pb` is a power basis of `S`
    over `R`.

## TODO

 * Prove the Kummer-Dedekind theorem in full generality.

 * Prove the converse of `ideal.irreducible_map_of_irreducible_minpoly`.

 * Prove that `normalized_factors_map_equiv_normalized_factors_min_poly_mk` can be expressed as
    `normalized_factors_map_equiv_normalized_factors_min_poly_mk g = ⟨I, G(α)⟩` for `g` a prime
    factor of `f mod I` and `G` a lift of `g` to `R[X]`.

## References

 * [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/

variables (R : Type*) {S : Type*} [comm_ring R] [comm_ring S] [algebra R S]

/-- Let `S / R` be a ring extension and `x : S`, then the conductor of R[x] is the
biggest ideal of `S` contained in `R[x]`. -/
def conductor (x : S) : ideal S :=
{ carrier := {a | ∀ (b : S), a * b ∈ algebra.adjoin R ({x} : set S)},
  zero_mem' := λ b, by simpa only [zero_mul] using subalgebra.zero_mem _,
  add_mem' := λ a b ha hb c, by simpa only [add_mul] using subalgebra.add_mem _ (ha c) (hb c),
  smul_mem' := λ c a ha b, by simpa only [smul_eq_mul, mul_left_comm, mul_assoc] using ha (c * b) }

variable {R}

lemma mem_adjoin_of_mem_conductor {x y : S} (hy : y ∈ conductor R x) :
  y ∈ algebra.adjoin R ({x} : set S) :=
by simpa only [mul_one] using hy 1

lemma conductor_eq_of_eq {x y : S} (h : (algebra.adjoin R ({x} : set S) : set S) =
  algebra.adjoin R ({y} : set S)) : conductor R x = conductor R y :=
ideal.ext (λ a, ⟨λ H b,by {rw [← set_like.mem_coe, (set.ext_iff.mp h _).symm], exact H b}, λ H b,
  by {rw [← set_like.mem_coe, (set.ext_iff.mp h _)], exact H b }⟩)

lemma conductor_subset_adjoin {x : S} : (conductor R x : set S) ⊆ algebra.adjoin R ({x} : set S) :=
λ y, mem_adjoin_of_mem_conductor

lemma mem_conductor_iff {x y : S} :
  y ∈ conductor R x ↔ ∀ (b : S), y * b ∈ algebra.adjoin R ({x} : set S) :=
⟨λ h, h, λ h, h⟩

variables {I : ideal R} {x : S}

/-- This technical lemma tell us that if `C` is the conductor of `R[x]` and `I` is an ideal of R
  then `p * (I * S) ⊆ I * R[x]` for any `p` in `C ∩ R` -/
-- TODO: (this should be generalized to `p ∈ C`)
lemma tricky_result (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (hx' : is_integral R x) {p : R} (hp : p ∈ ideal.comap (algebra_map R S) (conductor R x))
  {z : S} (hz : z ∈ algebra.adjoin R ({x} : set S))
  {hz' : z ∈ (I.map (algebra_map R S))} :
  (algebra_map R S p)*z ∈ algebra_map (algebra.adjoin R ({x} : set S)) S
    '' ↑(I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) :=
begin
  rw [ideal.map, ideal.span, finsupp.mem_span_image_iff_total] at hz',
  obtain ⟨l, H, H'⟩ := hz',
  rw finsupp.total_apply at H',
  rw [← H', mul_comm, finsupp.sum_mul],
  have test2 : ∀ {a : R}, a ∈ I → (l a • (algebra_map R S a) * (algebra_map R S p)) ∈ (algebra_map
   (algebra.adjoin R ({x} : set S)) S) '' (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))),
  { intros a ha,
    rw [algebra.id.smul_eq_mul, mul_assoc, mul_comm, mul_assoc, set.mem_image],
    refine exists.intro (algebra_map R (algebra.adjoin R ({x} : set S)) a * ⟨l a * algebra_map R S
      p, show l a * algebra_map R S p ∈ (algebra.adjoin R ({x} : set S)), from _ ⟩) _,
    { rw mul_comm,
      exact mem_conductor_iff.mp (ideal.mem_comap.mp hp) _ },
    refine ⟨_, by simpa only [map_mul, mul_comm (algebra_map R S p) (l a)]⟩,
    rw mul_comm,
    apply ideal.mul_mem_left (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) _
      (ideal.mem_map_of_mem _ ha) },
  refine finset.sum_induction _ (λ u, u ∈ (algebra_map (algebra.adjoin R ({x} : set S)) S) ''
    (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))))
    (λ a b ha hb, _) _ _,
  obtain ⟨z, hz, rfl⟩ := (set.mem_image _ _ _).mp ha,
  obtain ⟨y, hy, rfl⟩ := (set.mem_image _ _ _).mp hb,
  rw [← ring_hom.map_add, set.mem_image],
  exact exists.intro (z + y)
    ⟨ideal.add_mem (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) hz hy, rfl⟩,
  { refine (set.mem_image _ _ _).mpr (exists.intro 0 ⟨ideal.zero_mem (I.map (algebra_map R
    (algebra.adjoin R ({x} : set S)))), (ring_hom.map_zero _)⟩) },
  { intros y hy,
    exact test2 ((finsupp.mem_supported _ l).mp H hy) },
end

/-- A technical result telling us that `(I * S) ∩ R[x] = I * R[x]` for any ideal I of R. -/
lemma test (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤) (hx' : is_integral R x)
  (h_alg : function.injective (algebra_map (algebra.adjoin R ( {x} : set S)) S)):
  (I.map (algebra_map R S)).comap (algebra_map (algebra.adjoin R ( {x} : set S)) S)
    = I.map (algebra_map R (algebra.adjoin R ( {x} : set S))) :=
begin
  apply le_antisymm,
  { -- This is adapted from [Neukirch1992]. Let `C = (conductor R x)`. The idea of the proof
    -- is that since `I` and `C ∩ R` are coprime, we have
    -- `(I * S) ∩ R[x] ⊆ (I + C) * ((I * S) ∩ R[x]) ⊆ I * R[x] + I * C * S ⊆ I * R[x]`.
    intros y hy,
    obtain ⟨z, hz⟩ := y,
    obtain ⟨p, hp, q, hq, hpq⟩ := submodule.mem_sup.mp ((ideal.eq_top_iff_one _).mp hx),
    have temp : (algebra_map R S p)*z + (algebra_map R S q)*z = z,
    { simp only [←add_mul, ←ring_hom.map_add (algebra_map R S), hpq, map_one, one_mul] },
    suffices : z ∈ algebra_map (algebra.adjoin R ({x} : set S)) S '' (I.map (algebra_map R
      (algebra.adjoin R ({x} : set S)))) ↔ (⟨z, hz⟩ : (algebra.adjoin R ({x} : set S)))
      ∈ I.map (algebra_map R (algebra.adjoin R ({x} : set S))),
    { rw [← this, ← temp],
      obtain ⟨a, ha⟩ := (set.mem_image _ _ _).mp (tricky_result hx hx' hp hz),
      use a + (algebra_map R (algebra.adjoin R ({x} : set S)) q) * ⟨z, hz⟩,
      refine ⟨ ideal.add_mem (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) ha.left _,
        by simpa only [ha.right, map_add, map_mul, add_right_inj] ⟩,
      { rw mul_comm,
        exact ideal.mul_mem_left (I.map (algebra_map R (algebra.adjoin R ({x} : set S)))) _
          (ideal.mem_map_of_mem _ hq) },
      rwa ideal.mem_comap at hy },
    refine ⟨ λ h, _, λ h, (set.mem_image _ _ _).mpr (exists.intro ⟨z, hz⟩ ⟨by simp [h], rfl⟩ ) ⟩,
    { obtain ⟨x₁, hx₁, hx₂⟩ := (set.mem_image _ _ _).mp h,
      have : x₁ = ⟨z, hz⟩,
      { apply h_alg,
        simpa [hx₂], },
      rwa ← this }  },
  { have : algebra_map R S = (algebra_map (algebra.adjoin R ( {x} : set S)) S).comp
      (algebra_map R (algebra.adjoin R ( {x} : set S))) := by { ext, refl },
    rw [this, ← ideal.map_map],
    apply ideal.le_comap_map }
end

/-- The canonical morphism of rings from `R[x] ⧸ (I*R[x])` to `S ⧸ (I*S)` is an isomorphism
    when `I` and `(conductor R x) ∩ R` are coprime. -/
noncomputable def quot_adjoin_equiv_quot_map (hx : (conductor R x).comap (algebra_map R S) ⊔ I = ⊤)
  (hx' : is_integral R x)
  (h_alg : function.injective (algebra_map (algebra.adjoin R ( {x} : set S)) S)) :
  (algebra.adjoin R ( {x} : set S)) ⧸ (I.map (algebra_map R (algebra.adjoin R ( {x} : set S))))
    ≃+* S ⧸ (I.map (algebra_map R S : R →+* S)) :=
ring_equiv.of_bijective (ideal.quotient.lift (I.map (algebra_map R
  (algebra.adjoin R ( {x} : set S)))) (((I.map (algebra_map R S : R →+* S))^.quotient.mk).comp
  (algebra_map (algebra.adjoin R ( {x} : set S)) S : (algebra.adjoin R ( {x} : set S)) →+* S))
  (λ r hr, by {
    have : algebra_map R S = (algebra_map (algebra.adjoin R ( {x} : set S)) S).comp
    (algebra_map R (algebra.adjoin R ( {x} : set S))) := by ext ; refl,
    rw [ring_hom.comp_apply, ideal.quotient.eq_zero_iff_mem, this, ← ideal.map_map],
    exact ideal.mem_map_of_mem _ hr } ))
begin
  split,
  { --the kernel of the map is clearly `(I * S) ∩ R[α]`. To get injectivity, we need to show that
    --this is contained in `I * R[α]`, which is the content of the previous lemma.
    refine ideal.quotient.lift_injective_of_ker_le_ideal _ _ _ (λ u hu, _),
    rwa [ring_hom.mem_ker, ring_hom.comp_apply, ideal.quotient.eq_zero_iff_mem,
      ← ideal.mem_comap, test hx hx' h_alg] at hu },
  { -- Surjectivity follows from the surjectivity of the canonical map R[x] → S ⧸ (I * S),
    -- which in turn follows from the fact that `I * S + (conductor R x) = S`.
    refine ideal.quotient.lift_surjective_of_surjective _ _ _ (λ y, _),
    obtain ⟨z, hz⟩ := ideal.quotient.mk_surjective y,
    have : z ∈ conductor R x ⊔ (I.map (algebra_map R S : R →+* S)),
    { suffices : conductor R x ⊔ (I.map (algebra_map R S : R →+* S)) = ⊤,
      { simp only [this] },
      rw ideal.eq_top_iff_one at hx ⊢,
      replace hx := ideal.mem_map_of_mem (algebra_map R S) hx,
      rw [ideal.map_sup, ring_hom.map_one] at hx,
      exact (sup_le_sup (show  ((conductor R x).comap (algebra_map R S)).map (algebra_map R S) ≤
        conductor R x, from ideal.map_comap_le) (le_refl (I.map (algebra_map R S)))) hx },
    rw [← ideal.mem_quotient_iff_mem_sup, hz, ideal.mem_map_iff_of_surjective] at this,
    obtain ⟨u, hu, hu'⟩ := this,
    use ⟨u, conductor_subset_adjoin hu⟩,
    simpa only [← hu'],
    { exact ideal.quotient.mk_surjective } }

end

namespace kummer_dedekind

open_locale big_operators polynomial classical

open ideal polynomial double_quot unique_factorization_monoid

variables [is_domain S] [is_dedekind_domain S] [algebra R S]
variables (pb : power_basis R S)

local attribute [instance] ideal.quotient.field

variables [is_domain R]

/-- The first half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the prime
    factors of `I*S` are in bijection with those of the minimal polynomial of the generator of `S`
    over `R`, taken `mod I`.-/
noncomputable def normalized_factors_map_equiv_normalized_factors_min_poly_mk (hI : is_maximal I)
  (hI' : I ≠ ⊥) : {J : ideal S | J ∈ normalized_factors (I.map (algebra_map R S) )} ≃
    {d : (R ⧸ I)[X] | d ∈ normalized_factors (map I^.quotient.mk (minpoly R pb.gen)) } :=
((normalized_factors_equiv_of_quot_equiv ↑(pb.quotient_equiv_quotient_minpoly_map I)
  --show that `I * S` ≠ ⊥
  (show I.map (algebra_map R S) ≠ ⊥,
    by rwa [ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective, ← ne.def])
  --show that the ideal spanned by `(minpoly R pb.gen) mod I` is non-zero
  (by {by_contra, exact (show (map I^.quotient.mk (minpoly R pb.gen) ≠ 0), from
    polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen))
    (span_singleton_eq_bot.mp h) } )).trans
  (normalized_factors_equiv_span_normalized_factors
    (show (map I^.quotient.mk (minpoly R pb.gen)) ≠ 0, from
      polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen))).symm)

/-- The second half of the **Kummer-Dedekind Theorem** in the monogenic case, stating that the
    bijection `factors_equiv'` defined in the first half preserves multiplicities. -/
theorem multiplicity_factors_map_eq_multiplicity (hI : is_maximal I) (hI' : I ≠ ⊥) {J : ideal S}
  (hJ : J ∈ normalized_factors (I.map (algebra_map R S))) :
  multiplicity J (I.map (algebra_map R S)) =
    multiplicity ↑(normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' ⟨J, hJ⟩)
    (map I^.quotient.mk (minpoly R pb.gen)) :=
by rw [normalized_factors_map_equiv_normalized_factors_min_poly_mk, equiv.coe_trans,
       function.comp_app,
       multiplicity_normalized_factors_equiv_span_normalized_factors_symm_eq_multiplicity,
       normalized_factors_equiv_of_quot_equiv_multiplicity_eq_multiplicity]

/-- The **Kummer-Dedekind Theorem**. -/
theorem normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map (hI : is_maximal I)
  (hI' : I ≠ ⊥) : normalized_factors (I.map (algebra_map R S)) = multiset.map
  (λ f, ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm f : ideal S))
      (normalized_factors (polynomial.map I^.quotient.mk (minpoly R pb.gen))).attach :=
begin
  ext J,
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J ∈ normalized_factors (I.map (algebra_map R S)), swap,
  { rw [multiset.count_eq_zero.mpr hJ, eq_comm, multiset.count_eq_zero, multiset.mem_map],
    simp only [multiset.mem_attach, true_and, not_exists],
    rintros J' rfl,
    exact hJ
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm J').prop },

  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := multiplicity_factors_map_eq_multiplicity pb hI hI' hJ,
  rw [multiplicity_eq_count_normalized_factors, multiplicity_eq_count_normalized_factors,
      unique_factorization_monoid.normalize_normalized_factor _ hJ,
      unique_factorization_monoid.normalize_normalized_factor,
      part_enat.coe_inj]
    at this,
  refine this.trans _,
  -- Get rid of the `map` by applying the equiv to both sides.
  generalize hJ' : (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI')
    ⟨J, hJ⟩ = J',
  have : ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm
    J' : ideal S) = J,
  { rw [← hJ', equiv.symm_apply_apply _ _, subtype.coe_mk] },
  subst this,
  -- Get rid of the `attach` by applying the subtype `coe` to both sides.
  rw [multiset.count_map_eq_count' (λ f,
      ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm f
        : ideal S)),
      multiset.attach_count_eq_count_coe],
  { exact subtype.coe_injective.comp (equiv.injective _) },
  { exact (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' _).prop },
  { exact irreducible_of_normalized_factor _
    (normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI' _).prop },
  { exact polynomial.map_monic_ne_zero (minpoly.monic pb.is_integral_gen) },
  { exact irreducible_of_normalized_factor _ hJ },
  { rwa [← bot_eq_zero, ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective] },
end

theorem ideal.irreducible_map_of_irreducible_minpoly (hI : is_maximal I) (hI' : I ≠ ⊥)
  (hf : irreducible (map I^.quotient.mk (minpoly R pb.gen))) :
  irreducible (I.map (algebra_map R S)) :=
begin
  have mem_norm_factors : normalize (map I^.quotient.mk (minpoly R pb.gen)) ∈ normalized_factors
    (map I^.quotient.mk (minpoly R pb.gen)) := by simp [normalized_factors_irreducible hf],
  suffices : ∃ x, normalized_factors (I.map (algebra_map R S)) = {x},
  { obtain ⟨x, hx⟩ := this,
    have h := normalized_factors_prod (show I.map (algebra_map R S) ≠ 0, by
      rwa [← bot_eq_zero, ne.def, map_eq_bot_iff_of_injective pb.basis.algebra_map_injective]),
    rw [associated_iff_eq, hx, multiset.prod_singleton] at h,
    rw ← h,
    exact irreducible_of_normalized_factor x
      (show x ∈ normalized_factors (I.map (algebra_map R S)), by simp [hx]) },
  rw normalized_factors_ideal_map_eq_normalized_factors_min_poly_mk_map pb hI hI',
  use ((normalized_factors_map_equiv_normalized_factors_min_poly_mk pb hI hI').symm
    ⟨normalize (map I^.quotient.mk (minpoly R pb.gen)), mem_norm_factors⟩ : ideal S),
  rw multiset.map_eq_singleton,
  use ⟨normalize (map I^.quotient.mk (minpoly R pb.gen)), mem_norm_factors⟩,
  refine ⟨_, rfl⟩,
  apply multiset.map_injective subtype.coe_injective,
  rw [multiset.attach_map_coe, multiset.map_singleton, subtype.coe_mk],
  exact normalized_factors_irreducible hf
end

end kummer_dedekind
