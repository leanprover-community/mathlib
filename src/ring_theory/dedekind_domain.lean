/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.discrete_valuation_ring
import ring_theory.fractional_ideal
import ring_theory.ideal.over
import ring_theory.integrally_closed
import ring_theory.polynomial.rational_root
import ring_theory.trace
import algebra.associated

/-!
# Dedekind domains

This file defines the notion of a Dedekind domain (or Dedekind ring),
giving three equivalent definitions (TODO: and shows that they are equivalent).

## Main definitions

 - `is_dedekind_domain` defines a Dedekind domain as a commutative ring that is
   Noetherian, integrally closed in its field of fractions and has Krull dimension at most one.
   `is_dedekind_domain_iff` shows that this does not depend on the choice of field of fractions.
 - `is_dedekind_domain_dvr` alternatively defines a Dedekind domain as an integral domain that
   is Noetherian, and the localization at every nonzero prime ideal is a DVR.
 - `is_dedekind_domain_inv` alternatively defines a Dedekind domain as an integral domain where
   every nonzero fractional ideal is invertible.
 - `is_dedekind_domain_inv_iff` shows that this does note depend on the choice of field of
   fractions.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ is_field A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variables (R A K : Type*) [comm_ring R] [integral_domain A] [field K]

open_locale non_zero_divisors

/-- A ring `R` has Krull dimension at most one if all nonzero prime ideals are maximal. -/
def ring.dimension_le_one : Prop :=
∀ p ≠ (⊥ : ideal R), p.is_prime → p.is_maximal

open ideal ring

namespace ring

lemma dimension_le_one.principal_ideal_ring
  [is_principal_ideal_ring A] : dimension_le_one A :=
λ p nonzero prime, by { haveI := prime, exact is_prime.to_maximal_ideal nonzero }

lemma dimension_le_one.is_integral_closure (B : Type*) [integral_domain B]
  [nontrivial R] [algebra R A] [algebra R B] [algebra B A] [is_scalar_tower R B A]
  [is_integral_closure B R A] (h : dimension_le_one R) :
  dimension_le_one B :=
λ p ne_bot prime, by exactI
  is_integral_closure.is_maximal_of_is_maximal_comap A p
    (h _ (is_integral_closure.comap_ne_bot A ne_bot) infer_instance)

lemma dimension_le_one.integral_closure [nontrivial R] [algebra R A]
  (h : dimension_le_one R) : dimension_le_one (integral_closure R A) :=
h.is_integral_closure R A (integral_closure R A)

end ring

/--
A Dedekind domain is an integral domain that is Noetherian, integrally closed, and
has Krull dimension at most one.

This is definition 3.2 of [Neukirch1992].

The integral closure condition is independent of the choice of field of fractions:
use `is_dedekind_domain_iff` to prove `is_dedekind_domain` for a given `fraction_map`.

This is the default implementation, but there are equivalent definitions,
`is_dedekind_domain_dvr` and `is_dedekind_domain_inv`.
TODO: Prove that these are actually equivalent definitions.
-/
class is_dedekind_domain : Prop :=
(is_noetherian_ring : is_noetherian_ring A)
(dimension_le_one : dimension_le_one A)
(is_integrally_closed : is_integrally_closed A)

-- See library note [lower instance priority]
attribute [instance, priority 100]
  is_dedekind_domain.is_noetherian_ring is_dedekind_domain.is_integrally_closed

/-- An integral domain is a Dedekind domain iff and only if it is
Noetherian, has dimension ≤ 1, and is integrally closed in a given fraction field.
In particular, this definition does not depend on the choice of this fraction field. -/
lemma is_dedekind_domain_iff (K : Type*) [field K] [algebra A K] [is_fraction_ring A K] :
  is_dedekind_domain A ↔ is_noetherian_ring A ∧ dimension_le_one A ∧
    (∀ {x : K}, is_integral A x → ∃ y, algebra_map A K y = x) :=
⟨λ ⟨hr, hd, hi⟩, ⟨hr, hd, λ x, (is_integrally_closed_iff K).mp hi⟩,
 λ ⟨hr, hd, hi⟩, ⟨hr, hd, (is_integrally_closed_iff K).mpr @hi⟩⟩

@[priority 100] -- See library note [lower instance priority]
instance is_principal_ideal_ring.is_dedekind_domain [is_principal_ideal_ring A] :
  is_dedekind_domain A :=
⟨principal_ideal_ring.is_noetherian_ring,
 ring.dimension_le_one.principal_ideal_ring A,
 unique_factorization_monoid.is_integrally_closed⟩

/--
A Dedekind domain is an integral domain that is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `is_dedekind_domain`.
TODO: prove the equivalence.
-/
structure is_dedekind_domain_dvr : Prop :=
(is_noetherian_ring : is_noetherian_ring A)
(is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : ideal A), P.is_prime →
  discrete_valuation_ring (localization.at_prime P))

section inverse

variables {R₁ : Type*} [integral_domain R₁] [algebra R₁ K] [is_fraction_ring R₁ K]
variables {I J : fractional_ideal R₁⁰ K}

noncomputable instance : has_inv (fractional_ideal R₁⁰ K) := ⟨λ I, 1 / I⟩

lemma inv_eq : I⁻¹ = 1 / I := rfl

lemma inv_zero' : (0 : fractional_ideal R₁⁰ K)⁻¹ = 0 := fractional_ideal.div_zero

lemma inv_nonzero {J : fractional_ideal R₁⁰ K} (h : J ≠ 0) :
J⁻¹ = ⟨(1 : fractional_ideal R₁⁰ K) / J, fractional_ideal.fractional_div_of_nonzero h⟩ :=
fractional_ideal.div_nonzero _

lemma coe_inv_of_nonzero {J : fractional_ideal R₁⁰ K} (h : J ≠ 0) :
  (↑J⁻¹ : submodule R₁ K) = is_localization.coe_submodule K ⊤ / J :=
by { rwa inv_nonzero _, refl, assumption }

variables {K}

lemma mem_inv_iff (hI : I ≠ 0) {x : K} :
  x ∈ I⁻¹ ↔ ∀ y ∈ I, x * y ∈ (1 : fractional_ideal R₁⁰ K) :=
fractional_ideal.mem_div_iff_of_nonzero hI

lemma inv_anti_mono (hI : I ≠ 0) (hJ : J ≠ 0) (hIJ : I ≤ J) :
  J⁻¹ ≤ I⁻¹ :=
λ x, by { simp only [mem_inv_iff hI, mem_inv_iff hJ], exact λ h y hy, h y (hIJ hy) }

lemma le_self_mul_inv {I : fractional_ideal R₁⁰ K} (hI : I ≤ (1 : fractional_ideal R₁⁰ K)) :
  I ≤ I * I⁻¹ :=
fractional_ideal.le_self_mul_one_div hI

variables (K)

lemma coe_ideal_le_self_mul_inv (I : ideal R₁) :
  (I : fractional_ideal R₁⁰ K) ≤ I * I⁻¹ :=
le_self_mul_inv fractional_ideal.coe_ideal_le_one

/-- `I⁻¹` is the inverse of `I` if `I` has an inverse. -/
theorem right_inverse_eq (I J : fractional_ideal R₁⁰ K) (h : I * J = 1) :
  J = I⁻¹ :=
begin
  have hI : I ≠ 0 := fractional_ideal.ne_zero_of_mul_eq_one I J h,
  suffices h' : I * (1 / I) = 1,
  { exact (congr_arg units.inv $
      @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl) },
  apply le_antisymm,
  { apply fractional_ideal.mul_le.mpr _,
    intros x hx y hy,
    rw mul_comm,
    exact (fractional_ideal.mem_div_iff_of_nonzero hI).mp hy x hx },
  rw ← h,
  apply fractional_ideal.mul_left_mono I,
  apply (fractional_ideal.le_div_iff_of_nonzero hI).mpr _,
  intros y hy x hx,
  rw mul_comm,
  exact fractional_ideal.mul_mem_mul hx hy
end

theorem mul_inv_cancel_iff {I : fractional_ideal R₁⁰ K} :
  I * I⁻¹ = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨I⁻¹, h⟩, λ ⟨J, hJ⟩, by rwa ← right_inverse_eq K I J hJ⟩

lemma mul_inv_cancel_iff_is_unit {I : fractional_ideal R₁⁰ K} :
  I * I⁻¹ = 1 ↔ is_unit I :=
(mul_inv_cancel_iff K).trans is_unit_iff_exists_inv.symm

variables {K' : Type*} [field K'] [algebra R₁ K'] [is_fraction_ring R₁ K']

@[simp] lemma map_inv (I : fractional_ideal R₁⁰ K) (h : K ≃ₐ[R₁] K') :
  (I⁻¹).map (h : K →ₐ[R₁] K') = (I.map h)⁻¹ :=
by rw [inv_eq, fractional_ideal.map_div, fractional_ideal.map_one, inv_eq]

open submodule submodule.is_principal

@[simp] lemma span_singleton_inv (x : K) :
  (fractional_ideal.span_singleton R₁⁰ x)⁻¹ = fractional_ideal.span_singleton _ (x⁻¹) :=
fractional_ideal.one_div_span_singleton x

lemma mul_generator_self_inv (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) :
  I * fractional_ideal.span_singleton _ (generator (I : submodule R₁ K))⁻¹ = 1 :=
begin
  -- Rewrite only the `I` that appears alone.
  conv_lhs { congr, rw fractional_ideal.eq_span_singleton_of_principal I },
  rw [fractional_ideal.span_singleton_mul_span_singleton, mul_inv_cancel,
    fractional_ideal.span_singleton_one],
  intro generator_I_eq_zero,
  apply h,
  rw [fractional_ideal.eq_span_singleton_of_principal I, generator_I_eq_zero,
    fractional_ideal.span_singleton_zero]
end

lemma invertible_of_principal (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) :
  I * I⁻¹ = 1 :=
(fractional_ideal.mul_div_self_cancel_iff).mpr
  ⟨fractional_ideal.span_singleton _ (generator (I : submodule R₁ K))⁻¹,
    mul_generator_self_inv _ I h⟩

lemma invertible_iff_generator_nonzero (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] :
  I * I⁻¹ = 1 ↔ generator (I : submodule R₁ K) ≠ 0 :=
begin
  split,
  { intros hI hg,
    apply fractional_ideal.ne_zero_of_mul_eq_one _ _ hI,
    rw [fractional_ideal.eq_span_singleton_of_principal I, hg,
        fractional_ideal.span_singleton_zero] },
  { intro hg,
    apply invertible_of_principal,
    rw [fractional_ideal.eq_span_singleton_of_principal I],
    intro hI,
    have := fractional_ideal.mem_span_singleton_self _ (generator (I : submodule R₁ K)),
    rw [hI, fractional_ideal.mem_zero_iff] at this,
    contradiction }
end

lemma is_principal_inv (I : fractional_ideal R₁⁰ K)
  [submodule.is_principal (I : submodule R₁ K)] (h : I ≠ 0) :
  submodule.is_principal (I⁻¹).1 :=
begin
  rw [fractional_ideal.val_eq_coe, fractional_ideal.is_principal_iff],
  use (generator (I : submodule R₁ K))⁻¹,
  have hI : I  * fractional_ideal.span_singleton _ ((generator (I : submodule R₁ K))⁻¹)  = 1,
  apply mul_generator_self_inv _ I h,
  exact (right_inverse_eq _ I (fractional_ideal.span_singleton _
    ((generator (I : submodule R₁ K))⁻¹)) hI).symm
end

@[simp] lemma fractional_ideal.one_inv : (1⁻¹ : fractional_ideal R₁⁰ K) = 1 :=
fractional_ideal.div_one

/--
A Dedekind domain is an integral domain such that every fractional ideal has an inverse.

This is equivalent to `is_dedekind_domain`.
In particular we provide a `fractional_ideal.comm_group_with_zero` instance,
assuming `is_dedekind_domain A`, which implies `is_dedekind_domain_inv`. For **integral** ideals,
`is_dedekind_domain`(`_inv`) implies only `ideal.comm_cancel_monoid_with_zero`.
-/
def is_dedekind_domain_inv : Prop :=
∀ I ≠ (⊥ : fractional_ideal A⁰ (fraction_ring A)), I * I⁻¹ = 1

open fractional_ideal

variables {R A K}

lemma is_dedekind_domain_inv_iff [algebra A K] [is_fraction_ring A K] :
  is_dedekind_domain_inv A ↔
    (∀ I ≠ (⊥ : fractional_ideal A⁰ K), I * I⁻¹ = 1) :=
begin
  set h := fraction_ring.alg_equiv A K,
  split; rintros hi I hI,
  { refine fractional_ideal.map_injective h.symm.to_alg_hom h.symm.injective _,
    rw [alg_equiv.to_alg_hom_eq_coe, inv_eq, fractional_ideal.map_mul,
        fractional_ideal.map_one_div, fractional_ideal.map_one, ← inv_eq, hi],
    exact fractional_ideal.map_ne_zero _ hI },
  { refine fractional_ideal.map_injective h.to_alg_hom h.injective _,
    rw [alg_equiv.to_alg_hom_eq_coe, inv_eq, fractional_ideal.map_mul,
        fractional_ideal.map_one_div, fractional_ideal.map_one, ← inv_eq, hi],
    exact fractional_ideal.map_ne_zero _ hI },
end

lemma fractional_ideal.adjoin_integral_eq_one_of_is_unit [algebra A K] [is_fraction_ring A K]
  (x : K) (hx : is_integral A x) (hI : is_unit (adjoin_integral A⁰ x hx)) :
  adjoin_integral A⁰ x hx = 1 :=
begin
  set I := adjoin_integral A⁰ x hx,
  have mul_self : I * I = I,
  { apply fractional_ideal.coe_to_submodule_injective, simp },
  convert congr_arg (* I⁻¹) mul_self;
  simp only [(mul_inv_cancel_iff_is_unit K).mpr hI, mul_assoc, mul_one],
end

namespace is_dedekind_domain_inv

variables [algebra A K] [is_fraction_ring A K] (h : is_dedekind_domain_inv A)

include h

lemma mul_inv_eq_one {I : fractional_ideal A⁰ K} (hI : I ≠ 0) : I * I⁻¹ = 1 :=
is_dedekind_domain_inv_iff.mp h I hI

lemma inv_mul_eq_one {I : fractional_ideal A⁰ K} (hI : I ≠ 0) : I⁻¹ * I = 1 :=
(mul_comm _ _).trans (h.mul_inv_eq_one hI)

protected lemma is_unit {I : fractional_ideal A⁰ K} (hI : I ≠ 0) : is_unit I :=
is_unit_of_mul_eq_one _ _ (h.mul_inv_eq_one hI)

lemma is_noetherian_ring : is_noetherian_ring A :=
begin
  refine is_noetherian_ring_iff.mpr ⟨λ (I : ideal A), _⟩,
  by_cases hI : I = ⊥,
  { rw hI, apply submodule.fg_bot },
  have hI : (I : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr hI,
  exact I.fg_of_is_unit (is_fraction_ring.injective A (fraction_ring A)) (h.is_unit hI)
end

lemma integrally_closed : is_integrally_closed A :=
begin
  -- It suffices to show that for integral `x`,
  -- `A[x]` (which is a fractional ideal) is in fact equal to `A`.
  refine ⟨λ x hx, _⟩,
  rw [← set.mem_range, ← algebra.mem_bot, ← subalgebra.mem_to_submodule, algebra.to_submodule_bot,
      ← coe_span_singleton A⁰ (1 : fraction_ring A), fractional_ideal.span_singleton_one,
      ← fractional_ideal.adjoin_integral_eq_one_of_is_unit x hx (h.is_unit _)],
  { exact mem_adjoin_integral_self A⁰ x hx },
  { exact λ h, one_ne_zero (eq_zero_iff.mp h 1 (subalgebra.one_mem _)) },
end

lemma dimension_le_one : dimension_le_one A :=
begin
  -- We're going to show that `P` is maximal because any (maximal) ideal `M`
  -- that is strictly larger would be `⊤`.
  rintros P P_ne hP,
  refine ideal.is_maximal_def.mpr ⟨hP.ne_top, λ M hM, _⟩,
  -- We may assume `P` and `M` (as fractional ideals) are nonzero.
  have P'_ne : (P : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr P_ne,
  have M'_ne : (M : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 :=
    (coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr
      (lt_of_le_of_lt bot_le hM).ne',

  -- In particular, we'll show `M⁻¹ * P ≤ P`
  suffices : (M⁻¹ * P : fractional_ideal A⁰ (fraction_ring A)) ≤ P,
  { rw [eq_top_iff, ← coe_ideal_le_coe_ideal (fraction_ring A), fractional_ideal.coe_ideal_top],
    calc (1 : fractional_ideal A⁰ (fraction_ring A)) = _ * _ * _ : _
    ... ≤ _ * _ : mul_right_mono (P⁻¹ * M : fractional_ideal A⁰ (fraction_ring A)) this
    ... = M : _,
    { rw [mul_assoc, ← mul_assoc ↑P, h.mul_inv_eq_one P'_ne, one_mul, h.inv_mul_eq_one M'_ne] },
    { rw [← mul_assoc ↑P, h.mul_inv_eq_one P'_ne, one_mul] },
    { apply_instance } },

  -- Suppose we have `x ∈ M⁻¹ * P`, then in fact `x = algebra_map _ _ y` for some `y`.
  intros x hx,
  have le_one : (M⁻¹ * P : fractional_ideal A⁰ (fraction_ring A)) ≤ 1,
  { rw [← h.inv_mul_eq_one M'_ne],
    exact fractional_ideal.mul_left_mono _ ((coe_ideal_le_coe_ideal (fraction_ring A)).mpr hM.le) },
  obtain ⟨y, hy, rfl⟩ := (mem_coe_ideal _).mp (le_one hx),

  -- Since `M` is strictly greater than `P`, let `z ∈ M \ P`.
  obtain ⟨z, hzM, hzp⟩ := set_like.exists_of_lt hM,
  -- We have `z * y ∈ M * (M⁻¹ * P) = P`.
  have zy_mem := fractional_ideal.mul_mem_mul (mem_coe_ideal_of_mem A⁰ hzM) hx,
  rw [← ring_hom.map_mul, ← mul_assoc, h.mul_inv_eq_one M'_ne, one_mul] at zy_mem,
  obtain ⟨zy, hzy, zy_eq⟩ := (mem_coe_ideal A⁰).mp zy_mem,
  rw is_fraction_ring.injective A (fraction_ring A) zy_eq at hzy,
  -- But `P` is a prime ideal, so `z ∉ P` implies `y ∈ P`, as desired.
  exact mem_coe_ideal_of_mem A⁰ (or.resolve_left (hP.mem_or_mem hzy) hzp)
end

/-- Showing one side of the equivalence between the definitions
`is_dedekind_domain_inv` and `is_dedekind_domain` of Dedekind domains. -/
theorem is_dedekind_domain : is_dedekind_domain A :=
⟨h.is_noetherian_ring, h.dimension_le_one, h.integrally_closed⟩

end is_dedekind_domain_inv

variables [algebra A K] [is_fraction_ring A K]

/-- Specialization of `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` to Dedekind domains:
Let `I : ideal A` be a nonzero ideal, where `A` is a Dedekind domain that is not a field.
Then `exists_prime_spectrum_prod_le_and_ne_bot_of_domain` states we can find a product of prime
ideals that is contained within `I`. This lemma extends that result by making the product minimal:
let `M` be a maximal ideal that contains `I`, then the product including `M` is contained within `I`
and the product excluding `M` is not contained within `I`. -/
lemma exists_multiset_prod_cons_le_and_prod_not_le [is_dedekind_domain A]
  (hNF : ¬ is_field A) {I M : ideal A} (hI0 : I ≠ ⊥) (hIM : I ≤ M) [hM : M.is_maximal] :
  ∃ (Z : multiset (prime_spectrum A)),
    (M ::ₘ (Z.map prime_spectrum.as_ideal)).prod ≤ I ∧
    ¬ (multiset.prod (Z.map prime_spectrum.as_ideal) ≤ I) :=
begin
  -- Let `Z` be a minimal set of prime ideals such that their product is contained in `J`.
  obtain ⟨Z₀, hZ₀⟩ := exists_prime_spectrum_prod_le_and_ne_bot_of_domain hNF hI0,
  obtain ⟨Z, ⟨hZI, hprodZ⟩, h_eraseZ⟩ := multiset.well_founded_lt.has_min
    (λ Z, (Z.map prime_spectrum.as_ideal).prod ≤ I ∧ (Z.map prime_spectrum.as_ideal).prod ≠ ⊥)
    ⟨Z₀, hZ₀⟩,
  have hZM : multiset.prod (Z.map prime_spectrum.as_ideal) ≤ M := le_trans hZI hIM,
  have hZ0 : Z ≠ 0, { rintro rfl, simpa [hM.ne_top] using hZM },
  obtain ⟨_, hPZ', hPM⟩ := (hM.is_prime.multiset_prod_le (mt multiset.map_eq_zero.mp hZ0)).mp hZM,
  -- Then in fact there is a `P ∈ Z` with `P ≤ M`.
  obtain ⟨P, hPZ, rfl⟩ := multiset.mem_map.mp hPZ',
  letI := classical.dec_eq (ideal A),
  have := multiset.map_erase prime_spectrum.as_ideal subtype.coe_injective P Z,
  obtain ⟨hP0, hZP0⟩ : P.as_ideal ≠ ⊥ ∧ ((Z.erase P).map prime_spectrum.as_ideal).prod ≠ ⊥,
  { rwa [ne.def, ← multiset.cons_erase hPZ', multiset.prod_cons, ideal.mul_eq_bot,
         not_or_distrib, ← this] at hprodZ },
  -- By maximality of `P` and `M`, we have that `P ≤ M` implies `P = M`.
  have hPM' := (is_dedekind_domain.dimension_le_one _ hP0 P.is_prime).eq_of_le hM.ne_top hPM,
  tactic.unfreeze_local_instances,
  subst hPM',

  -- By minimality of `Z`, erasing `P` from `Z` is exactly what we need.
  refine ⟨Z.erase P, _, _⟩,
  { convert hZI,
    rw [this, multiset.cons_erase hPZ'] },
  { refine λ h, h_eraseZ (Z.erase P) ⟨h, _⟩ (multiset.erase_lt.mpr hPZ),
    exact hZP0 }
end

namespace fractional_ideal

lemma exists_not_mem_one_of_ne_bot [is_dedekind_domain A]
  (hNF : ¬ is_field A) {I : ideal A} (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
  ∃ x : K, x ∈ (I⁻¹ : fractional_ideal A⁰ K) ∧ x ∉ (1 : fractional_ideal A⁰ K) :=
begin
  -- WLOG, let `I` be maximal.
  suffices : ∀ {M : ideal A} (hM : M.is_maximal),
    ∃ x : K, x ∈ (M⁻¹ : fractional_ideal A⁰ K) ∧ x ∉ (1 : fractional_ideal A⁰ K),
  { obtain ⟨M, hM, hIM⟩ : ∃ (M : ideal A), is_maximal M ∧ I ≤ M := ideal.exists_le_maximal I hI1,
    resetI,
    have hM0 := (M.bot_lt_of_maximal hNF).ne',
    obtain ⟨x, hxM, hx1⟩ := this hM,
    refine ⟨x, inv_anti_mono _ _ ((coe_ideal_le_coe_ideal _).mpr hIM) hxM, hx1⟩;
      apply fractional_ideal.coe_ideal_ne_zero; assumption },

  -- Let `a` be a nonzero element of `M` and `J` the ideal generated by `a`.
  intros M hM,
  resetI,
  obtain ⟨⟨a, haM⟩, ha0⟩ := submodule.nonzero_mem_of_bot_lt (M.bot_lt_of_maximal hNF),
  replace ha0 : a ≠ 0 := subtype.coe_injective.ne ha0,
  let J : ideal A := ideal.span {a},
  have hJ0 : J ≠ ⊥ := mt ideal.span_singleton_eq_bot.mp ha0,
  have hJM : J ≤ M := ideal.span_le.mpr (set.singleton_subset_iff.mpr haM),
  have hM0 : ⊥ < M := M.bot_lt_of_maximal hNF,

  -- Then we can find a product of prime (hence maximal) ideals contained in `J`,
  -- such that removing element `M` from the product is not contained in `J`.
  obtain ⟨Z, hle, hnle⟩ := exists_multiset_prod_cons_le_and_prod_not_le hNF hJ0 hJM,
  -- Choose an element `b` of the product that is not in `J`.
  obtain ⟨b, hbZ, hbJ⟩ := set_like.not_le_iff_exists.mp hnle,
  have hnz_fa : algebra_map A K a ≠ 0 :=
    mt ((ring_hom.injective_iff _).mp (is_fraction_ring.injective A K) a) ha0,
  have hb0 : algebra_map A K b ≠ 0 :=
    mt ((ring_hom.injective_iff _).mp (is_fraction_ring.injective A K) b)
      (λ h, hbJ $ h.symm ▸ J.zero_mem),
  -- Then `b a⁻¹ : K` is in `M⁻¹` but not in `1`.
  refine ⟨algebra_map A K b * (algebra_map A K a)⁻¹, (mem_inv_iff _).mpr _, _⟩,
  { exact (fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl _)).mpr hM0.ne' },
  { rintro y₀ hy₀,
    obtain ⟨y, h_Iy, rfl⟩ := (fractional_ideal.mem_coe_ideal _).mp hy₀,
    rw [mul_comm, ← mul_assoc, ← ring_hom.map_mul],
    have h_yb : y * b ∈ J,
    { apply hle,
      rw multiset.prod_cons,
      exact submodule.smul_mem_smul h_Iy hbZ },
    rw ideal.mem_span_singleton' at h_yb,
    rcases h_yb with ⟨c, hc⟩,
    rw [← hc, ring_hom.map_mul, mul_assoc, mul_inv_cancel hnz_fa, mul_one],
    apply fractional_ideal.coe_mem_one },
  { refine mt (fractional_ideal.mem_one_iff _).mp _,
    rintros ⟨x', h₂_abs⟩,
    rw [← div_eq_mul_inv, eq_div_iff_mul_eq hnz_fa, ← ring_hom.map_mul] at h₂_abs,
    have := ideal.mem_span_singleton'.mpr ⟨x', is_fraction_ring.injective A K h₂_abs⟩,
    contradiction },
end

lemma one_mem_inv_coe_ideal {I : ideal A} (hI : I ≠ ⊥) :
  (1 : K) ∈ (I : fractional_ideal A⁰ K)⁻¹ :=
begin
  rw mem_inv_iff (fractional_ideal.coe_ideal_ne_zero hI),
  intros y hy,
  rw one_mul,
  exact coe_ideal_le_one hy,
  assumption
end

lemma mul_inv_cancel_of_le_one [h : is_dedekind_domain A]
  {I : ideal A} (hI0 : I ≠ ⊥) (hI : ((I * I⁻¹)⁻¹ : fractional_ideal A⁰ K) ≤ 1) :
  (I * I⁻¹ : fractional_ideal A⁰ K) = 1 :=
begin
  -- Handle a few trivial cases.
  by_cases hI1 : I = ⊤,
  { rw [hI1, coe_ideal_top, one_mul, fractional_ideal.one_inv] },
  by_cases hNF : is_field A,
  { letI := hNF.to_field A, rcases hI1 (I.eq_bot_or_top.resolve_left hI0) },
  -- We'll show a contradiction with `exists_not_mem_one_of_ne_bot`:
  -- `J⁻¹ = (I * I⁻¹)⁻¹` cannot have an element `x ∉ 1`, so it must equal `1`.
  obtain ⟨J, hJ⟩ : ∃ (J : ideal A), (J : fractional_ideal A⁰ K) = I * I⁻¹ :=
    le_one_iff_exists_coe_ideal.mp mul_one_div_le_one,
  by_cases hJ0 : J = ⊥,
  { subst hJ0,
    refine absurd _ hI0,
    rw [eq_bot_iff, ← coe_ideal_le_coe_ideal K, hJ],
    exact coe_ideal_le_self_mul_inv K I,
    apply_instance },
  by_cases hJ1 : J = ⊤,
  { rw [← hJ, hJ1, coe_ideal_top] },
  obtain ⟨x, hx, hx1⟩ : ∃ (x : K),
    x ∈ (J : fractional_ideal A⁰ K)⁻¹ ∧ x ∉ (1 : fractional_ideal A⁰ K) :=
    exists_not_mem_one_of_ne_bot hNF hJ0 hJ1,
  contrapose! hx1 with h_abs,
  rw hJ at hx,
  exact hI hx,
end

/-- Nonzero integral ideals in a Dedekind domain are invertible.

We will use this to show that nonzero fractional ideals are invertible,
and finally conclude that fractional ideals in a Dedekind domain form a group with zero.
-/
lemma coe_ideal_mul_inv [h : is_dedekind_domain A] (I : ideal A) (hI0 : I ≠ ⊥) :
  (I * I⁻¹ : fractional_ideal A⁰ K) = 1 :=
begin
  -- We'll show `1 ≤ J⁻¹ = (I * I⁻¹)⁻¹ ≤ 1`.
  apply mul_inv_cancel_of_le_one hI0,
  by_cases hJ0 : (I * I⁻¹ : fractional_ideal A⁰ K) = 0,
  { rw [hJ0, inv_zero'], exact fractional_ideal.zero_le _ },
  intros x hx,
  -- In particular, we'll show all `x ∈ J⁻¹` are integral.
  suffices : x ∈ integral_closure A K,
  { rwa [is_integrally_closed.integral_closure_eq_bot, algebra.mem_bot, set.mem_range,
         ← fractional_ideal.mem_one_iff] at this;
      assumption },
  -- For that, we'll find a subalgebra that is f.g. as a module and contains `x`.
  -- `A` is a noetherian ring, so we just need to find a subalgebra between `{x}` and `I⁻¹`.
  rw mem_integral_closure_iff_mem_fg,
  have x_mul_mem : ∀ b ∈ (I⁻¹ : fractional_ideal A⁰ K), x * b ∈ (I⁻¹ : fractional_ideal A⁰ K),
  { intros b hb,
    rw mem_inv_iff at ⊢ hx,
    swap, { exact fractional_ideal.coe_ideal_ne_zero hI0 },
    swap, { exact hJ0 },
    simp only [mul_assoc, mul_comm b] at ⊢ hx,
    intros y hy,
    exact hx _ (fractional_ideal.mul_mem_mul hy hb) },
  -- It turns out the subalgebra consisting of all `p(x)` for `p : polynomial A` works.
  refine ⟨alg_hom.range (polynomial.aeval x : polynomial A →ₐ[A] K),
          is_noetherian_submodule.mp (fractional_ideal.is_noetherian I⁻¹) _ (λ y hy, _),
          ⟨polynomial.X, polynomial.aeval_X x⟩⟩,
  obtain ⟨p, rfl⟩ := (alg_hom.mem_range _).mp hy,
  rw polynomial.aeval_eq_sum_range,
  refine submodule.sum_mem _ (λ i hi, submodule.smul_mem _ _ _),
  clear hi,
  induction i with i ih,
  { rw pow_zero, exact one_mem_inv_coe_ideal hI0 },
  { show x ^ i.succ ∈ (I⁻¹ : fractional_ideal A⁰ K),
    rw pow_succ, exact x_mul_mem _ ih },
end

/-- Nonzero fractional ideals in a Dedekind domain are units.

This is also available as `_root_.mul_inv_cancel`, using the
`comm_group_with_zero` instance defined below.
-/
protected theorem mul_inv_cancel [is_dedekind_domain A]
  {I : fractional_ideal A⁰ K} (hne : I ≠ 0) : I * I⁻¹ = 1 :=
begin
  obtain ⟨a, J, ha, hJ⟩ :
    ∃ (a : A) (aI : ideal A), a ≠ 0 ∧ I = span_singleton A⁰ (algebra_map _ _ a)⁻¹ * aI :=
    exists_eq_span_singleton_mul I,
  suffices h₂ : I * (span_singleton A⁰ (algebra_map _ _ a) * J⁻¹) = 1,
  { rw mul_inv_cancel_iff,
    exact ⟨span_singleton A⁰ (algebra_map _ _ a) * J⁻¹, h₂⟩ },
  subst hJ,
  rw [mul_assoc, mul_left_comm (J : fractional_ideal A⁰ K), coe_ideal_mul_inv, mul_one,
      fractional_ideal.span_singleton_mul_span_singleton, inv_mul_cancel,
      fractional_ideal.span_singleton_one],
  { exact mt ((algebra_map A K).injective_iff.mp (is_fraction_ring.injective A K) _) ha },
  { exact fractional_ideal.coe_ideal_ne_zero_iff.mp (right_ne_zero_of_mul hne) }
end

end fractional_ideal

/-- `is_dedekind_domain` and `is_dedekind_domain_inv` are equivalent ways
to express that an integral domain is a Dedekind domain. -/
theorem is_dedekind_domain_iff_is_dedekind_domain_inv :
  is_dedekind_domain A ↔ is_dedekind_domain_inv A :=
⟨λ h I hI, by exactI fractional_ideal.mul_inv_cancel hI, λ h, h.is_dedekind_domain⟩

end inverse

section is_dedekind_domain

variables {R A} [is_dedekind_domain A] [algebra A K] [is_fraction_ring A K]

open fractional_ideal

noncomputable instance fractional_ideal.comm_group_with_zero :
  comm_group_with_zero (fractional_ideal A⁰ K) :=
{ inv := λ I, I⁻¹,
  inv_zero := inv_zero' _,
  exists_pair_ne := ⟨0, 1, (coe_to_fractional_ideal_injective (le_refl _)).ne
    (by simpa using @zero_ne_one (ideal A) _ _)⟩,
  mul_inv_cancel := λ I, fractional_ideal.mul_inv_cancel,
  .. fractional_ideal.comm_semiring }

noncomputable instance ideal.comm_cancel_monoid_with_zero :
  comm_cancel_monoid_with_zero (ideal A) :=
function.injective.comm_cancel_monoid_with_zero (coe_ideal_hom A⁰ (fraction_ring A))
  coe_ideal_injective (ring_hom.map_zero _) (ring_hom.map_one _) (ring_hom.map_mul _)

/-- For ideals in a Dedekind domain, to divide is to contain. -/
lemma ideal.dvd_iff_le {I J : ideal A} : (I ∣ J) ↔ J ≤ I :=
⟨ideal.le_of_dvd,
  λ h, begin
    by_cases hI : I = ⊥,
    { have hJ : J = ⊥, { rwa [hI, ← eq_bot_iff] at h },
      rw [hI, hJ] },
    have hI' : (I : fractional_ideal A⁰ (fraction_ring A)) ≠ 0 :=
      (fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors A))).mpr hI,
    have : (I : fractional_ideal A⁰ (fraction_ring A))⁻¹ * J ≤ 1 := le_trans
      (fractional_ideal.mul_left_mono (↑I)⁻¹ ((coe_ideal_le_coe_ideal _).mpr h))
      (le_of_eq (inv_mul_cancel hI')),
    obtain ⟨H, hH⟩ := fractional_ideal.le_one_iff_exists_coe_ideal.mp this,
    use H,
    refine coe_to_fractional_ideal_injective (le_refl (non_zero_divisors A))
      (show (J : fractional_ideal A⁰ (fraction_ring A)) = _, from _),
    rw [fractional_ideal.coe_ideal_mul, hH, ← mul_assoc, mul_inv_cancel hI', one_mul]
end⟩

lemma ideal.dvd_not_unit_iff_lt {I J : ideal A} :
  dvd_not_unit I J ↔ J < I :=
⟨λ ⟨hI, H, hunit, hmul⟩, lt_of_le_of_ne (ideal.dvd_iff_le.mp ⟨H, hmul⟩)
   (mt (λ h, have H = 1, from mul_left_cancel₀ hI (by rw [← hmul, h, mul_one]),
   show is_unit H, from this.symm ▸ is_unit_one) hunit),
 λ h, dvd_not_unit_of_dvd_of_not_dvd (ideal.dvd_iff_le.mpr (le_of_lt h))
   (mt ideal.dvd_iff_le.mp (not_le_of_lt h))⟩

instance : wf_dvd_monoid (ideal A) :=
{ well_founded_dvd_not_unit :=
  have well_founded ((>) : ideal A → ideal A → Prop) :=
  is_noetherian_iff_well_founded.mp
    (is_noetherian_ring_iff.mp is_dedekind_domain.is_noetherian_ring),
  by { convert this, ext, rw ideal.dvd_not_unit_iff_lt } }

instance ideal.unique_factorization_monoid :
  unique_factorization_monoid (ideal A) :=
{ irreducible_iff_prime := λ P,
  ⟨λ hirr, ⟨hirr.ne_zero, hirr.not_unit, λ I J, begin
    have : P.is_maximal,
    { refine ⟨⟨mt ideal.is_unit_iff.mpr hirr.not_unit, _⟩⟩,
      intros J hJ,
      obtain ⟨J_ne, H, hunit, P_eq⟩ := ideal.dvd_not_unit_iff_lt.mpr hJ,
      exact ideal.is_unit_iff.mp ((hirr.is_unit_or_is_unit P_eq).resolve_right hunit) },
    rw [ideal.dvd_iff_le, ideal.dvd_iff_le, ideal.dvd_iff_le,
        set_like.le_def, set_like.le_def, set_like.le_def],
    contrapose!,
    rintros ⟨⟨x, x_mem, x_not_mem⟩, ⟨y, y_mem, y_not_mem⟩⟩,
    exact ⟨x * y, ideal.mul_mem_mul x_mem y_mem,
           mt this.is_prime.mem_or_mem (not_or x_not_mem y_not_mem)⟩,
   end⟩,
   prime.irreducible⟩,
  .. ideal.wf_dvd_monoid }

noncomputable instance ideal.normalization_monoid : normalization_monoid (ideal A) :=
normalization_monoid_of_unique_units

@[simp] lemma ideal.dvd_span_singleton {I : ideal A} {x : A} :
  I ∣ ideal.span {x} ↔ x ∈ I :=
ideal.dvd_iff_le.trans (ideal.span_le.trans set.singleton_subset_iff)

lemma ideal.is_prime_of_prime {P : ideal A} (h : prime P) : is_prime P :=
begin
  refine ⟨_, λ x y hxy, _⟩,
  { unfreezingI { rintro rfl },
    rw ← ideal.one_eq_top at h,
    exact h.not_unit is_unit_one },
  { simp only [← ideal.dvd_span_singleton, ← ideal.span_singleton_mul_span_singleton] at ⊢ hxy,
    exact h.dvd_or_dvd hxy }
end

theorem ideal.prime_of_is_prime {P : ideal A} (hP : P ≠ ⊥) (h : is_prime P) : prime P :=
begin
  refine ⟨hP, mt ideal.is_unit_iff.mp h.ne_top, λ I J hIJ, _⟩,
  simpa only [ideal.dvd_iff_le] using (h.mul_le.mp (ideal.le_of_dvd hIJ)),
end

/-- In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `ideal A`
are exactly the prime ideals. -/
theorem ideal.prime_iff_is_prime {P : ideal A} (hP : P ≠ ⊥) :
  prime P ↔ is_prime P :=
⟨ideal.is_prime_of_prime, ideal.prime_of_is_prime hP⟩

end is_dedekind_domain

section is_integral_closure

/-! ### `is_integral_closure` section

We show that an integral closure of a Dedekind domain in a finite separable
field extension is again a Dedekind domain. This implies the ring of integers
of a number field is a Dedekind domain. -/

open algebra
open_locale big_operators

variables {A K} [algebra A K] [is_fraction_ring A K]
variables {L : Type*} [field L] (C : Type*) [integral_domain C]
variables [algebra K L] [finite_dimensional K L] [algebra A L] [is_scalar_tower A K L]
variables [algebra C L] [is_integral_closure C A L] [algebra A C] [is_scalar_tower A C L]

lemma is_integral_closure.range_le_span_dual_basis [is_separable K L]
  {ι : Type*} [fintype ι] [decidable_eq ι] (b : basis ι K L)
  (hb_int : ∀ i, is_integral A (b i)) [is_integrally_closed A] :
  ((algebra.linear_map C L).restrict_scalars A).range ≤
    submodule.span A (set.range $ (trace_form K L).dual_basis (trace_form_nondegenerate K L) b) :=
begin
  let db := (trace_form K L).dual_basis (trace_form_nondegenerate K L) b,
  rintros _ ⟨x, rfl⟩,
  simp only [linear_map.coe_restrict_scalars_eq_coe, algebra.linear_map_apply],
  have hx : is_integral A (algebra_map C L x) :=
    (is_integral_closure.is_integral A L x).algebra_map,
  suffices : ∃ (c : ι → A), algebra_map C L x = ∑ i, c i • db i,
  { obtain ⟨c, x_eq⟩ := this,
    rw x_eq,
    refine submodule.sum_mem _ (λ i _, submodule.smul_mem _ _ (submodule.subset_span _)),
    rw set.mem_range,
    exact ⟨i, rfl⟩ },
  suffices : ∃ (c : ι → K), ((∀ i, is_integral A (c i)) ∧ algebra_map C L x = ∑ i, c i • db i),
  { obtain ⟨c, hc, hx⟩ := this,
    have hc' : ∀ i, is_localization.is_integer A (c i) :=
      λ i, is_integrally_closed.is_integral_iff.mp (hc i),
    use λ i, classical.some (hc' i),
    refine hx.trans (finset.sum_congr rfl (λ i _, _)),
    conv_lhs { rw [← classical.some_spec (hc' i)] },
    rw [← is_scalar_tower.algebra_map_smul K (classical.some (hc' i)) (db i)] },
  refine ⟨λ i, db.repr (algebra_map C L x) i, (λ i, _), (db.sum_repr _).symm⟩,
  rw bilin_form.dual_basis_repr_apply,
  exact is_integral_trace (is_integral_mul hx (hb_int i))
end

lemma integral_closure_le_span_dual_basis [is_separable K L]
  {ι : Type*} [fintype ι] [decidable_eq ι] (b : basis ι K L)
  (hb_int : ∀ i, is_integral A (b i)) [is_integrally_closed A] :
  (integral_closure A L).to_submodule ≤ submodule.span A (set.range $
    (trace_form K L).dual_basis (trace_form_nondegenerate K L) b) :=
begin
  refine le_trans _ (is_integral_closure.range_le_span_dual_basis (integral_closure A L) b hb_int),
  intros x hx,
  exact ⟨⟨x, hx⟩, rfl⟩
end

variables (A) (K)

include K

/-- Send a set of `x`'es in a finite extension `L` of the fraction field of `R`
to `(y : R) • x ∈ integral_closure R L`. -/
lemma exists_integral_multiples (s : finset L) :
  ∃ (y ≠ (0 : A)), ∀ x ∈ s, is_integral A (y • x) :=
begin
  haveI := classical.dec_eq L,
  refine s.induction _ _,
  { use [1, one_ne_zero],
    rintros x ⟨⟩ },
  { rintros x s hx ⟨y, hy, hs⟩,
    obtain ⟨x', y', hy', hx'⟩ := exists_integral_multiple
      ((is_fraction_ring.is_algebraic_iff A K).mpr (algebra.is_algebraic_of_finite x))
      ((algebra_map A L).injective_iff.mp _),
    refine ⟨y * y', mul_ne_zero hy hy', λ x'' hx'', _⟩,
    rcases finset.mem_insert.mp hx'' with (rfl | hx''),
    { rw [mul_smul, algebra.smul_def, algebra.smul_def, mul_comm _ x'', hx'],
      exact is_integral_mul is_integral_algebra_map x'.2 },
    { rw [mul_comm, mul_smul, algebra.smul_def],
      exact is_integral_mul is_integral_algebra_map (hs _ hx'') },
    { rw is_scalar_tower.algebra_map_eq A K L,
      apply (algebra_map K L).injective.comp,
      exact is_fraction_ring.injective _ _ } }
end

variables (L)

/-- If `L` is a finite extension of `K = Frac(A)`,
then `L` has a basis over `A` consisting of integral elements. -/
lemma finite_dimensional.exists_is_basis_integral :
  ∃ (s : finset L) (b : basis s K L), (∀ x, is_integral A (b x)) :=
begin
  letI := classical.dec_eq L,
  let s' := is_noetherian.finset_basis_index K L,
  let bs' := is_noetherian.finset_basis K L,
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (finset.univ.image bs'),
  have hy' : algebra_map A L y ≠ 0,
  { refine mt ((algebra_map A L).injective_iff.mp _ _) hy,
    rw is_scalar_tower.algebra_map_eq A K L,
    exact (algebra_map K L).injective.comp (is_fraction_ring.injective A K) },
  refine ⟨s', bs'.map { to_fun := λ x, algebra_map A L y * x,
                        inv_fun := λ x, (algebra_map A L y)⁻¹ * x,
                        left_inv := _,
                        right_inv := _,
                        .. algebra.lmul _ _ (algebra_map A L y) },
          _⟩,
  { intros x, simp only [inv_mul_cancel_left₀ hy'] },
  { intros x, simp only [mul_inv_cancel_left₀ hy'] },
  { rintros ⟨x', hx'⟩,
    simp only [algebra.smul_def, finset.mem_image, exists_prop, finset.mem_univ, true_and] at his',
    simp only [basis.map_apply, linear_equiv.coe_mk],
    exact his' _ ⟨_, rfl⟩ }
end

variables (A K L) [is_separable K L]
include L

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian. -/
lemma is_integral_closure.is_noetherian_ring [is_integrally_closed A] [is_noetherian_ring A] :
  is_noetherian_ring C :=
begin
  haveI := classical.dec_eq L,
  obtain ⟨s, b, hb_int⟩ := finite_dimensional.exists_is_basis_integral A K L,
  rw is_noetherian_ring_iff,
  let b' := (trace_form K L).dual_basis (trace_form_nondegenerate K L) b,
  letI := is_noetherian_span_of_finite A (set.finite_range b'),
  let f : C →ₗ[A] submodule.span A (set.range b') :=
    (submodule.of_le (is_integral_closure.range_le_span_dual_basis C b hb_int)).comp
    ((algebra.linear_map C L).restrict_scalars A).range_restrict,
  refine is_noetherian_of_tower A (is_noetherian_of_injective f _),
  rw [linear_map.ker_comp, submodule.ker_of_le, submodule.comap_bot, linear_map.ker_cod_restrict],
  exact linear_map.ker_eq_bot_of_injective (is_integral_closure.algebra_map_injective C A L)
end

variables {A K}

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure of `A` in `L` is
Noetherian. -/
lemma integral_closure.is_noetherian_ring [is_integrally_closed A] [is_noetherian_ring A] :
  is_noetherian_ring (integral_closure A L) :=
is_integral_closure.is_noetherian_ring A K L (integral_closure A L)

variables (A K)
/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure `C` of `A` in `L` is a Dedekind domain.

Can't be an instance since `A`, `K` or `L` can't be inferred. See also the instance
`integral_closure.is_dedekind_domain_fraction_ring` where `K := fraction_ring A`
and `C := integral_closure A L`.
-/
lemma is_integral_closure.is_dedekind_domain [h : is_dedekind_domain A] :
  is_dedekind_domain C :=
begin
  haveI : is_fraction_ring C L := is_integral_closure.is_fraction_ring_of_finite_extension A K L C,
  exact
  ⟨is_integral_closure.is_noetherian_ring A K L C,
   h.dimension_le_one.is_integral_closure _ L _,
   (is_integrally_closed_iff L).mpr (λ x hx, ⟨is_integral_closure.mk' C x
      (is_integral_trans (is_integral_closure.is_integral_algebra A L) _ hx),
    is_integral_closure.algebra_map_mk' _ _ _⟩)⟩
end

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

Can't be an instance since `K` can't be inferred. See also the instance
`integral_closure.is_dedekind_domain_fraction_ring` where `K := fraction_ring A`.
-/
lemma integral_closure.is_dedekind_domain [h : is_dedekind_domain A] :
  is_dedekind_domain (integral_closure A L) :=
is_integral_closure.is_dedekind_domain A K L (integral_closure A L)

omit K

variables [algebra (fraction_ring A) L] [is_scalar_tower A (fraction_ring A) L]
variables [finite_dimensional (fraction_ring A) L] [is_separable (fraction_ring A) L]

/- If `L` is a finite separable extension of `Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

See also the lemma `integral_closure.is_dedekind_domain` where you can choose
the field of fractions yourself.
-/
instance integral_closure.is_dedekind_domain_fraction_ring
  [is_dedekind_domain A] : is_dedekind_domain (integral_closure A L) :=
integral_closure.is_dedekind_domain A (fraction_ring A) L

end is_integral_closure

section is_dedekind_domain

variables {T : Type*} [integral_domain T] [is_dedekind_domain T] (I J : ideal T)
open_locale classical
open multiset unique_factorization_monoid ideal

lemma prod_normalized_factors_eq_self {I : ideal T} (hI : I ≠ ⊥) :
  (normalized_factors I).prod = I :=
associated_iff_eq.1 (normalized_factors_prod hI)

lemma normalized_factors_prod {α : multiset (ideal T)}
  (h : ∀ p ∈ α, prime p) : normalized_factors α.prod = α :=
by { simp_rw [← multiset.rel_eq, ← associated_eq_eq],
     exact prime_factors_unique (prime_of_normalized_factor) h
      (normalized_factors_prod (α.prod_ne_zero_of_prime h)) }

lemma count_le_of_ideal_ge {I J : ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : ideal T) :
  count K (normalized_factors J) ≤ count K (normalized_factors I) :=
le_iff_count.1 ((dvd_iff_normalized_factors_le_normalized_factors (ne_bot_of_le_ne_bot hI h) hI).1
  (dvd_iff_le.2 h)) _

lemma sup_eq_prod_inf_factors (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
  I ⊔ J = (normalized_factors I ∩ normalized_factors J).prod :=
begin
  have H : normalized_factors (normalized_factors I ∩ normalized_factors J).prod =
    normalized_factors I ∩ normalized_factors J,
  { apply _root_.normalized_factors_prod,
    intros p hp,
    rw mem_inter at hp,
    exact prime_of_normalized_factor p hp.left },
  have := (multiset.prod_ne_zero_of_prime (normalized_factors I ∩ normalized_factors J)
      (λ _ h, prime_of_normalized_factor _ (multiset.mem_inter.1 h).1)),
  apply le_antisymm,
  { rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le],
    split,
    { rw [dvd_iff_normalized_factors_le_normalized_factors this hI, H],
      exact inf_le_left },
    { rw [dvd_iff_normalized_factors_le_normalized_factors this hJ, H],
      exact inf_le_right } },
  { rw [← dvd_iff_le, dvd_iff_normalized_factors_le_normalized_factors,
      _root_.normalized_factors_prod, le_iff_count],
    { intro a,
      rw multiset.count_inter,
      exact le_min (count_le_of_ideal_ge le_sup_left hI a)
        (count_le_of_ideal_ge le_sup_right hJ a) },
    { intros p hp,
      rw mem_inter at hp,
      exact prime_of_normalized_factor p hp.left },
    { exact ne_bot_of_le_ne_bot hI le_sup_left },
    { exact this } },
end


variables {I}

lemma irreducible_pow_sup (hI : I ≠ ⊥) {p : ideal T} (hp : irreducible p) (n : ℕ) :
  p^n ⊔ I = p^(min ((normalized_factors I).count p) n) :=
by rw [sup_eq_prod_inf_factors (p^n) I (pow_ne_zero n hp.ne_zero) hI, ← inf_eq_inter,
       normalized_factors_irreducible_pow hp, normalize_eq p, repeat_inf, prod_repeat]

lemma irreducible_pow_sup_of_ge (hI : I ≠ ⊥) {p : ideal T} (hp : irreducible p) (n : ℕ)
  (hn : ↑n ≤ multiplicity p I) : p^n ⊔ I = p^n :=
begin
  rw [irreducible_pow_sup hI hp, min_eq_right],
  rwa [multiplicity_eq_count_normalized_factors hp hI, enat.coe_le_coe, normalize_eq p]
    at hn
end

lemma irreducible_pow_sup_of_le (hI : I ≠ ⊥) {p : ideal T} (hp : irreducible p) (n : ℕ)
  (hn : multiplicity p I ≤ n) : p^n ⊔ I = p ^ (multiplicity p I).get (enat.dom_of_le_coe hn) :=
begin
  rw [irreducible_pow_sup hI hp, min_eq_left],
  congr,
  { rw [← enat.coe_inj, enat.coe_get, multiplicity_eq_count_normalized_factors hp hI,
    normalize_eq p] },
  { rwa [multiplicity_eq_count_normalized_factors hp hI, enat.coe_le_coe, normalize_eq p]
      at hn }
end

end is_dedekind_domain
/-
section quotient_multiplicity
noncomputable theory
open_locale classical
variables {T : Type u_1} [integral_domain T] [is_dedekind_domain T] {I : ideal T}
variables {S : Type u_2}  [integral_domain S] [is_dedekind_domain S] {J : ideal S}
open ideal unique_factorization_monoid

/-- The predicate that the sequence of powers `(p')^m` for `n ≤ m` is constant,
    where `p'` is the image of `p` in `R/I` -/
def shifted_seq_pow_constant {R : Type u_3} [comm_ring R] (I : ideal R) (p : ideal R) : ℕ → Prop :=
  λ n, ∀ m : ℕ, n ≤ m → (map I^.quotient.mk p)^n = (map I^.quotient.mk p)^m

/--The sequence of powers `(p')^m` is eventually constant, where `p'` is the image of `p` in `R/I`-/
lemma pow_map_eq_of_exponent_ge (hI : I ≠ ⊥) {p : ideal T} (hp : irreducible p) (n : ℕ)
  (hn : multiplicity p I ≤ n) :
  (map I^.quotient.mk p)^n =
    (map I^.quotient.mk p)^((multiplicity p I).get (enat.dom_of_le_coe hn)) :=
begin
  rw [← map_pow, ← map_pow],
  have H : map I^.quotient.mk (p^n) = map I^.quotient.mk (p^n ⊔ I),
  { rw [map_sup, map_mk_eq_bot_of_le (le_refl I), sup_bot_eq] },
  rw irreducible_pow_sup_of_le hI hp n hn at H,
  exact H,
end

-- Can go to `ideal/operations.lean`, probably somewhere after `comap_map_of_surjective`.
lemma ideal.map_strict_mono_of_surjective {R S : Type*} [ring R] [ring S]
  (f : R →+* S) (hf : function.surjective f) {I J : ideal R}
  (hI : f.ker ≤ I) (hJ : f.ker ≤ J) (h : I < J) :
  map f I < map f J :=
lt_of_le_of_ne (map_mono h.le) (λ hIJ, h.ne $ calc
  I = I ⊔ comap f ⊥ : by rw [← f.ker_eq_comap_bot, sup_eq_left.mpr hI]
    ... = comap f (map f I) : (comap_map_of_surjective f hf I).symm
    ... = comap f (map f J) : by rw hIJ
    ... = J ⊔ comap f ⊥ : comap_map_of_surjective f hf J
    ... = J : by rw [← f.ker_eq_comap_bot, sup_eq_left.mpr hJ] )

lemma pow_map_mk_lt' (hI : I ≠ ⊥) {p : ideal T} (hp : irreducible p) {k n : ℕ}
  (hlt : n < k) (hle : ↑k ≤ multiplicity p I) :
  (map I^.quotient.mk p)^k < (map I^.quotient.mk p)^n :=
begin
  rw [← ideal.map_pow, ← ideal.map_pow],
  refine ideal.map_strict_mono_of_surjective _ quotient.mk_surjective _ _ _;
    try { rw mk_ker, apply le_of_dvd, apply multiplicity.pow_dvd_of_le_multiplicity },
  { assumption }, { exact ((enat.coe_lt_coe.mpr hlt).trans_le hle).le },
  rw ← ideal.dvd_not_unit_iff_lt,
  split,
  { exact pow_ne_zero n hp.ne_zero },
  { refine ⟨ p^(k - n), not_is_unit_of_not_is_unit_dvd hp.not_unit
      (dvd_pow (dvd_refl p) (ne_of_gt (sub_pos_iff_lt.mpr hlt))), _⟩,
    rw [← pow_add, nat.add_sub_of_le hlt.le] }
end

lemma pow_map_mk_lt (hI : I ≠ ⊥) {p : ideal T} (hp : irreducible p) {k n : ℕ}
  (hlt : n < k) (hn : ↑n < multiplicity p I) :
  (map I^.quotient.mk p)^k < (map I^.quotient.mk p)^n :=
begin
  cases le_total ↑k (multiplicity p I) with hk hk,
  { exact pow_map_mk_lt' hI hp hlt hk },
  { rw pow_map_eq_of_exponent_ge hI hp _ hk,
    refine pow_map_mk_lt' hI hp (enat.coe_lt_coe.mp _) (le_of_eq _);
      rwa enat.coe_get },
end

-- For somewhere near the start of `unique_factorization_domain.lean`
lemma multiplicity.finite_prime_left {R : Type*} [comm_cancel_monoid_with_zero R]
  [wf_dvd_monoid R] {a b : R} (ha : prime a) (hb : b ≠ 0) :
  multiplicity.finite a b :=
begin
  revert hb,
  refine wf_dvd_monoid.induction_on_irreducible b _ _ _,
  { contradiction },
  { intros u hu hu',
    rw [multiplicity.finite_iff_dom, multiplicity.is_unit_right ha.not_unit hu],
    exact enat.dom_coe 0 },
  { intros b p hb hp ih hpb,
    refine multiplicity.finite_mul ha
      (multiplicity.finite_iff_dom.mpr (enat.dom_of_le_coe (show multiplicity a p ≤ ↑1, from _)))
      (ih hb),
    norm_cast,
    exact (((multiplicity.squarefree_iff_multiplicity_le_one p).mp hp.squarefree a)
      .resolve_right ha.not_unit) }
end

lemma pow_map_mk_constant_iff_multiplicity_le (hI : I ≠ ⊥) {p : ideal T} (hp : irreducible p)
  {n : ℕ} : (∀ m, n ≤ m → (map I^.quotient.mk p)^n = (map I^.quotient.mk p)^m) ↔
    multiplicity p I ≤ n :=
begin
  split,
  { contrapose!, intro H,
    have := multiplicity.finite_prime_left (irreducible_iff_prime.mp hp) hI,
    have H' : n < (multiplicity p I).get this,
    { simpa only [← enat.coe_lt_coe, enat.coe_get] using H },
    exact ⟨(multiplicity p I).get this, H'.le, (pow_map_mk_lt hI hp H' H).ne'⟩ },
  { intros hn m hm,
    rw [pow_map_eq_of_exponent_ge hI hp n hn, pow_map_eq_of_exponent_ge hI hp m],
    exact hn.trans (enat.coe_le_coe.mpr hm) }
end

lemma seq_pow_eventually_constant' (hI : I ≠ ⊥) {p : ideal T} (hp : irreducible p) :
  shifted_seq_pow_constant I p ((normalized_factors I).count p) :=
begin
  refine (pow_map_mk_constant_iff_multiplicity_le hI hp).2 _,
  rw [multiplicity_eq_count_normalized_factors hp hI, normalize_eq],
end

/--The quotient multiplicity of `p` is the least natural number `n` such that the sequence of
 powers `(p')^m` for `m ≥ n` is constant, where `p'` is the image of `p` in `R/I` -/
def quotient_multiplicity (hI : I ≠ ⊥) {p : ideal T} (hp : irreducible p) : ℕ :=
nat.find ⟨(normalized_factors I).count p, seq_pow_eventually_constant' hI hp⟩

/--The quotient multiplicity of a prime factor `p` of `I ≠ 0` is equal to the multiplicity of `p`
  in the factorisation of `I` -/
lemma quotient_multiplicity_eq_count (hI : I ≠ 0) (p : ideal T) (hp : irreducible p) :
  multiplicity p I = quotient_multiplicity hI hp :=
begin
  apply le_antisymm,
  { rw [quotient_multiplicity, ← pow_map_mk_constant_iff_multiplicity_le hI hp],
    exact nat.find_spec (exists.intro ((normalized_factors I).count p)
      (seq_pow_eventually_constant' hI hp)) },
  { rw [quotient_multiplicity, multiplicity_eq_count_normalized_factors hp hI, normalize_eq,
    enat.coe_le_coe],
    exact nat.find_min' (exists.intro ((normalized_factors I).count p)
    (seq_pow_eventually_constant' hI hp)) (seq_pow_eventually_constant' hI hp) }
end

lemma quotient.mk_injective_iff {R : Type*} [comm_ring R] {I : ideal R} :
  function.injective I^.quotient.mk ↔ I = ⊥ :=
by rw [ring_hom.injective_iff_ker_eq_bot, mk_ker]

lemma comap_ne_bot_of_not_injective {R S : Type*} [comm_ring R] [comm_ring S]
  {f : R →+* S} (hf : ¬ function.injective f) (I : ideal S) :
  comap f I ≠ ⊥ :=
ne_bot_of_le_ne_bot (mt f.injective_iff_ker_eq_bot.mpr hf) (ker_le_comap f)

lemma comap_map_map_mem_normalized_factors_of_mem_normalized_factors (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
  (f : I.quotient ≃+* J.quotient) {p : ideal T} (hp : p ∈ normalized_factors I) :
  (comap J^.quotient.mk (map ↑f (map I^.quotient.mk p))) ∈ normalized_factors J :=
begin
  suffices H₃ : (comap J^.quotient.mk (map ↑f (map I^.quotient.mk p))) ∈ normalized_factors
    (comap J^.quotient.mk (map ↑f (map I^.quotient.mk p))),
  { refine multiset.mem_of_le ((dvd_iff_normalized_factors_le_normalized_factors
      (comap_ne_bot_of_not_injective (mt quotient.mk_injective_iff.mp hJ) _)
       hJ).1 _) H₃,
    rw dvd_iff_le,
    have : (J^.quotient.mk).ker ≤ (comap J^.quotient.mk (map ↑f (map I^.quotient.mk p))) :=
      ker_le_comap J^.quotient.mk,
    rw mk_ker at this,
    exact this },
  rw normalized_factors_irreducible,
  exact multiset.mem_singleton.mpr ((associated_iff_eq.1 (normalize_associated
    (comap J^.quotient.mk (map ↑f (map I^.quotient.mk p))))).symm),
  apply prime.irreducible,
  apply (prime_iff_is_prime
    (comap_ne_bot_of_not_injective (mt quotient.mk_injective_iff.mp hJ) _)).2,
  convert comap_is_prime J^.quotient.mk _,
  convert map_is_prime_of_equiv f,
  convert map_is_prime_of_surjective quotient.mk_surjective _,
  exact (is_prime_of_prime (prime_of_normalized_factor p hp)),
  rw mk_ker,
  exact (dvd_iff_le.1 (dvd_of_mem_normalized_factors hp)),
end

@[simps]
def ideal_correspondence (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient):
  {p : ideal T | p ∈ normalized_factors I} ≃ {p : ideal S | p ∈ normalized_factors J} :=
{
  to_fun := λ X, ⟨comap J^.quotient.mk (map ↑f (map I^.quotient.mk X)),
    begin
      obtain ⟨p, hp⟩ := X,
      exact comap_map_map_mem_normalized_factors_of_mem_normalized_factors hI hJ f hp,
    end⟩,
  inv_fun := λ X, ⟨comap I^.quotient.mk (map ↑(f.symm) (map J^.quotient.mk X)),
    begin
      obtain ⟨p, hp⟩ := X,
      exact comap_map_map_mem_normalized_factors_of_mem_normalized_factors hJ hI f.symm hp,
    end⟩,
  left_inv := λ X,
    begin
      obtain ⟨p, hp⟩:= X,
      rw [subtype.mk_eq_mk, subtype.coe_mk, subtype.coe_mk, map_comap_of_surjective _
        quotient.mk_surjective, map_of_equiv _ f, comap_map_of_surjective _ quotient.mk_surjective,
        ← ring_hom.ker_eq_comap_bot, mk_ker, sup_of_le_left
        (le_of_dvd (dvd_of_mem_normalized_factors hp))],
    end,
  right_inv := λ X,
    begin
      obtain ⟨p, hp⟩:= X,
      rw [subtype.mk_eq_mk, subtype.coe_mk, subtype.coe_mk, map_comap_of_surjective _
        quotient.mk_surjective],
      nth_rewrite 0 ← ring_equiv.symm_symm f,
      rw [map_of_equiv _ f.symm, comap_map_of_surjective _ quotient.mk_surjective,
        ← ring_hom.ker_eq_comap_bot, mk_ker, sup_of_le_left
        (le_of_dvd (dvd_of_mem_normalized_factors hp))],
    end
}

lemma shifted_seq_pow_constant_iff_ideal_correspondence_shifted_eq_pow_constant (hI : I ≠ ⊥)
  (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient) {p : ideal T} (hp : p ∈ normalized_factors I)
  (n : ℕ) : shifted_seq_pow_constant I p n
  ↔ shifted_seq_pow_constant J ↑(ideal_correspondence hI hJ f ⟨p, hp⟩) n :=
begin
  split,
  { rw [shifted_seq_pow_constant, shifted_seq_pow_constant],
    intros hn m hm,
    specialize hn m hm,
    apply_fun map (f : I.quotient →+* J.quotient) at hn,
    rw [ideal_correspondence_apply_coe, map_comap_of_surjective J^.quotient.mk quotient.mk_surjective,
        subtype.coe_mk, ← map_pow, hn, map_pow] },
  { rw [shifted_seq_pow_constant, shifted_seq_pow_constant],
    intros hn m hm,
    specialize hn m hm,
    rw [ideal_correspondence_apply_coe,
        map_comap_of_surjective J^.quotient.mk quotient.mk_surjective, ← map_pow, ← map_pow _ _ m]
      at hn,
    apply_fun map ↑f.symm at hn,
    rw [map_of_equiv _ f, map_of_equiv _ f] at hn,
    exact hn }
end

lemma irreducible_ideal_correspondence (hI : I ≠ 0) (hJ : J ≠ 0) (f : I.quotient ≃+* J.quotient)
  {p : ideal T} (hp : p ∈ normalized_factors I) :
  irreducible (ideal_correspondence hI hJ f ⟨p, hp⟩ : ideal S) :=
begin
  obtain ⟨q, hq⟩ := ideal_correspondence hI hJ f ⟨p, hp⟩,
  rw subtype.coe_mk,
  exact irreducible_of_normalized_factor q hq,
end


theorem multiplicity_eq_of_quot_equiv (hI : I ≠ 0) (hJ : J ≠ 0) (f : I.quotient ≃+* J.quotient)
  {p : ideal T} (hp : p ∈ normalized_factors I):
  quotient_multiplicity hI (irreducible_of_normalized_factor p hp) =
  quotient_multiplicity hJ (irreducible_ideal_correspondence hI hJ f hp) :=
begin
  apply le_antisymm,
  { rw [quotient_multiplicity, quotient_multiplicity],
    apply nat.find_min',
    rw shifted_seq_pow_constant_iff_ideal_correspondence_shifted_eq_pow_constant hI hJ f hp,
    refine nat.find_spec _ },
  { rw [quotient_multiplicity, quotient_multiplicity],
    apply nat.find_min',
    rw ← shifted_seq_pow_constant_iff_ideal_correspondence_shifted_eq_pow_constant hI hJ f hp,
    refine nat.find_spec _ },
end

end quotient_multiplicity
-/

namespace temporary

section factorisations_same_shape

/-
  Here are the changes I suggest.
  Once were are finished proving these, we would no longer need the whole `quotient_multiplicity`
  part above, which would greatly simplify the PR
-/
noncomputable theory
open_locale classical
variables {T : Type u_1} [integral_domain T] [is_dedekind_domain T] {I : ideal T}
variables {S : Type u_2}  [integral_domain S] [is_dedekind_domain S] {J : ideal S}
open ideal unique_factorization_monoid

@[simps]
def ideal_correspondence (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient):
  {p : ideal T | p ∣ I} ≃ {p : ideal S | p ∣ J} :=
{
  to_fun := λ X, ⟨comap J^.quotient.mk (map ↑f (map I^.quotient.mk X)), sorry⟩,
  inv_fun := λ X, ⟨comap I^.quotient.mk (map ↑(f.symm) (map J^.quotient.mk X)), sorry⟩,
  left_inv := λ X, sorry,
  right_inv := λ X, sorry
}

lemma ideal_correspondence_symm (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient)
  {p : ideal S} (hp : p ∣ J) :
  (ideal_correspondence hI hJ f).symm = ideal_correspondence hJ hI f.symm := rfl

lemma ideal_correspondence_mono (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient)
  {p q : ideal T} (hp : p ∣ I) (hq : q ∣ I) (h : p ≤ q) :
  ↑(ideal_correspondence hI hJ f ⟨p, hp⟩) ≤ ( ideal_correspondence hI hJ f ⟨q, hq⟩ : ideal S) :=
begin
  rw [ideal_correspondence_apply_coe, subtype.coe_mk, ideal_correspondence_apply_coe,
    subtype.coe_mk, comap_le_comap_iff_of_surjective J^.quotient.mk quotient.mk_surjective],
  apply le_map_of_comap_le_of_surjective ↑f,
  rw ring_equiv.coe_to_ring_hom,
  exact ring_equiv.surjective f,
  apply le_map_of_comap_le_of_surjective I^.quotient.mk quotient.mk_surjective,
  rw [map_comap_of_equiv, comap_of_equiv, comap_map_of_surjective I^.quotient.mk quotient.mk_surjective,
    ← ring_hom.ker_eq_comap_bot, mk_ker, sup_eq_left.2 (le_of_dvd hp)],
  exact h,
end

--this is quite simple, just use the two previous statements.
lemma ideal_correspondence_mono' (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient)
  {p q : ideal T} (hp : p ∣ I) (hq : q ∣ I) :
  p ≤ q ↔ ↑(ideal_correspondence hI hJ f ⟨p, hp⟩) ≤ ( ideal_correspondence hI hJ f ⟨q, hq⟩ : ideal S) :=
sorry

--this is quite easy and should be proven in more generality in `unique_factorisation_domain.lean`
lemma temp {p : ideal T} (hp : p ∣ I) : ∃ (b ∈ normalized_factors I), (b : ideal T) ∣ p :=
begin
  sorry
end

lemma ideal_correspondence_is_prime_of_is_prime (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
  (f : I.quotient ≃+* J.quotient) {p : ideal T} (hp : p ∈ normalized_factors I) :
  ↑(ideal_correspondence hI hJ f ⟨p, dvd_of_mem_normalized_factors hp⟩) ∈ normalized_factors J :=
begin
  obtain ⟨b, hb, H⟩ := temp (ideal_correspondence hI hJ f ⟨p, dvd_of_mem_normalized_factors hp⟩).2,
  obtain ⟨c, hc⟩ := equiv.surjective (ideal_correspondence hI hJ f)
    ⟨b, dvd_of_mem_normalized_factors hb⟩,
  obtain ⟨c, hd⟩ := c,
  have : (ideal_correspondence hI hJ f ⟨c, hd⟩ : ideal S) = b,
    rw subtype.coe_eq_iff,
    use dvd_of_mem_normalized_factors hb,
    exact hc,
  rw [dvd_iff_le, ← this, subtype.val_eq_coe, ← ideal_correspondence_mono' hI hJ f
    (dvd_of_mem_normalized_factors hp) hd] at H,
  have pmax : p.is_maximal,
  sorry, --should use a result like is_prime.is_maximal. I've already proven this so I'll add it soon
  suffices H'' : c ≠ ⊤,
  { simp only [is_maximal.eq_of_le pmax H'' H, hb, this] },
  sorry
end

lemma ideal.dvd_is_prime_pow {p q : ideal T} (hp : p.is_prime) {n : ℕ} :
  q ∣ p^n ↔ ∃ i ≤ n, q = p^i :=
sorry

lemma dvd_prime_pow {M : Type*} [comm_cancel_monoid_with_zero M] {p q : M} (hp : prime p) (n : ℕ) :
  q ∣ p^n ↔ ∃ i ≤ n, associated q (p ^ i) :=
begin
  induction n with n ih generalizing q,
  { simp [← is_unit_iff_dvd_one, associated_one_iff_is_unit] },
  split,
  { intro h,
    rw pow_succ at h,
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, rfl⟩ | hno),
    { rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h,
      rcases h with ⟨i, hi, hq⟩,
      { refine ⟨i + 1, nat.succ_le_succ hi, (hq.mul_left p).trans _⟩,
        rw pow_succ } },
    { obtain ⟨i, hi, hq⟩ := ih.mp hno,
      exact ⟨i, hi.trans n.le_succ, hq⟩ } },
  { rintro ⟨i, hi, hq⟩,
    exact hq.dvd.trans (pow_dvd_pow p hi) },
end

-- Can go to `algebra/associated.lean`, line 437.
lemma associates.bot_eq_one {M : Type*} [monoid_with_zero M] :
  (⊥ : associates M) = 1 := rfl

-- To `algebra/associated.lean:690`.
lemma associates.le_one_iff {M : Type*} [comm_cancel_monoid_with_zero M]
  {p : associates M} : p ≤ 1 ↔ p = 1 :=
by rw [← associates.bot_eq_one, le_bot_iff]

lemma pow_prime₁' {M : Type*} [comm_cancel_monoid_with_zero M] {q : associates M} (n : ℕ) (c : ℕ → associates M)
  (h₁ : strict_mono c)
  (h₂ : ∀ {r : associates M}, r ≤ q ↔ ∃ i ≤ n, r = c i) : is_unit (c 0) :=
begin
  obtain ⟨i, hi, hr⟩ := h₂.mp associates.one_le,
  rw [associates.is_unit_iff_eq_one, ← associates.le_one_iff, hr],
  exact h₁.monotone i.zero_le
end

lemma pow_prime₁ {q : ideal T} (n : ℕ) (c : ℕ → ideal T)
  (h₁ : strict_anti c) (h₂ : ∀ {r : ideal T}, r ∣ q ↔ ∃ i ≤ n, r = c i) :
  c 0 = ⊤ :=
begin
  obtain ⟨i, hi, hr⟩ := h₂.mp (one_dvd _),
  rw [eq_top_iff, ← ideal.one_eq_top, hr],
  exact h₁.antitone i.zero_le
end

lemma not_unit_of_dvd_not_unit {M : Type*} [comm_cancel_monoid_with_zero M] {p q : M}
  (hp : dvd_not_unit p q): ¬ is_unit q := sorry

lemma not_prime_of_not_unit_dvd_not_unit {M : Type*} [comm_cancel_monoid_with_zero M] {p q : M}
  (hp : ¬is_unit p)(h : dvd_not_unit p q) : ¬ irreducible q :=
begin
  by_contra hcontra,
  obtain ⟨hp', x, hx, hx'⟩ := h,
  exact hp (or.resolve_right ((irreducible_iff.1 hcontra).right p x hx') hx),
end

lemma pow_prime₂' {M : Type*} [comm_cancel_monoid_with_zero M] {p q : M} (n : ℕ) (c : ℕ → M)
  (h₁ : ∀ i j, i < j → dvd_not_unit (c i) (c j))
  (h₂ : ∀ {r : M}, r ∣ q ↔ ∃ i ≤ n, associated r (c i)) : prime (c 1) :=
begin
  rw prime,
  split,
  { sorry },
  { split,
    { exact not_unit_of_dvd_not_unit (h₁ 0 1 zero_lt_one) },
    { sorry } }, --the last part of the proof seems quite painful in the
                -- `comm_cancel_monoid_with_zero M` setting
end

lemma pow_prime₂ {q : ideal T} (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ideal T)
  (h₁ : strict_anti c) (h₂ : ∀ (r : ideal T), r ∣ q ↔ ∃ i ≤ n, r = c i) :
  (c 1).is_prime :=
begin
  apply is_maximal.is_prime,
  rw [is_maximal_def, is_coatom],
  split,
  { exact ne_top_of_lt (h₁ zero_lt_one) },

  intros b hb,
  have h : b ∣ q := (dvd_iff_le.2 hb.le).trans ((h₂ (c 1)).2 ⟨1, hn, rfl⟩),
  obtain ⟨i, hi, rfl⟩ := (h₂ b).1 h,
  have H : i < 1 := h₁.lt_iff_lt.mp hb,
  rw nat.lt_one_iff.mp H,
  exact pow_prime₁ n c h₁ h₂
end

lemma is_unit_of_associated_is_unit {M : Type*} [comm_cancel_monoid_with_zero M] {p q : M}
  (h : associated p q) (hp : is_unit p): is_unit q :=
by { obtain ⟨a, rfl⟩:= h, exact is_unit.mul hp (units.is_unit a) }

lemma not_associated_of_dvd_not_unit {M : Type*} [comm_cancel_monoid_with_zero M] {p q : M}
  (h : dvd_not_unit p q) : ¬ associated p q :=
begin
  by_contra hcontra,
  rw dvd_not_unit at h,
  obtain ⟨hp, x, hx, hx'⟩ := h,
  apply hx,
  obtain ⟨a, rfl⟩ := hcontra,
  rw mul_eq_mul_left_iff at hx',
  rw ← or.resolve_right hx' hp,
  exact units.is_unit a,
end

lemma dvd_not_unit_of_dvd_not_unit_associated {M : Type*} [comm_cancel_monoid_with_zero M]
  {p q r : M} (h : dvd_not_unit p q) (h' : associated q r) : dvd_not_unit p r :=
  sorry

lemma pow_prime₃' {M : Type*} [comm_cancel_monoid_with_zero M] {p q r : M} (n : ℕ) (hn : 1 ≤ n)
  (c : ℕ → M)  (h₁ : ∀ i j, i < j → dvd_not_unit (c i) (c j))
  (h₂ : ∀ (r : M), r ∣ q ↔ ∃ i ≤ n,  associated r (c i)) (hp : prime p) (hr : r ∣ q)
  (hr' : ¬ is_unit r) (hp' : p ∣ r) : associated p (c 1) :=
begin
  obtain ⟨i, hi, p_eq⟩ := (h₂ p).1 (dvd_trans hp' hr),
  have : 1 ≤ i,
  { rw [nat.succ_le_iff, pos_iff_ne_zero],
    rintro rfl,
    apply prime.not_unit hp,
    apply is_unit_of_associated_is_unit (associated.symm p_eq) (pow_prime₁' n c h₁ h₂),
    sorry, --Lean gives me a weird goal here, should go once `is_unit_of_associated_is_unit` is put in
          -- the right file ?
  },
  by_cases h : 1 = i,             --this part is very messy
  { rw ← h at p_eq,
    exact p_eq },
  { exfalso,
    have : ¬ prime p,
    { by_contra hcontra,
      replace hcontra := prime.irreducible hcontra,
      -- this part is quite messy. A clean-ish way of doing it would be to show that
      -- `i ≥ 1 → ¬ unit (c i)` using induction
      sorry,
    },
    exact this hp },
end

lemma pow_prime₃ {p q r : ideal T} (n : ℕ) (hn : 1 ≤ n) (c : ℕ → ideal T)
  (h₁ : strict_anti c) (h₂ : ∀ (r : ideal T), r ∣ q ↔ ∃ i ≤ n, r = c i)
  (hp : p.is_prime) (hr : r ∣ q) (hr' : r ≠ ⊤) :
  p ∈ normalized_factors r → p = c 1 :=
begin
  intro hp',
  obtain ⟨i, hi, p_eq⟩ := (h₂ p).1 (dvd_trans (dvd_of_mem_normalized_factors hp') hr),
  have : 1 ≤ i,
  { rw [nat.succ_le_iff, pos_iff_ne_zero],
    rintro rfl,
    refine hp.ne_top (p_eq.trans (pow_prime₁ n c h₁ h₂)) },
  rcases this.eq_or_lt with (rfl | h),
  exact p_eq,
  have temp := dvd_not_unit_iff_lt.mpr (h₁ h),
  sorry, --prove not_prime_of_prime_dvd_not_unit
end

lemma pow_prime₄' {M : Type*} [comm_cancel_monoid_with_zero M]
  {p q r : associates M} (n : ℕ) (c : ℕ → associates M)
  (h₁ : strict_mono c) (h₂ : ∀ (r : associates M), r ≤ q ↔ ∃ i ≤ n, r = c i)
  (m : finset (associates M)) (hm : ∀ r, r ∈ m → r ≤ q) : m.card ≤ n + 1 :=
begin
  have sorry_1: ∀ (r : associates M), r ≤ q ↔ r ∈ (finset.range (n+1)).image c,
  { simpa only [finset.mem_image, exists_prop, finset.mem_range, nat.lt_succ_iff, eq_comm]
      using h₂ },
  have sorry_2 : m ⊆ (finset.range (n+1)).image c :=
     λ x hx, (sorry_1 x).mp (hm x hx),
  rw ← finset.card_range (n + 1),
  exact le_trans (finset.card_le_of_subset sorry_2) (finset.card_image_le),
end

lemma pow_prime₄ {p q r : ideal T} (n : ℕ) (c : ℕ → ideal T)
  (h₁ : ∀ i j, i < j → c i > c j) (h₂ : ∀ (r : ideal T), r ∣ q ↔ ∃ i ≤ n, r = c i)
  (m : finset (ideal T)) (hm : ∀ r, r ∈ m → r ∣ q) : m.card ≤ n + 1 :=
begin
  have sorry_1: ∀ (r : ideal T), r ∣ q ↔ r ∈ (finset.range (n+1)).image c,
  { simpa only [finset.mem_image, exists_prop, finset.mem_range, nat.lt_succ_iff, eq_comm]
      using h₂ },
  have sorry_2 : m ⊆ (finset.range (n+1)).image c :=
     λ x hx, (sorry_1 x).mp (hm x hx),
  rw ← finset.card_range (n + 1),
  exact le_trans (finset.card_le_of_subset sorry_2) (finset.card_image_le),
end

lemma pow_prime₅' {M : Type*} [comm_cancel_monoid_with_zero M] {q r : M} (n : ℕ) (c : ℕ → M)
  (h₁ : ∀ i j, i < j → dvd_not_unit (c i) (c j))
  (h₂ : ∀ {r : M}, r ∣ q ↔ ∃ i ≤ n, associated r (c i)) (hr : r ∣ q) :
  ∃ (i ≤ n), associated ((c 1)^n) r :=
begin
  sorry,
end

lemma pow_prime₅ {p q r : ideal T} (n : ℕ) (c : ℕ → ideal T)
  (h₁ : ∀ i j, i < j → c i > c j) (h₂ : ∀ (r : ideal T), r ∣ q ↔ ∃ i, r = c i ∧ i ≤ n)
  (hr : r ∣ q) (hr' : r ≠ ⊤) : ∃ (i : ℕ), r = p^i ∧ i ≤ n :=
begin
  have : ∃ (i : ℕ), normalized_factors r = multiset.repeat q i,
    sorry,
  obtain ⟨i, hi⟩ := this,
  have : i ≤ n, --this should use something like `pow_prime₄`
    sorry,
  sorry,

end

lemma pow_prime {q : ideal T} (n : ℕ) :
(∃ (p : ideal T), p.is_prime ∧ q = p^n) ↔
  (∃ (c : ℕ → ideal T), (∀ i j, i < j → c i > c j) ∧
    ∀ (r : ideal T), r ∣ q ↔  ∃ (i ≤ n), r = c i) :=
begin
  split,
  { intro H,
    obtain ⟨p, hp₁, hp₂⟩ := H,
    use λ i, p^(i : ℕ),
    split,
    { sorry }, --this sorry shouldn't be too hard
    { intro y,
      split,
      { intro hy,
        apply (ideal.dvd_is_prime_pow hp₁).1,
        rw ← hp₂,
        exact hy },
      { intro hy,
        obtain ⟨i, hy', hy''⟩ := hy,
        use p^(n - i : ℕ),
        rw [hy'', pow_mul_pow_sub],
        exact hp₂,
        exact hy' } } },
  sorry, --this part of the proof is a lot harder so I've separated it into a bunch of
         --sub-results as above
end

lemma preserves_multiplicity (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient)
  {p : ideal T} (hp : p ∈ normalized_factors I) : multiplicity p I =
    multiplicity ↑(ideal_correspondence hI hJ f ⟨p, dvd_of_mem_normalized_factors hp⟩) J :=
sorry

def prime_factors_equiv (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient) :
  {p : ideal T | p ∈ normalized_factors I} ≃ {p : ideal S | p ∈ normalized_factors J} :=
{
  to_fun := λ X, ⟨↑(ideal_correspondence hI hJ f ⟨X.1, dvd_of_mem_normalized_factors X.2⟩),
    ideal_correspondence_is_prime_of_is_prime hI hJ f X.2⟩,
  inv_fun := λ X, ⟨↑(ideal_correspondence hJ hI f.symm ⟨X.1, dvd_of_mem_normalized_factors X.2⟩),
    ideal_correspondence_is_prime_of_is_prime hJ hI f.symm X.2⟩,
  left_inv := sorry,   --uses `ideal_correspondence_symm`
  right_inv := sorry   --same
}

end factorisations_same_shape
end temporary
