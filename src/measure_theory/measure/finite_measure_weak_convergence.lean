/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import measure_theory.measure.measure_space
import measure_theory.integral.set_integral
import measure_theory.integral.average
import topology.continuous_function.bounded
import topology.algebra.module.weak_dual
import topology.metric_space.thickened_indicator

/-!
# Weak convergence of (finite) measures

This file defines the topology of weak convergence of finite measures and probability measures
on topological spaces. The topology of weak convergence is the coarsest topology w.r.t. which
for every bounded continuous `ℝ≥0`-valued function `f`, the integration of `f` against the
measure is continuous.

TODOs:
* Include the portmanteau theorem on characterizations of weak convergence of (Borel) probability
  measures.

## Main definitions

The main definitions are the
 * types `measure_theory.finite_measure Ω` and `measure_theory.probability_measure Ω` with
   the topologies of weak convergence;
 * `measure_theory.finite_measure.normalize`, normalizing a finite measure to a probability measure
   (returns junk for the zero measure);
 * `measure_theory.finite_measure.to_weak_dual_bcnn : finite_measure Ω → (weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0))`
   allowing to interpret a finite measure as a continuous linear functional on the space of
   bounded continuous nonnegative functions on `Ω`. This is used for the definition of the
   topology of weak convergence.

## Main results

 * Finite measures `μ` on `Ω` give rise to continuous linear functionals on the space of
   bounded continuous nonnegative functions on `Ω` via integration:
   `measure_theory.finite_measure.to_weak_dual_bcnn : finite_measure Ω → (weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0))`
 * `measure_theory.finite_measure.tendsto_iff_forall_integral_tendsto` and
   `measure_theory.probability_measure.tendsto_iff_forall_integral_tendsto`: Convergence of finite
   measures and probability measures is characterized by the convergence of integrals of all
   bounded continuous functions. This shows that the chosen definition of topology coincides with
   the common textbook definition of weak convergence of measures.
   Similar characterizations by the convergence of integrals (in the `measure_theory.lintegral`
   sense) of all bounded continuous nonnegative functions are
   `measure_theory.finite_measure.tendsto_iff_forall_lintegral_tendsto` and
   `measure_theory.probability_measure.tendsto_iff_forall_lintegral_tendsto`.
 * `measure_theory.finite_measure.tendsto_normalize_iff_tendsto`: The convergence of finite
   measures to a nonzero limit is characterized by the convergence of the probability-normalized
   versions and of the total masses.

TODO:
* Portmanteau theorem:
  * `measure_theory.finite_measure.limsup_measure_closed_le_of_tendsto` proves one implication.
    The current formulation assumes `pseudo_emetric_space`. The only reason is to have
    bounded continuous pointwise approximations to the indicator function of a closed set. Clearly
    for example metrizability or pseudo-emetrizability would be sufficient assumptions. The
    typeclass assumptions should be later adjusted in a way that takes into account use cases, but
    the proof will presumably remain essentially the same.
  * `measure_theory.limsup_measure_closed_le_iff_liminf_measure_open_ge` proves the equivalence of
    the limsup condition for closed sets and the liminf condition for open sets for probability
    measures.
  * `measure_theory.tendsto_measure_of_null_frontier` proves that the liminf condition for open
    sets (which is equivalent to the limsup condition for closed sets) implies the convergence of
    probabilities of sets whose boundary carries no mass under the limit measure.
  * `measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto` is a
    combination of earlier implications, which shows that weak convergence of probability measures
    implies the convergence of probabilities of sets whose boundary carries no mass
    under the limit measure.
  * Prove the rest of the implications.
    (Where formulations are currently only provided for probability measures, one can obtain the
    finite measure formulations using the characterization of convergence of finite measures by
    their total masses and their probability-normalized versions, i.e., by
    `measure_theory.finite_measure.tendsto_normalize_iff_tendsto`.)

## Notations

No new notation is introduced.

## Implementation notes

The topology of weak convergence of finite Borel measures will be defined using a mapping from
`measure_theory.finite_measure Ω` to `weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0)`, inheriting the topology from the
latter.

The current implementation of `measure_theory.finite_measure Ω` and
`measure_theory.probability_measure Ω` is directly as subtypes of `measure_theory.measure Ω`, and
the coercion to a function is the composition `ennreal.to_nnreal` and the coercion to function
of `measure_theory.measure Ω`. Another alternative would be to use a bijection
with `measure_theory.vector_measure Ω ℝ≥0` as an intermediate step. The choice of implementation
should not have drastic downstream effects, so it can be changed later if appropriate.

Potential advantages of using the `nnreal`-valued vector measure alternative:
 * The coercion to function would avoid need to compose with `ennreal.to_nnreal`, the
   `nnreal`-valued API could be more directly available.

Potential drawbacks of the vector measure alternative:
 * The coercion to function would lose monotonicity, as non-measurable sets would be defined to
   have measure 0.
 * No integration theory directly. E.g., the topology definition requires
   `measure_theory.lintegral` w.r.t. a coercion to `measure_theory.measure Ω` in any case.

## References

* [Billingsley, *Convergence of probability measures*][billingsley1999]

## Tags

weak convergence of measures, finite measure, probability measure

-/

noncomputable theory
open measure_theory
open set
open filter
open bounded_continuous_function
open_locale topological_space ennreal nnreal bounded_continuous_function

namespace measure_theory

namespace finite_measure

section finite_measure
/-! ### Finite measures

In this section we define the `Type` of `finite_measure Ω`, when `Ω` is a measurable space. Finite
measures on `Ω` are a module over `ℝ≥0`.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[opens_measurable_space Ω]`), then `finite_measure Ω` is equipped with the topology
of weak convergence of measures. This is implemented by defining a pairing of finite measures `μ`
on `Ω` with continuous bounded nonnegative functions `f : Ω →ᵇ ℝ≥0` via integration, and using the
associated weak topology (essentially the weak-star topology on the dual of `Ω →ᵇ ℝ≥0`).
-/

variables {Ω : Type*} [measurable_space Ω]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def _root_.measure_theory.finite_measure (Ω : Type*) [measurable_space Ω] : Type* :=
{μ : measure Ω // is_finite_measure μ}

/-- A finite measure can be interpreted as a measure. -/
instance : has_coe (finite_measure Ω) (measure_theory.measure Ω) := coe_subtype

instance is_finite_measure (μ : finite_measure Ω) :
  is_finite_measure (μ : measure Ω) := μ.prop

instance : has_coe_to_fun (finite_measure Ω) (λ _, set Ω → ℝ≥0) :=
⟨λ μ s, (μ s).to_nnreal⟩

lemma coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : finite_measure Ω) :
  (ν : set Ω → ℝ≥0) = λ s, ((ν : measure Ω) s).to_nnreal := rfl

@[simp] lemma ennreal_coe_fn_eq_coe_fn_to_measure (ν : finite_measure Ω) (s : set Ω) :
  (ν s : ℝ≥0∞) = (ν : measure Ω) s := ennreal.coe_to_nnreal (measure_lt_top ↑ν s).ne

@[simp] lemma val_eq_to_measure (ν : finite_measure Ω) : ν.val = (ν : measure Ω) := rfl

lemma coe_injective : function.injective (coe : finite_measure Ω → measure Ω) :=
subtype.coe_injective

lemma apply_mono (μ : finite_measure Ω) {s₁ s₂ : set Ω} (h : s₁ ⊆ s₂) :
  μ s₁ ≤ μ s₂ :=
begin
  change ((μ : measure Ω) s₁).to_nnreal ≤ ((μ : measure Ω) s₂).to_nnreal,
  have key : (μ : measure Ω) s₁ ≤ (μ : measure Ω) s₂ := (μ : measure Ω).mono h,
  apply (ennreal.to_nnreal_le_to_nnreal (measure_ne_top _ s₁) (measure_ne_top _ s₂)).mpr key,
end

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`(μ : measure Ω) univ`. -/
def mass (μ : finite_measure Ω) : ℝ≥0 := μ univ

@[simp] lemma ennreal_mass {μ : finite_measure Ω} :
  (μ.mass : ℝ≥0∞) = (μ : measure Ω) univ := ennreal_coe_fn_eq_coe_fn_to_measure μ set.univ

instance has_zero : has_zero (finite_measure Ω) :=
{ zero := ⟨0, measure_theory.is_finite_measure_zero⟩ }

@[simp] lemma zero.mass : (0 : finite_measure Ω).mass = 0 := rfl

@[simp] lemma mass_zero_iff (μ : finite_measure Ω) : μ.mass = 0 ↔ μ = 0 :=
begin
  refine ⟨λ μ_mass, _, (λ hμ, by simp only [hμ, zero.mass])⟩,
  ext1,
  apply measure.measure_univ_eq_zero.mp,
  rwa [← ennreal_mass, ennreal.coe_eq_zero],
end

lemma mass_nonzero_iff (μ : finite_measure Ω) : μ.mass ≠ 0 ↔ μ ≠ 0 :=
begin
  rw not_iff_not,
  exact finite_measure.mass_zero_iff μ,
end

@[ext] lemma extensionality (μ ν : finite_measure Ω)
  (h : ∀ (s : set Ω), measurable_set s → μ s = ν s) :
  μ = ν :=
begin
  ext1, ext1 s s_mble,
  simpa [ennreal_coe_fn_eq_coe_fn_to_measure] using congr_arg (coe : ℝ≥0 → ℝ≥0∞) (h s s_mble),
end

instance : inhabited (finite_measure Ω) := ⟨0⟩

instance : has_add (finite_measure Ω) :=
{ add := λ μ ν, ⟨μ + ν, measure_theory.is_finite_measure_add⟩ }

variables {R : Type*} [has_smul R ℝ≥0] [has_smul R ℝ≥0∞] [is_scalar_tower R ℝ≥0 ℝ≥0∞]
  [is_scalar_tower R ℝ≥0∞ ℝ≥0∞]

instance : has_smul R (finite_measure Ω) :=
{ smul := λ (c : R) μ, ⟨c • μ, measure_theory.is_finite_measure_smul_of_nnreal_tower⟩, }

@[simp, norm_cast] lemma coe_zero : (coe : finite_measure Ω → measure Ω) 0 = 0 := rfl

@[simp, norm_cast] lemma coe_add (μ ν : finite_measure Ω) : ↑(μ + ν) = (↑μ + ↑ν : measure Ω) := rfl

@[simp, norm_cast] lemma coe_smul (c : R) (μ : finite_measure Ω) :
  ↑(c • μ) = (c • ↑μ : measure Ω) := rfl

@[simp, norm_cast] lemma coe_fn_zero :
  (⇑(0 : finite_measure Ω) : set Ω → ℝ≥0) = (0 : set Ω → ℝ≥0) := by { funext, refl, }

@[simp, norm_cast] lemma coe_fn_add (μ ν : finite_measure Ω) :
  (⇑(μ + ν) : set Ω → ℝ≥0) = (⇑μ + ⇑ν : set Ω → ℝ≥0) :=
by { funext, simp [← ennreal.coe_eq_coe], }

@[simp, norm_cast] lemma coe_fn_smul [is_scalar_tower R ℝ≥0 ℝ≥0] (c : R) (μ : finite_measure Ω) :
  (⇑(c • μ) : set Ω → ℝ≥0) = c • (⇑μ : set Ω → ℝ≥0) :=
by { funext, simp [← ennreal.coe_eq_coe, ennreal.coe_smul], }

instance : add_comm_monoid (finite_measure Ω) :=
coe_injective.add_comm_monoid coe coe_zero coe_add (λ _ _, coe_smul _ _)

/-- Coercion is an `add_monoid_hom`. -/
@[simps]
def coe_add_monoid_hom : finite_measure Ω →+ measure Ω :=
{ to_fun := coe, map_zero' := coe_zero, map_add' := coe_add }

instance {Ω : Type*} [measurable_space Ω] : module ℝ≥0 (finite_measure Ω) :=
function.injective.module _ coe_add_monoid_hom coe_injective coe_smul

@[simp] lemma coe_fn_smul_apply [is_scalar_tower R ℝ≥0 ℝ≥0]
  (c : R) (μ : finite_measure Ω) (s : set Ω) :
  (c • μ) s  = c • (μ s) :=
by { simp only [coe_fn_smul, pi.smul_apply], }

/-- Restrict a finite measure μ to a set A. -/
def restrict (μ : finite_measure Ω) (A : set Ω) : finite_measure Ω :=
{ val := (μ : measure Ω).restrict A,
  property := measure_theory.is_finite_measure_restrict μ A, }

lemma restrict_measure_eq (μ : finite_measure Ω) (A : set Ω) :
  (μ.restrict A : measure Ω) = (μ : measure Ω).restrict A := rfl

lemma restrict_apply_measure (μ : finite_measure Ω) (A : set Ω)
  {s : set Ω} (s_mble : measurable_set s) :
  (μ.restrict A : measure Ω) s = (μ : measure Ω) (s ∩ A) :=
measure.restrict_apply s_mble

lemma restrict_apply (μ : finite_measure Ω) (A : set Ω)
  {s : set Ω} (s_mble : measurable_set s) :
  (μ.restrict A) s = μ (s ∩ A) :=
begin
  apply congr_arg ennreal.to_nnreal,
  exact measure.restrict_apply s_mble,
end

lemma restrict_mass (μ : finite_measure Ω) (A : set Ω) :
  (μ.restrict A).mass = μ A :=
by simp only [mass, restrict_apply μ A measurable_set.univ, univ_inter]

lemma restrict_eq_zero_iff (μ : finite_measure Ω) (A : set Ω) :
  μ.restrict A = 0 ↔ μ A = 0 :=
by rw [← mass_zero_iff, restrict_mass]

lemma restrict_nonzero_iff (μ : finite_measure Ω) (A : set Ω) :
  μ.restrict A ≠ 0 ↔ μ A ≠ 0 :=
by rw [← mass_nonzero_iff, restrict_mass]

variables [topological_space Ω]

/-- The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure.
This is `finite_measure.test_against_nn`. -/
def test_against_nn (μ : finite_measure Ω) (f : Ω →ᵇ ℝ≥0) : ℝ≥0 :=
(∫⁻ ω, f ω ∂(μ : measure Ω)).to_nnreal

lemma _root_.bounded_continuous_function.nnreal.to_ennreal_comp_measurable {Ω : Type*}
  [topological_space Ω] [measurable_space Ω] [opens_measurable_space Ω] (f : Ω →ᵇ ℝ≥0) :
  measurable (λ ω, (f ω : ℝ≥0∞)) :=
measurable_coe_nnreal_ennreal.comp f.continuous.measurable

lemma _root_.measure_theory.lintegral_lt_top_of_bounded_continuous_to_nnreal
  (μ : measure Ω) [is_finite_measure μ] (f : Ω →ᵇ ℝ≥0) :
  ∫⁻ ω, f ω ∂μ < ∞ :=
begin
  apply is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal,
  use nndist f 0,
  intros x,
  have key := bounded_continuous_function.nnreal.upper_bound f x,
  rw ennreal.coe_le_coe,
  have eq : nndist f 0 = ⟨dist f 0, dist_nonneg⟩,
  { ext,
    simp only [real.coe_to_nnreal', max_eq_left_iff, subtype.coe_mk, coe_nndist], },
  rwa eq at key,
end

@[simp] lemma test_against_nn_coe_eq {μ : finite_measure Ω} {f : Ω →ᵇ ℝ≥0} :
  (μ.test_against_nn f : ℝ≥0∞) = ∫⁻ ω, f ω ∂(μ : measure Ω) :=
ennreal.coe_to_nnreal (lintegral_lt_top_of_bounded_continuous_to_nnreal _ f).ne

lemma test_against_nn_const (μ : finite_measure Ω) (c : ℝ≥0) :
  μ.test_against_nn (bounded_continuous_function.const Ω c) = c * μ.mass :=
by simp [← ennreal.coe_eq_coe]

lemma test_against_nn_mono (μ : finite_measure Ω)
  {f g : Ω →ᵇ ℝ≥0} (f_le_g : (f : Ω → ℝ≥0) ≤ g) :
  μ.test_against_nn f ≤ μ.test_against_nn g :=
begin
  simp only [←ennreal.coe_le_coe, test_against_nn_coe_eq],
  exact lintegral_mono (λ ω, ennreal.coe_mono (f_le_g ω)),
end

@[simp] lemma test_against_nn_zero (μ : finite_measure Ω) : μ.test_against_nn 0 = 0 :=
by simpa only [zero_mul] using μ.test_against_nn_const 0

@[simp] lemma test_against_nn_one (μ : finite_measure Ω) : μ.test_against_nn 1 = μ.mass :=
begin
  simp only [test_against_nn, coe_one, pi.one_apply, ennreal.coe_one, lintegral_one],
  refl,
end

@[simp] lemma zero.test_against_nn_apply (f : Ω →ᵇ ℝ≥0) :
  (0 : finite_measure Ω).test_against_nn f = 0 :=
by simp only [test_against_nn, coe_zero, lintegral_zero_measure, ennreal.zero_to_nnreal]

lemma zero.test_against_nn : (0 : finite_measure Ω).test_against_nn = 0 :=
by { funext, simp only [zero.test_against_nn_apply, pi.zero_apply], }

@[simp] lemma smul_test_against_nn_apply (c : ℝ≥0) (μ : finite_measure Ω) (f : Ω →ᵇ ℝ≥0) :
  (c • μ).test_against_nn f  = c • (μ.test_against_nn f) :=
by simp only [test_against_nn, coe_smul, smul_eq_mul, ← ennreal.smul_to_nnreal,
  ennreal.smul_def, lintegral_smul_measure]

variables [opens_measurable_space Ω]

lemma test_against_nn_add (μ : finite_measure Ω) (f₁ f₂ : Ω →ᵇ ℝ≥0) :
  μ.test_against_nn (f₁ + f₂) = μ.test_against_nn f₁ + μ.test_against_nn f₂ :=
begin
  simp only [←ennreal.coe_eq_coe, bounded_continuous_function.coe_add, ennreal.coe_add,
             pi.add_apply, test_against_nn_coe_eq],
  exact lintegral_add_left (bounded_continuous_function.nnreal.to_ennreal_comp_measurable _) _
end

lemma test_against_nn_smul [is_scalar_tower R ℝ≥0 ℝ≥0] [pseudo_metric_space R] [has_zero R]
  [has_bounded_smul R ℝ≥0]
  (μ : finite_measure Ω) (c : R) (f : Ω →ᵇ ℝ≥0) :
  μ.test_against_nn (c • f) = c • μ.test_against_nn f :=
begin
  simp only [←ennreal.coe_eq_coe, bounded_continuous_function.coe_smul,
             test_against_nn_coe_eq, ennreal.coe_smul],
  simp_rw [←smul_one_smul ℝ≥0∞ c (f _ : ℝ≥0∞), ←smul_one_smul ℝ≥0∞ c (lintegral _ _ : ℝ≥0∞),
           smul_eq_mul],
  exact @lintegral_const_mul _ _ (μ : measure Ω) (c • 1)  _
                   (bounded_continuous_function.nnreal.to_ennreal_comp_measurable f),
end

lemma test_against_nn_lipschitz_estimate (μ : finite_measure Ω) (f g : Ω →ᵇ ℝ≥0) :
  μ.test_against_nn f ≤ μ.test_against_nn g + (nndist f g) * μ.mass :=
begin
  simp only [←μ.test_against_nn_const (nndist f g), ←test_against_nn_add, ←ennreal.coe_le_coe,
             bounded_continuous_function.coe_add, const_apply, ennreal.coe_add, pi.add_apply,
             coe_nnreal_ennreal_nndist, test_against_nn_coe_eq],
  apply lintegral_mono,
  have le_dist : ∀ ω, dist (f ω) (g ω) ≤ nndist f g :=
  bounded_continuous_function.dist_coe_le_dist,
  intros ω,
  have le' : f ω ≤ g ω + nndist f g,
  { apply (nnreal.le_add_nndist (f ω) (g ω)).trans,
    rw add_le_add_iff_left,
    exact dist_le_coe.mp (le_dist ω), },
  have le : (f ω : ℝ≥0∞) ≤ (g ω : ℝ≥0∞) + (nndist f g),
  by { rw ←ennreal.coe_add, exact ennreal.coe_mono le', },
  rwa [coe_nnreal_ennreal_nndist] at le,
end

lemma test_against_nn_lipschitz (μ : finite_measure Ω) :
  lipschitz_with μ.mass (λ (f : Ω →ᵇ ℝ≥0), μ.test_against_nn f) :=
begin
  rw lipschitz_with_iff_dist_le_mul,
  intros f₁ f₂,
  suffices : abs (μ.test_against_nn f₁ - μ.test_against_nn f₂ : ℝ) ≤ μ.mass * (dist f₁ f₂),
  { rwa nnreal.dist_eq, },
  apply abs_le.mpr,
  split,
  { have key' := μ.test_against_nn_lipschitz_estimate f₂ f₁,
    rw mul_comm at key',
    suffices : ↑(μ.test_against_nn f₂) ≤ ↑(μ.test_against_nn f₁) + ↑(μ.mass) * dist f₁ f₂,
    { linarith, },
    have key := nnreal.coe_mono key',
    rwa [nnreal.coe_add, nnreal.coe_mul, nndist_comm] at key, },
  { have key' := μ.test_against_nn_lipschitz_estimate f₁ f₂,
    rw mul_comm at key',
    suffices : ↑(μ.test_against_nn f₁) ≤ ↑(μ.test_against_nn f₂) + ↑(μ.mass) * dist f₁ f₂,
    { linarith, },
    have key := nnreal.coe_mono key',
    rwa [nnreal.coe_add, nnreal.coe_mul] at key, },
end

/-- Finite measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `measure_theory.finite_measure.test_against_nn`, i.e., integration. -/
def to_weak_dual_bcnn (μ : finite_measure Ω) :
  weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0) :=
{ to_fun := λ f, μ.test_against_nn f,
  map_add' := test_against_nn_add μ,
  map_smul' := test_against_nn_smul μ,
  cont := μ.test_against_nn_lipschitz.continuous, }

@[simp] lemma coe_to_weak_dual_bcnn (μ : finite_measure Ω) :
  ⇑μ.to_weak_dual_bcnn = μ.test_against_nn := rfl

@[simp] lemma to_weak_dual_bcnn_apply (μ : finite_measure Ω) (f : Ω →ᵇ ℝ≥0) :
  μ.to_weak_dual_bcnn f = (∫⁻ x, f x ∂(μ : measure Ω)).to_nnreal := rfl

/-- The topology of weak convergence on `measure_theory.finite_measure Ω` is inherited (induced)
from the weak-* topology on `weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0)` via the function
`measure_theory.finite_measure.to_weak_dual_bcnn`. -/
instance : topological_space (finite_measure Ω) :=
topological_space.induced to_weak_dual_bcnn infer_instance

lemma to_weak_dual_bcnn_continuous :
  continuous (@to_weak_dual_bcnn Ω _ _ _) :=
continuous_induced_dom

/- Integration of (nonnegative bounded continuous) test functions against finite Borel measures
depends continuously on the measure. -/
lemma continuous_test_against_nn_eval (f : Ω →ᵇ ℝ≥0) :
  continuous (λ (μ : finite_measure Ω), μ.test_against_nn f) :=
(by apply (weak_bilin.eval_continuous _ _).comp to_weak_dual_bcnn_continuous :
  continuous ((λ φ : weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0), φ f) ∘ to_weak_dual_bcnn))

/-- The total mass of a finite measure depends continuously on the measure. -/
lemma continuous_mass : continuous (λ (μ : finite_measure Ω), μ.mass) :=
by { simp_rw ←test_against_nn_one, exact continuous_test_against_nn_eval 1, }

/-- Convergence of finite measures implies the convergence of their total masses. -/
lemma _root_.filter.tendsto.mass {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} {μ : finite_measure Ω} (h : tendsto μs F (𝓝 μ)) :
  tendsto (λ i, (μs i).mass) F (𝓝 μ.mass) :=
(continuous_mass.tendsto μ).comp h

lemma tendsto_iff_weak_star_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔ tendsto (λ i, (μs(i)).to_weak_dual_bcnn) F (𝓝 μ.to_weak_dual_bcnn) :=
inducing.tendsto_nhds_iff ⟨rfl⟩

theorem tendsto_iff_forall_to_weak_dual_bcnn_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ≥0), tendsto (λ i, (μs i).to_weak_dual_bcnn f) F (𝓝 (μ.to_weak_dual_bcnn f)) :=
by { rw [tendsto_iff_weak_star_tendsto, tendsto_iff_forall_eval_tendsto_top_dual_pairing], refl, }

theorem tendsto_iff_forall_test_against_nn_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ≥0), tendsto (λ i, (μs i).test_against_nn f) F (𝓝 (μ.test_against_nn f)) :=
by { rw finite_measure.tendsto_iff_forall_to_weak_dual_bcnn_tendsto, refl, }

/-- If the total masses of finite measures tend to zero, then the measures tend to
zero. This formulation concerns the associated functionals on bounded continuous
nonnegative test functions. See `finite_measure.tendsto_zero_of_tendsto_zero_mass` for
a formulation stating the weak convergence of measures. -/
lemma tendsto_zero_test_against_nn_of_tendsto_zero_mass
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω}
  (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 0)) (f : Ω →ᵇ ℝ≥0) :
  tendsto (λ i, (μs i).test_against_nn f) F (𝓝 0) :=
begin
  apply tendsto_iff_dist_tendsto_zero.mpr,
  have obs := λ i, (μs i).test_against_nn_lipschitz_estimate f 0,
  simp_rw [test_against_nn_zero, zero_add] at obs,
  simp_rw (show ∀ i, dist ((μs i).test_against_nn f) 0 = (μs i).test_against_nn f,
    by simp only [dist_nndist, nnreal.nndist_zero_eq_val', eq_self_iff_true,
                  implies_true_iff]),
  refine squeeze_zero (λ i, nnreal.coe_nonneg _) obs _,
  simp_rw nnreal.coe_mul,
  have lim_pair : tendsto (λ i, (⟨nndist f 0, (μs i).mass⟩ : ℝ × ℝ)) F (𝓝 (⟨nndist f 0, 0⟩)),
  { refine (prod.tendsto_iff _ _).mpr ⟨tendsto_const_nhds, _⟩,
    exact (nnreal.continuous_coe.tendsto 0).comp mass_lim, },
  have key := tendsto_mul.comp lim_pair,
  rwa mul_zero at key,
end

/-- If the total masses of finite measures tend to zero, then the measures tend to zero. -/
lemma tendsto_zero_of_tendsto_zero_mass {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 0)) :
  tendsto μs F (𝓝 0) :=
begin
  rw tendsto_iff_forall_test_against_nn_tendsto,
  intro f,
  convert tendsto_zero_test_against_nn_of_tendsto_zero_mass mass_lim f,
  rw [zero.test_against_nn_apply],
end

/-- A characterization of weak convergence in terms of integrals of bounded continuous
nonnegative functions. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ≥0),
    tendsto (λ i, (∫⁻ x, (f x) ∂(μs(i) : measure Ω))) F (𝓝 ((∫⁻ x, (f x) ∂(μ : measure Ω)))) :=
begin
  rw tendsto_iff_forall_to_weak_dual_bcnn_tendsto,
  simp_rw [to_weak_dual_bcnn_apply _ _, ←test_against_nn_coe_eq,
           ennreal.tendsto_coe, ennreal.to_nnreal_coe],
end

end finite_measure -- section

section finite_measure_bounded_convergence
/-! ### Bounded convergence results for finite measures

This section is about bounded convergence theorems for finite measures.
-/

variables {Ω : Type*} [measurable_space Ω] [topological_space Ω] [opens_measurable_space Ω]

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is `measure_theory.lintegral`, i.e., the functions and their integrals are
   `ℝ≥0∞`-valued.
-/
lemma tendsto_lintegral_nn_filter_of_le_const {ι : Type*} {L : filter ι} [L.is_countably_generated]
  (μ : measure Ω) [is_finite_measure μ] {fs : ι → (Ω →ᵇ ℝ≥0)} {c : ℝ≥0}
  (fs_le_const : ∀ᶠ i in L, ∀ᵐ (ω : Ω) ∂μ, fs i ω ≤ c) {f : Ω → ℝ≥0}
  (fs_lim : ∀ᵐ (ω : Ω) ∂μ, tendsto (λ i, fs i ω) L (𝓝 (f ω))) :
  tendsto (λ i, (∫⁻ ω, fs i ω ∂μ)) L (𝓝 (∫⁻ ω, (f ω) ∂μ)) :=
begin
  simpa only using tendsto_lintegral_filter_of_dominated_convergence (λ _, c)
    (eventually_of_forall ((λ i, (ennreal.continuous_coe.comp (fs i).continuous).measurable)))
    _ ((@lintegral_const_lt_top _ _ μ _ _ (@ennreal.coe_ne_top c)).ne) _,
  { simpa only [ennreal.coe_le_coe] using fs_le_const, },
  { simpa only [ennreal.tendsto_coe] using fs_lim, },
end

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant
and tend pointwise to a limit, then their integrals (`measure_theory.lintegral`) against the finite
measure tend to the integral of the limit.

A related result with more general assumptions is
`measure_theory.finite_measure.tendsto_lintegral_nn_filter_of_le_const`.
-/
lemma tendsto_lintegral_nn_of_le_const (μ : finite_measure Ω) {fs : ℕ → (Ω →ᵇ ℝ≥0)} {c : ℝ≥0}
  (fs_le_const : ∀ n ω, fs n ω ≤ c) {f : Ω → ℝ≥0}
  (fs_lim : ∀ ω, tendsto (λ n, fs n ω) at_top (𝓝 (f ω))) :
  tendsto (λ n, (∫⁻ ω, fs n ω ∂(μ : measure Ω))) at_top (𝓝 (∫⁻ ω, (f ω) ∂(μ : measure Ω))) :=
tendsto_lintegral_nn_filter_of_le_const μ
  (eventually_of_forall (λ n, eventually_of_forall (fs_le_const n))) (eventually_of_forall fs_lim)

/-- A bounded convergence theorem for a finite measure:
If bounded continuous non-negative functions are uniformly bounded by a constant and tend to a
limit, then their integrals against the finite measure tend to the integral of the limit.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere;
 * integration is the pairing against non-negative continuous test functions
   (`measure_theory.finite_measure.test_against_nn`).

A related result using `measure_theory.lintegral` for integration is
`measure_theory.finite_measure.tendsto_lintegral_nn_filter_of_le_const`.
-/
lemma tendsto_test_against_nn_filter_of_le_const {ι : Type*} {L : filter ι}
  [L.is_countably_generated] {μ : finite_measure Ω} {fs : ι → (Ω →ᵇ ℝ≥0)} {c : ℝ≥0}
  (fs_le_const : ∀ᶠ i in L, ∀ᵐ (ω : Ω) ∂(μ : measure Ω), fs i ω ≤ c) {f : Ω →ᵇ ℝ≥0}
  (fs_lim : ∀ᵐ (ω : Ω) ∂(μ : measure Ω), tendsto (λ i, fs i ω) L (𝓝 (f ω))) :
  tendsto (λ i, μ.test_against_nn (fs i)) L (𝓝 (μ.test_against_nn f)) :=
begin
  apply (ennreal.tendsto_to_nnreal
         (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) f).ne).comp,
  exact tendsto_lintegral_nn_filter_of_le_const μ fs_le_const fs_lim,
end

/-- A bounded convergence theorem for a finite measure:
If a sequence of bounded continuous non-negative functions are uniformly bounded by a constant and
tend pointwise to a limit, then their integrals (`measure_theory.finite_measure.test_against_nn`)
against the finite measure tend to the integral of the limit.

Related results:
 * `measure_theory.finite_measure.tendsto_test_against_nn_filter_of_le_const`:
   more general assumptions
 * `measure_theory.finite_measure.tendsto_lintegral_nn_of_le_const`:
   using `measure_theory.lintegral` for integration.
-/
lemma tendsto_test_against_nn_of_le_const {μ : finite_measure Ω}
  {fs : ℕ → (Ω →ᵇ ℝ≥0)} {c : ℝ≥0} (fs_le_const : ∀ n ω, fs n ω ≤ c) {f : Ω →ᵇ ℝ≥0}
  (fs_lim : ∀ ω, tendsto (λ n, fs n ω) at_top (𝓝 (f ω))) :
  tendsto (λ n, μ.test_against_nn (fs n)) at_top (𝓝 (μ.test_against_nn f)) :=
tendsto_test_against_nn_filter_of_le_const
  (eventually_of_forall (λ n, eventually_of_forall (fs_le_const n))) (eventually_of_forall fs_lim)

end finite_measure_bounded_convergence -- section

section finite_measure_convergence_by_bounded_continuous_functions
/-! ### Weak convergence of finite measures with bounded continuous real-valued functions

In this section we characterize the weak convergence of finite measures by the usual (defining)
condition that the integrals of all bounded continuous real-valued functions converge.
-/

variables {Ω : Type*} [measurable_space Ω] [topological_space Ω] [opens_measurable_space Ω]

lemma integrable_of_bounded_continuous_to_nnreal
  (μ : measure Ω) [is_finite_measure μ] (f : Ω →ᵇ ℝ≥0) :
  integrable ((coe : ℝ≥0 → ℝ) ∘ ⇑f) μ :=
begin
  refine ⟨(nnreal.continuous_coe.comp f.continuous).measurable.ae_strongly_measurable, _⟩,
  simp only [has_finite_integral, nnreal.nnnorm_eq],
  exact lintegral_lt_top_of_bounded_continuous_to_nnreal _ f,
end

lemma integrable_of_bounded_continuous_to_real
  (μ : measure Ω) [is_finite_measure μ] (f : Ω →ᵇ ℝ) :
  integrable ⇑f μ :=
begin
  refine ⟨f.continuous.measurable.ae_strongly_measurable, _⟩,
  have aux : (coe : ℝ≥0 → ℝ) ∘ ⇑f.nnnorm = (λ x, ∥f x∥),
  { ext ω,
    simp only [function.comp_app, bounded_continuous_function.nnnorm_coe_fun_eq, coe_nnnorm], },
  apply (has_finite_integral_iff_norm ⇑f).mpr,
  rw ← of_real_integral_eq_lintegral_of_real,
  { exact ennreal.of_real_lt_top, },
  { exact aux ▸ integrable_of_bounded_continuous_to_nnreal μ f.nnnorm, },
  { exact eventually_of_forall (λ ω, norm_nonneg (f ω)), },
end

lemma _root_.bounded_continuous_function.integral_eq_integral_nnreal_part_sub
  (μ : measure Ω) [is_finite_measure μ] (f : Ω →ᵇ ℝ) :
  ∫ ω, f ω ∂μ = ∫ ω, f.nnreal_part ω ∂μ - ∫ ω, (-f).nnreal_part ω ∂μ :=
by simp only [f.self_eq_nnreal_part_sub_nnreal_part_neg,
              pi.sub_apply, integral_sub, integrable_of_bounded_continuous_to_nnreal]

lemma lintegral_lt_top_of_bounded_continuous_to_real
  {Ω : Type*} [measurable_space Ω] [topological_space Ω] (μ : measure Ω) [is_finite_measure μ]
  (f : Ω →ᵇ ℝ) :
  ∫⁻ ω, ennreal.of_real (f ω) ∂μ < ∞ :=
lintegral_lt_top_of_bounded_continuous_to_nnreal _ f.nnreal_part

theorem tendsto_of_forall_integral_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω} {μ : finite_measure Ω}
  (h : (∀ (f : Ω →ᵇ ℝ),
       tendsto (λ i, (∫ x, (f x) ∂(μs i : measure Ω))) F (𝓝 ((∫ x, (f x) ∂(μ : measure Ω)))))) :
  tendsto μs F (𝓝 μ) :=
begin
  apply (@tendsto_iff_forall_lintegral_tendsto Ω _ _ _ γ F μs μ).mpr,
  intro f,
  have key := @ennreal.tendsto_to_real_iff _ F
              _ (λ i, (lintegral_lt_top_of_bounded_continuous_to_nnreal (μs i : measure Ω) f).ne)
              _ (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) f).ne,
  simp only [ennreal.of_real_coe_nnreal] at key,
  apply key.mp,
  have lip : lipschitz_with 1 (coe : ℝ≥0 → ℝ), from isometry_subtype_coe.lipschitz,
  set f₀ := bounded_continuous_function.comp _ lip f with def_f₀,
  have f₀_eq : ⇑f₀ = (coe : ℝ≥0 → ℝ) ∘ ⇑f, by refl,
  have f₀_nn : 0 ≤ ⇑f₀, from λ _, by simp only [f₀_eq, pi.zero_apply, nnreal.zero_le_coe],
  have f₀_ae_nn : 0 ≤ᵐ[(μ : measure Ω)] ⇑f₀, from eventually_of_forall f₀_nn,
  have f₀_ae_nns : ∀ i, 0 ≤ᵐ[(μs i : measure Ω)] ⇑f₀, from λ i, eventually_of_forall f₀_nn,
  have aux := integral_eq_lintegral_of_nonneg_ae f₀_ae_nn
              f₀.continuous.measurable.ae_strongly_measurable,
  have auxs := λ i, integral_eq_lintegral_of_nonneg_ae (f₀_ae_nns i)
              f₀.continuous.measurable.ae_strongly_measurable,
  simp only [f₀_eq, ennreal.of_real_coe_nnreal] at aux auxs,
  simpa only [←aux, ←auxs] using h f₀,
end

lemma _root_.bounded_continuous_function.nnreal.to_real_lintegral_eq_integral
  (f : Ω →ᵇ ℝ≥0) (μ : measure Ω) :
  (∫⁻ x, (f x : ℝ≥0∞) ∂μ).to_real = (∫ x, f x ∂μ) :=
begin
  rw integral_eq_lintegral_of_nonneg_ae _
     (nnreal.continuous_coe.comp f.continuous).measurable.ae_strongly_measurable,
  { simp only [ennreal.of_real_coe_nnreal], },
  { apply eventually_of_forall,
    simp only [pi.zero_apply, nnreal.zero_le_coe, implies_true_iff], },
end

/-- A characterization of weak convergence in terms of integrals of bounded continuous
real-valued functions. -/
theorem tendsto_iff_forall_integral_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω} {μ : finite_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ),
    tendsto (λ i, (∫ x, (f x) ∂(μs i : measure Ω))) F (𝓝 ((∫ x, (f x) ∂(μ : measure Ω)))) :=
begin
  refine ⟨_, tendsto_of_forall_integral_tendsto⟩,
  rw tendsto_iff_forall_lintegral_tendsto,
  intros h f,
  simp_rw bounded_continuous_function.integral_eq_integral_nnreal_part_sub,
  set f_pos := f.nnreal_part with def_f_pos,
  set f_neg := (-f).nnreal_part with def_f_neg,
  have tends_pos := (ennreal.tendsto_to_real
    ((lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) f_pos).ne)).comp (h f_pos),
  have tends_neg := (ennreal.tendsto_to_real
    ((lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) f_neg).ne)).comp (h f_neg),
  have aux : ∀ (g : Ω →ᵇ ℝ≥0), ennreal.to_real ∘ (λ (i : γ), ∫⁻ (x : Ω), ↑(g x) ∂(μs i : measure Ω))
         = λ (i : γ), (∫⁻ (x : Ω), ↑(g x) ∂(μs i : measure Ω)).to_real, from λ _, rfl,
  simp_rw [aux, bounded_continuous_function.nnreal.to_real_lintegral_eq_integral]
          at tends_pos tends_neg,
  exact tendsto.sub tends_pos tends_neg,
end

end finite_measure_convergence_by_bounded_continuous_functions -- section

end finite_measure -- namespace

section probability_measure
/-! ### Probability measures

In this section we define the type of probability measures on a measurable space `Ω`, denoted by
`measure_theory.probability_measure Ω`. TODO: Probability measures form a convex space.

If `Ω` is moreover a topological space and the sigma algebra on `Ω` is finer than the Borel sigma
algebra (i.e. `[opens_measurable_space Ω]`), then `measure_theory.probability_measure Ω` is
equipped with the topology of weak convergence of measures. Since every probability measure is a
finite measure, this is implemented as the induced topology from the coercion
`measure_theory.probability_measure.to_finite_measure`.
-/

/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def probability_measure (Ω : Type*) [measurable_space Ω] : Type* :=
{μ : measure Ω // is_probability_measure μ}

namespace probability_measure

variables {Ω : Type*} [measurable_space Ω]

instance [inhabited Ω] : inhabited (probability_measure Ω) :=
⟨⟨measure.dirac default, measure.dirac.is_probability_measure⟩⟩

/-- A probability measure can be interpreted as a measure. -/
instance : has_coe (probability_measure Ω) (measure_theory.measure Ω) := coe_subtype

instance : has_coe_to_fun (probability_measure Ω) (λ _, set Ω → ℝ≥0) :=
⟨λ μ s, (μ s).to_nnreal⟩

instance (μ : probability_measure Ω) : is_probability_measure (μ : measure Ω) := μ.prop

lemma coe_fn_eq_to_nnreal_coe_fn_to_measure (ν : probability_measure Ω) :
  (ν : set Ω → ℝ≥0) = λ s, ((ν : measure Ω) s).to_nnreal := rfl

@[simp] lemma val_eq_to_measure (ν : probability_measure Ω) : ν.val = (ν : measure Ω) := rfl

lemma coe_injective : function.injective (coe : probability_measure Ω → measure Ω) :=
subtype.coe_injective

@[simp] lemma coe_fn_univ (ν : probability_measure Ω) : ν univ = 1 :=
congr_arg ennreal.to_nnreal ν.prop.measure_univ

/-- A probability measure can be interpreted as a finite measure. -/
def to_finite_measure (μ : probability_measure Ω) : finite_measure Ω := ⟨μ, infer_instance⟩

@[simp] lemma coe_comp_to_finite_measure_eq_coe (ν : probability_measure Ω) :
  (ν.to_finite_measure : measure Ω) = (ν : measure Ω) := rfl

@[simp] lemma coe_fn_comp_to_finite_measure_eq_coe_fn (ν : probability_measure Ω) :
  (ν.to_finite_measure : set Ω → ℝ≥0) = (ν : set Ω → ℝ≥0) := rfl

@[simp] lemma ennreal_coe_fn_eq_coe_fn_to_measure (ν : probability_measure Ω) (s : set Ω) :
  (ν s : ℝ≥0∞) = (ν : measure Ω) s :=
by rw [← coe_fn_comp_to_finite_measure_eq_coe_fn,
  finite_measure.ennreal_coe_fn_eq_coe_fn_to_measure, coe_comp_to_finite_measure_eq_coe]

lemma apply_mono (P : probability_measure Ω) {s₁ s₂ : set Ω} (h : s₁ ⊆ s₂) :
  P s₁ ≤ P s₂ :=
begin
  rw ← coe_fn_comp_to_finite_measure_eq_coe_fn,
  exact measure_theory.finite_measure.apply_mono _ h,
end

lemma nonempty_of_probability_measure (P : probability_measure Ω) : nonempty Ω :=
begin
  by_contra maybe_empty,
  have zero : (P : measure Ω) univ = 0,
    by rw [univ_eq_empty_iff.mpr (not_nonempty_iff.mp maybe_empty), measure_empty],
  rw measure_univ at zero,
  exact zero_ne_one zero.symm,
end

@[ext] lemma extensionality (μ ν : probability_measure Ω)
  (h : ∀ (s : set Ω), measurable_set s → μ s = ν s) :
  μ = ν :=
begin
  ext1, ext1 s s_mble,
  simpa [ennreal_coe_fn_eq_coe_fn_to_measure] using congr_arg (coe : ℝ≥0 → ℝ≥0∞) (h s s_mble),
end

@[simp] lemma mass_to_finite_measure (μ : probability_measure Ω) :
  μ.to_finite_measure.mass = 1 := μ.coe_fn_univ

lemma to_finite_measure_nonzero (μ : probability_measure Ω) :
  μ.to_finite_measure ≠ 0 :=
begin
  intro maybe_zero,
  have mass_zero := (finite_measure.mass_zero_iff _).mpr maybe_zero,
  rw μ.mass_to_finite_measure at mass_zero,
  exact one_ne_zero mass_zero,
end

variables [topological_space Ω] [opens_measurable_space Ω]

lemma test_against_nn_lipschitz (μ : probability_measure Ω) :
  lipschitz_with 1 (λ (f : Ω →ᵇ ℝ≥0), μ.to_finite_measure.test_against_nn f) :=
μ.mass_to_finite_measure ▸ μ.to_finite_measure.test_against_nn_lipschitz

/-- The topology of weak convergence on `measure_theory.probability_measure Ω`. This is inherited
(induced) from the topology of weak convergence of finite measures via the inclusion
`measure_theory.probability_measure.to_finite_measure`. -/
instance : topological_space (probability_measure Ω) :=
topological_space.induced to_finite_measure infer_instance

lemma to_finite_measure_continuous :
  continuous (to_finite_measure : probability_measure Ω → finite_measure Ω) :=
continuous_induced_dom

/-- Probability measures yield elements of the `weak_dual` of bounded continuous nonnegative
functions via `measure_theory.finite_measure.test_against_nn`, i.e., integration. -/
def to_weak_dual_bcnn : probability_measure Ω → weak_dual ℝ≥0 (Ω →ᵇ ℝ≥0) :=
finite_measure.to_weak_dual_bcnn ∘ to_finite_measure

@[simp] lemma coe_to_weak_dual_bcnn (μ : probability_measure Ω) :
  ⇑μ.to_weak_dual_bcnn = μ.to_finite_measure.test_against_nn := rfl

@[simp] lemma to_weak_dual_bcnn_apply (μ : probability_measure Ω) (f : Ω →ᵇ ℝ≥0) :
  μ.to_weak_dual_bcnn f = (∫⁻ ω, f ω ∂(μ : measure Ω)).to_nnreal := rfl

lemma to_weak_dual_bcnn_continuous :
  continuous (λ (μ : probability_measure Ω), μ.to_weak_dual_bcnn) :=
finite_measure.to_weak_dual_bcnn_continuous.comp to_finite_measure_continuous

/- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
lemma continuous_test_against_nn_eval (f : Ω →ᵇ ℝ≥0) :
  continuous (λ (μ : probability_measure Ω), μ.to_finite_measure.test_against_nn f) :=
(finite_measure.continuous_test_against_nn_eval f).comp to_finite_measure_continuous

/- The canonical mapping from probability measures to finite measures is an embedding. -/
lemma to_finite_measure_embedding (Ω : Type*)
  [measurable_space Ω] [topological_space Ω] [opens_measurable_space Ω] :
  embedding (to_finite_measure : probability_measure Ω → finite_measure Ω) :=
{ induced := rfl,
  inj := λ μ ν h, subtype.eq (by convert congr_arg coe h) }

lemma tendsto_nhds_iff_to_finite_measures_tendsto_nhds {δ : Type*}
  (F : filter δ) {μs : δ → probability_measure Ω} {μ₀ : probability_measure Ω} :
  tendsto μs F (𝓝 μ₀) ↔ tendsto (to_finite_measure ∘ μs) F (𝓝 (μ₀.to_finite_measure)) :=
embedding.tendsto_nhds_iff (to_finite_measure_embedding Ω)

/-- A characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
theorem tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → probability_measure Ω} {μ : probability_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ≥0), tendsto (λ i, (∫⁻ ω, (f ω) ∂(μs(i) : measure Ω))) F
    (𝓝 ((∫⁻ ω, (f ω) ∂(μ : measure Ω)))) :=
begin
  rw tendsto_nhds_iff_to_finite_measures_tendsto_nhds,
  exact finite_measure.tendsto_iff_forall_lintegral_tendsto,
end

/-- The characterization of weak convergence of probability measures by the usual (defining)
condition that the integrals of every continuous bounded function converge to the integral of the
function against the limit measure. -/
theorem tendsto_iff_forall_integral_tendsto
  {γ : Type*} {F : filter γ} {μs : γ → probability_measure Ω} {μ : probability_measure Ω} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : Ω →ᵇ ℝ),
    tendsto (λ i, (∫ ω, (f ω) ∂(μs i : measure Ω))) F (𝓝 ((∫ ω, (f ω) ∂(μ : measure Ω)))) :=
begin
  rw tendsto_nhds_iff_to_finite_measures_tendsto_nhds,
  rw finite_measure.tendsto_iff_forall_integral_tendsto,
  simp only [coe_comp_to_finite_measure_eq_coe],
end

end probability_measure -- namespace

end probability_measure -- section

section normalize_finite_measure
/-! ### Normalization of finite measures to probability measures

This section is about normalizing finite measures to probability measures.

The weak convergence of finite measures to nonzero limit measures is characterized by
the convergence of the total mass and the convergence of the normalized probability
measures.
-/

namespace finite_measure

variables {Ω : Type*} [nonempty Ω] {m0 : measurable_space Ω} (μ : finite_measure Ω)

/-- Normalize a finite measure so that it becomes a probability measure, i.e., divide by the
total mass. -/
def normalize : probability_measure Ω :=
if zero : μ.mass = 0 then ⟨measure.dirac ‹nonempty Ω›.some, measure.dirac.is_probability_measure⟩
  else {  val := (μ.mass)⁻¹ • μ,
          property := begin
            refine ⟨_⟩,
            simp only [mass, measure.coe_nnreal_smul_apply,
                        ←ennreal_coe_fn_eq_coe_fn_to_measure μ univ],
            norm_cast,
            exact inv_mul_cancel zero,
          end }

@[simp] lemma self_eq_mass_mul_normalize (s : set Ω) : μ s = μ.mass * μ.normalize s :=
begin
  by_cases μ = 0,
  { rw h,
    simp only [zero.mass, coe_fn_zero, pi.zero_apply, zero_mul], },
  have mass_nonzero : μ.mass ≠ 0, by rwa μ.mass_nonzero_iff,
  simp only [(show μ ≠ 0, from h), mass_nonzero, normalize, not_false_iff, dif_neg],
  change μ s = μ.mass * ((μ.mass)⁻¹ • μ) s,
  rw coe_fn_smul_apply,
  simp only [mass_nonzero, algebra.id.smul_eq_mul, mul_inv_cancel_left₀, ne.def, not_false_iff],
end

lemma self_eq_mass_smul_normalize : μ = μ.mass • μ.normalize.to_finite_measure :=
begin
  ext s s_mble,
  rw [μ.self_eq_mass_mul_normalize s, coe_fn_smul_apply],
  refl,
end

lemma normalize_eq_of_nonzero (nonzero : μ ≠ 0) (s : set Ω) :
  μ.normalize s = (μ.mass)⁻¹ * (μ s) :=
by simp only [μ.self_eq_mass_mul_normalize, μ.mass_nonzero_iff.mpr nonzero,
              inv_mul_cancel_left₀, ne.def, not_false_iff]

lemma normalize_eq_inv_mass_smul_of_nonzero (nonzero : μ ≠ 0) :
  μ.normalize.to_finite_measure = (μ.mass)⁻¹ • μ :=
begin
  nth_rewrite 2 μ.self_eq_mass_smul_normalize,
  rw ← smul_assoc,
  simp only [μ.mass_nonzero_iff.mpr nonzero, algebra.id.smul_eq_mul,
             inv_mul_cancel, ne.def, not_false_iff, one_smul],
end

lemma coe_normalize_eq_of_nonzero (nonzero : μ ≠ 0) : (μ.normalize : measure Ω) = (μ.mass)⁻¹ • μ :=
begin
  ext1 s s_mble,
  simp only [← μ.normalize.ennreal_coe_fn_eq_coe_fn_to_measure s,
             μ.normalize_eq_of_nonzero nonzero s, ennreal.coe_mul,
             ennreal_coe_fn_eq_coe_fn_to_measure, measure.coe_nnreal_smul_apply],
end

@[simp] lemma _root_.probability_measure.to_finite_measure_normalize_eq_self
  {m0 : measurable_space Ω} (μ : probability_measure Ω) :
  μ.to_finite_measure.normalize = μ :=
begin
  ext s s_mble,
  rw μ.to_finite_measure.normalize_eq_of_nonzero μ.to_finite_measure_nonzero s,
  simp only [probability_measure.mass_to_finite_measure, inv_one, one_mul],
  refl,
end

/-- Averaging with respect to a finite measure is the same as integraing against
`measure_theory.finite_measure.normalize`. -/
lemma average_eq_integral_normalize
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
  (nonzero : μ ≠ 0) (f : Ω → E) :
  average (μ : measure Ω) f = ∫ ω, f ω ∂(μ.normalize : measure Ω) :=
begin
  rw [μ.coe_normalize_eq_of_nonzero nonzero, average],
  congr,
  simp only [ring_hom.to_fun_eq_coe, ennreal.coe_of_nnreal_hom,
             ennreal.coe_inv (μ.mass_nonzero_iff.mpr nonzero), ennreal_mass],
end

variables [topological_space Ω]

lemma test_against_nn_eq_mass_mul (f : Ω →ᵇ ℝ≥0) :
  μ.test_against_nn f = μ.mass * μ.normalize.to_finite_measure.test_against_nn f :=
begin
  nth_rewrite 0 μ.self_eq_mass_smul_normalize,
  rw μ.normalize.to_finite_measure.smul_test_against_nn_apply μ.mass f,
  refl,
end

lemma normalize_test_against_nn (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
  μ.normalize.to_finite_measure.test_against_nn f = (μ.mass)⁻¹ * μ.test_against_nn f :=
by simp [μ.test_against_nn_eq_mass_mul, μ.mass_nonzero_iff.mpr nonzero]

variables [opens_measurable_space Ω]

variables {μ}

lemma tendsto_test_against_nn_of_tendsto_normalize_test_against_nn_of_tendsto_mass
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω}
  (μs_lim : tendsto (λ i, (μs i).normalize) F (𝓝 μ.normalize))
  (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 μ.mass)) (f : Ω →ᵇ ℝ≥0) :
  tendsto (λ i, (μs i).test_against_nn f) F (𝓝 (μ.test_against_nn f)) :=
begin
  by_cases h_mass : μ.mass = 0,
  { simp only [μ.mass_zero_iff.mp h_mass, zero.test_against_nn_apply,
               zero.mass, eq_self_iff_true] at *,
    exact tendsto_zero_test_against_nn_of_tendsto_zero_mass mass_lim f, },
  simp_rw [(λ i, (μs i).test_against_nn_eq_mass_mul f), μ.test_against_nn_eq_mass_mul f],
  rw probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds at μs_lim,
  rw tendsto_iff_forall_test_against_nn_tendsto at μs_lim,
  have lim_pair : tendsto
        (λ i, (⟨(μs i).mass, (μs i).normalize.to_finite_measure.test_against_nn f⟩ : ℝ≥0 × ℝ≥0))
        F (𝓝 (⟨μ.mass, μ.normalize.to_finite_measure.test_against_nn f⟩)),
    from (prod.tendsto_iff _ _).mpr ⟨mass_lim, μs_lim f⟩,
  exact tendsto_mul.comp lim_pair,
end

lemma tendsto_normalize_test_against_nn_of_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} (μs_lim : tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) (f : Ω →ᵇ ℝ≥0) :
  tendsto (λ i, (μs i).normalize.to_finite_measure.test_against_nn f) F
          (𝓝 (μ.normalize.to_finite_measure.test_against_nn f)) :=
begin
  have lim_mass := μs_lim.mass,
  have aux : {(0 : ℝ≥0)}ᶜ ∈ 𝓝 (μ.mass),
    from is_open_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr nonzero),
  have eventually_nonzero : ∀ᶠ i in F, μs i ≠ 0,
  { simp_rw ← mass_nonzero_iff,
    exact lim_mass aux, },
  have eve : ∀ᶠ i in F,
    (μs i).normalize.to_finite_measure.test_against_nn f
    = ((μs i).mass)⁻¹ * (μs i).test_against_nn f,
  { filter_upwards [eventually_iff.mp eventually_nonzero],
    intros i hi,
    apply normalize_test_against_nn _ hi, },
  simp_rw [tendsto_congr' eve, μ.normalize_test_against_nn nonzero],
  have lim_pair : tendsto
        (λ i, (⟨((μs i).mass)⁻¹, (μs i).test_against_nn f⟩ : ℝ≥0 × ℝ≥0))
        F (𝓝 (⟨(μ.mass)⁻¹, μ.test_against_nn f⟩)),
  { refine (prod.tendsto_iff _ _).mpr ⟨_, _⟩,
    { exact (continuous_on_inv₀.continuous_at aux).tendsto.comp lim_mass, },
    { exact tendsto_iff_forall_test_against_nn_tendsto.mp μs_lim f, }, },
  exact tendsto_mul.comp lim_pair,
end

/-- If the normalized versions of finite measures converge weakly and their total masses
also converge, then the finite measures themselves converge weakly. -/
lemma tendsto_of_tendsto_normalize_test_against_nn_of_tendsto_mass
  {γ : Type*} {F : filter γ} {μs : γ → finite_measure Ω}
  (μs_lim : tendsto (λ i, (μs i).normalize) F (𝓝 μ.normalize))
  (mass_lim : tendsto (λ i, (μs i).mass) F (𝓝 μ.mass)) :
  tendsto μs F (𝓝 μ) :=
begin
  rw tendsto_iff_forall_test_against_nn_tendsto,
  exact λ f, tendsto_test_against_nn_of_tendsto_normalize_test_against_nn_of_tendsto_mass
             μs_lim mass_lim f,
end

/-- If finite measures themselves converge weakly to a nonzero limit measure, then their
normalized versions also converge weakly. -/
lemma tendsto_normalize_of_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} (μs_lim : tendsto μs F (𝓝 μ)) (nonzero : μ ≠ 0) :
  tendsto (λ i, (μs i).normalize) F (𝓝 (μ.normalize)) :=
begin
  rw [probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds,
      tendsto_iff_forall_test_against_nn_tendsto],
  exact λ f, tendsto_normalize_test_against_nn_of_tendsto μs_lim nonzero f,
end

/-- The weak convergence of finite measures to a nonzero limit can be characterized by the weak
convergence of both their normalized versions (probability measures) and their total masses. -/
theorem tendsto_normalize_iff_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measure Ω} (nonzero : μ ≠ 0) :
  tendsto (λ i, (μs i).normalize) F (𝓝 (μ.normalize)) ∧ tendsto (λ i, (μs i).mass) F (𝓝 (μ.mass))
  ↔ tendsto μs F (𝓝 μ) :=
begin
  split,
  { rintros ⟨normalized_lim, mass_lim⟩,
    exact tendsto_of_tendsto_normalize_test_against_nn_of_tendsto_mass normalized_lim mass_lim, },
  { intro μs_lim,
    refine ⟨tendsto_normalize_of_tendsto μs_lim nonzero, μs_lim.mass⟩, },
end

end finite_measure --namespace

end normalize_finite_measure -- section

section conditioned_probability_measure

namespace probability_measure

variables {Ω : Type*} [measurable_space Ω]

/-- Probability measure P conditioned on an event A. -/
def conditioned (P : probability_measure Ω) (A : set Ω) : probability_measure Ω :=
@finite_measure.normalize Ω (nonempty_of_probability_measure P) _ (P.to_finite_measure.restrict A)

lemma conditioned_apply
  (P : probability_measure Ω) {A : set Ω} (proba_nonzero : P A ≠ 0) {E : set Ω} (E_mble : measurable_set E) :
  (P.conditioned A) E = (P A)⁻¹ * P (E ∩ A) :=
begin
  rw [conditioned, finite_measure.normalize_eq_of_nonzero],
  { rw [measure_theory.finite_measure.restrict_apply _ _ E_mble,
        measure_theory.finite_measure.restrict_mass, coe_fn_comp_to_finite_measure_eq_coe_fn], },
  { rwa [measure_theory.finite_measure.restrict_nonzero_iff,
         coe_fn_comp_to_finite_measure_eq_coe_fn], },
end

@[simp] lemma conditioned_apply_mul_apply_self
  (P : probability_measure Ω) (A : set Ω) {E : set Ω} (E_mble : measurable_set E) :
  ((P.conditioned A) E) * (P A) = P (E ∩ A) :=
begin
  by_cases h : P A = 0,
  { simp only [h, mul_zero],
    refine le_antisymm zero_le' _,
    rw ← h,
    exact apply_mono _ (inter_subset_right E A), },
  rw [conditioned_apply P h E_mble, mul_comm, ← mul_assoc],
  simp [mul_inv_cancel h],
end

end probability_measure --namespace

end conditioned_probability_measure --section

section limsup_closed_le_and_le_liminf_open
/-! ### Portmanteau: limsup condition for closed sets iff liminf condition for open sets

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, the following two conditions are equivalent:
  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` is at most the limit
      measure of `F`.
  (O) For any open set `G` in `Ω` the liminf of the measures of `G` is at least the limit
      measure of `G`.
Either of these will later be shown to be equivalent to the weak convergence of the sequence
of measures.
-/

variables {Ω : Type*} [measurable_space Ω]

lemma le_measure_compl_liminf_of_limsup_measure_le
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  {E : set Ω} (E_mble : measurable_set E) (h : L.limsup (λ i, μs i E) ≤ μ E) :
  μ Eᶜ ≤ L.liminf (λ i, μs i Eᶜ) :=
begin
  by_cases L_bot : L = ⊥,
  { simp only [L_bot, le_top,
      (show liminf (λ i, μs i Eᶜ) ⊥ = ⊤, by simp only [liminf, filter.map_bot, Liminf_bot])], },
  haveI : L.ne_bot, from {ne' := L_bot},
  have meas_Ec : μ Eᶜ = 1 - μ E,
  { simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne, },
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E,
  { intro i,
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne, },
  simp_rw [meas_Ec, meas_i_Ec],
  have obs : L.liminf (λ (i : ι), 1 - μs i E) = L.liminf ((λ x, 1 - x) ∘ (λ (i : ι), μs i E)),
    by refl,
  rw obs,
  simp_rw ← antitone_const_tsub.map_limsup_of_continuous_at (λ i, μs i E)
            (ennreal.continuous_sub_left ennreal.one_ne_top).continuous_at,
  exact antitone_const_tsub h,
end

lemma le_measure_liminf_of_limsup_measure_compl_le
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  {E : set Ω} (E_mble : measurable_set E) (h : L.limsup (λ i, μs i Eᶜ) ≤ μ Eᶜ) :
  μ E ≤ L.liminf (λ i, μs i E) :=
compl_compl E ▸ (le_measure_compl_liminf_of_limsup_measure_le (measurable_set.compl E_mble) h)

lemma limsup_measure_compl_le_of_le_liminf_measure
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  {E : set Ω} (E_mble : measurable_set E) (h : μ E ≤ L.liminf (λ i, μs i E)) :
  L.limsup (λ i, μs i Eᶜ) ≤ μ Eᶜ :=
begin
  by_cases L_bot : L = ⊥,
  { simp only [L_bot, bot_le,
      (show limsup (λ i, μs i Eᶜ) ⊥ = ⊥, by simp only [limsup, filter.map_bot, Limsup_bot])], },
  haveI : L.ne_bot, from {ne' := L_bot},
  have meas_Ec : μ Eᶜ = 1 - μ E,
  { simpa only [measure_univ] using measure_compl E_mble (measure_lt_top μ E).ne, },
  have meas_i_Ec : ∀ i, μs i Eᶜ = 1 - μs i E,
  { intro i,
    simpa only [measure_univ] using measure_compl E_mble (measure_lt_top (μs i) E).ne, },
  simp_rw [meas_Ec, meas_i_Ec],
  have obs : L.limsup (λ (i : ι), 1 - μs i E) = L.limsup ((λ x, 1 - x) ∘ (λ (i : ι), μs i E)),
    by refl,
  rw obs,
  simp_rw ← antitone_const_tsub.map_liminf_of_continuous_at (λ i, μs i E)
            (ennreal.continuous_sub_left ennreal.one_ne_top).continuous_at,
  exact antitone_const_tsub h,
end

lemma limsup_measure_le_of_le_liminf_measure_compl
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  {E : set Ω} (E_mble : measurable_set E) (h : μ Eᶜ ≤ L.liminf (λ i, μs i Eᶜ)) :
  L.limsup (λ i, μs i E) ≤ μ E :=
compl_compl E ▸ (limsup_measure_compl_le_of_le_liminf_measure (measurable_set.compl E_mble) h)

variables [topological_space Ω] [opens_measurable_space Ω]

/-- One pair of implications of the portmanteau theorem:
For a sequence of Borel probability measures, the following two are equivalent:

(C) The limsup of the measures of any closed set is at most the measure of the closed set
under a candidate limit measure.

(O) The liminf of the measures of any open set is at least the measure of the open set
under a candidate limit measure.
-/
lemma limsup_measure_closed_le_iff_liminf_measure_open_ge
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)] :
  (∀ F, is_closed F → L.limsup (λ i, μs i F) ≤ μ F)
    ↔ (∀ G, is_open G → μ G ≤ L.liminf (λ i, μs i G)) :=
begin
  split,
  { intros h G G_open,
    exact le_measure_liminf_of_limsup_measure_compl_le
          G_open.measurable_set (h Gᶜ (is_closed_compl_iff.mpr G_open)), },
  { intros h F F_closed,
    exact limsup_measure_le_of_le_liminf_measure_compl
          F_closed.measurable_set (h Fᶜ (is_open_compl_iff.mpr F_closed)), },
end

end limsup_closed_le_and_le_liminf_open -- section

section tendsto_of_null_frontier
/-! ### Portmanteau: limit of measures of Borel sets whose boundary carries no mass in the limit

In this section we prove that for a sequence of Borel probability measures on a topological space
and its candidate limit measure, either of the following equivalent conditions:
  (C) For any closed set `F` in `Ω` the limsup of the measures of `F` is at most the limit
      measure of `F`
  (O) For any open set `G` in `Ω` the liminf of the measures of `G` is at least the limit
      measure of `G`
implies that
  (B) For any Borel set `E` in `Ω` whose boundary `∂E` carries no mass under the candidate limit
      measure, we have that the limit of measures of `E` is the measure of `E` under the
      candidate limit measure.
-/

variables {Ω : Type*} [measurable_space Ω]

lemma tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  {E₀ E E₁ : set Ω} (E₀_subset : E₀ ⊆ E) (subset_E₁ : E ⊆ E₁) (nulldiff : μ (E₁ \ E₀) = 0)
  (h_E₀ : μ E₀ ≤ L.liminf (λ i, μs i E₀)) (h_E₁ : L.limsup (λ i, μs i E₁) ≤ μ E₁) :
  L.tendsto (λ i, μs i E) (𝓝 (μ E)) :=
begin
  apply tendsto_of_le_liminf_of_limsup_le,
  { have E₀_ae_eq_E : E₀ =ᵐ[μ] E,
      from eventually_le.antisymm E₀_subset.eventually_le
            (subset_E₁.eventually_le.trans (ae_le_set.mpr nulldiff)),
    calc  μ(E)
        = μ(E₀)                      : measure_congr E₀_ae_eq_E.symm
    ... ≤ L.liminf (λ i, μs i E₀)    : h_E₀
    ... ≤ L.liminf (λ i, μs i E)     : _,
    { refine liminf_le_liminf (eventually_of_forall (λ _, measure_mono E₀_subset)) _,
      apply_auto_param, }, },
  { have E_ae_eq_E₁ : E =ᵐ[μ] E₁,
      from eventually_le.antisymm subset_E₁.eventually_le
            ((ae_le_set.mpr nulldiff).trans E₀_subset.eventually_le),
    calc  L.limsup (λ i, μs i E)
        ≤ L.limsup (λ i, μs i E₁)    : _
    ... ≤ μ E₁                       : h_E₁
    ... = μ E                        : measure_congr E_ae_eq_E₁.symm,
    { refine limsup_le_limsup (eventually_of_forall (λ _, measure_mono subset_E₁)) _,
      apply_auto_param, }, },
end

variables [topological_space Ω] [opens_measurable_space Ω]

/-- One implication of the portmanteau theorem:
For a sequence of Borel probability measures, if the liminf of the measures of any open set is at
least the measure of the open set under a candidate limit measure, then for any set whose
boundary carries no probability mass under the candidate limit measure, then its measures under the
sequence converge to its measure under the candidate limit measure.
-/
lemma tendsto_measure_of_null_frontier
  {ι : Type*} {L : filter ι} {μ : measure Ω} {μs : ι → measure Ω}
  [is_probability_measure μ] [∀ i, is_probability_measure (μs i)]
  (h_opens : ∀ G, is_open G → μ G ≤ L.liminf (λ i, μs i G))
  {E : set Ω} (E_nullbdry : μ (frontier E) = 0) :
  L.tendsto (λ i, μs i E) (𝓝 (μ E)) :=
begin
  have h_closeds : ∀ F, is_closed F → L.limsup (λ i, μs i F) ≤ μ F,
    from limsup_measure_closed_le_iff_liminf_measure_open_ge.mpr h_opens,
  exact tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
        interior_subset subset_closure E_nullbdry
        (h_opens _ is_open_interior) (h_closeds _ is_closed_closure),
end

end tendsto_of_null_frontier --section

section convergence_implies_limsup_closed_le
/-! ### Portmanteau implication: weak convergence implies a limsup condition for closed sets

In this section we prove, under the assumption that the underlying topological space `Ω` is
pseudo-emetrizable, that the weak convergence of measures on `measure_theory.finite_measure Ω`
implies that for any closed set `F` in `Ω` the limsup of the measures of `F` is at most the
limit measure of `F`. This is one implication of the portmanteau theorem characterizing weak
convergence of measures.

Combining with an earlier implication we also get that weak convergence implies that for any Borel
set `E` in `Ω` whose boundary `∂E` carries no mass under the limit measure, the limit of measures
of `E` is the measure of `E` under the limit measure.
-/

variables {Ω : Type*} [measurable_space Ω]

/-- If bounded continuous functions tend to the indicator of a measurable set and are
uniformly bounded, then their integrals against a finite measure tend to the measure of the set.
This formulation assumes:
 * the functions tend to a limit along a countably generated filter;
 * the limit is in the almost everywhere sense;
 * boundedness holds almost everywhere.
-/
lemma measure_of_cont_bdd_of_tendsto_filter_indicator {ι : Type*} {L : filter ι}
  [L.is_countably_generated] [topological_space Ω] [opens_measurable_space Ω]
  (μ : measure Ω) [is_finite_measure μ] {c : ℝ≥0} {E : set Ω} (E_mble : measurable_set E)
  (fs : ι → (Ω →ᵇ ℝ≥0)) (fs_bdd : ∀ᶠ i in L, ∀ᵐ (ω : Ω) ∂μ, fs i ω ≤ c)
  (fs_lim : ∀ᵐ (ω : Ω) ∂μ,
            tendsto (λ (i : ι), (coe_fn : (Ω →ᵇ ℝ≥0) → (Ω → ℝ≥0)) (fs i) ω) L
                    (𝓝 (indicator E (λ x, (1 : ℝ≥0)) ω))) :
  tendsto (λ n, lintegral μ (λ ω, fs n ω)) L (𝓝 (μ E)) :=
begin
  convert finite_measure.tendsto_lintegral_nn_filter_of_le_const μ fs_bdd fs_lim,
  have aux : ∀ ω, indicator E (λ ω, (1 : ℝ≥0∞)) ω = ↑(indicator E (λ ω, (1 : ℝ≥0)) ω),
  from λ ω, by simp only [ennreal.coe_indicator, ennreal.coe_one],
  simp_rw [←aux, lintegral_indicator _ E_mble],
  simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter],
end

/-- If a sequence of bounded continuous functions tends to the indicator of a measurable set and
the functions are uniformly bounded, then their integrals against a finite measure tend to the
measure of the set.

A similar result with more general assumptions is
`measure_theory.measure_of_cont_bdd_of_tendsto_filter_indicator`.
-/
lemma measure_of_cont_bdd_of_tendsto_indicator
  [topological_space Ω] [opens_measurable_space Ω]
  (μ : measure Ω) [is_finite_measure μ] {c : ℝ≥0} {E : set Ω} (E_mble : measurable_set E)
  (fs : ℕ → (Ω →ᵇ ℝ≥0)) (fs_bdd : ∀ n ω, fs n ω ≤ c)
  (fs_lim : tendsto (λ (n : ℕ), (coe_fn : (Ω →ᵇ ℝ≥0) → (Ω → ℝ≥0)) (fs n))
            at_top (𝓝 (indicator E (λ x, (1 : ℝ≥0))))) :
  tendsto (λ n, lintegral μ (λ ω, fs n ω)) at_top (𝓝 (μ E)) :=
begin
  have fs_lim' : ∀ ω, tendsto (λ (n : ℕ), (fs n ω : ℝ≥0))
                 at_top (𝓝 (indicator E (λ x, (1 : ℝ≥0)) ω)),
  by { rw tendsto_pi_nhds at fs_lim, exact λ ω, fs_lim ω, },
  apply measure_of_cont_bdd_of_tendsto_filter_indicator μ E_mble fs
      (eventually_of_forall (λ n, eventually_of_forall (fs_bdd n))) (eventually_of_forall fs_lim'),
end

/-- The integrals of thickened indicators of a closed set against a finite measure tend to the
measure of the closed set if the thickening radii tend to zero.
-/
lemma tendsto_lintegral_thickened_indicator_of_is_closed
  {Ω : Type*} [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  (μ : measure Ω) [is_finite_measure μ] {F : set Ω} (F_closed : is_closed F) {δs : ℕ → ℝ}
  (δs_pos : ∀ n, 0 < δs n) (δs_lim : tendsto δs at_top (𝓝 0)) :
  tendsto (λ n, lintegral μ (λ ω, (thickened_indicator (δs_pos n) F ω : ℝ≥0∞)))
          at_top (𝓝 (μ F)) :=
begin
  apply measure_of_cont_bdd_of_tendsto_indicator μ F_closed.measurable_set
          (λ n, thickened_indicator (δs_pos n) F)
          (λ n ω, thickened_indicator_le_one (δs_pos n) F ω),
  have key := thickened_indicator_tendsto_indicator_closure δs_pos δs_lim F,
  rwa F_closed.closure_eq at key,
end

/-- One implication of the portmanteau theorem:
Weak convergence of finite measures implies that the limsup of the measures of any closed set is
at most the measure of the closed set under the limit measure.
-/
lemma finite_measure.limsup_measure_closed_le_of_tendsto
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : finite_measure Ω} {μs : ι → finite_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {F : set Ω} (F_closed : is_closed F) :
  L.limsup (λ i, (μs i : measure Ω) F) ≤ (μ : measure Ω) F :=
begin
  by_cases L = ⊥,
  { simp only [h, limsup, filter.map_bot, Limsup_bot, ennreal.bot_eq_zero, zero_le], },
  apply ennreal.le_of_forall_pos_le_add,
  intros ε ε_pos μ_F_finite,
  set δs := λ (n : ℕ), (1 : ℝ) / (n+1) with def_δs,
  have δs_pos : ∀ n, 0 < δs n, from λ n, nat.one_div_pos_of_nat,
  have δs_lim : tendsto δs at_top (𝓝 0), from tendsto_one_div_add_at_top_nhds_0_nat,
  have key₁ := tendsto_lintegral_thickened_indicator_of_is_closed
                  (μ : measure Ω) F_closed δs_pos δs_lim,
  have room₁ : (μ : measure Ω) F < (μ : measure Ω) F + ε / 2,
  { apply ennreal.lt_add_right (measure_lt_top (μ : measure Ω) F).ne
          ((ennreal.div_pos_iff.mpr
              ⟨(ennreal.coe_pos.mpr ε_pos).ne.symm, ennreal.two_ne_top⟩).ne.symm), },
  rcases eventually_at_top.mp (eventually_lt_of_tendsto_lt room₁ key₁) with ⟨M, hM⟩,
  have key₂ := finite_measure.tendsto_iff_forall_lintegral_tendsto.mp
                μs_lim (thickened_indicator (δs_pos M) F),
  have room₂ : lintegral (μ : measure Ω) (λ a, thickened_indicator (δs_pos M) F a)
                < lintegral (μ : measure Ω) (λ a, thickened_indicator (δs_pos M) F a) + ε / 2,
  { apply ennreal.lt_add_right
          (lintegral_lt_top_of_bounded_continuous_to_nnreal (μ : measure Ω) _).ne
          ((ennreal.div_pos_iff.mpr
              ⟨(ennreal.coe_pos.mpr ε_pos).ne.symm, ennreal.two_ne_top⟩).ne.symm), },
  have ev_near := eventually.mono (eventually_lt_of_tendsto_lt room₂ key₂) (λ n, le_of_lt),
  have aux := λ n, le_trans (measure_le_lintegral_thickened_indicator
                            (μs n : measure Ω) F_closed.measurable_set (δs_pos M)),
  have ev_near' := eventually.mono ev_near aux,
  apply (filter.limsup_le_limsup ev_near').trans,
  haveI : ne_bot L, from ⟨h⟩,
  rw limsup_const,
  apply le_trans (add_le_add (hM M rfl.le).le (le_refl (ε/2 : ℝ≥0∞))),
  simp only [add_assoc, ennreal.add_halves, le_refl],
end

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the limsup of the measures of any closed
set is at most the measure of the closed set under the limit probability measure.
-/
lemma probability_measure.limsup_measure_closed_le_of_tendsto
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : probability_measure Ω} {μs : ι → probability_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {F : set Ω} (F_closed : is_closed F) :
  L.limsup (λ i, (μs i : measure Ω) F) ≤ (μ : measure Ω) F :=
by apply finite_measure.limsup_measure_closed_le_of_tendsto
         ((probability_measure.tendsto_nhds_iff_to_finite_measures_tendsto_nhds L).mp μs_lim)
         F_closed

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that the liminf of the measures of any open set
is at least the measure of the open set under the limit probability measure.
-/
lemma probability_measure.le_liminf_measure_open_of_tendsto
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : probability_measure Ω} {μs : ι → probability_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {G : set Ω} (G_open : is_open G) :
  (μ : measure Ω) G ≤ L.liminf (λ i, (μs i : measure Ω) G) :=
begin
  have h_closeds : ∀ F, is_closed F → L.limsup (λ i, (μs i : measure Ω) F) ≤ (μ : measure Ω) F,
    from λ F F_closed, probability_measure.limsup_measure_closed_le_of_tendsto μs_lim F_closed,
  exact le_measure_liminf_of_limsup_measure_compl_le
        G_open.measurable_set (h_closeds _ (is_closed_compl_iff.mpr G_open)),
end

lemma probability_measure.tendsto_measure_of_null_frontier_of_tendsto'
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : probability_measure Ω} {μs : ι → probability_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {E : set Ω} (E_nullbdry : (μ : measure Ω) (frontier E) = 0) :
  tendsto (λ i, (μs i : measure Ω) E) L (𝓝 ((μ : measure Ω) E)) :=
begin
  have h_opens : ∀ G, is_open G → (μ : measure Ω) G ≤ L.liminf (λ i, (μs i : measure Ω) G),
    from λ G G_open, probability_measure.le_liminf_measure_open_of_tendsto μs_lim G_open,
  exact tendsto_measure_of_null_frontier h_opens E_nullbdry,
end

/-- One implication of the portmanteau theorem:
Weak convergence of probability measures implies that if the boundary of a Borel set
carries no probability mass under the limit measure, then the limit of the measures of the set
equals the measure of the set under the limit probability measure.

A version with coercions to ordinary `ℝ≥0∞`-valued measures is
`measure_theory.probability_measure.tendsto_measure_of_null_frontier_of_tendsto'`.
-/
lemma probability_measure.tendsto_measure_of_null_frontier_of_tendsto
  {Ω ι : Type*} {L : filter ι}
  [measurable_space Ω] [pseudo_emetric_space Ω] [opens_measurable_space Ω]
  {μ : probability_measure Ω} {μs : ι → probability_measure Ω}
  (μs_lim : tendsto μs L (𝓝 μ)) {E : set Ω} (E_nullbdry : μ (frontier E) = 0) :
  tendsto (λ i, μs i E) L (𝓝 (μ E)) :=
begin
  have E_nullbdry' : (μ : measure Ω) (frontier E) = 0,
    by rw [← probability_measure.ennreal_coe_fn_eq_coe_fn_to_measure, E_nullbdry, ennreal.coe_zero],
  have key := probability_measure.tendsto_measure_of_null_frontier_of_tendsto' μs_lim E_nullbdry',
  exact (ennreal.tendsto_to_nnreal (measure_ne_top ↑μ E)).comp key,
end

end convergence_implies_limsup_closed_le --section

end measure_theory --namespace
