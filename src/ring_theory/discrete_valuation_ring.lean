/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import ring_theory.principal_ideal_domain order.conditionally_complete_lattice
import ring_theory.multiplicity
import ring_theory.valuation.basic
import tactic
import all

/-!
# Discrete valuation rings

There are ten definitions on Wikipedia.

## Important definitions

### Notation

### Definitions

## Implementation notes

## Tags

discrete valuation ring
-/

open_locale classical

universe u

open ideal local_ring

/-- A commutative ring is a discrete valuation ring if it's a local PID which is not a field -/
class discrete_valuation_ring (R : Type u) [integral_domain R]
  extends is_principal_ideal_ring R, local_ring R : Prop :=
(not_a_field' : maximal_ideal R ≠ ⊥)

namespace discrete_valuation_ring

variables (R : Type u) [integral_domain R] [discrete_valuation_ring R]

-- TODO: this should be localised
local notation `is_uniformiser` := irreducible

def not_a_field : maximal_ideal R ≠ ⊥ := not_a_field'

variable {R}
theorem uniformiser_iff_generator (ϖ : R) :
  is_uniformiser ϖ ↔ maximal_ideal R = ideal.span {ϖ} :=
begin
  split,
  { intro hϖ,
    cases (is_principal_ideal_ring.principal $ maximal_ideal R).principal with m hm,
    have hϖ2 : ϖ ∈ maximal_ideal R := hϖ.1,
    rw hm at hϖ2,
    rw submodule.mem_span_singleton at hϖ2,
    cases hϖ2 with a ha,
    -- rw algebra.id.smul_eq_mul at ha,
    cases hϖ.2 _ _ ha.symm,
    { rw hm,
      show ideal.span {m} = _,
      rw ←ha,
      exact (span_singleton_mul_left_unit h _).symm},
    { have h2 : ¬(is_unit m) := show m ∈ maximal_ideal R,
      from hm.symm ▸ submodule.mem_span_singleton_self m,
      exact absurd h h2}},
  { intro h,
    have h2 : ¬(is_unit ϖ) := show ϖ ∈ maximal_ideal R,
      from h.symm ▸ submodule.mem_span_singleton_self ϖ,
    split, exact h2,
    intros a b hab,
    by_contra h,
    push_neg at h,
    cases h with ha hb,
    change a ∈ maximal_ideal R at ha,
    change b ∈ maximal_ideal R at hb,
    rw h at ha hb,
    rw mem_span_singleton' at ha hb,
    rcases ha with ⟨a, rfl⟩,
    rcases hb with ⟨b, rfl⟩,
    rw (show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)), by ring) at hab,
    have h3 := eq_zero_of_mul_eq_self_right _ hab.symm,
    { apply not_a_field R,
      simp [h, h3]},
    { intro hh, apply h2,
      refine is_unit_of_dvd_one ϖ _,
      use a * b, exact hh.symm}
    }
end

variable (R)
theorem exists_uniformiser : ∃ ϖ : R, is_uniformiser ϖ :=
by {simp_rw [uniformiser_iff_generator],
    exact (is_principal_ideal_ring.principal $ maximal_ideal R).principal}

/-
Proving a result in Cassels-Froehlich: a DVR is a PID with exactly one non-zero prime ideal
-/

-- this should be somewhere else, it's a theorem about local rings
lemma local_of_unique_nonzero_prime (R : Type u) [comm_ring R]
  (h : ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P) : local_ring R :=
local_of_unique_max_ideal begin
  rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩,
  refine ⟨P, ⟨hPnot_top, _⟩, λ M hM, hPunique _ ⟨_, is_maximal.is_prime hM⟩⟩,
  { refine maximal_of_no_maximal (λ M hPM hM, ne_of_lt hPM _),
    exact (hPunique _ ⟨ne_bot_of_gt hPM, is_maximal.is_prime hM⟩).symm },
  { rintro rfl,
    exact hPnot_top (hM.2 P (bot_lt_iff_ne_bot.2 hPnonzero)) },
end

-- -- delete this
-- lemma local_of_unique_nonzero_prime'' (R : Type u) [comm_ring R]
-- (h : ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P) : local_ring R :=
-- local_of_unique_max_ideal
-- begin
--   rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩,
--   use P,
--   split,
--   { split, exact hPnot_top,
--     apply maximal_of_no_maximal,
--     intros M hPM hM,
--     apply ne_of_lt hPM,
--     symmetry,
--     apply hPunique,
--     split, apply ne_bot_of_gt hPM,
--     exact is_maximal.is_prime hM},
--   { intros M hM,
--     apply hPunique,
--     split,
--     { rintro rfl,
--       cases hM with hM1 hM2,
--       specialize hM2 P (bot_lt_iff_ne_bot.2 hPnonzero),
--       exact hPnot_top hM2},
--     { exact is_maximal.is_prime hM}}
-- end

-- lemma local_of_unique_nonzero_prime' (R : Type u) [comm_ring R]
-- (h : ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P) : local_ring R :=
-- let ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩ := h in
-- local_of_unique_max_ideal ⟨P, ⟨hPnot_top,
--   maximal_of_no_maximal $ λ M hPM hM, ne_of_lt hPM $ (hPunique _ ⟨ne_bot_of_gt hPM, is_maximal.is_prime hM⟩).symm⟩,
--   _
--  λ M hM, hPunique _ ⟨λ h, hPnot_top $ hM.2 _ (_ : M < P), is_maximal.is_prime hM⟩⟩

-- lemma local_of_unique_nonzero_prime' (R : Type u) [comm_ring R]
-- (h : ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P) : local_ring R :=
-- let ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩ := h in
-- local_of_unique_max_ideal ⟨P, ⟨hPnot_top,
--   maximal_of_no_maximal $ λ M hPM hM, ne_of_lt hPM $ (hPunique _ ⟨ne_bot_of_gt hPM, is_maximal.is_prime hM⟩).symm⟩,
--   λ M hM, hPunique _ ⟨λ (h : M = ⊥), hPnot_top $ hM.2 _ (h.symm ▸ (bot_lt_iff_ne_bot.2 hPnonzero : ⊥ < P) : M < P), is_maximal.is_prime hM⟩⟩

-- a DVR is a PID with exactly one non-zero prime ideal

theorem iff_PID_with_one_nonzero_prime (R : Type u) [integral_domain R] :
  discrete_valuation_ring R ↔ is_principal_ideal_ring R ∧ ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P :=
begin
  split,
  { intro RDVR,
    rcases id RDVR with ⟨RPID, Rlocal, Rnotafield⟩,
    split, assumption,
    resetI,
    use local_ring.maximal_ideal R,
    split, split,
    { assumption},
    { apply_instance},
    { rintro Q ⟨hQ1, hQ2⟩,
      obtain ⟨q, rfl⟩ := (is_principal_ideal_ring.principal Q).1,
      have hq : q ≠ 0,
      { rintro rfl,
        apply hQ1,
        simp,
      },
      erw span_singleton_prime hq at hQ2,
      replace hQ2 := irreducible_of_prime hQ2,
      rw uniformiser_iff_generator at hQ2,
      exact hQ2.symm}},
  { rintro ⟨RPID, Punique⟩,
    haveI : local_ring R := local_of_unique_nonzero_prime R Punique,
    refine {not_a_field' := _},
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, hP3⟩,
    have hPM : P ≤ maximal_ideal R := le_maximal_ideal (hP2.1),
    intro h, rw [h, le_bot_iff] at hPM, exact hP1 hPM}
end

lemma associated_of_uniformiser {a b : R} (ha : is_uniformiser a) (hb : is_uniformiser b) :
  associated a b :=
begin
  rw uniformiser_iff_generator at ha hb,
  rw [←span_singleton_eq_span_singleton, ←ha, hb],
end

end discrete_valuation_ring

/-
Serre:
"The non-zero ideals of A are of the form pi^n A, where pi is a uniformiser.
If x ≠ 0 is any element of A, one can write x = pi^n u, with n ∈ ℕ and u invertible;
the integer n is called the valuation of x and is denoted v(x); it doesn't depends
on the choice of pi. We make the convention that v(0)=+infty."
-/

-- this shoudl be somewhere else
noncomputable def add_valuation {R : Type*} [comm_ring R] (I : ideal R) (r : R) : enat :=
multiplicity I (span {r} : ideal R)

--instance foo : partial_order enat := by apply_instance
--instance : partial_order (multiplicative enat) := foo

-- want type T
-- T = {0} ∪ {g^n : n ∈ ℤ}, 0 <

def Γ := with_zero (multiplicative ℤ)
def g : Γ := some (-1 : ℤ)

set_option old_structure_cmd true

section prio
-- look this up later
class linear_ordered_comm_group (G : Type u) extends ordered_comm_group G, linear_order G.
end prio

namespace with_zero

instance (G : Type*) [group G] : group_with_zero (with_zero G) :=
{ inv_zero := with_zero.inv_zero,
  mul_inv_cancel := with_zero.mul_right_inv,
  .. with_zero.monoid,
  .. with_zero.mul_zero_class,
  .. with_zero.has_inv,
  .. with_zero.nonzero }

instance (G : Type u) [comm_group G] : comm_group_with_zero (with_zero G) :=
  {.. with_zero.group_with_zero G,
   .. with_zero.comm_monoid }

lemma zero_le {G : Type u} [partial_order G] (x : with_zero G) : 0 ≤ x :=
bot_le

lemma le_zero_iff {G : Type u} [partial_order G] (x : with_zero G) : x ≤ 0 ↔ x = 0 :=
le_bot_iff

lemma eq_zero_or_coe {G : Type u} : ∀ x : with_zero G, x = 0 ∨ ∃ y : G, ↑y = x
| none     := or.inl rfl
| (some y) := or.inr ⟨y, rfl⟩

lemma coe_le_coe {G : Type u} [partial_order G] {x y : G} : (x : with_zero G) ≤ y ↔ x ≤ y :=
with_bot.coe_le_coe

instance (G : Type u) [linear_ordered_comm_group G] : linear_ordered_comm_group_with_zero (with_zero G) :=
{ mul_le_mul_left := begin
    intros a b hab c,
    rcases eq_zero_or_coe a with rfl | ⟨a, rfl⟩, { rw mul_zero, exact with_zero.zero_le _ },
    rcases eq_zero_or_coe b with rfl | ⟨b, rfl⟩, { rw le_zero_iff at hab, cases hab },
    rw with_bot.coe_le_coe at hab,
    rcases eq_zero_or_coe c with rfl | ⟨c, rfl⟩, { rw [zero_mul, zero_mul], exact le_refl _ },
    rw [mul_coe, mul_coe, with_bot.coe_le_coe], exact mul_le_mul_left' hab
  end,
  zero_le_one := with_zero.zero_le _,
  .. with_zero.comm_group_with_zero G,
  .. with_zero.linear_order }

end with_zero

-- instance : partial_order (multiplicative ℤ) := (by apply_instance : partial_order ℤ)

-- instance : comm_group (multiplicative ℤ) := by apply_instance -- works

instance (G : Type u) [ordered_add_comm_group G] : ordered_comm_group (multiplicative G) :=
{ mul_le_mul_left := @add_le_add_left G _,
  ..(by apply_instance : comm_group (multiplicative G)),
  ..(by apply_instance : partial_order G) }

instance foo : ordered_comm_group (multiplicative ℤ) := by apply_instance

instance : linear_order (multiplicative ℤ) := (by apply_instance : linear_order ℤ)

instance (G : Type u) [decidable_linear_ordered_add_comm_group G] : linear_ordered_comm_group (multiplicative G) :=
{ ..(by apply_instance : ordered_comm_group (multiplicative G)),
  ..(by apply_instance : linear_order G) }

instance bar : linear_ordered_comm_group (multiplicative ℤ) := by apply_instance

instance : linear_ordered_comm_group_with_zero Γ := by dunfold Γ; apply_instance

instance baz : add_comm_monoid enat := by apply_instance

--def sdfsdf : ℕ →+ ℤ := nat.cast_add_monoid_hom _

noncomputable def qux : enat → with_zero (multiplicative ℤ)
| ⟨P, n⟩ := if H : P then ↑(multiplicative.of_add (n H) : multiplicative ℤ)⁻¹ else 0

def hom_with_zero {α β} [monoid α] [monoid β] (f : α →* β) : α →* with_zero β :=
{ to_fun := some ∘ f,
  map_one' := congr_arg some f.map_one,
  map_mul' := λ x y, congr_arg some $ f.map_mul _ _ }

def canonical : multiplicative enat →* Γ :=
{ to_fun := sorry,
  map_one' :=

}

-- instance : complete_lattice enat :=  by apply_instance


/-
Serre then proves that if A is a commutative ring, it's a DVR iff it's Noetherian and
local, and its maximal ideal is generated by a non-nilpotent element.
-/


/-
Wikipedia:
In abstract algebra, a discrete valuation ring (DVR) is a principal ideal domain (PID)
with exactly one non-zero maximal ideal.

This means a DVR is an integral domain R which satisfies any one of the following equivalent conditions:

-- USED    R is a local principal ideal domain, and not a field.
    R is a valuation ring with a value group isomorphic to the integers under addition.
    R is a local Dedekind domain and not a field.
    R is a Noetherian local domain whose maximal ideal is principal, and not a field.[1]
    R is an integrally closed Noetherian local ring with Krull dimension one.
-- WORKING ON THIS    R is a principal ideal domain with a unique non-zero prime ideal.
    R is a principal ideal domain with a unique irreducible element (up to multiplication by units).
    R is a unique factorization domain with a unique irreducible element (up to multiplication by units).
    R is Noetherian, not a field, and every nonzero fractional ideal of R is irreducible in the sense that it cannot be written as a finite intersection of fractional ideals properly containing it.
    There is some discrete valuation ν on the field of fractions K of R such that R = {x : x in K, ν(x) ≥ 0}.

Serre defines a DVR to be a PID with a unique non-zero prime ideal and one can build the
theory relatively quickly from this.
-/
