/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/

import ring_theory.principal_ideal_domain

/-!

# Bézout rings

A Bézout ring (Bezout ring) is a ring whose finitely generated ideals are principal.
Notible examples include principal ideal rings, valuation rings, and the ring of algebraic integers.

## Main results
- `is_bezout.iff_span_pair_is_principal`: It suffices to verify every `span {x, y}` is principal.
- `is_bezout.to_gcd_monoid`: Every Bézout domain is a GCD domain. This is not an instance.
- `is_bezout.tfae`: For a Bézout domain, noetherian ↔ PID ↔ UFD ↔ ACCP

-/

universes u v

variables (R : Type u) [comm_ring R]

/-- A Bézout ring is a ring whose finitely generated ideals are principal. -/
class is_bezout : Prop :=
(is_principal_of_fg : ∀ I : ideal R, I.fg → I.is_principal)

namespace is_bezout

variables {R}

lemma span_pair_is_principal [is_bezout R] (x y : R) :
  (ideal.span {x, y} : ideal R).is_principal :=
by { classical, exact is_principal_of_fg (ideal.span {x, y}) ⟨{x, y}, by simp⟩ }

lemma submodule.fg_induction (R M : Type*) [semiring R] [add_comm_monoid M] [module R M]
  (P : submodule R M → Prop)
  (h₁ : ∀ x, P (submodule.span R {x})) (h₂ : ∀ M₁ M₂, P M₁ → P M₂ → P (M₁ ⊔ M₂))
  (N : submodule R M) (hN : N.fg) : P N :=
begin
  classical,
  obtain ⟨s, rfl⟩ := hN,
  induction s using finset.induction,
  { rw [finset.coe_empty, submodule.span_empty, ← submodule.span_zero_singleton], apply h₁ },
  { rw [finset.coe_insert, submodule.span_insert], apply h₂; apply_assumption }
end

lemma iff_span_pair_is_principal :
  is_bezout R ↔ (∀ x y : R, (ideal.span {x, y} : ideal R).is_principal) :=
begin
  classical,
  split,
  { introsI H x y, apply span_pair_is_principal },
  { intro H,
    constructor,
    apply submodule.fg_induction,
    { exact λ _, ⟨⟨_, rfl⟩⟩ },
    { rintro _ _ ⟨⟨x, rfl⟩⟩ ⟨⟨y, rfl⟩⟩, rw ← submodule.span_insert, exact H _ _ } },
end

section gcd

variable [is_bezout R]

/-- The gcd of two elements in a bezout domain. -/
noncomputable
def gcd (x y : R) : R := (span_pair_is_principal x y).1.some

lemma gcd_prop (x y : R) : (ideal.span {gcd x y} : ideal R) = ideal.span {x, y} :=
(span_pair_is_principal x y).1.some_spec.symm

lemma gcd_dvd_left (x y : R) : gcd x y ∣ x :=
ideal.span_singleton_le_span_singleton.mp
  (by { rw gcd_prop, apply ideal.span_mono, simp })

lemma gcd_dvd_right (x y : R) : gcd x y ∣ y :=
ideal.span_singleton_le_span_singleton.mp
  (by { rw gcd_prop, apply ideal.span_mono, simp })

lemma dvd_gcd {x y z : R} (hx : z ∣ x) (hy : z ∣ y) : z ∣ gcd x y :=
begin
  rw [← ideal.span_singleton_le_span_singleton] at hx hy ⊢,
  rw [gcd_prop, ideal.span_insert, sup_le_iff],
  exact ⟨hx, hy⟩
end

lemma gcd_eq_sum (x y : R) : ∃ a b : R, a * x + b * y = gcd x y :=
ideal.mem_span_pair.mp (by { rw ← gcd_prop, apply ideal.subset_span, simp })

variable (R)

/-- Any bezout domain is a GCD domain. This is not an instance since `gcd_monoid` contains data,
and this might not be how we would like to construct it. -/
noncomputable
def to_gcd_domain [is_domain R] [decidable_eq R] :
  gcd_monoid R :=
gcd_monoid_of_gcd gcd gcd_dvd_left gcd_dvd_right
  (λ _ _ _, dvd_gcd)

end gcd

local attribute [instance] to_gcd_domain

lemma of_surjective {S : Type v} [comm_ring S] (f : R →+* S) (hf : function.surjective f)
  [is_bezout R] : is_bezout S :=
begin
  rw iff_span_pair_is_principal,
  intros x y,
  obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ⟨hf x, hf y⟩,
  use f (gcd x y),
  transitivity ideal.map f (ideal.span {gcd x y}),
  { rw [gcd_prop, ideal.map_span, set.image_insert_eq, set.image_singleton] },
  { rw [ideal.map_span, set.image_singleton], refl }
end

instance of_is_principal_ideal_ring [is_principal_ideal_ring R] : is_bezout R :=
⟨λ I _, is_principal_ideal_ring.principal I⟩

lemma is_noetherian_iff_fg_well_founded {M : Type*} [add_comm_monoid M] [module R M] :
  is_noetherian R M ↔ well_founded
    ((>) : { N : submodule R M // N.fg } → { N : submodule R M // N.fg } → Prop) :=
begin
  let α := { N : submodule R M // N.fg },
  split,
  { introI H,
    let f : α ↪o submodule R M := order_embedding.subtype _,
    exact order_embedding.well_founded f.dual (well_founded_submodule_gt _ _) },
  { intro H,
    constructor,
    intro N,
    obtain ⟨⟨N₀, h₁⟩, e : N₀ ≤ N, h₂⟩ := well_founded.well_founded_iff_has_max'.mp
      H { N' : α | N'.1 ≤ N } ⟨⟨⊥, submodule.fg_bot⟩, bot_le⟩,
    convert h₁,
    refine (e.antisymm _).symm,
    by_contra h₃,
    obtain ⟨x, hx₁ : x ∈ N, hx₂ : x ∉ N₀⟩ := set.not_subset.mp h₃,
    apply hx₂,
    have := h₂ ⟨(R ∙ x) ⊔ N₀, _⟩ _ _,
    { injection this with eq,
      rw ← eq,
      exact (le_sup_left : (R ∙ x) ≤ (R ∙ x) ⊔ N₀) (submodule.mem_span_singleton_self _) },
    { exact submodule.fg.sup ⟨{x}, by rw [finset.coe_singleton]⟩ h₁ },
    { exact sup_le ((submodule.span_singleton_le_iff_mem _ _).mpr hx₁) e },
    { show N₀ ≤ (R ∙ x) ⊔ N₀, from le_sup_right } }
end

lemma tfae [is_bezout R] [is_domain R] :
  tfae [is_noetherian_ring R,
    is_principal_ideal_ring R,
    unique_factorization_monoid R,
    wf_dvd_monoid R] :=
begin
  classical,
  tfae_have : 1 → 2,
  { introI H, exact ⟨λ I, is_principal_of_fg _ (is_noetherian.noetherian _)⟩ },
  tfae_have : 2 → 3,
  { introI _, apply_instance },
  tfae_have : 3 → 4,
  { introI _, apply_instance },
  tfae_have : 4 → 1,
  { rintro ⟨h⟩,
    rw [is_noetherian_ring_iff, is_noetherian_iff_fg_well_founded],
    apply rel_embedding.well_founded _ h,
    have : ∀ I : { J : ideal R // J.fg }, ∃ x : R, (I : ideal R) = ideal.span {x} :=
      λ ⟨I, hI⟩, (is_bezout.is_principal_of_fg I hI).1,
    choose f hf,
    exact
    { to_fun := f,
      inj' := λ x y e, by { ext1, rw [hf, hf, e] },
      map_rel_iff' := λ x y,
      by { dsimp, rw [← ideal.span_singleton_lt_span_singleton, ← hf, ← hf], refl } } },
  tfae_finish
end

end is_bezout
