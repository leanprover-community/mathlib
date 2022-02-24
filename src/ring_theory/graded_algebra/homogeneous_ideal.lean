/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/

import ring_theory.ideal.basic
import ring_theory.ideal.operations
import linear_algebra.finsupp
import ring_theory.graded_algebra.basic

/-!
# Homogeneous ideals of a graded algebra

This file defines homogeneous ideals of `graded_algebra 𝒜` where `𝒜 : ι → submodule R A` and
operations on them.

## Main definitions

For any `I : ideal A`:
* `ideal.is_homogeneous 𝒜 I`: The property that an ideal is closed under `graded_algebra.proj`.
* `homogeneous_ideal 𝒜`: The subtype of ideals which satisfy `ideal.is_homogeneous`
* `ideal.homogeneous_core I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `ideal.homogeneous_hull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `homogeneous_ideal.complete_lattice`: `ideal.is_homogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `ideal.homogeneous_core.gi`: `ideal.homogeneous_core` forms a galois insertion with coercion.
* `ideal.homogeneous_hull.gi`: `ideal.homogeneous_hull` forms a galois insertion with coercion.

## Implementation notes

We introduce `ideal.homogeneous_core'` earlier than might be expected so that we can get access
to `ideal.is_homogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/

open set_like direct_sum set
open_locale big_operators pointwise direct_sum

variables {ι R A : Type*}

section homogeneous_def

variables [comm_semiring R] [semiring A] [algebra R A]
variables (𝒜 : ι → submodule R A)
variables [decidable_eq ι] [add_monoid ι] [graded_algebra 𝒜]
variable (I : ideal A)

/--An `I : ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`.-/
def ideal.is_homogeneous : Prop :=
∀ (i : ι) ⦃r : A⦄, r ∈ I → (graded_algebra.decompose 𝒜 r i : A) ∈ I

/-- For any `semiring A`, we collect the homogeneous ideals of `A` into a type. -/
abbreviation homogeneous_ideal : Type* := { I : ideal A // I.is_homogeneous 𝒜 }

end homogeneous_def

section homogeneous_core

variables [comm_semiring R] [semiring A] [algebra R A]
variables (𝒜 : ι → submodule R A)
variable (I : ideal A)

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def ideal.homogeneous_core' : ideal A :=
ideal.span (coe '' ((coe : subtype (is_homogeneous 𝒜) → A) ⁻¹' I))

lemma ideal.homogeneous_core'_mono : monotone (ideal.homogeneous_core' 𝒜) :=
λ I J I_le_J, ideal.span_mono $ set.image_subset _ $ λ x, @I_le_J _

lemma ideal.homogeneous_core'_le : I.homogeneous_core' 𝒜 ≤ I :=
ideal.span_le.2 $ image_preimage_subset _ _

end homogeneous_core

section is_homogeneous_ideal_defs

variables [comm_semiring R] [semiring A] [algebra R A]
variables (𝒜 : ι → submodule R A)
variables [decidable_eq ι] [add_monoid ι] [graded_algebra 𝒜]
variable (I : ideal A)

lemma ideal.is_homogeneous_iff_forall_subset :
  I.is_homogeneous 𝒜 ↔ ∀ i, (I : set A) ⊆ graded_algebra.proj 𝒜 i ⁻¹' I :=
iff.rfl

lemma ideal.is_homogeneous_iff_subset_Inter :
  I.is_homogeneous 𝒜 ↔ (I : set A) ⊆ ⋂ i, graded_algebra.proj 𝒜 i ⁻¹' ↑I :=
subset_Inter_iff.symm

lemma ideal.mul_homogeneous_element_mem_of_mem
  {I : ideal A} (r x : A) (hx₁ : is_homogeneous 𝒜 x) (hx₂ : x ∈ I) (j : ι) :
  graded_algebra.proj 𝒜 j (r * x) ∈ I :=
begin
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw [←graded_algebra.sum_support_decompose 𝒜 r, finset.sum_mul, linear_map.map_sum],
  apply ideal.sum_mem,
  intros k hk,
  obtain ⟨i, hi⟩ := hx₁,
  have mem₁ : (graded_algebra.decompose 𝒜 r k : A) * x ∈ 𝒜 (k + i) := graded_monoid.mul_mem
    (submodule.coe_mem _) hi,
  erw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem 𝒜 mem₁,
    coe_of_submodule_apply 𝒜, submodule.coe_mk],
  split_ifs,
  { exact I.mul_mem_left _ hx₂ },
  { exact I.zero_mem },
end

lemma ideal.is_homogeneous_span (s : set A) (h : ∀ x ∈ s, is_homogeneous 𝒜 x) :
  (ideal.span s).is_homogeneous 𝒜 :=
begin
  rintros i r hr,
  rw [ideal.span, finsupp.span_eq_range_total] at hr,
  rw linear_map.mem_range at hr,
  obtain ⟨s, rfl⟩ := hr,
  rw [←graded_algebra.proj_apply, finsupp.total_apply, finsupp.sum, linear_map.map_sum],
  refine ideal.sum_mem _ _,
  rintros z hz1,
  rw [smul_eq_mul],
  refine ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z _ _ i,
  { rcases z with ⟨z, hz2⟩,
    apply h _ hz2, },
  { exact ideal.subset_span z.2 },
end

/--For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`.-/
def ideal.homogeneous_core : homogeneous_ideal 𝒜 :=
⟨ideal.homogeneous_core' 𝒜 I,
  ideal.is_homogeneous_span _ _ (λ x h, by { rw [subtype.image_preimage_coe] at h, exact h.2 })⟩

lemma ideal.homogeneous_core_mono : monotone (ideal.homogeneous_core 𝒜) :=
ideal.homogeneous_core'_mono 𝒜

lemma ideal.coe_homogeneous_core_le : ↑(I.homogeneous_core 𝒜) ≤ I :=
ideal.homogeneous_core'_le 𝒜 I

variables {𝒜 I}

lemma ideal.is_homogeneous.coe_homogeneous_core_eq_self (h : I.is_homogeneous 𝒜) :
  ↑(I.homogeneous_core 𝒜) = I :=
begin
  apply le_antisymm (I.homogeneous_core'_le 𝒜) _,
  intros x hx,
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw ←graded_algebra.sum_support_decompose 𝒜 x,
  exact ideal.sum_mem _ (λ j hj, ideal.subset_span ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩),
end

@[simp] lemma homogeneous_ideal.homogeneous_core_coe_eq_self (I : homogeneous_ideal 𝒜) :
  (I : ideal A).homogeneous_core 𝒜 = I :=
subtype.coe_injective $ ideal.is_homogeneous.coe_homogeneous_core_eq_self I.prop

variables (𝒜 I)

lemma ideal.is_homogeneous.iff_eq : I.is_homogeneous 𝒜 ↔ ↑(I.homogeneous_core 𝒜) = I :=
⟨ λ hI, hI.coe_homogeneous_core_eq_self,
  λ hI, hI ▸ (ideal.homogeneous_core 𝒜 I).2 ⟩

lemma ideal.is_homogeneous.iff_exists :
  I.is_homogeneous 𝒜 ↔ ∃ (S : set (homogeneous_submonoid 𝒜)), I = ideal.span (coe '' S) :=
begin
  rw [ideal.is_homogeneous.iff_eq, eq_comm],
  exact ((set.image_preimage.compose (submodule.gi _ _).gc).exists_eq_l _).symm,
end

end is_homogeneous_ideal_defs

/-! ### Operations

In this section, we show that `ideal.is_homogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `homogeneous_ideal`. -/

section operations

section semiring

variables [comm_semiring R] [semiring A] [algebra R A]
variables [decidable_eq ι] [add_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]

namespace ideal.is_homogeneous

lemma bot : ideal.is_homogeneous 𝒜 ⊥ := λ i r hr,
begin
  simp only [ideal.mem_bot] at hr,
  rw [hr, alg_equiv.map_zero, zero_apply],
  apply ideal.zero_mem
end

lemma top : ideal.is_homogeneous 𝒜 ⊤ :=
λ i r hr, by simp only [submodule.mem_top]

variables {𝒜}

lemma inf {I J : ideal A} (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) :
  (I ⊓ J).is_homogeneous 𝒜 :=
λ i r hr, ⟨HI _ hr.1, HJ _ hr.2⟩

lemma Inf {ℐ : set (ideal A)} (h : ∀ I ∈ ℐ, ideal.is_homogeneous 𝒜 I) :
  (Inf ℐ).is_homogeneous 𝒜 :=
begin
  intros i x Hx,
  simp only [ideal.mem_Inf] at Hx ⊢,
  intros J HJ,
  exact h _ HJ _ (Hx HJ),
end

lemma sup {I J : ideal A} (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) :
  (I ⊔ J).is_homogeneous 𝒜 :=
begin
  rw iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  refine ⟨s₁ ∪ s₂, _⟩,
  rw [set.image_union],
  exact (submodule.span_union _ _).symm,
end

lemma Sup {ℐ : set (ideal A)} (Hℐ : ∀ (I ∈ ℐ), ideal.is_homogeneous 𝒜 I) :
  (Sup ℐ).is_homogeneous 𝒜 :=
begin
  simp_rw iff_exists at Hℐ ⊢,
  choose 𝓈 h𝓈 using Hℐ,
  refine ⟨⋃ I hI, 𝓈 I hI, _⟩,
  simp_rw [set.image_Union, ideal.span_Union, Sup_eq_supr],
  conv in (ideal.span _) { rw ←h𝓈 i x },
end

end ideal.is_homogeneous

variables {𝒜}

namespace homogeneous_ideal

instance : partial_order (homogeneous_ideal 𝒜) :=
partial_order.lift _ subtype.coe_injective

instance : has_mem A (homogeneous_ideal 𝒜) :=
{ mem := λ r I, r ∈ (I : ideal A) }

instance : has_bot (homogeneous_ideal 𝒜) :=
⟨⟨⊥, ideal.is_homogeneous.bot 𝒜⟩⟩

@[simp] lemma coe_bot : ↑(⊥ : homogeneous_ideal 𝒜) = (⊥ : ideal A) := rfl

@[simp] lemma eq_bot_iff (I : homogeneous_ideal 𝒜) : I = ⊥ ↔ (I : ideal A) = ⊥ :=
subtype.ext_iff

instance : has_top (homogeneous_ideal 𝒜) :=
⟨⟨⊤, ideal.is_homogeneous.top 𝒜⟩⟩

@[simp] lemma coe_top : ↑(⊤ : homogeneous_ideal 𝒜) = (⊤ : ideal A) := rfl

@[simp] lemma eq_top_iff (I : homogeneous_ideal 𝒜) : I = ⊤ ↔ (I : ideal A) = ⊤ :=
subtype.ext_iff

instance : has_inf (homogeneous_ideal 𝒜) :=
{ inf := λ I J, ⟨I ⊓ J, I.prop.inf J.prop⟩ }

@[simp] lemma coe_inf (I J : homogeneous_ideal 𝒜) : ↑(I ⊓ J) = (I ⊓ J : ideal A) := rfl

instance : has_Inf (homogeneous_ideal 𝒜) :=
{ Inf := λ ℐ, ⟨Inf (coe '' ℐ), ideal.is_homogeneous.Inf $ λ _ ⟨I, _, hI⟩, hI ▸ I.prop⟩ }

@[simp] lemma coe_Inf (ℐ : set (homogeneous_ideal 𝒜)) : ↑(Inf ℐ) = (Inf (coe '' ℐ) : ideal A) :=
rfl

@[simp] lemma coe_infi {ι' : Sort*} (s : ι' → homogeneous_ideal 𝒜) :
  ↑(⨅ i, s i) = ⨅ i, (s i : ideal A) :=
by rw [infi, infi, coe_Inf, ←set.range_comp]

instance : has_sup (homogeneous_ideal 𝒜) :=
{ sup := λ I J, ⟨I ⊔ J, I.prop.sup J.prop⟩ }

@[simp] lemma coe_sup (I J : homogeneous_ideal 𝒜) : ↑(I ⊔ J) = (I ⊔ J : ideal A) := rfl

instance : has_Sup (homogeneous_ideal 𝒜) :=
{ Sup := λ ℐ, ⟨Sup (coe '' ℐ), ideal.is_homogeneous.Sup $ λ _ ⟨I, _, hI⟩, hI ▸ I.prop⟩ }

@[simp] lemma coe_Sup (ℐ : set (homogeneous_ideal 𝒜)) : ↑(Sup ℐ) = (Sup (coe '' ℐ) : ideal A) :=
rfl

@[simp] lemma coe_supr {ι' : Sort*} (s : ι' → homogeneous_ideal 𝒜) :
  ↑(⨆ i, s i) = ⨆ i, (s i : ideal A) :=
by rw [supr, supr, coe_Sup, ←set.range_comp]

instance : complete_lattice (homogeneous_ideal 𝒜) :=
subtype.coe_injective.complete_lattice _ coe_sup coe_inf coe_Sup coe_Inf coe_top coe_bot

instance : has_add (homogeneous_ideal 𝒜) := ⟨(⊔)⟩

@[simp] lemma coe_add (I J : homogeneous_ideal 𝒜) : ↑(I + J) = (I + J : ideal A) := rfl

instance : inhabited (homogeneous_ideal 𝒜) := { default := ⊥ }

end homogeneous_ideal

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [algebra R A]
variables [decidable_eq ι] [add_monoid ι]
variables {𝒜 : ι → submodule R A} [graded_algebra 𝒜]
variable (I : ideal A)

lemma ideal.is_homogeneous.mul {I J : ideal A}
  (HI : I.is_homogeneous 𝒜) (HJ : J.is_homogeneous 𝒜) : (I * J).is_homogeneous 𝒜 :=
begin
  rw ideal.is_homogeneous.iff_exists at HI HJ ⊢,
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := ⟨HI, HJ⟩,
  rw ideal.span_mul_span',
  refine ⟨s₁ * s₂, congr_arg _ _⟩,
  exact (set.image_mul (submonoid.subtype _).to_mul_hom).symm,
end

variables {𝒜}

instance : has_mul (homogeneous_ideal 𝒜) :=
{ mul := λ I J, ⟨I * J, I.prop.mul J.prop⟩ }

@[simp] lemma homogeneous_ideal.coe_mul (I J : homogeneous_ideal 𝒜) :
  ↑(I * J) = (I * J : ideal A) := rfl

end comm_semiring

end operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/

section homogeneous_core

variables [comm_semiring R] [semiring A]
variables [algebra R A] [decidable_eq ι] [add_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable (I : ideal A)

lemma ideal.homogeneous_core.gc : galois_connection coe (ideal.homogeneous_core 𝒜) :=
λ I J, ⟨
  λ H, I.homogeneous_core_coe_eq_self ▸ ideal.homogeneous_core_mono 𝒜 H,
  λ H, le_trans H (ideal.homogeneous_core'_le _ _)⟩

/--`coe : homogeneous_ideal 𝒜 → ideal A` and `ideal.homogeneous_core 𝒜` forms a galois
coinsertion-/
def ideal.homogeneous_core.gi : galois_coinsertion coe (ideal.homogeneous_core 𝒜) :=
{ choice := λ I HI, ⟨I, le_antisymm (I.coe_homogeneous_core_le 𝒜) HI ▸ subtype.prop _⟩,
  gc := ideal.homogeneous_core.gc 𝒜,
  u_l_le := λ I, ideal.homogeneous_core'_le _ _,
  choice_eq := λ I H, le_antisymm H (I.coe_homogeneous_core_le _) }

lemma ideal.homogeneous_core_eq_Sup :
  I.homogeneous_core 𝒜 = Sup {J : homogeneous_ideal 𝒜 | ↑J ≤ I} :=
eq.symm $ is_lub.Sup_eq $ (ideal.homogeneous_core.gc 𝒜).is_greatest_u.is_lub

lemma ideal.homogeneous_core'_eq_Sup :
  I.homogeneous_core' 𝒜 = Sup {J : ideal A | J.is_homogeneous 𝒜 ∧ J ≤ I} :=
begin
  refine (is_lub.Sup_eq _).symm,
  apply is_greatest.is_lub,
  have coe_mono : monotone (coe : {I : ideal A // I.is_homogeneous 𝒜} → ideal A) := λ _ _, id,
  convert coe_mono.map_is_greatest (ideal.homogeneous_core.gc 𝒜).is_greatest_u using 1,
  simp only [subtype.coe_image, exists_prop, mem_set_of_eq, subtype.coe_mk],
end

end homogeneous_core

/-! ### Homogeneous hulls -/

section homogeneous_hull

variables [comm_semiring R] [semiring A]
variables [algebra R A] [decidable_eq ι] [add_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]
variable (I : ideal A)

/--For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_hull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
def ideal.homogeneous_hull : homogeneous_ideal 𝒜 :=
⟨ideal.span {r : A | ∃ (i : ι) (x : I), (graded_algebra.decompose 𝒜 x i : A) = r}, begin
  refine ideal.is_homogeneous_span _ _ (λ x hx, _),
  obtain ⟨i, x, rfl⟩ := hx,
  apply set_like.is_homogeneous_coe
end⟩

lemma ideal.le_coe_homogeneous_hull :
  I ≤ ideal.homogeneous_hull 𝒜 I :=
begin
  intros r hr,
  letI : Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0) := λ _ _, classical.dec _,
  rw [←graded_algebra.sum_support_decompose 𝒜 r],
  refine ideal.sum_mem _ _, intros j hj,
  apply ideal.subset_span, use j, use ⟨r, hr⟩, refl,
end

lemma ideal.homogeneous_hull_mono : monotone (ideal.homogeneous_hull 𝒜) := λ I J I_le_J,
begin
  apply ideal.span_mono,
  rintros r ⟨hr1, ⟨x, hx⟩, rfl⟩,
  refine ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩,
end

variables {I 𝒜}

lemma ideal.is_homogeneous.homogeneous_hull_eq_self (h : I.is_homogeneous 𝒜) :
  ↑(ideal.homogeneous_hull 𝒜 I) = I :=
begin
  apply le_antisymm _ (ideal.le_coe_homogeneous_hull _ _),
  apply (ideal.span_le).2,
  rintros _ ⟨i, x, rfl⟩,
  exact h _ x.prop,
end

@[simp] lemma homogeneous_ideal.homogeneous_hull_coe_eq_self (I : homogeneous_ideal 𝒜) :
  (I : ideal A).homogeneous_hull 𝒜 = I :=
subtype.coe_injective $ ideal.is_homogeneous.homogeneous_hull_eq_self I.prop

variables (I 𝒜)

lemma ideal.coe_homogeneous_hull_eq_supr :
  ↑(I.homogeneous_hull 𝒜) = ⨆ i, ideal.span (graded_algebra.proj 𝒜 i '' I) :=
begin
  rw ←ideal.span_Union,
  apply congr_arg ideal.span _,
  ext1,
  simp only [set.mem_Union, set.mem_image, mem_set_of_eq, graded_algebra.proj_apply,
    set_like.exists, exists_prop, subtype.coe_mk, set_like.mem_coe],
end

lemma ideal.homogeneous_hull_eq_supr :
  (I.homogeneous_hull 𝒜) =
  ⨆ i, ⟨ideal.span (graded_algebra.proj 𝒜 i '' I), ideal.is_homogeneous_span 𝒜 _
    (by {rintros _ ⟨x, -, rfl⟩, apply set_like.is_homogeneous_coe})⟩ :=
by { ext1, rw [ideal.coe_homogeneous_hull_eq_supr, homogeneous_ideal.coe_supr], refl, }

end homogeneous_hull

section galois_connection

variables [comm_semiring R] [semiring A]
variables [algebra R A] [decidable_eq ι] [add_monoid ι]
variables (𝒜 : ι → submodule R A) [graded_algebra 𝒜]

lemma ideal.homogeneous_hull.gc : galois_connection (ideal.homogeneous_hull 𝒜) coe :=
λ I J, ⟨
  le_trans (ideal.le_coe_homogeneous_hull _ _),
  λ H, J.homogeneous_hull_coe_eq_self ▸ ideal.homogeneous_hull_mono 𝒜 H⟩

/-- `ideal.homogeneous_hull 𝒜` and `coe : homogeneous_ideal 𝒜 → ideal A` forms a galois insertion-/
def ideal.homogeneous_hull.gi : galois_insertion (ideal.homogeneous_hull 𝒜) coe :=
{ choice := λ I H, ⟨I, le_antisymm H (I.le_coe_homogeneous_hull 𝒜) ▸ subtype.prop _⟩,
  gc := ideal.homogeneous_hull.gc 𝒜,
  le_l_u := λ I, ideal.le_coe_homogeneous_hull _ _,
  choice_eq := λ I H, le_antisymm (I.le_coe_homogeneous_hull 𝒜) H}

lemma ideal.homogeneous_hull_eq_Inf (I : ideal A) :
  ideal.homogeneous_hull 𝒜 I = Inf { J : homogeneous_ideal 𝒜 | I ≤ J } :=
eq.symm $ is_glb.Inf_eq $ (ideal.homogeneous_hull.gc 𝒜).is_least_l.is_glb

end galois_connection

section linear_ordered_cancel_add_comm_monoid

variables {ι : Type*} [linear_ordered_cancel_add_comm_monoid ι] [decidable_eq ι]
variables {R : Type*} [comm_ring R]
variables (A : ι → ideal R) [graded_algebra A]
variable [Π (I : homogeneous_ideal A) (x : R),
  decidable_pred (λ (i : ι), graded_algebra.proj A i x ∉ I)]
variable [Π (i : ι) (x : A i), decidable (x ≠ 0)]

lemma homogeneous_ideal.is_prime_iff
  (I : homogeneous_ideal A)
  (I_ne_top : I ≠ ⊤)
  (homogeneous_mem_or_mem : ∀ {x y : R},
    set_like.is_homogeneous A x → set_like.is_homogeneous A y
    → (x * y ∈ I.1 → x ∈ I.1 ∨ y ∈ I.1)) : ideal.is_prime I.1 :=
⟨λ rid, begin
  have rid' : I.val = (⊤ : homogeneous_ideal A).val,
  unfold has_top.top, simp only [rid], refl,
  apply I_ne_top, exact subtype.val_injective rid',
end, begin
  intros x y hxy, by_contradiction rid,
  obtain ⟨rid₁, rid₂⟩ := not_or_distrib.mp rid,
  set set₁ := (graded_algebra.support A x).filter (λ i, graded_algebra.proj A i x ∉ I) with set₁_eq,
  set set₂ := (graded_algebra.support A y).filter (λ i, graded_algebra.proj A i y ∉ I) with set₂_eq,
  have set₁_nonempty : set₁.nonempty,
  { replace rid₁ : ¬(∀ (i : ι), (graded_algebra.decompose A x i : R) ∈ I.val),
    { intros rid, apply rid₁, rw ←graded_algebra.sum_support_decompose A x,
      apply ideal.sum_mem, intros, apply rid, },
    rw [not_forall] at rid₁,
    obtain ⟨i, h⟩ := rid₁,
    refine ⟨i, _⟩, rw set₁_eq, simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
    refine ⟨_, h⟩, rw graded_algebra.mem_support_iff, intro rid₃,
    rw graded_algebra.proj_apply at rid₃, rw rid₃ at h,
    simp only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] at h, exact h, },
  have set₂_nonempty : set₂.nonempty,
  { replace rid₂ : ¬(∀ (i : ι), (graded_algebra.decompose A y i : R) ∈ I.val),
    { intros rid, apply rid₂, rw ←graded_algebra.sum_support_decompose A y,
      apply ideal.sum_mem, intros, apply rid, },
    rw [not_forall] at rid₂,
    obtain ⟨i, h⟩ := rid₂,
    refine ⟨i, _⟩, rw set₂_eq, simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
    refine ⟨_, h⟩, rw graded_algebra.mem_support_iff, intro rid₃,
    rw graded_algebra.proj_apply at rid₃, rw rid₃ at h,
    simp only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] at h, exact h, },
  set max₁ := set₁.max' set₁_nonempty with max₁_eq,
  set max₂ := set₂.max' set₂_nonempty with max₂_eq,
  have mem_max₁ := finset.max'_mem set₁ set₁_nonempty,
  rw [←max₁_eq, set₁_eq] at mem_max₁,
  have mem_max₂ := finset.max'_mem set₂ set₂_nonempty,
  rw [←max₂_eq, set₂_eq] at mem_max₂,
  replace hxy : ∀ (i : ι), (graded_algebra.decompose A (x * y) i : R) ∈ I.val,
  { intros i, apply I.2, exact hxy, },
  specialize hxy (max₁ + max₂),
  have eq :=
    calc  graded_algebra.proj A (max₁ + max₂) (x * y)
        = ∑ ij in ((graded_algebra.support A x).product (graded_algebra.support A y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂),
            (graded_algebra.proj A ij.1 x) * (graded_algebra.proj A ij.2 y)
        : _ --(0)
    ... = ∑ ij in ((graded_algebra.support A x).product (graded_algebra.support A y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂)
                    \ {(max₁, max₂)} ∪ {(max₁, max₂)},
            (graded_algebra.proj A ij.1 x) * (graded_algebra.proj A ij.2 y)
        : _ -- (1),
    ... = ∑ (ij : ι × ι) in ((graded_algebra.support A x).product
            (graded_algebra.support A y)).filter
            (λ (z : ι × ι), prod.fst z + z.snd = max₁ + max₂)
                    \ {(max₁, max₂)},
            (graded_algebra.proj A (prod.fst ij) x) * (graded_algebra.proj A ij.snd y)
        + ∑ ij in {(max₁, max₂)}, (graded_algebra.proj A (prod.fst ij) x)
            * (graded_algebra.proj A ij.snd y)
        : _ -- (2)
    ... = ∑ ij in ((graded_algebra.support A x).product (graded_algebra.support A y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂)
                    \ {(max₁, max₂)},
            (graded_algebra.proj A ij.1 x) * (graded_algebra.proj A ij.2 y)
        + _
        : by rw finset.sum_singleton,

  have eq₂ :
    (graded_algebra.proj A (max₁, max₂).fst) x * (graded_algebra.proj A (max₁, max₂).snd) y
          = graded_algebra.proj A (max₁ + max₂) (x * y)
          - ∑ (ij : ι × ι) in finset.filter (λ (z : ι × ι), z.fst + z.snd = max₁ + max₂)
              ((graded_algebra.support A x).product (graded_algebra.support A y)) \ {(max₁, max₂)},
              (graded_algebra.proj A ij.fst) x * (graded_algebra.proj A ij.snd) y,
  { rw eq, ring },

  have mem_I₂ : ∑ (ij : ι × ι) in finset.filter (λ (z : ι × ι), z.fst + z.snd = max₁ + max₂)
              ((graded_algebra.support A x).product (graded_algebra.support A y)) \ {(max₁, max₂)},
              (graded_algebra.proj A ij.fst) x * (graded_algebra.proj A ij.snd) y ∈ I,
  { apply ideal.sum_mem, rintros ⟨i, j⟩ H,
    simp only [not_and, prod.mk.inj_iff, finset.mem_sdiff, ne.def, dfinsupp.mem_support_to_fun,
       finset.mem_singleton, finset.mem_filter, finset.mem_product] at H,
    obtain ⟨⟨⟨H₁, H₂⟩, H₃⟩, H₄⟩ := H,
    cases lt_trichotomy i max₁,
    { -- in this case `i < max₁`, so `max₂ < j`, so `of A j (y j) ∈ I`
      have ineq : max₂ < j,
      { by_contra rid₂, rw not_lt at rid₂,
        have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
        conv_lhs at rid₃ { rw add_comm },
        conv_rhs at rid₃ { rw add_comm },
        rw H₃ at rid₃, exact lt_irrefl _ rid₃, },
      have not_mem_j : j ∉ set₂,
      { intro rid₂,
        rw max₂_eq at ineq,
        have rid₃ := (finset.max'_lt_iff set₂ set₂_nonempty).mp ineq j rid₂,
        exact lt_irrefl _ rid₃, },
      rw set₂_eq at not_mem_j,
      simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
        finset.mem_filter] at not_mem_j,
      specialize not_mem_j H₂,
      apply ideal.mul_mem_left,
      convert not_mem_j, },
    { cases h,
      { -- in this case `i = max₁`, so `max₂ = j`, contradictory
        have : j = max₂,
        { rw h at H₃,
          exact linear_ordered_cancel_add_comm_monoid.add_left_cancel _ _ _ H₃, },
        exfalso,
        exact H₄ h this, },
      { -- in this case `i > max₁`, so `i < max₁`, so `of A i (x i) ∈ I`
        have ineq : max₁ < i,
        { by_contra rid₂, rw not_lt at rid₂,
          have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
          conv_lhs at rid₃ { rw linear_ordered_cancel_add_comm_monoid.add_comm },
          exact lt_irrefl _ rid₃, },
        have not_mem_i : i ∉ set₁,
        { intro rid₂,
          rw max₁_eq at ineq,
          have rid₃ := (finset.max'_lt_iff set₁ set₁_nonempty).mp ineq i rid₂,
          exact lt_irrefl _ rid₃,},
        rw set₁_eq at not_mem_i,
        simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
          finset.mem_filter] at not_mem_i,
        specialize not_mem_i H₁,
        apply ideal.mul_mem_right,
        convert not_mem_i, }, } },
  have mem_I₃ :
    (graded_algebra.proj A (max₁, max₂).fst) x * (graded_algebra.proj A (max₁, max₂).snd) y ∈ I,
  { rw eq₂, apply ideal.sub_mem,
    have HI := I.2,
    specialize HI (max₁ + max₂) hxy, exact hxy, exact mem_I₂, },
  specialize homogeneous_mem_or_mem ⟨max₁, _⟩ ⟨max₂, _⟩ mem_I₃,
  rw [graded_algebra.proj_apply], exact submodule.coe_mem _,
  rw [graded_algebra.proj_apply], exact submodule.coe_mem _,
  cases homogeneous_mem_or_mem,
  simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
  refine mem_max₁.2 homogeneous_mem_or_mem,
  simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
  refine mem_max₂.2 homogeneous_mem_or_mem,

  -- (0)
  rw [graded_algebra.proj_apply, alg_equiv.map_mul, graded_algebra.support, graded_algebra.support,
       direct_sum.coe_mul_apply_submodule], refl,

  -- (1)
  congr, ext, split; intros H,
  { simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product] at H,
    rw finset.mem_union,
    by_cases a = (max₁, max₂),
    right, rw h, exact finset.mem_singleton_self (max₁, max₂),
    left, rw finset.mem_sdiff, split,
    simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
    exact H, intro rid, simp only [finset.mem_singleton] at rid, exact h rid, },
  { rw finset.mem_union at H, cases H,
    rw finset.mem_sdiff at H, exact H.1,
    simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
    simp only [finset.mem_singleton] at H, rw H,
    refine ⟨⟨_, _⟩, rfl⟩,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
    exact mem_max₁.1,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
    exact mem_max₂.1, },

  -- (2)
  rw [finset.sum_union],
  apply finset.disjoint_iff_inter_eq_empty.mpr,
  rw finset.eq_empty_iff_forall_not_mem, rintros ⟨i, j⟩ Hij,
  rw [finset.mem_inter, finset.mem_sdiff, finset.mem_filter] at Hij,
  simp only [not_and, prod.mk.inj_iff, ne.def, dfinsupp.mem_support_to_fun, finset.mem_singleton,
    finset.mem_product] at Hij,
  exact Hij.1.2 Hij.2.1 Hij.2.2,
end⟩

lemma homogeneous_ideal.rad_eq (I : homogeneous_ideal A) :
  I.1.radical = Inf {J | I.1 ≤ J ∧ ideal.is_homogeneous A J ∧ J.is_prime} :=
begin
  have subset₁ : I.1.radical ≤ Inf {J | I.1 ≤ J ∧ ideal.is_homogeneous A J ∧ J.is_prime},
  { rw ideal.radical_eq_Inf, intros x hx,
    rw [submodule.mem_Inf] at hx ⊢, intros J HJ, apply hx,
    obtain ⟨HJ₁, _, HJ₂⟩ := HJ,
    refine ⟨HJ₁, HJ₂⟩, },
  have subset₂ : Inf {J | I.1 ≤ J ∧ ideal.is_homogeneous A J ∧ J.is_prime} ≤ I.1.radical,
  { intros x hx,
    rw ideal.radical_eq_Inf,
    rw [submodule.mem_Inf] at hx ⊢,
    rintros J ⟨HJ₁, HJ₂⟩,
    specialize hx (ideal.homogeneous_core A J) _,
    refine ⟨_, ideal.is_homogeneous.homogeneous_core A _, _⟩,
    { have HI := I.2,
      rw [ideal.is_homogeneous.iff_eq] at HI,
      rw HI, apply ideal.span_mono, intros y hy,
      obtain ⟨hy₁, ⟨z, hz⟩⟩ := hy,
      specialize HJ₁ hy₁, refine ⟨⟨z, hz⟩, HJ₁⟩, },
    { set J' := ideal.homogeneous_core A J with eq_J',
      have homogeneity₀ := ideal.is_homogeneous.homogeneous_core A J,
      apply homogeneous_ideal.is_prime_iff A ⟨J', homogeneity₀⟩,
      intro rid,
      have rid' : J = ⊤,
      { have : J' ≤ J := ideal.homogeneous_core_le_ideal A J,
        simp only [homogeneous_ideal.eq_top_iff] at rid,
        rw rid at this, rw top_le_iff at this, exact this, },
      apply HJ₂.1, exact rid',
      rintros x y hx hy hxy,
      have H := HJ₂.mem_or_mem (ideal.homogeneous_core_le_ideal A J hxy),
      cases H,
      { left,
        have : ∀ i : ι, (graded_algebra.decompose A x i : R) ∈
          (⟨J', homogeneity₀⟩ : homogeneous_ideal A),
        { intros i, apply homogeneity₀, apply ideal.subset_span,
          simp only [set.mem_inter_eq, set_like.mem_coe, set.mem_set_of_eq],
          refine ⟨hx, H⟩, },
        rw ←graded_algebra.sum_support_decompose A x, apply ideal.sum_mem J',
        intros j hj, apply this, },
      { right,
        have : ∀ i : ι, (graded_algebra.decompose A y i : R) ∈
          (⟨J', homogeneity₀⟩ : homogeneous_ideal A),
        { intros i, apply homogeneity₀, apply ideal.subset_span,
          simp only [set.mem_inter_eq, set_like.mem_coe, set.mem_set_of_eq],
          refine ⟨hy, H⟩, }, rw ←graded_algebra.sum_support_decompose A y, apply ideal.sum_mem J',
        intros j hj, apply this, }, },
      refine (ideal.homogeneous_core_le_ideal A J) hx, },

  ext x, split; intro hx,
  exact subset₁ hx, exact subset₂ hx,
end

lemma homogeneous_ideal.rad (I : homogeneous_ideal A)  :
  ideal.is_homogeneous A I.1.radical :=
begin
  have radI_eq := homogeneous_ideal.rad_eq A I,
  rw radI_eq,
  have : Inf {J : ideal R | I.val ≤ J ∧ ideal.is_homogeneous A J ∧ J.is_prime} =
  (Inf {J : homogeneous_ideal A | I.1 ≤ J.1 ∧ J.1.is_prime }).1,
  simp only [subtype.coe_le_coe, subtype.val_eq_coe], congr, ext J, split; intro H,
  { use ⟨J, H.2.1⟩, split, refine ⟨H.1, H.2.2⟩, refl, },
  { obtain ⟨K, ⟨⟨HK₁, HK₂⟩, HK₃⟩⟩ := H,
    split, convert HK₁, rw ←HK₃, split,
    rw ←HK₃, exact K.2, rw ←HK₃, exact HK₂, },
  rw this,
  refine (Inf {J : homogeneous_ideal A | I.val ≤ J.val ∧ J.val.is_prime}).2,
end

end linear_ordered_cancel_add_comm_monoid
