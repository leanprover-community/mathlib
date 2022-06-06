/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import algebra.direct_sum.algebra
import algebra.direct_sum.internal
import algebra.direct_sum.ring
import group_theory.subgroup.basic

/-!
# Internally-graded rings and algebras

This file defines the typeclass `graded_algebra 𝒜`, for working with an algebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `graded_ring 𝒜`: the typeclass, which is a combination of `set_like.graded_monoid`, and
  a constructive version of `direct_sum.is_internal 𝒜`.
* `graded_ring.decompose : A ≃+*[R] ⨁ i, 𝒜 i`, which breaks apart an element of the ring into
  its constituent pieces.
* `graded_algebra 𝒜`: A convenience alias for `graded_ring` when `𝒜` is a family of submodules.
* `graded_algebra.decompose : A ≃ₐ[R] ⨁ i, 𝒜 i`, which breaks apart an element of the algebra into
  its constituent pieces.
* `graded_algebra.proj 𝒜 i` is the linear map from `A` to its degree `i : ι` component, such that
  `proj 𝒜 i x = decompose 𝒜 x i`.
* `graded_algebra.support 𝒜 r` is the `finset ι` containing the `i : ι` such that the degree `i`
  component of `r` is not zero.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `𝒜 : ι → submodule ℕ A` and `𝒜 : ι → submodule ℤ A` respectively, since all
`semiring`s are ℕ-algebras via `algebra_nat`, and all `ring`s are `ℤ`-algebras via `algebra_int`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/

open_locale direct_sum big_operators

variables {ι R A σ : Type*}
section graded_ring
variables [decidable_eq ι] [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ)

include A

/-- An internally-graded `R`-algebra `A` is one that can be decomposed into a collection
of `submodule R A`s indexed by `ι` such that the canonical map `A → ⨁ i, 𝒜 i` is bijective and
respects multiplication, i.e. the product of an element of degree `i` and an element of degree `j`
is an element of degree `i + j`.

Note that the fact that `A` is internally-graded, `graded_algebra 𝒜`, implies an externally-graded
algebra structure `direct_sum.galgebra R (λ i, ↥(𝒜 i))`, which in turn makes available an
`algebra R (⨁ i, 𝒜 i)` instance.
-/
class graded_ring (𝒜 : ι → σ) extends set_like.graded_monoid 𝒜 :=
(decompose' : A → ⨁ i, 𝒜 i)
(left_inv : function.left_inverse decompose' (direct_sum.coe_add_monoid_hom 𝒜))
(right_inv : function.right_inverse decompose' (direct_sum.coe_add_monoid_hom 𝒜))

variables [graded_ring 𝒜]

protected lemma graded_ring.is_internal : direct_sum.is_internal 𝒜 :=
⟨graded_ring.left_inv.injective, graded_ring.right_inv.surjective⟩

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
a ring to a direct sum of components. -/
def graded_ring.decompose : A ≃+* ⨁ i, 𝒜 i := ring_equiv.symm
{ to_fun := direct_sum.coe_ring_hom 𝒜,
  inv_fun := graded_ring.decompose',
  left_inv := graded_ring.left_inv,
  right_inv := graded_ring.right_inv,
  map_mul' := ring_hom.map_mul _,
  map_add' := ring_hom.map_add _ }

@[simp] lemma graded_ring.decompose'_def :
  graded_ring.decompose' = graded_ring.decompose 𝒜 := rfl

@[simp] lemma graded_ring.decompose_symm_of {i : ι} (x : 𝒜 i) :
  (graded_ring.decompose 𝒜).symm (direct_sum.of _ i x) = x :=
direct_sum.coe_ring_hom_of 𝒜 _ _

@[simp] lemma graded_ring.decompose_coe {i : ι} (x : 𝒜 i) :
  graded_ring.decompose 𝒜 (x : A) = direct_sum.of _ i x :=
by rw [←graded_ring.decompose_symm_of, ring_equiv.apply_symm_apply]

lemma graded_ring.decompose_of_mem {x : A} {i : ι} (hx : x ∈ 𝒜 i) :
  graded_ring.decompose 𝒜 x = direct_sum.of _ i (⟨x, hx⟩ : 𝒜 i) :=
graded_ring.decompose_coe _ ⟨x, hx⟩

lemma graded_ring.decompose_of_mem_same {x : A} {i : ι} (hx : x ∈ 𝒜 i) :
  (graded_ring.decompose 𝒜 x i : A) = x :=
by rw [graded_ring.decompose_of_mem _ hx, direct_sum.of_eq_same, subtype.coe_mk]

lemma graded_ring.decompose_of_mem_ne {x : A} {i j : ι} (hx : x ∈ 𝒜 i) (hij : i ≠ j):
  (graded_ring.decompose 𝒜 x j : A) = 0 :=
by rw [graded_ring.decompose_of_mem _ hx, direct_sum.of_eq_of_ne _ _ _ _ hij,
  add_submonoid_class.coe_zero]

/-- The projection maps of a graded ring -/
def graded_ring.proj (i : ι) : A →+ A :=
(add_submonoid_class.subtype (𝒜 i)).comp $
  (dfinsupp.eval_add_monoid_hom i).comp $
  ring_hom.to_add_monoid_hom $ ring_equiv.to_ring_hom $ graded_ring.decompose 𝒜

@[simp] lemma graded_ring.proj_apply (i : ι) (r : A) :
  graded_ring.proj 𝒜 i r = (graded_ring.decompose 𝒜 r : ⨁ i, 𝒜 i) i := rfl

lemma graded_ring.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
  graded_ring.proj 𝒜 i ((graded_ring.decompose 𝒜).symm a) =
  (graded_ring.decompose 𝒜).symm (direct_sum.of _ i (a i)) :=
by rw [graded_ring.proj_apply, graded_ring.decompose_symm_of, ring_equiv.apply_symm_apply]

/-- The support of `r` is the `finset` where `proj R A i r ≠ 0 ↔ i ∈ r.support`-/
def graded_ring.support [Π i (x : 𝒜 i), decidable (x ≠ 0)]
  (r : A) : finset ι :=
(graded_ring.decompose 𝒜 r).support

lemma graded_ring.sum_support_decompose [Π i (x : 𝒜 i), decidable (x ≠ 0)] (r : A) :
  ∑ i in graded_ring.support 𝒜 r, (graded_ring.decompose 𝒜 r i : A) = r :=
begin
  conv_rhs { rw [←(graded_ring.decompose 𝒜).symm_apply_apply r,
    ←direct_sum.sum_support_of _ (graded_ring.decompose 𝒜 r)] },
  rw [map_sum, graded_ring.support],
  simp_rw graded_ring.decompose_symm_of,
end

lemma graded_ring.mem_support_iff [Π i (x : 𝒜 i), decidable (x ≠ 0)] (r : A) (i : ι) :
  i ∈ graded_ring.support 𝒜 r ↔ graded_ring.proj 𝒜 i r ≠ 0 :=
begin
  rw [graded_ring.support, dfinsupp.mem_support_iff, graded_ring.proj_apply],
  simp only [ne.def, add_submonoid_class.coe_eq_zero, graded_ring.decompose'_def],
end

end graded_ring

section graded_algebra
variables [decidable_eq ι] [add_monoid ι] [comm_semiring R] [semiring A] [algebra R A]
variables (𝒜 : ι → submodule R A)

/-- A special case of `graded_ring` with `σ = submodule R A`. This is useful both because it
can avoid typeclass search, and because it provides a more concise name. -/
@[reducible]
def graded_algebra := graded_ring 𝒜

/-- A helper to construct a `graded_algebra` when the `set_like.graded_monoid` structure is already
available. This makes the `left_inv` condition easier to prove, and phrases the `right_inv`
condition in a way that allows custom `@[ext]` lemmas to apply.

See note [reducible non-instances]. -/
@[reducible]
def graded_algebra.of_alg_hom [set_like.graded_monoid 𝒜] (decompose : A →ₐ[R] ⨁ i, 𝒜 i)
  (right_inv : (direct_sum.coe_alg_hom 𝒜).comp decompose = alg_hom.id R A)
  (left_inv : ∀ i (x : 𝒜 i), decompose (x : A) = direct_sum.of (λ i, ↥(𝒜 i)) i x) :
  graded_algebra 𝒜 :=
{ decompose' := decompose,
  right_inv := alg_hom.congr_fun right_inv,
  left_inv := begin
    suffices : decompose.comp (direct_sum.coe_alg_hom 𝒜) = alg_hom.id _ _,
    from alg_hom.congr_fun this,
    ext i x : 2,
    exact (decompose.congr_arg $ direct_sum.coe_alg_hom_of _ _ _).trans (left_inv i x),
  end}

variable [graded_algebra 𝒜]

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
an algebra to a direct sum of components. -/
def graded_algebra.decompose : A ≃ₐ[R] ⨁ i, 𝒜 i := alg_equiv.symm
{ to_fun := direct_sum.coe_alg_hom 𝒜,
  inv_fun := graded_ring.decompose',
  left_inv := graded_ring.left_inv,
  right_inv := graded_ring.right_inv,
  map_mul' := alg_hom.map_mul _,
  map_add' := alg_hom.map_add _,
  commutes' := alg_hom.commutes _,
  .. graded_ring.decompose 𝒜 }

@[simp] lemma graded_algebra.decompose_def :
  ⇑(graded_ring.decompose 𝒜) = graded_algebra.decompose 𝒜 := rfl

@[simp] lemma graded_algebra.decompose_symm_of {i : ι} (x : 𝒜 i) :
  (graded_algebra.decompose 𝒜).symm (direct_sum.of _ i x) = x :=
direct_sum.coe_alg_hom_of 𝒜 _ _

@[simp] lemma graded_algebra.decompose_coe {i : ι} (x : 𝒜 i) :
  graded_algebra.decompose 𝒜 x = direct_sum.of _ i x :=
graded_ring.decompose_coe _ _

lemma graded_algebra.decompose_of_mem {x : A} {i : ι} (hx : x ∈ 𝒜 i) :
  graded_algebra.decompose 𝒜 x = direct_sum.of _ i (⟨x, hx⟩ : 𝒜 i) :=
graded_ring.decompose_of_mem _ _

lemma graded_algebra.decompose_of_mem_same {x : A} {i : ι} (hx : x ∈ 𝒜 i) :
  (graded_algebra.decompose 𝒜 x i : A) = x :=
graded_ring.decompose_of_mem_same _ hx

lemma graded_algebra.decompose_of_mem_ne {x : A} {i j : ι} (hx : x ∈ 𝒜 i) (hij : i ≠ j):
  (graded_algebra.decompose 𝒜 x j : A) = 0 :=
graded_ring.decompose_of_mem_ne _ hx hij

/-- The projection maps of graded algebra-/
def graded_algebra.proj (𝒜 : ι → submodule R A) [graded_algebra 𝒜] (i : ι) : A →ₗ[R] A :=
(𝒜 i).subtype.comp $
  (dfinsupp.lapply i).comp $
  (graded_algebra.decompose 𝒜).to_alg_hom.to_linear_map

@[simp] lemma graded_algebra.proj_apply (i : ι) (r : A) :
  graded_algebra.proj 𝒜 i r = (graded_algebra.decompose 𝒜 r : ⨁ i, 𝒜 i) i := rfl

lemma graded_algebra.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
  graded_algebra.proj 𝒜 i ((graded_algebra.decompose 𝒜).symm a) =
  (graded_algebra.decompose 𝒜).symm (direct_sum.of _ i (a i)) :=
graded_ring.proj_recompose _ _ _

/-- The support of `r` is the `finset` where `proj R A i r ≠ 0 ↔ i ∈ r.support`-/
def graded_algebra.support [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)] (r : A) : finset ι :=
@graded_ring.support _ _ _ _ _ _ _ _ 𝒜 _ ‹_› r

variable [Π (i : ι) (x : 𝒜 i), decidable (x ≠ 0)]

lemma graded_algebra.mem_support_iff (r : A) (i : ι) :
  i ∈ graded_algebra.support 𝒜 r ↔ graded_algebra.proj 𝒜 i r ≠ 0 :=
graded_ring.mem_support_iff _ _ _

lemma graded_algebra.sum_support_decompose (r : A) :
  ∑ i in graded_algebra.support 𝒜 r, (graded_algebra.decompose 𝒜 r i : A) = r :=
graded_ring.sum_support_decompose _ _

end graded_algebra

section canonical_order

open graded_ring set_like.graded_monoid direct_sum

variables [semiring A] [decidable_eq ι]
variables [canonically_ordered_add_monoid ι]
variables [set_like σ A] [add_submonoid_class σ A] (𝒜 : ι → σ) [graded_ring 𝒜]

/--
If `A` is graded by a canonically ordered add monoid, then the projection map `x ↦ x₀` is a ring
homomorphism.
-/
@[simps]
def graded_ring.proj_zero_ring_hom : A →+* A :=
{ to_fun := λ a, decompose 𝒜 a 0,
  map_one' := decompose_of_mem_same 𝒜 one_mem,
  map_zero' := by simp only [subtype.ext_iff, map_zero, zero_apply, add_submonoid_class.coe_zero],
  map_add' := λ _ _, by simp [subtype.ext_iff, map_add, add_apply, add_mem_class.coe_add],
  map_mul' := λ x y, begin
    -- Convert the abstract add_submonoid into a concrete one. This is necessary as there is no
    -- lattice structure on the abstract ones.
    let 𝒜' : ι → add_submonoid A :=
      λ i, (⟨𝒜 i, λ _ _, add_mem_class.add_mem, zero_mem_class.zero_mem _⟩ : add_submonoid A),
    letI : graded_ring 𝒜' :=
      { decompose' := (graded_ring.decompose' : A → ⨁ i, 𝒜 i),
        left_inv := graded_ring.left_inv,
        right_inv := graded_ring.right_inv,
        ..(by apply_instance : set_like.graded_monoid 𝒜), },
    have m : ∀ x, x ∈ supr 𝒜',
    { intro x,
      rw direct_sum.is_internal.add_submonoid_supr_eq_top 𝒜' (graded_ring.is_internal 𝒜'),
      exact add_submonoid.mem_top x },
    refine add_submonoid.supr_induction 𝒜' (m x) (λ i c hc, _) _ _,
    { refine add_submonoid.supr_induction 𝒜' (m y) (λ j c' hc', _) _ _,
      { by_cases h : i + j = 0,
        { rw [decompose_of_mem_same 𝒜 (show c * c' ∈ 𝒜 0, from h ▸ mul_mem hc hc'),
            decompose_of_mem_same 𝒜 (show c ∈ 𝒜 0, from (add_eq_zero_iff.mp h).1 ▸ hc),
            decompose_of_mem_same 𝒜 (show c' ∈ 𝒜 0, from (add_eq_zero_iff.mp h).2 ▸ hc')] },
        { rw [decompose_of_mem_ne 𝒜 (mul_mem hc hc') h],
          cases (show i ≠ 0 ∨ j ≠ 0, by rwa [add_eq_zero_iff, not_and_distrib] at h) with h' h',
          { simp only [decompose_of_mem_ne 𝒜 hc h', zero_mul] },
          { simp only [decompose_of_mem_ne 𝒜 hc' h', mul_zero] } } },
      { simp only [map_zero, zero_apply, add_submonoid_class.coe_zero, mul_zero], },
      { intros _ _ hd he,
        simp only [mul_add, map_add, add_apply, add_mem_class.coe_add, hd, he] } },
    { simp only [map_zero, zero_apply, add_submonoid_class.coe_zero, zero_mul] },
    { rintros _ _ ha hb, simp only [add_mul, map_add, add_apply, add_mem_class.coe_add, ha, hb] },
  end }

end canonical_order
