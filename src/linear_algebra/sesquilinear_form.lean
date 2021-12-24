/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
import algebra.module.linear_map
import linear_algebra.bilinear_map
import linear_algebra.matrix.basis

/-!
# Sesquilinear form

This file defines a sesquilinear form over a module. The definition requires a ring antiautomorphism
on the scalar ring. Basic ideas such as
orthogonality are also introduced.

A sesquilinear form on an `R`-module `M`, is a function from `M × M` to `R`, that is linear in the
first argument and antilinear in the second, with respect to an antiautomorphism on `R` (an
antiisomorphism from `R` to `R`).

## Notations

Given any term `S` of type `sesq_form`, due to a coercion, can use the notation `S x y` to
refer to the function field, ie. `S x y = S.sesq x y`.

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form,
-/

open_locale big_operators

namespace linear_map

section comm_ring

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variables {R : Type*} {M : Type*} [comm_semiring R] [add_comm_monoid M] [module R M]
  {I : R →+* R}

/-- The proposition that two elements of a sesquilinear form space are orthogonal -/
def is_ortho (B : M →ₗ[R] M →ₛₗ[I] R) (x y) : Prop := B x y = 0

lemma is_ortho_def {B : M →ₗ[R] M →ₛₗ[I] R} {x y : M} :
  B.is_ortho x y ↔ B x y = 0 := iff.rfl

lemma is_ortho_zero_left (B : M →ₗ[R] M →ₛₗ[I] R) (x) : is_ortho B (0 : M) x :=
  by { dunfold is_ortho, rw [ map_zero B, zero_apply] }

lemma is_ortho_zero_right (B : M →ₗ[R] M →ₛₗ[I] R) (x) : is_ortho B x (0 : M) :=
  map_zero (B x)

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`bilin_form.is_ortho` -/
def is_Ortho {n : Type*} (B : M →ₗ[R] M →ₛₗ[I] R) (v : n → M) : Prop :=
pairwise (B.is_ortho on v)

lemma is_Ortho_def {n : Type*} {B : M →ₗ[R] M →ₛₗ[I] R} {v : n → M} :
  B.is_Ortho v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 := iff.rfl

end comm_ring
section is_domain

variables {R : Type*} {M : Type*} [comm_ring R] [is_domain R] [add_comm_group M]
  [module R M]
  {I : R ≃+* R}
  {B : M →ₗ[R] M →ₛₗ[I.to_ring_hom] R}
variables {V : Type*} {K : Type*} [field K] [add_comm_group V] [module K V]
  {J : K →+* K}


lemma ortho_smul_left {x y} {a : R} (ha : a ≠ 0) : (is_ortho B x y) ↔ (is_ortho B (a • x) y) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [map_smul₂, H, smul_zero]},
  { rw [map_smul₂, smul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }}
end

lemma ortho_smul_right {x y} {a : R} {ha : a ≠ 0} : (is_ortho B x y) ↔ (is_ortho B x (a • y)) :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [map_smulₛₗ, H, smul_zero] },
  { rw [map_smulₛₗ, smul_eq_zero] at H,
    cases H,
    { simp[ring_equiv.to_ring_hom_eq_coe] at H,
      exfalso,
      exact ha H },
    { exact H }}
end

/-- A set of orthogonal vectors `v` with respect to some sesquilinear form `B` is linearly
  independent if for all `i`, `B (v i) (v i) ≠ 0`. -/
lemma linear_independent_of_is_Ortho
  {n : Type*} {B : V →ₗ[K] V →ₛₗ[J] K} {v : n → V}
  (hv₁ : B.is_Ortho v) (hv₂ : ∀ i, ¬ B.is_ortho (v i) (v i)) :
  linear_independent K v :=
begin
  classical,
  rw linear_independent_iff',
  intros s w hs i hi,
  have : B (s.sum $ λ (i : n), w i • v i) (v i) = 0,
  { rw [hs, map_zero, zero_apply] },
  have hsum : s.sum (λ (j : n), w j * B (v j) (v i)) = w i * B (v i) (v i),
  { apply finset.sum_eq_single_of_mem i hi,
    intros j hj hij,
    rw [is_Ortho_def.1 hv₁ _ _ hij, mul_zero], },
  simp_rw [B.map_sum₂, map_smul₂, smul_eq_mul, hsum] at this,
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this,
end

end is_domain

variables {R : Type*} {M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  {I : R →+* R}
  {B : M →ₗ[R] M →ₛₗ[I] R}

/-- The proposition that a sesquilinear form is reflexive -/
def is_refl (B : M →ₗ[R] M →ₛₗ[I] R) : Prop :=
  ∀ (x y), B x y = 0 → B y x = 0

namespace is_refl

variable (H : B.is_refl)

lemma eq_zero : ∀ {x y}, B x y = 0 → B y x = 0 := λ x y, H x y

lemma ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x := ⟨eq_zero H, eq_zero H⟩

end is_refl

/-- The proposition that a sesquilinear form is symmetric -/
def is_symm (B : M →ₗ[R] M →ₛₗ[I] R) : Prop :=
  ∀ (x y), (I (B x y)) = B y x

namespace is_symm

variable (H : B.is_symm)
include H

protected lemma eq (x y) : (I (B x y)) = B y x := H x y

lemma is_refl : B.is_refl := λ x y H1, by { rw [←H], simp [H1] }

lemma ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x := H.is_refl.ortho_comm

end is_symm

/-- The proposition that a sesquilinear form is alternating -/
def is_alt (B : M →ₗ[R] M →ₛₗ[I] R) : Prop := ∀ (x : M), B x x = 0

namespace is_alt

variable (H : B.is_alt)
include H

lemma self_eq_zero (x) : B x x = 0 := H x

lemma neg (x y) : - B x y = B y x :=
begin
  have H1 : B (y + x) (y + x) = 0,
  { exact self_eq_zero H (y + x) },
  simp [map_add, self_eq_zero H] at H1,
  rw [add_eq_zero_iff_neg_eq] at H1,
  exact H1,
end

lemma is_refl : B.is_refl :=
begin
  intros x y h,
  rw [← neg H, h, neg_zero],
end

lemma ortho_comm {x y} : is_ortho B x y ↔ is_ortho B y x := H.is_refl.ortho_comm

end is_alt


section orthogonal

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonal (B : M →ₗ[R] M →ₛₗ[I] R) (N : submodule R M) : submodule R M :=
{ carrier := { m | ∀ n ∈ N, is_ortho B n m },
  zero_mem' := λ x _, B.is_ortho_zero_right x,
  add_mem' := λ x y hx hy n hn,
    by rw [is_ortho, map_add, show B n x = 0, by exact hx n hn,
        show B n y = 0, by exact hy n hn, zero_add],
  smul_mem' := λ c x hx n hn,
    by rw [is_ortho, map_smulₛₗ, show B n x = 0, by exact hx n hn, smul_zero] }

variables {N L : submodule R M}

@[simp] lemma mem_orthogonal_iff {N : submodule R M} {m : M} :
  m ∈ B.orthogonal N ↔ ∀ n ∈ N, is_ortho B n m := iff.rfl

lemma orthogonal_le (h : N ≤ L) : B.orthogonal L ≤ B.orthogonal N :=
λ _ hn l hl, hn l (h hl)

lemma le_orthogonal_orthogonal (b : B.is_refl) :
  N ≤ B.orthogonal (B.orthogonal N) :=
λ n hn m hm, b _ _ (hm n hn)

variables {V : Type*} {K : Type*} [field K] [add_comm_group V] [module K V]
  {J : K ≃+* K} {J₁ : K →+* K}


-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
lemma span_singleton_inf_orthogonal_eq_bot
  {B : V →ₗ[K] V →ₛₗ[J.to_ring_hom] K} {x : V} (hx : ¬ B.is_ortho x x) :
  (K ∙ x) ⊓ B.orthogonal (K ∙ x) = ⊥ :=
begin
  rw ← finset.coe_singleton,
  refine eq_bot_iff.2 (λ y h, _),
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩,
  have := h.2 x _,
  { rw finset.sum_singleton at this ⊢,
    suffices hμzero : μ x = 0,
    { rw [hμzero, zero_smul, submodule.mem_bot] },
    change B x (μ x • x) = 0 at this, rw [map_smulₛₗ, smul_eq_mul] at this,
    exact or.elim (zero_eq_mul.mp this.symm)
    (λ y, by { simp[ring_equiv.to_ring_hom_eq_coe] at y, exact y })
    (λ hfalse, false.elim $ hx hfalse) },
  { rw submodule.mem_span; exact λ _ hp, hp $ finset.mem_singleton_self _ }
end

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
lemma orthogonal_span_singleton_eq_to_lin_ker {B : V →ₗ[K] V →ₛₗ[J₁] K} (x : V) :
  B.orthogonal (K ∙ x) = (B x).ker :=
begin
  ext y,
  simp_rw [mem_orthogonal_iff, linear_map.mem_ker,
           submodule.mem_span_singleton ],
  split,
  { exact λ h, h x ⟨1, one_smul _ _⟩ },
  { rintro h _ ⟨z, rfl⟩,
    rw [is_ortho, map_smulₛₗ₂, smul_eq_zero],
    exact or.intro_right _ h }
end


-- todo: Generalize this to sesquilinear maps
lemma span_singleton_sup_orthogonal_eq_top {B : V →ₗ[K] V →ₗ[K] K}
  {x : V} (hx : ¬ B.is_ortho x x) :
  (K ∙ x) ⊔ B.orthogonal (K ∙ x) = ⊤ :=
begin
  rw orthogonal_span_singleton_eq_to_lin_ker,
  exact (B x).span_singleton_sup_ker_eq_top hx,
end


-- todo: Generalize this to sesquilinear maps
/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
lemma is_compl_span_singleton_orthogonal {B : V →ₗ[K] V →ₗ[K] K}
  {x : V} (hx : ¬ B.is_ortho x x) : is_compl (K ∙ x) (B.orthogonal $ K ∙ x) :=
{ inf_le_bot := eq_bot_iff.1 $
    (@span_singleton_inf_orthogonal_eq_bot _ _ _ _ _ (ring_equiv.refl K) B x hx),
  top_le_sup := eq_top_iff.1 $ span_singleton_sup_orthogonal_eq_top hx }

end orthogonal

end linear_map
