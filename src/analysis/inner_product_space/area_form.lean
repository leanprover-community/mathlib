/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.dual
import analysis.inner_product_space.orientation
import tactic.polyrith


noncomputable theory

open_locale real_inner_product_space complex_conjugate
open finite_dimensional

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

section foo
variables {R R₂ E E₂ : Type*} [semiring R] [semiring R₂]
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
  [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  [seminormed_add_comm_group E] [seminormed_add_comm_group E₂] [module R E] [module R₂ E₂]

def linear_isometry_equiv.of_linear_isometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
  (h₁ : f.to_linear_map.comp g = linear_map.id) (h₂ : g.comp f.to_linear_map = linear_map.id) :
  E ≃ₛₗᵢ[σ₁₂] E₂ :=
{ norm_map' := λ x, f.norm_map x,
  .. linear_equiv.of_linear f.to_linear_map g h₁ h₂ }

@[simp] lemma linear_isometry_equiv.coe_of_linear_isometry (f : E →ₛₗᵢ[σ₁₂] E₂) (g : E₂ →ₛₗ[σ₂₁] E)
  (h₁ : f.to_linear_map.comp g = linear_map.id) (h₂ : g.comp f.to_linear_map = linear_map.id) :
  (linear_isometry_equiv.of_linear_isometry f g h₁ h₂ : E → E₂) = (f : E → E₂) :=
rfl

@[simp] lemma linear_isometry_equiv.coe_of_linear_isometry_symm (f : E →ₛₗᵢ[σ₁₂] E₂)
  (g : E₂ →ₛₗ[σ₂₁] E) (h₁ : f.to_linear_map.comp g = linear_map.id)
  (h₂ : g.comp f.to_linear_map = linear_map.id) :
  ((linear_isometry_equiv.of_linear_isometry f g h₁ h₂).symm : E₂ → E) = (g : E₂ → E) :=
rfl

end foo

variables {E : Type*} [inner_product_space ℝ E] [fact (finrank ℝ E = 2)]
  (o : orientation ℝ E (fin 2))

include o

namespace orientation

/-- An antisymmetric bilinear form `E →ₗ[ℝ] E →ₗ[ℝ] ℝ` on an oriented real inner product space of
dimension 2 (usual notation `ω`).  When evaluated on two vectors, it gives the oriented area of the
parallelogram they span. -/
def area_form : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
begin
  let z : alternating_map ℝ E ℝ (fin 0) ≃ₗ[ℝ] ℝ :=
    alternating_map.const_linear_equiv_of_is_empty.symm,
  let y : alternating_map ℝ E ℝ (fin 1) →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (linear_map.llcomp ℝ E (alternating_map ℝ E ℝ (fin 0)) ℝ z) ∘ₗ
      alternating_map.curry_left_linear_map,
  exact y ∘ₗ (alternating_map.curry_left_linear_map o.volume_form),
end

local notation `ω` := o.area_form

lemma area_form_to_volume_form (x y : E) : ω x y = o.volume_form ![x, y] := by simp [area_form]

attribute [irreducible] area_form

@[simp] lemma area_form_apply_self (x : E) : ω x x = 0 :=
begin
  rw area_form_to_volume_form,
  refine o.volume_form.map_eq_zero_of_eq ![x, x] _ (_ : (0 : fin 2) ≠ 1),
  { simp },
  { norm_num }
end

lemma area_form_swap (x y : E) : ω x y = - ω y x :=
begin
  simp only [area_form_to_volume_form],
  convert o.volume_form.map_swap ![y, x] (_ : (0 : fin 2) ≠ 1),
  { ext i,
    fin_cases i; refl },
  { norm_num }
end

@[simp] lemma area_form_neg_orientation : (-o).area_form = -o.area_form :=
begin
  ext x y,
  simp [area_form_to_volume_form]
end

/-- Continuous linear map version of `orientation.area_form`, useful for calculus. -/
def area_form' : E →L[ℝ] (E →L[ℝ] ℝ) :=
((↑(linear_map.to_continuous_linear_map : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)))
  ∘ₗ o.area_form).to_continuous_linear_map

@[simp] lemma area_form'_apply (x : E) :
  o.area_form' x = (o.area_form x).to_continuous_linear_map :=
rfl

lemma abs_area_form_le (x y : E) : |ω x y| ≤ ∥x∥ * ∥y∥ :=
by simpa [area_form_to_volume_form, fin.prod_univ_succ] using o.abs_volume_form_apply_le ![x, y]

lemma area_form_le (x y : E) : ω x y ≤ ∥x∥ * ∥y∥ :=
by simpa [area_form_to_volume_form, fin.prod_univ_succ] using o.volume_form_apply_le ![x, y]

lemma abs_area_form_of_orthogonal {x y : E} (h : ⟪x, y⟫ = 0) : |ω x y| = ∥x∥ * ∥y∥ :=
begin
  rw [o.area_form_to_volume_form, o.abs_volume_form_apply_of_pairwise_orthogonal],
  { simp [fin.prod_univ_succ] },
  intros i j hij,
  fin_cases i; fin_cases j,
  { simpa },
  { simpa using h },
  { simpa [real_inner_comm] using h },
  { simpa }
end

/- Auxiliary construction for `orientation.almost_complex`, rotation by 90 degrees in an oriented
real inner product space of dimension 2. -/
def almost_complex_aux₁ : E →ₗ[ℝ] E :=
let to_dual : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) :=
  (inner_product_space.to_dual ℝ E).to_linear_equiv ≪≫ₗ linear_map.to_continuous_linear_map.symm in
↑to_dual.symm ∘ₗ ω

@[simp] lemma inner_almost_complex_aux₁_left (x y : E) : ⟪o.almost_complex_aux₁ x, y⟫ = ω x y :=
by simp [almost_complex_aux₁]

attribute [irreducible] almost_complex_aux₁

@[simp] lemma inner_almost_complex_aux₁_right (x y : E) : ⟪x, o.almost_complex_aux₁ y⟫ = - ω x y :=
begin
  rw real_inner_comm,
  simp [o.area_form_swap y x],
end

/- Auxiliary construction for `orientation.almost_complex`, rotation by 90 degrees in an oriented
real inner product space of dimension 2. -/
def almost_complex_aux₂ : E →ₗᵢ[ℝ] E :=
{ norm_map' := λ x, begin
    dsimp,
    refine le_antisymm _ _,
    { cases eq_or_lt_of_le (norm_nonneg (o.almost_complex_aux₁ x)) with h h,
      { rw ← h,
        positivity },
      refine le_of_mul_le_mul_right' _ h,
      rw [← real_inner_self_eq_norm_mul_norm, o.inner_almost_complex_aux₁_left],
      exact o.area_form_le x (o.almost_complex_aux₁ x) },
    { let K : submodule ℝ E := ℝ ∙ x,
      haveI : nontrivial Kᗮ,
      { apply @finite_dimensional.nontrivial_of_finrank_pos ℝ,
        have : finrank ℝ K ≤ finset.card {x},
        { rw ← set.to_finset_singleton,
          exact finrank_span_le_card ({x} : set E) },
        have : finset.card {x} = 1 := finset.card_singleton x,
        have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal,
        have : finrank ℝ E = 2 := fact.out _,
        linarith },
      obtain ⟨w, hw₀⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0,
      have hw' : ⟪x, (w:E)⟫ = 0 := inner_right_of_mem_orthogonal_singleton x w.2, -- hw'₀,
      have hw : (w:E) ≠ 0 := λ h, hw₀ (submodule.coe_eq_zero.mp h),
      refine le_of_mul_le_mul_right' _ (by rwa norm_pos_iff : 0 < ∥(w:E)∥),
      rw ← o.abs_area_form_of_orthogonal hw',
      rw ← o.inner_almost_complex_aux₁_left x w,
      exact abs_real_inner_le_norm (o.almost_complex_aux₁ x) w },
  end,
  .. o.almost_complex_aux₁ }

@[simp] lemma almost_complex_aux₁_almost_complex_aux₁ (x : E) :
  o.almost_complex_aux₁ (o.almost_complex_aux₁ x) = - x :=
begin
  apply ext_inner_left ℝ,
  intros y,
  have : ⟪o.almost_complex_aux₁ y, o.almost_complex_aux₁ x⟫ = ⟪y, x⟫ :=
    linear_isometry.inner_map_map o.almost_complex_aux₂ y x,
  rw [o.inner_almost_complex_aux₁_right, ← o.inner_almost_complex_aux₁_left, this, inner_neg_right],
end

/-- An isometric automorphism of an oriented real inner product space of dimension 2 (usual notation
`J`). This automorphism squares to -1.  We will define rotations in such a way that this
automorphism is equal to rotation by 90 degrees. -/
def almost_complex : E ≃ₗᵢ[ℝ] E :=
linear_isometry_equiv.of_linear_isometry
  o.almost_complex_aux₂
  (-o.almost_complex_aux₁)
  (by ext; simp [almost_complex_aux₂])
  (by ext; simp [almost_complex_aux₂])

local notation `J` := o.almost_complex

@[simp] lemma inner_almost_complex_left (x y : E) : ⟪J x, y⟫ = ω x y :=
o.inner_almost_complex_aux₁_left x y

@[simp] lemma inner_almost_complex_right (x y : E) : ⟪x, J y⟫ = - ω x y :=
o.inner_almost_complex_aux₁_right x y

@[simp] lemma almost_complex_almost_complex (x : E) : J (J x) = - x :=
o.almost_complex_aux₁_almost_complex_aux₁ x

@[simp] lemma almost_complex_symm :
  linear_isometry_equiv.symm J = linear_isometry_equiv.trans J (linear_isometry_equiv.neg ℝ) :=
linear_isometry_equiv.to_linear_isometry_injective rfl

attribute [irreducible] almost_complex

@[simp] lemma inner_almost_complex_self (x : E) : ⟪J x, x⟫ = 0 := by simp

lemma inner_almost_complex_swap (x y : E) : ⟪x, J y⟫ = - ⟪J x, y⟫ := by simp

lemma inner_almost_complex_swap' (x y : E) : ⟪J x, y⟫ = - ⟪x, J y⟫ :=
by simp [o.inner_almost_complex_swap x y]

lemma inner_comp_almost_complex (x y : E) : ⟪J x, J y⟫ = ⟪x, y⟫ :=
linear_isometry_equiv.inner_map_map J x y

@[simp] lemma area_form_almost_complex_left (x y : E) : ω (J x) y = - ⟪x, y⟫ :=
by rw [← o.inner_comp_almost_complex, o.inner_almost_complex_right, neg_neg]

@[simp] lemma area_form_almost_complex_right (x y : E) : ω x (J y) = ⟪x, y⟫ :=
by rw [← o.inner_almost_complex_left, o.inner_comp_almost_complex]

@[simp] lemma almost_complex_trans_almost_complex :
  linear_isometry_equiv.trans J J = linear_isometry_equiv.neg ℝ :=
by ext; simp

@[simp] lemma almost_complex_neg_orientation (x : E) :
  (-o).almost_complex x = - o.almost_complex x :=
begin
  apply ext_inner_right ℝ,
  intros y,
  rw inner_almost_complex_left,
  simp
end

@[simp] lemma almost_complex_trans_neg_orientation :
  (-o).almost_complex = o.almost_complex.trans (linear_isometry_equiv.neg ℝ) :=
linear_isometry_equiv.ext $ o.almost_complex_neg_orientation

/-- For a nonzero vector `x` in an oriented two-dimensional real inner product space `E`,
`![x, J x]` forms an (orthogonal) basis for `E`. -/
def basis_almost_complex (x : E) (hx : x ≠ 0) : basis (fin 2) ℝ E :=
@basis_of_linear_independent_of_card_eq_finrank _ _ _ _ _ _ _ _ ![x, J x]
(linear_independent_of_ne_zero_of_inner_eq_zero (λ i, by { fin_cases i; simp [hx] })
  begin
    intros i j hij,
    fin_cases i; fin_cases j,
    { simpa },
    { simp },
    { simp },
    { simpa }
  end)
(fact.out (finrank ℝ E = 2)).symm

@[simp] lemma coe_basis_almost_complex (x : E) (hx : x ≠ 0) :
  ⇑(o.basis_almost_complex x hx) = ![x, J x] :=
coe_basis_of_linear_independent_of_card_eq_finrank _ _

lemma inner_mul_inner_add_area_form_mul_area_form' (a x : E) :
  ⟪a, x⟫ • @innerₛₗ ℝ _ _ _ a + ω a x • ω a = ∥a∥ ^ 2 • @innerₛₗ ℝ _ _ _ x :=
begin
  by_cases ha : a = 0,
  { simp [ha] },
  apply (o.basis_almost_complex a ha).ext,
  intros i,
  fin_cases i,
  { simp only [real_inner_self_eq_norm_sq, algebra.id.smul_eq_mul, innerₛₗ_apply,
      linear_map.smul_apply, linear_map.add_apply, matrix.cons_val_zero, o.coe_basis_almost_complex,
      o.area_form_apply_self, real_inner_comm],
    ring },
  { simp only [real_inner_self_eq_norm_sq, algebra.id.smul_eq_mul, innerₛₗ_apply,
      linear_map.smul_apply, neg_inj, linear_map.add_apply, matrix.cons_val_one, matrix.head_cons,
      o.coe_basis_almost_complex, o.area_form_almost_complex_right, o.area_form_apply_self,
      o.inner_almost_complex_right],
    rw o.area_form_swap,
    ring, }
end

lemma inner_mul_inner_add_area_form_mul_area_form (a x y : E) :
  ⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ∥a∥ ^ 2 * ⟪x, y⟫ :=
congr_arg (λ f : E →ₗ[ℝ] ℝ, f y) (o.inner_mul_inner_add_area_form_mul_area_form' a x)

lemma inner_sq_add_area_form_sq (a b : E) : ⟪a, b⟫ ^ 2 + ω a b ^ 2 = ∥a∥ ^ 2 * ∥b∥ ^ 2 :=
by simpa [sq, real_inner_self_eq_norm_sq] using o.inner_mul_inner_add_area_form_mul_area_form a b b

lemma inner_mul_area_form_sub' (a x : E) :
  ⟪a, x⟫ • ω a - ω a x • @innerₛₗ ℝ _ _ _ a = ∥a∥ ^ 2 • ω x :=
begin
  by_cases ha : a = 0,
  { simp [ha] },
  apply (o.basis_almost_complex a ha).ext,
  intros i,
  fin_cases i,
  { simp only [o.coe_basis_almost_complex, o.area_form_apply_self, o.area_form_swap a x,
      real_inner_self_eq_norm_sq, algebra.id.smul_eq_mul, innerₛₗ_apply, linear_map.sub_apply,
      linear_map.smul_apply, matrix.cons_val_zero],
    ring },
  { simp only [o.area_form_almost_complex_right, o.area_form_apply_self, o.coe_basis_almost_complex,
      o.inner_almost_complex_right, real_inner_self_eq_norm_sq, real_inner_comm,
      algebra.id.smul_eq_mul, innerₛₗ_apply, linear_map.smul_apply, linear_map.sub_apply,
      matrix.cons_val_one, matrix.head_cons],
  ring},
end

lemma inner_mul_area_form_sub (a x y : E) : ⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ∥a∥ ^ 2 * ω x y :=
congr_arg (λ f : E →ₗ[ℝ] ℝ, f y) (o.inner_mul_area_form_sub' a x)

/-- A complex-valued real-bilinear map on an oriented real inner product space of dimension 2. Its
real part is the inner product and its imaginary part is `orientation.area_form`. -/
def kahler : E →ₗ[ℝ] E →ₗ[ℝ] ℂ :=
(linear_map.llcomp ℝ E ℝ ℂ complex.of_real_clm) ∘ₗ (@innerₛₗ ℝ E _ _)
+ (linear_map.llcomp ℝ E ℝ ℂ ((linear_map.lsmul ℝ ℂ).flip complex.I)) ∘ₗ ω

lemma kahler_apply_apply (x y : E) : o.kahler x y = ⟪x, y⟫ + ω x y • complex.I := rfl

lemma kahler_swap (x y : E) : o.kahler x y = conj (o.kahler y x) :=
begin
  simp only [kahler_apply_apply],
  rw [real_inner_comm, area_form_swap],
  simp,
end

@[simp] lemma kahler_apply_self (x : E) : o.kahler x x = ∥x∥ ^ 2 :=
by simp [kahler_apply_apply, real_inner_self_eq_norm_sq]

@[simp] lemma kahler_almost_complex_left (x y : E) :
  o.kahler (J x) y = - complex.I * o.kahler x y :=
begin
  simp only [o.area_form_almost_complex_left, o.inner_almost_complex_left, o.kahler_apply_apply,
    complex.of_real_neg, complex.real_smul],
  linear_combination ω x y * complex.I_sq,
end

@[simp] lemma kahler_almost_complex_right (x y : E) : o.kahler x (J y) = complex.I * o.kahler x y :=
begin
  simp only [o.area_form_almost_complex_right, o.inner_almost_complex_right, o.kahler_apply_apply,
    complex.of_real_neg, complex.real_smul],
  linear_combination - ω x y * complex.I_sq,
end

@[simp] lemma kahler_neg_orientation (x y : E) : (-o).kahler x y = conj (o.kahler x y) :=
by simp [kahler_apply_apply]

lemma kahler_mul (a x y : E) : o.kahler x a * o.kahler a y = ∥a∥ ^ 2 * o.kahler x y :=
begin
  transitivity (↑(∥a∥ ^ 2) : ℂ) * o.kahler x y,
  { ext,
    { simp only [o.kahler_apply_apply, complex.add_im, complex.add_re, complex.I_im, complex.I_re,
        complex.mul_im, complex.mul_re, complex.of_real_im, complex.of_real_re, complex.real_smul],
      rw [real_inner_comm a x, o.area_form_swap x a],
      linear_combination o.inner_mul_inner_add_area_form_mul_area_form a x y },
    { simp only [o.kahler_apply_apply, complex.add_im, complex.add_re, complex.I_im, complex.I_re,
        complex.mul_im, complex.mul_re, complex.of_real_im, complex.of_real_re, complex.real_smul],
      rw [real_inner_comm a x, o.area_form_swap x a],
      linear_combination o.inner_mul_area_form_sub a x y } },
  { norm_cast },
end

lemma norm_sq_kahler (x y : E) : complex.norm_sq (o.kahler x y) = ∥x∥ ^ 2 * ∥y∥ ^ 2 :=
by simpa [kahler_apply_apply, complex.norm_sq, sq] using o.inner_sq_add_area_form_sq x y

lemma abs_kahler (x y : E) : complex.abs (o.kahler x y) = ∥x∥ * ∥y∥ :=
begin
  rw [← sq_eq_sq, complex.sq_abs],
  { linear_combination o.norm_sq_kahler x y },
  { exact complex.abs_nonneg _ },
  { positivity }
end

lemma norm_kahler (x y : E) : ∥o.kahler x y∥ = ∥x∥ * ∥y∥ := by simpa using o.abs_kahler x y

lemma eq_zero_or_eq_zero_of_kahler_eq_zero {x y : E} (hx : o.kahler x y = 0) : x = 0 ∨ y = 0 :=
begin
  have : ∥x∥ * ∥y∥ = 0 := by simpa [hx] using (o.norm_kahler x y).symm,
  cases eq_zero_or_eq_zero_of_mul_eq_zero this with h h,
  { left,
    simpa using h },
  { right,
    simpa using h },
end

lemma kahler_eq_zero_iff (x y : E) : o.kahler x y = 0 ↔ x = 0 ∨ y = 0 :=
begin
  refine ⟨o.eq_zero_or_eq_zero_of_kahler_eq_zero, _⟩,
  rintros (rfl | rfl);
  simp,
end

lemma kahler_ne_zero {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : o.kahler x y ≠ 0 :=
begin
  apply mt o.eq_zero_or_eq_zero_of_kahler_eq_zero,
  tauto,
end

lemma kahler_ne_zero_iff (x y : E) : o.kahler x y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 :=
begin
  refine ⟨_, λ h, o.kahler_ne_zero h.1 h.2⟩,
  contrapose,
  simp only [not_and_distrib, not_not, kahler_apply_apply, complex.real_smul],
  rintros (rfl | rfl);
  simp,
end

section orthonormal_basis

lemma area_form_apply_orthonormal_basis (b : orthonormal_basis (fin 2) ℝ E)
  (h : b.to_basis.orientation = o) (x y : E) :
  ω x y = ⟪x, b 0⟫ * ⟪y, b 1⟫ - ⟪x, b 1⟫ * ⟪y, b 0⟫ :=
sorry

end orthonormal_basis

end orientation
