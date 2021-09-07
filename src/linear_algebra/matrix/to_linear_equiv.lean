/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.to_lin
import ring_theory.localization

/-!
# Matrices and linear equivalences

This file gives the map `matrix.to_linear_equiv` from matrices with invertible determinant,
to linear equivs.

## Main definitions

 * `matrix.to_linear_equiv`: a matrix with an invertible determinant forms a linear equiv

## Main results

 * `matrix.exists_mul_vec_eq_zero_iff`: `M` maps some `v ≠ 0` to zero iff `det M = 0`

## Tags

matrix, linear_equiv, determinant, inverse

-/

namespace matrix

open linear_map

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables {n : Type*} [fintype n]

section to_linear_equiv'

variables [decidable_eq n]

/-- An invertible matrix yields a linear equivalence from the free module to itself.

See `matrix.to_linear_equiv` for the same map on arbitrary modules.
-/
noncomputable def to_linear_equiv' (P : matrix n n R) (h : is_unit P) : (n → R) ≃ₗ[R] (n → R) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
{ inv_fun   := P⁻¹.to_lin',
  left_inv  := λ v,
    show (P⁻¹.to_lin'.comp P.to_lin') v = v,
    by rw [← matrix.to_lin'_mul, P.nonsing_inv_mul h', matrix.to_lin'_one, linear_map.id_apply],
  right_inv := λ v,
    show (P.to_lin'.comp P⁻¹.to_lin') v = v,
    by rw [← matrix.to_lin'_mul, P.mul_nonsing_inv h', matrix.to_lin'_one, linear_map.id_apply],
  ..P.to_lin' }

@[simp] lemma to_linear_equiv'_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv' h) : module.End R (n → R)) = P.to_lin' := rfl

@[simp] lemma to_linear_equiv'_symm_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv' h).symm : module.End R (n → R)) = P⁻¹.to_lin' := rfl

end to_linear_equiv'

section to_linear_equiv

variables (b : basis n R M)

include b

/-- Given `hA : is_unit A.det` and `b : basis R b`, `A.to_linear_equiv b hA` is
the `linear_equiv` arising from `to_lin b b A`.

See `matrix.to_linear_equiv'` for this result on `n → R`.
-/
@[simps apply]
noncomputable def to_linear_equiv [decidable_eq n] (A : matrix n n R) (hA : is_unit A.det) :
  M ≃ₗ[R] M :=
begin
  refine {
    to_fun := to_lin b b A,
    inv_fun := to_lin b b A⁻¹,
    left_inv := λ x, _,
    right_inv := λ x, _,
    .. to_lin b b A };
  simp only [← linear_map.comp_apply, ← matrix.to_lin_mul b b b,
             matrix.nonsing_inv_mul _ hA, matrix.mul_nonsing_inv _ hA,
             to_lin_one, linear_map.id_apply]
end

lemma ker_to_lin_eq_bot [decidable_eq n] (A : matrix n n R) (hA : is_unit A.det) :
  (to_lin b b A).ker = ⊥ :=
ker_eq_bot.mpr (to_linear_equiv b A hA).injective

lemma range_to_lin_eq_top [decidable_eq n] (A : matrix n n R) (hA : is_unit A.det) :
  (to_lin b b A).range = ⊤ :=
range_eq_top.mpr (to_linear_equiv b A hA).surjective

end to_linear_equiv

section nondegenerate

open_locale matrix

/-- This holds for all integral domains (see `matrix.exists_mul_vec_eq_zero_iff`),
not just fields, but it's easier to prove it for the field of fractions first. -/
lemma exists_mul_vec_eq_zero_iff_aux {K : Type*} [decidable_eq n] [field K] {M : matrix n n K} :
  (∃ (v ≠ 0), M.mul_vec v = 0) ↔ M.det = 0 :=
begin
  split,
  { rintros ⟨v, hv, mul_eq⟩,
    contrapose! hv,
    exact eq_zero_of_mul_vec_eq_zero hv mul_eq },
  { contrapose!,
    intros h,
    have : M.to_lin'.ker = ⊥,
    { simpa only [ker_to_lin'_eq_bot_iff, not_imp_not] using h },
    have : M ⬝ linear_map.to_matrix'
      ((linear_equiv.of_injective_endo M.to_lin' this).symm : (n → K) →ₗ[K] (n → K)) = 1,
    { refine matrix.to_lin'.injective (linear_map.ext $ λ v, _),
      rw [matrix.to_lin'_mul, matrix.to_lin'_one, matrix.to_lin'_to_matrix', linear_map.comp_apply],
      exact (linear_equiv.of_injective_endo M.to_lin' this).apply_symm_apply v },
    exact matrix.det_ne_zero_of_right_inverse this }
end

lemma exists_mul_vec_eq_zero_iff {A : Type*} [decidable_eq n] [integral_domain A]
  {M : matrix n n A} :
  (∃ (v ≠ 0), M.mul_vec v = 0) ↔ M.det = 0 :=
begin
  have : (∃ (v ≠ 0), mul_vec ((algebra_map A (fraction_ring A)).map_matrix M) v = 0) ↔ _ :=
    exists_mul_vec_eq_zero_iff_aux,
  rw [← ring_hom.map_det, is_fraction_ring.to_map_eq_zero_iff] at this,
  refine iff.trans _ this, split; rintro ⟨v, hv, mul_eq⟩,
  { refine ⟨λ i, algebra_map _ _ (v i), mt (λ h, funext $ λ i, _) hv, _⟩,
    { exact is_fraction_ring.injective A (fraction_ring A) (congr_fun h i) },
    { ext i,
      refine (ring_hom.map_mul_vec _ _ _ i).symm.trans _,
      rw [mul_eq, pi.zero_apply, ring_hom.map_zero, pi.zero_apply] } },
  { letI := classical.dec_eq (fraction_ring A),
    obtain ⟨⟨b, hb⟩, ba_eq⟩ := is_localization.exist_integer_multiples_of_finset
      (non_zero_divisors A) (finset.univ.image v),
    choose f hf using ba_eq,
    refine ⟨λ i, f _ (finset.mem_image.mpr ⟨i, finset.mem_univ i, rfl⟩),
            mt (λ h, funext $ λ i, _) hv, _⟩,
    { have := congr_arg (algebra_map A (fraction_ring A)) (congr_fun h i),
      rw [hf, subtype.coe_mk, pi.zero_apply, ring_hom.map_zero, algebra.smul_def,
          mul_eq_zero, is_fraction_ring.to_map_eq_zero_iff] at this,
      exact this.resolve_left (mem_non_zero_divisors_iff_ne_zero.mp hb), },
    { ext i,
      refine is_fraction_ring.injective A (fraction_ring A) _,
      calc algebra_map A (fraction_ring A) (M.mul_vec (λ (i : n), f (v i) _) i)
          = ((algebra_map A (fraction_ring A)).map_matrix M).mul_vec
              (algebra_map _ (fraction_ring A) b • v) i : _
      ... = 0 : _,
      { simp_rw [ring_hom.map_mul_vec, mul_vec, dot_product, function.comp_app, hf,
          subtype.coe_mk, ring_hom.map_matrix_apply, pi.smul_apply, smul_eq_mul,
          algebra.smul_def] },
      { rw [mul_vec_smul, mul_eq, pi.smul_apply, pi.zero_apply, smul_zero] } } },
end

end nondegenerate

end matrix
