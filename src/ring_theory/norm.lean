/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import field_theory.primitive_element
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.determinant
import ring_theory.power_basis

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `algebra.trace`, which is defined similarly as the trace of
`algebra.left_mul_matrix`.

## References

 * https://en.wikipedia.org/wiki/Field_norm

-/

universes u v w

variables {R S T : Type*} [comm_ring R] [is_domain R] [comm_ring S]
variables [algebra R S]
variables {K L F : Type*} [field K] [field L] [field F]
variables [algebra K L] [algebra L F] [algebra K F]
variables {ι : Type w} [fintype ι]

open finite_dimensional
open linear_map
open matrix

open_locale big_operators
open_locale matrix

namespace algebra

variables (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
noncomputable def norm : S →* R :=
linear_map.det.comp (lmul R S).to_ring_hom.to_monoid_hom

lemma norm_apply (x : S) : norm R x = linear_map.det (lmul R S x) := rfl

lemma norm_eq_one_of_not_exists_basis
  (h : ¬ ∃ (s : finset S), nonempty (basis s R S)) (x : S) : norm R x = 1 :=
by { rw [norm_apply, linear_map.det], split_ifs with h, refl }

variables {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
lemma norm_eq_matrix_det [decidable_eq ι] (b : basis ι R S) (s : S) :
  norm R s = matrix.det (algebra.left_mul_matrix b s) :=
by rw [norm_apply, ← linear_map.det_to_matrix b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`. -/
lemma norm_algebra_map_of_basis (b : basis ι R S) (x : R) :
  norm R (algebra_map R S x) = x ^ fintype.card ι :=
begin
  haveI := classical.dec_eq ι,
  rw [norm_apply, ← det_to_matrix b, lmul_algebra_map],
  convert @det_diagonal _ _ _ _ _ (λ (i : ι), x),
  { ext i j, rw [to_matrix_lsmul, matrix.diagonal] },
  { rw [finset.prod_const, finset.card_univ] }
end

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`.

(If `L` is not finite-dimensional over `K`, then `norm = 1 = x ^ 0 = x ^ (finrank L K)`.)
-/
@[simp]
lemma norm_algebra_map (x : K) : norm K (algebra_map K L x) = x ^ finrank K L :=
begin
  by_cases H : ∃ (s : finset L), nonempty (basis s K L),
  { rw [norm_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some] },
  { rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zero],
    rintros ⟨s, ⟨b⟩⟩,
    exact H ⟨s, ⟨b⟩⟩ },
end

section eq_prod_roots

lemma norm_gen_eq_prod_roots [algebra K S] (pb : power_basis K S)
  (hf : (minpoly K pb.gen).splits (algebra_map K F)) :
  algebra_map K F (norm K pb.gen) =
    ((minpoly K pb.gen).map (algebra_map K F)).roots.prod :=
begin
  -- Write the LHS as the 0'th coefficient of `minpoly K pb.gen`
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_left_mul_matrix,
      ring_hom.map_mul, ring_hom.map_pow, ring_hom.map_neg, ring_hom.map_one,
      ← polynomial.coeff_map, fintype.card_fin],
  -- Rewrite `minpoly K pb.gen` as a product over the roots.
  conv_lhs { rw polynomial.eq_prod_roots_of_splits hf },
  rw [polynomial.coeff_C_mul, polynomial.coeff_zero_multiset_prod, multiset.map_map,
      (minpoly.monic pb.is_integral_gen).leading_coeff, ring_hom.map_one, one_mul],
  -- Incorporate the `-1` from the `charpoly` back into the product.
  rw [← multiset.prod_repeat (-1 : F), ← pb.nat_degree_minpoly,
      polynomial.nat_degree_eq_card_roots hf, ← multiset.map_const, ← multiset.prod_map_mul],
  -- And conclude that both sides are the same.
  congr, convert multiset.map_id _, ext f, simp
end

end eq_prod_roots

section eq_zero_iff

lemma norm_eq_zero_iff_of_basis [is_domain S] (b : basis ι R S) {x : S} :
  algebra.norm R x = 0 ↔ x = 0 :=
begin
  have hι : nonempty ι := b.index_nonempty,
  letI := classical.dec_eq ι,
  rw algebra.norm_eq_matrix_det b,
  split,
  { rw ← matrix.exists_mul_vec_eq_zero_iff,
    rintros ⟨v, v_ne, hv⟩,
    rw [← b.equiv_fun.apply_symm_apply v, b.equiv_fun_symm_apply, b.equiv_fun_apply,
        algebra.left_mul_matrix_mul_vec_repr] at hv,
    refine (mul_eq_zero.mp (b.ext_elem $ λ i, _)).resolve_right (show ∑ i, v i • b i ≠ 0, from _),
    { simpa only [linear_equiv.map_zero, pi.zero_apply] using congr_fun hv i },
    { contrapose! v_ne with sum_eq,
      apply b.equiv_fun.symm.injective,
      rw [b.equiv_fun_symm_apply, sum_eq, linear_equiv.map_zero] } },
  { rintro rfl,
    rw [alg_hom.map_zero, matrix.det_zero hι] },
end

lemma norm_ne_zero_iff_of_basis [is_domain S] (b : basis ι R S) {x : S} :
  algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
not_iff_not.mpr (algebra.norm_eq_zero_iff_of_basis b)

/-- See also `algebra.norm_eq_zero_iff'` if you already have rewritten with `algebra.norm_apply`. -/
@[simp]
lemma norm_eq_zero_iff [finite_dimensional K L] {x : L} :
  algebra.norm K x = 0 ↔ x = 0 :=
algebra.norm_eq_zero_iff_of_basis (basis.of_vector_space K L)

/-- This is `algebra.norm_eq_zero_iff` composed with `algebra.norm_apply`. -/
@[simp]
lemma norm_eq_zero_iff' [finite_dimensional K L] {x : L} :
  linear_map.det (algebra.lmul K L x) = 0 ↔ x = 0 :=
algebra.norm_eq_zero_iff_of_basis (basis.of_vector_space K L)

end eq_zero_iff

open intermediate_field

variable (K)

lemma norm_eq_norm_adjoin [finite_dimensional K L] [is_separable K L] (x : L) :
  norm K x = norm K (adjoin_simple.gen K x) ^ finrank K⟮x⟯ L :=
begin
  letI := is_separable_tower_top_of_is_separable K K⟮x⟯ L,
  let pbL := field.power_basis_of_finite_of_separable K⟮x⟯ L,
  let pbx := intermediate_field.adjoin.power_basis (is_separable.is_integral K x),
  rw [← adjoin_simple.algebra_map_gen K x, norm_eq_matrix_det (pbx.basis.smul pbL.basis) _,
    smul_left_mul_matrix_algebra_map, det_block_diagonal, norm_eq_matrix_det pbx.basis],
  simp only [finset.card_fin, finset.prod_const, adjoin.power_basis_basis],
  congr,
  rw [← power_basis.finrank, adjoin_simple.algebra_map_gen K x],
end

section eq_prod_embeddings

variable {K}

open intermediate_field intermediate_field.adjoin_simple polynomial

variables (E : Type*) [field E] [algebra K E] [is_scalar_tower K L F]

lemma norm_eq_prod_embeddings_gen
  (pb : power_basis K L)
  (hE : (minpoly K pb.gen).splits (algebra_map K E)) (hfx : (minpoly K pb.gen).separable) :
  algebra_map K E (norm K pb.gen) =
    (@@finset.univ (power_basis.alg_hom.fintype pb)).prod (λ σ, σ pb.gen) :=
begin
  letI := classical.dec_eq E,
  rw [norm_gen_eq_prod_roots pb hE, fintype.prod_equiv pb.lift_equiv', finset.prod_mem_multiset,
    finset.prod_eq_multiset_prod, multiset.to_finset_val,
    multiset.erase_dup_eq_self.mpr (nodup_roots ((separable_map _).mpr hfx)), multiset.map_id],
  { intro x, refl },
  { intro σ, rw [power_basis.lift_equiv'_apply_coe, id.def] }
end

variable (F)

lemma prod_embeddings_eq_finrank_pow [is_alg_closed E] [is_separable K F] [finite_dimensional K F]
  (pb : power_basis K L) : ∏ σ : F →ₐ[K] E, σ (algebra_map L F pb.gen) =
  ((@@finset.univ (power_basis.alg_hom.fintype pb)).prod
    (λ σ : L →ₐ[K] E, σ pb.gen)) ^ finrank L F :=
begin
  haveI : finite_dimensional L F := finite_dimensional.right K L F,
  haveI : is_separable L F := is_separable_tower_top_of_is_separable K L F,
  letI : fintype (L →ₐ[K] E) := power_basis.alg_hom.fintype pb,
  letI : ∀ (f : L →ₐ[K] E), fintype (@@alg_hom L F E _ _ _ _ f.to_ring_hom.to_algebra) := _,
  rw [fintype.prod_equiv alg_hom_equiv_sigma (λ (σ : F →ₐ[K] E), _) (λ σ, σ.1 pb.gen),
     ← finset.univ_sigma_univ, finset.prod_sigma, ← finset.prod_pow],
  refine finset.prod_congr rfl (λ σ _, _),
  { letI : algebra L E := σ.to_ring_hom.to_algebra,
    simp only [finset.prod_const, finset.card_univ],
    congr,
    rw alg_hom.card L F E },
  { intros σ,
    simp only [alg_hom_equiv_sigma, equiv.coe_fn_mk, alg_hom.restrict_domain, alg_hom.comp_apply,
         is_scalar_tower.coe_to_alg_hom'] }
end

variable (K)

/-- For `L/K` a finite separable extension of fields and `E` an algebraically closed extension
of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images
of `x` over all the `K`-embeddings `σ`  of `L` into `E`. -/
lemma norm_eq_prod_embeddings [finite_dimensional K L] [is_separable K L] [is_alg_closed E]
  {x : L} : algebra_map K E (norm K x) = ∏ σ : L →ₐ[K] E, σ x :=
begin
  have hx := is_separable.is_integral K x,
  rw [norm_eq_norm_adjoin K x, ring_hom.map_pow, ← adjoin.power_basis_gen hx,
    norm_eq_prod_embeddings_gen E (adjoin.power_basis hx) (is_alg_closed.splits_codomain _)],
  { exact (prod_embeddings_eq_finrank_pow L E (adjoin.power_basis hx)).symm },
  { haveI := is_separable_tower_bot_of_is_separable K K⟮x⟯ L,
    exact is_separable.separable K _ }
end

end eq_prod_embeddings

end algebra
