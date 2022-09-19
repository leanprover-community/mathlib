/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Reeased under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.star.spectrum
import analysis.normed.group.quotient
import analysis.normed_space.algebra
import topology.continuous_function.units
import topology.continuous_function.compact
import topology.algebra.algebra
import topology.continuous_function.stone_weierstrass

/-!
# Gelfand Duality

The `gelfand_transform` is an algebra homomorphism from a topological `𝕜`-algebra `A` to
`C(character_space 𝕜 A, 𝕜)`. In the case where `A` is a commutative complex Banach algebra, then
the Gelfand transform is actually spectrum-preserving (`spectrum.gelfand_transform_eq`). Moreover,
when `A` is a commutative C⋆-algebra over `ℂ`, then the Gelfand transform is a surjective isometry,
and even an equivalence between C⋆-algebras.

## Main definitions

* `ideal.to_character_space` : constructs an element of the character space from a maximal ideal in
  a commutative complex Banach algebra

## Main statements

* `spectrum.gelfand_transform_eq` : the Gelfand transform is spectrum-preserving when the algebra is
  a commutative complex Banach algebra.
* `gelfand_transform_isometry` : the Gelfand transform is an isometry when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfand_transform_bijective` : the Gelfand transform is bijective when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.

## TODO

* After `star_alg_equiv` is defined, realize `gelfand_transform` as a `star_alg_equiv`.
* Prove that if `A` is the unital C⋆-algebra over `ℂ` generated by a fixed normal element `x` in
  a larger C⋆-algebra `B`, then `character_space ℂ A` is homeomorphic to `spectrum ℂ x`.
* From the previous result, construct the **continuous functional calculus**.
* Show that if `X` is a compact Hausdorff space, then `X` is (canonically) homeomorphic to
  `character_space ℂ C(X, ℂ)`.
* Conclude using the previous fact that the functors `C(⬝, ℂ)` and `character_space ℂ ⬝` along with
  the canonical homeomorphisms described above constitute a natural contravariant equivalence of
  the categories of compact Hausdorff spaces (with continuous maps) and commutative unital
  C⋆-algebras (with unital ⋆-algebra homomoprhisms); this is known as **Gelfand duality**.

## Tags

Gelfand transform, character space, C⋆-algebra
-/

open weak_dual
open_locale nnreal

section complex_banach_algebra
open ideal

variables {A : Type*} [normed_comm_ring A] [normed_algebra ℂ A] [complete_space A]
  [norm_one_class A] (I : ideal A) [ideal.is_maximal I]

/-- Every maximal ideal in a commutative complex Banach algebra gives rise to a character on that
algebra. In particular, the character, which may be identified as an algebra homomorphism due to
`weak_dual.character_space.equiv_alg_hom`, is given by the composition of the quotient map and
the Gelfand-Mazur isomorphism `normed_ring.alg_equiv_complex_of_complete`. -/
noncomputable def ideal.to_character_space : character_space ℂ A :=
character_space.equiv_alg_hom.symm $ ((@normed_ring.alg_equiv_complex_of_complete (A ⧸ I) _ _
  (by { letI := quotient.field I, exact @is_unit_iff_ne_zero (A ⧸ I) _ }) _).symm :
  A ⧸ I →ₐ[ℂ] ℂ).comp
  (quotient.mkₐ ℂ I)

lemma ideal.to_character_space_apply_eq_zero_of_mem {a : A} (ha : a ∈ I) :
  I.to_character_space a = 0 :=
begin
  unfold ideal.to_character_space,
  simpa only [character_space.equiv_alg_hom_symm_coe, alg_hom.coe_comp,
    alg_equiv.coe_alg_hom, quotient.mkₐ_eq_mk, function.comp_app, quotient.eq_zero_iff_mem.mpr ha,
    spectrum.zero_eq, normed_ring.alg_equiv_complex_of_complete_symm_apply]
    using set.eq_of_mem_singleton (set.singleton_nonempty (0 : ℂ)).some_mem,
end

/-- If `a : A` is not a unit, then some character takes the value zero at `a`. This is equivlaent
to `gelfand_transform ℂ A a` takes the value zero at some character. -/
lemma weak_dual.character_space.exists_apply_eq_zero {a : A} (ha : ¬ is_unit a) :
  ∃ f : character_space ℂ A, f a = 0 :=
begin
  unfreezingI { obtain ⟨M, hM, haM⟩ := (span {a}).exists_le_maximal (span_singleton_ne_top ha) },
  exact ⟨M.to_character_space, M.to_character_space_apply_eq_zero_of_mem
    (haM (mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩,
end

/-- The Gelfand transform is spectrum-preserving. -/
lemma spectrum.gelfand_transform_eq (a : A) : spectrum ℂ (gelfand_transform ℂ A a) = spectrum ℂ a :=
begin
  refine set.subset.antisymm (alg_hom.spectrum_apply_subset (gelfand_transform ℂ A) a) (λ z hz, _),
  obtain ⟨f, hf⟩ := weak_dual.character_space.exists_apply_eq_zero hz,
  simp only [map_sub, sub_eq_zero, alg_hom_class.commutes, algebra.id.map_eq_id, ring_hom.id_apply]
    at hf,
  exact (continuous_map.spectrum_eq_range (gelfand_transform ℂ A a)).symm ▸ ⟨f, hf.symm⟩,
end

instance : nonempty (character_space ℂ A) :=
begin
  haveI := norm_one_class.nontrivial A,
  exact ⟨classical.some $
    weak_dual.character_space.exists_apply_eq_zero (zero_mem_nonunits.mpr zero_ne_one)⟩,
end

end complex_banach_algebra

section complex_cstar_algebra

variables (A : Type*) [normed_comm_ring A] [normed_algebra ℂ A] [complete_space A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A] [nontrivial A]

/-- The Gelfand transform is an isometry when the algebra is a C⋆-algebra over `ℂ`. -/
lemma gelfand_transform_isometry : isometry (gelfand_transform ℂ A) :=
begin
  refine add_monoid_hom_class.isometry_of_norm (gelfand_transform ℂ A) (λ a, _),
  have gt_map_star : gelfand_transform ℂ A (star a) = star (gelfand_transform ℂ A a),
    from continuous_map.ext (λ φ, map_star φ a),
  /- By `spectrum.gelfand_transform_eq`, the spectra of `star a * a` and its
  `gelfand_transform` coincide. Therefore, so do their spectral radii, and since they are
  self-adjoint, so also do their norms. Applying the C⋆-property of the norm and taking square
  roots shows that the norm is preserved. -/
  have : spectral_radius ℂ (gelfand_transform ℂ A (star a * a)) = spectral_radius ℂ (star a * a),
  { unfold spectral_radius, rw spectrum.gelfand_transform_eq, },
  simp only [map_mul, gt_map_star, (is_self_adjoint.star_mul_self _).spectral_radius_eq_nnnorm,
    ennreal.coe_eq_coe, cstar_ring.nnnorm_star_mul_self, ←sq] at this,
  simpa only [function.comp_app, nnreal.sqrt_sq]
    using congr_arg ((coe : ℝ≥0 → ℝ) ∘ ⇑nnreal.sqrt) this,
end

/-- The Gelfand transform is bijective when the algebra is a C⋆-algebra over `ℂ`. -/
lemma gelfand_transform_bijective : function.bijective (gelfand_transform ℂ A) :=
begin
  refine ⟨(gelfand_transform_isometry A).injective, _⟩,
  suffices : (gelfand_transform ℂ A).range = ⊤,
  { exact λ x, this.symm ▸ (gelfand_transform ℂ A).mem_range.mp (this.symm ▸ algebra.mem_top) },
  /- Because the `gelfand_transform ℂ A` is an isometry, it has closed range, and so by the
  Stone-Weierstrass theorem, it suffices to show that the image of the Gelfand transform separates
  points in `C(character_space ℂ A, ℂ)` and is closed under `star`. -/
  have h : (gelfand_transform ℂ A).range.topological_closure = (gelfand_transform ℂ A).range,
  from le_antisymm (subalgebra.topological_closure_minimal _ le_rfl
    (gelfand_transform_isometry A).closed_embedding.closed_range)
    (subalgebra.subalgebra_topological_closure _),
  refine h ▸ continuous_map.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points
    _ (λ _ _, _) (λ f hf, _),
  /- Separating points just means that elements of the `character_space` which agree at all points
  of `A` are the same functional, which is just extensionality. -/
  { contrapose!,
    exact λ h, subtype.ext (continuous_linear_map.ext $
      λ a, h (gelfand_transform ℂ A a) ⟨gelfand_transform ℂ A a, ⟨a, rfl⟩, rfl⟩), },
  /- If `f = gelfand_transform ℂ A a`, then `star f` is also in the range of `gelfand_transform ℂ A`
  using the argument `star a`. The key lemma below may be hard to spot; it's `map_star` coming from
  `weak_dual.star_hom_class`, which is a nontrivial result. -/
  { obtain ⟨f, ⟨a, rfl⟩, rfl⟩ := subalgebra.mem_map.mp hf,
    refine ⟨star a, continuous_map.ext $ λ ψ, _⟩,
    simpa only [gelfand_transform_apply_apply, map_star, ring_hom.coe_monoid_hom,
      alg_equiv.coe_alg_hom, ring_hom.to_monoid_hom_eq_coe, alg_equiv.to_alg_hom_eq_coe,
      ring_hom.to_fun_eq_coe, continuous_map.coe_mk, is_R_or_C.conj_ae_coe,
      alg_hom.coe_to_ring_hom, monoid_hom.to_fun_eq_coe, ring_hom.comp_left_continuous_apply,
      monoid_hom.comp_left_continuous_apply, continuous_map.comp_apply,
      alg_hom.to_ring_hom_eq_coe, alg_hom.comp_left_continuous_apply] },
end

end complex_cstar_algebra
