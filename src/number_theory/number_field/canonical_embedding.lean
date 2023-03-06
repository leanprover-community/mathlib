/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/

import number_theory.number_field.embeddings
import measure_theory.group.geometry_of_numbers
import ring_theory.discriminant
import algebra.module.zlattice

/-!
# Canonical embedding of a number field
The canonical embedding of a number field `K` of signature `(r₁, r₂)` is the ring homomorphism
`K →+* ℝ^r₁ × ℂ^r₂` that sends `x ∈ K` to `(φ_₁(x),...,φ_r₁(x)) × (ψ_₁(x),..., ψ_r₂(x))` where
`φ_₁,...,φ_r₁` are its real embeddings and `ψ_₁,..., ψ_r₂` are its complex embeddings (up to
complex conjugation).

## Main definitions and results
* `number_field.canonical_embedding.ring_of_integers.inter_ball_finite`: the intersection of the
image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
radius is finite.

## Tags
number field, infinite places
-/

open_locale classical number_field

noncomputable theory

open number_field number_field.infinite_place module fintype finite_dimensional

variables (K : Type*) [field K]

namespace number_field.canonical_embedding

/-- The ambiant space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
@[reducible]
def space :=
  ({w : infinite_place K // is_real w} → ℝ) × ({w : infinite_place K // is_complex w} → ℂ)

instance : comm_ring (space K) := prod.comm_ring

instance : module ℝ (space K) := prod.module

lemma space_rank [number_field K] :
  finrank ℝ (space K) = finrank ℚ K :=
begin
  haveI : module.free ℝ ℂ := infer_instance,
  rw [module.free.finrank_prod, module.free.finrank_pi, module.free.finrank_pi_fintype,
    complex.finrank_real_complex, finset.sum_const, finset.card_univ, ← card_real_embeddings,
    algebra.id.smul_eq_mul, mul_comm, ← card_complex_embeddings, ← number_field.embeddings.card K ℂ,
    fintype.card_subtype_compl, nat.add_sub_of_le (fintype.card_subtype_le _)],
end

lemma space_nontrivial [number_field K] : nontrivial (space K) :=
begin
  obtain ⟨w⟩ := infinite_place.nonempty K,
  by_cases hw : is_real w,
  { convert nontrivial_prod_left,
    { convert @function.nontrivial _ _ _ real.nontrivial,
      use ⟨w, hw⟩, },
    exact nonempty_of_inhabited, },
 { convert nontrivial_prod_right,
   {  exact nonempty_of_inhabited, },
   {  convert @function.nontrivial _ _ _ complex.nontrivial,
      use ⟨w, not_is_real_iff_is_complex.mp hw⟩, }},
end

/-- The canonical embedding of a number field `K` of signature `(r₁, r₂)` into `ℝ^r₁ × ℂ^r₂`. -/
def _root_.number_field.canonical_embedding : K →+* (space K) :=
ring_hom.prod
  (pi.ring_hom (λ w, w.prop.embedding))
  (pi.ring_hom (λ w, w.val.embedding))

lemma _root_.number_field.canonical_embedding_injective [number_field K] :
  function.injective (number_field.canonical_embedding K) :=
begin
  convert ring_hom.injective _,
  exact (space_nontrivial K),
end

open number_field

variable {K}

@[simp]
lemma apply_at_real_infinite_place (w : {w : infinite_place K // is_real w}) (x : K) :
  (number_field.canonical_embedding K x).1 w = w.prop.embedding x :=
by simp only [canonical_embedding, ring_hom.prod_apply, pi.ring_hom_apply]

@[simp]
lemma apply_at_complex_infinite_place (w : { w : infinite_place K // is_complex w}) (x : K) :
  (number_field.canonical_embedding K x).2 w = embedding w.val x :=
by simp only [canonical_embedding, ring_hom.prod_apply, pi.ring_hom_apply]

lemma nnnorm_eq [number_field K] (x : K) :
  ‖canonical_embedding K x‖₊ = finset.univ.sup (λ w : infinite_place K, ⟨w x, map_nonneg w x⟩) :=
begin
  rw [prod.nnnorm_def', pi.nnnorm_def, pi.nnnorm_def],
  rw ( _ : finset.univ = {w : infinite_place K | is_real w}.to_finset
    ∪ {w : infinite_place K | is_complex w}.to_finset),
  { rw [finset.sup_union, sup_eq_max],
    refine congr_arg2 _ _ _,
    { convert (finset.univ.sup_map (function.embedding.subtype (λ w : infinite_place K, is_real w))
        (λ w, (⟨w x, map_nonneg w x⟩ : nnreal))).symm using 2,
      ext w,
      simpa only [apply_at_real_infinite_place, coe_nnnorm, real.norm_eq_abs,
        function.embedding.coe_subtype, subtype.coe_mk]
      using is_real.place_embedding_apply w.prop x, },
    { convert (finset.univ.sup_map (function.embedding.subtype (λ w : infinite_place K,
        is_complex w)) (λ w, (⟨w x, map_nonneg w x⟩ : nnreal))).symm using 2,
      ext w,
      simp only [apply_at_complex_infinite_place, subtype.val_eq_coe, coe_nnnorm,
        complex.norm_eq_abs, function.embedding.coe_subtype, subtype.coe_mk, abs_embedding], }},
  { ext w,
    simp only [em (is_real w), set.mem_set_of_eq, finset.mem_union, set.mem_to_finset,
      finset.mem_univ, ←infinite_place.not_is_real_iff_is_complex], },
end

lemma le_of_le [number_field K] (x : K) (r : ℝ) :
  ‖canonical_embedding K x‖ ≤ r ↔ ∀ w : infinite_place K, w x ≤ r :=
begin
  obtain hr | hr := lt_or_le r 0,
  { split,
    { intro h,
      exfalso,
      exact (not_le.mpr (lt_of_le_of_lt h hr)) (norm_nonneg _), },
    { intro h,
      exfalso,
      obtain ⟨w⟩ := infinite_place.nonempty K,
      exact (not_le.mpr (lt_of_le_of_lt (h w) hr)) (map_nonneg w _), }},
  { lift r to nnreal using hr,
    simp_rw [← coe_nnnorm, nnnorm_eq, nnreal.coe_le_coe, finset.sup_le_iff, finset.mem_univ,
      forall_true_left],
    split; { exact λ h w, h w, }},
end

variables (K)

/-- The image of `𝓞 K` as a subring of `ℝ^r₁ × ℂ^r₂`. -/
def integer_lattice : subring (space K) :=
subring.map (canonical_embedding K) (ring_hom.range (algebra_map (𝓞 K) K))

/-- The ring equiv between `𝓞 K` and the integer lattice. -/
def equiv_integer_lattice [number_field K] :
  𝓞 K ≃ₗ[ℤ] (integer_lattice K) :=
begin
  refine linear_equiv.of_bijective _ _,
  { refine linear_map.mk _ _ _,
    exact λ x, ⟨canonical_embedding K (algebra_map (𝓞 K) K x), algebra_map (𝓞 K) K x,
      by simp only [subring.mem_carrier, ring_hom.mem_range, exists_apply_eq_apply], rfl⟩,
    { intros _ _,
      simpa only [map_add], },
    { intros _ _,
      simpa only [zsmul_eq_mul, map_mul, map_int_cast], }},
  { split,
    { intros _ _ h,
      rw [linear_map.coe_mk, subtype.mk_eq_mk] at h,
      exact (is_fraction_ring.injective (𝓞 K) K) (canonical_embedding_injective K h), },
    { exact λ ⟨_, ⟨_, ⟨⟨a, rfl⟩, rfl⟩⟩⟩, ⟨a, rfl⟩, }}
end

lemma integer_lattice.inter_ball_finite [number_field K] (r : ℝ) :
  ((integer_lattice K : set (space K)) ∩ (metric.closed_ball 0 r)).finite :=
begin
  obtain hr | hr := lt_or_le r 0,
  { convert set.finite_empty,
    rw metric.closed_ball_eq_empty.mpr hr,
    exact set.inter_empty _, },
  { have heq : ∀ x : K, canonical_embedding K x ∈ (metric.closed_ball (0 : (space K)) r) ↔
      ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ r,
    { simp_rw [← place_apply, ← infinite_place.coe_mk, mem_closed_ball_zero_iff, le_of_le],
      exact λ x, le_iff_le x r, },
    convert set.finite.image (canonical_embedding K) (embeddings.finite_of_norm_le K ℂ r),
    ext, split,
    { rintros ⟨⟨_, ⟨⟨x, rfl⟩, rfl⟩⟩, hx2⟩,
      exact ⟨x, ⟨⟨set_like.coe_mem x, (heq x).mp hx2⟩, rfl⟩⟩, },
    { rintros ⟨x, ⟨⟨ hx1, hx2⟩, rfl⟩⟩,
      exact ⟨⟨x, ⟨⟨⟨x, hx1⟩, rfl⟩, rfl⟩⟩, (heq x).mpr hx2⟩, }},
end

lemma integer_lattice.countable [number_field K] : countable (integer_lattice K) :=
begin
  suffices : (⋃ n : ℕ, ((integer_lattice K : set (space K)) ∩ (metric.closed_ball 0 n))).countable,
  { refine set.countable.to_subtype (set.countable.mono _ this),
    rintros _ ⟨x, ⟨hx, rfl⟩⟩,
    rw set.mem_Union,
    use nat.ceil (‖canonical_embedding K x‖),
    exact ⟨⟨x, hx, rfl⟩, mem_closed_ball_zero_iff.mpr (nat.le_ceil _)⟩, },
  { exact set.countable_Union (λ n, (integer_lattice.inter_ball_finite K n).countable), },
end

section basis

open_locale complex_conjugate

variable (K)

/-- The embedding of `K` into `K →+* (K →+* ℂ) → ℂ` defined by sending `x : K` to the vector of its
image by all the complex embeddings of `K`. -/
def _root_.number_field.full_embedding : K →+* (K →+* ℂ) → ℂ :=
{ to_fun := λ x φ, φ x,
  map_zero' := funext (λ φ, map_zero φ),
  map_one' := funext (λ φ, map_one φ),
  map_add' := λ x y, funext (λ φ, map_add φ x y),
  map_mul' := λ x y, funext (λ φ, map_mul φ x y), }

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

/-- The map from `(K →+* ℂ) → ℂ` to `E` that gives a commuting diagramm, see
`number_field.canonical_embedding.commutes`. -/
def comm_map : ((K →+* ℂ) → ℂ) →ₗ[ℝ] E:=
{ to_fun := λ e, ⟨λ w, (e w.val.embedding).re, λ w, (e w.val.embedding)⟩,
  map_smul' := λ _ _, by simp_rw [ring_hom.id_apply, prod.smul_mk, pi.smul_def, smul_eq_mul,
    complex.real_smul, complex.of_real_mul_re],
  map_add' := λ _ _, by simp only [subtype.val_eq_coe, pi.add_apply, complex.add_re, prod.mk_add_mk,
    pi.add_def, eq_self_iff_true], }

lemma _root_.number_field.full_embedding.conj_apply [number_field K] {x : (K →+* ℂ) → ℂ}
  (φ : K →+* ℂ) (hx : x ∈ submodule.span ℝ
    (set.range (λ i, number_field.full_embedding K (integral_basis K i)))) :
  x (complex_embedding.conjugate φ) = conj (x φ) :=
begin
  refine submodule.span_induction hx _ _ (λ _ _ hx hy, _) (λ _ _ hx, _),
  { rintros _ ⟨_, rfl⟩, refl, },
  { simp only [pi.zero_apply, map_zero], },
  { rw [pi.add_apply, pi.add_apply, map_add, hx, hy], },
  { rw [pi.smul_apply, pi.smul_apply, complex.real_smul, complex.real_smul, map_mul, hx,
      is_R_or_C.conj_of_real], }
end

open number_field

lemma comm_map_eq_zero [number_field K] {x : (K →+* ℂ) → ℂ}
  (hx : x ∈ submodule.span ℝ (set.range (λ i, full_embedding K (integral_basis K i))))
  (hc : comm_map K x = 0):
  x = 0 :=
begin
  ext1 φ,
  rw pi.zero_apply,
  by_cases hφ : complex_embedding.is_real φ,
  { have : ((x φ).re : ℂ) = x φ,
    { rw ← complex.eq_conj_iff_re,
      rw ← full_embedding.conj_apply K _ hx,
      rw complex_embedding.is_real_iff.mp hφ, },
    rw ← this,
    have hw : is_real (mk φ) := ⟨φ, hφ, rfl⟩,
    have := congr_arg (coe : ℝ → ℂ)
      (congr_arg (λ x : ({w // is_real w} → ℝ) × ({w // is_complex w} → ℂ), x.1 ⟨mk φ,
      hw⟩) hc),
    convert this,
    convert (complex_embeddings.is_real.embedding_mk hφ).symm, },
  { have hw : is_complex (mk φ) := ⟨φ, hφ, rfl⟩,
    have := congr_arg (λ x : ({w // is_real w} → ℝ) × ({w // is_complex w} → ℂ),
      x.2 ⟨mk φ, hw⟩) hc,
    by_cases h2 : φ = (infinite_place.mk φ).embedding,
    { convert this, },
    { rw ← map_eq_zero_iff (star_ring_end ℂ) star_injective,
      rw ← full_embedding.conj_apply K _ hx,
      have t1 : φ = complex_embedding.conjugate (infinite_place.mk φ).embedding,
      { have t1 : infinite_place.mk ((infinite_place.mk φ).embedding) = mk φ,
        { simp only [mk_embedding], },
        have t2 := mk_eq_iff.mp t1,
        have t3 := t2.resolve_left _,
        exact t3.symm,
        exact ne_comm.mp h2, },
      rw t1,
      have := congr_arg (λ x : ({w // is_real w} → ℝ) × ({w // is_complex w} → ℂ),
        x.2 ⟨mk φ, hw⟩) hc,
      convert this,
      ext1,
      simp only [complex_embedding.conjugate_coe_eq, star_ring_end_self_apply], }},
end

lemma commutes (x : K) :
  comm_map K (full_embedding K x) = canonical_embedding K x :=
begin
  simp only [comm_map, full_embedding, canonical_embedding, subtype.val_eq_coe,
    ring_hom.coe_mk, linear_map.coe_mk, ring_hom.prod_apply, prod.mk.inj_iff,
    pi.ring_hom_apply],
  split,
  { ext w,
    simp only [pi.ring_hom_apply, ← complex_embedding.is_real.coe_embedding_apply
      (is_real_iff.mp w.prop) x, complex.of_real_re],
    refl, },
  { ext1 w,
    simp only [pi.ring_hom_apply], },
end

/-- A basis of `E` over `ℝ` that is also a basis of the `unit_lattice` over `ℤ`.-/
def lattice_basis [number_field K] : basis (free.choose_basis_index ℤ (𝓞 K)) ℝ E :=
begin
  let e : (K →+* ℂ) ≃ free.choose_basis_index ℤ (𝓞 K),
  { refine equiv_of_card_eq _,
    rw ← finrank_eq_card_basis (integral_basis K),
    exact embeddings.card K ℂ, },
  suffices : linear_independent ℂ (λ i, full_embedding K (integral_basis K (e i))),
  { have t0 := @linear_independent.restrict_scalars _ ℝ ℂ _ _ _ _ _ _ _ _ _
    (smul_left_injective ℝ one_ne_zero) this,
    have t1 : linear_independent ℝ (λ i, full_embedding K (integral_basis K i)),
    { refine (linear_independent_equiv' e.symm _).mpr t0,
      ext1 φ,
      simp only [equiv.apply_symm_apply, function.comp_app], },
    have t2 : linear_independent ℝ (λ i,
      (comm_map K ∘ full_embedding K) (integral_basis K i)),
    { refine linear_independent.map t1 _,
      refine linear_map.disjoint_ker.mpr _,
      intros x hx hc,
      exact comm_map_eq_zero K hx hc, },
    have t3 : linear_independent ℝ (λ i, canonical_embedding K (integral_basis K i)),
    { refine (linear_independent_equiv' (equiv.refl _) _).mp t2,
      ext1 i,
      exact (commutes K (integral_basis K i)).symm, },
    refine basis.mk t3 (le_of_eq (eq_of_le_of_finrank_le le_top _).symm),
    rw [finrank_top, canonical_embedding.rank, ← set.finrank,
      ← linear_independent_iff_card_eq_finrank_span.mp t3, ← ring_of_integers.rank,
     free.finrank_eq_card_choose_basis_index], },
  let B := pi.basis_fun ℂ (K →+* ℂ),
  let M := B.to_matrix (λ i, full_embedding K (integral_basis K (e i))),
  suffices : M.det ≠ 0,
  { rw ← is_unit_iff_ne_zero at this,
    rw ← basis.det_apply at this,
    rw ← is_basis_iff_det at this,
    exact this.1, },
  let N := algebra.embeddings_matrix_reindex ℚ ℂ (λ i, integral_basis K (e i))
    ring_hom.equiv_rat_alg_hom,
  rw (_ : M = N.transpose),
  { rw matrix.det_transpose,
    have h := algebra.discr_not_zero_of_basis ℚ (integral_basis K),
    contrapose! h,
    have t2 := algebra.discr_eq_det_embeddings_matrix_reindex_pow_two ℚ ℂ
      (λ i, integral_basis K (e i)) ring_hom.equiv_rat_alg_hom,
    rw h at t2,
    rw zero_pow (by norm_num : 0 < 2) at t2,
    rw map_eq_zero_iff _ (algebra_map ℚ ℂ).injective at t2,
    rw ← algebra.discr_reindex ℚ (integral_basis K) e.symm,
    convert t2,
    exact equiv.symm_symm e, },
  { ext1 φ j,
    dsimp [M, N],
    rw basis.to_matrix_apply _ _ φ j,
    rw pi.basis_fun_repr,
    refl, },
end

lemma lattice_basis_apply [number_field K] (i : free.choose_basis_index ℤ (𝓞 K)) :
  (lattice_basis K) i = (canonical_embedding K) (integral_basis K i) :=
by simp only [lattice_basis, basis.coe_mk]

#exit

lemma integral_basis_span [number_field K] :
  (integer_lattice K : set E) = submodule.span ℤ (set.range (lattice_basis K)) :=
begin
  have t1 : (canonical_embedding K).to_int_alg_hom.to_linear_map ''
    ((algebra_map (𝓞 K) K).to_int_alg_hom.to_linear_map '' (set.range (ring_of_integers.basis K))) =
    set.range (lattice_basis K),
  { change (canonical_embedding K) '' ((algebra_map (𝓞 K) K) ''
      (set.range (ring_of_integers.basis K))) = set.range (lattice_basis K),
    suffices : ∀ i, (canonical_embedding K) ((algebra_map (𝓞 K) K) (ring_of_integers.basis K i)) =
      (lattice_basis K) i,
    { rw ← set.range_comp,
      rw ← set.range_comp,
      refine congr_arg set.range _,
      funext i,
      exact this i, },
    intro i,
    rw lattice_basis_apply K i,
    rw integral_basis_apply K i, },
  have t2 := congr_arg (λ s, submodule.span ℤ s) t1,
  dsimp at t2,
  rw ← submodule.map_span at t2,
  rw ← submodule.map_span at t2,
  rw (ring_of_integers.basis K).span_eq at t2,
  rw ← t2,
  ext, split,
  { rintros ⟨a, ⟨ha, rfl⟩⟩,
    use a,
    split,
    { use a,
      exact ha,
      split,
      { trivial, },
      { refl, }},
    { refl, }},
  { rintros ⟨_, ⟨⟨b, ⟨_, rfl⟩⟩, rfl⟩⟩,
    use b,
    split,
    { exact subtype.mem b, },
    { refl, }},
end

end basis

#exit

/-- The real part of the convex body defined by `f`, see `convex_body`.-/
def convex_body_real (f : infinite_place K → nnreal) : set ({w : infinite_place K // is_real w} → ℝ)
:= set.pi set.univ (λ w, metric.ball 0 (f w))

/-- The complex part of the convex body defined by `f`, see `convex_body`.-/
def convex_body_complex (f : infinite_place K → nnreal) :
  set ({w : infinite_place K // is_complex w} → ℂ) :=
set.pi set.univ (λ w, metric.ball 0 (f w))

/-- The convex body defined by `f`: the set of points `x : E` such that `x w < f w` for all
infinite places `w`.-/
@[reducible]
def convex_body (f : infinite_place K → nnreal): set E :=
(convex_body_real K f) ×ˢ (convex_body_complex K f)

lemma convex_body.symmetric (f : infinite_place K → nnreal) :
  ∀ x : E, x ∈ (convex_body K f) → -x ∈ (convex_body K f) :=
begin
  intros x hx,
  refine set.mem_prod.1 ⟨_, _⟩,
  { intros w _,
    simpa only [prod.fst_neg, pi.neg_apply, mem_ball_zero_iff, real.norm_eq_abs, abs_neg]
      using mem_ball_zero_iff.1 (hx.1 w (set.mem_univ _)), },
  { intros w _,
    simpa only [prod.snd_neg, pi.neg_apply, mem_ball_zero_iff, complex.norm_eq_abs,
      absolute_value.map_neg] using mem_ball_zero_iff.mp (hx.right w (set.mem_univ w)), }
end

lemma convex_body.convex (f : infinite_place K → nnreal) :
  convex ℝ (convex_body K f) :=
begin
  refine convex.prod _ _;
  exact convex_pi (λ i _, (convex_ball 0 (f i))),
end

lemma convex_body_mem (x : K) (f : infinite_place K → nnreal) :
  canonical_embedding K x ∈ (convex_body K f) ↔ ∀ w : infinite_place K, w x < f w :=
begin
  rw set.mem_prod,
  rw convex_body_real,
  rw convex_body_complex,
  rw set.mem_pi,
  rw set.mem_pi,
  simp only [set.mem_univ, mem_ball_zero_iff, forall_true_left, real.norm_eq_abs,
    subtype.forall, subtype.coe_mk, complex.norm_eq_abs],
  simp_rw apply_at_real_infinite_place,
  simp_rw apply_at_complex_infinite_place,
  simp_rw ← infinite_place.apply,
  simp_rw mk_embedding,
  split,
  { rintros ⟨hr, hc⟩ w,
    by_cases h : is_real w,
    { convert hr w h,
      rw ← is_real.place_embedding_apply,
      refl, },
    { rw not_is_real_iff_is_complex at h,
      exact hc w h, }},
  { rintro h,
    split,
    { intros w hw,
      convert h w,
      rw ← is_real.place_embedding_apply,
      refl, },
    { intros w hw,
      exact h w, }}
end

variable [number_field K]

/-- The complex Haar measure giving measure 1 to the unit box with ℂ ≃ ℝ × ℝ -/
@[reducible]
def unit_measure : measure E :=
measure.prod (measure.pi (λ _, volume)) (measure.pi (λ _, complex.basis_one_I.add_haar))

instance : sigma_finite complex.basis_one_I.add_haar := infer_instance
instance : sigma_finite
  (measure.pi (λ w : { w : infinite_place K // is_complex w}, complex.basis_one_I.add_haar)) :=
  infer_instance

instance : measure.is_add_haar_measure (unit_measure K) :=
begin
  haveI : measure.is_add_haar_measure complex.basis_one_I.add_haar := infer_instance,
  haveI : has_measurable_add ℂ := infer_instance,
  have : measure.is_add_haar_measure (measure.pi (λ w : { w : infinite_place K // is_complex w },
    complex.basis_one_I.add_haar)) := @measure.pi.is_add_haar_measure _ _ _ _ _ _ _ _ _ _,
  convert measure.prod.is_add_haar_measure _ _,
  any_goals { apply_instance, },
end

lemma convex_body_real.volume (f : infinite_place K → nnreal) :
  measure.pi (λ _, volume) (convex_body_real K f) =
    2 ^ card {w : infinite_place K // is_real w} *
    finset.univ.prod (λ w : {w : infinite_place K // is_real w}, f w) :=
begin
  rw convex_body_real,
  rw measure.pi_pi,
  simp_rw real.volume_ball,
  simp_rw ennreal.of_real_mul (by norm_num : 0 ≤ (2 : ℝ)),
  simp only [ennreal.of_real_bit0, ennreal.of_real_one, ennreal.of_real_coe_nnreal],
  rw finset.prod_mul_distrib,
  rw finset.prod_const,
  rw finset.card_univ,
end

lemma convex_body_complex.volume (f : infinite_place K → nnreal) :
  (measure.pi (λ _, complex.basis_one_I.add_haar)) (convex_body_complex K f) =
  (complex.basis_one_I.add_haar) (metric.ball 0 1) ^
  card {w : infinite_place K // is_complex w} *
  finset.univ.prod (λ w : {w : infinite_place K // is_complex w}, (f w) ^ 2) :=
begin
  haveI : measure.is_add_haar_measure complex.basis_one_I.add_haar := infer_instance,
  haveI : has_measurable_add ℂ := infer_instance,
  haveI : measure.is_add_haar_measure (measure.pi (λ w : { w : infinite_place K // is_complex w },
    complex.basis_one_I.add_haar)) := @measure.pi.is_add_haar_measure _ _ _ _ _ _ _ _ _ _,
  rw convex_body_complex,
  rw measure.pi_pi,
  conv { to_lhs, congr, skip, funext,
    rw measure.add_haar_ball complex.basis_one_I.add_haar 0 (f i).prop,
    rw ennreal.of_real_pow (f i).prop, },
  rw finset.prod_mul_distrib,
  rw finset.prod_const,
  rw mul_comm,
  rw complex.finrank_real_complex,
  rw finset.card_univ,
  simp_rw ennreal.of_real_coe_nnreal,
end

/-- The fudge factor that appears the volume of `convex_body`.-/
def constant_volume : ennreal := 2 ^ card {w : infinite_place K // is_real w} *
  (complex.basis_one_I.add_haar) (metric.ball 0 1) ^ card {w : infinite_place K // is_complex w}

lemma constant_volume_pos : 0 < (constant_volume K) :=
begin
  refine ennreal.mul_pos _ _,
  { refine ennreal.pow_ne_zero _ _,
    exact ne_zero.ne 2, },
  { refine ennreal.pow_ne_zero _ _,
    refine ne_of_gt _,
    exact metric.measure_ball_pos _ _ (by norm_num), },
end

lemma constant_volume_lt_top : (constant_volume K) < ⊤ :=
begin
  refine ennreal.mul_lt_top _ _,
  { refine ne_of_lt _,
    refine ennreal.pow_lt_top _ _,
    exact lt_top_iff_ne_top.mpr ennreal.two_ne_top, },
  { refine ne_of_lt _,
    refine ennreal.pow_lt_top _ _,
    exact measure_ball_lt_top, },
end

lemma convex_body.volume (f : infinite_place K → nnreal) :
  (unit_measure K) (convex_body K f) = (constant_volume K) *
    finset.univ.prod (λ w : infinite_place K, (ite (w.is_real) (f w) (f w ^ 2))) :=
begin
  rw measure.prod_prod _ _,
  { rw convex_body_real.volume,
    rw convex_body_complex.volume,
    rw constant_volume,
    rw finset.prod_ite,
    have : ∀ (w : infinite_place K), w ∈ finset.filter (λ w : infinite_place K, w.is_real)
      finset.univ ↔ w.is_real,
    { intro _,
      simp only [finset.mem_filter, finset.mem_univ, true_and], },
    rw finset.prod_subtype _ this _,
    have : ∀ (w : infinite_place K), w ∈ finset.filter (λ w : infinite_place K, ¬ w.is_real)
      finset.univ ↔ w.is_complex,
    { intro _,
      simp only [not_is_real_iff_is_complex, finset.mem_filter, finset.mem_univ, true_and], },
    rw finset.prod_subtype _ this _,
    rw ← mul_assoc,
    nth_rewrite 1 mul_assoc,
    nth_rewrite 2 mul_comm,
    rw ← mul_assoc,
    rw ← mul_assoc, },
  { apply_instance, },
end

/-- The bound that appears in Minkowski theorem, see
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_finrank_lt_measure`.-/
def minkowski_bound : ennreal := (unit_measure K) (zspan.fundamental_domain (lattice_basis K)) *
  2 ^ (finrank ℝ E)

lemma minkowski_bound_lt_top : minkowski_bound K < ⊤ :=
begin
  refine ennreal.mul_lt_top _ _,
  { refine ne_of_lt _,
    refine metric.bounded.measure_lt_top _,
    exact zspan.metric.bounded_fundamental_domain (lattice_basis K), },
  { refine ne_of_lt _,
    refine ennreal.pow_lt_top _ _,
    exact lt_top_iff_ne_top.mpr ennreal.two_ne_top, },
end

lemma exists_ne_zero_mem_ring_of_integers_le {f : (infinite_place K) → nnreal}
  (h : minkowski_bound K < (unit_measure K) (convex_body K f)) :
  ∃ (a : 𝓞 K), a ≠ 0 ∧ ∀ w : infinite_place K, w a < f w :=
begin
  have t1 := zspan.is_add_fundamental_domain (lattice_basis K) (unit_measure K),
  haveI : countable (submodule.span ℤ (set.range (lattice_basis K))).to_add_subgroup,
    { change countable (submodule.span ℤ (set.range (lattice_basis K)) : set E),
      rw ← integral_basis_span,
      exact integer_lattice.countable K, },
  have := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_finrank_lt_measure
    (unit_measure K) t1 h (convex_body.symmetric K f) (convex_body.convex K f),
  obtain ⟨x, hnz, hmem⟩ := this,
  rsuffices ⟨a, ha1, ha2⟩ : ∃ a : 𝓞 K, a ≠ 0 ∧ canonical_embedding K a = x,
  { rw ← ha2 at hmem,
    rw convex_body_mem at hmem,
    use a,
    exact ⟨ha1, hmem⟩, },
  have : (x : E) ∈ (integer_lattice K),
  { rw ← set_like.mem_coe,
    rw integral_basis_span,
    have := set_like.coe_mem x,
    rwa ← set_like.mem_coe at this, },
  obtain ⟨z, hz1, hz2⟩ := this,
  use z,
  exact hz1,
  split,
  { apply subtype.ne_of_val_ne,
    rw [subtype.val_eq_coe],
    rw [subtype.val_eq_coe],
    rw subtype.coe_mk,
    rw [algebra_map.coe_zero],
    rw ← map_ne_zero_iff _ (injective_canonical_embedding K),
    rw hz2,
    simp only [hnz, ne.def, submodule.coe_eq_zero, not_false_iff], },
  { exact hz2, },
end

end number_field.canonical_embedding
