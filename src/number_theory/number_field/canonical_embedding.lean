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
The canonical embedding of a number field `K` of signature `(r₁, r_₂)` is the ring homomorphism
`K →+* ℝ^r₁ × ℂ^r₂` that sends `x ∈ K` to `(φ_₁(x),...,φ_r₁(x)) × (ψ_₁(x),..., ψ_r₂(x))` where
`φ_₁,...,φ_r₁` are its real embeddings and `ψ_₁,..., ψ_r₂` are its complex embeddings (up to
complex conjugation).

## Main Results
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

localized "notation `E` :=
  ({w : infinite_place K // is_real w} → ℝ) × ({w : infinite_place K // is_complex w} → ℂ)"
  in canonical_embedding

lemma number_field.canonical_embedding.rank [number_field K] :
  finrank ℝ E = finrank ℚ K :=
begin
  haveI : module.free ℝ ℂ := infer_instance,
  rw module.free.finrank_prod,
  rw module.free.finrank_pi,
  rw module.free.finrank_pi_fintype,
  rw complex.finrank_real_complex,
  rw finset.sum_const,
  rw finset.card_univ,
  rw ← card_real_embeddings,
  rw algebra.id.smul_eq_mul,
  rw mul_comm,
  rw ← card_complex_embeddings,
  rw ← number_field.embeddings.card K ℂ,
  rw fintype.card_subtype_compl,
  rw nat.add_sub_of_le (fintype.card_subtype_le _),
end

lemma number_field.canonical_embedding.nontrivial [number_field K] : nontrivial E :=
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

/-- The canonical embedding of a number field of signature `(s,t)` into `ℝ^s × ℂ^t`. -/
def number_field.canonical_embedding : K →+* E :=
ring_hom.prod
  (pi.ring_hom (λ w, w.prop.embedding))
  (pi.ring_hom (λ w, w.val.embedding))

lemma number_field.injective_canonical_embedding [number_field K] :
  function.injective (number_field.canonical_embedding K) :=
begin
  convert ring_hom.injective _,
  exact (number_field.canonical_embedding.nontrivial K),
end

namespace number_field.canonical_embedding

open number_field number_field.canonical_embedding number_field.infinite_place finite_dimensional
  measure_theory

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
  ‖(canonical_embedding K) x‖ ≤ r ↔ ∀ w : infinite_place K, w x ≤ r :=
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

variable (K)

/-- The image of the ring of integers of `K` as a subring. -/
def integer_lattice : subring E :=
subring.map (canonical_embedding K) (𝓞 K).to_subring

/-- The ring equiv between the ring of integers of `K` and the integer lattice. -/
def integer_linear_equiv [number_field K]: (𝓞 K) ≃ₗ[ℤ] (integer_lattice K) :=
begin
  refine linear_equiv.of_bijective _ _,
  { refine linear_map.mk _ _ _,
    exact λ x, ⟨canonical_embedding K x, x, subtype.mem x, rfl⟩,
    { intros _ _,
      simpa only [(canonical_embedding K).map_add, add_mem_class.coe_add], },
    { intros _ _,
      simpa only [zsmul_eq_mul, mul_mem_class.coe_mul, subring_class.coe_int_cast, map_mul,
        map_int_cast], }},
  { split,
    { intros x y hxy,
      rw ← subtype.coe_inj,
      apply injective_canonical_embedding K,
      rw linear_map.coe_mk at hxy,
      rwa subtype.mk_eq_mk at hxy, },
    { rintros ⟨_, ⟨a, ⟨ha, rfl⟩⟩⟩,
      use a,
      exact ha,
      refl, }},
end

lemma integer_lattice_discrete [number_field K] (r : ℝ) :
  ((integer_lattice K : set E) ∩ (metric.closed_ball 0 r)).finite :=
begin
  obtain hr | hr := lt_or_le r 0,
  { convert set.finite_empty,
    rw metric.closed_ball_eq_empty.mpr hr,
    exact set.inter_empty _, },
  { have heq : ∀ x : K, canonical_embedding K x ∈ (metric.closed_ball (0 : E) r) ↔
      ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ r,
    { simp_rw [← place_apply, ← infinite_place.coe_mk, mem_closed_ball_zero_iff,
        le_of_le],
      exact λ x, le_iff_le x r, },
    convert set.finite.image (canonical_embedding K) (embeddings.finite_of_norm_le K ℂ r),
    ext, split,
    { rintros ⟨⟨x, ⟨hx1, rfl⟩⟩, hx2⟩,
      exact ⟨x, ⟨⟨hx1, (heq x).mp hx2⟩, rfl⟩⟩, },
    { rintros ⟨x, ⟨⟨ hx1, hx2⟩, rfl⟩⟩,
      exact ⟨⟨x, ⟨hx1, rfl⟩⟩, (heq x).mpr hx2⟩, }},
end

lemma integer_lattice.countable [number_field K] : countable (integer_lattice K) :=
begin
  suffices : (⋃ n : ℕ, ((integer_lattice K : set E) ∩ (metric.closed_ball 0 n))).countable,
  { refine set.countable.to_subtype (set.countable.mono _ this),
    rintros _ ⟨x, ⟨hx, rfl⟩⟩,
    rw set.mem_Union,
    use nat.ceil (‖canonical_embedding K x‖),
    exact ⟨⟨x, hx, rfl⟩, mem_closed_ball_zero_iff.mpr (nat.le_ceil _)⟩, },
  { exact set.countable_Union (λ n, (integer_lattice_discrete K n).countable), },
end

section basis

open_locale complex_conjugate

variable (K)

def _root_.number_field.embedding_embedding : K →+* (K →+* ℂ) → ℂ :=
{ to_fun := λ x φ, φ x,
  map_zero' :=
  begin
    funext φ,
    exact map_zero φ,
  end,
  map_one' :=
  begin
    funext φ,
    exact map_one φ,
  end,
  map_add' :=
  begin
    intros x y,
    funext φ,
    exact map_add φ x y,
  end,
  map_mul' :=
  begin
    intros x y,
    funext φ,
    exact map_mul φ x y,
  end }

def comm_map : E →ₗ[ℝ] ((K →+* ℂ) → ℂ) :=
{ to_fun :=
  begin
  rintro ⟨xr, xc⟩,
  intro φ,
  by_cases h : complex_embedding.is_real φ,
  { exact xr (mk_real K ⟨φ, h⟩), },
  { let w := mk_complex K ⟨φ, h⟩,
    exact ite (w.1.embedding = φ) (xc w) (conj (xc w)), }
  end,
  map_add' :=
  begin
    rintros ⟨_, _⟩ ⟨_, _⟩,
    ext1 φ,
    by_cases h : complex_embedding.is_real φ,
    { simp only [dif_pos h, prod.mk_add_mk, pi.add_apply, complex.of_real_add], },
    { simp only [dif_neg h, subtype.val_eq_coe, mk_complex_coe, subtype.coe_mk, prod.mk_add_mk,
        pi.add_apply, map_add],
      split_ifs;
      simp only [eq_self_iff_true], },
  end,
  map_smul' :=
  begin
    rintros _ ⟨_, _⟩,
    ext1 φ,
    by_cases h : complex_embedding.is_real φ,
    { simp only [dif_pos h, prod.smul_mk, pi.smul_apply, algebra.id.smul_eq_mul,
        complex.of_real_mul, ring_hom.id_apply, is_R_or_C.of_real_smul], },
    { simp only [dif_neg h, prod.smul_mk, pi.smul_apply, complex.real_smul, map_mul,
        is_R_or_C.conj_of_real, ring_hom.id_apply, mul_ite], }
  end }

lemma commutes (x : K) :
  number_field.embedding_embedding K x = comm_map K (canonical_embedding K x) :=
begin
  ext1 φ,
  simp only [canonical_embedding, _root_.number_field.embedding_embedding, comm_map,
    subtype.val_eq_coe, ring_hom.coe_mk, pi.ring_hom_apply, ring_hom.prod_apply, linear_map.coe_mk],
  by_cases h : complex_embedding.is_real φ,
  { simp only [dif_pos h],
    rw ← complex_embedding.is_real.coe_embedding_apply h x,
    congr,
    simp only [h, mk_real_coe, subtype.coe_mk, complex_embeddings.is_real.embedding_mk], },
  { simp only [dif_neg h],
    split_ifs with h1,
    { exact congr_fun (congr_arg coe_fn h1.symm) x, },
    { rw ((or_iff_right h1).mp (mk_complex_embedding K ⟨φ, h⟩)),
      simp only [complex_embedding.conjugate_coe_eq, star_ring_end_self_apply, subtype.coe_mk], }}
end

def lattice_basis [number_field K] : basis (free.choose_basis_index ℤ (𝓞 K)) ℝ E :=
begin
  let b := integral_basis K,
  suffices : linear_independent ℝ (λ i, canonical_embedding K (b i )),
  { have t1 : ⊤ ≤ submodule.span ℝ (set.range (canonical_embedding K ∘ b)),
    { rw linear_independent_iff_card_le_finrank_span at this,
      rw ← free.finrank_eq_card_choose_basis_index at this,
      rw rank_eq_rank at this,
      rw ← number_field.canonical_embedding.rank at this,
      have t10 : finrank ℝ E = finrank ℝ (⊤ : submodule ℝ E) := finrank_top.symm,
      rw t10 at this,
      exact le_of_eq (eq_of_le_of_finrank_le le_top this).symm, },
    refine basis.mk this t1, },
  let h : (K →+* ℂ) ≃ free.choose_basis_index ℤ (𝓞 K),
  { refine equiv_of_card_eq _,
    rw ← finrank_eq_card_basis b,
    exact embeddings.card K ℂ, },
  let eb : (K →+* ℂ) → E := λ i, canonical_embedding K (b (h i)),
  suffices : linear_independent ℝ eb,
  { convert linear_independent.comp this h.symm (equiv.symm h).injective,
    ext1,
    simp only [eb, function.comp_app, equiv.apply_symm_apply], },
  suffices : linear_independent ℝ ((comm_map K) ∘ eb) ,
  { exact linear_independent.of_comp _ this, },
  let fb := λ i, number_field.embedding_embedding K (b (h i)),
  have : (comm_map K) ∘ eb = fb,
  { ext1 i,
    dsimp only [eb , fb],
    rw commutes _, },
  rw this,
  let B := pi.basis_fun ℂ (K →+* ℂ),
  let M := B.to_matrix fb,
  let N := algebra.embeddings_matrix_reindex ℚ ℂ (λ i, b (h i)) ring_hom.equiv_rat_alg_hom,
  have t0 : M = N.transpose,
  { ext1 φ j,
    dsimp only [B, M, N, fb, number_field.embedding_embedding],
    rw basis.to_matrix_apply _ _ φ j,
    rw pi.basis_fun_repr,
    dsimp [algebra.embeddings_matrix_reindex],
    refl, },
  have t1 := algebra.discr_not_zero_of_basis ℚ b,
  have t2 := algebra.discr_eq_det_embeddings_matrix_reindex_pow_two ℚ ℂ (λ i, b (h i))
    ring_hom.equiv_rat_alg_hom,
  have t3 : N.det ≠ 0,
  { contrapose! t1,
    dsimp [N] at t1,
    rw t1 at t2,
    rw zero_pow (by norm_num : 0 < 2) at t2,
    rw map_eq_zero_iff _ (algebra_map ℚ ℂ).injective at t2,
    rw ← algebra.discr_reindex ℚ b h.symm,
    convert t2,
    exact equiv.symm_symm h, },
  have t4 : M.det ≠ 0,
  { have t40 := congr_arg matrix.det t0,
    rw t40,
    rwa matrix.det_transpose, },
  have t5 : is_unit(B.det fb),
  { rw basis.det_apply,
    rw is_unit_iff_ne_zero,
    exact t4, },
  rw ← is_basis_iff_det at t5,
  refine t5.1.restrict_scalars (smul_left_injective _ (by norm_num)),
end

lemma lattice_basis_apply [number_field K] (i : free.choose_basis_index ℤ (𝓞 K)) :
  (lattice_basis K) i = (canonical_embedding K) (integral_basis K i) :=
by simp only [lattice_basis, basis.coe_mk]

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

def convex_body_real (f : infinite_place K → nnreal) : set ({w : infinite_place K // is_real w} → ℝ)
:= set.pi set.univ (λ w, metric.ball 0 (f w))

def convex_body_complex (f : infinite_place K → nnreal) :
  set ({w : infinite_place K // is_complex w} → ℂ) :=
set.pi set.univ (λ w, metric.ball 0 (f w))

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
