/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/

import number_theory.number_field.basic
import analysis.complex.polynomial
import topology.instances.complex
import topology.metric_space.basic

/-!
# Embeddings of number fields
This file defines the embeddings of a number field into an algebraic closed field.

## Main Results
* `number_field.embeddings.range_eval_eq_root_set_minpoly`: let `x ∈ K` with `K` number field and
  let `A` be an algebraic closed field of char. 0, then the images of `x` by the embeddings of `K`
   in `A` are exactly the roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `number_field.embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.

## Tags
number field, embeddings, places, infinite places
-/

open_locale classical

namespace number_field.embeddings

section fintype

open finite_dimensional

variables (K : Type*) [field K] [number_field K]
variables (A : Type*) [field A] [char_zero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : fintype (K →+* A) := fintype.of_equiv (K →ₐ[ℚ] A)
ring_hom.equiv_rat_alg_hom.symm

variables [is_alg_closed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
lemma card : fintype.card (K →+* A) = finrank ℚ K :=
by rw [fintype.of_equiv_card ring_hom.equiv_rat_alg_hom.symm, alg_hom.card]

end fintype

section roots

open set polynomial

variables (K A : Type*) [field K] [number_field K]
  [field A] [algebra ℚ A] [is_alg_closed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
lemma range_eval_eq_root_set_minpoly : range (λ φ : K →+* A, φ x) = (minpoly ℚ x).root_set A :=
begin
  convert (number_field.is_algebraic K).range_eval_eq_root_set_minpoly A x using 1,
  ext a,
  exact ⟨λ ⟨φ, hφ⟩, ⟨φ.to_rat_alg_hom, hφ⟩, λ ⟨φ, hφ⟩, ⟨φ.to_ring_hom, hφ⟩⟩,
end

end roots

section bounded

open finite_dimensional polynomial set

variables {K : Type*} [field K] [number_field K]
variables {A : Type*} [normed_field A] [is_alg_closed A] [normed_algebra ℚ A]

lemma coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ‖φ x‖ ≤ B) (i : ℕ) :
  ‖(minpoly ℚ x).coeff i‖ ≤ (max B 1) ^ (finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K) / 2) :=
begin
  have hx := is_separable.is_integral ℚ x,
  rw [← norm_algebra_map' A, ← coeff_map (algebra_map ℚ A)],
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx) (is_alg_closed.splits_codomain _)
    (minpoly.nat_degree_le hx) (λ z hz, _) i,
  classical, rw ← multiset.mem_to_finset at hz,
  obtain ⟨φ, rfl⟩ := (range_eval_eq_root_set_minpoly K A x).symm.subset hz,
  exact h φ,
end

variables (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
lemma finite_of_norm_le (B : ℝ) :
  {x : K | is_integral ℤ x ∧ ∀ φ : K →+* A, ‖φ x‖ ≤ B}.finite :=
begin
  let C := nat.ceil ((max B 1) ^ (finrank ℚ K) * (finrank ℚ K).choose ((finrank ℚ K) / 2)),
  have := bUnion_roots_finite (algebra_map ℤ K) (finrank ℚ K) (finite_Icc (-C : ℤ) C),
  refine this.subset (λ x hx, _), simp_rw mem_Union,
  have h_map_ℚ_minpoly := minpoly.gcd_domain_eq_field_fractions' ℚ hx.1,
  refine ⟨_, ⟨_, λ i, _⟩, (mem_root_set_iff (minpoly.ne_zero hx.1) x).2 (minpoly.aeval ℤ x)⟩,
  { rw [← (minpoly.monic hx.1).nat_degree_map (algebra_map ℤ ℚ), ← h_map_ℚ_minpoly],
    exact minpoly.nat_degree_le (is_integral_of_is_scalar_tower hx.1) },
  rw [mem_Icc, ← abs_le, ← @int.cast_le ℝ],
  refine (eq.trans_le _ $ coeff_bdd_of_norm_le hx.2 i).trans (nat.le_ceil _),
  rw [h_map_ℚ_minpoly, coeff_map, eq_int_cast, int.norm_cast_rat, int.norm_eq_abs, int.cast_abs],
end

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
lemma pow_eq_one_of_norm_eq_one {x : K}
  (hxi : is_integral ℤ x) (hx : ∀ φ : K →+* A, ‖φ x‖ = 1) :
  ∃ (n : ℕ) (hn : 0 < n), x ^ n = 1 :=
begin
  obtain ⟨a, -, b, -, habne, h⟩ := @set.infinite.exists_ne_map_eq_of_maps_to _ _ _ _
    ((^) x : ℕ → K) set.infinite_univ _ (finite_of_norm_le K A (1:ℝ)),
  { replace habne := habne.lt_or_lt,
    have : _, swap, cases habne, swap,
    { revert a b, exact this },
    { exact this b a h.symm habne },
    refine λ a b h hlt, ⟨a - b, tsub_pos_of_lt hlt, _⟩,
    rw [← nat.sub_add_cancel hlt.le, pow_add, mul_left_eq_self₀] at h,
    refine h.resolve_right (λ hp, _),
    specialize hx (is_alg_closed.lift (number_field.is_algebraic K)).to_ring_hom,
    rw [pow_eq_zero hp, map_zero, norm_zero] at hx, norm_num at hx },
  { exact λ a _, ⟨hxi.pow a, λ φ, by simp only [hx φ, norm_pow, one_pow, map_pow]⟩ },
end

end bounded

end number_field.embeddings

namespace number_field

section place

variables {A : Type*} [normed_division_ring A] {K : Type*} [field K] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def place : K → ℝ := norm ∘ φ

lemma places.nonneg (x : K) : 0 ≤ place φ x := by simp only [place, norm_nonneg]

@[simp]
lemma places.eq_zero_iff (x : K) : place φ x = 0 ↔ x = 0 :=
by simp only [place, norm_eq_zero, map_eq_zero]

@[simp]
lemma places.map_zero : place φ 0 = 0 :=
by simp only [place, function.comp_app, map_zero, norm_zero]

@[simp]
lemma places.map_one : place φ 1 = 1 :=
by simp only [place, function.comp_app, map_one, norm_one]

@[simp]
lemma places.map_inv (x : K) : place φ (x⁻¹) = (place φ x)⁻¹ :=
by simp only [place, function.comp_app, norm_inv, map_inv₀]

@[simp]
lemma places.map_mul (x y : K) : place φ (x * y) = (place φ x) * (place φ y) :=
by simp only [place, function.comp_app, map_mul, norm_mul]

lemma places.add_le (x y : K) : place φ (x + y) ≤ (place φ x) + (place φ y) :=
by simpa only [place, function.comp_app, map_add] using norm_add_le _ _

end place

end number_field

namespace number_field.complex_embeddings

open complex number_field

open_locale complex_conjugate

variables {K : Type*} [field K]

/-- The conjugate of a complex embedding as a complex embedding. -/
def conjugate (φ : K →+* ℂ) : K →+* ℂ := ring_hom.comp conj_ae.to_ring_equiv.to_ring_hom φ

lemma conjugate_coe_eq (φ : K →+* ℂ) (x : K) : (conjugate φ) x = conj (φ x) := rfl

lemma place_conjugate_eq_place (φ : K →+* ℂ) : place (conjugate φ) = place φ :=
by { ext1, simp only [place, conjugate_coe_eq, function.comp_app, norm_eq_abs, abs_conj] }

/-- A embedding into `ℂ` is real if it is fixed by complex conjugation. -/
def is_real (φ : K →+* ℂ): Prop := conjugate φ = φ

/-- A real embedding as a ring homomorphism from `K` to `ℝ` . -/
def real_embedding {φ : K →+* ℂ} (hφ : is_real φ) : K →+* ℝ :=
{ to_fun := λ x, (φ x).re,
  map_one' := by simp only [map_one, one_re],
  map_mul' := by simp only [complex.eq_conj_iff_im.mp (ring_hom.congr_fun hφ _), map_mul, mul_re,
  mul_zero, tsub_zero, eq_self_iff_true, forall_const],
  map_zero' := by simp only [map_zero, zero_re],
  map_add' := by simp only [map_add, add_re, eq_self_iff_true, forall_const], }

lemma real_embedding_eq_embedding {φ : K →+* ℂ} (hφ : is_real φ) (x : K) :
  (real_embedding hφ x : ℂ) = φ x :=
begin
  ext, { refl, },
  { rw [of_real_im, eq_comm, ← complex.eq_conj_iff_im],
    rw is_real at hφ,
    exact ring_hom.congr_fun hφ x, },
end

lemma place_real_embedding_eq_place {φ : K →+* ℂ} (hφ : is_real φ) :
  place (real_embedding hφ) = place φ :=
by { ext x, simp only [place, function.comp_apply, complex.norm_eq_abs, real.norm_eq_abs,
  ← real_embedding_eq_embedding hφ x, abs_of_real] }

lemma conjugate_conjugate_eq (φ : K →+* ℂ) :
  conjugate (conjugate φ) = φ :=
  by { ext1, simp only [conjugate_coe_eq, function.comp_app, star_ring_end_self_apply], }

lemma conjugate_is_real_iff {φ : K →+* ℂ} :
  is_real (conjugate φ) ↔ is_real φ := by simp only [is_real, conjugate_conjugate_eq, eq_comm]

end number_field.complex_embeddings

section infinite_places

open number_field

variables (K : Type*) [field K]

/-- An infinite place of a number field `K` is a place associated to a complex embedding. -/
def number_field.infinite_places := set.range (λ φ : K →+* ℂ, place φ)

lemma number_field.infinite_places.nonempty [number_field K] :
  nonempty (number_field.infinite_places K) :=
begin
  rsuffices ⟨φ⟩ : nonempty (K →+* ℂ), { use ⟨place φ, ⟨φ, rfl⟩⟩, },
  rw [← fintype.card_pos_iff, embeddings.card K ℂ],
  exact finite_dimensional.finrank_pos,
end

variables {K}

/-- Return the infinite place defined by a complex embedding `φ`. -/
noncomputable def number_field.infinite_place (φ : K →+* ℂ) : number_field.infinite_places K :=
⟨place φ, ⟨φ, rfl⟩⟩

namespace number_field.infinite_places

open number_field

instance : has_coe_to_fun (infinite_places K) (λ _, K → ℝ) := { coe := λ w, w.1 }

lemma infinite_place_eq_place (φ : K →+* ℂ) (x : K) :
  (infinite_place φ) x = (place φ) x := by refl

/-- Give an infinite place `w`, return an embedding `φ` such that `w = infinite_place φ` . -/
noncomputable def embedding (w : infinite_places K) : K →+* ℂ := (w.2).some

lemma infinite_place_embedding_eq_infinite_place (w : infinite_places K) :
  infinite_place (embedding w) = w :=
by { ext x, exact congr_fun ((w.2).some_spec) x }

lemma infinite_place_conjugate_eq_infinite_place (φ : K →+* ℂ) :
  infinite_place (complex_embeddings.conjugate φ) = infinite_place φ :=
by { ext1, exact complex_embeddings.place_conjugate_eq_place φ, }

@[simp]
lemma eq_zero_iff (w : infinite_places K) (x : K)  : w x = 0 ↔ x = 0 :=
by rw [← infinite_place_embedding_eq_infinite_place w, infinite_place_eq_place, places.eq_zero_iff]

@[simp]
lemma map_zero (w : infinite_places K) : w 0 = 0 :=
by rw [← infinite_place_embedding_eq_infinite_place w, infinite_place_eq_place, places.map_zero]

@[simp]
lemma map_one (w : infinite_places K) : w 1 = 1 :=
by rw [← infinite_place_embedding_eq_infinite_place w, infinite_place_eq_place, places.map_one]

@[simp]
lemma map_inv (w : infinite_places K) (x : K) : w (x⁻¹) = (w x)⁻¹ :=
by rw [← infinite_place_embedding_eq_infinite_place w, infinite_place_eq_place, places.map_inv,
  infinite_place_eq_place]

@[simp]
lemma map_mul (w : infinite_places K) (x y : K) : w (x * y) = (w x) * (w y) :=
by rw [← infinite_place_embedding_eq_infinite_place w, infinite_place_eq_place, places.map_mul,
    infinite_place_eq_place, infinite_place_eq_place]

lemma eq_iff {φ ψ : K →+* ℂ} :
  infinite_place φ = infinite_place ψ ↔ φ = ψ ∨ complex_embeddings.conjugate φ = ψ :=
begin
  split,
  { -- The proof goes as follows: Prove that the map ψ ∘ φ⁻¹ between φ(K) and ℂ is uniform
    -- continuous, thus it is either the inclusion or the complex conjugation.
    intro h₀,
    obtain ⟨j, hiφ⟩ := φ.injective.has_left_inverse ,
    let ι := ring_equiv.of_left_inverse hiφ,
    have hlip : lipschitz_with 1 (ring_hom.comp ψ ι.symm.to_ring_hom),
    { change lipschitz_with 1 (ψ ∘ ι.symm),
      apply lipschitz_with.of_dist_le_mul,
      intros x y,
      rw [nonneg.coe_one, one_mul, normed_field.dist_eq, ← map_sub, ← map_sub],
      apply le_of_eq,
      suffices : place φ ((ι.symm) (x - y)) = place ψ ((ι.symm) (x - y)),
      { simp_rw [place, function.comp_apply] at this,
        rw [← this, ← ring_equiv.of_left_inverse_apply hiφ _, ring_equiv.apply_symm_apply ι _],
        refl, },
      simp only [ ← infinite_place_eq_place, h₀], },
    cases (complex.uniform_continuous_ring_hom_eq_id_or_conj φ.field_range hlip.uniform_continuous),
    { left, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, },
    { right, ext1 x,
      convert (congr_fun h (ι x)).symm,
      exact (ring_equiv.apply_symm_apply ι.symm x).symm, }},
  { rintros (⟨h⟩ | ⟨h⟩),
    { exact congr_arg infinite_place h, },
    { rw ← infinite_place_conjugate_eq_infinite_place,
      exact congr_arg infinite_place h, }},
end

/-- An infinite place is real if it is defined by a real embedding. -/
def is_real (w : infinite_places K) : Prop :=
  ∃ φ : K →+* ℂ, complex_embeddings.is_real φ ∧ infinite_place φ = w

/-- An infinite place is complex if it is defined by a complex (ie. not real) embedding. -/
def is_complex (w : infinite_places K) : Prop :=
  ∃ φ : K →+* ℂ, ¬ complex_embeddings.is_real φ ∧ infinite_place φ = w

lemma embedding_or_conjugate_eq_embedding_place (φ : K →+* ℂ) :
  φ = embedding (infinite_place φ) ∨ complex_embeddings.conjugate φ = embedding (infinite_place φ)
  := by simp only [←eq_iff, infinite_place_embedding_eq_infinite_place]

lemma embedding_eq_embedding_infinite_place_real {φ : K →+* ℂ} (h : complex_embeddings.is_real φ) :
  φ = embedding (infinite_place φ) :=
begin
  rw complex_embeddings.is_real at h,
  convert embedding_or_conjugate_eq_embedding_place φ,
  simp only [h, or_self],
end

lemma infinite_place_is_real_iff {w : infinite_places K} :
  is_real w ↔ complex_embeddings.is_real (embedding w) :=
begin
  split,
  { rintros ⟨φ, ⟨hφ, rfl⟩⟩,
    rwa ← embedding_eq_embedding_infinite_place_real hφ, },
  { exact λ h, ⟨embedding w, h, infinite_place_embedding_eq_infinite_place w⟩, },
end

lemma infinite_place_is_complex_iff {w : infinite_places K} :
  is_complex w  ↔ ¬ complex_embeddings.is_real (embedding w) :=
begin
  split,
    { rintros ⟨φ, ⟨hφ, rfl⟩⟩,
      contrapose! hφ,
      cases eq_iff.mp (infinite_place_embedding_eq_infinite_place (infinite_place φ)),
      { rwa ← h, },
      { rw ← complex_embeddings.conjugate_is_real_iff at hφ,
        rwa ← h, }},
  { exact λ h, ⟨embedding w, h, infinite_place_embedding_eq_infinite_place w⟩, },
end

lemma not_is_real_iff_is_complex {w : infinite_places K} :
  ¬ is_real w ↔ is_complex w :=
by rw [infinite_place_is_complex_iff, infinite_place_is_real_iff]

variable [number_field K]
variable (K)

open fintype

noncomputable instance : fintype (infinite_places K) := set.fintype_range _

lemma card_real_embeddings_eq :
  card {φ : K →+* ℂ // complex_embeddings.is_real φ} = card {w : infinite_places K // is_real w} :=
begin
  rw fintype.card_of_bijective (_ : function.bijective _),
  { exact λ φ, ⟨infinite_place φ, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩, },
  split,
  { rintros ⟨φ, hφ⟩ ⟨ψ, hψ⟩ h,
    rw complex_embeddings.is_real at hφ,
    rw [subtype.mk_eq_mk, eq_iff, subtype.coe_mk, subtype.coe_mk, hφ, or_self] at h,
    exact subtype.eq h, },
  { exact λ ⟨w, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩, ⟨⟨φ, hφ1⟩,
    by { simp only [hφ2, subtype.coe_mk], }⟩, }
end

example {α : Type*} {p q : α} : ¬ (p = q) ↔  ¬ (q = p) := by refine ne_comm

lemma card_complex_embeddings_eq :
  card {φ : K →+* ℂ // ¬ complex_embeddings.is_real φ} =
  2 * card {w : infinite_places K // is_complex w} :=
begin
  let f : {φ : K →+* ℂ // ¬ complex_embeddings.is_real φ} → {w : infinite_places K // is_complex w},
  { exact λ φ, ⟨infinite_place φ, ⟨φ, ⟨φ.prop, rfl⟩⟩⟩, },
  suffices :  ∀ w : {w // is_complex w}, card {φ // f φ = w} = 2,
  { rw [fintype.card, fintype.card, mul_comm, ← algebra.id.smul_eq_mul, ← finset.sum_const],
    conv { to_rhs, congr, skip, funext, rw ← this x, rw fintype.card, },
    simp_rw finset.card_eq_sum_ones,
    exact (fintype.sum_fiberwise f (function.const _ 1)).symm, },
  { rintros ⟨⟨w, hw⟩, ⟨φ, ⟨hφ1, hφ2⟩⟩⟩,
    rw [fintype.card, finset.card_eq_two],
    refine ⟨⟨⟨φ, hφ1⟩, _⟩, ⟨⟨complex_embeddings.conjugate φ, _⟩, _⟩, ⟨_, _⟩⟩,
    { simpa only [f, hφ2], },
    { rwa iff.not complex_embeddings.conjugate_is_real_iff, },
    { simp only [f, ←hφ2, infinite_place_conjugate_eq_infinite_place, subtype.coe_mk], },
    { rwa [ne.def, subtype.mk_eq_mk, subtype.mk_eq_mk, ← ne.def, ne_comm], },
    ext ⟨⟨ψ, hψ1⟩, hψ2⟩,
    simpa only [finset.mem_univ, finset.mem_insert, finset.mem_singleton, true_iff, @eq_comm _ ψ _,
      ← eq_iff, hφ2] using subtype.mk_eq_mk.mp hψ2.symm, },
end

end number_field.infinite_places

end infinite_places

section canonical_embedding

open number_field

variables (K : Type*) [field K]

localized "notation `E` :=
  ({w : infinite_places K // infinite_places.is_real w} → ℝ) ×
  ({w : infinite_places K // infinite_places.is_complex w} → ℂ)"
  in embeddings

noncomputable def canonical_embedding : K →+* E :=
ring_hom.prod
  (pi.ring_hom (λ ⟨_, hw⟩,
    complex_embeddings.real_embedding (infinite_places.infinite_place_is_real_iff.mp hw)))
  (pi.ring_hom (λ ⟨w, _⟩, infinite_places.embedding w))

variable [number_field K]

lemma canonical_embedding_injective :
  function.injective (canonical_embedding K) :=
begin
  convert ring_hom.injective _,
  use [0, 1],
  obtain ⟨w⟩ := infinite_places.nonempty K,
  intro h,
  by_cases hw : infinite_places.is_real w,
  { have := congr_arg (λ x : E, x.1) h,
    have t1 := congr_fun this ⟨w, hw⟩,
    exact zero_ne_one t1, },
  { replace hw := infinite_places.not_is_real_iff_is_complex.mp hw,
    have := congr_arg (λ x : E, x.2) h,
    have t1 := congr_fun this ⟨w, hw⟩,
    exact zero_ne_one t1, }
end

lemma canonical_embedding_eval_real
  {w : infinite_places K} (hw : infinite_places.is_real w) (x : K) :
  ‖((canonical_embedding K) x).1 ⟨w, hw⟩‖ = w x :=
begin
  sorry,
end

lemma canonical_embedding_eval_complex
  {w : infinite_places K} (hw : infinite_places.is_complex w) (x : K) :
  ‖((canonical_embedding K) x).2 ⟨w, hw⟩‖ = w x :=
begin
  sorry,
end


lemma canonical_embedding.le_of_le {B : ℝ} {x : K} :
  ‖(canonical_embedding K) x‖ ≤ B ↔ ∀ w : infinite_places K, w x ≤ B :=
begin
  sorry,
end

example (B : set E) (hB0 : (0 : E) ∈ B) (hB : metric.bounded B) :
  (B ∩ ((canonical_embedding K) '' number_field.ring_of_integers K)).finite :=
begin
  sorry,
end

end canonical_embedding

section log_embedding

open number_field

variables (K : Type*) [field K]

noncomputable def log_embedding : Kˣ → (infinite_places K → ℝ) := λ x w, real.log (w x)

lemma log_embedding.map_one :
  log_embedding K 1 = 0 :=
by simpa only [log_embedding, infinite_places.map_one, real.log_one, units.coe_one]

lemma log_embedding.map_inv (x : Kˣ) :
  log_embedding K x⁻¹ = - log_embedding K x :=
by simpa only [log_embedding, infinite_places.map_inv, real.log_inv, units.coe_inv]

lemma log_embedding.map_mul (x y : Kˣ) :
  log_embedding K (x * y) = log_embedding K x + log_embedding K y :=
by simpa only [log_embedding, infinite_places.map_mul, real.log_mul, units.coe_mul, ne.def,
  infinite_places.eq_zero_iff, units.ne_zero, not_false_iff]

end log_embedding
