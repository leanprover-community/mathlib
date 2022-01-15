/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import analysis.inner_product_space.projection
import analysis.normed_space.lp_space

/-!
# Inner product space structure on `lp 2`

Given a family `(G : ι → Type*) [Π i, inner_product_space 𝕜 (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : Π i, G i` for which `∑' i, ∥f i∥ ^ 2`, the sum of the norms-squared, is
summable.  This construction is sometimes called the Hilbert sum of the family `G`.

The space `lp G 2` already held a normed space structure, `lp.normed_space`, so the work in this
file is to define the inner product and show it is compatible.

If each `G i` is a Hilbert space (i.e., complete), then the Hilbert sum `lp G 2` is also a Hilbert
space; again this follows from `lp.complete_space`, the case of general `p`.

By choosing `G` to be `ι → 𝕜`, the Hilbert space `ℓ²(ι, 𝕜)` may be seen as a special case of this
construction.

## Keywords

Hilbert space, Hilbert sum, l2
-/

open is_R_or_C submodule filter
open_locale big_operators nnreal ennreal classical complex_conjugate

local attribute [instance] fact_one_le_two_ennreal

noncomputable theory

variables {ι : Type*}
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E] [cplt : complete_space E]
variables {G : ι → Type*} [Π i, inner_product_space 𝕜 (G i)]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

notation `ℓ²(` ι `,` 𝕜 `)` := lp (λ i : ι, 𝕜) 2

namespace lp

lemma summable_inner (f g : lp G 2) : summable (λ i, ⟪f i, g i⟫) :=
begin
  -- Apply the Direct Comparison Test, comparing with ∑' i, ∥f i∥ * ∥g i∥ (summable by Hölder)
  refine summable_of_norm_bounded (λ i, ∥f i∥ * ∥g i∥) (lp.summable_mul _ f g) _,
  { rw real.is_conjugate_exponent_iff; norm_num },
  intros i,
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm _ _,
end

instance : inner_product_space 𝕜 (lp G 2) :=
{ inner := λ f g, ∑' i, ⟪f i, g i⟫,
  norm_sq_eq_inner := λ f, begin
    calc ∥f∥ ^ 2 = ∥f∥ ^ (2:ℝ≥0∞).to_real : by norm_cast
    ... = ∑' i, ∥f i∥ ^ (2:ℝ≥0∞).to_real : lp.norm_rpow_eq_tsum _ f
    ... = ∑' i, ∥f i∥ ^ 2 : by norm_cast
    ... = ∑' i, re ⟪f i, f i⟫ : by simp only [norm_sq_eq_inner]
    ... = re (∑' i, ⟪f i, f i⟫) : (is_R_or_C.re_clm.map_tsum _).symm
    ... = _ : by congr,
    { norm_num },
    { exact summable_inner f f },
  end,
  conj_sym := λ f g, begin
    calc conj _ = conj ∑' i, ⟪g i, f i⟫ : by congr
    ... = ∑' i, conj ⟪g i, f i⟫ : is_R_or_C.conj_cle.map_tsum
    ... = ∑' i, ⟪f i, g i⟫ : by simp only [inner_conj_sym]
    ... = _ : by congr,
  end,
  add_left := λ f₁ f₂ g, begin
    calc _ = ∑' i, ⟪(f₁ + f₂) i, g i⟫ : _
    ... = ∑' i, (⟪f₁ i, g i⟫ + ⟪f₂ i, g i⟫) :
          by simp only [inner_add_left, pi.add_apply, coe_fn_add]
    ... = (∑' i, ⟪f₁ i, g i⟫) + ∑' i, ⟪f₂ i, g i⟫ : tsum_add _ _
    ... = _ : by congr,
    { congr, },
    { exact summable_inner f₁ g },
    { exact summable_inner f₂ g }
  end,
  smul_left := λ f g c, begin
    calc _ = ∑' i, ⟪c • f i, g i⟫ : _
    ... = ∑' i, conj c * ⟪f i, g i⟫ : by simp only [inner_smul_left]
    ... = conj c * ∑' i, ⟪f i, g i⟫ : tsum_mul_left
    ... = _ : _,
    { simp only [coe_fn_smul, pi.smul_apply] },
    { congr },
  end,
  .. lp.normed_space }

lemma inner_eq_tsum (f g : lp G 2) : ⟪f, g⟫ = ∑' i, ⟪f i, g i⟫ := rfl

lemma has_sum_inner (f g : lp G 2) : has_sum (λ i, ⟪f i, g i⟫) ⟪f, g⟫ :=
(summable_inner f g).has_sum

lemma inner_single_left (i : ι) (a : G i) (f : lp G 2) : ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫ :=
begin
  refine (has_sum_inner (lp.single 2 i a) f).unique _,
  convert has_sum_ite_eq i ⟪a, f i⟫,
  ext j,
  rw lp.single_apply,
  split_ifs,
  { subst h },
  { simp }
end

lemma inner_single_right (i : ι) (a : G i) (f : lp G 2) : ⟪f, lp.single 2 i a⟫ = ⟪f i, a⟫ :=
by simpa [inner_conj_sym] using congr_arg conj (inner_single_left i a f)

end lp

namespace orthogonal_family
variables {V : Π i, G i →ₗᵢ[𝕜] E} (hV : orthogonal_family 𝕜 V)

include cplt hV

protected lemma summable_of_lp (f : lp G 2) : summable (λ i, V i (f i)) :=
begin
  rw hV.summable_iff_norm_sq_summable,
  convert (lp.mem_ℓp f).summable _,
  { norm_cast },
  { norm_num }
end

/-- A mutually orthogonal family of subspaces of `E` induce a linear isometry from `lp 2` of the
subspaces into `E`. -/
protected def linear_isometry : lp G 2 →ₗᵢ[𝕜] E :=
{ to_fun := λ f, ∑' i, V i (f i),
  map_add' := λ f g, by simp only [tsum_add (hV.summable_of_lp f) (hV.summable_of_lp g),
    lp.coe_fn_add, pi.add_apply, linear_isometry.map_add],
  map_smul' := λ c f, by simpa only [linear_isometry.map_smul, pi.smul_apply, lp.coe_fn_smul]
    using tsum_const_smul (hV.summable_of_lp f),
  norm_map' := λ f, begin
    classical, -- needed for lattice instance on `finset ι`, for `filter.at_top_ne_bot`
    have H : 0 < (2:ℝ≥0∞).to_real := by norm_num,
    suffices : ∥∑' (i : ι), V i (f i)∥ ^ ((2:ℝ≥0∞).to_real) = ∥f∥ ^ ((2:ℝ≥0∞).to_real),
    { exact real.rpow_left_inj_on H.ne' (norm_nonneg _) (norm_nonneg _) this },
    refine tendsto_nhds_unique  _ (lp.has_sum_norm H f),
    convert (hV.summable_of_lp f).has_sum.norm.rpow_const (or.inr H.le),
    ext s,
    exact_mod_cast (hV.norm_sum f s).symm,
  end }

protected lemma linear_isometry_apply (f : lp G 2) :
  hV.linear_isometry f = ∑' i, V i (f i) :=
rfl

protected lemma has_sum_linear_isometry (f : lp G 2) :
  has_sum (λ i, V i (f i)) (hV.linear_isometry f) :=
(hV.summable_of_lp f).has_sum

@[simp] protected lemma linear_isometry_apply_single {i : ι} (x : G i) :
  hV.linear_isometry (lp.single 2 i x) = V i x :=
begin
  rw [hV.linear_isometry_apply, ← tsum_ite_eq i (V i x)],
  congr,
  ext j,
  rw [lp.single_apply],
  split_ifs,
  { subst h },
  { simp }
end

@[simp] protected lemma linear_isometry_apply_dfinsupp_sum_single (W₀ : Π₀ (i : ι), G i) :
  hV.linear_isometry (W₀.sum (lp.single 2)) = W₀.sum (λ i, V i) :=
begin
  have : hV.linear_isometry (∑ i in W₀.support, lp.single 2 i (W₀ i))
    = ∑ i in W₀.support, hV.linear_isometry (lp.single 2 i (W₀ i)),
  { exact hV.linear_isometry.to_linear_map.map_sum },
  simp [dfinsupp.sum, this] {contextual := tt},
end

/-- The canonical linear isometry from the `lp 2` of a mutually orthogonal family of subspaces of
`E` into E, has range the closure of the span of the subspaces. -/
protected lemma range_linear_isometry [Π i, complete_space (G i)] :
  hV.linear_isometry.to_linear_map.range = (⨆ i, (V i).to_linear_map.range).topological_closure :=
begin
  classical,
  refine le_antisymm _ _,
  { rintros x ⟨f, rfl⟩,
    refine mem_closure_of_tendsto (hV.has_sum_linear_isometry f) (eventually_of_forall _),
    intros s,
    refine sum_mem (supr (λ i, (V i).to_linear_map.range)) _,
    intros i hi,
    refine mem_supr_of_mem i _,
    exact linear_map.mem_range_self _ (f i) },
  { apply topological_closure_minimal,
    { refine supr_le _,
      rintros i x ⟨x, rfl⟩,
      use lp.single 2 i x,
      convert hV.linear_isometry_apply_single _ },
    exact hV.linear_isometry.isometry.uniform_inducing.is_complete_range.is_closed }
end

/-- A mutually orthogonal family of complete subspaces of `E`, whose range is dense in `E`, induces
a linear isometry from E to `lp 2` of the subspaces.

Note that this goes in the opposite direction from `orthogonal_family.linear_isometry`. -/
noncomputable def linear_isometry_equiv [Π i, complete_space (G i)]
  (hV' : (⨆ i, (V i).to_linear_map.range).topological_closure = ⊤) :
  E ≃ₗᵢ[𝕜] lp G 2 :=
linear_isometry_equiv.symm $
linear_isometry_equiv.of_surjective
hV.linear_isometry
begin
  refine linear_map.range_eq_top.mp _,
  rw ← hV',
  rw hV.range_linear_isometry,
end

protected lemma linear_isometry_equiv_symm_apply [Π i, complete_space (G i)]
  (hV' : (⨆ i, (V i).to_linear_map.range).topological_closure = ⊤) (w : lp G 2) :
  (hV.linear_isometry_equiv hV').symm w = ∑' i, V i (w i) :=
by simp [orthogonal_family.linear_isometry_equiv, orthogonal_family.linear_isometry_apply]

protected lemma has_sum_linear_isometry_equiv_symm [Π i, complete_space (G i)]
  (hV' : (⨆ i, (V i).to_linear_map.range).topological_closure = ⊤) (w : lp G 2) :
  has_sum (λ i, V i (w i)) ((hV.linear_isometry_equiv hV').symm w) :=
by simp [orthogonal_family.linear_isometry_equiv, orthogonal_family.has_sum_linear_isometry]

@[simp] protected lemma linear_isometry_equiv_symm_apply_single [Π i, complete_space (G i)]
  (hV' : (⨆ i, (V i).to_linear_map.range).topological_closure = ⊤) {i : ι} (x : G i) :
  (hV.linear_isometry_equiv hV').symm (lp.single 2 i x) = V i x :=
by simp [orthogonal_family.linear_isometry_equiv, orthogonal_family.linear_isometry_apply_single]

@[simp] protected lemma linear_isometry_equiv_symm_apply_dfinsupp_sum_single
  [Π i, complete_space (G i)]
  (hV' : (⨆ i, (V i).to_linear_map.range).topological_closure = ⊤) (W₀ : Π₀ (i : ι), G i) :
  (hV.linear_isometry_equiv hV').symm (W₀.sum (lp.single 2)) = (W₀.sum (λ i, V i)) :=
by simp [orthogonal_family.linear_isometry_equiv,
  orthogonal_family.linear_isometry_apply_dfinsupp_sum_single]

@[simp] protected lemma linear_isometry_equiv_apply_dfinsupp_sum_single
  [Π i, complete_space (G i)]
  (hV' : (⨆ i, (V i).to_linear_map.range).topological_closure = ⊤) (W₀ : Π₀ (i : ι), G i) :
  (hV.linear_isometry_equiv hV' (W₀.sum (λ i, V i)) : Π i, G i) = W₀ :=
begin
  rw ← hV.linear_isometry_equiv_symm_apply_dfinsupp_sum_single hV',
  rw linear_isometry_equiv.apply_symm_apply,
  ext i,
  simp [dfinsupp.sum, lp.single_apply] {contextual := tt},
end

end orthogonal_family

section
variables (ι) (𝕜) (E)

/-- A Hilbert basis on `ι` for an inner product space `E` is an identification of `E` with the `lp`
space `ℓ²(ι, 𝕜)`. -/
structure hilbert_basis := of_repr :: (repr : E ≃ₗᵢ[𝕜] ℓ²(ι, 𝕜))

end

namespace hilbert_basis

/-- `b i` is the `i`th basis vector. -/
instance : has_coe_to_fun (hilbert_basis ι 𝕜 E) (λ _, ι → E) :=
{ coe := λ b i, b.repr.symm (lp.single 2 i (1:𝕜)) }

@[simp] protected lemma repr_symm_single (b : hilbert_basis ι 𝕜 E) (i : ι) :
  b.repr.symm (lp.single 2 i (1:𝕜)) = b i :=
rfl

@[simp] protected lemma repr_self (b : hilbert_basis ι 𝕜 E) (i : ι) :
  b.repr (b i) = lp.single 2 i (1:𝕜) :=
by rw [← b.repr_symm_single, linear_isometry_equiv.apply_symm_apply]

protected lemma repr_apply_apply (b : hilbert_basis ι 𝕜 E) (v : E) (i : ι) :
  b.repr v i = ⟪b i, v⟫ :=
begin
  rw [← b.repr.inner_map_map (b i) v, b.repr_self, lp.inner_single_left],
  simp,
end

@[simp] protected lemma orthonormal (b : hilbert_basis ι 𝕜 E) : orthonormal 𝕜 b :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self, b.repr_self, lp.inner_single_left,
    lp.single_apply],
  simp,
end

-- why does this proof show as timing out?
protected lemma has_sum_repr_symm (b : hilbert_basis ι 𝕜 E) (f : ℓ²(ι, 𝕜)) :
  has_sum (λ i, f i • b i) (b.repr.symm f) :=
begin
  have : has_sum (λ (i : ι), lp.single 2 i (f i)) f := lp.has_sum_single ennreal.two_ne_top f,
  convert (↑(b.repr.symm.to_continuous_linear_equiv) : ℓ²(ι, 𝕜) →L[𝕜] E).has_sum this,
  ext i,
  apply b.repr.injective,
  have : lp.single 2 i (f i * 1) = _ := lp.single_smul 2 i (1:𝕜) (f i),
  rw mul_one at this,
  rw [linear_isometry_equiv.map_smul, b.repr_self, ← this, continuous_linear_equiv.coe_coe,
    linear_isometry_equiv.coe_to_continuous_linear_equiv],
  -- exact (b.repr.apply_symm_apply (lp.single 2 i (f i))).symm,
  sorry
end

protected lemma has_sum_repr_symm' (b : hilbert_basis ι 𝕜 E) (x : E) :
  has_sum (λ i, b.repr x i • b i) x :=
by simpa using b.has_sum_repr_symm (b.repr x)

@[simp] protected lemma dense_span (b : hilbert_basis ι 𝕜 E) :
  (span 𝕜 (set.range b)).topological_closure = ⊤ :=
begin
  classical,
  rw eq_top_iff,
  rintros x -,
  refine mem_closure_of_tendsto (b.has_sum_repr_symm' x) (eventually_of_forall _),
  intros s,
  simp only [set_like.mem_coe],
  refine sum_mem _ _,
  rintros i -,
  refine smul_mem _ _ _,
  exact subset_span ⟨i, rfl⟩
end

variables {v : ι → E} (hv : orthonormal 𝕜 v)
include hv cplt

/-- An orthonormal family of vectors whose span is dense in the whole module is a Hilbert basis. -/
protected def mk (hsp : (span 𝕜 (set.range v)).topological_closure = ⊤) :
  hilbert_basis ι 𝕜 E :=
hilbert_basis.of_repr $
hv.orthogonal_family.linear_isometry_equiv
begin
  convert hsp,
  simp [← linear_map.span_singleton_eq_range, ← submodule.span_Union],
end

@[simp] protected lemma mk_apply (hsp : (span 𝕜 (set.range v)).topological_closure = ⊤) (i : ι) :
  hilbert_basis.mk hv hsp i = v i :=
show (hilbert_basis.mk hv hsp).repr.symm _ = v i, by simp [hilbert_basis.mk]

@[simp] protected lemma coe_mk (hsp : (span 𝕜 (set.range v)).topological_closure = ⊤) :
  ⇑(hilbert_basis.mk hv hsp) = v :=
by ext; simp

/-- An orthonormal family of vectors whose span has trivial orthogonal complement is a Hilbert
basis. -/
protected def mk_of_orthogonal_eq_bot (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) : hilbert_basis ι 𝕜 E :=
hilbert_basis.mk hv
(by rw [← orthogonal_orthogonal_eq_closure, orthogonal_eq_top_iff, hsp])

@[simp] protected lemma mk_of_orthogonal_eq_bot_apply (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) (i : ι) :
  hilbert_basis.mk_of_orthogonal_eq_bot hv hsp i = v i :=
hilbert_basis.mk_apply hv _ _

@[simp] protected lemma coe_of_orthogonal_eq_bot_mk (hsp : (span 𝕜 (set.range v))ᗮ = ⊥) :
  ⇑(hilbert_basis.mk_of_orthogonal_eq_bot hv hsp) = v :=
hilbert_basis.coe_mk hv _

omit hv

/-- A Hilbert space admits a Hilbert basis extending a given orthonormal subset. -/
lemma _root_.orthonormal.exists_hilbert_basis_extension
  {s : set E} (hs : orthonormal 𝕜 (coe : s → E)) :
  ∃ (w : set E) (b : hilbert_basis w 𝕜 E), s ⊆ w ∧ ⇑b = (coe : w → E) :=
let ⟨w, hws, hw_ortho, hw_max⟩ := exists_maximal_orthonormal hs in
⟨ w,
  hilbert_basis.mk_of_orthogonal_eq_bot hw_ortho
    (by simpa [maximal_orthonormal_iff_orthogonal_complement_eq_bot hw_ortho] using hw_max),
  hws,
  hilbert_basis.coe_of_orthogonal_eq_bot_mk _ _ ⟩

/-- A Hilbert space admits a Hilbert basis. -/
lemma _root_.orthonormal.exists_hilbert_basis :
  ∃ (w : set E) (b : hilbert_basis w 𝕜 E), ⇑b = (coe : w → E) :=
let ⟨w, hw, hw', hw''⟩ := (orthonormal_empty 𝕜 E).exists_hilbert_basis_extension in ⟨w, hw, hw''⟩

end hilbert_basis
