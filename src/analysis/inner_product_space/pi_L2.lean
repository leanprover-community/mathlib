/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth
-/
import analysis.inner_product_space.projection
import analysis.normed_space.pi_Lp

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `pi_Lp 2`.

## Main definitions

- `euclidean_space 𝕜 n`: defined to be `pi_Lp 2 (n → 𝕜)` for any `fintype n`, i.e., the space
  from functions to `n` to `𝕜` with the `L²` norm. We register several instances on it (notably
  that it is a finite-dimensional inner product space).

- `basis.isometry_euclidean_of_orthonormal`: provides the isometry to Euclidean space
  from a given finite-dimensional inner product space, induced by a basis of the space.

- `linear_isometry_equiv.of_inner_product_space`: provides an arbitrary isometry to Euclidean space
  from a given finite-dimensional inner product space, induced by choosing an arbitrary basis.

- `complex.isometry_euclidean`: standard isometry from `ℂ` to `euclidean_space ℝ (fin 2)`

-/

open real set filter is_R_or_C
open_locale big_operators uniformity topological_space nnreal ennreal complex_conjugate direct_sum

noncomputable theory

variables {ι : Type*}
variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E]
variables {E' : Type*} [inner_product_space 𝕜 E']
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `pi_Lp 2 f` for the product space, which is endowed with the `L^2` norm.
-/
instance pi_Lp.inner_product_space {ι : Type*} [fintype ι] (f : ι → Type*)
  [Π i, inner_product_space 𝕜 (f i)] : inner_product_space 𝕜 (pi_Lp 2 f) :=
{ inner := λ x y, ∑ i, inner (x i) (y i),
  norm_sq_eq_inner :=
  begin
    intro x,
    have h₁ : ∑ (i : ι), ∥x i∥ ^ (2 : ℕ) = ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { apply finset.sum_congr rfl,
      intros j hj,
      simp [←rpow_nat_cast] },
    have h₂ : 0 ≤ ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { rw [←h₁],
      exact finset.sum_nonneg (λ j (hj : j ∈ finset.univ), pow_nonneg (norm_nonneg (x j)) 2) },
    simp [norm, add_monoid_hom.map_sum, ←norm_sq_eq_inner],
    rw [←rpow_nat_cast ((∑ (i : ι), ∥x i∥ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) 2],
    rw [←rpow_mul h₂],
    norm_num [h₁],
  end,
  conj_sym :=
  begin
    intros x y,
    unfold inner,
    rw ring_hom.map_sum,
    apply finset.sum_congr rfl,
    rintros z -,
    apply inner_conj_sym,
  end,
  add_left := λ x y z,
    show ∑ i, inner (x i + y i) (z i) = ∑ i, inner (x i) (z i) + ∑ i, inner (y i) (z i),
    by simp only [inner_add_left, finset.sum_add_distrib],
  smul_left := λ x y r,
    show ∑ (i : ι), inner (r • x i) (y i) = (conj r) * ∑ i, inner (x i) (y i),
    by simp only [finset.mul_sum, inner_smul_left] }

@[simp] lemma pi_Lp.inner_apply {ι : Type*} [fintype ι] {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x y : pi_Lp 2 f) :
  ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
rfl

lemma pi_Lp.norm_eq_of_L2 {ι : Type*} [fintype ι] {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x : pi_Lp 2 f) :
  ∥x∥ = sqrt (∑ (i : ι), ∥x i∥ ^ 2) :=
by { rw [pi_Lp.norm_eq_of_nat 2]; simp [sqrt_eq_rpow] }


/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `euclidean_space 𝕜 (fin n)`. -/
@[reducible, nolint unused_arguments]
def euclidean_space (𝕜 : Type*) [is_R_or_C 𝕜]
  (n : Type*) [fintype n] : Type* := pi_Lp 2 (λ (i : n), 𝕜)

lemma euclidean_space.norm_eq {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]
  (x : euclidean_space 𝕜 n) : ∥x∥ = real.sqrt (∑ (i : n), ∥x i∥ ^ 2) :=
pi_Lp.norm_eq_of_L2 x

section
local attribute [reducible] pi_Lp

variables [fintype ι]

instance : finite_dimensional 𝕜 (euclidean_space 𝕜 ι) := by apply_instance
instance : inner_product_space 𝕜 (euclidean_space 𝕜 ι) := by apply_instance

@[simp] lemma finrank_euclidean_space :
  finite_dimensional.finrank 𝕜 (euclidean_space 𝕜 ι) = fintype.card ι := by simp

lemma finrank_euclidean_space_fin {n : ℕ} :
  finite_dimensional.finrank 𝕜 (euclidean_space 𝕜 (fin n)) = n := by simp

/-- A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
from `E` to `pi_Lp 2` of the subspaces equipped with the `L2` inner product. -/
def direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family
  [decidable_eq ι] {V : ι → submodule 𝕜 E} (hV : direct_sum.submodule_is_internal V)
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ)) :
  E ≃ₗᵢ[𝕜] pi_Lp 2 (λ i, V i) :=
begin
  let e₁ := direct_sum.linear_equiv_fun_on_fintype 𝕜 ι (λ i, V i),
  let e₂ := linear_equiv.of_bijective _ hV.injective hV.surjective,
  refine (e₂.symm.trans e₁).isometry_of_inner _,
  suffices : ∀ v w, ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫,
  { intros v₀ w₀,
    convert this (e₁ (e₂.symm v₀)) (e₁ (e₂.symm w₀));
    simp only [linear_equiv.symm_apply_apply, linear_equiv.apply_symm_apply] },
  intros v w,
  transitivity ⟪(∑ i, (V i).subtypeₗᵢ (v i)), ∑ i, (V i).subtypeₗᵢ (w i)⟫,
  { simp only [sum_inner, hV'.inner_right_fintype, pi_Lp.inner_apply] },
  { congr; simp }
end

@[simp] lemma direct_sum.submodule_is_internal.isometry_L2_of_orthogonal_family_symm_apply
  [decidable_eq ι] {V : ι → submodule 𝕜 E} (hV : direct_sum.submodule_is_internal V)
  (hV' : @orthogonal_family 𝕜 _ _ _ _ (λ i, V i) _ (λ i, (V i).subtypeₗᵢ))
  (w : pi_Lp 2 (λ i, V i)) :
  (hV.isometry_L2_of_orthogonal_family hV').symm w = ∑ i, (w i : E) :=
begin
  classical,
  let e₁ := direct_sum.linear_equiv_fun_on_fintype 𝕜 ι (λ i, V i),
  let e₂ := linear_equiv.of_bijective _ hV.injective hV.surjective,
  suffices : ∀ v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i,
  { exact this (e₁.symm w) },
  intros v,
  simp [e₂, direct_sum.submodule_coe, direct_sum.to_module, dfinsupp.sum_add_hom_apply]
end

variables (ι) (𝕜) (E) [fintype ι] [decidable_eq ι]


def euclidean_space.single {𝕜 : Type*} {ι : Type*} [fintype ι] [is_R_or_C 𝕜] (i : ι) (a : 𝕜): euclidean_space 𝕜 ι :=
  set.indicator {i} (λ j, a)


theorem euclidean_space.single_apply {𝕜 : Type*} {ι : Type*} [fintype ι] [decidable_eq ι] [is_R_or_C 𝕜] (i : ι) (a : 𝕜) (j : ι) :
  (euclidean_space.single i a) j = dite (j = i) (λ (h : j = i), a) (λ (h : ¬j = i), 0) :=
  begin
    rw [euclidean_space.single, dite_eq_ite, set.indicator],
    simp only [set.mem_singleton_iff],
  end

lemma euclidean_space.inner_single_left (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) :
  ⟪ euclidean_space.single i (a : 𝕜), v ⟫ = star_ring_end 𝕜 a * (v i) :=
  begin
    simp only [is_R_or_C.inner_apply, pi_Lp.inner_apply, finset.sum_congr],
    rw euclidean_space.single,
    simp_rw [set.indicator,apply_ite (star_ring_end 𝕜),@star_ring_end_apply _ _ _ (0 : 𝕜),star_zero, ite_mul],
    simp only [finset.mem_univ,
 if_true,
 set.mem_singleton_iff,
 mul_eq_mul_left_iff,
 zero_mul,
 true_or,
 eq_self_iff_true,
 finset.sum_ite_eq',
 ring_hom.map_eq_zero,
 finset.sum_congr],
  end

lemma euclidean_space.inner_single_right (i : ι) (a : 𝕜) (v : euclidean_space 𝕜 ι) :
  ⟪ v, euclidean_space.single i (a : 𝕜) ⟫ =  a * (star_ring_end 𝕜) (v i) :=
  begin
    rw [← inner_conj_sym, euclidean_space.inner_single_left],
    rw star_ring_end_apply,
    rw star_mul',
    rw ← star_ring_end_apply,
    rw ← star_ring_end_apply,
    rw star_ring_end_self_apply,
  end

/-- An orthonormal basis on E is an identification of `E` with its dimensional-matching
`euclidean_space 𝕜 ι`. -/
structure orthonormal_basis := of_repr :: (repr : E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι)

namespace orthonormal_basis

instance : inhabited (orthonormal_basis ι 𝕜 (euclidean_space 𝕜 ι)) :=
  ⟨of_repr (linear_isometry_equiv.refl 𝕜 (euclidean_space 𝕜 ι)) ⟩


/-- `b i` is the `i`th basis vector. -/
instance : has_coe_to_fun (orthonormal_basis ι 𝕜 E) (λ _, ι → E) :=
{
  coe := λ b i, b.repr.symm (euclidean_space.single i (1 : 𝕜))
}

@[simp] protected lemma repr_symm_single (b : orthonormal_basis ι 𝕜 E) (i : ι) :
  b.repr.symm (euclidean_space.single i (1:𝕜)) = b i :=
rfl

@[simp] protected lemma repr_self (b : orthonormal_basis ι 𝕜 E) (i : ι) :
  b.repr (b i) = euclidean_space.single i (1:𝕜) :=
  begin
    rw [← b.repr_symm_single _ _ _, linear_isometry_equiv.apply_symm_apply],
  end

protected lemma repr_apply_apply (b : orthonormal_basis ι 𝕜 E) (v : E) (i : ι) :
  b.repr v i = ⟪b i, v⟫ :=
begin
  rw [← b.repr.inner_map_map (b i) v, b.repr_self _ _ _, euclidean_space.inner_single_left],
  simp only [one_mul, eq_self_iff_true, map_one],
end

@[simp]
protected lemma orthonormal (b : orthonormal_basis ι 𝕜 E) : orthonormal 𝕜 b :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self _ _ _, b.repr_self _ _ _],
  rw euclidean_space.inner_single_left,
  rw euclidean_space.single_apply,
  simp only [mul_boole, dite_eq_ite, eq_self_iff_true, map_one],
end

protected lemma sum_repr_symm (b : orthonormal_basis ι 𝕜 E) (v : euclidean_space 𝕜 ι) :
  ∑ i , v i • b i = (b.repr.symm v) :=
  begin
    have : b.repr (∑ i, v i • b i) = v :=
    begin
      have : ⇑(b.repr) = (b.repr.to_linear_isometry.to_linear_map) :=
      begin
        simp only [linear_isometry.coe_to_linear_map, fun_like.coe_fn_eq, linear_isometry_equiv.coe_to_linear_isometry, eq_self_iff_true],
      end,
    rw this,
    simp_rw [linear_map.map_sum, linear_map.map_smul, ← this],
    ext i,
    change (∑ (c : ι), (λ x, v x • (b.repr) (b x)) c) i = v i,
    rw [@fintype.sum_apply _ _ ι _ _ i (λ x, v x • (b.repr) (b x))],
    simp only [algebra.id.smul_eq_mul, orthonormal_basis.repr_self, pi.smul_apply, finset.sum_congr],
    simp_rw [euclidean_space.single, set.indicator, mul_ite, mul_zero],
    simp only [mul_one, finset.mem_univ, if_true, set.mem_singleton_iff, eq_self_iff_true, finset.sum_congr, finset.sum_ite_eq],
    end,
    conv_rhs
    begin
    rw ← this,
    end,
    simp only [linear_isometry_equiv.symm_apply_apply, eq_self_iff_true],
  end

variables {ι} {𝕜} {E}
variable {v : ι → E}


/-- An orthonormal basis on a fintype `ι` for an inner product space induces an isometry with
`euclidean_space 𝕜 ι`. -/
def _root_.basis.isometry_euclidean_of_orthonormal
  (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι :=
v.equiv_fun.isometry_of_inner
begin
  intros x y,
  let p : euclidean_space 𝕜 ι := v.equiv_fun x,
  let q : euclidean_space 𝕜 ι := v.equiv_fun y,
  have key : ⟪p, q⟫ = ⟪∑ i, p i • v i, ∑ i, q i • v i⟫,
  { simp [sum_inner, inner_smul_left, hv.inner_right_fintype] },
  convert key,
  { rw [← v.equiv_fun.symm_apply_apply x, v.equiv_fun_symm_apply] },
  { rw [← v.equiv_fun.symm_apply_apply y, v.equiv_fun_symm_apply] }
end


@[simp] lemma _root_.basis.coe_isometry_euclidean_of_orthonormal
  (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  (v.isometry_euclidean_of_orthonormal hv : E → euclidean_space 𝕜 ι) = v.equiv_fun :=
rfl

@[simp] lemma _root_.basis.coe_isometry_euclidean_of_orthonormal_symm
  (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  ((v.isometry_euclidean_of_orthonormal hv).symm : euclidean_space 𝕜 ι → E) = v.equiv_fun.symm :=
rfl


/-- An orthonormal set that spans is an orthonormal basis -/
protected def mk (hon : orthonormal 𝕜 v) (hsp: submodule.span 𝕜 (set.range v) = ⊤): orthonormal_basis ι 𝕜 E :=
  orthonormal_basis.of_repr $
  basis.isometry_euclidean_of_orthonormal (basis.mk (orthonormal.linear_independent hon) hsp)
  begin
    rw basis.coe_mk,
    exact hon,
  end


@[simp]
protected lemma coe_mk (hon : orthonormal 𝕜 v) (hsp: submodule.span 𝕜 (set.range v) = ⊤) :
  ⇑(orthonormal_basis.mk hon hsp) = v :=
begin
  ext i,
  show (orthonormal_basis.mk hon hsp).repr.symm _ = v i,
  simp only [basis.coe_isometry_euclidean_of_orthonormal_symm,
 orthonormal_basis.mk.equations._eqn_1,
 basis.coe_mk,
 basis.equiv_fun_symm_apply,
 finset.sum_congr],
 simp_rw [euclidean_space.single_apply, dite_eq_ite, ite_smul],
 simp only [finset.mem_univ,
 if_true,
 eq_self_iff_true,
 one_smul,
 finset.sum_ite_eq',
 zero_smul,
 finset.sum_congr],
end


/-- A basis that is orthonormal is an orthonormal basis. -/
def _root_.basis.to_orthonormal_basis (b : basis ι 𝕜 E) (hb : orthonormal 𝕜 b) :
  orthonormal_basis ι 𝕜 E :=
    orthonormal_basis.of_repr(basis.isometry_euclidean_of_orthonormal b hb)

end orthonormal_basis


/-- If `f : E ≃ₗᵢ[𝕜] E'` is a linear isometry of inner product spaces then an orthonormal basis `v`
of `E` determines a linear isometry `e : E' ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι`. This result states that
`e` may be obtained either by transporting `v` to `E'` or by composing with the linear isometry
`E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι` provided by `v`. -/
@[simp] lemma basis.map_isometry_euclidean_of_orthonormal (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v)
  (f : E ≃ₗᵢ[𝕜] E') :
  (v.map f.to_linear_equiv).isometry_euclidean_of_orthonormal (hv.map_linear_isometry_equiv f) =
    f.symm.trans (v.isometry_euclidean_of_orthonormal hv) :=
linear_isometry_equiv.to_linear_equiv_injective $ v.map_equiv_fun _

end

/-- `ℂ` is isometric to `ℝ²` with the Euclidean inner product. -/
def complex.isometry_euclidean : ℂ ≃ₗᵢ[ℝ] (euclidean_space ℝ (fin 2)) :=
complex.basis_one_I.isometry_euclidean_of_orthonormal
begin
  rw orthonormal_iff_ite,
  intros i, fin_cases i;
  intros j; fin_cases j;
  simp [real_inner_eq_re_inner]
end

@[simp] lemma complex.isometry_euclidean_symm_apply (x : euclidean_space ℝ (fin 2)) :
  complex.isometry_euclidean.symm x = (x 0) + (x 1) * I :=
begin
  convert complex.basis_one_I.equiv_fun_symm_apply x,
  { simpa },
  { simp },
end

lemma complex.isometry_euclidean_proj_eq_self (z : ℂ) :
  ↑(complex.isometry_euclidean z 0) + ↑(complex.isometry_euclidean z 1) * (I : ℂ) = z :=
by rw [← complex.isometry_euclidean_symm_apply (complex.isometry_euclidean z),
  complex.isometry_euclidean.symm_apply_apply z]

@[simp] lemma complex.isometry_euclidean_apply_zero (z : ℂ) :
  complex.isometry_euclidean z 0 = z.re :=
by { conv_rhs { rw ← complex.isometry_euclidean_proj_eq_self z }, simp }

@[simp] lemma complex.isometry_euclidean_apply_one (z : ℂ) :
  complex.isometry_euclidean z 1 = z.im :=
by { conv_rhs { rw ← complex.isometry_euclidean_proj_eq_self z }, simp }

open finite_dimensional

/-- Given a natural number `n` equal to the `finrank` of a finite-dimensional inner product space,
there exists an isometry from the space to `euclidean_space 𝕜 (fin n)`. -/
def linear_isometry_equiv.of_inner_product_space
  [finite_dimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n) :
  E ≃ₗᵢ[𝕜] (euclidean_space 𝕜 (fin n)) :=
(fin_std_orthonormal_basis hn).isometry_euclidean_of_orthonormal (fin_std_orthonormal_basis_orthonormal hn)

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`euclidean_space 𝕜 (fin n)`. -/
def linear_isometry_equiv.from_orthogonal_span_singleton
  (n : ℕ) [fact (finrank 𝕜 E = n + 1)] {v : E} (hv : v ≠ 0) :
  (𝕜 ∙ v)ᗮ ≃ₗᵢ[𝕜] (euclidean_space 𝕜 (fin n)) :=
linear_isometry_equiv.of_inner_product_space (finrank_orthogonal_span_singleton hv)
