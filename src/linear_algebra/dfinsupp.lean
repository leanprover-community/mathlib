/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import data.finsupp.to_dfinsupp
import linear_algebra.basis

/-!
# Properties of the module `Π₀ i, M i`

Given an indexed collection of `R`-modules `M i`, the `R`-module structure on `Π₀ i, M i`
is defined in `data.dfinsupp`.

In this file we define `linear_map` versions of various maps:

* `dfinsupp.lsingle a : M →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lmk s : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i`: `dfinsupp.single a` as a linear map;

* `dfinsupp.lapply i : (Π₀ i, M i) →ₗ[R] M`: the map `λ f, f i` as a linear map;

* `dfinsupp.lsum`: `dfinsupp.sum` or `dfinsupp.lift_add_hom` as a `linear_map`;

## Implementation notes

This file should try to mirror `linear_algebra.finsupp` where possible. The API of `finsupp` is
much more developed, but many lemmas in that file should be eligible to copy over.

## Tags

function with finite support, module, linear algebra
-/

variables {ι : Type*} {R : Type*} {S : Type*} {M : ι → Type*} {N : Type*}

variables [dec_ι : decidable_eq ι]
variables [semiring R] [Π i, add_comm_monoid (M i)] [Π i, module R (M i)]
variables [add_comm_monoid N] [module R N]

namespace dfinsupp

include dec_ι

/-- `dfinsupp.mk` as a `linear_map`. -/
def lmk (s : finset ι) : (Π i : (↑s : set ι), M i) →ₗ[R] Π₀ i, M i :=
{ to_fun := mk s, map_add' := λ _ _, mk_add, map_smul' := λ c x, mk_smul c x}

/-- `dfinsupp.single` as a `linear_map` -/
def lsingle (i) : M i →ₗ[R] Π₀ i, M i :=
{ to_fun := single i, map_smul' := single_smul, .. dfinsupp.single_add_hom _ _ }

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere. -/
lemma lhom_ext ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄
  (h : ∀ i x, φ (single i x) = ψ (single i x)) :
  φ = ψ :=
linear_map.to_add_monoid_hom_injective $ add_hom_ext h

/-- Two `R`-linear maps from `Π₀ i, M i` which agree on each `single i x` agree everywhere.

See note [partially-applied ext lemmas].
After apply this lemma, if `M = R` then it suffices to verify `φ (single a 1) = ψ (single a 1)`. -/
@[ext] lemma lhom_ext' ⦃φ ψ : (Π₀ i, M i) →ₗ[R] N⦄
  (h : ∀ i, φ.comp (lsingle i) = ψ.comp (lsingle i)) :
  φ = ψ :=
lhom_ext $ λ i, linear_map.congr_fun (h i)

omit dec_ι

/-- Interpret `λ (f : Π₀ i, M i), f i` as a linear map. -/
def lapply (i : ι) : (Π₀ i, M i) →ₗ[R] M i :=
{ to_fun := λ f, f i,
  map_add' := λ f g, add_apply f g i,
  map_smul' := λ c f, smul_apply c f i}

include dec_ι

@[simp] lemma lmk_apply (s : finset ι) (x) : (lmk s : _ →ₗ[R] Π₀ i, M i) x = mk s x := rfl

@[simp] lemma lsingle_apply (i : ι) (x : M i) : (lsingle i : _ →ₗ[R] _) x = single i x := rfl

omit dec_ι

@[simp] lemma lapply_apply (i : ι) (f : Π₀ i, M i) : (lapply i : _ →ₗ[R] _) f = f i := rfl

section lsum

/-- Typeclass inference can't find `dfinsupp.add_comm_monoid` without help for this case.
This instance allows it to be found where it is needed on the LHS of the colon in
`dfinsupp.module_of_linear_map`. -/
instance add_comm_monoid_of_linear_map : add_comm_monoid (Π₀ (i : ι), M i →ₗ[R] N) :=
@dfinsupp.add_comm_monoid _ (λ i, M i →ₗ[R] N) _

/-- Typeclass inference can't find `dfinsupp.module` without help for this case.
This is needed to define `dfinsupp.lsum` below.

The cause seems to be an inability to unify the `Π i, add_comm_monoid (M i →ₗ[R] N)` instance that
we have with the `Π i, has_zero (M i →ₗ[R] N)` instance which appears as a parameter to the
`dfinsupp` type. -/
instance module_of_linear_map [semiring S] [module S N] [smul_comm_class R S N] :
  module S (Π₀ (i : ι), M i →ₗ[R] N) :=
@dfinsupp.module _ _ (λ i, M i →ₗ[R] N) _ _ _

variables (S)

include dec_ι

/-- The `dfinsupp` version of `finsupp.lsum`.

See note [bundled maps over different rings] for why separate `R` and `S` semirings are used. -/
@[simps]
def lsum [semiring S] [module S N] [smul_comm_class R S N] :
  (Π i, M i →ₗ[R] N) ≃ₗ[S] ((Π₀ i, M i) →ₗ[R] N) :=
{ to_fun := λ F, {
    to_fun := sum_add_hom (λ i, (F i).to_add_monoid_hom),
    map_add' := (lift_add_hom (λ i, (F i).to_add_monoid_hom)).map_add,
    map_smul' := λ c f, by {
      dsimp,
      apply dfinsupp.induction f,
      { rw [smul_zero, add_monoid_hom.map_zero, smul_zero] },
      { intros a b f ha hb hf,
        rw [smul_add, add_monoid_hom.map_add, add_monoid_hom.map_add, smul_add, hf, ←single_smul,
          sum_add_hom_single, sum_add_hom_single, linear_map.to_add_monoid_hom_coe,
          linear_map.map_smul], } } },
  inv_fun := λ F i, F.comp (lsingle i),
  left_inv := λ F, by { ext x y, simp },
  right_inv := λ F, by { ext x y, simp },
  map_add' := λ F G, by { ext x y, simp },
  map_smul' := λ c F, by { ext, simp } }

end lsum

/-! ### Bundled versions of `dfinsupp.map_range`

The names should match the equivalent bundled `finsupp.map_range` definitions.
-/

section map_range

variables {β β₁ β₂: ι → Type*}
variables [Π i, add_comm_monoid (β i)] [Π i, add_comm_monoid (β₁ i)] [Π i, add_comm_monoid (β₂ i)]
variables [Π i, module R (β i)] [Π i, module R (β₁ i)] [Π i, module R (β₂ i)]

lemma map_range_smul (f : Π i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0)
  (r : R) (hf' : ∀ i x, f i (r • x) = r • f i x) (g : Π₀ i, β₁ i):
  map_range f hf (r • g) = r • map_range f hf g :=
begin
  ext,
  simp only [map_range_apply f, coe_smul, pi.smul_apply, hf']
end

/-- `dfinsupp.map_range` as an `linear_map`. -/
@[simps apply]
def map_range.linear_map (f : Π i, β₁ i →ₗ[R] β₂ i) : (Π₀ i, β₁ i) →ₗ[R] (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, f i x) (λ i, (f i).map_zero),
  map_smul' := λ r, map_range_smul _ _ _ (λ i, (f i).map_smul r),
  .. map_range.add_monoid_hom (λ i, (f i).to_add_monoid_hom) }

@[simp]
lemma map_range.linear_map_id :
  map_range.linear_map (λ i, (linear_map.id : (β₂ i) →ₗ[R] _)) = linear_map.id :=
linear_map.ext map_range_id

lemma map_range.linear_map_comp (f : Π i, β₁ i →ₗ[R] β₂ i) (f₂ : Π i, β i →ₗ[R] β₁ i):
  map_range.linear_map (λ i, (f i).comp (f₂ i)) =
    (map_range.linear_map f).comp (map_range.linear_map f₂) :=
linear_map.ext $ map_range_comp (λ i x, f i x) (λ i x, f₂ i x) _ _ _

/-- `dfinsupp.map_range.linear_map` as an `linear_equiv`. -/
@[simps apply]
def map_range.linear_equiv (e : Π i, β₁ i ≃ₗ[R] β₂ i) : (Π₀ i, β₁ i) ≃ₗ[R] (Π₀ i, β₂ i) :=
{ to_fun := map_range (λ i x, e i x) (λ i, (e i).map_zero),
  inv_fun := map_range (λ i x, (e i).symm x) (λ i, (e i).symm.map_zero),
  .. map_range.add_equiv (λ i, (e i).to_add_equiv),
  .. map_range.linear_map (λ i, (e i).to_linear_map) }

@[simp]
lemma map_range.linear_equiv_refl :
  (map_range.linear_equiv $ λ i, linear_equiv.refl R (β₁ i)) = linear_equiv.refl _ _ :=
linear_equiv.ext map_range_id

lemma map_range.linear_equiv_trans (f : Π i, β i ≃ₗ[R] β₁ i) (f₂ : Π i, β₁ i ≃ₗ[R] β₂ i):
  map_range.linear_equiv (λ i, (f i).trans (f₂ i)) =
    (map_range.linear_equiv f).trans (map_range.linear_equiv f₂) :=
linear_equiv.ext $ map_range_comp (λ i x, f₂ i x) (λ i x, f i x) _ _ _

@[simp]
lemma map_range.linear_equiv_symm (e : Π i, β₁ i ≃ₗ[R] β₂ i) :
  (map_range.linear_equiv e).symm = map_range.linear_equiv (λ i, (e i).symm) := rfl

end map_range

section basis

/-- The direct sum of free modules is free.

Note that while this is stated for `dfinsupp` not `direct_sum`, the types are defeq. -/
noncomputable def basis {η : ι → Type*} (b : Π i, basis (η i) R (M i)) :
  basis (Σ i, η i) R (Π₀ i, M i) :=
basis.of_repr ((map_range.linear_equiv (λ i, (b i).repr)).trans
  (sigma_finsupp_lequiv_dfinsupp R).symm)

end basis

end dfinsupp

include dec_ι

namespace submodule
open dfinsupp

lemma dfinsupp_sum_mem {β : ι → Type*} [Π i, has_zero (β i)]
  [Π i (x : β i), decidable (x ≠ 0)] (S : submodule R N)
  (f : Π₀ i, β i) (g : Π i, β i → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) : f.sum g ∈ S :=
S.to_add_submonoid.dfinsupp_sum_mem f g h

lemma dfinsupp_sum_add_hom_mem {β : ι → Type*} [Π i, add_zero_class (β i)]
  (S : submodule R N) (f : Π₀ i, β i) (g : Π i, β i →+ N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ S) :
  dfinsupp.sum_add_hom g f ∈ S :=
S.to_add_submonoid.dfinsupp_sum_add_hom_mem f g h

/-- The supremum of a family of submodules is equal to the range of `dfinsupp.lsum`; that is
every element in the `supr` can be produced from taking a finite number of non-zero elements
of `p i`, coercing them to `N`, and summing them. -/
lemma supr_eq_range_dfinsupp_lsum (p : ι → submodule R N) :
  supr p = (dfinsupp.lsum ℕ (λ i, (p i).subtype)).range :=
begin
  apply le_antisymm,
  { apply supr_le _,
    intros i y hy,
    exact ⟨dfinsupp.single i ⟨y, hy⟩, dfinsupp.sum_add_hom_single _ _ _⟩, },
  { rintros x ⟨v, rfl⟩,
    exact dfinsupp_sum_add_hom_mem _ v _ (λ i _, (le_supr p i : p i ≤ _) (v i).prop) }
end

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom` composed with `dfinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `supr` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
lemma bsupr_eq_range_dfinsupp_lsum (p : ι → Prop)
  [decidable_pred p] (S : ι → submodule R N) :
  (⨆ i (h : p i), S i) =
    ((dfinsupp.lsum ℕ (λ i, (S i).subtype)).comp (dfinsupp.filter_linear_map R _ p)).range :=
begin
  apply le_antisymm,
  { apply bsupr_le _,
    intros i hi y hy,
    refine ⟨dfinsupp.single i ⟨y, hy⟩, _⟩,
    rw [linear_map.comp_apply, filter_linear_map_apply, filter_single_pos _ _ hi],
    exact dfinsupp.sum_add_hom_single _ _ _, },
  { rintros x ⟨v, rfl⟩,
    refine dfinsupp_sum_add_hom_mem _ _ _ (λ i hi, _),
    refine mem_supr_of_mem i _,
    by_cases hp : p i,
    { simp [hp], },
    { simp [hp] }, }
end

lemma mem_supr_iff_exists_dfinsupp (p : ι → submodule R N) (x : N) :
  x ∈ supr p ↔ ∃ f : Π₀ i, p i, dfinsupp.lsum ℕ (λ i, (p i).subtype) f = x :=
set_like.ext_iff.mp (supr_eq_range_dfinsupp_lsum p) x

/-- A variant of `submodule.mem_supr_iff_exists_dfinsupp` with the RHS fully unfolded. -/
lemma mem_supr_iff_exists_dfinsupp' (p : ι → submodule R N) [Π i (x : p i), decidable (x ≠ 0)]
  (x : N) :
  x ∈ supr p ↔ ∃ f : Π₀ i, p i, f.sum (λ i xi, ↑xi) = x :=
begin
  rw mem_supr_iff_exists_dfinsupp,
  simp_rw [dfinsupp.lsum_apply_apply, dfinsupp.sum_add_hom_apply],
  congr',
end

lemma mem_bsupr_iff_exists_dfinsupp (p : ι → Prop) [decidable_pred p] (S : ι → submodule R N)
  (x : N) :
  x ∈ (⨆ i (h : p i), S i) ↔
    ∃ f : Π₀ i, S i, dfinsupp.lsum ℕ (λ i, (S i).subtype) (f.filter p) = x :=
set_like.ext_iff.mp (bsupr_eq_range_dfinsupp_lsum p S) x

end submodule

/- Old proof:

/-- If a family of submodules are independent, then `dfinsupp.lsum` applied with
`submodule.subtype` is injective. -/
lemma lsum_ker_of_independent {R M : Type*} [ring R]
  [add_comm_group M] [module R M] (p : ι → submodule R M) (h_ind : complete_lattice.independent p) :
  (lsum ℕ (λ (i : ι), (p i).subtype)).ker = ⊥ :=
begin
  -- Lean can't find this without our help
  letI : add_comm_group (Π₀ i, p i) := @dfinsupp.add_comm_group _ (λ i, p i) _,
  rw linear_map.ker_eq_bot',
  intros x hx,
  ext1 i,
  -- extract `x i` from the sum
  replace hx : lsum ℕ (λ (i : ι), (p i).subtype) (x.filter (≠ i)) + x i = 0,
  { rw [←erase_add_single i x, ←filter_ne_eq_erase, linear_map.map_add] at hx,
    convert hx using 2,
    rw [lsum_apply_apply, dfinsupp.sum_add_hom_single],
    refl, },
  rw [zero_apply, ←submodule.mem_right_iff_eq_zero_of_disjoint (h_ind i),
    submodule.bsupr_eq_mrange_dfinsupp_lsum],
  refine ⟨-x, _⟩,
  rw [linear_map.map_neg, neg_eq_iff_add_eq_zero],
  exact hx,
end

-/

namespace complete_lattice

open dfinsupp

/-- A family of submodules over an additive group are independent if and only iff `dfinsupp.lsum`
applied with `submodule.subtype` is injective. -/
lemma independent_iff_dfinsupp_lsum_ker {R M : Type*}
  [ring R] [add_comm_group M] [module R M] (p : ι → submodule R M) :
  independent p ↔ (lsum ℕ (λ i, (p i).subtype)).ker = ⊥ :=
begin
  -- Lean can't find this without our help
  letI : add_comm_group (Π₀ i, p i) := @dfinsupp.add_comm_group _ (λ i, p i) _,
  -- simplify everything down to binders over equalities in `M`
  rw [linear_map.ker_eq_bot', complete_lattice.independent_def],
  simp_rw [submodule.disjoint_def, submodule.bsupr_eq_mrange_dfinsupp_lsum,
    linear_map.mem_range, dfinsupp.ext_iff, zero_apply, ←submodule.coe_eq_zero,
    exists_imp_distrib, linear_map.comp_apply, filter_linear_map_apply],
  -- we can't seem to rewrite the iff with this, but we use it in both directions.
  have h_lsum : ∀ (m : Π₀ i, p i) {i} {x} (hx : x ∈ p i),
    lsum ℕ (λ i, (p i).subtype) (filter (≠ i) m) = x ↔
      lsum ℕ (λ i, (p i).subtype) (filter (≠ i) m - single i ⟨x, hx⟩) = 0,
  { intros m i x hx,
    simp only [add_monoid_hom.map_sub, lsum_apply_apply, sum_add_hom_single, sub_eq_zero],
    refl },
  split,
  { intros h m hm i,
    refine h i (m i) (m i).prop (-m) _,
    rw h_lsum (-m) (m i).prop,
    rw [@filter_neg _ (λ i, p i) _ _ _ m, ←neg_add', linear_map.map_neg, filter_ne_eq_erase,
      subtype.coe_eta, erase_add_single, hm, neg_zero], },
  { intros h i x hx m hm,
    rw h_lsum m hx at hm,
    have := h _ hm i,
    rw [sub_eq_add_neg, add_apply, filter_ne_eq_erase, erase_same, zero_add] at this,
    change (-(single i (⟨x, hx⟩ : p i) i) : M) = 0 at this, -- `neg_apply` doesn't work :(
    rw [neg_eq_zero, single_eq_same] at this,
    exact this, },
end

end complete_lattice
