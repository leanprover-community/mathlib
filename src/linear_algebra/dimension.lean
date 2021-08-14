/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen
-/
import linear_algebra.basis
import linear_algebra.std_basis
import set_theory.cofinality
import linear_algebra.invariant_basis_number

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `module.rank : cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

Although this definition works for any module over a (semi)ring,
for now we quickly specialize to division rings and then to fields.
There's lots of generalization still to be done.

## Main statements

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.
* `dim_quotient_add_dim`: if V₁ is a submodule of V, then
  `module.rank (V/V₁) + module.rank V₁ = module.rank V`.
* `dim_range_add_dim_ker`: the rank-nullity theorem.

## Implementation notes

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `V`, `V'`, ... all live in different universes,
and `V₁`, `V₂`, ... all live in the same universe.
-/

noncomputable theory

universes u v v' v'' u₁' w w'

variables {K : Type u} {V V₁ V₂ V₃ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}
variables {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open_locale classical big_operators

open basis submodule function set

section module

section
variables [semiring K] [add_comm_monoid V] [module K V]
include K

variables (K V)

/-- The rank of a module, defined as a term of type `cardinal`.

We define this as the supremum of the cardinalities of linearly independent subsets.

For a free module over any ring satisfying the strong rank condition
(e.g. left-noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

The definition is marked as protected to avoid conflicts with `_root_.rank`,
the rank of a linear map.
-/
protected def module.rank : cardinal :=
cardinal.sup.{v v}
  (λ ι : {s : set V // linear_independent K (coe : s → V)}, cardinal.mk ι.1)

end

section
variables {R : Type u} [ring R] [nontrivial R]
variables {M : Type v} [add_comm_group M] [module R M]

lemma {m} cardinal_lift_le_dim_of_linear_independent
  {ι : Type w} {v : ι → M} (hv : linear_independent R v) :
  cardinal.lift.{w (max v m)} (cardinal.mk ι) ≤ cardinal.lift.{v (max w m)} (module.rank R M) :=
begin
  apply le_trans,
  { exact cardinal.lift_mk_le.mpr
      ⟨(equiv.of_injective _ hv.injective).to_embedding⟩, },
  { simp only [cardinal.lift_le],
    apply le_trans,
    swap,
    exact cardinal.le_sup _ ⟨range v, hv.coe_range⟩,
    exact le_refl _, },
end

lemma cardinal_le_dim_of_linear_independent
  {ι : Type v} {v : ι → M} (hv : linear_independent R v) :
  cardinal.mk ι ≤ module.rank R M :=
by simpa using cardinal_lift_le_dim_of_linear_independent hv

lemma cardinal_le_dim_of_linear_independent'
  {s : set M} (hs : linear_independent R (λ x, x : s → M)) :
  cardinal.mk s ≤ module.rank R M :=
cardinal_le_dim_of_linear_independent hs

@[simp] lemma dim_bot : module.rank R (⊥ : submodule R M) = 0 :=
begin
  apply le_bot_iff.mp,
  dsimp [module.rank],
  apply cardinal.sup_le.mpr,
  rintro ⟨s, li⟩,
  apply le_bot_iff.mpr,
  apply cardinal.mk_emptyc_iff.mpr,
  simp only [subtype.coe_mk],
  by_contradiction h,
  have ne : s.nonempty := ne_empty_iff_nonempty.mp h,
  simpa using linear_independent.ne_zero (⟨_, ne.some_mem⟩ : s) li,
end

/--
Over any nontrivial ring, the existence of a finite spanning set implies that any basis is finite.
-/
-- One might hope that a finite spanning set implies that any linearly independent set is finite.
-- While this is true over a division ring
-- (simply because any linearly independent set can be extended to a basis),
-- I'm not certain what more general statements are possible.
def basis_fintype_of_finite_spans (w : set M) [fintype w] (s : span R w = ⊤)
  {ι : Type w} (b : basis ι R M) : fintype ι :=
begin
  -- We'll work by contradiction, assuming `ι` is infinite.
  apply fintype_of_not_infinite _,
  introI i,
  -- Let `S` be the union of the supports of `x ∈ w` expressed as linear combinations of `b`.
  -- This is a finite set since `w` is finite.
  let S : finset ι := finset.univ.sup (λ x : w, (b.repr x).support),
  let bS : set M := b '' S,
  have h : ∀ x ∈ w, x ∈ span R bS,
  { intros x m,
    rw [←b.total_repr x, finsupp.span_image_eq_map_total, submodule.mem_map],
    use b.repr x,
    simp only [and_true, eq_self_iff_true, finsupp.mem_supported],
    change (b.repr x).support ≤ S,
    convert (finset.le_sup (by simp : (⟨x, m⟩ : w) ∈ finset.univ)),
    refl, },
  -- Thus this finite subset of the basis elements spans the entire module.
  have k : span R bS = ⊤ := eq_top_iff.2 (le_trans s.ge (span_le.2 h)),

  -- Now there is some `x : ι` not in `S`, since `ι` is infinite.
  obtain ⟨x, nm⟩ := infinite.exists_not_mem_finset S,
  -- However it must be in the span of the finite subset,
  have k' : b x ∈ span R bS, { rw k, exact mem_top, },
  -- giving the desire contradiction.
  refine b.linear_independent.not_mem_span_image _ k',
  exact nm,
end

/--
Over any ring `R`, if `b` is a basis for a module `M`,
and `s` is a maximal linearly independent set,
then the union of the supports of `x ∈ s` (when written out in the basis `b`) is all of `b`.
-/
-- From [Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
lemma union_support_maximal_linear_independent_eq_range_basis
  {ι : Type w} (b : basis ι R M)
  {κ : Type w'} (v : κ → M) (i : linear_independent R v) (m : i.maximal) :
  (⋃ k, ((b.repr (v k)).support : set ι)) = univ :=
begin
  -- If that's not the case,
  by_contradiction h,
  simp only [←ne.def, ne_univ_iff_exists_not_mem, mem_Union, not_exists_not,
    finsupp.mem_support_iff, finset.mem_coe] at h,
  -- We have some basis element `b b'` which is not in the support of any of the `v i`.
  obtain ⟨b', w⟩ := h,
  -- Using this, we'll construct a linearly independent family strictly larger than `v`,
  -- by also using this `b b'`.
  let v' : option κ → M := λ o, o.elim (b b') v,
  have r : range v ⊆ range v',
  { rintro - ⟨k, rfl⟩,
    use some k,
    refl, },
  have r' : b b' ∉ range v,
  { rintro ⟨k, p⟩,
    simpa [w] using congr_arg (λ m, (b.repr m) b') p, },
  have r'' : range v ≠ range v',
  { intro e,
    have p : b b' ∈ range v', { use none, refl, },
    rw ←e at p,
    exact r' p, },
  have inj' : injective v',
  { rintros (_|k) (_|k) z,
    { refl, },
    { exfalso, exact r' ⟨k, z.symm⟩, },
    { exfalso, exact r' ⟨k, z⟩, },
    { congr, exact i.injective z, }, },
  -- The key step in the proof is checking that this strictly larger family is linearly independent.
  have i' : linear_independent R (coe : range v' → M),
  { rw [linear_independent_subtype_range inj', linear_independent_iff],
    intros l z,
    rw [finsupp.total_option] at z,
    simp only [v', option.elim] at z,
    change _ + finsupp.total κ M R v l.some = 0 at z,
    -- We have some linear combination of `b b'` and the `v i`, which we want to show is trivial.
    -- We'll first show the coefficient of `b b'` is zero,
    -- by expressing the `v i` in the basis `b`, and using that the `v i` have no `b b'` term.
    have l₀ : l none = 0,
    { rw ←eq_neg_iff_add_eq_zero at z,
      replace z := eq_neg_of_eq_neg z,
      apply_fun (λ x, b.repr x b') at z,
      simp only [repr_self, linear_equiv.map_smul, mul_one, finsupp.single_eq_same, pi.neg_apply,
        finsupp.smul_single', linear_equiv.map_neg, finsupp.coe_neg] at z,
      erw finsupp.congr_fun (finsupp.apply_total R (b.repr : M →ₗ[R] ι →₀ R) v l.some) b' at z,
      simpa [finsupp.total_apply, w] using z, },
    -- Then all the other coefficients are zero, because `v` is linear independent.
    have l₁ : l.some = 0,
    { rw [l₀, zero_smul, zero_add] at z,
      exact linear_independent_iff.mp i _ z, },
    -- Finally we put those facts together to show the linear combination is trivial.
    ext (_|a),
    { simp only [l₀, finsupp.coe_zero, pi.zero_apply], },
    { erw finsupp.congr_fun l₁ a,
      simp only [finsupp.coe_zero, pi.zero_apply], }, },
  dsimp [linear_independent.maximal] at m,
  specialize m (range v') i' r,
  exact r'' m,
end

/--
Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
lemma infinite_basis_le_maximal_linear_independent'
  {ι : Type w} (b : basis ι R M) [infinite ι]
  {κ : Type w'} (v : κ → M) (i : linear_independent R v) (m : i.maximal) :
  cardinal.lift.{w w'} (cardinal.mk ι) ≤ cardinal.lift.{w' w} (cardinal.mk κ) :=
begin
  let Φ := λ k : κ, (b.repr (v k)).support,
  have w₁ : cardinal.mk ι ≤ cardinal.mk (set.range Φ),
  { apply cardinal.le_range_of_union_finset_eq_top,
    exact union_support_maximal_linear_independent_eq_range_basis b v i m, },
  have w₂ :
    cardinal.lift.{w w'} (cardinal.mk (set.range Φ)) ≤ cardinal.lift.{w' w} (cardinal.mk κ) :=
    cardinal.mk_range_le_lift,
  exact (cardinal.lift_le.mpr w₁).trans w₂,
end

/--
Over any ring `R`, if `b` is an infinite basis for a module `M`,
and `s` is a maximal linearly independent set,
then the cardinality of `b` is bounded by the cardinality of `s`.
-/
-- (See `infinite_basis_le_maximal_linear_independent'` for the more general version
-- where the index types can live in different universes.)
lemma infinite_basis_le_maximal_linear_independent
  {ι : Type w} (b : basis ι R M) [infinite ι]
  {κ : Type w} (v : κ → M) (i : linear_independent R v) (m : i.maximal) :
  cardinal.mk ι ≤ cardinal.mk κ :=
cardinal.lift_le.mp (infinite_basis_le_maximal_linear_independent' b v i m)

end

section invariant_basis_number

variables {R : Type u} [ring R] [nontrivial R] [invariant_basis_number R]
variables {M : Type v} [add_comm_group M] [module R M]

/-- The dimension theorem: if `v` and `v'` are two bases, their index types
have the same cardinalities. -/
theorem mk_eq_mk_of_basis (v : basis ι R M) (v' : basis ι' R M) :
  cardinal.lift.{w w'} (cardinal.mk ι) = cardinal.lift.{w' w} (cardinal.mk ι') :=
begin
  by_cases h : cardinal.mk ι < cardinal.omega,
  { -- `v` is a finite basis, so by `basis_fintype_of_finite_spans` so is `v'`.
    haveI : fintype ι := (cardinal.lt_omega_iff_fintype.mp h).some,
    haveI : fintype (range v) := set.fintype_range ⇑v,
    haveI := basis_fintype_of_finite_spans _ v.span_eq v',
    -- We clean up a little:
    rw [cardinal.fintype_card, cardinal.fintype_card],
    simp only [cardinal.lift_nat_cast, cardinal.nat_cast_inj],
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_lequiv R,
    exact (((finsupp.linear_equiv_fun_on_fintype R R ι).symm.trans v.repr.symm).trans
      v'.repr).trans (finsupp.linear_equiv_fun_on_fintype R R ι'), },
  { -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linear_independent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linear_independent` again
    -- we see they have the same cardinality.
    simp only [not_lt] at h,
    haveI : infinite ι := cardinal.infinite_iff.mpr h,
    have w₁ :=
      infinite_basis_le_maximal_linear_independent' v _ v'.linear_independent v'.maximal,
    haveI : infinite ι' := cardinal.infinite_iff.mpr (begin
      apply cardinal.lift_le.{w' w}.mp,
      have p := (cardinal.lift_le.mpr h).trans w₁,
      rw cardinal.lift_omega at ⊢ p,
      exact p,
    end),
    have w₂ :=
      infinite_basis_le_maximal_linear_independent' v' _ v.linear_independent v.maximal,
    exact le_antisymm w₁ w₂, }
end

theorem mk_eq_mk_of_basis' {ι' : Type w} (v : basis ι R M) (v' : basis ι' R M) :
  cardinal.mk ι = cardinal.mk ι' :=
cardinal.lift_inj.1 $ mk_eq_mk_of_basis v v'

end invariant_basis_number

section rank_condition

variables {R : Type u} [ring R] [rank_condition R]
variables {M : Type v} [add_comm_group M] [module R M]

/--
An auxiliary lemma for `basis.le_span`.

If `R` satisfies the rank condition,
then for any finite basis `b : basis ι R M`,
and any finite spanning set `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
lemma basis.le_span'' {ι : Type*} [fintype ι] (b : basis ι R M)
  {w : set M} [fintype w] (s : span R w = ⊤) :
  fintype.card ι ≤ fintype.card w :=
begin
   -- We construct an surjective linear map `(w → R) →ₗ[R] (ι → R)`,
   -- by expressing a linear combination in `w` as a linear combination in `ι`.
   fapply card_le_of_surjective' R,
   { exact b.repr.to_linear_map.comp (finsupp.total w M R coe), },
   { apply surjective.comp,
    apply linear_equiv.surjective,
    rw [←linear_map.range_eq_top, finsupp.range_total],
    simpa using s, },
end

variables [nontrivial R]

/--
Another auxiliary lemma for `basis.le_span`, which does not require assuming the basis is finite,
but still assumes we have a finite spanning set.
-/
lemma basis_le_span' {ι : Type*} (b : basis ι R M)
  {w : set M} [fintype w] (s : span R w = ⊤) :
  cardinal.mk ι ≤ fintype.card w :=
begin
  haveI := basis_fintype_of_finite_spans w s b,
  rw cardinal.fintype_card ι,
  simp only [cardinal.nat_cast_le],
  exact basis.le_span'' b s,
end

/--
If `R` satisfies the rank condition,
then the cardinality of any basis is bounded by the cardinality of any spanning set.
-/
-- Note that if `R` satisfies the strong rank condition,
-- this also follows from `linear_independent_le_span` below.
theorem basis.le_span {J : set M} (v : basis ι R M)
   (hJ : span R J = ⊤) : cardinal.mk (range v) ≤ cardinal.mk J :=
begin
  cases le_or_lt cardinal.omega (cardinal.mk J) with oJ oJ,
  { have := cardinal.mk_range_eq_of_injective v.injective,
    let S : J → set ι := λ j, ↑(v.repr j).support,
    let S' : J → set M := λ j, v '' S j,
    have hs : range v ⊆ ⋃ j, S' j,
    { intros b hb,
      rcases mem_range.1 hb with ⟨i, hi⟩,
      have : span R J ≤ comap v.repr.to_linear_map (finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 (λ j hj x hx, ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩),
      rw hJ at this,
      replace : v.repr (v i) ∈ (finsupp.supported R R (⋃ j, S j)) := this trivial,
      rw [v.repr_self, finsupp.mem_supported,
        finsupp.support_single_ne_zero one_ne_zero] at this,
      { subst b,
        rcases mem_Union.1 (this (finset.mem_singleton_self _)) with ⟨j, hj⟩,
        exact mem_Union.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩ },
      { apply_instance } },
    refine le_of_not_lt (λ IJ, _),
    suffices : cardinal.mk (⋃ j, S' j) < cardinal.mk (range v),
    { exact not_le_of_lt this ⟨set.embedding_of_subset _ _ hs⟩ },
    refine lt_of_le_of_lt (le_trans cardinal.mk_Union_le_sum_mk
      (cardinal.sum_le_sum _ (λ _, cardinal.omega) _)) _,
    { exact λ j, le_of_lt (cardinal.lt_omega_iff_finite.2 $ (finset.finite_to_set _).image _) },
    { rwa [cardinal.sum_const, cardinal.mul_eq_max oJ (le_refl _), max_eq_left oJ] } },
  { haveI : fintype J := (cardinal.lt_omega_iff_fintype.mp oJ).some,
    rw [←cardinal.lift_le, cardinal.mk_range_eq_of_injective v.injective, cardinal.fintype_card J],
    convert cardinal.lift_le.{w v}.2 (basis_le_span' v hJ),
    simp, },
end

end rank_condition

section strong_rank_condition

variables {R : Type u} [ring R] [strong_rank_condition R]
variables {M : Type v} [add_comm_group M] [module R M]

open submodule

-- An auxiliary lemma for `linear_independent_le_span'`,
-- with the additional assumption that the linearly independent family is finite.
lemma linear_independent_le_span_aux'
  {ι : Type*} [fintype ι] (v : ι → M) (i : linear_independent R v)
  (w : set M) [fintype w] (s : range v ≤ span R w) :
  fintype.card ι ≤ fintype.card w :=
begin
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R,
  { apply finsupp.total,
    exact λ i, span.repr R w ⟨v i, s (mem_range_self i)⟩, },
  { intros f g h,
    apply_fun finsupp.total w M R coe at h,
    simp only [finsupp.total_total, submodule.coe_mk, span.finsupp_total_repr] at h,
    rw [←sub_eq_zero, ←linear_map.map_sub] at h,
    exact sub_eq_zero.mp (linear_independent_iff.mp i _ h), },
end

/--
If `R` satisfies the strong rank condition,
then any linearly independent family `v : ι → M`
contained in the span of some finite `w : set M`,
is itself finite.
-/
def linear_independent_fintype_of_le_span_fintype
  {ι : Type*} (v : ι → M) (i : linear_independent R v)
  (w : set M) [fintype w] (s : range v ≤ span R w) : fintype ι :=
fintype_of_finset_card_le (fintype.card w) (λ t, begin
  let v' := λ x : (t : set ι), v x,
  have i' : linear_independent R v' := i.comp _ subtype.val_injective,
  have s' : range v' ≤ span R w := (range_comp_subset_range _ _).trans s,
  simpa using linear_independent_le_span_aux' v' i' w s',
end)

/--
If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
contained in the span of some finite `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
lemma linear_independent_le_span' {ι : Type*} (v : ι → M) (i : linear_independent R v)
  (w : set M) [fintype w] (s : range v ≤ span R w) :
  cardinal.mk ι ≤ fintype.card w :=
begin
  haveI : fintype ι := linear_independent_fintype_of_le_span_fintype v i w s,
  rw cardinal.fintype_card,
  simp only [cardinal.nat_cast_le],
  exact linear_independent_le_span_aux' v i w s,
end

/--
If `R` satisfies the strong rank condition,
then for any linearly independent family `v : ι → M`
and any finite spanning set `w : set M`,
the cardinality of `ι` is bounded by the cardinality of `w`.
-/
lemma linear_independent_le_span {ι : Type*} (v : ι → M) (i : linear_independent R v)
  (w : set M) [fintype w] (s : span R w = ⊤) :
  cardinal.mk ι ≤ fintype.card w :=
begin
  apply linear_independent_le_span' v i w,
  rw s,
  exact le_top,
end

/--
An auxiliary lemma for `linear_independent_le_basis`:
we handle the case where the basis `b` is infinite.
-/
lemma linear_independent_le_infinite_basis
  {ι : Type*} (b : basis ι R M) [infinite ι]
  {κ : Type*} (v : κ → M) (i : linear_independent R v) :
  cardinal.mk κ ≤ cardinal.mk ι :=
begin
  by_contradiction,
  simp only [not_le] at h,
  have w : cardinal.mk (finset ι) = cardinal.mk ι :=
    cardinal.mk_finset_eq_mk (cardinal.infinite_iff.mp ‹infinite ι›),
  rw ←w at h,
  let Φ := λ k : κ, (b.repr (v k)).support,
  obtain ⟨s, w : infinite ↥(Φ ⁻¹' {s})⟩ := cardinal.exists_infinite_fiber Φ h
    (by { rw [cardinal.infinite_iff, w], exact (cardinal.infinite_iff.mp ‹infinite ι›), }),
  let v' := λ k : Φ ⁻¹' {s}, v k,
  have i' : linear_independent R v' := i.comp _ subtype.val_injective,
  have w' : fintype (Φ ⁻¹' {s}),
  { apply linear_independent_fintype_of_le_span_fintype v' i' (s.image b),
    rintros m ⟨⟨p,⟨rfl⟩⟩,rfl⟩,
    simp only [set_like.mem_coe, subtype.coe_mk, finset.coe_image],
    apply basis.mem_span_repr_support, },
  exactI w.false,
end

/--
Over any ring `R` satisfying the strong rank condition,
if `b` is a basis for a module `M`,
and `s` is a linearly independent set,
then the cardinality of `s` is bounded by the cardinality of `b`.
-/
lemma linear_independent_le_basis
  {ι : Type*} (b : basis ι R M)
  {κ : Type*} (v : κ → M) (i : linear_independent R v) :
  cardinal.mk κ ≤ cardinal.mk ι :=
begin
  -- We split into cases depending on whether `ι` is infinite.
  cases fintype_or_infinite ι; resetI,
  { -- When `ι` is finite, we have `linear_independent_le_span`,
    rw cardinal.fintype_card ι,
    haveI : nontrivial R := nontrivial_of_invariant_basis_number R,
    rw fintype.card_congr (equiv.of_injective b b.injective),
    exact linear_independent_le_span v i (range b) b.span_eq, },
  { -- and otherwise we have `linear_indepedent_le_infinite_basis`.
    exact linear_independent_le_infinite_basis b v i, },
end

/--
Over any ring `R` satisfying the strong rank condition,
if `b` is an infinite basis for a module `M`,
then every maximal linearly independent set has the same cardinality as `b`.

This proof (along with some of the lemmas above) comes from
[Les familles libres maximales d'un module ont-elles le meme cardinal?][lazarus1973]
-/
-- When the basis is not infinite this need not be true!
lemma maximal_linear_independent_eq_infinite_basis
  {ι : Type*} (b : basis ι R M) [infinite ι]
  {κ : Type*} (v : κ → M) (i : linear_independent R v) (m : i.maximal) :
  cardinal.mk κ = cardinal.mk ι :=
begin
  apply le_antisymm,
  { exact linear_independent_le_basis b v i, },
  { haveI : nontrivial R := nontrivial_of_invariant_basis_number R,
    exact infinite_basis_le_maximal_linear_independent b v i m, }
end

variables [nontrivial R]

theorem basis.mk_eq_dim'' {ι : Type v} (v : basis ι R M) :
  cardinal.mk ι = module.rank R M :=
begin
  apply le_antisymm,
  { transitivity,
    swap,
    apply cardinal.le_sup,
    exact ⟨set.range v, by { convert v.reindex_range.linear_independent, ext, simp }⟩,
    exact (cardinal.eq_congr (equiv.of_injective v v.injective)).le, },
  { apply cardinal.sup_le.mpr,
    rintro ⟨s, li⟩,
    apply linear_independent_le_basis v _ li, },
end

-- By this stage we want to have a complete API for `module.rank`,
-- so we set it `irreducible` here, to keep ourselves honest.
attribute [irreducible] module.rank

theorem basis.mk_range_eq_dim (v : basis ι R M) :
  cardinal.mk (range v) = module.rank R M :=
v.reindex_range.mk_eq_dim''

theorem basis.mk_eq_dim (v : basis ι R M) :
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (module.rank R M) :=
by rw [←v.mk_range_eq_dim, cardinal.mk_range_eq_of_injective v.injective]

theorem {m} basis.mk_eq_dim' (v : basis ι R M) :
  cardinal.lift.{w (max v m)} (cardinal.mk ι) = cardinal.lift.{v (max w m)} (module.rank R M) :=
by simpa using v.mk_eq_dim

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
lemma basis.nonempty_fintype_index_of_dim_lt_omega {ι : Type*}
  (b : basis ι R M) (h : module.rank R M < cardinal.omega) :
  nonempty (fintype ι) :=
by rwa [← cardinal.lift_lt, ← b.mk_eq_dim,
        -- ensure `omega` has the correct universe
        cardinal.lift_omega, ← cardinal.lift_omega.{u_1 v},
        cardinal.lift_lt, cardinal.lt_omega_iff_fintype] at h

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
noncomputable def basis.fintype_index_of_dim_lt_omega {ι : Type*}
  (b : basis ι R M) (h : module.rank R M < cardinal.omega) :
  fintype ι :=
classical.choice (b.nonempty_fintype_index_of_dim_lt_omega h)

/-- If a module has a finite dimension, all bases are indexed by a finite set. -/
lemma basis.finite_index_of_dim_lt_omega {ι : Type*} {s : set ι}
  (b : basis s R M) (h : module.rank R M < cardinal.omega) :
  s.finite :=
b.nonempty_fintype_index_of_dim_lt_omega h

lemma dim_span {v : ι → M} (hv : linear_independent R v) :
  module.rank R ↥(span R (range v)) = cardinal.mk (range v) :=
by rw [←cardinal.lift_inj, ← (basis.span hv).mk_eq_dim,
    cardinal.mk_range_eq_of_injective (@linear_independent.injective ι R M v _ _ _ _ hv)]

lemma dim_span_set {s : set M} (hs : linear_independent R (λ x, x : s → M)) :
  module.rank R ↥(span R s) = cardinal.mk s :=
by { rw [← @set_of_mem_eq _ s, ← subtype.range_coe_subtype], exact dim_span hs }

variables (R)

lemma dim_of_ring : module.rank R R = 1 :=
by rw [←cardinal.lift_inj, ← (basis.singleton punit R).mk_eq_dim, cardinal.mk_punit]

end strong_rank_condition


section division_ring
variables [division_ring K] [add_comm_group V] [module K V] [add_comm_group V₁] [module K V₁]
variables {K V}

-- TODO this is true over any ring
theorem dim_le {n : ℕ}
  (H : ∀ s : finset V, linear_independent K (λ i : s, (i : V)) → s.card ≤ n) :
  module.rank K V ≤ n :=
begin
  rw ← (basis.of_vector_space K V).mk_eq_dim'',
  refine cardinal.card_le_of (λ s, _),
  rw ← finset.card_map ⟨_, subtype.val_injective⟩,
  apply H,
  refine (of_vector_space_index.linear_independent K V).mono (λ y (h : y ∈ (s.map _).1), _),
  rw [← finset.mem_def, finset.mem_map] at h,
  rcases h with ⟨x, hx, rfl⟩,
  exact x.2
end

/-- If a vector space has a finite dimension, the index set of `basis.of_vector_space` is finite. -/
lemma basis.finite_of_vector_space_index_of_dim_lt_omega (h : module.rank K V < cardinal.omega) :
  (basis.of_vector_space_index K V).finite :=
(basis.of_vector_space K V).nonempty_fintype_index_of_dim_lt_omega h

variables [add_comm_group V'] [module K V']

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
-- TODO this is true over any ring
theorem linear_equiv.lift_dim_eq (f : V ≃ₗ[K] V') :
  cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K V') :=
let b := basis.of_vector_space K V in
calc cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v v'} (cardinal.mk _) :
  congr_arg _ b.mk_eq_dim''.symm
... = cardinal.lift.{v' v} (module.rank K V') : (b.map f).mk_eq_dim

/-- Two linearly equivalent vector spaces have the same dimension. -/
-- TODO this is true over any ring
theorem linear_equiv.dim_eq (f : V ≃ₗ[K] V₁) :
  module.rank K V = module.rank K V₁ :=
cardinal.lift_inj.1 f.lift_dim_eq

lemma dim_eq_of_injective (f : V →ₗ[K] V₁) (h : injective f) :
  module.rank K V = module.rank K f.range :=
(linear_equiv.of_injective f (linear_map.ker_eq_bot.mpr h)).dim_eq

/--
The image of a subset `r` of a subset `s` under the coercion from `s` to the ambient type
is equivalent to itself.
-/
-- FIXME find a home
def coe_image_equiv {ι : Type*} (s : set ι) (r : set s) : (coe : s → ι) '' r ≃ r :=
{ to_fun := λ x, ⟨⟨x, by tidy⟩, by tidy⟩,
  inv_fun := λ x, ⟨x, ⟨x, by simp⟩⟩,
  left_inv := by tidy,
  right_inv := by tidy, }

lemma dim_submodule_le (s : submodule K V) : module.rank K s ≤ module.rank K V :=
begin
  dsimp [module.rank], -- FIXME: the API is incomplete!
  apply cardinal.sup_le.mpr,
  rintro ⟨r, l⟩,
  apply le_trans,
  swap,
  { apply cardinal.le_sup,
    exact ⟨(coe : s → V) '' r,
      (linear_independent_equiv (coe_image_equiv (s : set V) r)).mpr (l.map' _ s.ker_subtype)⟩, },
  { exact (cardinal.eq_congr (coe_image_equiv _ _).symm).le, },
end

-- TODO this is true over any ring
lemma dim_le_of_injective (f : V →ₗ[K] V₁) (h : injective f) :
  module.rank K V ≤ module.rank K V₁ :=
by { rw [dim_eq_of_injective f h], exact dim_submodule_le _ }

-- TODO this is true over any ring
lemma dim_le_of_submodule (s t : submodule K V) (h : s ≤ t) :
  module.rank K s ≤ module.rank K t :=
dim_le_of_injective (of_le h) $ assume ⟨x, hx⟩ ⟨y, hy⟩ eq,
  subtype.eq $ show x = y, from subtype.ext_iff_val.1 eq

-- TODO this is true over any ring
lemma linear_independent_le_dim
  {v : ι → V} (hv : linear_independent K v) :
  cardinal.lift.{w v} (cardinal.mk ι) ≤ cardinal.lift.{v w} (module.rank K V) :=
calc
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (cardinal.mk (set.range v)) :
     (cardinal.mk_range_eq_of_injective (linear_independent.injective hv)).symm
  ... = cardinal.lift.{v w} (module.rank K (submodule.span K (set.range v))) :
    by rw (dim_span hv).symm
  ... ≤ cardinal.lift.{v w} (module.rank K V) :
    cardinal.lift_le.2 (dim_submodule_le (submodule.span K _))

-- TODO this is true over any ring
theorem {u₁} linear_independent_le_dim' {v : ι → V} (hs : linear_independent K v) :
  ((cardinal.mk ι).lift : cardinal.{(max w v u₁)}) ≤
    ((module.rank K V).lift : cardinal.{(max v w u₁)}) :=
cardinal.mk_range_eq_lift hs.injective ▸ dim_span hs ▸ cardinal.lift_le.2 (dim_submodule_le _)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_lift_dim_eq
  (cond : cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K V')) :
  nonempty (V ≃ₗ[K] V') :=
begin
  let B := basis.of_vector_space K V,
  let B' := basis.of_vector_space K V',
  have : cardinal.lift.{v v'} (cardinal.mk _) = cardinal.lift.{v' v} (cardinal.mk _),
    by rw [B.mk_eq_dim'', cond, B'.mk_eq_dim''],
  exact (cardinal.lift_mk_eq.{v v' 0}.1 this).map (B.equiv B')
end

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_dim_eq (cond : module.rank K V = module.rank K V₁) :
  nonempty (V ≃ₗ[K] V₁) :=
nonempty_linear_equiv_of_lift_dim_eq $ congr_arg _ cond

section

variables (V V' V₁)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def linear_equiv.of_lift_dim_eq
  (cond : cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K V')) :
  V ≃ₗ[K] V' :=
classical.choice (nonempty_linear_equiv_of_lift_dim_eq cond)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def linear_equiv.of_dim_eq (cond : module.rank K V = module.rank K V₁) : V ≃ₗ[K] V₁ :=
classical.choice (nonempty_linear_equiv_of_dim_eq cond)

end

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem linear_equiv.nonempty_equiv_iff_lift_dim_eq :
  nonempty (V ≃ₗ[K] V') ↔
    cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K V') :=
⟨λ ⟨h⟩, linear_equiv.lift_dim_eq h, λ h, nonempty_linear_equiv_of_lift_dim_eq h⟩

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem linear_equiv.nonempty_equiv_iff_dim_eq :
  nonempty (V ≃ₗ[K] V₁) ↔ module.rank K V = module.rank K V₁ :=
⟨λ ⟨h⟩, linear_equiv.dim_eq h, λ h, nonempty_linear_equiv_of_dim_eq h⟩

-- TODO this is true over any ring
@[simp] lemma dim_top : module.rank K (⊤ : submodule K V) = module.rank K V :=
linear_equiv.dim_eq (linear_equiv.of_top _ rfl)

-- TODO this is true over any ring
lemma dim_range_of_surjective (f : V →ₗ[K] V') (h : surjective f) :
  module.rank K f.range = module.rank K V' :=
by rw [linear_map.range_eq_top.2 h, dim_top]

-- TODO how far can we generalise this?
lemma dim_span_le (s : set V) : module.rank K (span K s) ≤ cardinal.mk s :=
begin
  classical,
  rcases
    exists_linear_independent (linear_independent_empty K V) (set.empty_subset s)
    with ⟨b, hb, _, hsb, hlib⟩,
  have hsab : span K s = span K b,
    from span_eq_of_le _ hsb (span_le.2 (λ x hx, subset_span (hb hx))),
  convert cardinal.mk_le_mk_of_subset hb,
  rw [hsab, dim_span_set hlib]
end

lemma dim_span_of_finset (s : finset V) :
  module.rank K (span K (↑s : set V)) < cardinal.omega :=
calc module.rank K (span K (↑s : set V)) ≤ cardinal.mk (↑s : set V) : dim_span_le ↑s
                             ... = s.card : by rw [cardinal.finset_card, finset.coe_sort_coe]
                             ... < cardinal.omega : cardinal.nat_lt_omega _

theorem dim_prod : module.rank K (V × V₁) = module.rank K V + module.rank K V₁ :=
begin
  let b := basis.of_vector_space K V,
  let c := basis.of_vector_space K V₁,
  rw [← cardinal.lift_inj,
      ← (basis.prod b c).mk_eq_dim,
      cardinal.lift_add, cardinal.lift_mk,
      ← b.mk_eq_dim, ← c.mk_eq_dim,
      cardinal.lift_mk, cardinal.lift_mk,
      cardinal.add_def (ulift _)],
  exact cardinal.lift_inj.1 (cardinal.lift_mk_eq.2
      ⟨equiv.ulift.trans (equiv.sum_congr equiv.ulift equiv.ulift).symm ⟩),
end

end division_ring

section field
variables [field K] [add_comm_group V] [module K V] [add_comm_group V₁] [module K V₁]
variables [add_comm_group V'] [module K V']
variables {K V}

theorem dim_quotient_add_dim (p : submodule K V) :
  module.rank K p.quotient + module.rank K p = module.rank K V :=
by classical; exact let ⟨f⟩ := quotient_prod_linear_equiv p in dim_prod.symm.trans f.dim_eq

theorem dim_quotient_le (p : submodule K V) :
  module.rank K p.quotient ≤ module.rank K V :=
by { rw ← dim_quotient_add_dim p, exact self_le_add_right _ _ }

/-- rank-nullity theorem -/
theorem dim_range_add_dim_ker (f : V →ₗ[K] V₁) :
  module.rank K f.range + module.rank K f.ker = module.rank K V :=
begin
  haveI := λ (p : submodule K V), classical.dec_eq p.quotient,
  rw [← f.quot_ker_equiv_range.dim_eq, dim_quotient_add_dim]
end

-- TODO determine how this generalises
lemma dim_range_le (f : V →ₗ[K] V₁) : module.rank K f.range ≤ module.rank K V :=
by { rw ← dim_range_add_dim_ker f, exact self_le_add_right _ _ }

lemma dim_map_le (f : V →ₗ V₁) (p : submodule K V) : module.rank K (p.map f) ≤ module.rank K p :=
begin
  have h := dim_range_le (f.comp (submodule.subtype p)),
  rwa [linear_map.range_comp, range_subtype] at h,
end

lemma dim_eq_of_surjective (f : V →ₗ[K] V₁) (h : surjective f) :
  module.rank K V = module.rank K V₁ + module.rank K f.ker :=
by rw [← dim_range_add_dim_ker f, ← dim_range_of_surjective f h]

lemma dim_le_of_surjective (f : V →ₗ[K] V₁) (h : surjective f) :
  module.rank K V₁ ≤ module.rank K V :=
by { rw [dim_eq_of_surjective f h], refine self_le_add_right _ _ }

section
variables [add_comm_group V₂] [module K V₂]
variables [add_comm_group V₃] [module K V₃]
open linear_map

/-- This is mostly an auxiliary lemma for `dim_sup_add_dim_inf_eq`. -/
lemma dim_add_dim_split
  (db : V₂ →ₗ[K] V) (eb : V₃ →ₗ[K] V) (cd : V₁ →ₗ[K] V₂) (ce : V₁ →ₗ[K] V₃)
  (hde : ⊤ ≤ db.range ⊔ eb.range)
  (hgd : ker cd = ⊥)
  (eq : db.comp cd = eb.comp ce)
  (eq₂ : ∀d e, db d = eb e → (∃c, cd c = d ∧ ce c = e)) :
  module.rank K V + module.rank K V₁ = module.rank K V₂ + module.rank K V₃ :=
have hf : surjective (coprod db eb),
begin
  refine (range_eq_top.1 $ top_unique $ _),
  rwa [← map_top, ← prod_top, map_coprod_prod, ←range_eq_map, ←range_eq_map]
end,
begin
  conv {to_rhs, rw [← dim_prod, dim_eq_of_surjective _ hf] },
  congr' 1,
  apply linear_equiv.dim_eq,
  refine linear_equiv.of_bijective _ _ _,
  { refine cod_restrict _ (prod cd (- ce)) _,
    { assume c,
      simp only [add_eq_zero_iff_eq_neg, linear_map.prod_apply, mem_ker,
        coprod_apply, neg_neg, map_neg, neg_apply],
      exact linear_map.ext_iff.1 eq c } },
  { rw [ker_cod_restrict, ker_prod, hgd, bot_inf_eq] },
  { rw [eq_top_iff, range_cod_restrict, ← map_le_iff_le_comap, map_top, range_subtype],
    rintros ⟨d, e⟩,
    have h := eq₂ d (-e),
    simp only [add_eq_zero_iff_eq_neg, linear_map.prod_apply, mem_ker, set_like.mem_coe,
      prod.mk.inj_iff, coprod_apply, map_neg, neg_apply, linear_map.mem_range] at ⊢ h,
    assume hde,
    rcases h hde with ⟨c, h₁, h₂⟩,
    refine ⟨c, h₁, _⟩,
    rw [h₂, _root_.neg_neg] }
end

lemma dim_sup_add_dim_inf_eq (s t : submodule K V) :
  module.rank K (s ⊔ t : submodule K V) + module.rank K (s ⊓ t : submodule K V) =
    module.rank K s + module.rank K t :=
dim_add_dim_split (of_le le_sup_left) (of_le le_sup_right) (of_le inf_le_left) (of_le inf_le_right)
  begin
    rw [← map_le_map_iff' (ker_subtype $ s ⊔ t), map_sup, map_top,
      ← linear_map.range_comp, ← linear_map.range_comp, subtype_comp_of_le, subtype_comp_of_le,
      range_subtype, range_subtype, range_subtype],
    exact le_refl _
  end
  (ker_of_le _ _ _)
  begin ext ⟨x, hx⟩, refl end
  begin
    rintros ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ eq,
    have : b₁ = b₂ := congr_arg subtype.val eq,
    subst this,
    exact ⟨⟨b₁, hb₁, hb₂⟩, rfl, rfl⟩
  end

lemma dim_add_le_dim_add_dim (s t : submodule K V) :
  module.rank K (s ⊔ t : submodule K V) ≤ module.rank K s + module.rank K t :=
by { rw [← dim_sup_add_dim_inf_eq], exact self_le_add_right _ _ }

end

section fintype
variable [fintype η]
variables [∀i, add_comm_group (φ i)] [∀i, module K (φ i)]

open linear_map

lemma dim_pi : module.rank K (Πi, φ i) = cardinal.sum (λi, module.rank K (φ i)) :=
begin
  let b := assume i, basis.of_vector_space K (φ i),
  let this : basis (Σ j, _) K (Π j, φ j) := pi.basis b,
  rw [←cardinal.lift_inj, ← this.mk_eq_dim],
  simp [λ i, (b i).mk_range_eq_dim.symm, cardinal.sum_mk]
end

lemma dim_fun {V η : Type u} [fintype η] [add_comm_group V] [module K V] :
  module.rank K (η → V) = fintype.card η * module.rank K V :=
by rw [dim_pi, cardinal.sum_const, cardinal.fintype_card]

lemma dim_fun_eq_lift_mul :
  module.rank K (η → V) = (fintype.card η : cardinal.{max u₁' v}) *
    cardinal.lift.{v u₁'} (module.rank K V) :=
by rw [dim_pi, cardinal.sum_const_eq_lift_mul, cardinal.fintype_card, cardinal.lift_nat_cast]

lemma dim_fun' : module.rank K (η → K) = fintype.card η :=
by rw [dim_fun_eq_lift_mul, dim_of_ring, cardinal.lift_one, mul_one, cardinal.nat_cast_inj]

lemma dim_fin_fun (n : ℕ) : module.rank K (fin n → K) = n :=
by simp [dim_fun']

end fintype

lemma exists_mem_ne_zero_of_ne_bot {s : submodule K V} (h : s ≠ ⊥) : ∃ b : V, b ∈ s ∧ b ≠ 0 :=
begin
  classical,
  by_contradiction hex,
  have : ∀x∈s, (x:V) = 0, { simpa only [not_exists, not_and, not_not, ne.def] using hex },
  exact (h $ bot_unique $ assume s hs, (submodule.mem_bot K).2 $ this s hs)
end

lemma exists_mem_ne_zero_of_dim_pos {s : submodule K V} (h : 0 < module.rank K s) :
  ∃ b : V, b ∈ s ∧ b ≠ 0 :=
exists_mem_ne_zero_of_ne_bot $ assume eq, by rw [eq, dim_bot] at h; exact lt_irrefl _ h

section rank

/-- `rank f` is the rank of a `linear_map f`, defined as the dimension of `f.range`. -/
def rank (f : V →ₗ[K] V') : cardinal := module.rank K f.range

lemma rank_le_domain (f : V →ₗ[K] V₁) : rank f ≤ module.rank K V :=
by { rw [← dim_range_add_dim_ker f], exact self_le_add_right _ _ }

lemma rank_le_range (f : V →ₗ[K] V₁) : rank f ≤ module.rank K V₁ :=
dim_submodule_le _

lemma rank_add_le (f g : V →ₗ[K] V') : rank (f + g) ≤ rank f + rank g :=
calc rank (f + g) ≤ module.rank K (f.range ⊔ g.range : submodule K V') :
  begin
    refine dim_le_of_submodule _ _ _,
    exact (linear_map.range_le_iff_comap.2 $ eq_top_iff'.2 $
      assume x, show f x + g x ∈ (f.range ⊔ g.range : submodule K V'), from
        mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩)
  end
  ... ≤ rank f + rank g : dim_add_le_dim_add_dim _ _

@[simp] lemma rank_zero : rank (0 : V →ₗ[K] V') = 0 :=
by rw [rank, linear_map.range_zero, dim_bot]

lemma rank_finset_sum_le {η} (s : finset η) (f : η → V →ₗ[K] V') :
  rank (∑ d in s, f d) ≤ ∑ d in s, rank (f d) :=
@finset.sum_hom_rel _ _ _ _ _ (λa b, rank a ≤ b) f (λ d, rank (f d)) s (le_of_eq rank_zero)
      (λ i g c h, le_trans (rank_add_le _ _) (add_le_add_left h _))

variables [add_comm_group V''] [module K V'']

lemma rank_comp_le1 (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') : rank (f.comp g) ≤ rank f :=
begin
  refine dim_le_of_submodule _ _ _,
  rw [linear_map.range_comp],
  exact linear_map.map_le_range,
end

variables [add_comm_group V'₁] [module K V'₁]

lemma rank_comp_le2 (g : V →ₗ[K] V') (f : V' →ₗ V'₁) : rank (f.comp g) ≤ rank g :=
by rw [rank, rank, linear_map.range_comp]; exact dim_map_le _ _

end rank

lemma dim_zero_iff_forall_zero : module.rank K V = 0 ↔ ∀ x : V, x = 0 :=
begin
  split,
  { intros h x,
    have card_mk_range := (basis.of_vector_space K V).mk_range_eq_dim,
    rw [h, cardinal.mk_emptyc_iff, coe_of_vector_space, subtype.range_coe] at card_mk_range,
    simpa [card_mk_range] using (of_vector_space K V).mem_span x },
  { intro h,
    have : (⊤ : submodule K V) = ⊥,
    { ext x, simp [h x] },
    rw [←dim_top, this, dim_bot] }
end

lemma dim_zero_iff : module.rank K V = 0 ↔ subsingleton V :=
dim_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

/-- The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensional.

See also `finite_dimensional.fin_basis`.
-/
def basis.of_dim_eq_zero {ι : Type*} [is_empty ι] (hV : module.rank K V = 0) :
  basis ι K V :=
begin
  haveI : subsingleton V := dim_zero_iff.1 hV,
  exact basis.empty _
end

@[simp] lemma basis.of_dim_eq_zero_apply {ι : Type*} [is_empty ι]
  (hV : module.rank K V = 0) (i : ι) :
  basis.of_dim_eq_zero hV i = 0 :=
rfl


lemma dim_pos_iff_exists_ne_zero : 0 < module.rank K V ↔ ∃ x : V, x ≠ 0 :=
begin
  rw ←not_iff_not,
  simpa using dim_zero_iff_forall_zero
end

lemma dim_pos_iff_nontrivial : 0 < module.rank K V ↔ nontrivial V :=
dim_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

lemma dim_pos [h : nontrivial V] : 0 < module.rank K V :=
dim_pos_iff_nontrivial.2 h

lemma le_dim_iff_exists_linear_independent {c : cardinal} :
  c ≤ module.rank K V ↔ ∃ s : set V, cardinal.mk s = c ∧ linear_independent K (coe : s → V) :=
begin
  split,
  { intro h,
    let t := basis.of_vector_space K V,
    rw [← t.mk_eq_dim'', cardinal.le_mk_iff_exists_subset] at h,
    rcases h with ⟨s, hst, hsc⟩,
    exact ⟨s, hsc, (of_vector_space_index.linear_independent K V).mono hst⟩ },
  { rintro ⟨s, rfl, si⟩,
    exact cardinal_le_dim_of_linear_independent si }
end

lemma le_dim_iff_exists_linear_independent_finset {n : ℕ} :
  ↑n ≤ module.rank K V ↔
    ∃ s : finset V, s.card = n ∧ linear_independent K (coe : (s : set V) → V) :=
begin
  simp only [le_dim_iff_exists_linear_independent, cardinal.mk_eq_nat_iff_finset],
  split,
  { rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩,
    exact ⟨t, rfl, si⟩ },
  { rintro ⟨s, rfl, si⟩,
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩ }
end

lemma le_rank_iff_exists_linear_independent {c : cardinal} {f : V →ₗ[K] V'} :
  c ≤ rank f ↔
  ∃ s : set V, cardinal.lift.{v v'} (cardinal.mk s) = cardinal.lift.{v' v} c ∧
    linear_independent K (λ x : s, f x) :=
begin
  rcases f.range_restrict.exists_right_inverse_of_surjective f.range_range_restrict with ⟨g, hg⟩,
  have fg : left_inverse f.range_restrict g, from linear_map.congr_fun hg,
  refine ⟨λ h, _, _⟩,
  { rcases le_dim_iff_exists_linear_independent.1 h with ⟨s, rfl, si⟩,
    refine ⟨g '' s, cardinal.mk_image_eq_lift _ _ fg.injective, _⟩,
    replace fg : ∀ x, f (g x) = x, by { intro x, convert congr_arg subtype.val (fg x) },
    replace si : linear_independent K (λ x : s, f (g x)),
      by simpa only [fg] using si.map' _ (ker_subtype _),
    exact si.image_of_comp s g f },
  { rintro ⟨s, hsc, si⟩,
    have : linear_independent K (λ x : s, f.range_restrict x),
      from linear_independent.of_comp (f.range.subtype) (by convert si),
    convert cardinal_le_dim_of_linear_independent this.image,
    rw [← cardinal.lift_inj, ← hsc, cardinal.mk_image_eq_of_inj_on_lift],
    exact inj_on_iff_injective.2 this.injective }
end

lemma le_rank_iff_exists_linear_independent_finset {n : ℕ} {f : V →ₗ[K] V'} :
  ↑n ≤ rank f ↔ ∃ s : finset V, s.card = n ∧ linear_independent K (λ x : (s : set V), f x) :=
begin
  simp only [le_rank_iff_exists_linear_independent, cardinal.lift_nat_cast,
    cardinal.lift_eq_nat_iff, cardinal.mk_eq_nat_iff_finset],
  split,
  { rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩,
    exact ⟨t, rfl, si⟩ },
  { rintro ⟨s, rfl, si⟩,
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩ }
end

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
lemma dim_le_one_iff : module.rank K V ≤ 1 ↔ ∃ v₀ : V, ∀ v, ∃ r : K, r • v₀ = v :=
begin
  let b := basis.of_vector_space K V,
  split,
  { intro hd,
    rw [← b.mk_eq_dim'', cardinal.le_one_iff_subsingleton, subsingleton_coe] at hd,
    rcases eq_empty_or_nonempty (of_vector_space_index K V) with hb | ⟨⟨v₀, hv₀⟩⟩,
    { use 0,
      have h' : ∀ v : V, v = 0, { simpa [hb, submodule.eq_bot_iff] using b.span_eq.symm },
      intro v,
      simp [h' v] },
    { use v₀,
      have h' : (K ∙ v₀) = ⊤, { simpa [hd.eq_singleton_of_mem hv₀] using b.span_eq },
      intro v,
      have hv : v ∈ (⊤ : submodule K V) := mem_top,
      rwa [←h', mem_span_singleton] at hv } },
  { rintros ⟨v₀, hv₀⟩,
    have h : (K ∙ v₀) = ⊤,
    { ext, simp [mem_span_singleton, hv₀] },
    rw [←dim_top, ←h],
    convert dim_span_le _,
    simp }
end

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
lemma dim_submodule_le_one_iff (s : submodule K V) : module.rank K s ≤ 1 ↔ ∃ v₀ ∈ s, s ≤ K ∙ v₀ :=
begin
  simp_rw [dim_le_one_iff, le_span_singleton_iff],
  split,
  { rintro ⟨⟨v₀, hv₀⟩, h⟩,
    use [v₀, hv₀],
    intros v hv,
    obtain ⟨r, hr⟩ := h ⟨v, hv⟩,
    use r,
    simp_rw [subtype.ext_iff, coe_smul, submodule.coe_mk] at hr,
    exact hr },
  { rintro ⟨v₀, hv₀, h⟩,
    use ⟨v₀, hv₀⟩,
    rintro ⟨v, hv⟩,
    obtain ⟨r, hr⟩ := h v hv,
    use r,
    simp_rw [subtype.ext_iff, coe_smul, submodule.coe_mk],
    exact hr }
end

/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
lemma dim_submodule_le_one_iff' (s : submodule K V) : module.rank K s ≤ 1 ↔ ∃ v₀, s ≤ K ∙ v₀ :=
begin
  rw dim_submodule_le_one_iff,
  split,
  { rintros ⟨v₀, hv₀, h⟩,
    exact ⟨v₀, h⟩ },
  { rintros ⟨v₀, h⟩,
    by_cases hw : ∃ w : V, w ∈ s ∧ w ≠ 0,
    { rcases hw with ⟨w, hw, hw0⟩,
      use [w, hw],
      rcases mem_span_singleton.1 (h hw) with ⟨r', rfl⟩,
      have h0 : r' ≠ 0,
      { rintro rfl,
        simpa using hw0 },
      rwa span_singleton_smul_eq _ h0 },
    { push_neg at hw,
      rw ←submodule.eq_bot_iff at hw,
      simp [hw] } }
end

end field

end module

section unconstrained_universes

variables {E : Type v'}
variables [division_ring K] [add_comm_group V] [module K V]
          [add_comm_group E] [module K E]
open module

/-- Version of linear_equiv.dim_eq without universe constraints. -/
theorem linear_equiv.dim_eq_lift (f : V ≃ₗ[K] E) :
  cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K E) :=
begin
  let b := basis.of_vector_space K V,
  rw [← cardinal.lift_inj.1 b.mk_eq_dim, ← (b.map f).mk_eq_dim, cardinal.lift_mk],
end

end unconstrained_universes
