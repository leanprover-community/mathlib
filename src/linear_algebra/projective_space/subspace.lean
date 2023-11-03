/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/

import linear_algebra.projective_space.basic

/-!
# Subspaces of Projective Space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define subspaces of a projective space, and show that the subspaces of a projective
space form a complete lattice under inclusion.

## Implementation Details

A subspace of a projective space ℙ K V is defined to be a structure consisting of a subset of
ℙ K V such that if two nonzero vectors in V determine points in ℙ K V which are in the subset, and
the sum of the two vectors is nonzero, then the point determined by the sum of the two vectors is
also in the subset.

## Results

- There is a Galois insertion between the subsets of points of a projective space
  and the subspaces of the projective space, which is given by taking the span of the set of points.
- The subspaces of a projective space form a complete lattice under inclusion.

# Future Work
- Show that there is a one-to-one order-preserving correspondence between subspaces of a
  projective space and the submodules of the underlying vector space.
-/

variables (K V : Type*) [field K] [add_comm_group V] [module K V]

namespace projectivization

/-- A subspace of a projective space is a structure consisting of a set of points such that:
If two nonzero vectors determine points which are in the set, and the sum of the two vectors is
nonzero, then the point determined by the sum is also in the set. -/
@[ext] structure subspace :=
(carrier : set (ℙ K V))
(mem_add' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
  mk K v hv ∈ carrier → mk K w hw ∈ carrier → mk K (v + w) (hvw) ∈ carrier)

namespace subspace

variables {K V}

instance : set_like (subspace K V) (ℙ K V) :=
{ coe := carrier,
  coe_injective' := λ A B, by { cases A, cases B, simp } }

@[simp]
lemma mem_carrier_iff (A : subspace K V) (x : ℙ K V) : x ∈ A.carrier ↔ x ∈ A := iff.refl _

lemma mem_add (T : subspace K V) (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
  projectivization.mk K v hv ∈ T → projectivization.mk K w hw ∈ T →
  projectivization.mk K (v + w) (hvw) ∈ T :=
  T.mem_add' v w hv hw hvw

/-- The span of a set of points in a projective space is defined inductively to be the set of points
which contains the original set, and contains all points determined by the (nonzero) sum of two
nonzero vectors, each of which determine points in the span. -/
inductive span_carrier (S : set (ℙ K V)) : set (ℙ K V)
| of (x : ℙ K V) (hx : x ∈ S) : span_carrier x
| mem_add (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (hvw : v + w ≠ 0) :
    span_carrier (projectivization.mk K v hv) → span_carrier (projectivization.mk K w hw) →
    span_carrier (projectivization.mk K (v + w) (hvw))

/-- The span of a set of points in projective space is a subspace. -/
def span (S : set (ℙ K V)) : subspace K V :=
{ carrier := span_carrier S,
  mem_add' := λ v w hv hw hvw,
    span_carrier.mem_add v w hv hw hvw }

/-- The span of a set of points contains the set of points. -/
lemma subset_span (S : set (ℙ K V)) : S ⊆ span S := λ x hx, span_carrier.of _ hx

/-- The span of a set of points is a Galois insertion between sets of points of a projective space
and subspaces of the projective space. -/
def gi : galois_insertion (span : set (ℙ K V) → subspace K V) coe :=
{ choice := λ S hS, span S,
  gc := λ A B, ⟨λ h, le_trans (subset_span _) h, begin
    intros h x hx,
    induction hx,
    { apply h, assumption },
    { apply B.mem_add, assumption' }
  end⟩,
  le_l_u := λ S, subset_span _,
  choice_eq := λ _ _, rfl }

/-- The span of a subspace is the subspace. -/
@[simp] lemma span_coe (W : subspace K V) : span ↑W = W := galois_insertion.l_u_eq gi W

/-- The infimum of two subspaces exists. -/
instance has_inf : has_inf (subspace K V) :=
⟨λ A B, ⟨A ⊓ B, λ v w hv hw hvw h1 h2,
  ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

/-- Infimums of arbitrary collections of subspaces exist. -/
instance has_Inf : has_Inf (subspace K V) :=
⟨λ A, ⟨Inf (coe '' A), λ v w hv hw hvw h1 h2 t, begin
  rintro ⟨s, hs, rfl⟩,
  exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩),
end⟩⟩

/-- The subspaces of a projective space form a complete lattice. -/
instance : complete_lattice (subspace K V) :=
{ inf_le_left := λ A B x hx, by exact hx.1,
  inf_le_right := λ A B x hx, by exact hx.2,
  le_inf := λ A B C h1 h2 x hx, ⟨h1 hx, h2 hx⟩,
  ..(infer_instance : has_inf _),
  ..complete_lattice_of_Inf (subspace K V)
  begin
    refine λ s, ⟨λ a ha x hx, (hx _ ⟨a, ha, rfl⟩), λ a ha x hx E, _⟩,
    rintros ⟨E, hE, rfl⟩,
    exact (ha hE hx)
  end }

instance subspace_inhabited : inhabited (subspace K V) :=
{ default := ⊤ }

/-- The span of the empty set is the bottom of the lattice of subspaces. -/
@[simp] lemma span_empty : span (∅ : set (ℙ K V)) = ⊥ := gi.gc.l_bot

/-- The span of the entire projective space is the top of the lattice of subspaces. -/
@[simp] lemma span_univ : span (set.univ : set (ℙ K V)) = ⊤ :=
by { rw [eq_top_iff, set_like.le_def], intros x hx, exact subset_span _ (set.mem_univ x) }

/-- The span of a set of points is contained in a subspace if and only if the set of points is
contained in the subspace. -/
lemma span_le_subspace_iff {S : set (ℙ K V)} {W : subspace K V} : span S ≤ W ↔ S ⊆ W :=
gi.gc S W

/-- If a set of points is a subset of another set of points, then its span will be contained in the
span of that set. -/
@[mono] lemma monotone_span : monotone (span : set (ℙ K V) → subspace K V) := gi.gc.monotone_l

lemma subset_span_trans {S T U : set (ℙ K V)} (hST : S ⊆ span T) (hTU : T ⊆ span U) :
  S ⊆ span U :=
gi.gc.le_u_l_trans hST hTU

/-- The supremum of two subspaces is equal to the span of their union. -/
lemma span_union (S T : set (ℙ K V)) : span (S ∪ T) = span S ⊔ span T := (@gi K V _ _ _).gc.l_sup

/-- The supremum of a collection of subspaces is equal to the span of the union of the
collection. -/
lemma span_Union {ι} (s : ι → set (ℙ K V)) : span (⋃ i, s i) = ⨆ i, span (s i) :=
(@gi K V _ _ _).gc.l_supr

/-- The supremum of a subspace and the span of a set of points is equal to the span of the union of
the subspace and the set of points. -/
lemma sup_span {S : set (ℙ K V)} {W : subspace K V} : W ⊔ span S = span (W ∪ S) :=
by rw [span_union, span_coe]

lemma span_sup {S : set (ℙ K V)} {W : subspace K V}: span S ⊔ W = span (S ∪ W) :=
by rw [span_union, span_coe]

/-- A point in a projective space is contained in the span of a set of points if and only if the
point is contained in all subspaces of the projective space which contain the set of points. -/
lemma mem_span {S : set (ℙ K V)} (u : ℙ K V) : u ∈ span S ↔ ∀ (W : subspace K V), S ⊆ W → u ∈ W :=
by { simp_rw ← span_le_subspace_iff, exact ⟨λ hu W hW, hW hu, λ W, W (span S) (le_refl _)⟩ }

/-- The span of a set of points in a projective space is equal to the infimum of the collection of
subspaces which contain the set. -/
lemma span_eq_Inf {S : set (ℙ K V)} : span S = Inf {W | S ⊆ W} :=
begin
  ext,
  simp_rw [mem_carrier_iff, mem_span x],
  refine ⟨λ hx, _, λ hx W hW, _⟩,
  { rintros W ⟨T, ⟨hT, rfl⟩⟩, exact (hx T hT) },
  { exact (@Inf_le _ _ {W : subspace K V | S ⊆ ↑W} W hW) x hx },
end

/-- If a set of points in projective space is contained in a subspace, and that subspace is
contained in the span of the set of points, then the span of the set of points is equal to
the subspace. -/
lemma span_eq_of_le {S : set (ℙ K V)} {W : subspace K V} (hS : S ⊆ W) (hW : W ≤ span S) :
  span S = W :=
le_antisymm (span_le_subspace_iff.mpr hS) hW

/-- The spans of two sets of points in a projective space are equal if and only if each set of
points is contained in the span of the other set. -/
lemma span_eq_span_iff {S T : set (ℙ K V)} : span S = span T ↔ S ⊆ span T ∧ T ⊆ span S :=
⟨λ h, ⟨h ▸ subset_span S, h.symm ▸ subset_span T⟩,
  λ h, le_antisymm (span_le_subspace_iff.2 h.1) (span_le_subspace_iff.2 h.2)⟩

open_locale big_operators

/-- If a family of vectors is such that every nonzero vector in the family determines a point in the
corresponding projective space which is contained in a subspace, then every nonzero finite sum of
vectors from the family also determines a point contained in that subspace. -/
lemma mk_sum_mem {ι : Type*} (s : finset ι) (W : subspace K V) (f : ι → V)
  (hf : ∀ i, i ∈ s → f i = 0 ∨ ∃ (hi : f i ≠ 0), projectivization.mk K (f i) (hi) ∈ W)
  (hs : ∑ i in s, f i ≠ 0) : projectivization.mk K (∑ i in s, f i) hs ∈ W :=
begin
  suffices : (∑ (i : ι) in s, f i = 0) ∨
    (∃ (h : (∑ (i : ι) in s, f i ≠ 0)), (projectivization.mk K (∑ (i : ι) in s, f i) h ∈ W)), by
    { rcases this, contradiction, cases this, assumption },
  apply finset.sum_induction f (λ x, x = 0 ∨ (∃ hx : x ≠ 0, projectivization.mk K x hx ∈ W)),
  { intros a b ha hb, by_cases hab : a + b = 0,
    { left, exact hab },
    { cases ha; cases hb,
      { rw [ha, hb, zero_add], simp },
      { simp_rw [ha, zero_add], right, exact hb },
      { simp_rw [hb, add_zero], right, exact ha },
      { right, cases ha, cases hb, exact ⟨hab, mem_add W a b ha_w hb_w hab ha_h hb_h⟩ } } },
  { simp },
  { intros i hi, exact hf i hi }
end

/-- If a family of vectors is such that every nonzero vector in the family determines a point in the
corresponding projective space which is contained in a subspace, then every nonzero linear
combination of vectors from the family also determines a point contained in that subspace. -/
lemma mk_sum_smul_mem {ι : Type*} (s : finset ι) (W : subspace K V) (f : ι → V) (g : ι → K)
  (hf : ∀ i, i ∈ s → f i = 0 ∨ ∃ (hi : f i ≠ 0), projectivization.mk K (f i) (hi) ∈ W)
  (hs : ∑ i in s, (g i) • f i ≠ 0) : projectivization.mk K (∑ i in s, (g i) • f i) hs ∈ W :=
begin
  refine mk_sum_mem s W (g • f) _ hs,
  intro i,
  by_cases hgz : g i = 0,
  { rw [hgz, zero_smul], simp },
  { by_cases hfz : f i = 0,
    { rw [hfz, smul_zero], simp },
    { intro hi, right,
      refine ⟨by { rw [ne.def, smul_eq_zero, not_or_distrib], exact ⟨hgz, hfz⟩ }, _⟩,
      cases (or.resolve_left (hf i hi) hfz), convert h using 1, rw mk_eq_mk_iff', use g i } }
end

/-- If a set of points in a projective space has the property that for any two unique points
contained in the set, these points being dependent with a third point in the projective space
implies that this third point is contained in the set, then the set is a subspace. -/
def mk_of_dependent (S : set (ℙ K V))
  (h : ∀ u v w, u ≠ v → u ∈ S → v ∈ S → dependent ![u, v, w] → w ∈ S) : subspace K V :=
{ carrier := S,
  mem_add' := λ u v hu hv huv huS hvS,
  begin
    by_cases heq : projectivization.mk K u hu = projectivization.mk K v hv,
    { convert hvS using 1,
      rw mk_eq_mk_iff' at heq ⊢,
      cases heq with a ha,
      exact ⟨a + 1, by { rw [add_smul, ha, one_smul] }⟩ },
    { refine h _ _ (projectivization.mk K (u + v) huv) heq huS hvS _,
      convert dependent.mk ![u, v, u + v] _ _,
      { ext i, fin_cases i; simp },
      { intro i, fin_cases i; assumption },
      { rw fintype.not_linear_independent_iff,
        refine ⟨![-1, -1, 1], _, ⟨2, by { simp }⟩⟩,
        simp only [fin.sum_univ_three, matrix.cons_val_zero, neg_smul, one_smul,
          matrix.cons_val_one, matrix.head_cons, matrix.cons_vec_bit0_eq_alt0, matrix.cons_append,
          matrix.empty_append, matrix.cons_vec_alt0],
        abel } },
  end }

/-- If a set of points in a projective space has the property that for any independent family of
points contained in the set, this family being dependent with another point in the projective space
implies that this point is contained in the set, then the set is a subspace. -/
def mk_of_dependent' (S : set (ℙ K V)) (h : ∀ (ι : Type*) (f : ι → ℙ K V) (hf: independent f)
  (u : ℙ K V) (hf' : dependent (λ t, sum.rec_on t f (λ _, u) : ι ⊕ punit → ℙ K V))
  (h : ∀ i, f i ∈ S), u ∈ S) : subspace K V :=
mk_of_dependent S
begin
  intros u v w huv huS hvS hdep,
  refine h (ulift $ fin 2) (![u, v] ∘ ulift.down) _ _ _ _,
  { rw [independent_iff],
    rw [← independent_pair_iff_neq, independent_iff] at huv,
    apply linear_independent.comp huv ulift.down (ulift.down_injective) },
  { rw [dependent_iff] at hdep ⊢, by_contra, apply hdep,
    convert linear_independent.comp h (![sum.inl 0, sum.inl 1, sum.inr punit.star]) _,
    { ext i, fin_cases i; refl },
    { intros m n _, fin_cases m; fin_cases n; tidy } },
  { simp_rw [ulift.forall, function.comp_app], intro x, fin_cases x; assumption },
end

/-- If a family of points in a projective space is independent, and adding a point to the family
results in it becoming dependent, then the added point's representative is in the span
of the representatives of the original family. -/
lemma independent_sum_punit_dependent {ι : Type*} (f : ι → ℙ K V) (hf: independent f) (u : ℙ K V)
  (hf' : dependent (λ t, sum.rec_on t f (λ _, u) : ι ⊕ punit → ℙ K V)) :
  u.rep ∈ submodule.span K (set.range (projectivization.rep ∘ f)) :=
begin
  simp_rw [dependent_iff, independent_iff] at hf' hf,
  have : ¬ linear_independent K (sum.elim (projectivization.rep ∘ f)
    (projectivization.rep ∘ (λ t, u) : punit → V)), by { convert hf', ext, cases x; simp },
  have hu : linear_independent K (λ (x : punit), u.rep) :=
    linear_independent_unique (λ (x : punit), u.rep) (rep_nonzero u),
  have hd : ¬ disjoint (submodule.span K (set.range (projectivization.rep ∘ f)))
    (submodule.span K (set.range (projectivization.rep ∘ (λ t, u) : punit → V))), by
    { by_contra, exact this (linear_independent.sum_type hf hu h) },
  rw [disjoint_iff, ← ne.def, submodule.ne_bot_iff] at hd,
  rcases hd with ⟨v, hv1, hv3⟩,
  cases submodule.mem_inf.1 hv1 with hv1 hv2,
  have hv : v ∈ submodule.span K {u.rep}, by { convert hv2, simp },
  cases submodule.mem_span_singleton.1 hv with a ha,
  rw [← ha] at hv1,
  convert submodule.smul_mem _ a⁻¹ hv1,
  have haz : a ≠ 0, by { by_contra haz, rw [haz, zero_smul] at ha, exact hv3 ha.symm },
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel haz, one_smul],
end

/-- If a subspace of a projective space contains a family of independent points, and this family is
dependent with another point in the projective space, then the point is contained in the
subspace. -/
lemma mem_of_dependent' {ι : Type*} (W : subspace K V) (f : ι → ℙ K V) (hf: independent f)
  (u : ℙ K V) (hf' : dependent (λ t, sum.rec_on t f (λ _, u) : ι ⊕ punit → ℙ K V))
  (h : ∀ i, f i ∈ W) : u ∈ W :=
begin
  let hu := independent_sum_punit_dependent f hf u hf',
  rcases (submodule.mem_span_finite_of_mem_span hu) with ⟨s, ⟨h2, h3⟩⟩,
  rcases mem_span_finset.1 h3 with ⟨g, hg⟩,
  convert mk_sum_smul_mem s W (λ x, x : V → V) (g) _ _,
  { rw [← mk_rep u, mk_eq_mk_iff'], use 1, rw one_smul, exact hg },
  { intros i his, by_cases hi : i = 0,
    { left, exact hi },
    { right,
      refine ⟨hi, _⟩,
      cases h2 his with y hy,
      rw function.comp_app at hy,
      convert h y,
      rw [← mk_rep (f y), mk_eq_mk_iff'],
      exact ⟨1, by { rwa one_smul }⟩ } },
  { rw hg, exact rep_nonzero u },
end

/-- If a subspace of a projective space contains two unique points, and a third point from the
projective space is dependent with the two unique points, then the third point is contained in the
subspace. -/
lemma mem_of_dependent (W : subspace K V) (u v w : ℙ K V) (h: u ≠ v) (hu : u ∈ W) (hv : v ∈ W)
  (hdep: dependent ![u, v, w]) : w ∈ W :=
begin
  refine mem_of_dependent' W ![u, v] _ w _ _,
  { rwa independent_pair_iff_neq },
  { rw [dependent_iff] at hdep ⊢,
    by_contra,
    apply hdep,
    convert linear_independent.comp h (![sum.inl 0, sum.inl 1, sum.inr punit.star]) _,
    { ext, fin_cases x; refl },
    { intros m n; fin_cases m; fin_cases n; tidy } },
  { intro i, fin_cases i; assumption },
end

end subspace

end projectivization
