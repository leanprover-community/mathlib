/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.integration

/-!

# Vector valued measures

This file defines vector valued measures, which are σ-additive functions from a set to a add monoid
`M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `signed_measure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `complex_measure α`.

## Main definitions

* `vector_measure` is a vector valued, σ-additive function that maps the empty
  and non-measurable set to zero.
* `vector_measure.map` is the pushforward of a vector measure along a function.
* `vector_measure.restrict` is the restriction of a vector measure on some set.

## Notation

* `v ≤[i] w` means that the vector measure `v` restricted on the set `i` is less than or equal
  to the vector measure `w` restricted on `i`, i.e. `v.restrict i ≤ w.restrict i`.

## Implementation notes

We require all non-measurable sets to be mapped to zero in order for the extensionality lemma
to only compare the underlying functions for measurable sets.

We use `has_sum` instead of `tsum` in the definition of vector measures in comparison to `measure`
since this provides summablity.

## Tags

vector measure, signed measure, complex measure
-/

noncomputable theory

open_locale classical big_operators nnreal ennreal

namespace measure_theory

variables {α β : Type*} [measurable_space α]

/-- A vector measure on a measurable space `α` is a σ-additive `M`-valued function (for some `M`
an add monoid) such that the empty set and non-measurable sets are mapped to zero. -/
structure vector_measure (α : Type*) [measurable_space α]
  (M : Type*) [add_comm_monoid M] [topological_space M] :=
(measure_of' : set α → M)
(empty' : measure_of' ∅ = 0)
(not_measurable' ⦃i : set α⦄ : ¬ measurable_set i → measure_of' i = 0)
(m_Union' ⦃f : ℕ → set α⦄ :
  (∀ i, measurable_set (f i)) → pairwise (disjoint on f) →
  has_sum (λ i, measure_of' (f i)) (measure_of' (⋃ i, f i)))

/-- A `signed_measure` is a `ℝ`-vector measure. -/
abbreviation signed_measure (α : Type*) [measurable_space α] := vector_measure α ℝ
/-- A `complex_measure` is a `ℂ`-vector_measure. -/
abbreviation complex_measure (α : Type*) [measurable_space α] := vector_measure α ℂ

open set measure_theory

namespace vector_measure

section

variables {M : Type*} [add_comm_monoid M] [topological_space M]

instance : has_coe_to_fun (vector_measure α M) :=
⟨λ _, set α → M, vector_measure.measure_of'⟩

initialize_simps_projections vector_measure (measure_of' → apply)

@[simp]
lemma measure_of_eq_coe (v : vector_measure α M) : v.measure_of' = v := rfl

@[simp]
lemma empty (v : vector_measure α M) : v ∅ = 0 := v.empty'

lemma not_measurable (v : vector_measure α M)
  {i : set α} (hi : ¬ measurable_set i) : v i = 0 := v.not_measurable' hi

lemma m_Union (v : vector_measure α M) {f : ℕ → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  has_sum (λ i, v (f i)) (v (⋃ i, f i)) :=
v.m_Union' hf₁ hf₂

lemma of_disjoint_Union_nat [t2_space M] (v : vector_measure α M) {f : ℕ → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  v (⋃ i, f i) = ∑' i, v (f i) :=
(v.m_Union hf₁ hf₂).tsum_eq.symm

lemma coe_injective : @function.injective (vector_measure α M) (set α → M) coe_fn :=
λ v w h, by { cases v, cases w, congr' }

lemma ext_iff' (v w : vector_measure α M) :
  v = w ↔ ∀ i : set α, v i = w i :=
by rw [← coe_injective.eq_iff, function.funext_iff]

lemma ext_iff (v w : vector_measure α M) :
  v = w ↔ ∀ i : set α, measurable_set i → v i = w i :=
begin
  split,
  { rintro rfl _ _, refl },
  { rw ext_iff',
    intros h i,
    by_cases hi : measurable_set i,
    { exact h i hi },
    { simp_rw [not_measurable _ hi] } }
end

@[ext] lemma ext {s t : vector_measure α M}
  (h : ∀ i : set α, measurable_set i → s i = t i) : s = t :=
(ext_iff s t).2 h

variables [t2_space M] {v : vector_measure α M} {f : ℕ → set α}

lemma has_sum_of_disjoint_Union [encodable β] {f : β → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  has_sum (λ i, v (f i)) (v (⋃ i, f i)) :=
begin
  set g := λ i : ℕ, ⋃ (b : β) (H : b ∈ encodable.decode₂ β i), f b with hg,
  have hg₁ : ∀ i, measurable_set (g i),
  { exact λ _, measurable_set.Union (λ b, measurable_set.Union_Prop $ λ _, hf₁ b) },
  have hg₂ : pairwise (disjoint on g),
  { exact encodable.Union_decode₂_disjoint_on hf₂ },
  have := v.of_disjoint_Union_nat hg₁ hg₂,
  rw [hg, encodable.Union_decode₂] at this,

  have hg₃ : (λ (i : β), v (f i)) = (λ i, v (g (encodable.encode i))),
  { ext, rw hg, simp only,
    congr, ext y, simp only [exists_prop, mem_Union, option.mem_def],
    split,
    { intro hy,
      refine ⟨x, (encodable.decode₂_is_partial_inv _ _).2 rfl, hy⟩ },
    { rintro ⟨b, hb₁, hb₂⟩,
      rw (encodable.decode₂_is_partial_inv _ _) at hb₁,
      rwa ← encodable.encode_injective hb₁ } },

  rw [summable.has_sum_iff, this, ← tsum_Union_decode₂],
  { exact v.empty },
  { rw hg₃, change summable ((λ i, v (g i)) ∘ encodable.encode),
    rw function.injective.summable_iff encodable.encode_injective,
    { exact (v.m_Union hg₁ hg₂).summable },
    { intros x hx,
      convert v.empty,
      simp only [Union_eq_empty, option.mem_def, not_exists, mem_range] at ⊢ hx,
      intros i hi,
      exact false.elim ((hx i) ((encodable.decode₂_is_partial_inv _ _).1 hi)) } }
end

lemma of_disjoint_Union [encodable β] {f : β → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  v (⋃ i, f i) = ∑' i, v (f i) :=
(has_sum_of_disjoint_Union hf₁ hf₂).tsum_eq.symm

lemma of_union {A B : set α}
  (h : disjoint A B) (hA : measurable_set A) (hB : measurable_set B) :
  v (A ∪ B) = v A + v B :=
begin
  rw [union_eq_Union, of_disjoint_Union, tsum_fintype, fintype.sum_bool, cond, cond],
  exacts [λ b, bool.cases_on b hB hA, pairwise_disjoint_on_bool.2 h]
end

lemma of_add_of_diff {A B : set α} (hA : measurable_set A) (hB : measurable_set B)
  (h : A ⊆ B) : v A + v (B \ A) = v B :=
begin
  rw [← of_union disjoint_diff hA (hB.diff hA), union_diff_cancel h],
  apply_instance,
end

lemma of_diff {M : Type*} [add_comm_group M]
  [topological_space M] [t2_space M] {v : vector_measure α M}
  {A B : set α} (hA : measurable_set A) (hB : measurable_set B)
  (h : A ⊆ B) : v (B \ A) = v B - (v A) :=
begin
  rw [← of_add_of_diff hA hB h, add_sub_cancel'],
  apply_instance,
end

lemma of_Union_nonneg {M : Type*} [topological_space M]
  [ordered_add_comm_monoid M] [order_closed_topology M]
  {v : vector_measure α M} (hf₁ : ∀ i, measurable_set (f i))
  (hf₂ : pairwise (disjoint on f)) (hf₃ : ∀ i, 0 ≤ v (f i)) :
  0 ≤ v (⋃ i, f i) :=
(v.of_disjoint_Union_nat hf₁ hf₂).symm ▸ tsum_nonneg hf₃

lemma of_Union_nonpos {M : Type*} [topological_space M]
  [ordered_add_comm_monoid M] [order_closed_topology M]
  {v : vector_measure α M} (hf₁ : ∀ i, measurable_set (f i))
  (hf₂ : pairwise (disjoint on f)) (hf₃ : ∀ i, v (f i) ≤ 0) :
  v (⋃ i, f i) ≤ 0 :=
(v.of_disjoint_Union_nat hf₁ hf₂).symm ▸ tsum_nonpos hf₃

lemma of_nonneg_disjoint_union_eq_zero {s : signed_measure α} {A B : set α}
  (h : disjoint A B) (hA₁ : measurable_set A) (hB₁ : measurable_set B)
  (hA₂ : 0 ≤ s A) (hB₂ : 0 ≤ s B)
  (hAB : s (A ∪ B) = 0) : s A = 0 :=
begin
  rw of_union h hA₁ hB₁ at hAB,
  linarith,
  apply_instance,
end

lemma of_nonpos_disjoint_union_eq_zero {s : signed_measure α} {A B : set α}
  (h : disjoint A B) (hA₁ : measurable_set A) (hB₁ : measurable_set B)
  (hA₂ : s A ≤ 0) (hB₂ : s B ≤ 0)
  (hAB : s (A ∪ B) = 0) : s A = 0 :=
begin
  rw of_union h hA₁ hB₁ at hAB,
  linarith,
  apply_instance,
end

end

section add_comm_monoid

variables {M : Type*} [add_comm_monoid M] [topological_space M]

instance : has_zero (vector_measure α M) :=
⟨⟨0, rfl, λ _ _, rfl, λ _ _ _, has_sum_zero⟩⟩

instance : inhabited (vector_measure α M) := ⟨0⟩

@[simp] lemma coe_zero : ⇑(0 : vector_measure α M) = 0 := rfl
lemma zero_apply (i : set α) : (0 : vector_measure α M) i = 0 := rfl

variables [has_continuous_add M]

/-- The sum of two vector measure is a vector measure. -/
def add (v w : vector_measure α M) : vector_measure α M :=
{ measure_of' := v + w,
  empty' := by simp,
  not_measurable' := λ _ hi,
    by simp [v.not_measurable hi, w.not_measurable hi],
  m_Union' := λ f hf₁ hf₂,
    has_sum.add (v.m_Union hf₁ hf₂) (w.m_Union hf₁ hf₂) }

instance : has_add (vector_measure α M) := ⟨add⟩

@[simp] lemma coe_add (v w : vector_measure α M) : ⇑(v + w) = v + w := rfl
lemma add_apply (v w : vector_measure α M) (i : set α) :(v + w) i = v i + w i := rfl

instance : add_comm_monoid (vector_measure α M) :=
function.injective.add_comm_monoid _ coe_injective coe_zero coe_add

/-- `coe_fn` is an `add_monoid_hom`. -/
@[simps]
def coe_fn_add_monoid_hom : vector_measure α M →+ (set α → M) :=
{ to_fun := coe_fn, map_zero' := coe_zero, map_add' := coe_add }

end add_comm_monoid

section add_comm_group

variables {M : Type*} [add_comm_group M] [topological_space M]

variables [topological_add_group M]

/-- The negative of a vector measure is a vector measure. -/
def neg (v : vector_measure α M) : vector_measure α M :=
{ measure_of' := -v,
  empty' := by simp,
  not_measurable' := λ _ hi, by simp [v.not_measurable hi],
  m_Union' := λ f hf₁ hf₂, has_sum.neg $ v.m_Union hf₁ hf₂ }

instance : has_neg (vector_measure α M) := ⟨neg⟩

@[simp] lemma coe_neg (v : vector_measure α M) : ⇑(-v) = - v := rfl
lemma neg_apply (v : vector_measure α M) (i : set α) :(-v) i = - v i := rfl

/-- The difference of two vector measure is a vector measure. -/
def sub (v w : vector_measure α M) : vector_measure α M :=
{ measure_of' := v - w,
  empty' := by simp,
  not_measurable' := λ _ hi,
    by simp [v.not_measurable hi, w.not_measurable hi],
  m_Union' := λ f hf₁ hf₂,
    has_sum.sub (v.m_Union hf₁ hf₂)
      (w.m_Union hf₁ hf₂) }

instance : has_sub (vector_measure α M) := ⟨sub⟩

@[simp] lemma coe_sub (v w : vector_measure α M) : ⇑(v - w) = v - w := rfl
lemma sub_apply (v w : vector_measure α M) (i : set α) : (v - w) i = v i - w i := rfl

instance : add_comm_group (vector_measure α M) :=
function.injective.add_comm_group _ coe_injective coe_zero coe_add coe_neg coe_sub

end add_comm_group

section distrib_mul_action

variables {M : Type*} [add_comm_monoid M] [topological_space M]
variables {R : Type*} [semiring R] [distrib_mul_action R M]
variables [topological_space R] [has_continuous_smul R M]

/-- Given a real number `r` and a signed measure `s`, `smul r s` is the signed
measure corresponding to the function `r • s`. -/
def smul (r : R) (v : vector_measure α M) : vector_measure α M :=
{ measure_of' := r • v,
  empty' := by rw [pi.smul_apply, empty, smul_zero],
  not_measurable' := λ _ hi, by rw [pi.smul_apply, v.not_measurable hi, smul_zero],
  m_Union' := λ _ hf₁ hf₂, has_sum.smul (v.m_Union hf₁ hf₂) }

instance : has_scalar R (vector_measure α M) := ⟨smul⟩

@[simp] lemma coe_smul (r : R) (v : vector_measure α M) : ⇑(r • v) = r • v := rfl
lemma smul_apply (r : R) (v : vector_measure α M) (i : set α) :
  (r • v) i = r • v i := rfl

instance [has_continuous_add M] : distrib_mul_action R (vector_measure α M) :=
function.injective.distrib_mul_action coe_fn_add_monoid_hom coe_injective coe_smul

end distrib_mul_action

section module

variables {M : Type*} [add_comm_monoid M] [topological_space M]
variables {R : Type*} [semiring R] [module R M]
variables [topological_space R] [has_continuous_smul R M]

instance [has_continuous_add M] : module R (vector_measure α M) :=
function.injective.module R coe_fn_add_monoid_hom coe_injective coe_smul

end module

end vector_measure

namespace measure

/-- A finite measure coerced into a real function is a signed measure. -/
@[simps]
def to_signed_measure (μ : measure α) [hμ : finite_measure μ] : signed_measure α :=
{ measure_of' := λ i : set α, if measurable_set i then (μ.measure_of i).to_real else 0,
  empty' := by simp [μ.empty],
  not_measurable' := λ _ hi, if_neg hi,
  m_Union' :=
  begin
    intros _ hf₁ hf₂,
    rw [μ.m_Union hf₁ hf₂, ennreal.tsum_to_real_eq, if_pos (measurable_set.Union hf₁),
        summable.has_sum_iff],
    { congr, ext n, rw if_pos (hf₁ n) },
    { refine @summable_of_nonneg_of_le _ (ennreal.to_real ∘ μ ∘ f) _ _ _ _,
      { intro, split_ifs,
        exacts [ennreal.to_real_nonneg, le_refl _] },
      { intro, split_ifs,
        exacts [le_refl _, ennreal.to_real_nonneg] },
        exact summable_measure_to_real hf₁ hf₂ },
    { intros a ha,
      apply ne_of_lt hμ.measure_univ_lt_top,
      rw [eq_top_iff, ← ha, outer_measure.measure_of_eq_coe, coe_to_outer_measure],
      exact measure_mono (set.subset_univ _) }
  end }

lemma to_signed_measure_apply_measurable {μ : measure α} [finite_measure μ]
  {i : set α} (hi : measurable_set i) :
  μ.to_signed_measure i = (μ i).to_real :=
if_pos hi

@[simp] lemma to_signed_measure_zero :
  (0 : measure α).to_signed_measure = 0 :=
by { ext i hi, simp }

@[simp] lemma to_signed_measure_add (μ ν : measure α) [finite_measure μ] [finite_measure ν] :
  (μ + ν).to_signed_measure = μ.to_signed_measure + ν.to_signed_measure :=
begin
  ext i hi,
  rw [to_signed_measure_apply_measurable hi, add_apply,
      ennreal.to_real_add (ne_of_lt (measure_lt_top _ _ )) (ne_of_lt (measure_lt_top _ _)),
      vector_measure.add_apply, to_signed_measure_apply_measurable hi,
      to_signed_measure_apply_measurable hi],
  all_goals { apply_instance }
end

@[simp] lemma to_signed_measure_smul (μ : measure α) [finite_measure μ] (r : ℝ≥0) :
  (r • μ).to_signed_measure = r • μ.to_signed_measure :=
begin
  ext i hi,
  rw [to_signed_measure_apply_measurable hi, vector_measure.smul_apply,
      to_signed_measure_apply_measurable hi, coe_nnreal_smul, pi.smul_apply,
      ennreal.to_real_smul],
end

/-- A measure is a vector measure over `ℝ≥0∞`. -/
@[simps]
def to_ennreal_vector_measure (μ : measure α) : vector_measure α ℝ≥0∞ :=
{ measure_of' := λ i : set α, if measurable_set i then μ i else 0,
  empty' := by simp [μ.empty],
  not_measurable' := λ _ hi, if_neg hi,
  m_Union' := λ _ hf₁ hf₂,
  begin
    rw summable.has_sum_iff ennreal.summable,
    { rw [if_pos (measurable_set.Union hf₁), measure_theory.measure_Union hf₂ hf₁],
      exact tsum_congr (λ n, if_pos (hf₁ n)) },
  end }

lemma to_ennreal_vector_measure_apply_measurable
  {μ : measure α} {i : set α} (hi : measurable_set i) :
  μ.to_ennreal_vector_measure i = μ i :=
if_pos hi

@[simp] lemma to_ennreal_vector_measure_zero :
  (0 : measure α).to_ennreal_vector_measure = 0 :=
by { ext i hi, simp }

@[simp] lemma to_ennreal_vector_measure_add (μ ν : measure α) :
  (μ + ν).to_ennreal_vector_measure = μ.to_ennreal_vector_measure + ν.to_ennreal_vector_measure :=
begin
  refine measure_theory.vector_measure.ext (λ i hi, _),
  rw [to_ennreal_vector_measure_apply_measurable hi, add_apply, vector_measure.add_apply,
      to_ennreal_vector_measure_apply_measurable hi, to_ennreal_vector_measure_apply_measurable hi]
end

/-- Given two finite measures `μ, ν`, `sub_to_signed_measure μ ν` is the signed measure
corresponding to the function `μ - ν`. -/
def sub_to_signed_measure (μ ν : measure α) [hμ : finite_measure μ] [hν : finite_measure ν] :
  signed_measure α :=
μ.to_signed_measure - ν.to_signed_measure

lemma sub_to_signed_measure_apply {μ ν : measure α} [finite_measure μ] [finite_measure ν]
  {i : set α} (hi : measurable_set i) :
  μ.sub_to_signed_measure ν i = (μ i).to_real - (ν i).to_real :=
begin
  rw [sub_to_signed_measure, vector_measure.sub_apply, to_signed_measure_apply_measurable hi,
      measure.to_signed_measure_apply_measurable hi, sub_eq_add_neg]
end

end measure

namespace vector_measure

section

variables [measurable_space β]
variables {M : Type*} [add_comm_monoid M] [topological_space M]
variables (v : vector_measure α M)

/-- The pushforward of a vector measure along a function. -/
def map (v : vector_measure α M) (f : α → β) :
  vector_measure β M :=
if hf : measurable f then
{ measure_of' := λ s, if measurable_set s then v (f ⁻¹' s) else 0,
  empty' := by simp,
  not_measurable' := λ i hi, if_neg hi,
  m_Union' :=
  begin
    intros g hg₁ hg₂,
    convert v.m_Union (λ i, hf (hg₁ i)) (λ i j hij x hx, hg₂ i j hij hx),
    { ext i, rw if_pos (hg₁ i) },
    { rw [preimage_Union, if_pos (measurable_set.Union hg₁)] }
  end } else 0

lemma map_apply {f : α → β} (hf : measurable f) {s : set β} (hs : measurable_set s) :
  v.map f s = v (f ⁻¹' s) :=
by { rw [map, dif_pos hf], exact if_pos hs }

@[simp] lemma map_id : v.map id = v :=
ext (λ i hi, by rw [map_apply v measurable_id hi, preimage_id])

@[simp] lemma map_zero (f : α → β) : (0 : vector_measure α M).map f = 0 :=
begin
  by_cases hf : measurable f,
  { ext i hi,
    rw [map_apply _ hf hi, zero_apply, zero_apply] },
  { exact dif_neg hf }
end

/-- The restriction of a vector measure on some set. -/
def restrict (v : vector_measure α M) (i : set α) :
  vector_measure α M :=
if hi : measurable_set i then
{ measure_of' := λ s, if measurable_set s then v (s ∩ i) else 0,
  empty' := by simp,
  not_measurable' := λ i hi, if_neg hi,
  m_Union' :=
  begin
    intros f hf₁ hf₂,
    convert v.m_Union (λ n, (hf₁ n).inter hi)
      (hf₂.mono $ λ i j, disjoint.mono inf_le_left inf_le_left),
    { ext n, rw if_pos (hf₁ n) },
    { rw [Union_inter, if_pos (measurable_set.Union hf₁)] }
  end } else 0

lemma restrict_not_measurable {i : set α} (hi : ¬ measurable_set i) :
  v.restrict i = 0 :=
dif_neg hi

lemma restrict_apply {i : set α} (hi : measurable_set i)
  {j : set α} (hj : measurable_set j) : v.restrict i j = v (j ∩ i) :=
by { rw [restrict, dif_pos hi], exact if_pos hj }

lemma restrict_eq_self {i : set α} (hi : measurable_set i)
  {j : set α} (hj : measurable_set j) (hij : j ⊆ i) : v.restrict i j = v j :=
by rw [restrict_apply v hi hj, inter_eq_left_iff_subset.2 hij]

@[simp] lemma restrict_empty : v.restrict ∅ = 0 :=
ext (λ i hi, by rw [restrict_apply v measurable_set.empty hi, inter_empty, v.empty, zero_apply])

@[simp] lemma restrict_univ : v.restrict univ = v :=
ext (λ i hi, by rw [restrict_apply v measurable_set.univ hi, inter_univ])

@[simp] lemma restrict_zero {i : set α} :
  (0 : vector_measure α M).restrict i = 0 :=
begin
  by_cases hi : measurable_set i,
  { ext j hj, rw [restrict_apply 0 hi hj], refl },
  { exact dif_neg hi }
end

section has_continuous_add

variables [has_continuous_add M]

lemma map_add (v w : vector_measure α M) (f : α → β) :
  (v + w).map f = v.map f + w.map f :=
begin
  by_cases hf : measurable f,
  { ext i hi,
    simp [map_apply _ hf hi] },
  { simp [map, dif_neg hf] }
end

/-- `vector_measure.map` as an additive monoid homomorphism. -/
@[simps] def map_gm (f : α → β) : vector_measure α M →+ vector_measure β M :=
{ to_fun := λ v, v.map f,
  map_zero' := map_zero f,
  map_add' := λ _ _, map_add _ _ f }

lemma restrict_add (v w : vector_measure α M) (i : set α) :
  (v + w).restrict i = v.restrict i + w.restrict i :=
begin
  by_cases hi : measurable_set i,
  { ext j hj,
    simp [restrict_apply _ hi hj] },
  { simp [restrict_not_measurable _ hi] }
end

/--`vector_measure.restrict` as an additive monoid homomorphism. -/
@[simps] def restrict_gm (i : set α) : vector_measure α M →+ vector_measure α M :=
{ to_fun := λ v, v.restrict i,
  map_zero' := restrict_zero,
  map_add' := λ _ _, restrict_add _ _ i }

end has_continuous_add

end

section

variables [measurable_space β]
variables {M : Type*} [add_comm_monoid M] [topological_space M]
variables {R : Type*} [semiring R] [distrib_mul_action R M]
variables [topological_space R] [has_continuous_smul R M]

@[simp] lemma map_smul {v : vector_measure α M} {f : α → β} (c : R) :
  (c • v).map f = c • v.map f :=
begin
  by_cases hf : measurable f,
  { ext i hi,
    simp [map_apply _ hf hi] },
  { simp only [map, dif_neg hf],
    -- `smul_zero` does not work since we do not require `has_continuous_add`
    ext i hi, simp }
end

@[simp] lemma restrict_smul {v :vector_measure α M} {i : set α} (c : R) :
  (c • v).restrict i = c • v.restrict i :=
begin
  by_cases hi : measurable_set i,
  { ext j hj,
    simp [restrict_apply _ hi hj] },
  { simp only [restrict_not_measurable _ hi],
    -- `smul_zero` does not work since we do not require `has_continuous_add`
    ext j hj, simp }
end

end

section

variables [measurable_space β]
variables {M : Type*} [add_comm_monoid M] [topological_space M]
variables {R : Type*} [semiring R] [module R M]
variables [topological_space R] [has_continuous_smul R M] [has_continuous_add M]

/-- `vector_measure.map` as a linear map. -/
@[simps] def mapₗ (f : α → β) : vector_measure α M →ₗ[R] vector_measure β M :=
{ to_fun := λ v, v.map f,
  map_add' := λ _ _, map_add _ _ f,
  map_smul' := λ _ _, map_smul _ }

/-- `vector_measure.restrict` as an additive monoid homomorphism. -/
@[simps] def restrictₗ (i : set α) : vector_measure α M →ₗ[R] vector_measure α M :=
{ to_fun := λ v, v.restrict i,
  map_add' := λ _ _, restrict_add _ _ i,
  map_smul' := λ _ _, restrict_smul _ }

end

section

variables {M : Type*} [topological_space M] [add_comm_monoid M] [partial_order M]

/-- Vector measures over a partially ordered monoid is partially ordered.

This definition is consistent with `measure.partial_order`. -/
instance : partial_order (vector_measure α M) :=
{ le          := λ v w, ∀ i, measurable_set i → v i ≤ w i,
  le_refl     := λ v i hi, le_refl _,
  le_trans    := λ u v w h₁ h₂ i hi, le_trans (h₁ i hi) (h₂ i hi),
  le_antisymm := λ v w h₁ h₂, ext (λ i hi, le_antisymm (h₁ i hi) (h₂ i hi)) }

variables {u v w : vector_measure α M}

lemma le_iff : v ≤ w ↔ ∀ i, measurable_set i → v i ≤ w i :=
iff.rfl

lemma le_iff' : v ≤ w ↔ ∀ i, v i ≤ w i :=
begin
  refine ⟨λ h i, _, λ h i hi, h i⟩,
  by_cases hi : measurable_set i,
  { exact h i hi },
  { rw [v.not_measurable hi, w.not_measurable hi] }
end

end

localized "notation v ` ≤[`:50 i:50 `] `:0 w:50 :=
measure_theory.vector_measure.restrict v i ≤ measure_theory.vector_measure.restrict w i"
in measure_theory

section

variables {M : Type*} [topological_space M] [add_comm_monoid M] [partial_order M]
variables (v w : vector_measure α M)

lemma restrict_le_restrict_iff {i : set α} (hi : measurable_set i) :
  v ≤[i] w ↔ ∀ ⦃j⦄, measurable_set j → j ⊆ i → v j ≤ w j :=
⟨λ h j hj₁ hj₂, (restrict_eq_self v hi hj₁ hj₂) ▸ (restrict_eq_self w hi hj₁ hj₂) ▸ h j hj₁,
 λ h, le_iff.1 (λ j hj, (restrict_apply v hi hj).symm ▸ (restrict_apply w hi hj).symm ▸
   h (hj.inter hi) (set.inter_subset_right j i))⟩

lemma subset_le_of_restrict_le_restrict {i : set α}
  (hi : measurable_set i) (hi₂ : v ≤[i] w) {j : set α} (hj : j ⊆ i) :
  v j ≤ w j :=
begin
  by_cases hj₁ : measurable_set j,
  { exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj },
  { rw [v.not_measurable hj₁, w.not_measurable hj₁] },
end

lemma restrict_le_restrict_of_subset_le {i : set α}
  (h : ∀ ⦃j⦄, measurable_set j → j ⊆ i → v j ≤ w j) : v ≤[i] w :=
begin
  by_cases hi : measurable_set i,
  { exact (restrict_le_restrict_iff _ _ hi).2 h },
  { rw [restrict_not_measurable v hi, restrict_not_measurable w hi],
    exact le_refl _ },
end

lemma restrict_le_restrict_subset {i j : set α}
  (hi₁ : measurable_set i) (hi₂ : v ≤[i] w) (hij : j ⊆ i) : v ≤[j] w :=
restrict_le_restrict_of_subset_le v w (λ k hk₁ hk₂,
  subset_le_of_restrict_le_restrict v w hi₁ hi₂ (set.subset.trans hk₂ hij))

lemma le_restrict_empty : v ≤[∅] w :=
begin
  intros j hj,
  rw [restrict_empty, restrict_empty]
end

end

section

variables {M : Type*} [topological_space M] [ordered_add_comm_monoid M] [order_closed_topology M]
variables (v w : vector_measure α M) {i j : set α}

lemma restrict_le_restrict_Union {f : ℕ → set α}
  (hf₁ : ∀ n, measurable_set (f n)) (hf₂ : ∀ n, v ≤[f n] w) :
  v ≤[⋃ n, f n] w :=
begin
  refine restrict_le_restrict_of_subset_le v w (λ a ha₁ ha₂, _),
  have ha₃ : (⋃ n, a ∩ disjointed f n) = a,
  { rwa [← inter_Union, Union_disjointed, inter_eq_left_iff_subset] },
  have ha₄ : pairwise (disjoint on (λ n, a ∩ disjointed f n)),
  { exact (disjoint_disjointed _).mono (λ i j, disjoint.mono inf_le_right inf_le_right) },
  rw [← ha₃, v.of_disjoint_Union_nat _ ha₄, w.of_disjoint_Union_nat _ ha₄],
  refine tsum_le_tsum (λ n, (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) _ _) _ _,
  { exact (ha₁.inter (measurable_set.disjointed hf₁ n)) },
  { exact set.subset.trans (set.inter_subset_right _ _) (disjointed_subset _ _) },
  { refine (v.m_Union (λ n, _) _).summable,
    { exact ha₁.inter (measurable_set.disjointed hf₁ n) },
    { exact (disjoint_disjointed _).mono (λ i j, disjoint.mono inf_le_right inf_le_right) } },
  { refine (w.m_Union (λ n, _) _).summable,
    { exact ha₁.inter (measurable_set.disjointed hf₁ n) },
    { exact (disjoint_disjointed _).mono (λ i j, disjoint.mono inf_le_right inf_le_right) } },
  { intro n, exact (ha₁.inter (measurable_set.disjointed hf₁ n)) },
  { exact λ n, ha₁.inter (measurable_set.disjointed hf₁ n) }
end

lemma restrict_le_restrict_encodable_Union [encodable β] {f : β → set α}
  (hf₁ : ∀ b, measurable_set (f b)) (hf₂ : ∀ b, v ≤[f b] w) :
  v ≤[⋃ b, f b] w :=
begin
  rw ← encodable.Union_decode₂,
  refine restrict_le_restrict_Union v w _ _,
  { intro n, measurability },
  { intro n,
    cases encodable.decode₂ β n with b,
    { simp },
    { simp [hf₂ b] } }
end

lemma restrict_le_restrict_union
  (hi₁ : measurable_set i) (hi₂ : v ≤[i] w)
  (hj₁ : measurable_set j) (hj₂ : v ≤[j] w) :
  v ≤[i ∪ j] w :=
begin
  rw union_eq_Union,
  refine restrict_le_restrict_encodable_Union v w _ _,
  { measurability },
  { rintro (_ | _); simpa }
end

end

section

variables {M : Type*} [topological_space M] [ordered_add_comm_monoid M]
variables (v w : vector_measure α M) {i j : set α}

lemma nonneg_of_zero_le_restrict (hi₂ : 0 ≤[i] v) :
  0 ≤ v i :=
begin
  by_cases hi₁ : measurable_set i,
  { exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ set.subset.rfl },
  { rw v.not_measurable hi₁ },
end

lemma nonpos_of_restrict_le_zero (hi₂ : v ≤[i] 0) :
  v i ≤ 0 :=
begin
  by_cases hi₁ : measurable_set i,
  { exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ set.subset.rfl },
  { rw v.not_measurable hi₁ }
end

lemma zero_le_restrict_not_measurable (hi : ¬ measurable_set i) :
  0 ≤[i] v :=
begin
  rw [restrict_zero, restrict_not_measurable _ hi],
  exact le_refl _,
end

lemma restrict_le_zero_of_not_measurable (hi : ¬ measurable_set i) :
  v ≤[i] 0 :=
begin
  rw [restrict_zero, restrict_not_measurable _ hi],
  exact le_refl _,
end

lemma measurable_of_not_zero_le_restrict (hi : ¬ 0 ≤[i] v) : measurable_set i :=
not.imp_symm (zero_le_restrict_not_measurable _) hi

lemma measurable_of_not_restrict_le_zero (hi : ¬ v ≤[i] 0) : measurable_set i :=
not.imp_symm (restrict_le_zero_of_not_measurable _) hi

lemma zero_le_restrict_subset (hi₁ : measurable_set i) (hij : j ⊆ i) (hi₂ : 0 ≤[i] v):
  0 ≤[j] v :=
restrict_le_restrict_of_subset_le _ _
  (λ k hk₁ hk₂, (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (set.subset.trans hk₂ hij))

lemma restrict_le_zero_subset (hi₁ : measurable_set i) (hij : j ⊆ i) (hi₂ : v ≤[i] 0):
  v ≤[j] 0 :=
restrict_le_restrict_of_subset_le _ _
  (λ k hk₁ hk₂, (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (set.subset.trans hk₂ hij))

end

section

variables {M : Type*} [topological_space M] [linear_ordered_add_comm_monoid M]
variables (v w : vector_measure α M) {i j : set α}

lemma exists_pos_measure_of_not_restrict_le_zero (hi : ¬ v ≤[i] 0) :
  ∃ j : set α, measurable_set j ∧ j ⊆ i ∧ 0 < v j :=
begin
  have hi₁ : measurable_set i := measurable_of_not_restrict_le_zero _ hi,
  rw [restrict_le_restrict_iff _ _ hi₁] at hi,
  push_neg at hi,
  obtain ⟨j, hj₁, hj₂, hj⟩ := hi,
  exact ⟨j, hj₁, hj₂, hj⟩,
end

end

section

variables {M : Type*} [topological_space M] [add_comm_monoid M] [partial_order M]
  [covariant_class M M (+) (≤)] [has_continuous_add M]

instance covariant_add_le :
  covariant_class (vector_measure α M) (vector_measure α M) (+) (≤) :=
⟨λ u v w h i hi, add_le_add_left (h i hi) _⟩

end

end vector_measure

namespace signed_measure

open vector_measure

open_locale measure_theory

/-- The underlying function for `signed_measure.to_measure`. -/
def to_measure' (s : signed_measure α)
  (i : set α) (hi₁ : measurable_set i) (hi₂ : 0 ≤[i] s)
  (j : set α) (hj₁ : measurable_set j) : ℝ≥0∞ :=
@coe ℝ≥0 ℝ≥0∞ _ ⟨s.restrict i j, le_trans (by simp) (hi₂ j hj₁)⟩

/-- Given a signed measure `s` and a positive measurable set `i`, `to_measure`
provides the measure, mapping measurable sets `j` to `s (i ∩ j)`. -/
def to_measure (s : signed_measure α) (i : set α) (hi₁ : measurable_set i) (hi₂ : 0 ≤[i] s) :
  measure α :=
measure.of_measurable (s.to_measure' i hi₁ hi₂)
  (by { simp_rw [to_measure', s.restrict_apply hi₁ measurable_set.empty,
                 set.empty_inter i, s.empty], refl })
  begin
    intros f hf₁ hf₂,
    have h₁ : ∀ n, measurable_set (i ∩ f n) := λ n, hi₁.inter (hf₁ n),
    have h₂ : pairwise (disjoint on λ (n : ℕ), i ∩ f n),
    { rintro n m hnm x ⟨⟨_, hx₁⟩, _, hx₂⟩,
      exact hf₂ n m hnm ⟨hx₁, hx₂⟩ },
    simp only [to_measure', s.restrict_apply hi₁ (measurable_set.Union hf₁),
               set.inter_comm, set.inter_Union, s.of_disjoint_Union_nat h₁ h₂,
               ennreal.some_eq_coe, id.def],
    have h : ∀ n, 0 ≤ s (i ∩ f n),
    { exact λ n, s.nonneg_of_zero_le_restrict
          (s.zero_le_restrict_subset hi₁ (inter_subset_left _ _) hi₂) },
    rw [nnreal.coe_tsum_of_nonneg h, ennreal.coe_tsum],
    { refine tsum_congr (λ n, _),
      simp_rw [s.restrict_apply hi₁ (hf₁ n), set.inter_comm] },
    { exact (nnreal.summable_coe_of_nonneg h).2 (s.m_Union h₁ h₂).summable }
  end

variables (s : signed_measure α) {i j : set α}

lemma to_measure_apply (hi : 0 ≤[i] s) (hi₁ : measurable_set i) (hj₁ : measurable_set j) :
  s.to_measure i hi₁ hi j =
  @coe ℝ≥0 ℝ≥0∞ _ ⟨s (i ∩ j), nonneg_of_zero_le_restrict s
    (zero_le_restrict_subset s hi₁ (set.inter_subset_left _ _) hi)⟩ :=
by { simp_rw [to_measure, measure.of_measurable_apply _ hj₁, to_measure',
              s.restrict_apply hi₁ hj₁, set.inter_comm] }

/-- `signed_measure.to_measure` is a finite measure. -/
instance to_measure_finite (hi : 0 ≤[i] s) (hi₁ : measurable_set i) :
  finite_measure (s.to_measure i hi₁ hi) :=
{ measure_univ_lt_top :=
  begin
    rw [to_measure_apply s hi hi₁ measurable_set.univ],
    exact ennreal.coe_lt_top,
  end }

end signed_measure

end measure_theory
