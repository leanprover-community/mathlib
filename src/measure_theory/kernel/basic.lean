/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.constructions.prod

/-!
# Markov Kernels

A kernel from a measurable space `α` to another measurable space `β` is a measurable map
`α → measure β`, where the measurable space instance on `measure β` is the one defined in
`measure_theory.measure.measurable_space`. That is, a kernel `κ` verifies that for all measurable
sets `s` of `β`, `λ a, κ a s` is measurable.

## Main definitions

Classes of kernels:
* `kernel α β`: kernels from `α` to `β`, defined as the `add_submonoid` of the measurable
  functions in `α → measure β`.
* `is_markov_kernel κ`: a kernel from `α` to `β` is said to be a Markov kernel if for all `a : α`,
  `k a` is a probability measure.
* `is_finite_kernel κ`: a kernel from `α` to `β` is said to be finite if there exists `C : ℝ≥0∞`
  such that `C < ∞` and for all `a : α`, `κ a univ ≤ C`. This implies in particular that all
  measures in the image of `κ` are finite, but is stronger since it requires an uniform bound. This
  stronger condition is necessary to ensure that the composition of two finite kernels is finite.
* `is_s_finite_kernel κ`: a kernel is called s-finite if it is a countable sum of finite kernels.

Kernels built from other kernels:
* `comp (κ : kernel α β) (η : kernel (α × β) γ) : kernel α (β × γ)`: composition of
  two s-finite kernels.
  `∫⁻ bc, f bc.1 bc.2 ∂(comp κ η a) = ∫⁻ b, ∫⁻ c, f b c ∂(η (a, b)) ∂(κ a)`
* `map (κ : kernel α β) (f : β → γ) (hf : measurable f) : kernel α mγ`
  `∫⁻ b, g b ∂(map κ f hf a) = ∫⁻ a, g (f a) ∂κ a`
* `comap (κ : kernel α β) (f : γ → α) (hf : measurable f) : kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`
* `comp2 (η : kernel β γ) (κ : kernel α β) : kernel α γ`: another composition, special case
  of the first one. TODO name, obviously. We define a notation `η ∘ₖ κ = comp2 η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`

## Main statements

* `ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable functions `f`, then the
  two kernels `κ` and `η` are equal.

* `measurable_lintegral`: the function `λ a, ∫⁻ b, f a b ∂(κ a)` is measurable, for an s-finite
  kernel `κ : kernel α β` and a function `f : α → β → ℝ≥0∞` such that `function.uncurry f`
  is measurable.

* `lintegral_comp`: `∫⁻ bc, f bc.1 bc.2 ∂(comp κ η a) = ∫⁻ b, ∫⁻ c, f b c ∂(η (a, b)) ∂(κ a)`.
* `is_finite_kernel.comp`
* `is_s_finite_kernel.comp`

-/

open measure_theory

open_locale measure_theory ennreal big_operators

namespace measure_theory

-- TODO move
instance measure.has_measurable_add₂ {α : Type*} {m : measurable_space α} :
  has_measurable_add₂ (measure α) :=
begin
  refine ⟨measure.measurable_of_measurable_coe _ (λ s hs, _)⟩,
  simp_rw [measure.coe_add, pi.add_apply],
  refine measurable.add _ _,
  { exact (measure.measurable_coe hs).comp measurable_fst, },
  { exact (measure.measurable_coe hs).comp measurable_snd, },
end

-- TODO move
lemma lintegral_indicator_const {α : Type*} {mα : measurable_space α} {μ : measure α}
  {s : set α} (hs : measurable_set s) (c : ℝ≥0∞) :
  ∫⁻ a, s.indicator (λ _, c) a ∂μ = c * μ s :=
by rw [lintegral_indicator _ hs, set_lintegral_const]

-- TODO move
lemma lintegral_indicator_const_comp {α β : Type*} {mα : measurable_space α} {μ : measure α}
  {mβ : measurable_space β}
  {f : α → β} {s : set β} (hf : measurable f) (hs : measurable_set s) (c : ℝ≥0∞) :
  ∫⁻ a, s.indicator (λ _, c) (f a) ∂μ = c * μ (f ⁻¹' s) :=
by rw [lintegral_comp (measurable_const.indicator hs) hf, lintegral_indicator_const hs,
  measure.map_apply hf hs]

-- TODO move
lemma measure.sum_comm {α ι : Type*} {mα : measurable_space α} (μ : ι → ι → measure α) :
  measure.sum (λ n, measure.sum (μ n)) = measure.sum (λ m, measure.sum (λ n, μ n m)) :=
by { ext1 s hs, simp_rw [measure.sum_apply _ hs], rw ennreal.tsum_comm, }

/-- A kernel from a measurable space `α` to another measurable space `β` is a measurable function
`κ : α → measure β`. The measurable space structure on `measure β` is given by
`measure_theory.measure.measurable_space`. A map `κ : α → measure β` is measurable iff
`∀ s : set β, measurable_set s → measurable (λ a, κ a s)`. -/
def kernel (α β : Type*) [measurable_space α] [measurable_space β] :
  add_submonoid (α → measure β) :=
{ carrier := measurable,
  zero_mem' := measurable_zero,
  add_mem' := λ f g hf hg, measurable.add hf hg, }

variables {α β ι : Type*} [measurable_space α] [measurable_space β]

instance : has_coe_to_fun (kernel α β) (λ _, α → measure β) := ⟨λ κ, κ.val⟩

namespace kernel

@[simp] lemma coe_fn_zero : ⇑(0 : kernel α β) = 0 := rfl
@[simp] lemma coe_fn_add (κ η : kernel α β) : ⇑(κ + η) = κ + η := rfl

/-- Coercion to a function as an additive monoid homomorphism. -/
def coe_add_hom (α β : Type*) [measurable_space α] [measurable_space β] :
  kernel α β →+ (α → measure β) :=
⟨coe_fn, coe_fn_zero, coe_fn_add⟩

@[simp] lemma zero_apply (a : α) : (0 : kernel α β) a = 0 := rfl

@[simp] lemma coe_finset_sum (I : finset ι) (κ : ι → kernel α β) :
  ⇑(∑ i in I, κ i) = ∑ i in I, κ i :=
(coe_add_hom α β).map_sum _ _

lemma finset_sum_apply (I : finset ι) (κ : ι → kernel α β) (a : α) :
  (∑ i in I, κ i) a = ∑ i in I, κ i a :=
by rw [coe_finset_sum, finset.sum_apply]

lemma finset_sum_apply' (I : finset ι) (κ : ι → kernel α β) (a : α) (s : set β) :
  (∑ i in I, κ i) a s = ∑ i in I, κ i a s :=
by rw [finset_sum_apply, measure.finset_sum_apply]

end kernel

/-- A kernel is a Markov kernel if every measure in its image is a probability measure. -/
class is_markov_kernel (κ : kernel α β) : Prop :=
(is_probability_measure : ∀ a, is_probability_measure (κ a))

/-- A kernel is finite if every measure in its image is finite, with a uniform bound. -/
class is_finite_kernel (κ : kernel α β) : Prop :=
(exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a set.univ ≤ C)

/-- A constant `C : ℝ≥0∞` such that `C < ∞` (`is_finite_kernel.bound_lt_top κ`) and for all
`a : α` and `s : set β`, `κ a s ≤ C` (`measure_le_bound κ a s`). -/
noncomputable
def is_finite_kernel.bound (κ : kernel α β) [h : is_finite_kernel κ] : ℝ≥0∞ :=
h.exists_univ_le.some

lemma is_finite_kernel.bound_lt_top (κ : kernel α β) [h : is_finite_kernel κ] :
  is_finite_kernel.bound κ < ∞ :=
h.exists_univ_le.some_spec.1

lemma is_finite_kernel.bound_ne_top (κ : kernel α β) [h : is_finite_kernel κ] :
  is_finite_kernel.bound κ ≠ ∞ :=
(is_finite_kernel.bound_lt_top κ).ne

lemma kernel.measure_le_bound (κ : kernel α β) [h : is_finite_kernel κ] (a : α) (s : set β) :
  κ a s ≤ is_finite_kernel.bound κ :=
(measure_mono (set.subset_univ s)).trans (h.exists_univ_le.some_spec.2 a)

instance is_finite_kernel_zero (α β : Type*) [measurable_space α] [measurable_space β] :
  is_finite_kernel (0 : kernel α β) :=
⟨⟨0, ennreal.coe_lt_top,
  λ a, by simp only [kernel.zero_apply, measure.coe_zero, pi.zero_apply, le_zero_iff]⟩⟩

instance is_finite_kernel.add (κ η : kernel α β) [is_finite_kernel κ] [is_finite_kernel η] :
  is_finite_kernel (κ + η) :=
begin
  let Cκ := is_finite_kernel.bound κ,
  let Cη := is_finite_kernel.bound η,
  refine ⟨⟨Cκ + Cη,
    ennreal.add_lt_top.mpr ⟨is_finite_kernel.bound_lt_top κ, is_finite_kernel.bound_lt_top η⟩,
    λ a, _⟩⟩,
  simp_rw [kernel.coe_fn_add, pi.add_apply, measure.coe_add, pi.add_apply],
  exact add_le_add (kernel.measure_le_bound _ _ _) (kernel.measure_le_bound _ _ _),
end

variables {κ : kernel α β}

instance is_markov_kernel.is_probability_measure' [h : is_markov_kernel κ] (a : α) :
  is_probability_measure (κ a) :=
is_markov_kernel.is_probability_measure a

instance is_finite_kernel.is_finite_measure [h : is_finite_kernel κ] (a : α) :
  is_finite_measure (κ a) :=
⟨(kernel.measure_le_bound κ a set.univ).trans_lt (is_finite_kernel.bound_lt_top κ)⟩

@[priority 100]
instance is_markov_kernel.is_finite_kernel [h : is_markov_kernel κ] : is_finite_kernel κ :=
⟨⟨1, ennreal.one_lt_top, λ a, prob_le_one⟩⟩

namespace kernel

@[ext] lemma ext {κ : kernel α β} {η : kernel α β} (h : ∀ a, κ a = η a) : κ = η :=
by { ext1, ext1 a, exact h a, }

lemma ext_fun {κ η : kernel α β} (h : ∀ a f, measurable f → ∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)) :
  κ = η :=
begin
  ext a s hs,
  specialize h a (s.indicator (λ _, 1)) (measurable.indicator measurable_const hs),
  simp_rw [lintegral_indicator_const hs, one_mul] at h,
  rw h,
end

protected lemma measurable (κ : kernel α β) : measurable κ := κ.prop

protected lemma measurable_coe (κ : kernel α β) {s : set β} (hs : measurable_set s) :
  measurable (λ a, κ a s) :=
(measure.measurable_coe hs).comp (kernel.measurable κ)

section const

/-- Constant kernel, which always returns the same measure. -/
def const (α : Type*) {β : Type*} [measurable_space α] {mβ : measurable_space β} (μβ : measure β) :
  kernel α β :=
{ val := λ _, μβ,
  property := measure.measurable_of_measurable_coe _ (λ s hs, measurable_const), }

lemma is_finite_kernel_const {μβ : measure β} [hμβ : is_finite_measure μβ] :
  is_finite_kernel (const α μβ) :=
⟨⟨μβ set.univ, measure_lt_top _ _, λ a, le_rfl⟩⟩

lemma is_markov_kernel_const {μβ : measure β} [hμβ : is_probability_measure μβ] :
  is_markov_kernel (const α μβ) :=
⟨λ a, hμβ⟩

end const

section deterministic

/-- Kernel which to `a` associates the dirac measure at `f a`. -/
noncomputable
def deterministic {f : α → β} (hf : measurable f) :
  kernel α β :=
{ val := λ a, measure.dirac (f a),
  property :=
    begin
      refine measure.measurable_of_measurable_coe _ (λ s hs, _),
      simp_rw measure.dirac_apply' _ hs,
      refine measurable.indicator _ (hf hs),
      simp only [pi.one_apply, measurable_const],
    end, }

lemma deterministic_apply {f : α → β} (hf : measurable f) (a : α) :
  deterministic hf a = measure.dirac (f a) := rfl

lemma deterministic_apply' {f : α → β} (hf : measurable f) (a : α) {s : set β}
  (hs : measurable_set s) :
  deterministic hf a s = s.indicator (λ _, 1) (f a) :=
begin
  rw [deterministic],
  change measure.dirac (f a) s = s.indicator 1 (f a),
  simp_rw measure.dirac_apply' _ hs,
end

instance is_finite_kernel.deterministic {f : α → β} (hf : measurable f) :
  is_finite_kernel (deterministic hf) :=
begin
  refine ⟨⟨1, ennreal.one_lt_top, λ a, le_of_eq _⟩⟩,
  rw [deterministic_apply' hf a measurable_set.univ, set.indicator_univ],
end

end deterministic

/-- In a countable space with measurable singletons, every function `α → measure β` defines a
kernel. -/
def of_fun_of_countable (α β : Type*) [measurable_space α] [measurable_space β]
  [countable α] [measurable_singleton_class α] (f : α → measure β) :
  kernel α β :=
{ val := f,
  property := measurable_of_countable f }

section sum

/-- Sum of an indexed family of kernels. -/
protected noncomputable
def sum [countable ι] (κ : ι → kernel α β) : kernel α β :=
{ val := λ a, measure.sum (λ n, κ n a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    simp_rw measure.sum_apply _ hs,
    exact measurable.ennreal_tsum (λ n, kernel.measurable_coe (κ n) hs),
  end, }

lemma sum_apply [countable ι] (κ : ι → kernel α β) (a : α) :
  kernel.sum κ a = measure.sum (λ n, κ n a) := rfl

lemma sum_apply' [countable ι] (κ : ι → kernel α β) (a : α) {s : set β} (hs : measurable_set s) :
  kernel.sum κ a s = ∑' n, κ n a s :=
by rw [sum_apply κ a, measure.sum_apply _ hs]

lemma sum_comm [countable ι] (κ : ι → ι → kernel α β) :
  kernel.sum (λ n, kernel.sum (κ n)) = kernel.sum (λ m, kernel.sum (λ n, κ n m)) :=
by { ext a s hs, simp_rw [sum_apply], rw measure.sum_comm, }

@[simp] lemma sum_fintype [fintype ι] (κ : ι → kernel α β) : kernel.sum κ = ∑ i, κ i :=
by { ext a s hs, simp only [sum_apply' κ a hs, finset_sum_apply' _ κ a s, tsum_fintype], }

lemma sum_add [countable ι] (κ η : ι → kernel α β) :
  kernel.sum (λ n, κ n + η n) = kernel.sum κ + kernel.sum η :=
begin
  ext a s hs,
  simp only [coe_fn_add, pi.add_apply, sum_apply, measure.sum_apply _ hs, pi.add_apply,
    measure.coe_add, tsum_add ennreal.summable ennreal.summable],
end

end sum

/-- A kernel is s-finite if it can be written as the sum of countably many finite kernels. -/
class is_s_finite_kernel (κ : kernel α β) : Prop :=
(tsum_finite : ∃ κs : ℕ → kernel α β, (∀ n, is_finite_kernel (κs n)) ∧ κ = kernel.sum κs)

@[priority 100]
instance is_finite_kernel.is_s_finite_kernel [h : is_finite_kernel κ] : is_s_finite_kernel κ :=
⟨⟨λ n, if n = 0 then κ else 0,
  λ n, by { split_ifs, exact h, apply_instance, },
  begin
    ext a s hs,
    rw kernel.sum_apply' _ _ hs,
    have : (λ i, ((ite (i = 0) κ 0) a) s) = λ i, ite (i = 0) (κ a s) 0,
    { ext1 i, split_ifs; refl, },
    rw [this, tsum_ite_eq],
  end⟩⟩

/-- A sequence of finite kernels such that `κ = kernel.sum (seq κ)`. See `is_finite_kernel_seq`
and `kernel_sum_seq`. -/
noncomputable
def seq (κ : kernel α β) [h : is_s_finite_kernel κ] :
  ℕ → kernel α β :=
h.tsum_finite.some

lemma kernel_sum_seq (κ : kernel α β) [h : is_s_finite_kernel κ] :
  kernel.sum (seq κ) = κ :=
h.tsum_finite.some_spec.2.symm

lemma measure_sum_seq (κ : kernel α β) [h : is_s_finite_kernel κ] (a : α) :
  measure.sum (λ n, seq κ n a) = κ a :=
by rw [← kernel.sum_apply, kernel_sum_seq κ]

instance is_finite_kernel_seq (κ : kernel α β) [h : is_s_finite_kernel κ] (n : ℕ) :
  is_finite_kernel (kernel.seq κ n) :=
h.tsum_finite.some_spec.1 n

instance is_s_finite_kernel.add (κ η : kernel α β) [is_s_finite_kernel κ] [is_s_finite_kernel η] :
  is_s_finite_kernel (κ + η) :=
begin
  refine ⟨⟨λ n, seq κ n + seq η n, λ n, infer_instance, _⟩⟩,
  rw [sum_add, kernel_sum_seq κ, kernel_sum_seq η],
end

lemma is_s_finite_kernel.finset_sum {κs : ι → kernel α β} (I : finset ι)
  (h : ∀ i ∈ I, is_s_finite_kernel (κs i)) :
  is_s_finite_kernel (∑ i in I, κs i) :=
begin
  unfreezingI
  { induction I using finset.induction with i I hi_nmem_I h_ind h,
    { exact classical.dec_eq ι, },
    { rw [finset.sum_empty], apply_instance, },
    { classical,
      rw finset.sum_insert hi_nmem_I,
      haveI : is_s_finite_kernel (κs i) := h i (finset.mem_insert_self _ _),
      haveI : is_s_finite_kernel (∑ (x : ι) in I, κs x),
        from h_ind (λ i hiI, h i (finset.mem_insert_of_mem hiI)),
      exact is_s_finite_kernel.add _ _, }, },
end

lemma is_s_finite_kernel_sum_of_denumerable [denumerable ι] {κs : ι → kernel α β}
  (hκs : ∀ n, is_s_finite_kernel (κs n)) :
  is_s_finite_kernel (kernel.sum κs) :=
begin
  let e : ℕ ≃ (ι × ℕ) := denumerable.equiv₂ ℕ (ι × ℕ),
  refine ⟨⟨λ n, seq (κs (e n).1) (e n).2, infer_instance, _⟩⟩,
  have hκ_eq : kernel.sum κs = kernel.sum (λ n, kernel.sum (seq (κs n))),
  { simp_rw kernel_sum_seq, },
  ext1 a,
  ext1 s hs,
  rw hκ_eq,
  simp_rw kernel.sum_apply' _ _ hs,
  change ∑' i m, seq (κs i) m a s = ∑' n, (λ im : ι × ℕ, seq (κs im.fst) im.snd a s) (e n),
  rw e.tsum_eq,
  { rw tsum_prod' ennreal.summable (λ _, ennreal.summable), },
  { apply_instance, },
end

lemma is_s_finite_kernel_sum [countable ι] {κs : ι → kernel α β}
  (hκs : ∀ n, is_s_finite_kernel (κs n)) :
  is_s_finite_kernel (kernel.sum κs) :=
begin
  casesI fintype_or_infinite ι,
  { rw sum_fintype,
    exact is_s_finite_kernel.finset_sum finset.univ (λ i _, hκs i), },
  haveI : encodable ι := encodable.of_countable ι,
  haveI : denumerable ι := denumerable.of_encodable_of_infinite ι,
  exact is_s_finite_kernel_sum_of_denumerable hκs,
end

section restrict
variables {s t : set β}

/-- Restriction of the measures in the image of a kernel to a set. -/
protected noncomputable
def restrict (κ : kernel α β) (hs : measurable_set s) : kernel α β :=
{ val := λ a, (κ a).restrict s,
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ t ht, _),
    simp_rw measure.restrict_apply ht,
    exact kernel.measurable_coe κ (ht.inter hs),
  end, }

lemma restrict_apply (κ : kernel α β) (hs : measurable_set s) (a : α) :
  kernel.restrict κ hs a = (κ a).restrict s := rfl

lemma restrict_apply' (κ : kernel α β) (hs : measurable_set s) (a : α) (ht : measurable_set t) :
  kernel.restrict κ hs a t = (κ a) (t ∩ s) :=
by rw [restrict_apply κ hs a, measure.restrict_apply ht]

lemma lintegral_restrict (κ : kernel α β) (hs : measurable_set s) (a : α) (f : β → ℝ≥0∞) :
  ∫⁻ b, f b ∂(kernel.restrict κ hs a) = ∫⁻ b in s, f b ∂(κ a) :=
by rw restrict_apply

instance is_finite_kernel.restrict (κ : kernel α β) [is_finite_kernel κ] (hs : measurable_set s) :
  is_finite_kernel (kernel.restrict κ hs) :=
begin
  refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw restrict_apply' κ hs a measurable_set.univ,
  exact measure_le_bound κ a _,
end

instance is_s_finite_kernel.restrict (κ : kernel α β) [is_s_finite_kernel κ]
  (hs : measurable_set s) :
  is_s_finite_kernel (kernel.restrict κ hs) :=
begin
  refine ⟨⟨λ n, kernel.restrict (seq κ n) hs, infer_instance, _⟩⟩,
  ext1 a,
  simp_rw [sum_apply, restrict_apply, ← measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq],
end

end restrict

section measurable_lintegral

/-- This is an auxiliary lemma for `measurable_prod_mk_mem`. -/
lemma measurable_prod_mk_mem_of_finite (κ : kernel α β) {t : set (α × β)} (ht : measurable_set t)
  (hκs : ∀ a, is_finite_measure (κ a)) :
  measurable (λ a, κ a {b | (a, b) ∈ t}) :=
begin
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  refine measurable_space.induction_on_inter generate_from_prod.symm is_pi_system_prod _ _ _ _ ht,
  { -- case `t = ∅`
    simp only [set.mem_empty_iff_false, set.set_of_false, measure_empty, measurable_const], },
  { -- case of a box: `t = t₁ ×ˢ t₂` for measurable sets `t₁` and `t₂`
    intros t' ht',
    simp only [set.mem_image2, set.mem_set_of_eq, exists_and_distrib_left] at ht',
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht',
    simp only [set.prod_mk_mem_set_prod_eq],
    classical,
    have h_eq_ite : (λ a, κ a {b : β | a ∈ t₁ ∧ b ∈ t₂}) = λ a, ite (a ∈ t₁) (κ a t₂) 0,
    { ext1 a,
      split_ifs,
      { simp only [h, true_and], refl, },
      { simp only [h, false_and, set.set_of_false, set.inter_empty, measure_empty], }, },
    rw h_eq_ite,
    exact measurable.ite ht₁ (kernel.measurable_coe κ ht₂) measurable_const },
  { -- we assume that the result is true for `t` and we prove it for `tᶜ`
    intros t' ht' h_meas,
    have h_eq_sdiff : ∀ a, {b : β | (a, b) ∈ t'ᶜ} = set.univ \ {b : β | (a, b) ∈ t'},
    { intro a,
      ext1 b,
      simp only [set.mem_compl_iff, set.mem_set_of_eq, set.mem_diff, set.mem_univ, true_and], },
    simp_rw h_eq_sdiff,
    have : (λ a, κ a (set.univ \ {b : β | (a, b) ∈ t'}))
      = (λ a, (κ a set.univ - κ a {b : β | (a, b) ∈ t'})),
    { ext1 a,
      rw [← set.diff_inter_self_eq_diff, set.inter_univ, measure_diff],
      { exact set.subset_univ _, },
      { exact (@measurable_prod_mk_left α β _ _ a) t' ht', },
      { exact measure_ne_top _ _, }, },
    rw this,
    exact measurable.sub (kernel.measurable_coe κ measurable_set.univ) h_meas, },
  { -- we assume that the result is true for a family of disjoint sets and prove it for their union
    intros f h_disj hf_meas hf,
    have h_Union : (λ a, κ a {b : β | (a, b) ∈ ⋃ i, f i}) = λ a, κ a (⋃ i, {b : β | (a, b) ∈ f i}),
    { ext1 a,
      congr' with b,
      simp only [set.mem_Union, set.supr_eq_Union, set.mem_set_of_eq],
      refl, },
    rw h_Union,
    have h_tsum : (λ a, κ a (⋃ i, {b : β | (a, b) ∈ f i})) = λ a, ∑' i, κ a {b : β | (a, b) ∈ f i},
    { ext1 a,
      rw measure_Union,
      { exact λ i j hij b hb, h_disj i j hij hb, },
      { exact λ i, (@measurable_prod_mk_left α β _ _ a) _ (hf_meas i), }, },
    rw h_tsum,
    exact measurable.ennreal_tsum hf, },
end

lemma measurable_prod_mk_mem (κ : kernel α β) [is_s_finite_kernel κ]
  {t : set (α × β)} (ht : measurable_set t) :
  measurable (λ a, κ a {b | (a, b) ∈ t}) :=
begin
  rw ← kernel_sum_seq κ,
  have : ∀ a, kernel.sum (seq κ) a {b : β | (a, b) ∈ t} = ∑' n, seq κ n a {b : β | (a, b) ∈ t},
    from λ a, kernel.sum_apply' _ _ (measurable_prod_mk_left ht),
  simp_rw this,
  refine measurable.ennreal_tsum (λ n, _),
  exact measurable_prod_mk_mem_of_finite (seq κ n) ht infer_instance,
end

lemma measurable_lintegral_indicator_const (κ : kernel α β) [is_s_finite_kernel κ]
  {t : set (α × β)} (ht : measurable_set t) (c : ℝ≥0∞) :
  measurable (λ a, ∫⁻ b, t.indicator (function.const (α × β) c) (a, b) ∂κ a) :=
begin
  simp_rw lintegral_indicator_const_comp measurable_prod_mk_left ht _,
  exact measurable.const_mul (measurable_prod_mk_mem _ ht) c,
end

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is measurable when seen as a
map from `α × β` (hypothesis `measurable (function.uncurry f)`), the integral
`a ↦ ∫⁻ b, f a b ∂κ a` is measurable. -/
theorem measurable_lintegral (κ : kernel α β) [is_s_finite_kernel κ]
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) :
  measurable (λ a, ∫⁻ b, f a b ∂κ a) :=
begin
  have h := simple_func.supr_eapprox_apply (function.uncurry f) hf,
  simp only [prod.forall, function.uncurry_apply_pair] at h,
  simp_rw ← h,
  have : ∀ a, ∫⁻ b, (⨆ n, (simple_func.eapprox (function.uncurry f) n) (a, b)) ∂κ a
    = ⨆ n, ∫⁻ b, (simple_func.eapprox (function.uncurry f) n) (a, b) ∂κ a,
  { intro a,
    rw lintegral_supr,
    { exact λ n, (simple_func.eapprox (function.uncurry f) n).measurable.comp
        measurable_prod_mk_left, },
    { exact λ i j hij b, simple_func.monotone_eapprox (function.uncurry f) hij _, }, },
  simp_rw this,
  refine measurable_supr (λ n, _),
  refine simple_func.induction _ _ (simple_func.eapprox (function.uncurry f) n),
  { intros c t ht,
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, set.piecewise_eq_indicator],
    exact measurable_lintegral_indicator_const κ ht c, },
  { intros g₁ g₂ h_disj hm₁ hm₂,
    simp only [simple_func.coe_add, pi.add_apply],
    have h_add : (λ a, ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a)
      = (λ a, ∫⁻ b, g₁ (a, b) ∂κ a) + (λ a, ∫⁻ b, g₂ (a, b) ∂κ a),
    { ext1 a,
      rw [pi.add_apply, lintegral_add_left],
      exact g₁.measurable.comp measurable_prod_mk_left, },
    rw h_add,
    exact measurable.add hm₁ hm₂, },
end

lemma measurable_set_lintegral (κ : kernel α β) [is_s_finite_kernel κ]
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) {s : set β} (hs : measurable_set s) :
  measurable (λ a, ∫⁻ b in s, f a b ∂κ a) :=
by { simp_rw ← lintegral_restrict κ hs, exact measurable_lintegral _ _ hf }

end measurable_lintegral

section with_density
variables {f : α → β → ℝ≥0∞}

/-- Kernel with image `(κ a).with_density (f a)`. It verifies
`∫⁻ b, g b ∂(with_density κ f hf a) = ∫⁻ b, f a b * g b ∂(κ a)`. -/
noncomputable
def with_density (κ : kernel α β) [is_s_finite_kernel κ]
  (f : α → β → ℝ≥0∞) (hf : measurable (function.uncurry f)) :
  kernel α β :=
{ val := λ a, (κ a).with_density (f a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    have : (λ a, (κ a).with_density (f a) s) = (λ a, ∫⁻ b in s, f a b ∂κ a),
    { ext1 a, exact with_density_apply (f a) hs, },
    rw this,
    exact measurable_set_lintegral κ f hf hs,
  end, }

protected lemma with_density_apply (κ : kernel α β) [is_s_finite_kernel κ]
  (hf : measurable (function.uncurry f)) (a : α) :
  with_density κ f hf a = (κ a).with_density (f a) := rfl

lemma with_density_apply' (κ : kernel α β) [is_s_finite_kernel κ]
  (hf : measurable (function.uncurry f)) (a : α) {s : set β} (hs : measurable_set s) :
  with_density κ f hf a s = ∫⁻ b in s, f a b ∂(κ a) :=
by rw [kernel.with_density_apply, with_density_apply _ hs]

lemma lintegral_with_density (κ : kernel α β) [is_s_finite_kernel κ]
  (hf : measurable (function.uncurry f)) (a : α) {g : β → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ b, g b ∂(with_density κ f hf a) = ∫⁻ b, f a b * g b ∂(κ a) :=
begin
  rw [kernel.with_density_apply,
    lintegral_with_density_eq_lintegral_mul _ (measurable.of_uncurry_left hf) hg],
  simp_rw pi.mul_apply,
end

end with_density

section composition

/-!
### Composition of kernels
 -/

variables {γ : Type*} [measurable_space γ]

/-- Auxiliary function for the definition of the composition of two kernels. `comp_fun` is a
countably additive function with value zero on the empty set, and the composition of kernels is
defined in `kernel.comp` through `measure.of_measurable`. -/
noncomputable
def comp_fun (κ : kernel α β) (η : kernel (α × β) γ) (a : α) (s : set (β × γ)) : ℝ≥0∞ :=
∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a

lemma comp_fun_empty (κ : kernel α β) (η : kernel (α × β) γ) (a : α) :
  comp_fun κ η a ∅ = 0 :=
by simp only [comp_fun, set.mem_empty_iff_false, set.set_of_false, measure_empty, lintegral_const,
  zero_mul]

lemma comp_fun_Union (κ : kernel α β) (η : kernel (α × β) γ) [is_s_finite_kernel η] (a : α)
  (f : ℕ → set (β × γ)) (hf_meas : ∀ i, measurable_set (f i)) (hf_disj : pairwise (disjoint on f)) :
  comp_fun κ η a (⋃ i, f i) = ∑' i, comp_fun κ η a (f i) :=
begin
  have h_Union : (λ b, η (a, b) {c : γ | (b, c) ∈ ⋃ i, f i})
    = λ b, η (a,b) (⋃ i, {c : γ | (b, c) ∈ f i}),
  { ext b,
    congr' with c,
    simp only [set.mem_Union, set.supr_eq_Union, set.mem_set_of_eq],
    refl, },
  rw [comp_fun, h_Union],
  have h_tsum : (λ b, η (a, b) (⋃ i, {c : γ | (b, c) ∈ f i}))
    = λ b, ∑' i, η (a, b) {c : γ | (b, c) ∈ f i},
  { ext1 b,
    rw measure_Union,
    { intros i j hij c hc,
      simp only [set.inf_eq_inter, set.mem_inter_iff, set.mem_set_of_eq] at hc,
      specialize hf_disj i j hij hc,
      simpa using hf_disj, },
    { exact λ i, (@measurable_prod_mk_left β γ _ _ b) _ (hf_meas i), }, },
  rw [h_tsum, lintegral_tsum],
  { refl, },
  intros i,
  have hm : measurable_set {p : (α × β) × γ | (p.1.2, p.2) ∈ f i},
    from (measurable_fst.snd.prod_mk measurable_snd) (hf_meas i),
  exact (measurable_prod_mk_mem η hm).comp measurable_prod_mk_left,
end

lemma comp_fun_tsum_right (κ : kernel α β) (η : kernel (α × β) γ) [is_s_finite_kernel η]
  (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp_fun κ η a s = ∑' n, comp_fun κ (seq η n) a s :=
begin
  simp_rw [comp_fun, (measure_sum_seq η _).symm],
  have : ∫⁻ (b : β), ⇑(measure.sum (λ n, seq η n (a, b))) {c : γ | (b, c) ∈ s} ∂κ a
    = ∫⁻ (b : β), ∑' n, seq η n (a, b) {c : γ | (b, c) ∈ s} ∂κ a,
  { congr',
    ext1 b,
    rw measure.sum_apply,
    exact measurable_prod_mk_left hs, },
  rw [this, lintegral_tsum (λ n : ℕ, _)],
  exact (measurable_prod_mk_mem (seq η n) ((measurable_fst.snd.prod_mk measurable_snd) hs)).comp
    measurable_prod_mk_left,
end

lemma comp_fun_tsum_left (κ : kernel α β) (η : kernel (α × β) γ) [is_s_finite_kernel κ]
  (a : α) (s : set (β × γ)) :
  comp_fun κ η a s = ∑' n, comp_fun (seq κ n) η a s :=
by simp_rw [comp_fun, (measure_sum_seq κ _).symm, lintegral_sum_measure]

lemma comp_fun_eq_tsum (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η]
  (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp_fun κ η a s = ∑' n m, comp_fun (seq κ n) (seq η m) a s :=
by simp_rw [comp_fun_tsum_left κ η a s, comp_fun_tsum_right _ η a hs]

/-- Auxiliary lemma for `measurable_comp_fun`. -/
lemma measurable_comp_fun_of_finite (κ : kernel α β) [is_finite_kernel κ]
  (η : kernel (α × β) γ) [is_finite_kernel η] {s : set (β × γ)} (hs : measurable_set s) :
  measurable (λ a, comp_fun κ η a s) :=
begin
  simp only [comp_fun],
  have h_meas : measurable (function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})),
  { have : function.uncurry (λ a b, η (a, b) {c : γ | (b, c) ∈ s})
      = λ p, η p {c : γ | (p.2, c) ∈ s},
    { ext1 p,
      have hp_eq_mk : p = (p.fst, p.snd) := prod.mk.eta.symm,
      rw [hp_eq_mk, function.uncurry_apply_pair], },
    rw this,
    exact measurable_prod_mk_mem η (measurable_fst.snd.prod_mk measurable_snd hs), },
  exact measurable_lintegral κ (λ a b, η (a, b) {c : γ | (b, c) ∈ s}) h_meas,
end

lemma measurable_comp_fun (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] {s : set (β × γ)} (hs : measurable_set s) :
  measurable (λ a, comp_fun κ η a s) :=
begin
  simp_rw comp_fun_tsum_right κ η _ hs,
  refine measurable.ennreal_tsum (λ n, _),
  simp only [comp_fun],
  have h_meas : measurable (function.uncurry (λ a b, seq η n (a, b) {c : γ | (b, c) ∈ s})),
  { have : function.uncurry (λ a b, seq η n (a, b) {c : γ | (b, c) ∈ s})
      = λ p, seq η n p {c : γ | (p.2, c) ∈ s},
    { ext1 p,
      have hp_eq_mk : p = (p.fst, p.snd) := prod.mk.eta.symm,
      rw [hp_eq_mk, function.uncurry_apply_pair], },
    rw this,
    exact measurable_prod_mk_mem (seq η n) (measurable_fst.snd.prod_mk measurable_snd hs), },
  exact measurable_lintegral κ (λ a b, seq η n (a, b) {c : γ | (b, c) ∈ s}) h_meas,
end

/-- Composition of kernels.
`kernel α β → kernel (α × β) γ → kernel α (β × γ)`.
It verifies `∫⁻ bc, f bc.1 bc.2 ∂(comp κ η a) = ∫⁻ b, ∫⁻ c, f b c ∂(η (a, b)) ∂(κ a)` (see
`lintegral_comp`). -/
noncomputable
def comp (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  kernel α (β × γ) :=
{ val := λ a, measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
    (comp_fun_Union κ η a),
  property :=
  begin
    refine measure.measurable_of_measurable_coe _ (λ s hs, _),
    have : (λ a, measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
        (comp_fun_Union κ η a) s) = λ a, comp_fun κ η a s,
    { ext1 a, rwa measure.of_measurable_apply, },
    rw this,
    exact measurable_comp_fun κ η hs,
  end, }

lemma comp_apply_eq_comp_fun (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp κ η a s = comp_fun κ η a s :=
begin
  rw [comp],
  change measure.of_measurable (λ s hs, comp_fun κ η a s) (comp_fun_empty κ η a)
    (comp_fun_Union κ η a) s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a,
  rw measure.of_measurable_apply _ hs,
  refl,
end

lemma comp_apply (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp κ η a s = ∫⁻ b, η (a, b) {c | (b, c) ∈ s} ∂κ a :=
comp_apply_eq_comp_fun κ η a hs

/-- Integral against the composition of two kernels. -/
theorem lintegral_comp (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) {f : β → γ → ℝ≥0∞} (hf : measurable (function.uncurry f)) :
  ∫⁻ bc, f bc.1 bc.2 ∂(comp κ η a) = ∫⁻ b, ∫⁻ c, f b c ∂(η (a, b)) ∂(κ a) :=
begin
  have h := simple_func.supr_eapprox_apply (function.uncurry f) hf,
  simp only [prod.forall, function.uncurry_apply_pair] at h,
  simp_rw [← h, prod.mk.eta],
  have h_mono : monotone (λ (n : ℕ) (a : β × γ), simple_func.eapprox (function.uncurry f) n a),
    from λ i j hij b, simple_func.monotone_eapprox (function.uncurry f) hij _,
  rw lintegral_supr (λ n, (simple_func.eapprox (function.uncurry f) n).measurable) h_mono,
  have : ∀ b, ∫⁻ c, (⨆ n, simple_func.eapprox (function.uncurry f) n (b, c)) ∂η (a, b)
    = ⨆ n, ∫⁻ c, simple_func.eapprox (function.uncurry f) n (b, c) ∂η (a, b),
  { intro a,
    rw lintegral_supr,
    { exact λ n, (simple_func.eapprox (function.uncurry f) n).measurable.comp
        measurable_prod_mk_left, },
    { exact λ i j hij b, h_mono hij _, }, },
  simp_rw this,
  have h_some_meas_integral : ∀ f' : simple_func (β × γ) ℝ≥0∞,
    measurable (λ b, ∫⁻ c, f' (b, c) ∂η (a, b)),
  { intros f',
    have : (λ b, ∫⁻ c, f' (b, c) ∂η (a, b)) = (λ ab, ∫⁻ c, f' (ab.2, c) ∂η (ab)) ∘ (λ b, (a, b)),
      { ext1 ab, refl, },
      rw this,
      refine measurable.comp _ measurable_prod_mk_left,
      refine (measurable_lintegral η _
        ((simple_func.measurable _).comp (measurable_fst.snd.prod_mk measurable_snd))), },
  rw lintegral_supr,
  rotate,
  { exact λ n, h_some_meas_integral (simple_func.eapprox (function.uncurry f) n), },
  { exact λ i j hij b, lintegral_mono (λ c, h_mono hij _), },
  congr,
  ext1 n,
  refine simple_func.induction _ _ (simple_func.eapprox (function.uncurry f) n),
  { intros c s hs,
    simp only [simple_func.const_zero, simple_func.coe_piecewise, simple_func.coe_const,
      simple_func.coe_zero, set.piecewise_eq_indicator, lintegral_indicator_const hs],
    rw [comp_apply κ η _ hs, ← lintegral_const_mul c _],
    swap, { exact (measurable_prod_mk_mem η ((measurable_fst.snd.prod_mk measurable_snd) hs)).comp
      measurable_prod_mk_left, },
    congr,
    ext1 b,
    classical,
    rw lintegral_indicator_const_comp measurable_prod_mk_left hs,
    refl, },
  { intros f f' h_disj hf_eq hf'_eq,
    simp_rw [simple_func.coe_add, pi.add_apply],
    change ∫⁻ x : β × γ, ((f : (β × γ) → ℝ≥0∞) x + f' x) ∂(comp κ η a)
      = ∫⁻ b, ∫⁻ (c : γ), f (b, c) + f' (b, c) ∂η (a, b) ∂κ a,
    rw [lintegral_add_left (simple_func.measurable _), hf_eq, hf'_eq, ← lintegral_add_left],
    swap, { exact h_some_meas_integral f, },
    congr' with b,
    rw ← lintegral_add_left ((simple_func.measurable _).comp measurable_prod_mk_left), },
end

lemma comp_eq_tsum_comp (κ : kernel α β) [is_s_finite_kernel κ] (η : kernel (α × β) γ)
  [is_s_finite_kernel η] (a : α) {s : set (β × γ)} (hs : measurable_set s) :
  comp κ η a s = ∑' (n m : ℕ), comp (seq κ n) (seq η m) a s :=
by { simp_rw comp_apply_eq_comp_fun _ _ _ hs, exact comp_fun_eq_tsum κ η a hs, }

lemma comp_eq_sum_comp (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  comp κ η = kernel.sum (λ n, kernel.sum (λ m, comp (seq κ n) (seq η m))) :=
by { ext a s hs, simp_rw [kernel.sum_apply' _ a hs], rw comp_eq_tsum_comp κ η a hs, }

lemma comp_eq_sum_comp_left (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  comp κ η = kernel.sum (λ n, comp (seq κ n) η) :=
begin
  rw comp_eq_sum_comp,
  congr' with n a s hs,
  simp_rw [kernel.sum_apply' _ _ hs, comp_apply_eq_comp_fun _ _ _ hs, comp_fun_tsum_right _ η a hs],
end

lemma comp_eq_sum_comp_right (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  comp κ η = kernel.sum (λ n, comp κ (seq η n)) :=
by { rw comp_eq_sum_comp, simp_rw comp_eq_sum_comp_left κ _, rw kernel.sum_comm, }

instance is_markov_kernel.comp (κ : kernel α β) [is_markov_kernel κ]
  (η : kernel (α × β) γ) [is_markov_kernel η] :
  is_markov_kernel (comp κ η) :=
⟨λ a, ⟨
begin
  rw comp_apply κ η a measurable_set.univ,
  simp only [set.mem_univ, set.set_of_true, measure_univ, lintegral_one],
end⟩⟩

lemma comp_apply_univ_le (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_finite_kernel η] (a : α) :
  comp κ η a set.univ ≤ (κ a set.univ) * (is_finite_kernel.bound η) :=
begin
  rw comp_apply κ η a measurable_set.univ,
  simp only [set.mem_univ, set.set_of_true],
  let Cη := is_finite_kernel.bound η,
  calc ∫⁻ b, η (a, b) set.univ ∂κ a
      ≤ ∫⁻ b, Cη ∂κ a : lintegral_mono (λ b, measure_le_bound η (a, b) set.univ)
  ... = Cη * κ a set.univ : lintegral_const Cη
  ... = κ a set.univ * Cη : mul_comm _ _,
end

instance is_finite_kernel.comp (κ : kernel α β) [is_finite_kernel κ]
  (η : kernel (α × β) γ) [is_finite_kernel η] :
  is_finite_kernel (comp κ η) :=
⟨⟨is_finite_kernel.bound κ * is_finite_kernel.bound η,
  ennreal.mul_lt_top (is_finite_kernel.bound_ne_top κ) (is_finite_kernel.bound_ne_top η),
  λ a, calc comp κ η a set.univ
    ≤ (κ a set.univ) * is_finite_kernel.bound η : comp_apply_univ_le κ η a
... ≤ is_finite_kernel.bound κ * is_finite_kernel.bound η :
        ennreal.mul_le_mul (measure_le_bound κ a set.univ) le_rfl, ⟩⟩

instance is_s_finite_kernel.comp (κ : kernel α β) [is_s_finite_kernel κ]
  (η : kernel (α × β) γ) [is_s_finite_kernel η] :
  is_s_finite_kernel (comp κ η) :=
begin
  rw comp_eq_sum_comp,
  exact kernel.is_s_finite_kernel_sum (λ n, kernel.is_s_finite_kernel_sum infer_instance),
end

end composition

section map_comap
/-! ### map, comap and composition -/

variables {γ : Type*} [measurable_space γ] {f : β → γ} {g : γ → α}

/-- The pushforward of a kernel along a measurable function. -/
noncomputable
def map (κ : kernel α β) (f : β → γ) (hf : measurable f) : kernel α γ :=
{ val := λ a, (κ a).map f,
  property := (measure.measurable_map _ hf).comp (kernel.measurable κ) }

lemma map_apply (κ : kernel α β) (hf : measurable f) (a : α) :
  map κ f hf a = (κ a).map f := rfl

lemma map_apply' (κ : kernel α β) (hf : measurable f) (a : α) {s : set γ} (hs : measurable_set s) :
  map κ f hf a s = κ a (f ⁻¹' s) :=
by rw [map_apply, measure.map_apply hf hs]

lemma lintegral_map (κ : kernel α β) (hf : measurable f) (a : α)
  {g' : γ → ℝ≥0∞} (hg : measurable g') :
  ∫⁻ b, g' b ∂(map κ f hf a) = ∫⁻ a, g' (f a) ∂κ a :=
by rw [map_apply _ hf, lintegral_map hg hf]

instance is_markov_kernel.map (κ : kernel α β) [is_markov_kernel κ] (hf : measurable f) :
  is_markov_kernel (map κ f hf) :=
 ⟨λ a, ⟨by rw [map_apply' κ hf a measurable_set.univ, set.preimage_univ, measure_univ]⟩⟩

instance is_finite_kernel.map (κ : kernel α β) [is_finite_kernel κ] (hf : measurable f) :
  is_finite_kernel (map κ f hf) :=
begin
  refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw map_apply' κ hf a measurable_set.univ,
  exact measure_le_bound κ a _,
end

instance is_s_finite_kernel.map (κ : kernel α β) [is_s_finite_kernel κ] (hf : measurable f) :
  is_s_finite_kernel (map κ f hf) :=
begin
  refine ⟨⟨λ n, map (seq κ n) f hf, infer_instance, _⟩⟩,
  ext a s hs,
  rw [kernel.sum_apply, map_apply' κ hf a hs, measure.sum_apply _ hs, ← measure_sum_seq κ,
    measure.sum_apply _ (hf hs)],
  simp_rw map_apply' _ hf _ hs,
end

/-- Pullback of a kernel. If `g` is measurable, then for each set s we have
`comap κ g hg c s = κ (g c) s`. -/
def comap (κ : kernel α β) (g : γ → α) (hg : measurable g) : kernel γ β :=
{ val := λ a, κ (g a),
  property := (kernel.measurable κ).comp hg }

lemma comap_apply (κ : kernel α β) (hg : measurable g) (c : γ) (s : set β) :
  comap κ g hg c s = κ (g c) s := rfl

lemma lintegral_comap (κ : kernel α β) (hg : measurable g) (c : γ) (g' : β → ℝ≥0∞) :
  ∫⁻ b, g' b ∂(comap κ g hg c) = ∫⁻ b, g' b ∂(κ (g c)) := rfl

instance is_markov_kernel.comap (κ : kernel α β) [is_markov_kernel κ] (hg : measurable g) :
  is_markov_kernel (comap κ g hg) :=
⟨λ a, ⟨by rw [comap_apply κ hg a set.univ, measure_univ]⟩⟩

instance is_finite_kernel.comap (κ : kernel α β) [is_finite_kernel κ] (hg : measurable g) :
  is_finite_kernel (comap κ g hg) :=
begin
  refine ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, λ a, _⟩⟩,
  rw comap_apply κ hg a set.univ,
  exact measure_le_bound κ _ _,
end

instance is_s_finite_kernel.comap (κ : kernel α β) [is_s_finite_kernel κ] (hg : measurable g) :
  is_s_finite_kernel (comap κ g hg) :=
begin
  refine ⟨⟨λ n, comap (seq κ n) g hg, infer_instance, _⟩⟩,
  ext a s hs,
  rw [kernel.sum_apply, comap_apply κ hg a s, measure.sum_apply _ hs, ← measure_sum_seq κ,
    measure.sum_apply _ hs],
  simp_rw comap_apply _ hg _ s,
end

/-- Define a `kernel (γ × α) β` from a `kernel α β` by taking the comap of the projection. -/
def prod_mk_left (κ : kernel α β) (γ : Type*) [measurable_space γ] : kernel (γ × α) β :=
comap κ prod.snd measurable_snd

lemma prod_mk_left_apply (κ : kernel α β) (ca : γ × α) (s : set β) :
  prod_mk_left κ γ ca s = (κ ca.snd) s :=
by rw [prod_mk_left, comap_apply _ _ _ s]

lemma lintegral_prod_mk_left (κ : kernel α β) (ca : γ × α) (g : β → ℝ≥0∞) :
  ∫⁻ b, g b ∂(prod_mk_left κ γ ca) = ∫⁻ b, g b ∂κ ca.snd := rfl

instance is_markov_kernel.prod_mk_left (κ : kernel α β) [is_markov_kernel κ] :
  is_markov_kernel (prod_mk_left κ γ) :=
by { rw prod_mk_left, apply_instance, }

instance is_finite_kernel.prod_mk_left (κ : kernel α β) [is_finite_kernel κ] :
  is_finite_kernel (prod_mk_left κ γ) :=
by { rw prod_mk_left, apply_instance, }

instance is_s_finite_kernel.prod_mk_left (κ : kernel α β) [is_s_finite_kernel κ] :
  is_s_finite_kernel (prod_mk_left κ γ) :=
by { rw prod_mk_left, apply_instance, }

/-- Define a `kernel α γ` from a `kernel α (β × γ)` by taking the map of the projection. -/
noncomputable
def snd_right (κ : kernel α (β × γ)) : kernel α γ :=
map κ prod.snd measurable_snd

lemma snd_right_apply (κ : kernel α (β × γ)) (a : α) {s : set γ} (hs : measurable_set s) :
  snd_right κ a s = κ a {p | p.2 ∈ s} :=
by { rw [snd_right, map_apply' _ _ _ hs], refl, }

lemma lintegral_snd_right (κ : kernel α (β × γ)) (a : α) {g : γ → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂(snd_right κ a) = ∫⁻ (bc : β × γ), g bc.snd ∂(κ a) :=
by rw [snd_right, lintegral_map _ measurable_snd a hg]

lemma snd_right_univ (κ : kernel α (β × γ)) (a : α) :
  snd_right κ a set.univ = κ a set.univ :=
snd_right_apply _ _ measurable_set.univ

instance is_markov_kernel.snd_right (κ : kernel α (β × γ)) [is_markov_kernel κ] :
  is_markov_kernel (snd_right κ) :=
by { rw snd_right, apply_instance, }

instance is_finite_kernel.snd_right (κ : kernel α (β × γ)) [is_finite_kernel κ] :
  is_finite_kernel (snd_right κ) :=
by { rw snd_right, apply_instance, }

instance is_s_finite_kernel.snd_right (κ : kernel α (β × γ)) [is_s_finite_kernel κ] :
  is_s_finite_kernel (snd_right κ) :=
by { rw snd_right, apply_instance, }

/-- Composition of two s-finite kernels. -/
noncomputable
def comp2 (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ] :
  kernel α γ :=
snd_right (comp κ (prod_mk_left η α))

localized "notation (name := kernel.comp2) η ` ∘ₖ `:90 κ := comp2 η κ" in measure_theory

lemma comp2_apply (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ]
  (a : α) {s : set γ} (hs : measurable_set s) :
  (η ∘ₖ κ) a s = ∫⁻ b, η b s ∂κ a :=
begin
  rw [comp2, snd_right_apply _ _ hs, comp_apply],
  swap, { exact measurable_snd hs, },
  simp only [set.mem_set_of_eq, set.set_of_mem_eq],
  simp_rw prod_mk_left_apply _ _ s,
end

lemma lintegral_comp2 (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ]
  (a : α) {g : γ → ℝ≥0∞} (hg : measurable g) :
  ∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a) :=
begin
  rw [comp2, lintegral_snd_right _ _ hg],
  change ∫⁻ (bc : β × γ), (λ a b, g b) bc.fst bc.snd ∂(comp κ (prod_mk_left η _)) a
    = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂κ a,
  exact lintegral_comp _ _ _ (hg.comp measurable_snd),
end

instance is_markov_kernel.comp2 (η : kernel β γ) [is_markov_kernel η]
  (κ : kernel α β) [is_markov_kernel κ] :
  is_markov_kernel (η ∘ₖ κ) :=
by { rw comp2, apply_instance, }

instance is_finite_kernel.comp2 (η : kernel β γ) [is_finite_kernel η]
  (κ : kernel α β) [is_finite_kernel κ] :
  is_finite_kernel (η ∘ₖ κ) :=
by { rw comp2, apply_instance, }

instance is_s_finite_kernel.comp2 (η : kernel β γ) [is_s_finite_kernel η]
  (κ : kernel α β) [is_s_finite_kernel κ] :
  is_s_finite_kernel (η ∘ₖ κ) :=
by { rw comp2, apply_instance, }

lemma comp2_assoc {δ : Type*} {mδ : measurable_space δ} (ξ : kernel γ δ) [is_s_finite_kernel ξ]
  (η : kernel β γ) [is_s_finite_kernel η] (κ : kernel α β) [is_s_finite_kernel κ] :
  ((ξ ∘ₖ η) ∘ₖ κ) = ξ ∘ₖ η ∘ₖ κ :=
begin
  refine ext_fun (λ a f hf, _),
  simp_rw lintegral_comp2 _ _ _ hf,
  have h_meas : measurable (λ b, ∫⁻ d, f d ∂(ξ b)),
    from measurable_lintegral ξ _ (hf.comp measurable_snd),
  rw lintegral_comp2 _ _ _ h_meas,
end

lemma comp2_deterministic_left_eq_map (hf : measurable f) (κ : kernel α β) [is_s_finite_kernel κ] :
  (deterministic hf ∘ₖ κ) = map κ f hf :=
begin
  ext a s hs,
  simp_rw [map_apply' _ _ _ hs, comp2_apply _ _ _ hs, deterministic_apply' hf _ hs,
    lintegral_indicator_const_comp hf hs, one_mul],
end

lemma comp2_deterministic_right_eq_comap
  (κ : kernel α β) [is_s_finite_kernel κ] (hg : measurable g) :
  (κ ∘ₖ deterministic hg) = comap κ g hg :=
begin
  ext a s hs,
  simp_rw [comap_apply _ _ _ s, comp2_apply _ _ _ hs, deterministic_apply hg a,
    lintegral_dirac' _ (kernel.measurable_coe κ hs)],
end

end map_comap

end kernel

end measure_theory
