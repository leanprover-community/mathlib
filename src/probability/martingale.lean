/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
import probability.notation
import probability.stopping

/-!
# Martingales

A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if every
`f i` is integrable, `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] =ᵐ[μ] f i`. On the other hand, `f : ι → α → E` is said to be a supermartingale
with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with resepct to `ℱ`
and for all `i ≤ j`, `μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. Finally, `f : ι → α → E` is said to be a
submartingale with respect to the filtration `ℱ` if `f i` is integrable, `f` is adapted with
resepct to `ℱ` and for all `i ≤ j`, `f i ≤ᵐ[μ] μ[f j | ℱ.le i]`.

The definitions of filtration and adapted can be found in `probability.stopping`.

### Definitions

* `measure_theory.martingale f ℱ μ`: `f` is a martingale with respect to filtration `ℱ` and
  measure `μ`.
* `measure_theory.supermartingale f ℱ μ`: `f` is a supermartingale with respect to
  filtration `ℱ` and measure `μ`.
* `measure_theory.submartingale f ℱ μ`: `f` is a submartingale with respect to filtration `ℱ` and
  measure `μ`.

### Results

* `measure_theory.martingale_condexp f ℱ μ`: the sequence `λ i, μ[f | ℱ i, ℱ.le i])` is a
  martingale with respect to `ℱ` and `μ`.

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {α E ι : Type*} [preorder ι]
  {m0 : measurable_space α} {μ : measure α}
  [normed_group E] [normed_space ℝ E] [complete_space E]
  {f g : ι → α → E} {ℱ : filtration ι m0} [sigma_finite_filtration μ ℱ]

/-- A family of functions `f : ι → α → E` is a martingale with respect to a filtration `ℱ` if `f`
is adapted with respect to `ℱ` and for all `i ≤ j`, `μ[f j | ℱ.le i] =ᵐ[μ] f i`. -/
def martingale (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
adapted ℱ f ∧ ∀ i j, i ≤ j → μ[f j | ℱ i, ℱ.le i] =ᵐ[μ] f i

/-- A family of integrable functions `f : ι → α → E` is a supermartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`μ[f j | ℱ.le i] ≤ᵐ[μ] f i`. -/
def supermartingale [has_le E] (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → μ[f j | ℱ i, ℱ.le i] ≤ᵐ[μ] f i) ∧ ∀ i, integrable (f i) μ

/-- A family of integrable functions `f : ι → α → E` is a submartingale with respect to a
filtration `ℱ` if `f` is adapted with respect to `ℱ` and for all `i ≤ j`,
`f i ≤ᵐ[μ] μ[f j | ℱ.le i]`. -/
def submartingale [has_le E] (f : ι → α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] : Prop :=
adapted ℱ f ∧ (∀ i j, i ≤ j → f i ≤ᵐ[μ] μ[f j | ℱ i, ℱ.le i]) ∧ ∀ i, integrable (f i) μ

variables (E)
lemma martingale_zero (ℱ : filtration ι m0) (μ : measure α) [sigma_finite_filtration μ ℱ] :
  martingale (0 : ι → α → E) ℱ μ :=
⟨adapted_zero E ℱ, λ i j hij, by { rw [pi.zero_apply, condexp_zero], simp, }⟩
variables {E}

namespace martingale

@[protected]
lemma adapted (hf : martingale f ℱ μ) : adapted ℱ f := hf.1

@[protected]
lemma strongly_measurable (hf : martingale f ℱ μ) (i : ι) : strongly_measurable[ℱ i] (f i) :=
hf.adapted i

lemma condexp_ae_eq (hf : martingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  μ[f j | ℱ i, ℱ.le i] =ᵐ[μ] f i :=
hf.2 i j hij

@[protected]
lemma integrable (hf : martingale f ℱ μ) (i : ι) : integrable (f i) μ :=
integrable_condexp.congr (hf.condexp_ae_eq (le_refl i))

lemma set_integral_eq (hf : martingale f ℱ μ) {i j : ι} (hij : i ≤ j) {s : set α}
  (hs : measurable_set[ℱ i] s) :
  ∫ x in s, f i x ∂μ = ∫ x in s, f j x ∂μ :=
begin
  rw ← @set_integral_condexp _ _ _ _ _ (ℱ i) m0 _ (ℱ.le i) _ _ _ (hf.integrable j) hs,
  refine set_integral_congr_ae (ℱ.le i s hs) _,
  filter_upwards [hf.2 i j hij] with _ heq _ using heq.symm,
end

lemma add (hf : martingale f ℱ μ) (hg : martingale g ℱ μ) : martingale (f + g) ℱ μ :=
begin
  refine ⟨hf.adapted.add hg.adapted, λ i j hij, _⟩,
  exact (condexp_add (hf.integrable j) (hg.integrable j)).trans
    ((hf.2 i j hij).add (hg.2 i j hij)),
end

lemma neg (hf : martingale f ℱ μ) : martingale (-f) ℱ μ :=
⟨hf.adapted.neg, λ i j hij, (condexp_neg (f j)).trans ((hf.2 i j hij).neg)⟩

lemma sub (hf : martingale f ℱ μ) (hg : martingale g ℱ μ) : martingale (f - g) ℱ μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg, }

lemma smul (c : ℝ) (hf : martingale f ℱ μ) : martingale (c • f) ℱ μ :=
begin
  refine ⟨hf.adapted.smul c, λ i j hij, _⟩,
  refine (condexp_smul c (f j)).trans ((hf.2 i j hij).mono (λ x hx, _)),
  rw [pi.smul_apply, hx, pi.smul_apply, pi.smul_apply],
end

lemma supermartingale [preorder E] (hf : martingale f ℱ μ) : supermartingale f ℱ μ :=
⟨hf.1, λ i j hij, (hf.2 i j hij).le, λ i, hf.integrable i⟩

lemma submartingale [preorder E] (hf : martingale f ℱ μ) : submartingale f ℱ μ :=
⟨hf.1, λ i j hij, (hf.2 i j hij).symm.le, λ i, hf.integrable i⟩

end martingale

lemma martingale_iff [partial_order E] : martingale f ℱ μ ↔
  supermartingale f ℱ μ ∧ submartingale f ℱ μ :=
⟨λ hf, ⟨hf.supermartingale, hf.submartingale⟩,
 λ ⟨hf₁, hf₂⟩, ⟨hf₁.1, λ i j hij, (hf₁.2.1 i j hij).antisymm (hf₂.2.1 i j hij)⟩⟩

lemma martingale_condexp (f : α → E) (ℱ : filtration ι m0) (μ : measure α)
  [sigma_finite_filtration μ ℱ] :
  martingale (λ i, μ[f | ℱ i, ℱ.le i]) ℱ μ :=
⟨λ i, strongly_measurable_condexp, λ i j hij, condexp_condexp_of_le (ℱ.mono hij) _⟩

namespace supermartingale

@[protected]
lemma adapted [has_le E] (hf : supermartingale f ℱ μ) : adapted ℱ f := hf.1

@[protected]
lemma strongly_measurable [has_le E] (hf : supermartingale f ℱ μ) (i : ι) :
  strongly_measurable[ℱ i] (f i) :=
hf.adapted i

@[protected]
lemma integrable [has_le E] (hf : supermartingale f ℱ μ) (i : ι) : integrable (f i) μ := hf.2.2 i

lemma condexp_ae_le [has_le E] (hf : supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  μ[f j | ℱ i, ℱ.le i] ≤ᵐ[μ] f i :=
hf.2.1 i j hij

lemma set_integral_le {f : ι → α → ℝ} (hf : supermartingale f ℱ μ)
  {i j : ι} (hij : i ≤ j) {s : set α} (hs : measurable_set[ℱ i] s) :
  ∫ x in s, f j x ∂μ ≤ ∫ x in s, f i x ∂μ :=
begin
  rw ← set_integral_condexp (ℱ.le i) (hf.integrable j) hs,
  refine set_integral_mono_ae integrable_condexp.integrable_on (hf.integrable i).integrable_on _,
  filter_upwards [hf.2.1 i j hij] with _ heq using heq,
end

lemma add [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : supermartingale g ℱ μ) : supermartingale (f + g) ℱ μ :=
begin
  refine ⟨hf.1.add hg.1, λ i j hij, _, λ i, (hf.2.2 i).add (hg.2.2 i)⟩,
  refine (condexp_add (hf.integrable j) (hg.integrable j)).le.trans _,
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij],
  intros,
  refine add_le_add _ _; assumption,
end

lemma add_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : martingale g ℱ μ) : supermartingale (f + g) ℱ μ :=
hf.add hg.supermartingale

lemma neg [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) : submartingale (-f) ℱ μ :=
begin
  refine ⟨hf.1.neg, λ i j hij, _, λ i, (hf.2.2 i).neg⟩,
  refine eventually_le.trans _ (condexp_neg (f j)).symm.le,
  filter_upwards [hf.2.1 i j hij] with _ _,
  simpa,
end

end supermartingale

namespace submartingale

@[protected]
lemma adapted [has_le E] (hf : submartingale f ℱ μ) : adapted ℱ f := hf.1

@[protected]
lemma strongly_measurable [has_le E] (hf : submartingale f ℱ μ) (i : ι) :
  strongly_measurable[ℱ i] (f i) :=
hf.adapted i

@[protected]
lemma integrable [has_le E] (hf : submartingale f ℱ μ) (i : ι) : integrable (f i) μ := hf.2.2 i

lemma ae_le_condexp [has_le E] (hf : submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  f i ≤ᵐ[μ] μ[f j | ℱ i, ℱ.le i] :=
hf.2.1 i j hij

lemma add [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) (hg : submartingale g ℱ μ) : submartingale (f + g) ℱ μ :=
begin
  refine ⟨hf.1.add hg.1, λ i j hij, _, λ i, (hf.2.2 i).add (hg.2.2 i)⟩,
  refine eventually_le.trans _ (condexp_add (hf.integrable j) (hg.integrable j)).symm.le,
  filter_upwards [hf.2.1 i j hij, hg.2.1 i j hij],
  intros,
  refine add_le_add _ _; assumption,
end

lemma add_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) (hg : martingale g ℱ μ) : submartingale (f + g) ℱ μ :=
hf.add hg.submartingale

lemma neg [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) : supermartingale (-f) ℱ μ :=
begin
  refine ⟨hf.1.neg, λ i j hij, (condexp_neg (f j)).le.trans _, λ i, (hf.2.2 i).neg⟩,
  filter_upwards [hf.2.1 i j hij] with _ _,
  simpa,
end

/-- The converse of this lemma is `measure_theory.submartingale_of_set_integral_le`. -/
lemma set_integral_le {f : ι → α → ℝ} (hf : submartingale f ℱ μ)
  {i j : ι} (hij : i ≤ j) {s : set α} (hs : measurable_set[ℱ i] s) :
  ∫ x in s, f i x ∂μ ≤ ∫ x in s, f j x ∂μ :=
begin
  rw [← neg_le_neg_iff, ← integral_neg, ← integral_neg],
  exact supermartingale.set_integral_le hf.neg hij hs,
end

lemma sub_supermartingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) (hg : supermartingale g ℱ μ) : submartingale (f - g) ℱ μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

lemma sub_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : submartingale f ℱ μ) (hg : martingale g ℱ μ) : submartingale (f - g) ℱ μ :=
hf.sub_supermartingale hg.supermartingale

end submartingale

section

lemma submartingale_of_set_integral_le [is_finite_measure μ]
  {f : ι → α → ℝ} (hadp : adapted ℱ f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i j : ι, i ≤ j → ∀ s : set α, measurable_set[ℱ i] s →
    ∫ x in s, f i x ∂μ ≤ ∫ x in s, f j x ∂μ) :
  submartingale f ℱ μ :=
begin
  refine ⟨hadp, λ i j hij, _, hint⟩,
  -- need to show `f i ≤ᵐ[μ] μ[f j|_]`. This is equivalent to `f i ≤ᵐ[μ.trim _] μ[f j|_]`
  -- since both sides are `ℱ i`-measurable
  suffices : f i ≤ᵐ[μ.trim (ℱ.le i)] μ[f j| ℱ.le i],
  { change ∀ᵐ x ∂μ, _,
    change ∀ᵐ x ∂μ.trim _, _ at this,
    rw [ae_iff] at this ⊢,
    rwa trim_measurable_set_eq at this,
    exact measurable_set.compl (@measurable_set_le _ _ _ _ _ (ℱ i) _ _ _ _ _ (hadp i).measurable
      strongly_measurable_condexp.measurable) },
  suffices : 0 ≤ᵐ[μ.trim (ℱ.le i)] μ[f j| ℱ.le i] - f i,
  { filter_upwards [this] with x hx,
    rwa ← sub_nonneg },
  refine ae_nonneg_of_forall_set_integral_nonneg_of_finite_measure
    ((integrable_condexp.sub (hint i)).trim _ (strongly_measurable_condexp.sub $ hadp i))
    (λ s hs, _),
  specialize hf i j hij s hs,
  rwa [← set_integral_trim _ (strongly_measurable_condexp.sub $ hadp i) hs,
    integral_sub' integrable_condexp.integrable_on (hint i).integrable_on, sub_nonneg,
    set_integral_condexp _ (hint j) hs],
end

end

namespace supermartingale

lemma sub_submartingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : submartingale g ℱ μ) : supermartingale (f - g) ℱ μ :=
by { rw sub_eq_add_neg, exact hf.add hg.neg }

lemma sub_martingale [preorder E] [covariant_class E E (+) (≤)]
  (hf : supermartingale f ℱ μ) (hg : martingale g ℱ μ) : supermartingale (f - g) ℱ μ :=
hf.sub_submartingale hg.submartingale

section

variables {F : Type*} [normed_lattice_add_comm_group F]
  [normed_space ℝ F] [complete_space F] [ordered_smul ℝ F]

lemma smul_nonneg {f : ι → α → F}
  {c : ℝ} (hc : 0 ≤ c) (hf : supermartingale f ℱ μ) :
  supermartingale (c • f) ℱ μ :=
begin
  refine ⟨hf.1.smul c, λ i j hij, _, λ i, (hf.2.2 i).smul c⟩,
  refine (condexp_smul c (f j)).le.trans _,
  filter_upwards [hf.2.1 i j hij] with _ hle,
  simp,
  exact smul_le_smul_of_nonneg hle hc,
end

lemma smul_nonpos {f : ι → α → F}
  {c : ℝ} (hc : c ≤ 0) (hf : supermartingale f ℱ μ) :
  submartingale (c • f) ℱ μ :=
begin
  rw [← neg_neg c, (by { ext i x, simp } : - -c • f = -(-c • f))],
  exact (hf.smul_nonneg $ neg_nonneg.2 hc).neg,
end

end

end supermartingale

namespace submartingale

section

variables {F : Type*} [normed_lattice_add_comm_group F]
  [normed_space ℝ F] [complete_space F] [ordered_smul ℝ F]

lemma smul_nonneg {f : ι → α → F}
  {c : ℝ} (hc : 0 ≤ c) (hf : submartingale f ℱ μ) :
  submartingale (c • f) ℱ μ :=
begin
  rw [← neg_neg c, (by { ext i x, simp } : - -c • f = -(c • -f))],
  exact supermartingale.neg (hf.neg.smul_nonneg hc),
end

lemma smul_nonpos {f : ι → α → F}
  {c : ℝ} (hc : c ≤ 0) (hf : submartingale f ℱ μ) :
  supermartingale (c • f) ℱ μ :=
begin
  rw [← neg_neg c, (by { ext i x, simp } : - -c • f = -(-c • f))],
  exact (hf.smul_nonneg $ neg_nonneg.2 hc).neg,
end

end

end submartingale

section nat

variables {𝒢 : filtration ℕ m0} [sigma_finite_filtration μ 𝒢]

namespace submartingale

lemma integrable_stopped_value [has_le E] {f : ℕ → α → E} (hf : submartingale f 𝒢 μ) {τ : α → ℕ}
  (hτ : is_stopping_time 𝒢 τ) {N : ℕ} (hbdd : ∀ x, τ x ≤ N) :
  integrable (stopped_value f τ) μ :=
integrable_stopped_value hτ hf.integrable hbdd

-- We may generalize the below lemma to functions taking value in a `normed_lattice_add_comm_group`.
-- Similarly, generalize `(super/)submartingale.set_integral_le`.

/-- Given a submartingale `f` and bounded stopping times `τ` and `π` such that `τ ≤ π`, the
expectation of `stopped_value f τ` is less than or equal to the expectation of `stopped_value f π`.
This is the forward direction of the optional stopping theorem. -/
lemma expected_stopped_value_mono {f : ℕ → α → ℝ} (hf : submartingale f 𝒢 μ) {τ π : α → ℕ}
  (hτ : is_stopping_time 𝒢 τ) (hπ : is_stopping_time 𝒢 π) (hle : τ ≤ π)
  {N : ℕ} (hbdd : ∀ x, π x ≤ N) :
  μ[stopped_value f τ] ≤ μ[stopped_value f π] :=
begin
  rw [← sub_nonneg, ← integral_sub', stopped_value_sub_eq_sum' hle hbdd],
  { simp only [finset.sum_apply],
    have : ∀ i, measurable_set[𝒢 i] {x : α | τ x ≤ i ∧ i < π x},
    { intro i,
      refine (hτ i).inter _,
      convert (hπ i).compl,
      ext x,
      simpa },
    rw integral_finset_sum,
    { refine finset.sum_nonneg (λ i hi, _),
      rw [integral_indicator (𝒢.le _ _ (this _)), integral_sub', sub_nonneg],
      { exact hf.set_integral_le (nat.le_succ i) (this _) },
      { exact (hf.integrable _).integrable_on },
      { exact (hf.integrable _).integrable_on } },
    intros i hi,
    exact integrable.indicator (integrable.sub (hf.integrable _) (hf.integrable _))
      (𝒢.le _ _ (this _)) },
  { exact hf.integrable_stopped_value hπ hbdd },
  { exact hf.integrable_stopped_value hτ (λ x, le_trans (hle x) (hbdd x)) }
end

end submartingale

-- We now prove the converse of the optional stopping theorem

section indicator_stopping_time

/-- Auxilliary definition for `submartingale_of_expected_stopped_value_mono`.  -/
def indicator_stopping_time (i j : ℕ) (s : set α) [decidable_pred (λ k, k ∈ s)] : α → ℕ :=
s.piecewise i j

variables {i j n : ℕ} {s : set α} {x : α} [decidable_pred (λ k, k ∈ s)]

lemma indicator_stopping_time_eq_iff :
  indicator_stopping_time i j s x = n ↔ (x ∈ s ∧ i = n) ∨ (x ∉ s ∧ j = n) :=
begin
  rw [indicator_stopping_time, set.piecewise],
  dsimp only,
  split_ifs; simp [h],
end

@[simp] lemma indicator_stopping_time_of_eq : indicator_stopping_time i i s x = i :=
by simp [indicator_stopping_time]

@[simp] lemma indicator_stopping_time_of_mem (hx : x ∈ s) :
  indicator_stopping_time i j s x = i :=
by simp [indicator_stopping_time_eq_iff, hx]

@[simp] lemma indicator_stopping_time_of_nmem (hx : x ∉ s) :
  indicator_stopping_time i j s x = j :=
by simp [indicator_stopping_time_eq_iff, hx]

lemma indicator_stopping_time_eq_left_iff (hij : i ≠ j) :
  indicator_stopping_time i j s x = i ↔ x ∈ s :=
begin
  simp only [indicator_stopping_time_eq_iff, eq_self_iff_true, and_true, or_iff_left_iff_imp,
    and_imp],
  exact λ hx hij_eq, absurd hij_eq.symm hij,
end

lemma indicator_stopping_time_eq_right_iff (hij : i ≠ j) :
  indicator_stopping_time i j s x = j ↔ x ∈ sᶜ :=
begin
  simp only [indicator_stopping_time_eq_iff, eq_self_iff_true, and_true, set.mem_compl_eq,
    or_iff_right_iff_imp, and_imp],
  exact λ hx hij_eq, absurd hij_eq hij,
end

lemma indicator_stopping_time_compl :
  indicator_stopping_time j i sᶜ = indicator_stopping_time i j s :=
by { ext1 x, by_cases hx : x ∈ s; simp [hx], }

lemma indicator_stopping_time_le_max : indicator_stopping_time i j s x ≤ max i j :=
by { by_cases hx : x ∈ s; simp [hx], }

@[measurability]
lemma measurable_indicator_stopping_time {m : measurable_space α} (hs : measurable_set s) :
  measurable (indicator_stopping_time i j s) :=
begin
  simp_rw [indicator_stopping_time, pi.coe_nat],
  exact measurable.piecewise hs measurable_const measurable_const,
end

lemma is_stopping_time_indicator_stopping_time (hij : i ≤ j) (hs : measurable_set[𝒢 i] s) :
  is_stopping_time 𝒢 (indicator_stopping_time i j s) :=
begin
  refine is_stopping_time_of_measurable_set_eq (λ n, _),
  by_cases hij' : i = j,
  { simp [hij'], },
  by_cases hin : i = n,
  { have hs_n : measurable_set[𝒢 n] s, by { convert hs, exact hin.symm, },
    exact measurable_indicator_stopping_time hs_n (measurable_set_singleton n), },
  by_cases hjn : j = n,
  { have hs_n : measurable_set[𝒢 n] s, by { convert 𝒢.mono hij _ hs, exact hjn.symm, },
    exact measurable_indicator_stopping_time hs_n (measurable_set_singleton n), },
  simp [indicator_stopping_time_eq_iff, hin, hjn],
end

lemma stopped_value_indicator_stopping_time {f : ℕ → α → ℝ} :
  stopped_value f (indicator_stopping_time i j s) = s.indicator (f i) + sᶜ.indicator (f j) :=
by { ext x, rw stopped_value, by_cases hx : x ∈ s; simp [hx], }

end indicator_stopping_time

/-- The converse direction of the optional stopping theorem, i.e. an adapted integrable process `f`
is a submartingale if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
lemma submartingale_of_expected_stopped_value_mono [is_finite_measure μ]
  {f : ℕ → α → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ τ π : α → ℕ, is_stopping_time 𝒢 τ → is_stopping_time 𝒢 π → τ ≤ π → (∃ N, ∀ x, π x ≤ N) →
    μ[stopped_value f τ] ≤ μ[stopped_value f π]) :
  submartingale f 𝒢 μ :=
begin
  refine submartingale_of_set_integral_le hadp hint (λ i j hij s hs, _),
  classical,
  specialize hf (indicator_stopping_time i j s) _
      (is_stopping_time_indicator_stopping_time hij hs)
      (is_stopping_time_const j) (λ x, indicator_stopping_time_le_max.trans (max_eq_right hij).le)
      ⟨j, λ x, le_rfl⟩,
  rwa [stopped_value_const, stopped_value_indicator_stopping_time,
    integral_add' ((hint i).indicator (𝒢.le _ _ hs)) ((hint j).indicator (𝒢.le _ _ hs.compl)),
    integral_indicator (𝒢.le _ _ hs), integral_indicator (𝒢.le _ _ hs.compl),
    ← integral_add_compl (𝒢.le _ _ hs) (hint j), add_le_add_iff_right] at hf,
end

/-- **The optional stopping theorem** (fair game theorem): an adapted integrable process `f`
is a submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`. -/
lemma submartingale_iff_expected_stopped_value_mono [is_finite_measure μ]
  {f : ℕ → α → ℝ} (hadp : adapted 𝒢 f) (hint : ∀ i, integrable (f i) μ) :
  submartingale f 𝒢 μ ↔
  ∀ τ π : α → ℕ, is_stopping_time 𝒢 τ → is_stopping_time 𝒢 π → τ ≤ π → (∃ N, ∀ x, π x ≤ N) →
    μ[stopped_value f τ] ≤ μ[stopped_value f π] :=
⟨λ hf _ _ hτ hπ hle ⟨N, hN⟩, hf.expected_stopped_value_mono hτ hπ hle hN,
 submartingale_of_expected_stopped_value_mono hadp hint⟩

end nat

end measure_theory
