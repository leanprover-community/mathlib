/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.hitting_time
import probability.martingale

/-!

# Doob's upcrossing estimate

Given a discrete real-valued submartingale $(f_n)_{n \in \mathbb{N}}$, denoting $U_N(a, b)$ the
number of times $f_n$ crossed from below $a$ to above $b$ before time $N$, Doob's upcrossing
estimate (also known as Doob's inequality) states that
$$(b - a) \mathbb{E}[U_N(a, b)] \le \mathbb{E}[(f_N - a)^+].$$
Doob's upcrossing estimate is an important inequality and is central in proving the martingale
convergence theorems.

## Main definitions

* `measure_theory.upper_crossing_time a b f N n`: is the stopping time corresponding to `f`
  crossing above `b` the `n`-th time before time `N` (if this does not occur then the value is
  taken to be `N`).
* `measure_theory.lower_crossing_time a b f N n`: is the stopping time corresponding to `f`
  crossing below `a` the `n`-th time before time `N` (if this does not occur then the value is
  taken to be `N`).
* `measure_theory.upcrossing_strat a b f N`: is the predictable process which is 1 if `n` is
  between a consecutive pair of lower and upper crossing and is 0 otherwise. Intuitively
  one might think of the `upcrossing_strat` as the strategy of buying 1 share whenever the process
  crosses below `a` for the first time after selling and selling 1 share whenever the process
  crosses above `b` for the first time after buying.
* `measure_theory.upcrossings_before a b f N`: is the number of times `f` crosses from below `a` to
  above `b` before time `N`.
* `measure_theory.upcrossings a b f`: is the number of times `f` crosses from below `a` to above
  `b`. This takes value in `ℝ≥0∞` and so is allowed to be `∞`.

## Main results

* `measure_theory.adapted.is_stopping_time_upper_crossing_time`: `upper_crossing_time` is a
  stopping time whenever the process it is associated to is adapted.
* `measure_theory.adapted.is_stopping_time_lower_crossing_time`: `lower_crossing_time` is a
  stopping time whenever the process it is associated to is adapted.
* `measure_theory.submartingale.mul_integral_upcrossings_before_le_integral_pos_part`: Doob's
  upcrossing estimate.
* `measure_theory.submartingale.mul_lintegral_upcrossing_le_lintegral_pos_part`: the inequality
  obtained by taking the supremum on both sides of Doob's upcrossing estimate.

### References

We mostly follow the proof from [Kallenberg, *Foundations of modern probability*][kallenberg2021]

-/

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators topological_space

namespace measure_theory

variables {α ι : Type*} {m0 : measurable_space α} {μ : measure α}

/-!

## Proof outline

In this section, we will denote $U_N(a, b)$ the number of upcrossings of $(f_n)$ from below $a$ to
above $b$ before time $N$.

To define $U_N(a, b)$, we will construct two stopping times corresponding to when $(f_n)$ crosses
below $a$ and above $b$. Namely, we define
$$
  \sigma_n := \inf \{n \ge \tau_n \mid f_n \le a\} \wedge N;
$$
$$
  \tau_{n + 1} := \inf \{n \ge \sigma_n \mid f_n \ge b\} \wedge N.
$$
These are `lower_crossing_time` and `upper_crossing_time` in our formalization which are defined
using `measure_theory.hitting` allowing us to specify a starting and ending time.
Then, we may simply define $U_N(a, b) := \sup \{n \mid \tau_n < N\}$.

Fixing $a < b \in \mathbb{R}$, we will first prove the theorem in the special case that
$0 \le f_0$ and $a \le f_N$. In particular, we will show
$$
  (b - a) \mathbb{E}[U_N(a, b)] \le \mathbb{E}[f_N].
$$
This is `measure_theory.integral_mul_upcrossing_le_integral` in our formalization.

To prove this, we use the fact that given a non-negative, bounded, predictable process $(C_n)$
(i.e. $(C_{n + 1})$ is adapted), $(C \bullet f)_n := \sum_{k \le n} C_{k + 1}(f_{k + 1} - f_k)$ is
a submartingale if $(f_n)$ is.

Define $C_n := \sum_{k \le n} \mathbf{1}_{[\sigma_k, \tau_{k + 1})}(n)$. It is easy to see that
$(1 - C_n)$ is non-negative, bounded and predictable, and hence, given a submartingale $(f_n)$,
$(1 - C) \bullet f$ is also a submartingale. Thus, by the submartingale property,
$0 \le \mathbb{E}[((1 - C) \bullet f)_0] \le \mathbb{E}[((1 - C) \bullet f)_N]$ implying
$$
  \mathbb{E}[(C \bullet f)_N] \le \mathbb{E}[(1 \bullet f)_N] = \mathbb{E}[f_N] - \mathbb{E}[f_0].
$$

Furthermore,
\begin{align}
    (C \bullet f)_N & =
      \sum_{n \le N} \sum_{k \le N} \mathbf{1}_{[\sigma_k, \tau_{k + 1})}(n)(f_{n + 1} - f_n)\\
    & = \sum_{k \le N} \sum_{n \le N} \mathbf{1}_{[\sigma_k, \tau_{k + 1})}(n)(f_{n + 1} - f_n)\\
    & = \sum_{k \le N} (f_{\sigma_k + 1} - f_{\sigma_k} + f_{\sigma_k + 2} - f_{\sigma_k + 1}
      + \cdots + f_{\tau_{k + 1}} - f_{\tau_{k + 1} - 1})\\
    & = \sum_{k \le N} (f_{\tau_{k + 1}} - f_{\sigma_k})
      \ge \sum_{k < U_N(a, b)} (b - a) = (b - a) U_N(a, b)
\end{align}
where the inequality follows since for all $k < U_N(a, b)$,
$f_{\tau_{k + 1}} - f_{\sigma_k} \ge b - a$ while for all $k > U_N(a, b)$,
$f_{\tau_{k + 1}} = f_{\sigma_k} = f_N$ and
$f_{\tau_{U_N(a, b) + 1}} - f_{\sigma_{U_N(a, b)}} = f_N - a \ge 0$. Hence, we have
$$
  (b - a) \mathbb{E}[U_N(a, b)] \le \mathbb{E}[(C \bullet f)_N]
  \le \mathbb{E}[f_N] - \mathbb{E}[f_0] \le \mathbb{E}[f_N],
$$
as required.

To obtain the general case, we simply apply the above to $((f_n - a)^+)_n$.

-/

/-- `lower_crossing_time_aux a f c N` is the first time `f` reached below `a` after time `c` before
time `N`. -/
noncomputable
def lower_crossing_time_aux [preorder ι] [has_Inf ι] (a : ℝ) (f : ι → α → ℝ) (c N : ι) : α → ι :=
hitting f (set.Iic a) c N

/-- `upper_crossing_time a b f N n` is the first time before time `N`, `f` reaches
above `b` after `f` reached below `a` for the `n - 1`-th time. -/
noncomputable
def upper_crossing_time [preorder ι] [order_bot ι] [has_Inf ι]
  (a b : ℝ) (f : ι → α → ℝ) (N : ι) : ℕ → α → ι
| 0 := ⊥
| (n + 1) := λ x, hitting f (set.Ici b)
    (lower_crossing_time_aux a f (upper_crossing_time n x) N x) N x

/-- `lower_crossing_time a b f N n` is the first time before time `N`, `f` reaches
below `a` after `f` reached above `b` for the `n`-th time. -/
noncomputable
def lower_crossing_time [preorder ι] [order_bot ι] [has_Inf ι]
  (a b : ℝ) (f : ι → α → ℝ) (N : ι) (n : ℕ) : α → ι :=
λ x, hitting f (set.Iic a) (upper_crossing_time a b f N n x) N x

section

variables [preorder ι] [order_bot ι] [has_Inf ι]
variables {a b : ℝ} {f : ι → α → ℝ} {N : ι} {n m : ℕ} {x : α}

@[simp]
lemma upper_crossing_time_zero : upper_crossing_time a b f N 0 = ⊥ := rfl

@[simp]
lemma lower_crossing_time_zero : lower_crossing_time a b f N 0 = hitting f (set.Iic a) ⊥ N := rfl

lemma upper_crossing_time_succ :
  upper_crossing_time a b f N (n + 1) x =
  hitting f (set.Ici b) (lower_crossing_time_aux a f (upper_crossing_time a b f N n x) N x) N x :=
by rw upper_crossing_time

lemma upper_crossing_time_succ_eq (x : α) :
  upper_crossing_time a b f N (n + 1) x =
  hitting f (set.Ici b) (lower_crossing_time a b f N n x) N x :=
begin
  simp only [upper_crossing_time_succ],
  refl,
end

end

section conditionally_complete_linear_order_bot

variables [conditionally_complete_linear_order_bot ι]
variables {a b : ℝ} {f : ι → α → ℝ} {N : ι} {n m : ℕ} {x : α}

lemma upper_crossing_time_le : upper_crossing_time a b f N n x ≤ N :=
begin
  cases n,
  { simp only [upper_crossing_time_zero, pi.bot_apply, bot_le] },
  { simp only [upper_crossing_time_succ, hitting_le] },
end

@[simp]
lemma upper_crossing_time_zero' : upper_crossing_time a b f ⊥ n x = ⊥ :=
eq_bot_iff.2 upper_crossing_time_le

lemma lower_crossing_time_le : lower_crossing_time a b f N n x ≤ N :=
by simp only [lower_crossing_time, hitting_le x]

lemma upper_crossing_time_le_lower_crossing_time :
  upper_crossing_time a b f N n x ≤ lower_crossing_time a b f N n x :=
by simp only [lower_crossing_time, le_hitting upper_crossing_time_le x]

lemma lower_crossing_time_le_upper_crossing_time_succ :
  lower_crossing_time a b f N n x ≤ upper_crossing_time a b f N (n + 1) x :=
begin
  rw upper_crossing_time_succ,
  exact le_hitting lower_crossing_time_le x,
end

lemma lower_crossing_time_mono (hnm : n ≤ m) :
  lower_crossing_time a b f N n x ≤ lower_crossing_time a b f N m x :=
begin
  suffices : monotone (λ n, lower_crossing_time a b f N n x),
  { exact this hnm },
  exact monotone_nat_of_le_succ
    (λ n, le_trans lower_crossing_time_le_upper_crossing_time_succ
    upper_crossing_time_le_lower_crossing_time)
end

lemma upper_crossing_time_mono (hnm : n ≤ m) :
  upper_crossing_time a b f N n x ≤ upper_crossing_time a b f N m x :=
begin
  suffices : monotone (λ n, upper_crossing_time a b f N n x),
  { exact this hnm },
  exact monotone_nat_of_le_succ
    (λ n, le_trans upper_crossing_time_le_lower_crossing_time
    lower_crossing_time_le_upper_crossing_time_succ),
end

end conditionally_complete_linear_order_bot

variables {a b : ℝ} {f : ℕ → α → ℝ} {N : ℕ} {n m : ℕ} {x : α}

lemma stopped_value_lower_crossing_time (h : lower_crossing_time a b f N n x ≠ N) :
  stopped_value f (lower_crossing_time a b f N n) x ≤ a :=
begin
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hitting_le_iff_of_lt _ (lt_of_le_of_ne lower_crossing_time_le h)).1 le_rfl,
  exact stopped_value_hitting_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 lower_crossing_time_le⟩, hj₂⟩,
end

lemma stopped_value_upper_crossing_time (h : upper_crossing_time a b f N (n + 1) x ≠ N) :
  b ≤ stopped_value f (upper_crossing_time a b f N (n + 1)) x :=
begin
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hitting_le_iff_of_lt _ (lt_of_le_of_ne upper_crossing_time_le h)).1 le_rfl,
  exact stopped_value_hitting_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 (hitting_le _)⟩, hj₂⟩,
end

lemma upper_crossing_time_lt_lower_crossing_time
  (hab : a < b) (hn : lower_crossing_time a b f N (n + 1) x ≠ N) :
  upper_crossing_time a b f N (n + 1) x < lower_crossing_time a b f N (n + 1) x :=
begin
  refine lt_of_le_of_ne upper_crossing_time_le_lower_crossing_time
    (λ h, not_le.2 hab $ le_trans _ (stopped_value_lower_crossing_time hn)),
  simp only [stopped_value],
  rw ← h,
  exact stopped_value_upper_crossing_time (h.symm ▸ hn),
end

lemma lower_crossing_time_lt_upper_crossing_time
  (hab : a < b) (hn : upper_crossing_time a b f N (n + 1) x ≠ N) :
  lower_crossing_time a b f N n x < upper_crossing_time a b f N (n + 1) x :=
begin
  refine lt_of_le_of_ne lower_crossing_time_le_upper_crossing_time_succ
    (λ h, not_le.2 hab $ le_trans (stopped_value_upper_crossing_time hn) _),
  simp only [stopped_value],
  rw ← h,
  exact stopped_value_lower_crossing_time (h.symm ▸ hn),
end

lemma upper_crossing_time_lt_succ (hab : a < b) (hn : upper_crossing_time a b f N (n + 1) x ≠ N) :
  upper_crossing_time a b f N n x < upper_crossing_time a b f N (n + 1) x :=
lt_of_le_of_lt upper_crossing_time_le_lower_crossing_time
  (lower_crossing_time_lt_upper_crossing_time hab hn)

lemma lower_crossing_time_stabilize (hnm : n ≤ m) (hn : lower_crossing_time a b f N n x = N) :
  lower_crossing_time a b f N m x = N :=
le_antisymm lower_crossing_time_le (le_trans (le_of_eq hn.symm) (lower_crossing_time_mono hnm))

lemma upper_crossing_time_stabilize (hnm : n ≤ m) (hn : upper_crossing_time a b f N n x = N) :
  upper_crossing_time a b f N m x = N :=
le_antisymm upper_crossing_time_le (le_trans (le_of_eq hn.symm) (upper_crossing_time_mono hnm))

lemma lower_crossing_time_stabilize' (hnm : n ≤ m) (hn : N ≤ lower_crossing_time a b f N n x) :
  lower_crossing_time a b f N m x = N :=
lower_crossing_time_stabilize hnm (le_antisymm lower_crossing_time_le hn)

lemma upper_crossing_time_stabilize' (hnm : n ≤ m) (hn : N ≤ upper_crossing_time a b f N n x) :
  upper_crossing_time a b f N m x = N :=
upper_crossing_time_stabilize hnm (le_antisymm upper_crossing_time_le hn)

-- `upper_crossing_time_bound_eq` provides an explicit bound
lemma exists_upper_crossing_time_eq (f : ℕ → α → ℝ) (N : ℕ) (x : α) (hab : a < b) :
  ∃ n, upper_crossing_time a b f N n x = N :=
begin
  by_contra h, push_neg at h,
  have : strict_mono (λ n, upper_crossing_time a b f N n x) :=
    strict_mono_nat_of_lt_succ (λ n, upper_crossing_time_lt_succ hab (h _)),
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ :
    ∃ m (hm : m ∈ set.range (λ n, upper_crossing_time a b f N n x)), N < m :=
    ⟨upper_crossing_time a b f N (N + 1) x, ⟨N + 1, rfl⟩,
      lt_of_lt_of_le (N.lt_succ_self) (strict_mono.id_le this (N + 1))⟩,
  exact not_le.2 hk upper_crossing_time_le
end

lemma upper_crossing_time_lt_bdd_above (hab : a < b) :
  bdd_above {n | upper_crossing_time a b f N n x < N} :=
begin
  obtain ⟨k, hk⟩ := exists_upper_crossing_time_eq f N x hab,
  refine ⟨k, λ n (hn : upper_crossing_time a b f N n x < N), _⟩,
  by_contra hn',
  exact hn.ne (upper_crossing_time_stabilize (not_le.1 hn').le hk)
end

lemma upper_crossing_time_lt_nonempty (hN : 0 < N) :
  {n | upper_crossing_time a b f N n x < N}.nonempty :=
⟨0, hN⟩

lemma upper_crossing_time_bound_eq (f : ℕ → α → ℝ) (N : ℕ) (x : α) (hab : a < b) :
  upper_crossing_time a b f N N x = N :=
begin
  by_cases hN' : N < nat.find (exists_upper_crossing_time_eq f N x hab),
  { refine le_antisymm upper_crossing_time_le _,
    have hmono : strict_mono_on (λ n, upper_crossing_time a b f N n x)
      (set.Iic (nat.find (exists_upper_crossing_time_eq f N x hab)).pred),
    { refine strict_mono_on_Iic_of_lt_succ (λ m hm, upper_crossing_time_lt_succ hab _),
      rw nat.lt_pred_iff at hm,
      convert nat.find_min _ hm },
    convert strict_mono_on.Iic_id_le hmono N (nat.le_pred_of_lt hN') },
  { rw not_lt at hN',
    exact upper_crossing_time_stabilize hN'
      (nat.find_spec (exists_upper_crossing_time_eq f N x hab)) }
end

lemma upper_crossing_time_eq_of_bound_le (hab : a < b) (hn : N ≤ n) :
  upper_crossing_time a b f N n x = N :=
le_antisymm upper_crossing_time_le
  ((le_trans (upper_crossing_time_bound_eq f N x hab).symm.le (upper_crossing_time_mono hn)))

variables {ℱ : filtration ℕ m0}

lemma adapted.is_stopping_time_crossing (hf : adapted ℱ f) :
  is_stopping_time ℱ (upper_crossing_time a b f N n) ∧
  is_stopping_time ℱ (lower_crossing_time a b f N n) :=
begin
  induction n with k ih,
  { refine ⟨is_stopping_time_const _ 0, _⟩,
    simp [hitting_is_stopping_time hf measurable_set_Iic] },
  { obtain ⟨ih₁, ih₂⟩ := ih,
    have : is_stopping_time ℱ (upper_crossing_time a b f N (k + 1)),
    { intro n,
      simp_rw upper_crossing_time_succ_eq,
      exact is_stopping_time_hitting_is_stopping_time ih₂ (λ _, lower_crossing_time_le)
        measurable_set_Ici hf _ },
    refine ⟨this, _⟩,
    { intro n,
      exact is_stopping_time_hitting_is_stopping_time this (λ _, upper_crossing_time_le)
        measurable_set_Iic hf _ } }
end

lemma adapted.is_stopping_time_upper_crossing_time (hf : adapted ℱ f) :
  is_stopping_time ℱ (upper_crossing_time a b f N n) :=
hf.is_stopping_time_crossing.1

lemma adapted.is_stopping_time_lower_crossing_time (hf : adapted ℱ f) :
  is_stopping_time ℱ (lower_crossing_time a b f N n) :=
hf.is_stopping_time_crossing.2

/-- `upcrossing_strat a b f N n` is 1 if `n` is between a consecutive pair of lower and upper
crossing and is 0 otherwise. `upcrossing_strat` is shifted by one index so that it is adapted
rather than predictable. -/
noncomputable
def upcrossing_strat (a b : ℝ) (f : ℕ → α → ℝ) (N n : ℕ) (x : α) : ℝ :=
∑ k in finset.range N,
  (set.Ico (lower_crossing_time a b f N k x) (upper_crossing_time a b f N (k + 1) x)).indicator 1 n

lemma upcrossing_strat_nonneg : 0 ≤ upcrossing_strat a b f N n x :=
finset.sum_nonneg (λ i hi, set.indicator_nonneg (λ x hx, zero_le_one) _)

lemma upcrossing_strat_le_one : upcrossing_strat a b f N n x ≤ 1 :=
begin
  rw [upcrossing_strat, ← set.indicator_finset_bUnion_apply],
  { exact set.indicator_le_self' (λ _ _, zero_le_one) _ },
  { intros i hi j hj hij,
    rw set.Ico_disjoint_Ico,
    obtain (hij' | hij') := lt_or_gt_of_ne hij,
    { rw [min_eq_left ((upper_crossing_time_mono (nat.succ_le_succ hij'.le)) :
          upper_crossing_time a b f N _ x ≤ upper_crossing_time a b f N _ x),
          max_eq_right (lower_crossing_time_mono hij'.le :
          lower_crossing_time a b f N _ _ ≤ lower_crossing_time _ _ _ _ _ _)],
      refine le_trans upper_crossing_time_le_lower_crossing_time (lower_crossing_time_mono
        (nat.succ_le_of_lt hij')) },
    { rw gt_iff_lt at hij',
      rw [min_eq_right ((upper_crossing_time_mono (nat.succ_le_succ hij'.le)) :
          upper_crossing_time a b f N _ x ≤ upper_crossing_time a b f N _ x),
          max_eq_left (lower_crossing_time_mono hij'.le :
          lower_crossing_time a b f N _ _ ≤ lower_crossing_time _ _ _ _ _ _)],
      refine le_trans upper_crossing_time_le_lower_crossing_time
        (lower_crossing_time_mono (nat.succ_le_of_lt hij')) } }
end

lemma adapted.upcrossing_strat_adapted (hf : adapted ℱ f) :
  adapted ℱ (upcrossing_strat a b f N) :=
begin
  intro n,
  change strongly_measurable[ℱ n] (λ x, ∑ k in finset.range N,
    ({n | lower_crossing_time a b f N k x ≤ n} ∩
     {n | n < upper_crossing_time a b f N (k + 1) x}).indicator 1 n),
  refine finset.strongly_measurable_sum _ (λ i hi,
    strongly_measurable_const.indicator ((hf.is_stopping_time_lower_crossing_time n).inter _)),
  simp_rw ← not_le,
  exact (hf.is_stopping_time_upper_crossing_time n).compl,
end

lemma submartingale.sum_upcrossing_strat_mul [is_finite_measure μ] (hf : submartingale f ℱ μ)
  (a b : ℝ) (N : ℕ) :
  submartingale
    (λ n : ℕ, ∑ k in finset.range n, upcrossing_strat a b f N k * (f (k + 1) - f k)) ℱ μ :=
hf.sum_mul_sub hf.adapted.upcrossing_strat_adapted
  (λ _ _, upcrossing_strat_le_one) (λ _ _, upcrossing_strat_nonneg)

lemma submartingale.sum_sub_upcrossing_strat_mul [is_finite_measure μ] (hf : submartingale f ℱ μ)
  (a b : ℝ) (N : ℕ) :
  submartingale
    (λ n : ℕ, ∑ k in finset.range n, (1 - upcrossing_strat a b f N k) * (f (k + 1) - f k)) ℱ μ :=
begin
  refine hf.sum_mul_sub (λ n, (adapted_const ℱ 1 n).sub (hf.adapted.upcrossing_strat_adapted n))
    (_ : ∀ n x, (1 - upcrossing_strat a b f N n) x ≤ 1) _,
  { refine λ n x, sub_le.1 _,
    simp [upcrossing_strat_nonneg] },
  { intros n x,
    simp [upcrossing_strat_le_one] }
end

lemma submartingale.sum_mul_upcrossing_strat_le [is_finite_measure μ] (hf : submartingale f ℱ μ) :
  μ[∑ k in finset.range n, upcrossing_strat a b f N k * (f (k + 1) - f k)] ≤
  μ[f n] - μ[f 0] :=
begin
  have h₁ : (0 : ℝ) ≤
    μ[∑ k in finset.range n, (1 - upcrossing_strat a b f N k) * (f (k + 1) - f k)],
  { have := (hf.sum_sub_upcrossing_strat_mul a b N).set_integral_le (zero_le n) measurable_set.univ,
    rw [integral_univ, integral_univ] at this,
    refine le_trans _ this,
    simp only [finset.range_zero, finset.sum_empty, integral_zero'] },
  have h₂ : μ[∑ k in finset.range n, (1 - upcrossing_strat a b f N k) * (f (k + 1) - f k)] =
    μ[∑ k in finset.range n, (f (k + 1) - f k)] -
    μ[∑ k in finset.range n, upcrossing_strat a b f N k * (f (k + 1) - f k)],
  { simp only [sub_mul, one_mul, finset.sum_sub_distrib, pi.sub_apply,
      finset.sum_apply, pi.mul_apply],
    refine integral_sub (integrable.sub (integrable_finset_sum _ (λ i hi, hf.integrable _))
      (integrable_finset_sum _ (λ i hi, hf.integrable _))) _,
    convert (hf.sum_upcrossing_strat_mul a b N).integrable n,
    ext, simp },
  rw [h₂, sub_nonneg] at h₁,
  refine le_trans h₁ _,
  simp_rw [finset.sum_range_sub, integral_sub' (hf.integrable _) (hf.integrable _)],
end

/-- The number of upcrossings (strictly) before time `N`. -/
noncomputable
def upcrossings_before [preorder ι] [order_bot ι] [has_Inf ι]
  (a b : ℝ) (f : ι → α → ℝ) (N : ι) (x : α) : ℕ :=
Sup {n | upper_crossing_time a b f N n x < N}

@[simp]
lemma upcrossings_before_bot [preorder ι] [order_bot ι] [has_Inf ι]
  {a b : ℝ} {f : ι → α → ℝ} {x : α} :
  upcrossings_before a b f ⊥ x = ⊥ :=
by simp [upcrossings_before]

lemma upcrossings_before_zero :
  upcrossings_before a b f 0 x = 0 :=
by simp [upcrossings_before]

@[simp] lemma upcrossings_before_zero' :
  upcrossings_before a b f 0 = 0 :=
by { ext x, exact upcrossings_before_zero }

lemma upper_crossing_time_lt_of_le_upcrossings_before
  (hN : 0 < N) (hab : a < b) (hn : n ≤ upcrossings_before a b f N x) :
  upper_crossing_time a b f N n x < N :=
begin
  have : upper_crossing_time a b f N (upcrossings_before a b f N x) x < N :=
    (upper_crossing_time_lt_nonempty hN).cSup_mem
    ((order_bot.bdd_below _).finite_of_bdd_above (upper_crossing_time_lt_bdd_above hab)),
  exact lt_of_le_of_lt (upper_crossing_time_mono hn) this,
end

lemma upper_crossing_time_eq_of_upcrossings_before_lt
  (hab : a < b) (hn : upcrossings_before a b f N x < n) :
  upper_crossing_time a b f N n x = N :=
begin
  refine le_antisymm upper_crossing_time_le (not_lt.1 _),
  convert not_mem_of_cSup_lt hn (upper_crossing_time_lt_bdd_above hab),
end

lemma upcrossings_before_le (f : ℕ → α → ℝ) (x : α) (hN : 0 < N) (hab : a < b) :
  upcrossings_before a b f N x ≤ N :=
begin
  refine cSup_le ⟨0, hN⟩ (λ n (hn : _ < _), _),
  by_contra hnN,
  exact hn.ne (upper_crossing_time_eq_of_bound_le hab (not_le.1 hnN).le),
end

lemma crossing_eq_crossing_of_lower_crossing_time_lt {M : ℕ} (hNM : N ≤ M)
  (h : lower_crossing_time a b f N n x < N) :
  upper_crossing_time a b f M n x = upper_crossing_time a b f N n x ∧
  lower_crossing_time a b f M n x = lower_crossing_time a b f N n x :=
begin
  have h' : upper_crossing_time a b f N n x < N :=
    lt_of_le_of_lt upper_crossing_time_le_lower_crossing_time h,
  induction n with k ih,
  { simp only [nat.nat_zero_eq_zero, upper_crossing_time_zero, bot_eq_zero', eq_self_iff_true,
      lower_crossing_time_zero, true_and, eq_comm],
    refine hitting_eq_hitting_of_exists hNM _,
    simp only [lower_crossing_time, hitting_lt_iff] at h,
    obtain ⟨j, hj₁, hj₂⟩ := h,
    exact ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩ },
  { specialize ih (lt_of_le_of_lt (lower_crossing_time_mono (nat.le_succ _)) h)
      (lt_of_le_of_lt (upper_crossing_time_mono (nat.le_succ _)) h'),
    have : upper_crossing_time a b f M k.succ x = upper_crossing_time a b f N k.succ x,
    { simp only [upper_crossing_time_succ_eq, hitting_lt_iff] at h' ⊢,
      obtain ⟨j, hj₁, hj₂⟩ := h',
      rw [eq_comm, ih.2],
      exact hitting_eq_hitting_of_exists hNM ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩ },
    refine ⟨this, _⟩,
    simp only [lower_crossing_time, eq_comm, this],
    refine hitting_eq_hitting_of_exists hNM _,
    rw [lower_crossing_time, hitting_lt_iff _ le_rfl] at h,
    swap, { apply_instance },
    obtain ⟨j, hj₁, hj₂⟩ := h,
    exact ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩ }
end

lemma crossing_eq_crossing_of_upper_crossing_time_lt {M : ℕ} (hNM : N ≤ M)
  (h : upper_crossing_time a b f N (n + 1) x < N) :
  upper_crossing_time a b f M (n + 1) x = upper_crossing_time a b f N (n + 1) x ∧
  lower_crossing_time a b f M n x = lower_crossing_time a b f N n x :=
begin
  have := (crossing_eq_crossing_of_lower_crossing_time_lt hNM
    (lt_of_le_of_lt lower_crossing_time_le_upper_crossing_time_succ h)).2,
  refine ⟨_, this⟩,
  rw [upper_crossing_time_succ_eq, upper_crossing_time_succ_eq, eq_comm, this],
  refine hitting_eq_hitting_of_exists hNM _,
  simp only [upper_crossing_time_succ_eq, hitting_lt_iff] at h,
  obtain ⟨j, hj₁, hj₂⟩ := h,
  exact ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩
end

lemma upper_crossing_time_eq_upper_crossing_time_of_lt {M : ℕ} (hNM : N ≤ M)
  (h : upper_crossing_time a b f N n x < N) :
  upper_crossing_time a b f M n x = upper_crossing_time a b f N n x :=
begin
  cases n,
  { simp },
  { exact (crossing_eq_crossing_of_upper_crossing_time_lt hNM h).1 }
end

lemma upcrossings_before_mono (hab : a < b) :
  monotone (λ N x, upcrossings_before a b f N x) :=
begin
  intros N M hNM x,
  simp only [upcrossings_before],
  by_cases hemp : {n : ℕ | upper_crossing_time a b f N n x < N}.nonempty,
  { refine cSup_le_cSup (upper_crossing_time_lt_bdd_above hab) hemp (λ n hn, _),
    rw [set.mem_set_of_eq, upper_crossing_time_eq_upper_crossing_time_of_lt hNM hn],
    exact lt_of_lt_of_le hn hNM },
  { rw set.not_nonempty_iff_eq_empty at hemp,
    simp [hemp, cSup_empty, bot_eq_zero', zero_le'] }
end

lemma upcrossings_before_lt_upcrossing_of_exists_upcrossings_before (hab : a < b) {N₁ N₂ : ℕ}
  (hN₁: N ≤ N₁) (hN₁': f N₁ x < a) (hN₂: N₁ ≤ N₂) (hN₂': b < f N₂ x) :
  upcrossings_before a b f N x < upcrossings_before a b f (N₂ + 1) x :=
begin
  refine lt_of_lt_of_le (nat.lt_succ_self _) (le_cSup (upper_crossing_time_lt_bdd_above hab) _),
  rw [set.mem_set_of_eq, upper_crossing_time_succ_eq, hitting_lt_iff _ le_rfl],
  swap,
  { apply_instance },
  { refine ⟨N₂, ⟨_, nat.lt_succ_self _⟩, hN₂'.le⟩,
    rw [lower_crossing_time, hitting_le_iff_of_lt _ (nat.lt_succ_self _)],
    refine ⟨N₁, ⟨le_trans _ hN₁, hN₂⟩, hN₁'.le⟩,
    by_cases hN : 0 < N,
    { have : upper_crossing_time a b f N (upcrossings_before a b f N x) x < N :=
        nat.Sup_mem (upper_crossing_time_lt_nonempty hN) (upper_crossing_time_lt_bdd_above hab),
      rw upper_crossing_time_eq_upper_crossing_time_of_lt
        (hN₁.trans (hN₂.trans $ nat.le_succ _)) this,
      exact this.le },
    { rw [not_lt, le_zero_iff] at hN,
      rw [hN, upcrossings_before_zero, upper_crossing_time_zero],
      refl } },
end

lemma lower_crossing_time_lt_of_lt_upcrossings_before
  (hN : 0 < N) (hab : a < b) (hn : n < upcrossings_before a b f N x) :
  lower_crossing_time a b f N n x < N :=
lt_of_le_of_lt lower_crossing_time_le_upper_crossing_time_succ
  (upper_crossing_time_lt_of_le_upcrossings_before hN hab hn)

lemma le_sub_of_le_upcrossings_before
  (hN : 0 < N) (hab : a < b) (hn : n < upcrossings_before a b f N x) :
  b - a ≤
  stopped_value f (upper_crossing_time a b f N (n + 1)) x -
  stopped_value f (lower_crossing_time a b f N n) x :=
sub_le_sub (stopped_value_upper_crossing_time
  (upper_crossing_time_lt_of_le_upcrossings_before hN hab hn).ne)
  (stopped_value_lower_crossing_time (lower_crossing_time_lt_of_lt_upcrossings_before hN hab hn).ne)

lemma sub_eq_zero_of_upcrossings_before_lt (hab : a < b) (hn : upcrossings_before a b f N x < n) :
  stopped_value f (upper_crossing_time a b f N (n + 1)) x -
  stopped_value f (lower_crossing_time a b f N n) x = 0 :=
begin
  have : N ≤ upper_crossing_time a b f N n x,
  { rw upcrossings_before at hn,
    rw ← not_lt,
    exact λ h, not_le.2 hn (le_cSup (upper_crossing_time_lt_bdd_above hab) h) },
  simp [stopped_value, upper_crossing_time_stabilize' (nat.le_succ n) this,
    lower_crossing_time_stabilize' le_rfl
      (le_trans this upper_crossing_time_le_lower_crossing_time)]
end

lemma mul_upcrossings_before_le (hf : a ≤ f N x) (hN : 0 < N) (hab : a < b) :
  (b - a) * upcrossings_before a b f N x ≤
  ∑ k in finset.range N, upcrossing_strat a b f N k x * (f (k + 1) - f k) x :=
begin
  classical,
  simp_rw [upcrossing_strat, finset.sum_mul, ← set.indicator_mul_left, pi.one_apply,
    pi.sub_apply, one_mul],
  rw finset.sum_comm,
  have h₁ : ∀ k, ∑ n in finset.range N,
    (set.Ico (lower_crossing_time a b f N k x) (upper_crossing_time a b f N (k + 1) x)).indicator
    (λ m, f (m + 1) x - f m x) n =
    stopped_value f (upper_crossing_time a b f N (k + 1)) x -
    stopped_value f (lower_crossing_time a b f N k) x,
  { intro k,
    rw [finset.sum_indicator_eq_sum_filter, (_ : (finset.filter
      (λ i, i ∈ set.Ico (lower_crossing_time a b f N k x) (upper_crossing_time a b f N (k + 1) x))
      (finset.range N)) =
      finset.Ico (lower_crossing_time a b f N k x) (upper_crossing_time a b f N (k + 1) x)),
      finset.sum_Ico_eq_add_neg _ lower_crossing_time_le_upper_crossing_time_succ,
      finset.sum_range_sub (λ n, f n x), finset.sum_range_sub (λ n, f n x), neg_sub,
      sub_add_sub_cancel],
    { refl },
    { ext i,
      simp only [set.mem_Ico, finset.mem_filter, finset.mem_range, finset.mem_Ico,
        and_iff_right_iff_imp, and_imp],
      exact λ _ h, lt_of_lt_of_le h upper_crossing_time_le } },
  simp_rw [h₁],
  have h₂ : ∑ k in finset.range (upcrossings_before a b f N x), (b - a) ≤
    ∑ k in finset.range N,
    (stopped_value f (upper_crossing_time a b f N (k + 1)) x -
    stopped_value f (lower_crossing_time a b f N k) x),
  { calc ∑ k in finset.range (upcrossings_before a b f N x), (b - a)
       ≤ ∑ k in finset.range (upcrossings_before a b f N x),
          (stopped_value f (upper_crossing_time a b f N (k + 1)) x -
           stopped_value f (lower_crossing_time a b f N k) x) :
    begin
      refine finset.sum_le_sum (λ i hi, le_sub_of_le_upcrossings_before hN hab _),
      rwa finset.mem_range at hi,
    end
    ...≤ ∑ k in finset.range N,
          (stopped_value f (upper_crossing_time a b f N (k + 1)) x -
           stopped_value f (lower_crossing_time a b f N k) x) :
    begin
      refine finset.sum_le_sum_of_subset_of_nonneg
        (finset.range_subset.2 (upcrossings_before_le f x hN hab)) (λ i _ hi, _),
      by_cases hi' : i = upcrossings_before a b f N x,
      { subst hi',
        simp only [stopped_value],
        rw upper_crossing_time_eq_of_upcrossings_before_lt hab (nat.lt_succ_self _),
        by_cases heq : lower_crossing_time a b f N (upcrossings_before a b f N x) x = N,
        { rw [heq, sub_self] },
        { rw sub_nonneg,
          exact le_trans (stopped_value_lower_crossing_time heq) hf } },
      { rw sub_eq_zero_of_upcrossings_before_lt hab,
        rw [finset.mem_range, not_lt] at hi,
        exact lt_of_le_of_ne hi (ne.symm hi') },
    end },
  refine le_trans _ h₂,
  rw [finset.sum_const, finset.card_range, nsmul_eq_mul, mul_comm],
end

lemma integral_mul_upcrossings_before_le_integral [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hfN : ∀ x, a ≤ f N x) (hfzero : 0 ≤ f 0) (hN : 0 < N) (hab : a < b) :
  (b - a) * μ[upcrossings_before a b f N] ≤ μ[f N] :=
calc (b - a) * μ[upcrossings_before a b f N]
     ≤ μ[∑ k in finset.range N, upcrossing_strat a b f N k * (f (k + 1) - f k)] :
begin
  rw ← integral_mul_left,
  refine integral_mono_of_nonneg _ ((hf.sum_upcrossing_strat_mul a b N).integrable N) _,
  { exact eventually_of_forall (λ x, mul_nonneg (sub_nonneg.2 hab.le) (nat.cast_nonneg _)) },
  { refine eventually_of_forall (λ x, _),
    simpa using mul_upcrossings_before_le (hfN x) hN hab },
end
  ...≤ μ[f N] - μ[f 0] : hf.sum_mul_upcrossing_strat_le
  ...≤ μ[f N] : (sub_le_self_iff _).2 (integral_nonneg hfzero)

lemma crossing_pos_eq (hab : a < b) :
  upper_crossing_time 0 (b - a) (λ n x, (f n x - a)⁺) N n = upper_crossing_time a b f N n ∧
  lower_crossing_time 0 (b - a) (λ n x, (f n x - a)⁺) N n = lower_crossing_time a b f N n :=
begin
  have hab' : 0 < b - a := sub_pos.2 hab,
  have hf : ∀ x i, b - a ≤ (f i x - a)⁺ ↔ b ≤ f i x,
  { intros i x,
    refine ⟨λ h, _, λ h, _⟩,
    { rwa [← sub_le_sub_iff_right a,
        ← lattice_ordered_comm_group.pos_of_pos_pos (lt_of_lt_of_le hab' h)] },
    { rw ← sub_le_sub_iff_right a at h,
      rwa lattice_ordered_comm_group.pos_of_nonneg _ (le_trans hab'.le h) } },
  have hf' : ∀ x i, (f i x - a)⁺ ≤ 0 ↔ f i x ≤ a,
  { intros x i,
    rw [lattice_ordered_comm_group.pos_nonpos_iff, sub_nonpos] },
  induction n with k ih,
  { refine ⟨rfl, _⟩,
    simp only [lower_crossing_time_zero, hitting, set.mem_Icc, set.mem_Iic],
    ext x,
    split_ifs with h₁ h₂ h₂,
    { simp_rw [hf'] },
    { simp_rw [set.mem_Iic, ← hf' _ _] at h₂,
      exact false.elim (h₂ h₁) },
    { simp_rw [set.mem_Iic, hf' _ _] at h₁,
      exact false.elim (h₁ h₂) },
    { refl } },
  { have : upper_crossing_time 0 (b - a) (λ n x, (f n x - a)⁺) N (k + 1) =
      upper_crossing_time a b f N (k + 1),
    { ext x,
      simp only [upper_crossing_time_succ_eq, ← ih.2, hitting, set.mem_Ici, tsub_le_iff_right],
      split_ifs with h₁ h₂ h₂,
      { simp_rw [← sub_le_iff_le_add, hf x] },
      { simp_rw [set.mem_Ici, ← hf _ _] at h₂,
        exact false.elim (h₂ h₁) },
      { simp_rw [set.mem_Ici, hf _ _] at h₁,
        exact false.elim (h₁ h₂) },
      { refl } },
    refine ⟨this, _⟩,
    ext x,
    simp only [lower_crossing_time, this, hitting, set.mem_Iic],
    split_ifs with h₁ h₂ h₂,
    { simp_rw [hf' x] },
    { simp_rw [set.mem_Iic, ← hf' _ _] at h₂,
      exact false.elim (h₂ h₁) },
    { simp_rw [set.mem_Iic, hf' _ _] at h₁,
      exact false.elim (h₁ h₂) },
    { refl } }
end

lemma upcrossings_before_pos_eq (hab : a < b) :
  upcrossings_before 0 (b - a) (λ n x, (f n x - a)⁺) N x = upcrossings_before a b f N x :=
by simp_rw [upcrossings_before, (crossing_pos_eq hab).1]

private lemma mul_integral_upcrossings_before_le_integral_pos_part'' [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hN : 0 < N) (hab : a < b) :
  (b - a) * μ[upcrossings_before a b f N] ≤ μ[λ x, (f N x - a)⁺] :=
begin
  refine le_trans (le_of_eq _) (integral_mul_upcrossings_before_le_integral
    (hf.sub_martingale (martingale_const _ _ _)).pos
    (λ x, lattice_ordered_comm_group.pos_nonneg _)
    (λ x, lattice_ordered_comm_group.pos_nonneg _) hN (sub_pos.2 hab)),
  simp_rw [sub_zero, ← upcrossings_before_pos_eq hab],
  refl,
end

private lemma mul_integral_upcrossings_before_le_integral_pos_part' [is_finite_measure μ]
  (hf : submartingale f ℱ μ) (hab : a < b) :
  (b - a) * μ[upcrossings_before a b f N] ≤ μ[λ x, (f N x - a)⁺] :=
begin
  by_cases hN : N = 0,
  { subst hN,
    simp_rw [← bot_eq_zero, upcrossings_before_bot, bot_eq_zero, integral_const,
      algebra.id.smul_eq_mul, nat.cast_zero, mul_zero],
    exact integral_nonneg (λ x, lattice_ordered_comm_group.pos_nonneg _) },
  { exact mul_integral_upcrossings_before_le_integral_pos_part'' hf (zero_lt_iff.2 hN) hab }
end

/-- **Doob's upcrossing estimate**: given a real valued discrete submartingale `f` and real
values `a` and `b`, we have `(b - a) * 𝔼[upcrossings_before a b f N] ≤ 𝔼[(f N - a)⁺]` where
`upcrossings_before a b f N` is the number of times the process `f` crossed from below `a` to above
`b` before the time `N`. -/
lemma submartingale.mul_integral_upcrossings_before_le_integral_pos_part [is_finite_measure μ]
  (a b : ℝ) (hf : submartingale f ℱ μ) (N : ℕ) :
  (b - a) * μ[upcrossings_before a b f N] ≤ μ[λ x, (f N x - a)⁺] :=
begin
  by_cases hab : a < b,
  { exact mul_integral_upcrossings_before_le_integral_pos_part' hf hab },
  { rw [not_lt, ← sub_nonpos] at hab,
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (integral_nonneg (λ x, nat.cast_nonneg _)))
      (integral_nonneg (λ x, lattice_ordered_comm_group.pos_nonneg _)) }
end

lemma upcrossings_before_eq_sum (hN : 0 < N) (hab : a < b) :
  upcrossings_before a b f N x =
  ∑ i in finset.Ico 1 (N + 1), {n | upper_crossing_time a b f N n x < N}.indicator 1 i :=
begin
  rw ← finset.sum_Ico_consecutive _ (nat.succ_le_succ zero_le')
    (nat.succ_le_succ (upcrossings_before_le f x hN hab)),
  have h₁ : ∀ k ∈ finset.Ico 1 (upcrossings_before a b f N x + 1),
    {n : ℕ | upper_crossing_time a b f N n x < N}.indicator 1 k = 1,
  { rintro k hk,
    rw finset.mem_Ico at hk,
    rw set.indicator_of_mem,
    { refl },
    { refine upper_crossing_time_lt_of_le_upcrossings_before hN hab (nat.lt_succ_iff.1 hk.2) } },
  have h₂ : ∀ k ∈ finset.Ico (upcrossings_before a b f N x + 1) (N + 1),
    {n : ℕ | upper_crossing_time a b f N n x < N}.indicator 1 k = 0,
  { rintro k hk,
    rw [finset.mem_Ico, nat.succ_le_iff] at hk,
    rw set.indicator_of_not_mem,
    simp only [set.mem_set_of_eq, not_lt],
    exact (upper_crossing_time_eq_of_upcrossings_before_lt hab hk.1).symm.le },
  rw [finset.sum_congr rfl h₁, finset.sum_congr rfl h₂, finset.sum_const, finset.sum_const,
    smul_eq_mul, mul_one, smul_eq_mul, mul_zero, nat.card_Ico, nat.add_succ_sub_one,
    add_zero, add_zero],
end

lemma adapted.measurable_upcrossings_before (hf : adapted ℱ f) (hab : a < b) :
  measurable (upcrossings_before a b f N) :=
begin
  by_cases hN : N = 0,
  { rw [hN, upcrossings_before_zero'],
    exact measurable_zero },
  { have : upcrossings_before a b f N =
      λ x, ∑ i in finset.Ico 1 (N + 1), {n | upper_crossing_time a b f N n x < N}.indicator 1 i,
    { ext x,
      exact upcrossings_before_eq_sum (zero_lt_iff.2 hN) hab },
    rw this,
    exact finset.measurable_sum _ (λ i hi, measurable.indicator measurable_const $
      ℱ.le N _ (hf.is_stopping_time_upper_crossing_time.measurable_set_lt_of_pred N)) },
end

lemma adapted.integrable_upcrossings_before [is_finite_measure μ]
  (hf : adapted ℱ f) (hab : a < b) :
  integrable (λ x, (upcrossings_before a b f N x : ℝ)) μ :=
begin
  by_cases hN : N = 0,
  { rw [hN, upcrossings_before_zero'],
    simp only [pi.zero_apply, nat.cast_zero, integrable_zero] },
  { have h₁ : upcrossings_before a b f N =
      λ x, ∑ i in finset.Ico 1 (N + 1), {n | upper_crossing_time a b f N n x < N}.indicator 1 i,
    { ext x,
      exact upcrossings_before_eq_sum (zero_lt_iff.2 hN) hab },
    rw h₁,
    simp only [nat.cast_sum],
    refine integrable_finset_sum _ (λ i hi, _),
    have h₂ : ∀ x, (({n | upper_crossing_time a b f N n x < N}.indicator 1 i : ℕ) : ℝ) =
      {x | upper_crossing_time a b f N i x < N}.indicator 1 x,
    { intro x,
      by_cases i ∈ {n : ℕ | upper_crossing_time a b f N n x < N},
      { rw [set.indicator_of_mem h, set.indicator_of_mem, pi.one_apply, pi.one_apply, nat.cast_one],
        exact h },
      { rw [set.indicator_of_not_mem h, set.indicator_of_not_mem, nat.cast_zero],
        exact h } },
    simp_rw [h₂],
    rw [integrable_indicator_iff (ℱ.le N _
      (hf.is_stopping_time_upper_crossing_time.measurable_set_lt_of_pred N)),
      pi.one_def, integrable_on_const],
    exact or.inr (measure_lt_top _ _) },
end

/-- The number of upcrossings of a realization of a stochastic process (`upcrossing` takes value
in `ℝ≥0∞` and so is allowed to be `∞`). -/
noncomputable def upcrossings [preorder ι] [order_bot ι] [has_Inf ι]
  (a b : ℝ) (f : ι → α → ℝ) (x : α) : ℝ≥0∞ :=
⨆ N, (upcrossings_before a b f N x : ℝ≥0∞)

lemma adapted.measurable_upcrossings (hf : adapted ℱ f) (hab : a < b) :
  measurable (upcrossings a b f) :=
measurable_supr (λ N, measurable_from_top.comp (hf.measurable_upcrossings_before hab))

lemma upcrossings_lt_top_iff :
  upcrossings a b f x < ∞ ↔ ∃ k, ∀ N, upcrossings_before a b f N x ≤ k :=
begin
  have : upcrossings a b f x < ⊤ ↔ ∃ k : ℝ≥0, upcrossings a b f x ≤ k,
  { split,
    { intro h,
      lift upcrossings a b f x to ℝ≥0 using h.ne with r hr,
      exact ⟨r, le_rfl⟩ },
    { rintro ⟨k, hk⟩,
      exact lt_of_le_of_lt hk ennreal.coe_lt_top } },
  simp_rw [this, upcrossings, supr_le_iff],
  split; rintro ⟨k, hk⟩,
  { obtain ⟨m, hm⟩ := exists_nat_ge k,
    refine ⟨m, λ N, ennreal.coe_nat_le_coe_nat.1 ((hk N).trans _)⟩,
    rwa [← ennreal.coe_nat, ennreal.coe_le_coe] },
  { refine ⟨k, λ N, _⟩,
    simp only [ennreal.coe_nat, ennreal.coe_nat_le_coe_nat, hk N] }
end

/-- A variant of Doob's upcrossing estimate obtained by taking the supremum on both sides. -/
lemma submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part [is_finite_measure μ]
  (a b : ℝ) (hf : submartingale f ℱ μ) :
  ennreal.of_real (b - a) * ∫⁻ x, upcrossings a b f x ∂μ ≤
  ⨆ N, ∫⁻ x, ennreal.of_real ((f N x - a)⁺) ∂μ :=
begin
  by_cases hab : a < b,
  { simp_rw [upcrossings],
    have : ∀ N, ∫⁻ x, ennreal.of_real ((f N x - a)⁺) ∂μ = ennreal.of_real (∫ x, (f N x - a)⁺ ∂μ),
    { intro N,
      rw of_real_integral_eq_lintegral_of_real,
      { exact (hf.sub_martingale (martingale_const _ _ _)).pos.integrable _ },
      { exact eventually_of_forall (λ x, lattice_ordered_comm_group.pos_nonneg _) } },
    rw lintegral_supr',
    { simp_rw [this, ennreal.mul_supr, supr_le_iff],
      intro N,
      rw [(by simp : ∫⁻ x, upcrossings_before a b f N x ∂μ =
        ∫⁻ x, ↑(upcrossings_before a b f N x : ℝ≥0) ∂μ), lintegral_coe_eq_integral,
        ← ennreal.of_real_mul (sub_pos.2 hab).le],
      { simp_rw [nnreal.coe_nat_cast],
        exact (ennreal.of_real_le_of_real
          (hf.mul_integral_upcrossings_before_le_integral_pos_part a b N)).trans (le_supr _ N) },
      { simp only [nnreal.coe_nat_cast, hf.adapted.integrable_upcrossings_before hab] } },
    { refine λ n, measurable_from_top.comp_ae_measurable
        (hf.adapted.measurable_upcrossings_before  hab).ae_measurable },
    { refine eventually_of_forall (λ x N M hNM, _),
      rw ennreal.coe_nat_le_coe_nat,
      exact upcrossings_before_mono hab hNM x } },
  { rw [not_lt, ← sub_nonpos] at hab,
    rw [ennreal.of_real_of_nonpos hab, zero_mul],
    exact zero_le _ }
end

end measure_theory
