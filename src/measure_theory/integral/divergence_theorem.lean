/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.divergence_theorem
import analysis.box_integral.integrability
import measure_theory.integral.interval_integral
import data.set.intervals.monotone

/-!
# Divergence theorem for Bochner integral

In this file we prove the Divergence theorem for Bochner integral on a box in
`ℝⁿ⁺¹ = fin (n + 1) → ℝ`. More precisely, we prove the following theorem.

Let `E` be a complete normed space. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is
continuous on a rectangular box `[a, b] : set ℝⁿ⁺¹`, `a ≤ b`, differentiable on its interior with
derivative `f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹`, and the divergence `λ x, ∑ i, f' x eᵢ i` is integrable on
`[a, b]`, where `eᵢ = pi.single i 1` is the `i`-th basis vector, then its integral is equal to the
sum of integrals of `f` over the faces of `[a, b]`, taken with appropriate signs. Moreover, the same
is true if the function is not differentiable at countably many points of the interior of `[a, b]`.

Once we prove the general theorem, we deduce corollaries for functions `ℝ → E` and pairs of
functions `(ℝ × ℝ) → E`.

Once we prove the general theorem, we deduce corollaries for functions `ℝ → E` and pairs of
functions `(ℝ × ℝ) → E`.

## Notations

We use the following local notation to make the statement more readable. Note that the documentation
website shows the actual terms, not those abbreviated using local notations.

* `ℝⁿ`, `ℝⁿ⁺¹`, `Eⁿ⁺¹`: `fin n → ℝ`, `fin (n + 1) → ℝ`, `fin (n + 1) → E`;
* `face i`: the `i`-th face of the box `[a, b]` as a closed segment in `ℝⁿ`, namely `[a ∘
  fin.succ_above i, b ∘ fin.succ_above i]`;
* `e i` : `i`-th basis vector `pi.single i 1`;
* `front_face i`, `back_face i`: embeddings `ℝⁿ → ℝⁿ⁺¹` corresponding to the front face
  `{x | x i = b i}` and back face `{x | x i = a i}` of the box `[a, b]`, respectively.
  They are given by `fin.insert_nth i (b i)` and `fin.insert_nth i (a i)`.

## TODO

* Add a version that assumes existence and integrability of partial derivatives.

## Tags

divergence theorem, Bochner integral
-/

open set finset topological_space function box_integral measure_theory filter
open_locale big_operators classical topological_space interval

universes u

namespace measure_theory

variables {E : Type u} [normed_group E] [normed_space ℝ E] [complete_space E]

section
variables {n : ℕ}

local notation `ℝⁿ` := fin n → ℝ
local notation `ℝⁿ⁺¹` := fin (n + 1) → ℝ
local notation `Eⁿ⁺¹` := fin (n + 1) → E
local notation `e` i := pi.single i 1

section

/-!
### Divergence theorem for functions on `ℝⁿ⁺¹ = fin (n + 1) → ℝ`.

In this section we use the divergence theorem for a Henstock-Kurzweil-like integral
`box_integral.has_integral_bot_divergence_of_forall_has_deriv_within_at` to prove the divergence
theorem for Bochner integral. The divergence theorem for Bochner integral
`measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable` assumes that the function
itself is continuous on a closed box, differentiable at all but countably many points of its
interior, and the divergence is integrable on the box.

This statement differs from `box_integral.has_integral_bot_divergence_of_forall_has_deriv_within_at`
in several aspects.

* We use Bochner integral instead of a Henstock-Kurzweil integral. This modification is done in
  `measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_aux₁`. As a side effect
  of this change, we need to assume that the divergence is integrable.

* We don't assume differentiability on the boundary of the box. This modification is done in
  `measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable_aux₂`. To prove it, we
  choose an increasing sequence of smaller boxes that cover the interior of the original box, then
  apply the previous lemma to these smaller boxes and take the limit of both sides of the equation.

* We assume `a ≤ b` instead of `∀ i, a i < b i`. This is the last step of the proof, and it is done
  in the main theorem `measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable`.
-/

/-- An auxiliary lemma for
`measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable`. This is exactly
`box_integral.has_integral_bot_divergence_of_forall_has_deriv_within_at` reformulated for the
Bochner integral. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable_aux₁ (I : box (fin (n + 1)))
  (f : ℝⁿ⁺¹ → Eⁿ⁺¹) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : set ℝⁿ⁺¹) (hs : countable s)
  (Hc : continuous_on f I.Icc) (Hd : ∀ x ∈ I.Icc \ s, has_fderiv_within_at f (f' x) I.Icc x)
  (Hi : integrable_on (λ x, ∑ i, f' x (e i) i) I.Icc) :
  ∫ x in I.Icc, ∑ i, f' x (e i) i =
    ∑ i : fin (n + 1),
      ((∫ x in (I.face i).Icc, f (i.insert_nth (I.upper i) x) i) -
        ∫ x in (I.face i).Icc, f (i.insert_nth (I.lower i) x) i) :=
begin
  simp only [← set_integral_congr_set_ae (box.coe_ae_eq_Icc _)],
  have A := ((Hi.mono_set box.coe_subset_Icc).has_box_integral ⊥ rfl),
  have B := has_integral_bot_divergence_of_forall_has_deriv_within_at I f f' (s ∩ I.Icc)
    (hs.mono (inter_subset_left _ _)) (λ x hx, Hc _ hx.2)
    (λ x hx, Hd _ ⟨hx.1, λ h, hx.2 ⟨h, hx.1⟩⟩),
  rw continuous_on_pi at Hc,
  refine (A.unique B).trans (sum_congr rfl $ λ i hi, _),
  refine congr_arg2 has_sub.sub _ _,
  { have := box.continuous_on_face_Icc (Hc i) (set.right_mem_Icc.2 (I.lower_le_upper i)),
    have := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc,
    exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance },
  { have := box.continuous_on_face_Icc (Hc i) (set.left_mem_Icc.2 (I.lower_le_upper i)),
    have := (this.integrable_on_compact (box.is_compact_Icc _)).mono_set box.coe_subset_Icc,
    exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance }
end

/-- An auxiliary lemma for
`measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable`. Compared to the previous
lemma, here we drop the assumption of differentiability on the boundary of the box. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable_aux₂ (I : box (fin (n + 1)))
  (f : ℝⁿ⁺¹ → Eⁿ⁺¹) (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : set ℝⁿ⁺¹) (hs : countable s)
  (Hc : continuous_on f I.Icc) (Hd : ∀ x ∈ I.Ioo \ s, has_fderiv_at f (f' x) x)
  (Hi : integrable_on (λ x, ∑ i, f' x (e i) i) I.Icc) :
  ∫ x in I.Icc, ∑ i, f' x (e i) i =
    ∑ i : fin (n + 1),
      ((∫ x in (I.face i).Icc, f (i.insert_nth (I.upper i) x) i) -
        ∫ x in (I.face i).Icc, f (i.insert_nth (I.lower i) x) i) :=
begin
  /- Choose a monotone sequence `J k` of subboxes that cover the interior of `I` and prove that
  these boxes satisfy the assumptions of the previous lemma. -/
  rcases I.exists_seq_mono_tendsto with ⟨J, hJ_sub, hJl, hJu⟩,
  have hJ_sub' : ∀ k, (J k).Icc ⊆ I.Icc, from λ k, (hJ_sub k).trans I.Ioo_subset_Icc,
  have hJ_le : ∀ k, J k ≤ I, from λ k, box.le_iff_Icc.2 (hJ_sub' k),
  have HcJ : ∀ k, continuous_on f (J k).Icc, from λ k, Hc.mono (hJ_sub' k),
  have HdJ : ∀ k (x ∈ (J k).Icc \ s), has_fderiv_within_at f (f' x) (J k).Icc x,
    from λ k x hx, (Hd x ⟨hJ_sub k hx.1, hx.2⟩).has_fderiv_within_at,
  have HiJ : ∀ k, integrable_on (λ x, ∑ i, f' x (e i) i) (J k).Icc,
    from λ k, Hi.mono_set (hJ_sub' k),
  -- Apply the previous lemma to `J k`.
  have HJ_eq := λ k, integral_divergence_of_has_fderiv_within_at_off_countable_aux₁ (J k) f f' s hs
    (HcJ k) (HdJ k) (HiJ k),
  /- Note that the LHS of `HJ_eq k` tends to the LHS of the goal as `k → ∞`. -/
  have hI_tendsto : tendsto (λ k, ∫ x in (J k).Icc, ∑ i, f' x (e i) i) at_top
    (𝓝 (∫ x in I.Icc, ∑ i, f' x (e i) i)),
  { simp only [integrable_on, ← measure.restrict_congr_set (box.Ioo_ae_eq_Icc _)] at Hi ⊢,
    rw ← box.Union_Ioo_of_tendsto J.monotone hJl hJu at Hi ⊢,
    exact tendsto_set_integral_of_monotone (λ k, (J k).measurable_set_Ioo)
      (box.Ioo.comp J).monotone Hi },
  /- Thus it suffices to prove the same about the RHS. -/
  refine tendsto_nhds_unique_of_eventually_eq hI_tendsto _ (eventually_of_forall HJ_eq),
  clear hI_tendsto,
  rw tendsto_pi_nhds at hJl hJu,
  /- We'll need to prove a similar statement about the integrals over the front sides and the
  integrals over the back sides. In order to avoid repeating ourselves, we formulate a lemma. -/
  suffices : ∀ (i : fin (n + 1)) (c : ℕ → ℝ) d,
    (∀ k, c k ∈ Icc (I.lower i) (I.upper i)) → tendsto c at_top (𝓝 d) →
      tendsto (λ k, ∫ x in ((J k).face i).Icc, f (i.insert_nth (c k) x) i) at_top
        (𝓝 $ ∫ x in (I.face i).Icc, f (i.insert_nth d x) i),
  { rw box.Icc_eq_pi at hJ_sub',
    refine tendsto_finset_sum _ (λ i hi, (this _ _ _ _ (hJu _)).sub (this _ _ _ _ (hJl _))),
    exacts [λ k, hJ_sub' k (J k).upper_mem_Icc _ trivial,
      λ k, hJ_sub' k (J k).lower_mem_Icc _ trivial] },
  intros i c d hc hcd,
  /- First we prove that the integrals of the restriction of `f` to `{x | x i = d}` over increasing
  boxes `((J k).face i).Icc` tend to the desired limit. The proof mostly repeats the one above. -/
  have hd : d ∈ Icc (I.lower i) (I.upper i),
    from is_closed_Icc.mem_of_tendsto hcd (eventually_of_forall hc),
  have Hic : ∀ k, integrable_on (λ x, f (i.insert_nth (c k) x) i) (I.face i).Icc,
    from λ k, (box.continuous_on_face_Icc ((continuous_apply i).comp_continuous_on Hc)
      (hc k)).integrable_on_Icc,
  have Hid : integrable_on (λ x, f (i.insert_nth d x) i) (I.face i).Icc,
    from (box.continuous_on_face_Icc ((continuous_apply i).comp_continuous_on Hc)
      hd).integrable_on_Icc,
  have H : tendsto (λ k, ∫ x in ((J k).face i).Icc, f (i.insert_nth d x) i) at_top
      (𝓝 $ ∫ x in (I.face i).Icc, f (i.insert_nth d x) i),
  { have hIoo : (⋃ k, ((J k).face i).Ioo) = (I.face i).Ioo,
      from box.Union_Ioo_of_tendsto ((box.monotone_face i).comp J.monotone)
        (tendsto_pi_nhds.2 (λ _, hJl _)) (tendsto_pi_nhds.2 (λ _, hJu _)),
    simp only [integrable_on, ← measure.restrict_congr_set (box.Ioo_ae_eq_Icc _), ← hIoo] at Hid ⊢,
    exact tendsto_set_integral_of_monotone (λ k, ((J k).face i).measurable_set_Ioo)
      (box.Ioo.monotone.comp ((box.monotone_face i).comp J.monotone)) Hid },
  /- Thus it suffices to show that the distance between the integrals of the restrictions of `f` to
  `{x | x i = c k}` and `{x | x i = d}` over `((J k).face i).Icc` tends to zero as `k → ∞`. Choose
  `ε > 0`. -/
  refine H.congr_dist (metric.nhds_basis_closed_ball.tendsto_right_iff.2 (λ ε εpos, _)),
  have hvol_pos : ∀ J : box (fin n), 0 < ∏ j, (J.upper j - J.lower j),
    from λ J, (prod_pos $ λ j hj, sub_pos.2 $ J.lower_lt_upper _),
  /- Choose `δ > 0` such that for any `x y ∈ I.Icc` at distance at most `δ`, the distance between
  `f x` and `f y` is at most `ε / volume (I.face i).Icc`, then the distance between the integrals
  is at most `(ε / volume (I.face i).Icc) * volume ((J k).face i).Icc ≤ ε`. -/
  rcases metric.uniform_continuous_on_iff_le.1
    (I.is_compact_Icc.uniform_continuous_on_of_continuous Hc)
    (ε / ∏ j, ((I.face i).upper j - (I.face i).lower j)) (div_pos εpos (hvol_pos (I.face i)))
    with ⟨δ, δpos, hδ⟩,
  refine (hcd.eventually (metric.ball_mem_nhds _ δpos)).mono (λ k hk, _),
  have Hsub : ((J k).face i).Icc ⊆ (I.face i).Icc,
    from box.le_iff_Icc.1 (box.face_mono (hJ_le _) i),
  rw [mem_closed_ball_zero_iff, real.norm_eq_abs, abs_of_nonneg dist_nonneg,
    dist_eq_norm, ← integral_sub (Hid.mono_set Hsub) ((Hic _).mono_set Hsub)],
  calc ∥(∫ x in ((J k).face i).Icc, f (i.insert_nth d x) i - f (i.insert_nth (c k) x) i)∥
      ≤ (ε / ∏ j, ((I.face i).upper j - (I.face i).lower j)) * (volume ((J k).face i).Icc).to_real :
    begin
      refine norm_set_integral_le_of_norm_le_const' (((J k).face i).measure_Icc_lt_top _)
        ((J k).face i).measurable_set_Icc (λ x hx, _),
      rw ← dist_eq_norm,
      calc dist (f (i.insert_nth d x) i) (f (i.insert_nth (c k) x) i)
          ≤ dist (f (i.insert_nth d x)) (f (i.insert_nth (c k) x)) :
        dist_le_pi_dist (f (i.insert_nth d x)) (f (i.insert_nth (c k) x)) i
      ... ≤ (ε / ∏ j, ((I.face i).upper j - (I.face i).lower j)) :
        hδ _ (I.maps_to_insert_nth_face_Icc hd $ Hsub hx)
           _ (I.maps_to_insert_nth_face_Icc (hc _) $ Hsub hx) _,
      rw [fin.dist_insert_nth_insert_nth, dist_self, dist_comm],
      exact max_le hk.le δpos.lt.le
    end
  ... ≤ ε :
    begin
      rw [box.Icc_def, real.volume_Icc_pi_to_real ((J k).face i).lower_le_upper,
        ← le_div_iff (hvol_pos _)],
      refine div_le_div_of_le_left εpos.le (hvol_pos _) (prod_le_prod (λ j hj, _) (λ j hj, _)),
      exacts [sub_nonneg.2 (box.lower_le_upper _ _),
        sub_le_sub ((hJ_sub' _ (J _).upper_mem_Icc).2 _) ((hJ_sub' _ (J _).lower_mem_Icc).1 _)]
    end
end

variables (a b : ℝⁿ⁺¹)

local notation `face` i := set.Icc (a ∘ fin.succ_above i) (b ∘ fin.succ_above i)
local notation `front_face` i:2000 := fin.insert_nth i (b i)
local notation `back_face` i:2000 := fin.insert_nth i (a i)

/-- **Divergence theorem** for Bochner integral. If `f : ℝⁿ⁺¹ → Eⁿ⁺¹` is continuous on a rectangular
box `[a, b] : set ℝⁿ⁺¹`, `a ≤ b`, is differentiable on its interior with derivative
`f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹` and the divergence `λ x, ∑ i, f' x eᵢ i` is integrable on `[a, b]`,
where `eᵢ = pi.single i 1` is the `i`-th basis vector, then its integral is equal to the sum of
integrals of `f` over the faces of `[a, b]`, taken with appropriat signs.

Moreover, the same is true if the function is not differentiable at countably many
points of the interior of `[a, b]`.

We represent both faces `x i = a i` and `x i = b i` as the box
`face i = [a ∘ fin.succ_above i, b ∘ fin.succ_above i]` in `ℝⁿ`, where
`fin.succ_above : fin n ↪o fin (n + 1)` is the order embedding with range `{i}ᶜ`. The restrictions
of `f : ℝⁿ⁺¹ → Eⁿ⁺¹` to these faces are given by `f ∘ back_face i` and `f ∘ front_face i`, where
`back_face i = fin.insert_nth i (a i)` and `front_face i = fin.insert_nth i (b i)` are embeddings
`ℝⁿ → ℝⁿ⁺¹` that take `y : ℝⁿ` and insert `a i` (resp., `b i`) as `i`-th coordinate. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable (hle : a ≤ b) (f : ℝⁿ⁺¹ → Eⁿ⁺¹)
  (f' : ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] Eⁿ⁺¹) (s : set ℝⁿ⁺¹) (hs : countable s) (Hc : continuous_on f (Icc a b))
  (Hd : ∀ x ∈ set.pi univ (λ i, Ioo (a i) (b i)) \ s, has_fderiv_at f (f' x) x)
  (Hi : integrable_on (λ x, ∑ i, f' x (e i) i) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' x (e i) i =
    ∑ i : fin (n + 1),
      ((∫ x in face i, f (front_face i x) i) - ∫ x in face i, f (back_face i x) i) :=
begin
  rcases em (∃ i, a i = b i) with ⟨i, hi⟩|hne,
  { /- First we sort out the trivial case `∃ i, a i = b i`. -/
    simp only [volume_pi, ← set_integral_congr_set_ae measure.univ_pi_Ioc_ae_eq_Icc],
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt,
    have : pi set.univ (λ j, Ioc (a j) (b j)) = ∅, from univ_pi_eq_empty hi',
    rw [this, integral_empty, sum_eq_zero],
    rintro j -,
    rcases eq_or_ne i j with rfl|hne,
    { simp [hi] },
    { rcases fin.exists_succ_above_eq hne with ⟨i, rfl⟩,
      have : pi set.univ (λ k : fin n, Ioc (a $ j.succ_above k) (b $ j.succ_above k)) = ∅,
        from univ_pi_eq_empty hi',
      rw [this, integral_empty, integral_empty, sub_self] } },
  { /- In the non-trivial case `∀ i, a i < b i`, we apply a lemma we proved above. -/
    have hlt : ∀ i, a i < b i, from λ i, (hle i).lt_of_ne (λ hi, hne ⟨i, hi⟩),
    convert integral_divergence_of_has_fderiv_within_at_off_countable_aux₂ ⟨a, b, hlt⟩
      f f' s hs Hc Hd Hi }
end

/-- **Divergence theorem** for a family of functions `f : fin (n + 1) → ℝⁿ⁺¹ → E`. See also
`measure_theory.integral_divergence_of_has_fderiv_within_at_off_countable'` for a version formulated
in terms of a vector-valued function `f : ℝⁿ⁺¹ → Eⁿ⁺¹`. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable' (hle : a ≤ b)
  (f : fin (n + 1) → ℝⁿ⁺¹ → E) (f' : fin (n + 1) → ℝⁿ⁺¹ → ℝⁿ⁺¹ →L[ℝ] E)
  (s : set ℝⁿ⁺¹) (hs : countable s) (Hc : ∀ i, continuous_on (f i) (Icc a b))
  (Hd : ∀ (x ∈ pi set.univ (λ i, Ioo (a i) (b i)) \ s) i, has_fderiv_at (f i) (f' i x) x)
  (Hi : integrable_on (λ x, ∑ i, f' i x (e i)) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' i x (e i) =
    ∑ i : fin (n + 1),
      ((∫ x in face i, f i (front_face i x)) - ∫ x in face i, f i (back_face i x)) :=
integral_divergence_of_has_fderiv_within_at_off_countable a b hle (λ x i, f i x)
  (λ x, continuous_linear_map.pi (λ i, f' i x)) s hs
  (continuous_on_pi.2 Hc) (λ x hx, has_fderiv_at_pi.2 (Hd x hx)) Hi

end

/-- An auxiliary lemma that is used to specialize the general divergence theorem to spaces that do
not have the form `fin n → ℝ`. -/
lemma integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv
  {F : Type*} [normed_group F] [normed_space ℝ F] [partial_order F] [measure_space F]
  [borel_space F] (eL : F ≃L[ℝ] ℝⁿ⁺¹) (he_ord : ∀ x y, eL x ≤ eL y ↔ x ≤ y)
  (he_vol : measure_preserving eL volume volume) (f : fin (n + 1) → F → E)
  (f' : fin (n + 1) → F → F →L[ℝ] E) (s : set F) (hs : countable s)
  (a b : F) (hle : a ≤ b) (Hc : ∀ i, continuous_on (f i) (Icc a b))
  (Hd : ∀ (x ∈ interior (Icc a b) \ s) i, has_fderiv_at (f i) (f' i x) x)
  (DF : F → E) (hDF : ∀ x, DF x = ∑ i, f' i x (eL.symm $ e i)) (Hi : integrable_on DF (Icc a b)) :
  ∫ x in Icc a b, DF x =
    ∑ i : fin (n + 1), ((∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL b i) x)) -
      (∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL a i) x))) :=
have he_emb : measurable_embedding eL := eL.to_homeomorph.to_measurable_equiv.measurable_embedding,
have hIcc : eL ⁻¹' (Icc (eL a) (eL b)) = Icc a b,
  by { ext1 x, simp only [set.mem_preimage, set.mem_Icc, he_ord] },
have hIcc' : Icc (eL a) (eL b) = eL.symm ⁻¹' (Icc a b),
  by rw [← hIcc, eL.symm_preimage_preimage],
calc ∫ x in Icc a b, DF x = ∫ x in Icc a b, ∑ i, f' i x (eL.symm $ e i) : by simp only [hDF]
... = ∫ x in Icc (eL a) (eL b), ∑ i, f' i (eL.symm x) (eL.symm $ e i) :
  begin
    rw [← he_vol.set_integral_preimage_emb he_emb],
    simp only [hIcc, eL.symm_apply_apply]
  end
... = ∑ i : fin (n + 1), ((∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL b i) x)) -
      (∫ x in Icc (eL a ∘ i.succ_above) (eL b ∘ i.succ_above),
        f i (eL.symm $ i.insert_nth (eL a i) x))) :
  begin
    convert integral_divergence_of_has_fderiv_within_at_off_countable' (eL a) (eL b)
      ((he_ord _ _).2 hle) (λ i x, f i (eL.symm x))
      (λ i x, f' i (eL.symm x) ∘L (eL.symm : ℝⁿ⁺¹ →L[ℝ] F))
      (eL.symm ⁻¹' s) (hs.preimage eL.symm.injective) _ _ _,
    { exact λ i, (Hc i).comp eL.symm.continuous_on hIcc'.subset },
    { refine λ x hx i, (Hd (eL.symm x) ⟨_, hx.2⟩ i).comp x eL.symm.has_fderiv_at,
      rw ← hIcc,
      refine preimage_interior_subset_interior_preimage eL.continuous _,
      simp only [set.mem_preimage, eL.apply_symm_apply, ← pi_univ_Icc,
        interior_pi_set (finite.of_fintype _), interior_Icc],
      exact hx.1 },
    { rw [← he_vol.integrable_on_comp_preimage he_emb, hIcc],
      simp [← hDF, (∘), Hi] }
  end

end

open_locale interval
open continuous_linear_map (smul_right)

local notation `ℝ¹` := fin 1 → ℝ
local notation `ℝ²` := fin 2 → ℝ
local notation `E¹` := fin 1 → E
local notation `E²` := fin 2 → E

/-- **Fundamental theorem of calculus, part 2**. This version assumes that `f` is continuous on the
interval and is differentiable off a countable set `s`.

See also

* `interval_integral.integral_eq_sub_of_has_deriv_right_of_le` for a version that only assumes right
differentiability of `f`;

* `measure_theory.integral_eq_of_has_deriv_within_at_off_countable` for a version that works both
  for `a ≤ b` and `b ≤ a` at the expense of using unordered intervals instead of `set.Icc`. -/
theorem integral_eq_of_has_deriv_within_at_off_countable_of_le (f f' : ℝ → E)
  {a b : ℝ} (hle : a ≤ b) {s : set ℝ} (hs : countable s)
  (Hc : continuous_on f (Icc a b)) (Hd : ∀ x ∈ Ioo a b \ s, has_deriv_at f (f' x) x)
  (Hi : interval_integrable f' volume a b) :
  ∫ x in a..b, f' x = f b - f a :=
begin
  set e : ℝ ≃L[ℝ] ℝ¹ := (continuous_linear_equiv.fun_unique (fin 1) ℝ ℝ).symm,
  have e_symm : ∀ x, e.symm x = x 0 := λ x, rfl,
  set F' : ℝ → ℝ →L[ℝ] E := λ x, smul_right (1 : ℝ →L[ℝ] ℝ) (f' x),
  have hF' : ∀ x y, F' x y = y • f' x := λ x y, rfl,
  calc ∫ x in a..b, f' x = ∫ x in Icc a b, f' x :
    by simp only [interval_integral.integral_of_le hle, set_integral_congr_set_ae Ioc_ae_eq_Icc]
  ... = ∑ i : fin 1, ((∫ x in Icc (e a ∘ i.succ_above) (e b ∘ i.succ_above),
        f (e.symm $ i.insert_nth (e b i) x)) -
      (∫ x in Icc (e a ∘ i.succ_above) (e b ∘ i.succ_above),
        f (e.symm $ i.insert_nth (e a i) x))) :
    begin
      simp only [← interior_Icc] at Hd,
      refine integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv e _ _
        (λ _, f) (λ _, F') s hs a b hle (λ i, Hc) (λ x hx i, Hd x hx) _ _ _,
      { exact λ x y, (order_iso.fun_unique (fin 1) ℝ).symm.le_iff_le },
      { exact (volume_preserving_fun_unique (fin 1) ℝ).symm },
      { intro x, rw [fin.sum_univ_one, hF', e_symm, pi.single_eq_same, one_smul] },
      { rw [interval_integrable_iff_integrable_Ioc_of_le hle] at Hi,
        exact Hi.congr_set_ae Ioc_ae_eq_Icc.symm }
    end
  ... = f b - f a :
    begin
      simp only [fin.sum_univ_one, e_symm],
      have : ∀ (c : ℝ), const (fin 0) c = is_empty_elim := λ c, subsingleton.elim _ _,
      simp [this, volume_pi, measure.pi_of_empty (λ _ : fin 0, volume)]
    end
end

/-- **Fundamental theorem of calculus, part 2**. This version assumes that `f` is continuous on the
interval and is differentiable off a countable set `s`.

See also `measure_theory.interval_integral.integral_eq_sub_of_has_deriv_right` for a version that
only assumes right differentiability of `f`.
-/
theorem integral_eq_of_has_deriv_within_at_off_countable (f f' : ℝ → E) {a b : ℝ} {s : set ℝ}
  (hs : countable s) (Hc : continuous_on f [a, b])
  (Hd : ∀ x ∈ Ioo (min a b) (max a b) \ s, has_deriv_at f (f' x) x)
  (Hi : interval_integrable f' volume a b) :
  ∫ x in a..b, f' x = f b - f a :=
begin
  cases le_total a b with hab hab,
  { simp only [interval_of_le hab, min_eq_left hab, max_eq_right hab] at *,
    exact integral_eq_of_has_deriv_within_at_off_countable_of_le f f' hab hs Hc Hd Hi },
  { simp only [interval_of_ge hab, min_eq_right hab, max_eq_left hab] at *,
    rw [interval_integral.integral_symm, neg_eq_iff_neg_eq, neg_sub, eq_comm],
    exact integral_eq_of_has_deriv_within_at_off_countable_of_le f f' hab hs Hc Hd Hi.symm }
end

/-- **Divergence theorem** for functions on the plane along rectangles. It is formulated in terms of
two functions `f g : ℝ × ℝ → E` and an integral over `Icc a b = [a.1, b.1] × [a.2, b.2]`, where
`a b : ℝ × ℝ`, `a ≤ b`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle equals the integral of the normal derivative of `F` along the
boundary.

See also `measure_theory.integral2_divergence_prod_of_has_fderiv_within_at_off_countable` for a
version that does not assume `a ≤ b` and uses iterated interval integral instead of the integral
over `Icc a b`. -/
lemma integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le (f g : ℝ × ℝ → E)
  (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a b : ℝ × ℝ) (hle : a ≤ b) (s : set (ℝ × ℝ)) (hs : countable s)
  (Hcf : continuous_on f (Icc a b)) (Hcg : continuous_on g (Icc a b))
  (Hdf : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, has_fderiv_at f (f' x) x)
  (Hdg : ∀ x ∈ Ioo a.1 b.1 ×ˢ Ioo a.2 b.2 \ s, has_fderiv_at g (g' x) x)
  (Hi : integrable_on (λ x, f' x (1, 0) + g' x (0, 1)) (Icc a b)) :
  ∫ x in Icc a b, f' x (1, 0) + g' x (0, 1) =
    (∫ x in a.1..b.1, g (x, b.2)) - (∫ x in a.1..b.1, g (x, a.2)) +
      (∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) :=
let e : (ℝ × ℝ) ≃L[ℝ] ℝ² := (continuous_linear_equiv.fin_two_arrow ℝ ℝ).symm in
calc ∫ x in Icc a b, f' x (1, 0) + g' x (0, 1)
    = ∑ i : fin 2, ((∫ x in Icc (e a ∘ i.succ_above) (e b ∘ i.succ_above),
        ![f, g] i (e.symm $ i.insert_nth (e b i) x)) -
      (∫ x in Icc (e a ∘ i.succ_above) (e b ∘ i.succ_above),
        ![f, g] i (e.symm $ i.insert_nth (e a i) x))) :
  begin
    refine integral_divergence_of_has_fderiv_within_at_off_countable_of_equiv e _ _
      ![f, g] ![f', g'] s hs a b hle _ (λ x hx, _) _ _ Hi,
    { exact λ x y, (order_iso.fin_two_arrow_iso ℝ).symm.le_iff_le },
    { exact (volume_preserving_fin_two_arrow ℝ).symm },
    { exact fin.forall_fin_two.2 ⟨Hcf, Hcg⟩ },
    { rw [Icc_prod_eq, interior_prod_eq, interior_Icc, interior_Icc] at hx,
      exact fin.forall_fin_two.2 ⟨Hdf x hx, Hdg x hx⟩ },
    { intro x, rw fin.sum_univ_two, simp }
  end
... = (∫ y in Icc a.2 b.2, f (b.1, y)) - (∫ y in Icc a.2 b.2, f (a.1, y)) +
        ((∫ x in Icc a.1 b.1, g (x, b.2)) - ∫ x in Icc a.1 b.1, g (x, a.2)) :
  begin
    have : ∀ (a b : ℝ¹) (f : ℝ¹ → E), ∫ x in Icc a b, f x = ∫ x in Icc (a 0) (b 0), f (λ _, x),
    { intros a b f,
      convert ((volume_preserving_fun_unique (fin 1) ℝ).symm.set_integral_preimage_emb
        (measurable_equiv.measurable_embedding _) _ _).symm,
      exact ((order_iso.fun_unique (fin 1) ℝ).symm.preimage_Icc a b).symm },
    simp only [fin.sum_univ_two, this],
    refl
  end
... = (∫ x in a.1..b.1, g (x, b.2)) - (∫ x in a.1..b.1, g (x, a.2)) +
        (∫ y in a.2..b.2, f (b.1, y)) - ∫ y in a.2..b.2, f (a.1, y) :
  begin
    simp only [interval_integral.integral_of_le hle.1, interval_integral.integral_of_le hle.2,
      set_integral_congr_set_ae Ioc_ae_eq_Icc],
    abel
  end

/-- **Divergence theorem** for functions on the plane. It is formulated in terms of two functions
`f g : ℝ × ℝ → E` and iterated integral `∫ x in a₁..b₁, ∫ y in a₂..b₂, _`, where
`a₁ a₂ b₁ b₂ : ℝ`. When thinking of `f` and `g` as the two coordinates of a single function
`F : ℝ × ℝ → E × E` and when `E = ℝ`, this is the usual statement that the integral of the
divergence of `F` inside the rectangle with vertices `(aᵢ, bⱼ)`, `i, j =1,2`, equals the integral of
the normal derivative of `F` along the boundary.

See also `measure_theory.integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le`
for a version that uses an integral over `Icc a b`, where `a b : ℝ × ℝ`, `a ≤ b`. -/
lemma integral2_divergence_prod_of_has_fderiv_within_at_off_countable (f g : ℝ × ℝ → E)
  (f' g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E) (a₁ a₂ b₁ b₂ : ℝ) (s : set (ℝ × ℝ)) (hs : countable s)
  (Hcf : continuous_on f ([a₁, b₁] ×ˢ [a₂, b₂])) (Hcg : continuous_on g ([a₁, b₁] ×ˢ [a₂, b₂]))
  (Hdf : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s,
    has_fderiv_at f (f' x) x)
  (Hdg : ∀ x ∈ Ioo (min a₁ b₁) (max a₁ b₁) ×ˢ Ioo (min a₂ b₂) (max a₂ b₂) \ s,
    has_fderiv_at g (g' x) x)
  (Hi : integrable_on (λ x, f' x (1, 0) + g' x (0, 1)) ([a₁, b₁] ×ˢ [a₂, b₂])) :
  ∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1) =
    (∫ x in a₁..b₁, g (x, b₂)) - (∫ x in a₁..b₁, g (x, a₂)) +
      (∫ y in a₂..b₂, f (b₁, y)) - ∫ y in a₂..b₂, f (a₁, y) :=
begin
  wlog h₁ : a₁ ≤ b₁ := le_total a₁ b₁ using [a₁ b₁, b₁ a₁] tactic.skip,
  wlog h₂ : a₂ ≤ b₂ := le_total a₂ b₂ using [a₂ b₂, b₂ a₂] tactic.skip,
  { simp only [interval_of_le h₁, interval_of_le h₂, min_eq_left, max_eq_right, h₁, h₂]
      at Hcf Hcg Hdf Hdg Hi,
    calc ∫ x in a₁..b₁, ∫ y in a₂..b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1)
        = ∫ x in Icc a₁ b₁, ∫ y in Icc a₂ b₂, f' (x, y) (1, 0) + g' (x, y) (0, 1) :
      by simp only [interval_integral.integral_of_le, h₁, h₂,
        set_integral_congr_set_ae Ioc_ae_eq_Icc]
    ... = ∫ x in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f' x (1, 0) + g' x (0, 1) :
      (set_integral_prod _ Hi).symm
    ... = (∫ x in a₁..b₁, g (x, b₂)) - (∫ x in a₁..b₁, g (x, a₂)) +
            (∫ y in a₂..b₂, f (b₁, y)) - ∫ y in a₂..b₂, f (a₁, y) :
      begin
        rw Icc_prod_Icc at *,
        apply integral_divergence_prod_Icc_of_has_fderiv_within_at_off_countable_of_le f g f' g'
          (a₁, a₂) (b₁, b₂) ⟨h₁, h₂⟩ s; assumption
      end },
  { rw [interval_swap b₂ a₂, min_comm b₂ a₂, max_comm b₂ a₂] at this,
    intros Hcf Hcg Hdf Hdg Hi,
    simp only [interval_integral.integral_symm b₂ a₂, interval_integral.integral_neg],
    refine (congr_arg has_neg.neg (this Hcf Hcg Hdf Hdg Hi)).trans _, abel },
  { rw [interval_swap b₁ a₁, min_comm b₁ a₁, max_comm b₁ a₁] at this,
    intros Hcf Hcg Hdf Hdg Hi,
    simp only [interval_integral.integral_symm b₁ a₁],
    refine (congr_arg has_neg.neg (this Hcf Hcg Hdf Hdg Hi)).trans _, abel }
end

end measure_theory
