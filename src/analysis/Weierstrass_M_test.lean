import order.filter.archimedean
import data.complex.basic
import topology.instances.nnreal
import analysis.complex.basic
import order.filter.at_top_bot
universes u v w


/-!
# The Weierstrass M-test
This file proves the theorem known as the Weierstrass M-test which gives conditions for a
series to be absolutely and uniformly convergent.
-/

noncomputable theory

open complex metric open_locale big_operators nnreal classical filter topological_space

variables {α : Type u} {β : Type v}

lemma summable_if_complex_abs_summable {f : α → ℂ} :
  summable (λ x, complex.abs (f x)) →  summable f :=
begin
  intro h,
  apply summable_of_norm_bounded  (λ x, complex.abs (f x))  h,
  intro i,
  unfold norm,
  exact complete_of_proper,
end

lemma M_test_summable (F : ℕ → α → ℂ) (M : ℕ → ℝ)
  (h1 : ∀ (n : ℕ), ∀ (a : α), (complex.abs (F n a)) ≤ (M n))
  (h2 : summable M) : (∀ (a : α), summable (λ (n : ℕ), F n a)) :=
begin
  intro a,
  apply summable_if_complex_abs_summable,
  have c1 : ∀ (n : ℕ), 0 ≤ (complex.abs (F n a)), by {intro n, apply complex.abs_nonneg (F n a),},
  have H1 : ∀ (n : ℕ), (complex.abs (F n a)) ≤ (M n), by {simp only [h1, forall_const]},
  apply summable_of_nonneg_of_le c1 H1,
  exact h2,
end

lemma sum_sub_tsum_nat_add  {f : ℕ → ℂ} (k : ℕ) (h : summable f) :
 ∑' i, f i - (∑ i in finset.range k, f i) = (∑' i, f (i + k))  :=
begin
  have:= sum_add_tsum_nat_add  k h,
  exact sub_eq_of_eq_add' (eq.symm this),
end

lemma abs_tsum (f : ℕ → ℂ) (h : summable (λ (i : ℕ), ∥ f i ∥ )) :
  complex.abs (∑'(i : ℕ), f i ) ≤  (∑' (i : ℕ), complex.abs (f i)) :=
begin
  rw ← complex.norm_eq_abs,
  simp_rw ← complex.norm_eq_abs,
  apply norm_tsum_le_tsum_norm,
  exact h,
end



lemma M_test_uniform [nonempty α] (F : ℕ → α → ℂ) (M : ℕ → ℝ)
  (h1 : ∀ (n : ℕ), ∀ (a : α), (complex.abs (F n a)) ≤ (M n))
  (h2 : summable M) :
  tendsto_uniformly (λ (n : ℕ), (λ (a : α), ∑ i in (finset.range n), F i a))
  ( (λ (a : α), ∑' (n : ℕ), F n a)) filter.at_top :=
begin
  have Mpos: ∀ (n : ℕ), 0 ≤ M n ,
    by {intro n,
    have := h1 n,
    have t1 : ∀ (a : α), 0 ≤  complex.abs(F n a), by {intro a, apply complex.abs_nonneg,},
    apply le_trans (t1 _) (this _),
    have ne := exists_true_iff_nonempty.2 _inst_1,
    use classical.some ne,},
  rw metric.tendsto_uniformly_iff,
  intros ε hε,
  have hS := M_test_summable F M h1 h2,
  simp only [filter.eventually_at_top, gt_iff_lt, ge_iff_le] at *,
  have H := summable_iff_vanishing_norm.1 h2 ε hε,
  simp only at H,
  have HU : ∃ (a : ℕ), ∀ (b : ℕ), a ≤ b → ∥ ∑' i, M (i+b) ∥ < ε,
     by { have HC := tendsto_sum_nat_add M,
     simp [tendsto_iff_dist_tendsto_zero] at HC,
     simp only [dist_zero_right, norm_norm] at HC,
     simp_rw metric.tendsto_nhds at HC,
     simp only [filter.eventually_at_top, gt_iff_lt, ge_iff_le, dist_zero_right, norm_norm] at HC,
     exact HC ε hε,},
  have c1 : ∀ (a : α) (n : ℕ), 0 ≤ (complex.abs (F n a)),
  by {intros a n, apply complex.abs_nonneg (F n a),},
  have H1 : ∀ (a : α) (n : ℕ), complex.abs (F n a) ≤ (M n), by {simp [h1]},
  have B1 : ∀ (a : α), ∑' (n : ℕ), complex.abs(F n a) ≤ ∑' (n : ℕ), M n,
    by { intro a,
    apply tsum_le_tsum,
    simp only [h1, forall_const],
    apply summable_of_nonneg_of_le (c1 a) (H1 a) h2,
    exact h2,},
  have S1 : ∀ (a : α), summable (λ (i : ℕ), complex.abs (F i a)),
  by  {intro a, apply summable_of_nonneg_of_le (c1 a) (H1 a) h2,},
  have BU : ∃ (a : ℕ), ∀ (b : ℕ), a ≤ b → ∀ (r : α),  ∑' i, complex.abs (F (i+b) r)  < ε,
    by {cases HU,
    use HU_w,
    intros b hb,
    intro r,
    have :  ∑' i, complex.abs (F (i+b) r)  ≤ ∥ ∑' i, M (i+b) ∥,
      by { have r1 : ∥ ∑' i, M (i+b) ∥=∑' i, M (i+b),
        by {apply real.norm_of_nonneg,
        apply  tsum_nonneg,
        simp only [Mpos, forall_const],},
      rw r1,
      apply tsum_le_tsum,
      simp only [h1, forall_const],
      apply (summable_nat_add_iff b).2 (S1 r),
      apply (summable_nat_add_iff b).2 h2,},
    cases H,
    cases h2,
    dsimp at *,
    have hut := HU_h b hb, exact gt_of_gt_of_ge (HU_h b hb) this,},
  have H2 : ∀ (a : α) (k : ℕ),
  ∑' (n : ℕ), F n a - ∑ (i : ℕ) in finset.range k, F i a = ∑' (n : ℕ), F (n+k) a,
    by {intros a k,
    apply  sum_sub_tsum_nat_add k,
    exact hS a,},
  simp_rw dist_eq_norm,
  simp_rw H2,
  simp only [norm_eq_abs] at *,
  cases BU,
  use BU_w,
  intros b hb r,
  have BUC := BU_h b hb r,
  let G := (λ (i : ℕ), F (i) r),
  have f_um := abs_tsum (λ (i : ℕ), F (i+b) r) _,
  exact gt_of_gt_of_ge BUC f_um,
  have f_sum := (S1 r),
  apply (summable_nat_add_iff b).2 f_sum,
end
