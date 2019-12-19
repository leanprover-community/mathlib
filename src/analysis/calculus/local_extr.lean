/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import topology.local_extr analysis.calculus.deriv

/-! # Local extrema of smooth functions

## Main statements

Rolle's Theorem, Lagrange's and Cauchy's Mean Value Theorems.

TODO:

* if `deriv f` is positive on an interval, then `f` is strictly increasing;
* similarly for negative/nonpositive/nonnegative;
* in particular, if `∀ x, deriv f x = 0`, then `f = const`.
* possibly move some lemmas to other file(s)
-/

universes u v

open filter set
open_locale topological_space classical

section vector_space

variables {E : Type u} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {a : E}
  {f' : E →L[ℝ] ℝ}

/-- "Positive" tangent cone to `s` at `x`; the definition differs fron `tangent_cone_at`
by the requirement. One can think about `pos_tangent_cone_at` as `tangent_cone_at nnreal`
but we have no theory of normed semifields yet. -/
def pos_tangent_cone_at (s : set E) (x : E) : set E :=
{y : E | ∃(c : ℕ → ℝ) (d : ℕ → E), {n:ℕ | x + d n ∈ s} ∈ (at_top : filter ℕ) ∧
  (tendsto c at_top at_top) ∧ (tendsto (λn, c n • d n) at_top (𝓝 y))}

lemma pos_tangent_cone_at_mono : monotone (λ s, pos_tangent_cone_at s a) :=
begin
  rintros s t hst y ⟨c, d, hd, hc, hcd⟩,
  exact ⟨c, d, mem_sets_of_superset hd $ λ h hn, hst hn, hc, hcd⟩
end

lemma mem_pos_tangent_cone_at_of_segment_subset {s : set E} {x y : E} (h : segment x y ⊆ s) :
  y - x ∈ pos_tangent_cone_at s x :=
begin
  let c := λn:ℕ, (2:ℝ)^n,
  let d := λn:ℕ, (c n)⁻¹ • (y-x),
  refine ⟨c, d, filter.univ_mem_sets' (λn, h _), _, _⟩,
  show x + d n ∈ segment x y,
  { refine ⟨(c n)⁻¹, ⟨_, _⟩, _⟩,
    { rw inv_nonneg, apply pow_nonneg, norm_num },
    { apply inv_le_one, apply one_le_pow_of_one_le, norm_num },
    { simp only [d], abel } },
  show tendsto c at_top at_top,
  { exact tendsto_pow_at_top_at_top_of_gt_1 one_lt_two },
  show filter.tendsto (λ (n : ℕ), c n • d n) filter.at_top (𝓝 (y - x)),
  { have : (λ (n : ℕ), c n • d n) = (λn, y - x),
    { ext n,
      simp only [d, smul_smul],
      rw [mul_inv_cancel, one_smul],
      exact pow_ne_zero _ (by norm_num) },
    rw this,
    apply tendsto_const_nhds }
end

lemma pos_tangent_cone_at_univ : pos_tangent_cone_at univ a = univ :=
eq_univ_iff_forall.2
begin
  assume x,
  rw [← add_sub_cancel x a],
  exact mem_pos_tangent_cone_at_of_segment_subset (subset_univ _)
end

lemma is_local_max_on.has_fderiv_within_at_nonpos {s : set E} (h : is_local_max_on f a s)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a) :
  f' y ≤ 0 :=
begin
  rcases hy with ⟨c, d, hd, hc, hcd⟩,
  have hc' : tendsto (λ n, ∥c n∥) at_top at_top,
    from tendsto_at_top_mono _ (λ n, le_abs_self _) hc,
  refine le_of_tendsto at_top_ne_bot (hf.lim at_top hd hc' hcd) _,
  replace hd : tendsto (λ n, a + d n) at_top (nhds_within (a + 0) s),
   -- TODO use `tendsto.inf`once #1809 is landed
  from tendsto_inf.2 ⟨tendsto_const_nhds.add (tangent_cone_at.lim_zero _ hc' hcd),
    by rwa tendsto_principal⟩,
  rw [add_zero] at hd,
  replace h : {n : ℕ | f (a + d n) ≤ f a} ∈ at_top, from mem_map.1 (hd h),
  replace hc : {n | 0 ≤ c n} ∈ at_top, from mem_map.1 (hc (mem_at_top (0:ℝ))),
  filter_upwards [h, hc],
  simp only [mem_set_of_eq, smul_eq_mul, mem_preimage, subset_def],
  assume n hnf hn,
  exact mul_nonpos_of_nonneg_of_nonpos hn (sub_nonpos.2 hnf)
end

lemma is_local_max_on.fderiv_within_nonpos {s : set E} (h : is_local_max_on f a s)
  (hf : differentiable_within_at ℝ f s a) {y} (hy : y ∈ pos_tangent_cone_at s a) :
  (fderiv_within ℝ f s a : E → ℝ) y ≤ 0 :=
h.has_fderiv_within_at_nonpos hf.has_fderiv_within_at hy

lemma is_local_max_on.has_fderiv_within_at_eq_zero {s : set E} (h : is_local_max_on f a s)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a)
  (hy' : -y ∈ pos_tangent_cone_at s a) :
  f' y = 0 :=
le_antisymm (h.has_fderiv_within_at_nonpos hf hy) $
  by simpa using h.has_fderiv_within_at_nonpos hf hy'

lemma is_local_max_on.fderiv_within_eq_zero {s : set E} (h : is_local_max_on f a s)
  {y} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) :
  (fderiv_within ℝ f s a : E → ℝ) y = 0 :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_eq_zero hf.has_fderiv_within_at hy hy'
else by { rw fderiv_within_zero_of_not_differentiable_within_at hf, refl }

lemma is_local_min_on.has_fderiv_within_at_nonneg {s : set E} (h : is_local_min_on f a s)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a) :
  0 ≤ f' y :=
by simpa using h.neg.has_fderiv_within_at_nonpos hf.neg hy

lemma is_local_min_on.fderiv_within_nonneg {s : set E} (h : is_local_min_on f a s)
  (hf : differentiable_within_at ℝ f s a) {y} (hy : y ∈ pos_tangent_cone_at s a) :
  (0:ℝ) ≤ (fderiv_within ℝ f s a : E → ℝ) y :=
h.has_fderiv_within_at_nonneg hf.has_fderiv_within_at hy

lemma is_local_min_on.has_fderiv_within_at_eq_zero {s : set E} (h : is_local_min_on f a s)
  (hf : has_fderiv_within_at f f' s a) {y} (hy : y ∈ pos_tangent_cone_at s a)
  (hy' : -y ∈ pos_tangent_cone_at s a) :
  f' y = 0 :=
by simpa using h.neg.has_fderiv_within_at_eq_zero hf.neg hy hy'

lemma is_local_min_on.fderiv_within_eq_zero {s : set E} (h : is_local_min_on f a s)
  {y} (hy : y ∈ pos_tangent_cone_at s a) (hy' : -y ∈ pos_tangent_cone_at s a) :
  (fderiv_within ℝ f s a : E → ℝ) y = 0 :=
if hf : differentiable_within_at ℝ f s a
then h.has_fderiv_within_at_eq_zero hf.has_fderiv_within_at hy hy'
else by { rw fderiv_within_zero_of_not_differentiable_within_at hf, refl }

/-- The derivative at a local minimum equals zero. -/
lemma is_local_min.has_fderiv_at_eq_zero (h : is_local_min f a) (hf : has_fderiv_at f f' a) :
  f' = 0 :=
begin
  ext y,
  apply (h.on univ).has_fderiv_within_at_eq_zero hf.has_fderiv_within_at;
    rw pos_tangent_cone_at_univ; apply mem_univ
end

/-- The derivative at a local minimum equals zero. -/
lemma is_local_min.fderiv_eq_zero (h : is_local_min f a) : fderiv ℝ f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_fderiv_at_eq_zero hf.has_fderiv_at
else fderiv_zero_of_not_differentiable_at hf

lemma is_local_max.has_fderiv_at_eq_zero (h : is_local_max f a) (hf : has_fderiv_at f f' a) :
  f' = 0 :=
neg_eq_zero.1 $ h.neg.has_fderiv_at_eq_zero hf.neg

lemma is_local_max.fderiv_eq_zero (h : is_local_max f a) : fderiv ℝ f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_fderiv_at_eq_zero hf.has_fderiv_at
else fderiv_zero_of_not_differentiable_at hf

lemma is_local_extr.has_fderiv_at_eq_zero (h : is_local_extr f a) :
  has_fderiv_at f f' a → f' = 0 :=
h.elim is_local_min.has_fderiv_at_eq_zero is_local_max.has_fderiv_at_eq_zero

lemma is_local_extr.fderiv_eq_zero (h : is_local_extr f a) : fderiv ℝ f a = 0 :=
h.elim is_local_min.fderiv_eq_zero is_local_max.fderiv_eq_zero

end vector_space

section real

variables {f : ℝ → ℝ} {f' : ℝ} {a b : ℝ}

lemma is_local_min.has_deriv_at_eq_zero (h : is_local_min f a) (hf : has_deriv_at f f' a) :
  f' = 0 :=
by simpa using continuous_linear_map.ext_iff.1
  (h.has_fderiv_at_eq_zero (has_deriv_at_iff_has_fderiv_at.1 hf)) 1

lemma is_local_min.deriv_eq_zero (h : is_local_min f a) : deriv f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_deriv_at_eq_zero hf.has_deriv_at
else deriv_zero_of_not_differentiable_at hf

lemma is_local_max.has_deriv_at_eq_zero (h : is_local_max f a) (hf : has_deriv_at f f' a) :
  f' = 0 :=
neg_eq_zero.1 $ h.neg.has_deriv_at_eq_zero hf.neg

lemma is_local_max.deriv_eq_zero (h : is_local_max f a) : deriv f a = 0 :=
if hf : differentiable_at ℝ f a then h.has_deriv_at_eq_zero hf.has_deriv_at
else deriv_zero_of_not_differentiable_at hf

lemma is_local_extr.has_deriv_at_eq_zero (h : is_local_extr f a) :
  has_deriv_at f f' a → f' = 0 :=
h.elim is_local_min.has_deriv_at_eq_zero is_local_max.has_deriv_at_eq_zero

lemma is_local_extr.deriv_eq_zero (h : is_local_extr f a) : deriv f a = 0 :=
h.elim is_local_min.deriv_eq_zero is_local_max.deriv_eq_zero

end real

section MVT

variables (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : continuous f) (hfI : f a = f b)

include hab hfc hfI

lemma exists_global_extr_Ioo :
  ∃ c ∈ Ioo a b, (∀ x ∈ Icc a b, f c ≤ f x) ∨ (∀ x ∈ Icc a b, f x ≤ f c) :=
begin
  have ne : Icc a b ≠ ∅, from ne_empty_of_mem (left_mem_Icc.2 (le_of_lt hab)),
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x,
    from compact_Icc.exists_forall_le ne f hfc.continuous_on,
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f C,
    from compact_Icc.exists_forall_ge ne f hfc.continuous_on,
  by_cases hc : f c = f a,
  { by_cases hC : f C = f a,
    { have : ∀ x ∈ Icc a b, f x = f a,
        from λ x hx, le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx),
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases dense hab with ⟨c', hc'⟩,
      refine ⟨c', hc', or.inl _⟩,
      assume x hx,
      rw [this x hx, ← hC],
      exact Cge c' ⟨le_of_lt hc'.1, le_of_lt hc'.2⟩ },

    { refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 $ mt _ hC, lt_of_le_of_ne Cmem.2 $ mt _ hC⟩, or.inr Cge⟩,
      exacts [λ h, by rw h, λ h, by rw [h, hfI]] } },
  { refine ⟨c, ⟨lt_of_le_of_ne cmem.1 $ mt _ hc, lt_of_le_of_ne cmem.2 $ mt _ hc⟩, or.inl cle⟩,
      exacts [λ h, by rw h, λ h, by rw [h, hfI]] }
end

lemma exists_local_extr_Ioo : ∃ c ∈ Ioo a b, is_local_extr f c :=
by rcases exists_global_extr_Ioo f hab hfc hfI with ⟨c, cmem, hc | hc⟩; use [c, cmem]; [left,right];
  exact mem_nhds_iff_exists_Ioo_subset.2 ⟨a, b, cmem, λ x hx, hc _ ⟨le_of_lt hx.1, le_of_lt hx.2⟩⟩

variable (hff' : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x)

include hff'

/-- Rolle's Theorem `has_deriv_at` version -/
lemma exists_has_deriv_at_eq_zero :
  ∃ c ∈ Ioo a b, f' c = 0 :=
let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI in
  ⟨c, cmem, hc.has_deriv_at_eq_zero $ hff' c cmem⟩

omit hfI

/-- Cauchy version of the Mean Value Theorem -/
lemma exists_ratio_has_deriv_at_eq_ratio_slope
  (g g' : ℝ → ℝ) (hgc : continuous g) (hgg' : ∀ x ∈ Ioo a b, has_deriv_at g (g' x) x) :
  ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c :=
begin
  let h := λ x, (g b - g a) * f x - (f b - f a) * g x,
  have hI : h a = h b,
  { simp only [h], ring },
  let h' := λ x, (g b - g a) * f' x - (f b - f a) * g' x,
  have hhh' : ∀ x ∈ Ioo a b, has_deriv_at h (h' x) x,
  { assume x hx,
    convert ((has_deriv_at_const x (g b - g a)).mul (hff' x hx)).sub
      ((has_deriv_at_const x (f b - f a)).mul (hgg' x hx)),
    simp only [h', mul_zero, add_zero] },
  have hhc : continuous h,
    from (continuous_const.mul hfc).sub (continuous_const.mul hgc),
  rcases exists_has_deriv_at_eq_zero h h' hab hhc hI hhh' with ⟨c, cmem, hc⟩,
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩
end

lemma exists_has_deriv_at_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) :=
begin
  rcases exists_ratio_has_deriv_at_eq_ratio_slope f f' hab hfc hff' id 1 continuous_id (λ x hx, has_deriv_at_id x) with ⟨c, cmem, hc⟩,
  use [c, cmem],
  simp only [id, pi.one_apply, mul_one] at hc,
  rw [← hc, mul_div_cancel_left],
  exact ne_of_gt (sub_pos.2 hab)
end

omit hff'

lemma exists_deriv_eq_zero : ∃ c ∈ Ioo a b, deriv f c = 0 :=
let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI in
  ⟨c, cmem, hc.deriv_eq_zero⟩

lemma exists_ratio_deriv_eq_ratio_slope (hfd : ∀ x ∈ Ioo a b, differentiable_at ℝ f x)
  (g : ℝ → ℝ) (hgc : continuous g) (hgd : ∀ x ∈ Ioo a b, differentiable_at ℝ g x):
  ∃ c ∈ Ioo a b, (g b - g a) * (deriv f c) = (f b - f a) * (deriv g c) :=
exists_ratio_has_deriv_at_eq_ratio_slope f (deriv f) hab hfc
  (λ x hx, (hfd x hx).has_deriv_at) g (deriv g) hgc (λ x hx, (hgd x hx).has_deriv_at)

lemma exists_deriv_eq_slope (hfd : ∀ x ∈ Ioo a b, differentiable_at ℝ f x) :
  ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
exists_has_deriv_at_eq_slope f (deriv f) hab hfc (λ x hx, (hfd x hx).has_deriv_at)

end MVT
