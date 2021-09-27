/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials
import algebra.archimedean

lemma norm_coe_nat_le_coe (R : Type*) [semi_normed_ring R] [norm_one_class R] :
  ∀ (n : ℕ), ∥(n : R)∥ ≤ (n : ℝ)
| 0 := by simp
| (n + 1) := begin
  simp only [nat.cast_add, nat.cast_one],
  refine (norm_add_le _ _).trans _,
  refine add_le_add (norm_coe_nat_le_coe n) (le_of_eq _),
  refine norm_one,
end

lemma coe_nat_is_O_coe_nat (R : Type*) [semi_normed_ring R] [norm_one_class R] :
  asymptotics.is_O (coe : ℕ → R) (coe : ℕ → ℝ) filter.at_top :=
begin
  refine asymptotics.is_O_of_le filter.at_top (λ n, _),
  refine le_trans (norm_coe_nat_le_coe R n) _,
  simp,
end

-- lemma exists_norm_coe_nat_gt (x : ℝ) : ∃ (n : ℕ), x < ∥(n : ℝ)∥ :=
-- let ⟨n, hn⟩ := exists_nat_gt x in
--   ⟨n, lt_of_lt_of_le hn (le_of_eq (real.norm_coe_nat n).symm)⟩

-- @[simp]
-- lemma norm_coe_nat_le_iff (n m : ℕ) :
--   ∥(n : ℝ)∥ ≤ ∥(m : ℝ)∥ ↔ n ≤ m :=
-- by simp only [real.norm_coe_nat, nat.cast_le]

lemma real.norm_coe_nat_eventually_ge (c : ℝ) :
  ∀ᶠ (x : ℕ) in filter.at_top, c ≤ ∥(x : ℝ)∥ :=
begin
  simp only [filter.eventually_at_top, real.norm_coe_nat, ge_iff_le],
  obtain ⟨y, hy⟩ := exists_nat_ge c,
  exact ⟨y, λ x hx, hy.trans $ nat.cast_le.mpr hx⟩,
end

lemma nat_coe_tendsto_at_top (R : Type*) [ordered_ring R] [nontrivial R] [archimedean R] :
  filter.tendsto (λ (n : ℕ), (↑n : R)) filter.at_top filter.at_top :=
begin
  refine filter.tendsto_at_top.2 (λ x, _),
  obtain ⟨m, hm⟩ := exists_nat_ge x,
  rw filter.eventually_at_top,
  refine ⟨m, λ y hy, hm.trans $ nat.cast_le.2 hy⟩,
end

namespace asymptotics

lemma fpow_is_O_fpow_of_le {α 𝕜 : Type*} [preorder α] [normed_field 𝕜]
  {f : α → 𝕜} {a b : ℤ} (hab : a ≤ b)
  (h : ∀ᶠ (x : α) in filter.at_top, 1 ≤ ∥f x∥):
  (is_O (λ n, (f n) ^ a) (λ n, (f n) ^ b) filter.at_top) :=
begin
  refine is_O.of_bound 1 (filter.sets_of_superset filter.at_top h (λ x hx, _)),
  simp only [one_mul, normed_field.norm_fpow, set.mem_set_of_eq],
  exact fpow_le_of_le hx hab,
end






/-- Definition of negligible functions over an arbitrary `normed_field`.
  Note that the second function always has type `ℕ → ℝ`, which generally gives better lemmas. -/
def negligible {𝕜 : Type*} [normed_ring 𝕜] (f : ℕ → 𝕜) :=
∀ (c : ℤ), is_O f (λ n, (n : ℝ) ^ c) filter.at_top

variables {𝕜 : Type*} [normed_field 𝕜]
variables {f g : ℕ → 𝕜}

lemma negligible_of_is_O (hg : negligible g)
  (h : is_O f g filter.at_top) : negligible f :=
λ c, h.trans $ hg c

lemma negligible_of_eventually_le (hg : negligible g)
  (h : ∀ᶠ n in filter.at_top, ∥f n∥ ≤ ∥g n∥) : negligible f :=
negligible_of_is_O hg $ is_O_iff.2 ⟨1, by simpa only [one_mul] using h⟩

/-- It suffices to check the negligiblity condition for only sufficiently small exponents -/
lemma negligible_of_eventually_is_O
  (h : ∀ᶠ (c : ℤ) in filter.at_bot, is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligible f :=
begin
  obtain ⟨C, hC⟩ := filter.eventually_at_bot.mp h,
  intro c,
  by_cases hc : c ≤ C,
  { exact hC c hc },
  { exact (hC C le_rfl).trans
      (fpow_is_O_fpow_of_le (le_of_not_le hc) (real.norm_coe_nat_eventually_ge 1)) }
end

lemma negligible_of_is_O_fpow_le (C : ℤ)
  (h : ∀ c ≤ C, is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligible f :=
negligible_of_eventually_is_O (filter.eventually_at_bot.2 ⟨C, h⟩)

lemma negligible_of_is_O_fpow_lt (C : ℤ)
  (h : ∀ c < C, is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligible f :=
negligible_of_is_O_fpow_le C.pred
  (λ c hc, h c (lt_of_le_of_lt hc (int.pred_self_lt C)))

lemma tendsto_zero_of_negligible (hf : negligible f) :
  filter.tendsto f filter.at_top (nhds 0) :=
begin
  refine is_O.trans_tendsto (hf (-1)) _,
  have : (λ (n : ℕ), (n : ℝ) ^ (-1 : ℤ)) = (has_inv.inv : ℝ → ℝ) ∘ (coe : ℕ → ℝ),
  by simp only [gpow_one, fpow_neg],
  rw this,
  refine filter.tendsto.comp (tendsto_inv_at_top_zero) (nat_coe_tendsto_at_top ℝ),
end

lemma norm_eventually_le_of_negligible
  (hf : negligible f) (x₀ : ℝ) (hx₀ : 0 < x₀) :
  ∀ᶠ (n : ℕ) in filter.at_top, ∥f n∥ ≤ x₀ :=
begin
  specialize hf (-1),
  rw is_O_iff at hf,
  obtain ⟨c, hc⟩ := hf,
  refine filter.eventually.mp hc _,
  have : ∀ᶠ (n : ℕ) in filter.at_top, c * ∥(n : ℝ) ^ (-1 : ℤ)∥ ≤ x₀,
  {
    rw filter.eventually_at_top,
    obtain ⟨a, ha⟩ := exists_nat_ge (c * x₀⁻¹),
    rw mul_inv_le_iff hx₀ at ha,
    use (max a 1),
    intros b hb,
    have : 0 < (b : ℝ) := nat.cast_pos.2 (le_trans (le_max_right a 1) hb),
    simp,
    rw [mul_inv_le_iff this, mul_comm _ x₀],
    refine le_trans ha _,
    refine mul_le_mul le_rfl _ (nat.cast_nonneg a) (le_of_lt hx₀),
    refine nat.cast_le.2 (le_trans _ hb),
    refine le_max_left a 1,
  },
  refine filter.eventually.mono this _,
  refine (λ x hx hx', le_trans hx' hx),
end

@[simp]
lemma negligible_zero : negligible (function.const ℕ (0 : 𝕜)) :=
λ c, is_O_zero _ _

lemma negligible_add (hf : negligible f) (hg : negligible g) :
  negligible (f + g) :=
λ c, is_O.add (hf c) (hg c)

lemma negligible_mul (hf : negligible f) (hg : negligible g) :
  negligible (f * g) :=
begin
  suffices : is_O (f * g) f filter.at_top,
  from λ c, this.trans (hf c),
  refine is_O.of_bound 1 _,
  have := norm_eventually_le_of_negligible hg 1 (zero_lt_one),
  refine this.mono (λ x hx, _),
  rw [pi.mul_apply, normed_field.norm_mul, mul_comm 1 ∥f x∥],
  exact mul_le_mul le_rfl hx (norm_nonneg $ g x) (norm_nonneg $ f x),
end

@[simp]
lemma negligable_const_iff [t1_space 𝕜] (x : 𝕜) :
  negligible (function.const ℕ x) ↔ x = 0 :=
begin
  refine ⟨λ h, not_not.1 (λ hx, _), λ h, h.symm ▸ negligible_zero⟩,
  have := tendsto_zero_of_negligible h,
  rw tendsto_nhds at this,
  specialize this {x}ᶜ (is_open_ne) (ne.symm hx),
  have h' : function.const ℕ x ⁻¹' {x}ᶜ = ∅,
  { refine set.preimage_eq_empty _,
    rw set.range_const,
    exact disjoint_compl_left },
  rw h' at this,
  exact filter.at_top.empty_not_mem this,
end

@[simp]
lemma negligible_const_mul_iff (f : ℕ → 𝕜) (c : 𝕜) :
  negligible (λ n, c * f n) ↔ (c = 0) ∨ (negligible f) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { by_cases hc : c = 0,
    { exact or.inl hc },
    { exact or.inr (negligible_of_is_O h (is_O_self_const_mul c hc f filter.at_top)) } },
  { cases h,
    { simp only [h, zero_mul, negligable_const_iff] },
    { exact negligible_of_is_O h (is_O_const_mul_self c f filter.at_top) } }
end

-- TODO: add `∨ c = 0` to conclusion instead
lemma negligible_const_mul_iff_of_ne_zero (f : ℕ → 𝕜) {c : 𝕜} (hc : c ≠ 0) :
  negligible (λ n, c * f n) ↔ negligible f :=
(negligible_const_mul_iff f c).trans (by simp only [hc, false_or])

lemma negligable_const_mul_of_negligable {f : ℕ → 𝕜} (c : 𝕜)
  (hf : negligible f) : negligible (λ n, c * f n) :=
(negligible_const_mul_iff f c).2 (or.inr hf)

section extra_assumption

@[simp]
lemma negligible_nsmul_iff (f : ℕ → 𝕜) :
  negligible (λ n, n • f n) ↔ negligible f :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    refine negligible_of_is_O h _,

    -- TODO: Not sure what extra assumptions would give this
    have h𝕜 : ∃ (d : ℝ) (hd : 0 < d), ∀ (n : ℕ) (hn : n ≠ 0), d ≤ ∥(n : 𝕜)∥ := sorry,
    obtain ⟨d, hd0, hd⟩ := h𝕜,

    refine is_O.of_bound d⁻¹ _,
    rw filter.eventually_at_top,
    use 1,
    intros n hn,
    specialize hd n (by linarith),
    rw [nsmul_eq_mul, normed_field.norm_mul],
    calc ∥f n∥ ≤ 1 * ∥f n∥ : by rw one_mul
      ... ≤ (d⁻¹ * ∥(n : 𝕜)∥) * ∥f n∥ : begin
        refine mul_le_mul_of_nonneg_right _ (norm_nonneg (f n)),
        rw inv_eq_one_div,
        rw mul_comm (1 / d),
        rw ← mul_div_assoc,
        rw mul_one,
        rw le_div_iff hd0,
        rwa one_mul,
      end

      ... ≤ d⁻¹ * (∥(n : 𝕜)∥ * ∥f n∥) : by rw mul_assoc

  },
  { refine negligible_of_is_O_fpow_lt 0 (λ c hc, _),
    specialize h (c - 1),
    have := is_O.mul (coe_nat_is_O_coe_nat 𝕜) h,
    simp at this,
    simp [nsmul_eq_mul],
    refine this.trans _,
    refine is_O_of_le _ (λ x, le_of_eq (congr_arg _ _)),
    by_cases hx : (x : ℝ) = 0,
    { simp [hx, this],
      refine symm (zero_fpow c (ne_of_lt hc)) },
    calc (x : ℝ) * ↑x ^ (c - 1) = (↑x ^ (1 : ℤ)) * (↑x ^ (c - 1)) : by rw gpow_one
      ... = ↑x ^ (1 + (c - 1)) : (fpow_add hx 1 (c - 1)).symm
      ... = ↑x ^ c : congr_arg (λ g, gpow g (x : ℝ)) (by linarith)
  }
end

lemma negligible_coe_nat_mul_iff (f : ℕ → 𝕜) :
  negligible (λ n, (n : 𝕜) * f n) ↔ negligible f :=
trans (by simp only [nsmul_eq_mul]) (negligible_nsmul_iff f)

@[simp]
lemma negligible_pow_nsmul_iff (f : ℕ → 𝕜) (c : ℕ) :
  negligible (λ n, (n ^ c) • f n : ℕ → 𝕜) ↔ negligible f :=
begin
  induction c with c hc,
  { simp [one_mul, pow_zero] },
  { refine iff.trans _ hc,
    simp only [pow_succ, mul_assoc, nsmul_eq_mul, nat.cast_mul, nat.cast_pow],
    simp_rw ← nsmul_eq_mul,
    exact negligible_nsmul_iff _ }
end

@[simp]
lemma negligible_pow_mul_iff (f : ℕ → 𝕜) (c : ℕ) :
  negligible (λ n, ((n : 𝕜) ^ c) * f n) ↔ negligible f :=
trans (by simp only [nsmul_eq_mul, nat.cast_pow]) (negligible_pow_nsmul_iff f c)

theorem negligable_polynomial_mul_iff (f : ℕ → 𝕜)
  (p : polynomial 𝕜) (hp0 : p ≠ 0) :
  negligible (λ n, (p.eval n) * f n) ↔ negligible f :=
begin
  refine ⟨λ h, _, _⟩,
  { by_cases hp : 1 ≤ p.degree,
    { have : ∀ᶠ (n : ℕ) in filter.at_top, 1 ≤ ∥polynomial.eval ↑n p∥ :=
        sorry,
        -- (comap_nat_coe_at_top ℝ) ▸ filter.eventually_comap' (poly_help hp 1),
      refine (negligible_of_eventually_le h $ filter.sets_of_superset _ this (λ x hx, _)),
      simp only [normed_field.norm_mul, set.mem_set_of_eq] at ⊢ hx,
      by_cases hfx : f x = 0,
      { simp only [hfx, norm_zero, mul_zero]},
      { refine (le_mul_iff_one_le_left (norm_pos_iff.2 hfx)).2 hx } },
    { replace hp : p.degree ≤ 0,
      { rw not_le at hp,
        contrapose! hp,
        rwa nat.with_bot.one_le_iff_zero_lt },
      have hp_C := polynomial.eq_C_of_degree_le_zero hp,
      have hpc0 : p.coeff 0 ≠ 0 := λ h, hp0 (hp_C.trans (by simp only [h, ring_hom.map_zero])),
      rw [hp_C] at h,
      simpa only [polynomial.eval_C, negligible_const_mul_iff_of_ne_zero _ hpc0] using h } },
  { refine λ h, polynomial.induction_on' p (λ p q hp hq, _) (λ n x, _),
    { simpa [polynomial.eval_add, add_mul] using negligible_add hp hq },
    { simp only [negligible_const_mul_iff, mul_assoc x,
        negligible_pow_mul_iff, polynomial.eval_monomial],
      exact or.inr h, } }
end

end extra_assumption


end asymptotics
