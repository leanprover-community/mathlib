/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import field_theory.abel_ruffini
import analysis.calculus.local_extr
/-!
Construction of an algebraic number that is not solvable by radicals.

The main ingredients are:
 * `solvable_by_rad.is_solvable'` in `field_theory/abel_ruffini` :
  an irreducible polynomial with an `is_solvable_by_rad` root has solvable Galois group
 * `gal_action_hom_bijective_of_prime_degree'` in `field_theory/polynomial_galois_group` :
  an irreducible polynomial of prime degree with 1-3 non-real roots has full Galois group
 * `equiv.perm.not_solvable` in `group_theory/solvable` : the symmetric group is not solvable

Then all that remains is the construction of a specific polynomial satisfying the conditions of
`gal_action_hom_bijective_of_prime_degree'`, which is done in this file.

-/

namespace abel_ruffini

open function polynomial polynomial.gal

local attribute [instance] splits_ℚ_ℂ

variables (R : Type*) [comm_ring R] (a b : ℕ)

/-- A quintic polynomial that we will show is irreducible -/
noncomputable def Φ : polynomial R := X ^ 5 - C ↑a * X + C ↑b

variables {R}

@[simp] lemma map_Phi {S : Type*} [comm_ring S] (f : R →+* S) : (Φ R a b).map f = Φ S a b :=
by simp [Φ]

@[simp] lemma coeff_zero_Phi : (Φ R a b).coeff 0 = ↑b :=
by simp [Φ, coeff_X_pow]

@[simp] lemma coeff_five_Phi : (Φ R a b).coeff 5 = 1 :=
by simp [Φ, coeff_X, coeff_C, -C_eq_nat_cast, -ring_hom.map_nat_cast]

variables [nontrivial R]

lemma degree_Phi : (Φ R a b).degree = ↑5 :=
begin
  suffices : degree (X ^ 5 - C ↑a * X) = ↑5,
  { rwa [Φ, degree_add_eq_left_of_degree_lt],
    rw this,
    exact lt_of_le_of_lt degree_C_le (with_bot.coe_lt_coe.mpr (nat.zero_lt_bit1 2)) },
  rw [degree_sub_eq_left_of_degree_lt, degree_X_pow],
  rw [degree_X_pow, ←pow_one X],
  exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
    (with_bot.coe_lt_coe.mpr (nat.one_lt_bit1 two_ne_zero)),
end

lemma nat_degree_Phi : (Φ R a b).nat_degree = 5 :=
nat_degree_eq_of_degree_eq_some (degree_Phi a b)

lemma leading_coeff_Phi : (Φ R a b).leading_coeff = 1 :=
by rw [leading_coeff, nat_degree_Phi, coeff_five_Phi]

lemma monic_Phi : (Φ R a b).monic :=
leading_coeff_Phi a b

lemma irreducible_Phi (p : ℕ) (hp : p.prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬ (p ^ 2 ∣ b)) :
  irreducible (Φ ℚ a b) :=
begin
  rw [←map_Phi a b (int.cast_ring_hom ℚ), ←is_primitive.int.irreducible_iff_irreducible_map_cast],
  apply irreducible_of_eisenstein_criterion,
  { rwa [ideal.span_singleton_prime (int.coe_nat_ne_zero.mpr hp.ne_zero),
      int.prime_iff_nat_abs_prime] },
  { rw [leading_coeff_Phi, ideal.mem_span_singleton],
    exact_mod_cast mt nat.dvd_one.mp (hp.ne_one) },
  { intros n hn,
    rw ideal.mem_span_singleton,
    rw [degree_Phi, with_bot.coe_lt_coe] at hn,
    interval_cases n with hn;
    simp [Φ, coeff_X_pow, coeff_C, int.coe_nat_dvd.mpr, hpb, hpa, -ring_hom.eq_int_cast] },
  { simp only [degree_Phi, ←with_bot.coe_zero, with_bot.coe_lt_coe, nat.succ_pos'] },
  { rwa [coeff_zero_Phi, pow_two, ideal.span_singleton_mul_span_singleton, ←pow_two,
      ideal.mem_span_singleton, ←int.coe_nat_pow],
    norm_num,
    exact mt int.coe_nat_dvd.mp hp2b },
  all_goals { exact polynomial.monic.is_primitive (monic_Phi a b) },
end

lemma real_roots_Phi_le : fintype.card ((Φ ℚ a b).root_set ℝ) ≤ 3 :=
begin
  rw [←map_Phi a b (algebra_map ℤ ℚ), Φ, ←one_mul (X ^ 5), ←C_1],
  refine (card_root_set_le_derivative _).trans
    (nat.succ_le_succ ((card_root_set_le_derivative _).trans (nat.succ_le_succ _))),
  suffices : ((C ((algebra_map ℤ ℚ) 20) * X ^ 3).root_set ℝ).subsingleton,
  { norm_num [fintype.card_le_one_iff_subsingleton, ← mul_assoc, *] at * },
  rw root_set_C_mul_X_pow; norm_num,
end

lemma real_roots_Phi_ge_aux' (hab : b < a) : (a : ℝ) ^ 2 - a ^ 5 + b ≤ 0 :=
begin
  have h1 : (b : ℝ) + 1 ≤ a := by exact_mod_cast hab,
  have h2 : 1 ≤ (a : ℝ) := nat.one_le_cast.mpr (nat.one_le_of_lt hab),
  calc (a : ℝ) ^ 2 - a ^ 5 + b ≤ a ^ 2 - a ^ 3 + (a - 1) : add_le_add
      (sub_le_sub_left (pow_le_pow h2 (bit1_le_bit1.mpr one_le_two)) _) (le_sub_iff_add_le.mpr h1)
    ... = - ((a - 1) ^ 2 * (a + 1)) : by ring
    ... ≤ 0 : neg_nonpos.mpr (mul_nonneg (pow_two_nonneg _) (by linarith)),
end

lemma real_roots_Phi_ge_aux (hab : b < a) :
  ∃ x y : ℝ, x ≠ y ∧ aeval x (Φ ℚ a b) = 0 ∧ aeval y (Φ ℚ a b) = 0 :=
begin
  let f := λ x : ℝ, aeval x (Φ ℚ a b),
  have hf : f = λ x, x ^ 5 - a * x + b, { simp [f, Φ] },
  have hc : ∀ s : set ℝ, continuous_on f s := λ s, (Φ ℚ a b).continuous_on_aeval,
  have ha : (1 : ℝ) ≤ a := nat.one_le_cast.mpr (nat.one_le_of_lt hab),
  have hle : (0 : ℝ) ≤ 1 := zero_le_one,
  have hf0 : 0 ≤ f 0, { norm_num [hf] },
  by_cases hb : (1 : ℝ) - a + b < 0,
  { have hf1 : f 1 < 0, { norm_num [hf, hb] },
    have hfa : 0 ≤ f a,
    { simp_rw [hf, ← sq],
      refine add_nonneg (sub_nonneg.mpr (pow_le_pow ha _)) _; norm_num },
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Ico' hle (hc _) (set.mem_Ioc.mpr ⟨hf1, hf0⟩),
    obtain ⟨y, ⟨hy1, -⟩, hy2⟩ := intermediate_value_Ioc ha (hc _) (set.mem_Ioc.mpr ⟨hf1, hfa⟩),
    exact ⟨x, y, (hx1.trans hy1).ne, hx2, hy2⟩ },
  { have hb' : (1 : ℝ) - a + b = 0,
    { refine le_antisymm _ (not_lt.mp hb),
      rw [sub_add_eq_add_sub, sub_nonpos, add_comm],
      exact_mod_cast nat.succ_le_iff.mpr hab },
    have hf1 : f 1 = 0, { norm_num [hf, hb'] },
    have hfa : f (-a) ≤ 0, { norm_num [hf, ← sq, real_roots_Phi_ge_aux' a b hab] },
    have ha' := neg_nonpos.mpr (hle.trans ha),
    obtain ⟨x, ⟨-, hx1⟩, hx2⟩ := intermediate_value_Icc ha' (hc _) (set.mem_Icc.mpr ⟨hfa, hf0⟩),
    exact ⟨x, 1, (hx1.trans_lt zero_lt_one).ne, hx2, hf1⟩ },
end

lemma real_roots_Phi_ge (hab : b < a) : 2 ≤ fintype.card ((Φ ℚ a b).root_set ℝ) :=
begin
  have q_ne_zero : Φ ℚ a b ≠ 0 := (monic_Phi a b).ne_zero,
  obtain ⟨x, y, hxy, hx, hy⟩ := real_roots_Phi_ge_aux a b hab,
  have key : ↑({x, y} : finset ℝ) ⊆ (Φ ℚ a b).root_set ℝ,
  { simp [set.insert_subset, mem_root_set q_ne_zero, hx, hy] },
  replace key := fintype.card_le_of_embedding (set.embedding_of_subset _ _ key),
  rwa [fintype.card_coe, finset.card_insert_of_not_mem, finset.card_singleton] at key,
  rwa finset.mem_singleton,
end

lemma complex_roots_Phi (h : (Φ ℚ a b).separable) : fintype.card ((Φ ℚ a b).root_set ℂ) = 5 :=
(card_root_set_eq_nat_degree h (is_alg_closed.splits_codomain _)).trans (nat_degree_Phi a b)

lemma gal_Phi (hab : b < a) (h_irred : irreducible (Φ ℚ a b)) :
  bijective (gal_action_hom (Φ ℚ a b) ℂ) :=
begin
  apply gal_action_hom_bijective_of_prime_degree' h_irred,
  { norm_num [nat_degree_Phi] },
  { rw [complex_roots_Phi a b h_irred.separable, nat.succ_le_succ_iff],
    exact (real_roots_Phi_le a b).trans (nat.le_succ 3) },
  { simp_rw [complex_roots_Phi a b h_irred.separable, nat.succ_le_succ_iff],
    exact real_roots_Phi_ge a b hab },
end

theorem not_solvable_by_rad (p : ℕ) (x : ℂ) (hx : aeval x (Φ ℚ a b) = 0) (hab : b < a)
  (hp : p.prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬ (p ^ 2 ∣ b))  :
  ¬ is_solvable_by_rad ℚ x :=
begin
  have h_irred := irreducible_Phi a b p hp hpa hpb hp2b,
  apply mt (solvable_by_rad.is_solvable' h_irred hx),
  introI h,
  refine equiv.perm.not_solvable _ (le_of_eq _)
    (solvable_of_surjective (gal_Phi a b hab h_irred).2),
  rw_mod_cast [cardinal.fintype_card, complex_roots_Phi a b h_irred.separable],
end

theorem not_solvable_by_rad' (x : ℂ) (hx : aeval x (Φ ℚ 4 2) = 0) :
  ¬ is_solvable_by_rad ℚ x :=
by apply not_solvable_by_rad 4 2 2 x hx; norm_num

theorem exists_not_solvable_by_rad : ∃ x : ℂ, is_algebraic ℚ x ∧ ¬ is_solvable_by_rad ℚ x :=
begin
  obtain ⟨x, hx⟩ := exists_root_of_splits (algebra_map ℚ ℂ)
    (is_alg_closed.splits_codomain (Φ ℚ 4 2))
    (ne_of_eq_of_ne (degree_Phi 4 2) (mt with_bot.coe_eq_coe.mp (nat.bit1_ne_zero 2))),
  exact ⟨x, ⟨Φ ℚ 4 2, (monic_Phi 4 2).ne_zero, hx⟩, not_solvable_by_rad' x hx⟩,
end

end abel_ruffini
