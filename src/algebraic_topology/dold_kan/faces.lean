/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.homotopies
import data.nat.parity
import tactic.ring_exp

/-!

# Study of face maps for the Dold-Kan correspondence

TODO (@joelriou) continue adding the various files references below

In this file, we obtain the technical lemmas that are used in the file
`projections.lean` in order to get basic properties of the endomorphisms
`P q : K[X] ⟶ K[X]` with respect to face maps (see `homotopies.lean` for the
role of these endomorphisms in the overall strategy of proof).

The main lemma in this file is `higher_faces_vanish.induction`. It is based
on two technical lemmas `higher_faces_vanish.comp_Hσ_eq` and
`higher_faces_vanish.comp_Hσ_eq_zero`.

-/

open nat
open category_theory
open category_theory.limits
open category_theory.category
open category_theory.preadditive
open category_theory.simplicial_object
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]
variables {X : simplicial_object C}

/-- A morphism `φ : Y ⟶ X _[n+1]` satisfies `higher_faces_vanish q φ`
when the compositions `φ ≫ X.δ j` are `0` for `j ≥ max 1 (n+2-q)`. When `q ≤ n+1`,
it basically means that the composition `φ ≫ X.δ j` are `0` for the `q` highest
possible values of a nonzero `j`. Otherwise, when `q ≥ n+2`, all the compositions
`φ ≫ X.δ j` for nonzero `j` vanish. See also the lemma `comp_P_eq_self_iff` in
`projections.lean` which states that `higher_faces_vanish q φ` is equivalent to
the identity `φ ≫ (P q).f (n+1) = φ`. -/
def higher_faces_vanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n+1]) : Prop :=
∀ (j : fin (n+1)), (n+1 ≤ (j : ℕ) + q) → φ ≫ X.δ j.succ = 0

namespace higher_faces_vanish

lemma of_succ {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish (q+1) φ) : higher_faces_vanish q φ :=
λ j hj, v j (by simpa only [← add_assoc] using le_add_right hj)

lemma of_comp {Y Z : C} {q n : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) (f : Z ⟶ Y) :
  higher_faces_vanish q (f ≫ φ) := λ j hj,
by rw [assoc, v j hj, comp_zero]

lemma comp_Hσ_eq {Y : C} {n a q : ℕ} (hnaq : n=a+q) {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) =
  - φ ≫ X.δ ⟨a+1, nat.succ_lt_succ (nat.lt_succ_iff.mpr (nat.le.intro hnaq.symm))⟩ ≫
    X.σ ⟨a, nat.lt_succ_iff.mpr (nat.le.intro hnaq.symm)⟩ :=
begin
  have hnaq_shift : Π d : ℕ, n+d=(a+d)+q,
  { intro d, rw [add_assoc, add_comm d, ← add_assoc, hnaq], },
  rw [Hσ, homotopy.null_homotopic_map'_f (c_mk (n+2) (n+1) rfl) (c_mk (n+1) n rfl),
    hσ'_eq hnaq (c_mk (n+1) n rfl), hσ'_eq (hnaq_shift 1) (c_mk (n+2) (n+1) rfl)],
  simp only [alternating_face_map_complex.obj_d_eq, eq_to_hom_refl,
    comp_id, comp_sum, sum_comp, comp_add],
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul],
  /- cleaning up the first sum -/
  rw [← fin.sum_congr' _ (hnaq_shift 2).symm, fin.sum_trunc], swap,
  { rintro ⟨k, hk⟩,
    suffices : φ ≫ X.δ (⟨a+2+k, by linarith⟩ : fin (n+2)) = 0,
    { simp only [this, fin.nat_add_mk, fin.cast_mk, zero_comp, smul_zero], },
    convert v ⟨a+k+1, by linarith⟩ (by { rw fin.coe_mk, linarith, }),
    rw [nat.succ_eq_add_one],
    linarith, },
  /- cleaning up the second sum -/
  rw [← fin.sum_congr' _ (hnaq_shift 3).symm, @fin.sum_trunc _ _ (a+3)], swap,
  { rintros ⟨k, hk⟩,
    suffices : φ ≫ X.σ ⟨a+1, by linarith⟩ ≫ X.δ ⟨a+3+k, by linarith⟩ = 0,
    { dsimp, rw [assoc, this, smul_zero], },
    let i : fin (n+1) := ⟨a+1+k, by linarith⟩,
    have h : fin.cast_succ (⟨a+1, by linarith⟩ : fin (n+1)) < i.succ,
    { simp only [fin.lt_iff_coe_lt_coe, fin.cast_succ_mk, fin.coe_mk, fin.succ_mk],
      linarith, },
    have δσ_rel := δ_comp_σ_of_gt X h,
    conv_lhs at δσ_rel
    { simp only [fin.cast_succ_mk, fin.succ_mk, show a+1+k+1+1 = a+3+k, by linarith], },
      rw [δσ_rel, ← assoc, v i, zero_comp],
    simp only [i, fin.coe_mk],
    linarith, },
  /- leaving out three specific terms -/
  conv_lhs { congr, skip, rw [fin.sum_univ_cast_succ, fin.sum_univ_cast_succ], },
  rw fin.sum_univ_cast_succ,
  simp only [fin.last, fin.cast_le_mk, fin.coe_cast, fin.cast_mk,
    fin.coe_cast_le, fin.coe_mk, fin.cast_succ_mk, fin.coe_cast_succ],
  /- the purpose of the following `simplif` is to create three subgoals in order
    to finish the proof -/
  have simplif : ∀ (a b c d e f : Y ⟶ X _[n+1]), b=f → d+e=0 → c+a=0 → a+b+(c+d+e) = f,
  { intros a b c d e f h1 h2 h3,
    rw [add_assoc c d e, h2, add_zero, add_comm a b, add_assoc,
      add_comm a c, h3, add_zero, h1], },
  apply simplif,
  { /- b=f -/
    rw [← pow_add, odd.neg_one_pow, neg_smul, one_zsmul],
    use a,
    linarith, },
  { /- d+e = 0 -/
    let b : fin (n+2) := ⟨a+1, by linarith⟩,
    have eq₁ : X.σ b ≫ X.δ (fin.cast_succ b) = 𝟙 _ := δ_comp_σ_self _,
    have eq₂ : X.σ b ≫ X.δ b.succ = 𝟙 _ := δ_comp_σ_succ _,
    simp only [b, fin.cast_succ_mk, fin.succ_mk] at eq₁ eq₂,
    simp only [eq₁, eq₂, fin.last, assoc, fin.cast_succ_mk, fin.cast_le_mk, fin.coe_mk,
      comp_id, add_eq_zero_iff_eq_neg, ← neg_zsmul],
    congr,
    ring_exp,
    rw mul_one, },
  { /- c+a = 0 -/
    rw ← finset.sum_add_distrib,
    apply finset.sum_eq_zero,
    rintros ⟨i, hi⟩ h₀,
    have hia : (⟨i, by linarith⟩ : fin (n+2)) ≤ fin.cast_succ (⟨a, by linarith⟩ : fin (n+1)) :=
      by simpa only [fin.le_iff_coe_le_coe, fin.coe_mk, fin.cast_succ_mk, ← lt_succ_iff] using hi,
    simp only [fin.coe_mk, fin.cast_le_mk, fin.cast_succ_mk, fin.succ_mk, assoc, fin.cast_mk,
      ← δ_comp_σ_of_le X hia, add_eq_zero_iff_eq_neg, ← neg_zsmul],
    congr,
    ring_exp, },
end

lemma comp_Hσ_eq_zero {Y : C} {n q : ℕ} (hqn : n<q) {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : φ ≫ (Hσ q).f (n+1) = 0 :=
begin
  simp only [Hσ, homotopy.null_homotopic_map'_f (c_mk (n+2) (n+1) rfl) (c_mk (n+1) n rfl)],
  rw [hσ'_eq_zero hqn (c_mk (n+1) n rfl), comp_zero, zero_add],
  by_cases hqn' : n+1<q,
  { rw [hσ'_eq_zero hqn' (c_mk (n+2) (n+1) rfl), zero_comp, comp_zero], },
  { simp only [hσ'_eq (show n+1=0+q, by linarith) (c_mk (n+2) (n+1) rfl),
      pow_zero, fin.mk_zero, one_zsmul, eq_to_hom_refl, comp_id,
      comp_sum, alternating_face_map_complex.obj_d_eq],
    rw [← fin.sum_congr' _ (show 2+(n+1)=n+1+2, by linarith), fin.sum_trunc],
    { simp only [fin.sum_univ_cast_succ, fin.sum_univ_zero, zero_add, fin.last,
        fin.cast_le_mk, fin.cast_mk, fin.cast_succ_mk],
      simp only [fin.mk_zero, fin.coe_zero, pow_zero, one_zsmul, fin.mk_one,
        fin.coe_one, pow_one, neg_smul, comp_neg],
      erw [δ_comp_σ_self, δ_comp_σ_succ, add_right_neg], },
    { intro j,
      simp only [comp_zsmul],
      convert zsmul_zero _,
      have h : fin.cast (by rw add_comm 2) (fin.nat_add 2 j) = j.succ.succ,
      { ext, simp only [add_comm 2, fin.coe_cast, fin.coe_nat_add, fin.coe_succ], },
      rw [h, ← fin.cast_succ_zero, δ_comp_σ_of_gt X], swap,
      { exact fin.succ_pos j, },
      simp only [← assoc, v j (by linarith), zero_comp], }, },
end

lemma induction {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n+1]}
  (v : higher_faces_vanish q φ) : higher_faces_vanish (q+1) (φ ≫ (𝟙 _ + Hσ q).f (n+1)) :=
begin
  intros j hj₁,
  dsimp,
  simp only [comp_add, add_comp, comp_id],
  -- when n < q, the result follows immediately from the assumption
  by_cases hqn : n<q,
  { rw [comp_Hσ_eq_zero hqn v, zero_comp, add_zero, v j (by linarith)], },
  -- we now assume that n≥q, and write n=a+q
  cases nat.le.dest (not_lt.mp hqn) with a ha,
  rw [comp_Hσ_eq (show n=a+q, by linarith) v, neg_comp, add_neg_eq_zero, assoc, assoc],
  cases n with m hm,
  -- the boundary case n=0
  { simpa only [nat.eq_zero_of_add_eq_zero_left ha, fin.eq_zero j,
      fin.mk_zero, fin.mk_one, δ_comp_σ_succ, comp_id], },
  -- in the other case, we need to write n as m+1
  -- then, we first consider the particular case j = a
  by_cases hj₂ : a = (j : ℕ),
  { simp only [hj₂, fin.eta, δ_comp_σ_succ, comp_id],
    congr,
    ext,
    simp only [fin.coe_succ, fin.coe_mk], },
  -- now, we assume j ≠ a (i.e. a < j)
  have haj : a<j := (ne.le_iff_lt hj₂).mp (by linarith),
  have hj₃ := j.is_lt,
  have ham : a≤m,
  { by_contradiction,
    rw [not_le, ← nat.succ_le_iff] at h,
    linarith, },
  have ineq₁ : (fin.cast_succ (⟨a, nat.lt_succ_iff.mpr ham⟩ : fin (m+1)) < j),
  { rw fin.lt_iff_coe_lt_coe, exact haj, },
  have eq₁ := δ_comp_σ_of_gt X ineq₁,
  rw fin.cast_succ_mk at eq₁,
  rw eq₁,
  obtain (ham' | ham'') := ham.lt_or_eq,
  { -- case where `a<m`
    have ineq₂ : (fin.cast_succ (⟨a+1, nat.succ_lt_succ ham'⟩ : fin (m+1)) ≤ j),
    { simpa only [fin.le_iff_coe_le_coe] using nat.succ_le_iff.mpr haj, },
    have eq₂ := δ_comp_δ X ineq₂,
    simp only [fin.cast_succ_mk] at eq₂,
    slice_rhs 2 3 { rw ← eq₂, },
    simp only [← assoc, v j (by linarith), zero_comp], },
  { -- in the last case, a=m, q=1 and j=a+1
    have hq : q=1 := by rw [← add_left_inj a, ha, ham'', add_comm],
    have hj₄ : (⟨a+1, by linarith⟩ : fin (m+3)) = fin.cast_succ j,
    { ext,
      simp only [fin.coe_mk, fin.coe_cast_succ],
      linarith, },
    slice_rhs 2 3 { rw [hj₄, δ_comp_δ_self], },
    simp only [← assoc, v j (by linarith), zero_comp], },
end

end higher_faces_vanish

end dold_kan

end algebraic_topology
