/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/

import set_theory.game.basic
import tactic.nth_rewrite.default

/-!
# Basic definitions about impartial (pre-)games

We will define an impartial game, one in which left and right can make exactly the same moves.
Our definition differs slightly by saying that the game is always equivalent to its negative,
no matter what moves are played. This allows for games such as poker-nim to be classifed as
impartial.
-/

universe u

namespace pgame

local infix ` ⧏ `:50 := lf
local infix ` ≈ ` := equiv
local infix ` ∥ `:50 := fuzzy

/-- The definition for a impartial game, defined using Conway induction. -/
def impartial_aux : pgame → Prop
| G := G ≈ -G ∧ (∀ i, impartial_aux (G.move_left i)) ∧ ∀ j, impartial_aux (G.move_right j)
using_well_founded { dec_tac := pgame_wf_tac }

lemma impartial_aux_def {G : pgame} : G.impartial_aux ↔ G ≈ -G ∧
  (∀ i, impartial_aux (G.move_left i)) ∧ ∀ j, impartial_aux (G.move_right j) :=
by rw impartial_aux

/-- A typeclass on impartial games. -/
class impartial (G : pgame) : Prop := (out : impartial_aux G)

lemma impartial_iff_aux {G : pgame} : G.impartial ↔ G.impartial_aux :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma impartial_def {G : pgame} : G.impartial ↔ G ≈ -G ∧
  (∀ i, impartial (G.move_left i)) ∧ ∀ j, impartial (G.move_right j) :=
by simpa only [impartial_iff_aux] using impartial_aux_def

namespace impartial

instance impartial_zero : impartial 0 :=
by { rw impartial_def, dsimp, simp }

instance impartial_star : impartial star :=
by { rw impartial_def, simpa using impartial.impartial_zero }

lemma neg_equiv_self (G : pgame) [h : G.impartial] : G ≈ -G := (impartial_def.1 h).1

@[simp] lemma mk_neg_equiv_self (G : pgame) [h : G.impartial] : -⟦G⟧ = ⟦G⟧ :=
quot.sound (neg_equiv_self G).symm

instance move_left_impartial {G : pgame} [h : G.impartial] (i : G.left_moves) :
  (G.move_left i).impartial :=
(impartial_def.1 h).2.1 i

instance move_right_impartial {G : pgame} [h : G.impartial] (j : G.right_moves) :
  (G.move_right j).impartial :=
(impartial_def.1 h).2.2 j

theorem impartial_congr : ∀ {G H : pgame} (e : relabelling G H) [G.impartial], H.impartial
| G H e := begin
  introI h,
  rw impartial_def,
  refine ⟨equiv_trans e.symm.equiv (equiv_trans (neg_equiv_self G) (neg_congr e.equiv)),
    λ i, _, λ j, _⟩;
  cases e with _ _ L R hL hR,
  { convert impartial_congr (hL (L.symm i)),
    rw equiv.apply_symm_apply },
  { exact impartial_congr (hR j) }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance impartial_add : ∀ (G H : pgame) [G.impartial] [H.impartial], (G + H).impartial
| G H :=
begin
  introsI hG hH,
  rw impartial_def,
  refine ⟨equiv_trans (add_congr (neg_equiv_self _) (neg_equiv_self _))
    (neg_add_relabelling _ _).equiv.symm, λ i, _, λ i, _⟩,
  { rcases left_moves_add_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩,
    all_goals
    { simp only [add_move_left_inl, add_move_left_inr],
      apply impartial_add } },
  { rcases right_moves_add_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩,
    all_goals
    { simp only [add_move_right_inl, add_move_right_inr],
      apply impartial_add } }
end
using_well_founded { dec_tac := pgame_wf_tac }

instance impartial_neg : ∀ (G : pgame) [G.impartial], (-G).impartial
| G :=
begin
  introI hG,
  rw impartial_def,
  refine ⟨_, λ i, _, λ i, _⟩,
  { rw neg_neg,
    exact (neg_equiv_self G).symm },
  { rw move_left_neg',
    apply impartial_neg },
  { rw move_right_neg',
    apply impartial_neg }
end
using_well_founded { dec_tac := pgame_wf_tac }

variables (G : pgame) [impartial G]

lemma nonpos : ¬ 0 < G :=
λ h, begin
  have h' := neg_lt_iff.2 h,
  rw [pgame.neg_zero, lt_congr_left (equiv_symm (neg_equiv_self G))] at h',
  exact (h.trans h').false
end

lemma nonneg : ¬ G < 0 :=
λ h, begin
  have h' := neg_lt_iff.2 h,
  rw [pgame.neg_zero, lt_congr_right (equiv_symm (neg_equiv_self G))] at h',
  exact (h.trans h').false
end

lemma equiv_or_fuzzy_zero : G ≈ 0 ∨ G ∥ 0 :=
begin
  rcases lt_or_equiv_or_gt_or_fuzzy G 0 with h | h | h | h,
  { exact ((nonneg G) h).elim },
  { exact or.inl h },
  { exact ((nonpos G) h).elim },
  { exact or.inr h }
end

@[simp] lemma not_equiv_zero_iff : ¬ G ≈ 0 ↔ G ∥ 0 :=
⟨(equiv_or_fuzzy_zero G).resolve_left, fuzzy.not_equiv⟩

@[simp] lemma not_fuzzy_zero_iff : ¬ G ∥ 0 ↔ G ≈ 0 :=
⟨(equiv_or_fuzzy_zero G).resolve_right, equiv.not_fuzzy⟩

lemma add_self : G + G ≈ 0 :=
equiv_trans (add_congr_left (neg_equiv_self G)) (add_left_neg_equiv G)

@[simp] lemma mk_add_self : ⟦G⟧ + ⟦G⟧ = 0 := quot.sound (add_self G)

/-- This lemma doesn't require `H` to be impartial. -/
lemma equiv_iff_add_equiv_zero (H : pgame) : H ≈ G ↔ H + G ≈ 0 :=
begin
  rw [←game.mk_eq, ←game.mk_eq, ←@add_right_cancel_iff _ _ (-⟦G⟧)],
  simp,
  exact iff.rfl
end

/-- This lemma doesn't require `H` to be impartial. -/
lemma equiv_iff_add_equiv_zero' (H : pgame) : G ≈ H ↔ G + H ≈ 0 :=
begin
  rw [←game.mk_eq, ←game.mk_eq, ←@add_left_cancel_iff _ _ (-⟦G⟧), eq_comm],
  simp,
  exact iff.rfl
end

lemma le_zero_iff {G : pgame} [G.impartial] : G ≤ 0 ↔ 0 ≤ G :=
by rw [←zero_le_neg_iff, le_congr_right (neg_equiv_self G)]

lemma lf_zero_iff {G : pgame} [G.impartial] : G ⧏ 0 ↔ 0 ⧏ G :=
by rw [←zero_lf_neg_iff, lf_congr_right (neg_equiv_self G)]

lemma equiv_zero_iff_le: G ≈ 0 ↔ G ≤ 0 := ⟨and.left, λ h, ⟨h, le_zero_iff.1 h⟩⟩
lemma fuzzy_zero_iff_lf : G ∥ 0 ↔ G ⧏ 0 := ⟨and.left, λ h, ⟨h, lf_zero_iff.1 h⟩⟩
lemma equiv_zero_iff_ge : G ≈ 0 ↔ 0 ≤ G := ⟨and.right, λ h, ⟨le_zero_iff.2 h, h⟩⟩
lemma fuzzy_zero_iff_gf : G ∥ 0 ↔ 0 ⧏ G := ⟨and.right, λ h, ⟨lf_zero_iff.2 h, h⟩⟩

lemma forall_left_moves_fuzzy_iff_equiv_zero : (∀ i, G.move_left i ∥ 0) ↔ G ≈ 0 :=
begin
  refine ⟨λ hb, _, λ hp i, _⟩,
  { rw [equiv_zero_iff_le G, le_zero_lf],
    exact λ i, (hb i).1 },
  { rw fuzzy_zero_iff_lf,
    exact move_left_lf_of_le i hp.1 }
end

lemma forall_right_moves_fuzzy_iff_equiv_zero : (∀ j, G.move_right j ∥ 0) ↔ G ≈ 0 :=
begin
  refine ⟨λ hb, _, λ hp i, _⟩,
  { rw [equiv_zero_iff_ge G, zero_le_lf],
    exact λ i, (hb i).2 },
  { rw fuzzy_zero_iff_gf,
    exact lf_move_right_of_le i hp.2 }
end

lemma exists_left_move_equiv_iff_fuzzy_zero : (∃ i, G.move_left i ≈ 0) ↔ G ∥ 0 :=
begin
  refine ⟨λ ⟨i, hi⟩, (fuzzy_zero_iff_gf G).2 (lf_of_le_move_left hi.2), λ hn, _⟩,
  rw [fuzzy_zero_iff_gf G, zero_lf_le] at hn,
  cases hn with i hi,
  exact ⟨i, (equiv_zero_iff_ge _).2 hi⟩
end

lemma exists_right_move_equiv_iff_fuzzy_zero : (∃ j, G.move_right j ≈ 0) ↔ G ∥ 0 :=
begin
  refine ⟨λ ⟨i, hi⟩, (fuzzy_zero_iff_lf G).2 (lf_of_move_right_le hi.1), λ hn, _⟩,
  rw [fuzzy_zero_iff_lf G, lf_zero_le] at hn,
  cases hn with i hi,
  exact ⟨i, (equiv_zero_iff_le _).2 hi⟩
end

end impartial
end pgame
