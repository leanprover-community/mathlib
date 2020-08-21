/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import set_theory.game.impartial
import set_theory.ordinal
import data.set
import logic.basic

universes u v

/-!
# Nim and the Sprague-Grundy theorem

This file contains the definition for nim for any ordinal `O`. In the game of `nim O₁` both players
may move to `nim O₂` for any `O₂ < O₁`.
We also define a Grundy value for an impartial game `G` and prove the Sprague-Grundy theorem, that
`G` is equivalent to `nim (Grundy_value G)`.
-/

open pgame

local infix ` ≈ ` := equiv

/-- The definition of single-heap nim, which can be viewed as a pile of stones where each player can
 take a positive number of stones from it on their turn. -/
noncomputable def nim : ordinal → pgame
| O₁ := ⟨ O₁.out.α, O₁.out.α,
  λ O₂, have hwf : (ordinal.typein O₁.out.r O₂) < O₁,
    from begin nth_rewrite_rhs 0 ←ordinal.type_out O₁, exact ordinal.typein_lt_type _ _ end,
    nim (ordinal.typein O₁.out.r O₂),
  λ O₂, have hwf : (ordinal.typein O₁.out.r O₂) < O₁,
    from begin nth_rewrite_rhs 0 ←ordinal.type_out O₁, exact ordinal.typein_lt_type _ _ end,
    nim (ordinal.typein O₁.out.r O₂)⟩
using_well_founded {dec_tac := tactic.assumption}

namespace nim

lemma nim_def (O : ordinal) : nim O = pgame.mk
  O.out.α O.out.α
  (λ O₂, nim (ordinal.typein O.out.r O₂))
  (λ O₂, nim (ordinal.typein O.out.r O₂)) :=
by rw nim

lemma nim_wf_lemma {O₁ : ordinal} (O₂ : O₁.out.α) : (ordinal.typein O₁.out.r O₂) < O₁ :=
begin
  nth_rewrite_rhs 0 ← ordinal.type_out O₁,
  exact ordinal.typein_lt_type _ _
end

lemma nim_impartial : ∀ (O : ordinal), impartial (nim O)
| O :=
begin
  rw [impartial_def, nim_def, neg_def],
  split,
  split,
  { rw pgame.le_def,
    split,
    { intro i,
      let hwf : (ordinal.typein O.out.r i) < O := nim_wf_lemma i,
      left,
      exact ⟨ i, (impartial_neg_equiv_self $ nim_impartial $ ordinal.typein O.out.r i).1 ⟩ },
    { intro j,
      let hwf : (ordinal.typein O.out.r j) < O := nim_wf_lemma j,
      right,
      exact ⟨ j, (impartial_neg_equiv_self $ nim_impartial $ ordinal.typein O.out.r j).1 ⟩ } },
  { rw pgame.le_def,
    split,
    { intro i,
      let hwf : (ordinal.typein O.out.r i) < O := nim_wf_lemma i,
      left,
      exact ⟨ i, (impartial_neg_equiv_self $ nim_impartial $ ordinal.typein O.out.r i).2 ⟩ },
    { intro j,
      let hwf : (ordinal.typein O.out.r j) < O := nim_wf_lemma j,
      right,
      exact ⟨ j, (impartial_neg_equiv_self $ nim_impartial $ ordinal.typein O.out.r j).2 ⟩ } },
  split,
  { intro i,
    let hwf : (ordinal.typein O.out.r i) < O := nim_wf_lemma i,
    rw move_left_mk,
    exact nim_impartial (ordinal.typein O.out.r i) },
  { intro j,
    let hwf : (ordinal.typein O.out.r j) < O := nim_wf_lemma j,
    rw move_right_mk,
    exact nim_impartial (ordinal.typein O.out.r j) }
end
using_well_founded {dec_tac := tactic.assumption}

lemma nim_zero_first_loses : (nim (0:ordinal)).first_loses :=
begin
  rw nim_def,
  split;
  rw le_def_lt;
  split;
  intro i;
  try {rw left_moves_mk at i};
  try {rw right_moves_mk at i};
  try { have h := ordinal.typein_lt_type (quotient.out (0:ordinal)).r i,
    rw ordinal.type_out at h,
    have hcontra := ordinal.zero_le (ordinal.typein (quotient.out (0:ordinal)).r i),
    have h := not_le_of_lt h,
    contradiction };
  try { exact pempty.elim i }
end

lemma nim_non_zero_first_wins (O : ordinal) (hO : O ≠ 0) : (nim O).first_wins :=
begin
  rw nim_def,
  rw ←ordinal.pos_iff_ne_zero at hO,
  split;
  rw lt_def_le,
  { left,
    use (ordinal.principal_seg_out hO).top,
    rw [move_left_mk, ordinal.typein_top, ordinal.type_out],
    exact nim_zero_first_loses.2 },
  { right,
    use (ordinal.principal_seg_out hO).top,
    rw [move_right_mk, ordinal.typein_top, ordinal.type_out],
    exact nim_zero_first_loses.1 }
end

lemma nim_sum_first_loses_iff_eq (O₁ O₂ : ordinal) : (nim O₁ + nim O₂).first_loses ↔ O₁ = O₂ :=
begin
  split,
  { contrapose,
    intros hneq hp,
    wlog h : O₁ ≤ O₂ using [O₁ O₂, O₂ O₁],
    exact ordinal.le_total O₁ O₂,
    { have h : O₁ < O₂ := lt_of_le_of_ne h hneq,
      rw ←(no_good_left_moves_iff_first_loses $ impartial_add (nim_impartial O₁) (nim_impartial O₂))
        at hp,
      equiv_rw left_moves_add (nim O₁) (nim O₂) at hp,
      rw nim_def O₂ at hp,
      specialize hp (sum.inr (ordinal.principal_seg_out h).top),
      rw [id, add_move_left_inr, move_left_mk, ordinal.typein_top, ordinal.type_out] at hp,
      cases hp,
      have hcontra := (impartial_add_self $ nim_impartial O₁).1,
      rw ←pgame.not_lt at hcontra,
      contradiction },
    exact this (λ h, hneq h.symm) (first_loses_of_equiv add_comm_equiv hp) },
  { intro h,
    rw h,
    exact impartial_add_self (nim_impartial O₂) }
end

lemma nim_sum_first_wins_iff_neq (O₁ O₂ : ordinal) : (nim O₁ + nim O₂).first_wins ↔ O₁ ≠ O₂ :=
begin
  split,
  { intros hn heq,
    cases hn,
    rw ←nim_sum_first_loses_iff_eq at heq,
    cases heq with h,
    rw ←pgame.not_lt at h,
    contradiction },
  { contrapose,
    intro hnp,
    rw [not_not, ←nim_sum_first_loses_iff_eq],
    cases impartial_winner_cases (impartial_add (nim_impartial O₁) (nim_impartial O₂)),
    assumption,
    contradiction }
end

/-- This definition will be used in the proof of the Sprague-Grundy theorem. It takes a function
  from some type to ordinals and returns a nonempty set of ordinals with empty intersection with
  the image of the function. It is guaranteed that the smallest ordinal not in the image will be
  in the set, i.e. we can use this to find the mex. -/
def nonmoves {α : Type u} (M : α → ordinal.{u}) : set ordinal.{u} :=
  { O : ordinal | ¬ ∃ a : α, M a = O }

lemma nonmoves_nonempty {α : Type u} (M : α → ordinal.{u}) : ∃ O : ordinal, O ∈ nonmoves M :=
begin
  classical,
  by_contra h,
  rw nonmoves at h,
  simp only [not_exists, not_forall, set.mem_set_of_eq, not_not] at h,

  have hle : cardinal.univ.{u (u+1)} ≤ cardinal.lift.{u (u+1)} (cardinal.mk α),
  { split,
    fconstructor,
    { rintro ⟨ O ⟩,
      exact ⟨ (classical.indefinite_description _ $ h O).val ⟩ },
    { rintros ⟨ O₁ ⟩ ⟨ O₂ ⟩ heq,
      ext,
      transitivity,
      symmetry,
      exact (classical.indefinite_description _ (h O₁)).prop,
      injection heq with heq,
      rw subtype.val_eq_coe at heq,
      rw heq,
      exact (classical.indefinite_description _ (h O₂)).prop } },

  have hlt : cardinal.lift.{u (u+1)} (cardinal.mk α) < cardinal.univ.{u (u+1)} :=
    cardinal.lt_univ.2 ⟨ cardinal.mk α, rfl ⟩,

  cases hlt,
  contradiction
end

/-- The Grundy value of an impartial game, the ordinal which corresponds to the game of nim that the
 game is equivalent to -/
noncomputable def Grundy_value : Π {G : pgame.{u}}, G.impartial → ordinal.{u}
| G :=
  λ hG, ordinal.omin (nonmoves (λ i, Grundy_value $ impartial_move_left_impartial hG i))
    (nonmoves_nonempty (λ i, Grundy_value (impartial_move_left_impartial hG i)))
using_well_founded {dec_tac := pgame_wf_tac}

lemma Grundy_value_def {G : pgame} (hG : G.impartial) :
Grundy_value hG = ordinal.omin (nonmoves (λ i, (Grundy_value $ impartial_move_left_impartial hG i)))
  (nonmoves_nonempty (λ i, Grundy_value (impartial_move_left_impartial hG i))) :=
begin
  rw Grundy_value,
  refl
end

/-- The Sprague-Grundy theorem which states that every impartial game is equivalent to a game of
 nim, namely the game of nim corresponding to the games Grundy value -/
theorem Sprague_Grundy : ∀ {G : pgame.{u}} (hG : G.impartial), G ≈ nim (Grundy_value hG)
| G :=
begin
  classical,
  intro hG,
  rw [equiv_iff_sum_first_loses hG (nim_impartial _),
    ←no_good_left_moves_iff_first_loses (impartial_add hG (nim_impartial _))],
  intro i,
  equiv_rw left_moves_add G (nim $ Grundy_value hG) at i,
  cases i with i₁ i₂,
  { rw add_move_left_inl,
    apply first_wins_of_equiv,
    exact (add_congr (Sprague_Grundy $ impartial_move_left_impartial hG i₁).symm (equiv_refl _)),
    rw nim_sum_first_wins_iff_neq,
    intro heq,
    have heq := symm heq,
    rw Grundy_value_def hG at heq,
    have h := ordinal.omin_mem
      (nonmoves (λ (i : G.left_moves), Grundy_value (impartial_move_left_impartial hG i)))
      (nonmoves_nonempty _),
    rw heq at h,
    have hcontra : ∃ (i' : G.left_moves),
      (λ (i'' : G.left_moves), Grundy_value $ impartial_move_left_impartial hG i'') i' =
        Grundy_value (impartial_move_left_impartial hG i₁) :=
      ⟨ i₁, rfl ⟩,
    contradiction },
  { rw [add_move_left_inr,
    ←good_left_move_iff_first_wins
      (impartial_add hG $ impartial_move_left_impartial (nim_impartial _) _)],
    revert i₂,
    rw nim_def,
    intro i₂,

    have h' : ∃ i : G.left_moves, (Grundy_value $ impartial_move_left_impartial hG i) =
      ordinal.typein (quotient.out $ Grundy_value hG).r i₂,
    { have hlt : ordinal.typein (quotient.out $ Grundy_value hG).r i₂ <
        ordinal.type (quotient.out $ Grundy_value hG).r :=
        ordinal.typein_lt_type _ _,
      rw ordinal.type_out at hlt,
      revert i₂ hlt,
      rw Grundy_value_def,
      intros i₂ hlt,
      have hnotin :
        ordinal.typein (quotient.out (ordinal.omin
        (nonmoves (λ i, Grundy_value (impartial_move_left_impartial hG i))) _)).r i₂ ∉
        (nonmoves (λ (i : G.left_moves), Grundy_value (impartial_move_left_impartial hG i))),
      { intro hin,
        have hge := ordinal.omin_le hin,
        have hcontra := (le_not_le_of_lt hlt).2,
        contradiction },
      unfold nonmoves at hnotin,
      simpa using hnotin },

    cases h' with i hi,
    use (left_moves_add _ _).symm (sum.inl i),
    rw [add_move_left_inl, move_left_mk],
    apply first_loses_of_equiv,
    apply add_congr,
    symmetry,
    exact Sprague_Grundy (impartial_move_left_impartial hG i),
    refl,
    rw hi,
    exact impartial_add_self (nim_impartial _) }
end
using_well_founded {dec_tac := pgame_wf_tac}

end nim
