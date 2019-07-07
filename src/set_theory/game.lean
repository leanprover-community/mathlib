/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Isabel Longbottom, Scott Morrison

The basic theory of combinatorial games. The surreal numbers will be built as a subtype.
-/
import tactic.interactive data.nat.cast data.equiv.basic logic.embedding
import data.fintype

universes u

@[simp] lemma equiv.refl_symm {α : Type u} (a : α) : (equiv.refl α).symm a = a := rfl
@[simp] lemma equiv.sum_congr_symm {α β γ δ : Type u} (e : α ≃ β) (f : γ ≃ δ) (x) :
  (equiv.sum_congr e f).symm x = (equiv.sum_congr (e.symm) (f.symm)) x :=
begin
  induction e, induction f,
  dsimp [equiv.sum_congr, equiv.symm],
  cases x; refl,
end

/-- The type of pre-games, before we have quotiented
  by extensionality. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a pre-game is built
  inductively from two families of pre-games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC. -/
inductive pgame : Type (u+1)
| mk : ∀ α β : Type u, (α → pgame) → (β → pgame) → pgame

namespace pgame

def left_moves : pgame → Type u
| (mk l _ _ _) := l
def right_moves : pgame → Type u
| (mk _ r _ _) := r

def move_left : Π (g : pgame), left_moves g → pgame
| (mk l _ L _) i := L i
def move_right : Π (g : pgame), right_moves g → pgame
| (mk _ r _ R) j := R j

@[simp] lemma left_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).left_moves = xl := rfl
@[simp] lemma move_left_mk {xl xr xL xR i} : (⟨xl, xr, xL, xR⟩ : pgame).move_left i = xL i := rfl
@[simp] lemma right_moves_mk {xl xr xL xR} : (⟨xl, xr, xL, xR⟩ : pgame).right_moves = xr := rfl
@[simp] lemma move_right_mk {xl xr xL xR j} : (⟨xl, xr, xL, xR⟩ : pgame).move_right j = xR j := rfl

inductive r : pgame → pgame → Prop
| left : Π (x : pgame) (i : x.left_moves), r (x.move_left i) x
| right : Π (x : pgame) (j : x.right_moves), r (x.move_right j) x
| trans : Π (x y z : pgame), r x y → r y z → r x z

def r.left_move {xl xr} {xL : xl → pgame} {xR : xr → pgame} {i : xl} : r (xL i) (mk xl xr xL xR) :=
r.left (mk xl xr xL xR) (by { convert i, refl })
def r.right_move {xl xr} {xL : xl → pgame} {xR : xr → pgame} {j : xr} : r (xR j) (mk xl xr xL xR) :=
r.right (mk xl xr xL xR) (by { convert j, refl })

theorem wf_r : well_founded r :=
⟨λ x, begin
  induction x with l r L R IHl IHr,
  refine ⟨_, λ y h, _⟩,
  generalize_hyp e : mk l r L R = x at h,
  induction h with _ i _ j a b _ h1 h2 IH1 IH2; subst e,
  { apply IHl },
  { apply IHr },
  { exact acc.inv (IH2 rfl) h1 }
end⟩

instance : has_well_founded pgame :=
{ r := r,
  wf := wf_r }

-- FIXME, ugh, the current implementation of `solve_by_elim` apparently only uses each passed lemma
-- once. We cheat for now by repeating some of the lemmas!!
meta def pgame_wf_tac :=
`[solve_by_elim
  [psigma.lex.left, psigma.lex.left, psigma.lex.right, psigma.lex.right, r.left_move, r.right_move, r.left, r.right, r.trans]
  { max_rep := 10 }]

-- This is is just a temporary test to check pgame_wf_tac is working.
example {xl xr xL xR yl yr yL yR zl zr} {zL : zl → pgame} {zR} {i : zl} :
  has_well_founded.r
    (⟨mk xl xr xL xR, ⟨mk yl yr yL yR, zL i⟩⟩ : Σ' (g : pgame), Σ' (h : pgame), pgame)
    (⟨mk xl xr xL xR, ⟨mk yl yr yL yR, mk zl zr zL zR⟩⟩ : Σ' (g : pgame), Σ' (h : pgame), pgame) :=
begin
  -- apply psigma.lex.right,
  -- apply psigma.lex.right,
  -- apply r.left',
  pgame_wf_tac
end

/-- The pre-surreal zero is defined by `0 = { | }`. -/
instance : has_zero pgame := ⟨⟨pempty, pempty, pempty.elim, pempty.elim⟩⟩

@[simp] lemma zero_left_moves : (0 : pgame).left_moves = pempty := rfl
@[simp] lemma zero_right_moves : (0 : pgame).right_moves = pempty := rfl

/-- The pre-surreal one is defined by `1 = { 0 | }`. -/
instance : has_one pgame := ⟨⟨punit, pempty, λ _, 0, pempty.elim⟩⟩

@[simp] lemma one_left_moves : (1 : pgame).left_moves = punit := rfl
@[simp] lemma one_move_left : (1 : pgame).move_left punit.star = 0 := rfl
@[simp] lemma one_right_moves : (1 : pgame).right_moves = pempty := rfl

/-- Define simultaneously by mutual induction the `<=` and `<`
  relation on games. The ZFC definition says that `x = {xL | xR}`
  is less or equal to `y = {yL | yR}` if `∀ x₁ ∈ xL, x₁ < y`
  and `∀ y₂ ∈ yR, x < y₂`, where `x < y` is the same as `¬ y <= x`.
  This is a tricky induction because it only decreases one side at
  a time, and it also swaps the arguments in the definition of `<`.
  So we define `x < y` and `x <= y` simultaneously. -/
def le_lt (x y : pgame) : Prop × Prop :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  exact ((∀ i, (IHxl i ⟨yl, yr, yL, yR⟩).2) ∧ (∀ i, (IHyr i).2),
         (∃ i, (IHxr i ⟨yl, yr, yL, yR⟩).1) ∨ (∃ i, (IHyl i).1))
end

instance : has_le pgame := ⟨λ x y, (le_lt x y).1⟩
instance : has_lt pgame := ⟨λ x y, (le_lt x y).2⟩

/-- Definition of `x ≤ y` on pre-games built using the constructor. -/
@[simp] theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) ≤ ⟨yl, yr, yL, yR⟩ ↔
  (∀ i, xL i < ⟨yl, yr, yL, yR⟩) ∧
  (∀ i, (⟨xl, xr, xL, xR⟩ : pgame) < yR i) := iff.rfl

/-- Definition of `x ≤ y` on pre-games, in terms of `<` -/
theorem le_def_lt {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves, x.move_left i < y) ∧
  (∀ j : y.right_moves, x < y.move_right j) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  simp,
  refl,
end

/-- Definition of `x < y` on pre-games built using the constructor. -/
@[simp] theorem mk_lt_mk {xl xr xL xR yl yr yL yR} :
  (⟨xl, xr, xL, xR⟩ : pgame) < ⟨yl, yr, yL, yR⟩ ↔
  (∃ j, xR j ≤ ⟨yl, yr, yL, yR⟩) ∨
  (∃ i, (⟨xl, xr, xL, xR⟩ : pgame) ≤ yL i) := iff.rfl

/-- Definition of `x < y` on pre-games, in terms of `≤` -/
theorem lt_def_le {x y : pgame} : x < y ↔
  (∃ j : x.right_moves, x.move_right j ≤ y) ∨
  (∃ i : y.left_moves, x ≤ y.move_left i) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  simp,
  refl,
end

theorem le_def {x y : pgame} : x ≤ y ↔
  (∀ i : x.left_moves,
   (∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ y) ∨
   (∃ i' : y.left_moves, (x.move_left i) ≤ (y.move_left i'))) ∧
  (∀ j : y.right_moves,
   (∃ j' : x.right_moves, x.move_right j' ≤ (y.move_right j)) ∨
   (∃ i : (y.move_right j).left_moves, x ≤ (y.move_right j).move_left i)) :=
begin
  rw [le_def_lt],
  conv { to_lhs, simp [lt_def_le] },
end

-- TODO corresponding lt_def

theorem forall_pempty {P : pempty → Prop} : (∀ x : pempty, P x) ↔ true :=
begin
  constructor,
  { intro h, trivial, },
  { rintros _ ⟨ ⟩, }
end
theorem exists_pempty {P : pempty → Prop} : (∃ x : pempty, P x) ↔ false :=
begin
  constructor,
  { rintro ⟨⟨ ⟩⟩ },
  { rintro ⟨ ⟩ },
end

theorem le_zero {x : pgame} : x ≤ 0 ↔
  ∀ i : x.left_moves, ∃ j : (x.move_left i).right_moves, (x.move_left i).move_right j ≤ 0 :=
begin
  rw le_def,
  conv { to_lhs, congr, skip, erw [forall_pempty], },
  rw [and_true],
  constructor,
  { intros h i,
    have hi := h i,
    erw exists_pempty at hi,
    simpa using hi, },
  { intros h i,
    erw exists_pempty,
    rw [or_false],
    exact h i }
end

theorem zero_le {x : pgame} : 0 ≤ x ↔
  ∀ j : x.right_moves, ∃ i : (x.move_right j).left_moves, 0 ≤ (x.move_right j).move_left i :=
begin
  rw le_def,
  conv { to_lhs, congr, erw [forall_pempty], },
  rw [true_and],
  constructor,
  { intros h j,
    have hj := h j,
    erw exists_pempty at hj,
    simpa using hj, },
  { intros h j,
    erw exists_pempty,
    rw [false_or],
    exact h j }
end

/-- Given a right-player-wins game, provide a response to any move by left. -/
noncomputable def right_response {x : pgame} (h : x ≤ 0) (i : x.left_moves) : (x.move_left i).right_moves :=
classical.some $ (le_zero.1 h) i

/-- Show that the response for right provided by `right_response`
    preserves the right-player-wins condition. -/
lemma right_response_spec {x : pgame} (h : x ≤ 0) (i : x.left_moves) : (x.move_left i).move_right (right_response h i) ≤ 0 :=
classical.some_spec $ (le_zero.1 h) i

/-- Given a left-player-wins game, provide a response to any move by right. -/
noncomputable def left_response {x : pgame} (h : 0 ≤ x) (j : x.right_moves) : (x.move_right j).left_moves :=
classical.some $ (zero_le.1 h) j

/-- Show that the response for left provided by `left_response`
    preserves the left-player-wins condition. -/
lemma left_response_spec {x : pgame} (h : 0 ≤ x) (j : x.right_moves) : 0 ≤ (x.move_right j).move_left (left_response h j) :=
classical.some_spec $ (zero_le.1 h) j

theorem lt_of_le_mk {xl xr xL xR y i} :
  (⟨xl, xr, xL, xR⟩ : pgame) ≤ y → xL i < y :=
by cases y; exact λ h, h.1 i

theorem lt_of_mk_le {x : pgame} {yl yr yL yR i} :
  x ≤ ⟨yl, yr, yL, yR⟩ → x < yR i :=
by cases x; exact λ h, h.2 i

theorem mk_lt_of_le {xl xr xL xR y i} :
  (by exact xR i ≤ y) → (⟨xl, xr, xL, xR⟩ : pgame) < y :=
by cases y; exact λ h, or.inl ⟨i, h⟩

theorem lt_mk_of_le {x : pgame} {yl yr yL yR i} :
  (by exact x ≤ yL i) → x < ⟨yl, yr, yL, yR⟩ :=
by cases x; exact λ h, or.inr ⟨i, h⟩

theorem not_le_lt {x y : pgame} :
  (¬ x ≤ y ↔ y < x) ∧ (¬ x < y ↔ y ≤ x) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  classical,
  simp [not_and_distrib, not_or_distrib, not_forall, not_exists,
    and_comm, or_comm, IHxl, IHxr, IHyl, IHyr]
end

theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y < x := not_le_lt.1
theorem not_lt {x y : pgame} : ¬ x < y ↔ y ≤ x := not_le_lt.2

@[refl] theorem le_refl : ∀ x : pgame, x ≤ x
| ⟨l, r, L, R⟩ :=
  ⟨λ i, lt_mk_of_le (le_refl _), λ i, mk_lt_of_le (le_refl _)⟩

theorem lt_irrefl (x : pgame) : ¬ x < x :=
not_lt.2 (le_refl _)

theorem ne_of_lt : ∀ {x y : pgame}, x < y → x ≠ y
| x _ h rfl := lt_irrefl x h

theorem le_trans_aux
  {xl xr} {xL : xl → pgame} {xR : xr → pgame}
  {yl yr} {yL : yl → pgame} {yR : yr → pgame}
  {zl zr} {zL : zl → pgame} {zR : zr → pgame}
  (h₁ : ∀ i, mk yl yr yL yR ≤ mk zl zr zL zR → mk zl zr zL zR ≤ xL i → mk yl yr yL yR ≤ xL i)
  (h₂ : ∀ i, zR i ≤ mk xl xr xL xR → mk xl xr xL xR ≤ mk yl yr yL yR → zR i ≤ mk yl yr yL yR) :
  mk xl xr xL xR ≤ mk yl yr yL yR →
  mk yl yr yL yR ≤ mk zl zr zL zR →
  mk xl xr xL xR ≤ mk zl zr zL zR :=
λ ⟨xLy, xyR⟩ ⟨yLz, yzR⟩, ⟨
  λ i, not_le.1 (λ h, not_lt.2 (h₁ _ ⟨yLz, yzR⟩ h) (xLy _)),
  λ i, not_le.1 (λ h, not_lt.2 (h₂ _ h ⟨xLy, xyR⟩) (yzR _))⟩

@[trans] theorem le_trans {x y z : pgame} : x ≤ y → y ≤ z → x ≤ z :=
suffices ∀ {x y z : pgame},
  (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y),
from this.1, begin
  clear x y z, intros,
  induction x with xl xr xL xR IHxl IHxr generalizing y z,
  induction y with yl yr yL yR IHyl IHyr generalizing z,
  induction z with zl zr zL zR IHzl IHzr,
  exact ⟨
    le_trans_aux (λ i, (IHxl _).2.1) (λ i, (IHzr _).2.2),
    le_trans_aux (λ i, (IHyl _).2.2) (λ i, (IHxr _).1),
    le_trans_aux (λ i, (IHzl _).1) (λ i, (IHyr _).2.1)⟩,
end

/-- Define the equivalence relation on pre-surreals. Two pre-surreals
  `x`, `y` are equivalent if `x ≤ y` and `y ≤ x`. -/
def equiv (x y : pgame) : Prop := x ≤ y ∧ y ≤ x

local infix ` ≈ ` := pgame.equiv

theorem equiv_refl (x) : x ≈ x := ⟨le_refl _, le_refl _⟩
theorem equiv_symm {x y} : x ≈ y → y ≈ x | ⟨xy, yx⟩ := ⟨yx, xy⟩
theorem equiv_trans {x y z} : x ≈ y → y ≈ z → x ≈ z
| ⟨xy, yx⟩ ⟨yz, zy⟩ := ⟨le_trans xy yz, le_trans zy yx⟩

theorem le_congr {x₁ y₁ x₂ y₂} : x₁ ≈ x₂ → y₁ ≈ y₂ → (x₁ ≤ y₁ ↔ x₂ ≤ y₂)
| ⟨x12, x21⟩ ⟨y12, y21⟩ := ⟨λ h, le_trans x21 (le_trans h y12), λ h, le_trans x12 (le_trans h y21)⟩

theorem lt_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
not_le.symm.trans $ (not_congr (le_congr hy hx)).trans not_le

/-- `sub_game x y` says that left always has fewer moves in `x` than in `y`,
     and right always has more moves in `x` than in `y` -/
inductive sub_game : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π (x y : pgame) (L : x.left_moves ↪ y.left_moves) (R : y.right_moves ↪ x.right_moves),
         (∀ (i : x.left_moves), sub_game (x.move_left i) (y.move_left (L i))) →
         (∀ (j : y.right_moves), sub_game (x.move_right (R j)) (y.move_right j)) → sub_game x y

-- TODO prove `sub_game x y → sub_game y x → relabelling x y`
-- TODO prove results below about relabelling for `sub_game`, as appropriate

inductive relabelling : pgame.{u} → pgame.{u} → Type (u+1)
| mk : Π (x y : pgame) (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves),
         (∀ (i : x.left_moves), relabelling (x.move_left i) (y.move_left (L i))) →
         (∀ (j : y.right_moves), relabelling (x.move_right (R.symm j)) (y.move_right j)) → relabelling x y

@[refl] def relabelling.refl : Π (x : pgame), relabelling x x
| (mk xl xr xL xR) :=
  relabelling.mk (mk xl xr xL xR) (mk xl xr xL xR) (equiv.refl _) (equiv.refl _)
    (λ i, relabelling.refl _) (λ j, relabelling.refl _)
using_well_founded { dec_tac := pgame_wf_tac }

@[symm] def relabelling.symm : Π {x y : pgame}, relabelling x y → relabelling y x
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk _ _ L_equiv R_equiv L_relabelling R_relabelling) :=
begin
  refine relabelling.mk _ _ L_equiv.symm R_equiv.symm _ _,
  intro i,
  simpa using (L_relabelling (L_equiv.symm i)).symm,
  intro j,
  simpa using (R_relabelling (R_equiv j)).symm,
end

-- TODO trans for relabelling?

theorem le_of_relabelling : Π {x y : pgame} (r : relabelling x y), x ≤ y
| (mk xl xr xL xR) (mk yl yr yL yR) (relabelling.mk _ _ L_equiv R_equiv L_relabelling R_relabelling) :=
begin
  rw le_def,
  fsplit,
  { intro i,
    right,
    use (L_equiv.to_fun i),
    dsimp,
    exact le_of_relabelling (L_relabelling i) },
  { intro j,
    left,
    use (R_equiv.inv_fun j),
    dsimp,
    exact le_of_relabelling (R_relabelling j) },
end

theorem ge_of_relabelling {x y : pgame} (r : relabelling x y) : x ≥ y :=
le_of_relabelling r.symm

theorem equiv_of_relabelling {x y : pgame} (r : relabelling x y) : x ≈ y :=
⟨le_of_relabelling r, ge_of_relabelling r⟩

/-- The negation of `{L | R}` is `{-R | -L}`. -/
def neg : pgame → pgame
| ⟨l, r, L, R⟩ := ⟨r, l, λ i, neg (R i), λ i, neg (L i)⟩

instance : has_neg pgame := ⟨neg⟩

@[simp] lemma neg_def {xl xr xL xR} : -(mk xl xr xL xR) = mk xr xl (λ j, -(xR j)) (λ i, -(xL i)) := rfl

@[simp] theorem neg_neg : Π {x : pgame}, -(-x) = x
| (mk xl xr xL xR) :=
begin
  dsimp [has_neg.neg, neg],
  congr; funext i,
  { have t := @neg_neg (xL i),
    exact t },
  { have t := @neg_neg (xR i),
    exact t }
end

@[simp] theorem neg_neg' {x : pgame} : neg (neg x) = x :=
begin
  have := neg_neg,
  dsimp [has_neg.neg] at this,
  exact this
end

@[simp] theorem neg_zero : -(0 : pgame) = 0 :=
begin
  dsimp [has_zero.zero, has_neg.neg, neg],
  congr; funext i; cases i
end

def left_moves_neg (x : pgame) : (-x).left_moves ≃ x.right_moves :=
begin
  induction x,
  refl,
end
def right_moves_neg (x : pgame) : (-x).right_moves ≃ x.left_moves :=
begin
  induction x,
  refl,
end

@[simp] lemma move_right_left_moves_neg {x : pgame} (i : left_moves (-x)) :
move_right x ((left_moves_neg x) i) = -(move_left (-x) i) :=
begin
  induction x,
  dsimp [left_moves_neg],
  rw neg_neg,
end
@[simp] lemma move_left_right_moves_neg_symm {x : pgame} (i : right_moves x) :
move_left (-x) ((left_moves_neg x).symm i) = -(move_right x i) :=
begin
  induction x,
  refl,
end
@[simp] lemma move_left_right_moves_neg {x : pgame} (i : right_moves (-x)) :
move_left x ((right_moves_neg x) i) = -(move_right (-x) i) :=
begin
  induction x,
  dsimp [right_moves_neg],
  rw neg_neg,
end
@[simp] lemma move_right_right_moves_neg_symm {x : pgame} (i : left_moves x) :
move_right (-x) ((right_moves_neg x).symm i) = -(move_left x i) :=
begin
  induction x,
  refl,
end

theorem le_iff_neg_ge : Π {x y : pgame}, x ≤ y ↔ -y ≤ -x
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  rw [le_def],
  rw [le_def],
  dsimp [neg],
  fsplit,
  { intro h,
    fsplit,
    { intro i, have t := h.right i, cases t,
      { right, cases t, use t_w, exact le_iff_neg_ge.1 t_h, },
      { left,  cases t, use (@right_moves_neg (yR i)).symm t_w, convert le_iff_neg_ge.1 t_h, simp } },
    { intro j, have t := h.left j, cases t,
      { right, cases t, use (@left_moves_neg (xL j)).symm t_w, convert le_iff_neg_ge.1 t_h, simp, },
      { left,  cases t, use t_w, exact le_iff_neg_ge.1 t_h, } } },
  { intro h,
    fsplit,
    { intro i, have t := h.right i, cases t,
      { right, cases t, use t_w, exact le_iff_neg_ge.2 t_h, },
      { left,  cases t, use (@left_moves_neg (xL i)) t_w, convert le_iff_neg_ge.2 _, convert t_h, simp, } },
    { intro j, have t := h.left j, cases t,
      { right, cases t, use (@right_moves_neg (yR j)) t_w, convert le_iff_neg_ge.2 _, convert t_h, simp },
      { left,  cases t, use t_w, exact le_iff_neg_ge.2 t_h, } } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_congr {x y : pgame} (h : x ≈ y) : -x ≈ -y :=
⟨le_iff_neg_ge.1 h.2, le_iff_neg_ge.1 h.1⟩

theorem zero_le_iff_neg_le_zero {x : pgame} : 0 ≤ x ↔ -x ≤ 0 :=
begin
  convert le_iff_neg_ge,
  rw neg_zero
end

theorem le_zero_iff_zero_le_neg {x : pgame} : x ≤ 0 ↔ 0 ≤ -x :=
begin
  convert le_iff_neg_ge,
  rw neg_zero
end

/-- The sum of `x = {xL | xR}` and `y = {yL | yR}` is `{xL + y, x + yL | xR + y, x + yR}`. -/
def add (x y : pgame) : pgame :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl ⊕ yl, xr ⊕ yr, sum.rec _ _, sum.rec _ _⟩,
  { exact λ i, IHxl i y },
  { exact λ i, IHyl i },
  { exact λ i, IHxr i y },
  { exact λ i, IHyr i }
end

instance : has_add pgame := ⟨add⟩

def add_zero_relabelling : Π (x : pgame), relabelling (x + 0) x
| (mk xl xr xL xR) :=
begin
  fsplit,
  exact equiv.sum_pempty xl,
  exact equiv.sum_pempty xr,
  { rintro (⟨i⟩|⟨⟨⟩⟩),
    change relabelling (xL i + 0) (xL i),
    apply add_zero_relabelling, },
  { rintro j,
    change relabelling (xR j + 0) (xR j),
    apply add_zero_relabelling, }
end

def add_zero_equiv (x : pgame) : x + 0 ≈ x :=
equiv_of_relabelling (add_zero_relabelling x)

def zero_add_relabelling : Π (x : pgame), relabelling (0 + x) x
| (mk xl xr xL xR) :=
begin
  fsplit,
  exact equiv.pempty_sum xl,
  exact equiv.pempty_sum xr,
  { rintro (⟨⟨⟩⟩|⟨i⟩),
    change relabelling (0 + xL i) (xL i),
    apply zero_add_relabelling, },
  { rintro j,
    change relabelling (0 + xR j) (xR j),
    apply zero_add_relabelling, }
end

def zero_add_equiv (x : pgame) : 0 + x ≈ x :=
equiv_of_relabelling (zero_add_relabelling x)


-- def addL {xl xr yl yr} (xL : xl → pgame) (xR yL yR) (xy : xl ⊕ yl) : pgame :=
-- sum.cases_on xy (λ i, xL i + mk yl yr yL yR) (λ i, mk xl xr xL xR + yL i)

-- @[simp] lemma addL_inl {xl xr yl yr} (xL xR yL yR) (i : xl) :
--   @addL xl xr yl yr xL xR yL yR (sum.inl i) = xL i + mk yl yr yL yR := rfl

-- @[simp] lemma addL_inr {xl xr yl yr} (xL xR yL yR) (i : yl) :
--   @addL xl xr yl yr xL xR yL yR (sum.inr i) = mk xl xr xL xR + yL i := rfl

-- def addR {xl xr yl yr} (xL) (xR : xr → pgame) (yL yR) (xy : xr ⊕ yr) : pgame :=
-- sum.cases_on xy (λ i, xR i + mk yl yr yL yR) (λ i, mk xl xr xL xR + yR i)

-- @[simp] lemma addR_inl {xl xr yl yr} (xL xR yL yR) (i : xr) :
--   @addR xl xr yl yr xL xR yL yR (sum.inl i) = xR i + mk yl yr yL yR := rfl

-- @[simp] lemma addR_inr {xl xr yl yr} (xL xR yL yR) (i : yr) :
--   @addR xl xr yl yr xL xR yL yR (sum.inr i) = mk xl xr xL xR + yR i := rfl

-- lemma add_def {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} :
--   mk xl xr xL xR + mk yl yr yL yR =
--   mk (xl ⊕ yl) (xr ⊕ yr) (addL xL xR yL yR) (addR xL xR yL yR) := rfl

-- def left_moves_add_mk {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} :
--   (mk xl xr xL xR + mk yl yr yL yR).left_moves = ((mk xl xr xL xR).left_moves ⊕ (mk yl yr yL yR).left_moves) :=
-- rfl
-- def right_moves_add_mk {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} :
--   (mk xl xr xL xR + mk yl yr yL yR).right_moves = ((mk xl xr xL xR).right_moves ⊕ (mk yl yr yL yR).right_moves) :=
-- rfl

def left_moves_add {x y : pgame} : (x + y).left_moves ≃ (x.left_moves ⊕ y.left_moves) :=
begin
  induction x generalizing y,
  induction y,
  refl,
end
def right_moves_add {x y : pgame} : (x + y).right_moves ≃ (x.right_moves ⊕ y.right_moves) :=
begin
  induction x generalizing y,
  induction y,
  refl,
end

-- @[simp] lemma left_moves_add_mk_inl {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} {i} :
--   (@left_moves_add (mk xl xr xL xR) (mk yl yr yL yR)) (sum.inl i) = sum.inl i := rfl
-- @[simp] lemma left_moves_add_mk_inr {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} {i} :
--   (@left_moves_add (mk xl xr xL xR) (mk yl yr yL yR)) (sum.inr i) = sum.inr i := rfl
-- @[simp] lemma right_moves_add_mk_inl {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} {i} :
--   (@right_moves_add (mk xl xr xL xR) (mk yl yr yL yR)) (sum.inl i) = sum.inl i := rfl
-- @[simp] lemma right_moves_add_mk_inr {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} {i} :
--   (@right_moves_add (mk xl xr xL xR) (mk yl yr yL yR)) (sum.inr i) = sum.inr i := rfl
-- @[simp] lemma left_moves_add_mk_symm_inl {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} {i} :
--   (@left_moves_add (mk xl xr xL xR) (mk yl yr yL yR)).symm (sum.inl i) = sum.inl i := rfl
-- @[simp] lemma left_moves_add_mk_symm_inr {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} {i} :
--   (@left_moves_add (mk xl xr xL xR) (mk yl yr yL yR)).symm (sum.inr i) = sum.inr i := rfl
-- @[simp] lemma right_moves_add_mk_symm_inl {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} {i} :
--   (@right_moves_add (mk xl xr xL xR) (mk yl yr yL yR)).symm (sum.inl i) = sum.inl i := rfl
-- @[simp] lemma right_moves_add_mk_symm_inr {xl xr : Type u} {xL xR} {yl yr : Type u} {yL yR} {i} :
--   (@right_moves_add (mk xl xr xL xR) (mk yl yr yL yR)).symm (sum.inr i) = sum.inr i := rfl

-- -- This is a bit of a pain...
@[simp] lemma left_moves_add_inv_fun_inl {x y : pgame} {i : x.left_moves} :
  left_moves_add.inv_fun (sum.inl i) = (@left_moves_add x y).symm (sum.inl i) := rfl
@[simp] lemma left_moves_add_inv_fun_inr {x y : pgame} {i : y.left_moves} :
  left_moves_add.inv_fun (sum.inr i) = (@left_moves_add x y).symm (sum.inr i) := rfl
@[simp] lemma right_moves_add_inv_fun_inl {x y : pgame} {i : x.right_moves} :
  right_moves_add.inv_fun (sum.inl i) = (@right_moves_add x y).symm (sum.inl i) := rfl
@[simp] lemma right_moves_add_inv_fun_inr {x y : pgame} {i : y.right_moves} :
  right_moves_add.inv_fun (sum.inr i) = (@right_moves_add x y).symm (sum.inr i) := rfl

@[simp] lemma mk_add_move_left_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inl i) = (mk xl xr xL xR).move_left i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_left_inl {x y : pgame} {i} :
  (x + y).move_left ((@left_moves_add x y).symm (sum.inl i)) = x.move_left i + y :=
begin
  cases x, cases y,
  refl,
end
@[simp] lemma mk_add_move_right_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inl i) = (mk xl xr xL xR).move_right i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_right_inl {x y : pgame} {i} :
  (x + y).move_right ((@right_moves_add x y).symm (sum.inl i)) = x.move_right i + y :=
begin
  cases x, cases y,
  refl,
end
@[simp] lemma mk_add_move_left_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inr i) = (mk xl xr xL xR) + (mk yl yr yL yR).move_left i :=
rfl
@[simp] lemma add_move_left_inr {x y : pgame} {i : y.left_moves} :
  (x + y).move_left ((@left_moves_add x y).symm (sum.inr i)) = x + y.move_left i :=
begin
  cases x, cases y,
  refl,
end
@[simp] lemma mk_add_move_right_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inr i) = (mk xl xr xL xR) + (mk yl yr yL yR).move_right i :=
rfl
@[simp] lemma add_move_right_inr {x y : pgame} {i} :
  (x + y).move_right ((@right_moves_add x y).symm (sum.inr i)) = x + y.move_right i :=
begin
  cases x, cases y,
  refl,
end

instance : has_sub pgame := ⟨λ x y, x + -y⟩

def neg_add_relabelling : Π (x y : pgame), relabelling (-(x + y)) (-x + -y)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  fsplit,
  refl,
  refl,
  { intro j, dsimp, change xr ⊕ yr at j,
    cases j,
    dsimp,
    exact neg_add_relabelling (xR j) (mk yl yr yL yR),
    dsimp,
    exact neg_add_relabelling (mk xl xr xL xR) (yR j), },
  { intro i, dsimp, change xl ⊕ yl at i,
    cases i,
    dsimp,
    exact neg_add_relabelling (xL i) (mk yl yr yL yR),
    dsimp,
    exact neg_add_relabelling (mk xl xr xL xR) (yL i), },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem neg_add_le {x y : pgame} : -(x + y) ≤ -x + -y :=
le_of_relabelling (neg_add_relabelling x y)
theorem neg_add_ge {x y : pgame} : -(x + y) ≥ -x + -y :=
ge_of_relabelling (neg_add_relabelling x y)

-- TODO
-- theorem le_iff_sub_le_zero {x y : pgame} : x ≤ y ↔ x - y ≤ 0 := sorry
-- theorem le_iff_zero_le_sub {x y : pgame} : x ≤ y ↔ 0 ≤ y - x := sorry

theorem add_le_zero_of_le_zero : Π {x y : pgame} (hx : x ≤ 0) (hy : y ≤ 0), x + y ≤ 0
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  intros hx hy,
  rw le_zero,
  intro i,
  change xl ⊕ yl at i, -- I wish dsimp would do this
  cases i,
  { use right_moves_add.inv_fun (sum.inl (right_response hx i)),
    simp,
    have rs := right_response_spec hx i,
    dsimp,
    simp only [add_move_right_inl],
    exact add_le_zero_of_le_zero rs hy, },
  { fsplit,
    change right_moves (mk xl xr xL xR + move_left (mk yl yr yL yR) i),
    use right_moves_add.inv_fun (sum.inr (right_response hy i)),
    simp,
    have rs := right_response_spec hy i,
    dsimp,
    simp only [add_move_right_inr],
    exact add_le_zero_of_le_zero hx rs, },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem zero_le_add_of_zero_le : Π {x y : pgame} (hx : 0 ≤ x) (hy : 0 ≤ y), 0 ≤ x + y :=
begin
  intros x y,
  repeat { rw zero_le_iff_neg_le_zero },
  intros hx hy,
  transitivity,
  exact neg_add_le,
  solve_by_elim [add_le_zero_of_le_zero],
end

def add_comm_relabelling : Π (x y : pgame.{u}), relabelling (x + y) (y + x)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  fsplit,
  { transitivity,
    exact left_moves_add,
    transitivity,
    apply equiv.sum_comm,
    exact left_moves_add.symm, },
  { transitivity,
    exact right_moves_add,
    transitivity,
    apply equiv.sum_comm,
    exact right_moves_add.symm, },
  { intros,
    cases i; { dsimp [left_moves_add], apply add_comm_relabelling, } },
  { intros,
    simp only [equiv.symm_trans_apply, equiv.symm_symm_apply, equiv.sum_comm],
    cases j; { dsimp [right_moves_add], apply add_comm_relabelling, } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_comm_le {x y : pgame} : (x + y) ≤ (y + x) :=
le_of_relabelling (add_comm_relabelling x y)

theorem add_comm_equiv {x y : pgame} : (x + y) ≈ (y + x) :=
⟨le_of_relabelling (add_comm_relabelling x y), ge_of_relabelling (add_comm_relabelling x y)⟩

def add_assoc_relabelling : Π (x y z : pgame.{u}), relabelling ((x + y) + z) (x + (y + z))
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  fsplit,
  { transitivity,
    exact left_moves_add,
    transitivity,
    apply equiv.sum_congr left_moves_add (equiv.refl _),
    apply equiv.sum_assoc, },
  { transitivity,
    exact right_moves_add,
    transitivity,
    apply equiv.sum_congr right_moves_add (equiv.refl _),
    apply equiv.sum_assoc, },
  { rintro (⟨i|i⟩|i),
    { apply add_assoc_relabelling, },
    { change relabelling (mk xl xr xL xR + yL i + mk zl zr zL zR) (mk xl xr xL xR + (yL i + mk zl zr zL zR)), apply add_assoc_relabelling, },
    { change relabelling (mk xl xr xL xR + mk yl yr yL yR + zL i) (mk xl xr xL xR + (mk yl yr yL yR + zL i)), apply add_assoc_relabelling, } },
  { rintro (j|⟨j|j⟩),
    { apply add_assoc_relabelling, },
    { change relabelling (mk xl xr xL xR + yR j + mk zl zr zL zR) (mk xl xr xL xR + (yR j + mk zl zr zL zR)), apply add_assoc_relabelling, },
    { change relabelling (mk xl xr xL xR + mk yl yr yL yR + zR j) (mk xl xr xL xR + (mk yl yr yL yR + zR j)), apply add_assoc_relabelling, } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem add_assoc_equiv {x y z : pgame} : ((x + y) + z) ≈ (x + (y + z)) :=
⟨le_of_relabelling (add_assoc_relabelling x y z), ge_of_relabelling (add_assoc_relabelling x y z)⟩

theorem le_add_right : Π {x y z : pgame} (h : x ≤ y), x + z ≤ y + z
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  intros h,
  rw le_def,
  fsplit,
  { -- if left plays first
    intros i,
    change xl ⊕ zl at i,
    cases i,
    { -- either they play in x
      rw le_def at h,
      cases h,
      have t := h_left i,
      rcases t with ⟨j, jh⟩ | ⟨i, ih⟩,
      { left,
        use right_moves_add.inv_fun (sum.inl j),
        dsimp,
        simp only [add_move_right_inl],
        exact le_add_right jh },
      { right,
        use left_moves_add.inv_fun (sum.inl i),
        dsimp,
        simp only [move_left_mk, add_move_left_inl],
        exact le_add_right ih, },
      },
    { -- or play in z
      right,
      use left_moves_add.inv_fun (sum.inr i),
      dsimp,
      simp only [move_left_mk, add_move_left_inr],
      exact le_add_right h,
    }, },
  { -- if right plays first
    intros j,
    change yr ⊕ zr at j,
    cases j,
    { -- either they play in y
      rw le_def at h,
      cases h,
      have t := h_right j,
      rcases t with ⟨j, jh⟩ | ⟨i, ih⟩,
      { left,
        use right_moves_add.inv_fun (sum.inl j),
        dsimp,
        simp only [move_left_mk, add_move_left_inr],
        exact le_add_right jh },
      { right,
        use left_moves_add.inv_fun (sum.inl i),
        dsimp,
        simp only [add_move_left_inl],
        exact le_add_right ih, },
      },
    { -- or play in z
      left,
      use right_moves_add.inv_fun (sum.inr j),
      dsimp,
      simp only [move_right_mk, add_move_right_inr],
      exact le_add_right h,
    }
  }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem le_add_left {x y z : pgame} (h : y ≤ z) : x + y ≤ x + z :=
begin
  transitivity,
  apply add_comm_le,
  transitivity,
  apply le_add_right h,
  apply add_comm_le,
end

theorem add_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : (w + y) ≈ (x + z) :=
begin
  fsplit,
  { transitivity w + z,
    exact le_add_left h₂.1,
    exact le_add_right h₁.1, },
  { transitivity x + y,
    exact le_add_left h₂.2,
    exact le_add_right h₁.2 }
end

inductive short : pgame.{u} → Type (u+1)
| mk : Π (x : pgame) [fintype x.left_moves] [fintype x.right_moves]
         [∀ i : x.left_moves, short (x.move_left i)] [∀ j : x.right_moves, short (x.move_right j)], short x

attribute [class] short

instance fintype_left_moves (x : pgame) [S : short x] : fintype (x.left_moves) :=
begin
  tactic.unfreeze_local_instances,
  induction S with _ F _ _ _,
  apply F
end
instance fintype_right_moves (x : pgame) [S : short x] : fintype (x.right_moves) :=
begin
  tactic.unfreeze_local_instances,
  induction S with _ _ F _ _,
  apply F
end
instance move_left_short (x : pgame) [S : short x] (i : x.left_moves) : short (x.move_left i) :=
begin
  tactic.unfreeze_local_instances,
  cases S with _ _ _ L _,
  apply L
end
instance move_left_short' {xl xr xL xR} [S : short (mk xl xr xL xR)] (i : xl) : short (xL i) :=
begin
  tactic.unfreeze_local_instances,
  cases S with _ _ _ L _,
  apply L
end
instance move_right_short (x : pgame) [S : short x] (j : x.right_moves) : short (x.move_right j) :=
begin
  tactic.unfreeze_local_instances,
  cases S with _ _ _ _ R,
  apply R
end
instance move_right_short' {xl xr xL xR} [S : short (mk xl xr xL xR)] (j : xr) : short (xR j) :=
begin
  tactic.unfreeze_local_instances,
  cases S with _ _ _ _ R,
  apply R
end

instance short_0 : short 0 :=
@short.mk 0 pempty.fintype pempty.fintype (λ i, by cases i) (λ j, by cases j)

instance short_1 : short 1 :=
@short.mk 1 punit.fintype pempty.fintype (λ i, begin cases i, dsimp, apply_instance, end) (λ j, by cases j)

instance short_add : Π (x y : pgame.{u}) [short x] [short y], short (x + y)
| (mk xl xr xL xR) (mk yl yr yL yR) _ _ :=
begin
  resetI,
  apply @short.mk _ _ _ _ _,
  { apply fintype.of_equiv _ (left_moves_add.symm),
    apply sum.fintype },
  { apply fintype.of_equiv _ (right_moves_add.symm),
    apply sum.fintype },
  { rintro ⟨i⟩,
    { apply short_add, },
    { change short (mk xl xr xL xR + yL i), apply short_add, } },
  { rintro ⟨j⟩,
    { apply short_add, },
    { change short (mk xl xr xL xR + yR j), apply short_add, } },
end
using_well_founded { dec_tac := pgame_wf_tac }

instance le_decidable : Π (x y : pgame.{u}) [short x] [short y], decidable (x ≤ y)
| x y _ _ :=
begin
  resetI,
  rw le_def,
  apply @and.decidable _ _ _ _,
  { apply @fintype.decidable_forall_fintype (left_moves x) (by apply_instance) _ _,
    intro i,
    apply @or.decidable _ _ _ _,
    { apply @fintype.decidable_exists_fintype (right_moves (move_left x i)) (by apply_instance) _ _,
      intro j,
      apply le_decidable },
    { apply @fintype.decidable_exists_fintype (left_moves y) (by apply_instance) _ _,
      intro j,
      apply le_decidable }, },
  { apply @fintype.decidable_forall_fintype (right_moves y) (by apply_instance) _ _,
    intro i,
    apply @or.decidable _ _ _ _,
    { apply @fintype.decidable_exists_fintype (right_moves x) (by apply_instance) _ _,
      intro j,
      apply le_decidable },
    { apply @fintype.decidable_exists_fintype (left_moves (move_right y i)) (by apply_instance) _ _,
      intro j,
      apply le_decidable }, },
end
using_well_founded { dec_tac := pgame_wf_tac }

instance equiv_decidable (x y : pgame.{u}) [short x] [short y] : decidable (x ≈ y) :=
and.decidable

example : short 0 := by apply_instance
example : short 1 := by apply_instance
example : short (0 + 0) := by apply_instance

example : decidable ((1 : pgame) ≤ 1) := by apply_instance

#eval to_bool ((1 : pgame) ≤ 0)
#eval to_bool ((0 : pgame) ≤ 1)
#eval to_bool ((1 : pgame) ≤ 1)

#eval to_bool ((1 : pgame) + 1 + 1 ≤ (1 + 0 + 1))

-- TODO but this doesn't work?
-- example : (0 : pgame) ≤ 0 := dec_trivial
-- example : (1 : pgame) ≤ 1 := by exact dec_trivial

/-- The game `ω`. (In fact all ordinals have surreal
  representatives.) -/
def omega : pgame := ⟨ulift ℕ, pempty, λ n, ↑n.1, pempty.elim⟩

end pgame

local infix ` ≈ ` := pgame.equiv

instance pgame.setoid : setoid pgame :=
⟨λ x y, x ≈ y,
 λ x, pgame.equiv_refl _,
 λ x y, pgame.equiv_symm,
 λ x y z, pgame.equiv_trans⟩

/-- The type of combinatorial games. In ZFC, a combinatorial game is constructed from
  two sets of combinatorial games that have been constructed at an earlier
  stage. To do this in type theory, we say that a combinatorial pre-game is built
  inductively from two families of combinatorial games indexed over any type
  in Type u. The resulting type `pgame.{u}` lives in `Type (u+1)`,
  reflecting that it is a proper class in ZFC.
  A combinatorial game is then constructed by quotienting by equivalence so that
  the ordering becomes a total order. -/
def game := quotient pgame.setoid

open pgame

namespace game

/-- The relation `x ≤ y` on games. -/
def le : game → game → Prop :=
quotient.lift₂ (λ x y, x ≤ y) (λ x₁ y₁ x₂ y₂ hx hy, propext (le_congr hx hy))

/-- The relation `x < y` on games. -/
def lt : game → game → Prop :=
quotient.lift₂ (λ x y, x < y) (λ x₁ y₁ x₂ y₂ hx hy, propext (lt_congr hx hy))

theorem not_le : ∀ {x y : game}, ¬ le x y ↔ lt y x :=
by { rintro ⟨x⟩ ⟨y⟩, exact not_le }

instance : has_zero game := ⟨⟦0⟧⟩
instance : has_one game := ⟨⟦1⟧⟩

def add : game → game → game :=
quotient.lift₂ (λ x y : pgame, ⟦x + y⟧) (λ x₁ y₁ x₂ y₂ hx hy, quot.sound (pgame.add_congr hx hy))

instance : has_add game := ⟨add⟩

def add_assoc (x y z : game) : x + y + z = x + (y + z) :=
begin
  induction x generalizing y z,
  induction y generalizing z,
  induction z,
  apply quot.sound,
  exact add_assoc_equiv,
  refl,
  refl,
  refl
end

instance : add_semigroup game :=
{ add_assoc := add_assoc,
  ..(by apply_instance : has_add game) }

def add_zero (x : game) : x + 0 = x :=
begin
  induction x,
  apply quot.sound,
  apply add_zero_equiv,
  refl
end
def zero_add (x : game) : 0 + x = x :=
begin
  induction x,
  apply quot.sound,
  apply zero_add_equiv,
  refl
end

instance : add_monoid game :=
{ add_zero := add_zero,
  zero_add := zero_add,
  ..(by apply_instance : has_zero game),
  ..(by apply_instance : add_semigroup game) }

def neg : game → game :=
quot.lift (λ x, ⟦-x⟧) (λ x y h, quot.sound (@neg_congr x y h))

instance : add_group game :=
{ neg := neg,
  add_left_neg := sorry,
  ..(game.add_monoid) }

def add_comm (x y : game) : x + y = y + x :=
begin
  induction x generalizing y,
  induction y,
  apply quot.sound,
  exact add_comm_equiv,
  refl,
  refl,
end

instance : add_comm_semigroup game :=
{ add_comm := add_comm,
  ..(by apply_instance : add_semigroup game) }

instance : add_comm_group game :=
{ ..(game.add_comm_semigroup),
  ..(game.add_group) }

-- TODO show order properties

namespace domineering_aux

def shift_up : ℤ × ℤ ↪ ℤ × ℤ := ⟨λ p : ℤ × ℤ, (p.1, p.2 + 1), sorry⟩
def shift_right : ℤ × ℤ ↪ ℤ × ℤ := ⟨λ p : ℤ × ℤ, (p.1 + 1, p.2), sorry⟩

def left_set  (b : finset (ℤ × ℤ)) : finset (ℤ × ℤ) := b ∩ b.map shift_up
def right_set (b : finset (ℤ × ℤ)) : finset (ℤ × ℤ) := b ∩ b.map shift_right

def left  (b : finset (ℤ × ℤ)) : Type := { p | p ∈ left_set b }
def right (b : finset (ℤ × ℤ)) : Type := { p | p ∈ right_set b }

instance fintype_left (b : finset (ℤ × ℤ)) : fintype (left b) :=
fintype.subtype _ (λ x, iff.refl _)

instance fintype_right (b : finset (ℤ × ℤ)) : fintype (right b) :=
fintype.subtype _ (λ x, iff.refl _)

def move_left (b : finset (ℤ × ℤ)) (m : left b) : finset (ℤ × ℤ) :=
(b.erase m.val).erase (m.val.1, m.val.2 - 1)
def move_right (b : finset (ℤ × ℤ)) (m : right b) : finset (ℤ × ℤ) :=
(b.erase m.val).erase (m.val.1 - 1, m.val.2)

lemma int.succ_ne_self {x : ℤ} : x + 1 ≠ x :=
begin
  sorry
end

lemma move_left_smaller (b : finset (ℤ × ℤ)) (m : left b) :
  finset.card (move_left b m) < finset.card b :=
begin
  dsimp [move_left],
  rcases m with ⟨⟨x,y⟩,p⟩,
  dsimp,
  dsimp [left_set] at p,
  simp at p,
  cases p with p₁ p₂,
  dsimp [shift_up] at p₂,
  simp at p₂,
  rcases p₂ with ⟨x,y,⟨p,rfl,rfl⟩⟩,
  rw finset.card_erase_of_mem,
  rw finset.card_erase_of_mem,
  { apply lt_of_le_of_lt (nat.pred_le _),
    exact nat.pred_lt (finset.card_ne_zero_of_mem p₁), },
  { exact p₁ },
  apply finset.mem_erase_of_ne_of_mem _ _,
  { intro h,
    replace h := congr_arg prod.snd h,
    dsimp at h,
    simp at h,
    apply (int.succ_ne_self h.symm), },
  { simpa using p },
end
lemma move_right_smaller (b : finset (ℤ × ℤ)) (m : right b) :
  finset.card (move_right b m) < finset.card b :=
begin
  dsimp [move_right],
  rcases m with ⟨⟨x,y⟩,p⟩,
  dsimp,
  dsimp [right_set] at p,
  simp at p,
  cases p with p₁ p₂,
  dsimp [shift_right] at p₂,
  simp at p₂,
  rcases p₂ with ⟨x,y,⟨p,rfl,rfl⟩⟩,
  rw finset.card_erase_of_mem,
  rw finset.card_erase_of_mem,
  { apply lt_of_le_of_lt (nat.pred_le _),
    exact nat.pred_lt (finset.card_ne_zero_of_mem p₁), },
  { exact p₁ },
  apply finset.mem_erase_of_ne_of_mem _ _,
  { intro h,
    replace h := congr_arg prod.fst h,
    dsimp at h,
    simp at h,
    apply (int.succ_ne_self h.symm), },
  { simpa using p },
end

end domineering_aux


section
open domineering_aux

instance : has_well_founded (finset (ℤ × ℤ)) := ⟨measure finset.card, measure_wf finset.card⟩

def domineering : finset (ℤ × ℤ) → pgame
| b := pgame.mk
    (left b) (right b)
    (λ m, have _, from move_left_smaller b m,  domineering (move_left b m))
    (λ m, have _, from move_right_smaller b m, domineering (move_right b m))

@[simp] lemma domineering_left_moves (b : finset (ℤ × ℤ)) :
  (domineering b).left_moves = left b :=
begin
  sorry
end
@[simp] lemma domineering_right_moves (b : finset (ℤ × ℤ)) :
  (domineering b).right_moves = right b :=
begin
  sorry
end

instance fintype_left_moves (b : finset (ℤ × ℤ)) : fintype ((domineering b).left_moves) :=
begin
  rw domineering_left_moves,
  exact domineering_aux.fintype_left b,
end
instance fintype_right_moves (b : finset (ℤ × ℤ)) : fintype ((domineering b).right_moves) :=
begin
  rw domineering_right_moves,
  exact domineering_aux.fintype_right b,
end

instance short_domineering : Π (b : finset (ℤ × ℤ)), short (domineering b)
| b :=
@short.mk (domineering b) (by apply_instance) (by apply_instance)
begin
  intro i,
  apply short_domineering (move_left b i),
end

def domineering.half := domineering ([(0,2), (0,1), (0,0), (1,0)].to_finset)

#eval to_bool (domineering.half + domineering.half ≈ 1)

end
end game
