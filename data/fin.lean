/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis

More about finite numbers.
-/

import data.nat.basic

open fin nat

theorem eq_of_lt_succ_of_not_lt {a b : ℕ} (h1 : a < b + 1) (h2 : ¬ a < b) : a = b :=
have h3 : a ≤ b, from le_of_lt_succ h1,
or.elim (eq_or_lt_of_not_lt h2) (λ h, h) (λ h, absurd h (not_lt_of_ge h3))

instance fin_to_nat (n : ℕ) : has_coe (fin n) nat := ⟨fin.val⟩
instance fin_to_int (n : ℕ) : has_coe (fin n) int := ⟨λ k, ↑(fin.val k)⟩

namespace fin
variables {n : ℕ} {a b : fin n}

@[simp] protected lemma eta (a : fin n) (h : a.1 < n) : (⟨a.1, h⟩ : fin n) = a :=
by cases a; refl

protected lemma ext_iff (a b : fin n) : a = b ↔ a.val = b.val :=
iff.intro (congr_arg _) fin.eq_of_veq

instance {n : ℕ} : decidable_linear_order (fin n) :=
{ le_refl := λ a, @le_refl ℕ _ _,
  le_trans := λ a b c, @le_trans ℕ _ _ _ _,
  le_antisymm := λ a b ha hb, fin.eq_of_veq $ le_antisymm ha hb,
  le_total := λ a b, @le_total ℕ _ _ _,
  lt_iff_le_not_le := λ a b, @lt_iff_le_not_le ℕ _ _ _,
  decidable_le := fin.decidable_le,
  ..fin.has_le,
  ..fin.has_lt }

instance {n : ℕ} : preorder (fin n) :=
by apply_instance

section succ
protected theorem succ.inj (p : fin.succ a = fin.succ b) : a = b :=
by cases a; cases b; exact eq_of_veq (nat.succ.inj (veq_of_eq p))

@[elab_as_eliminator] def succ_rec
  {C : ∀ n, fin n → Sort*}
  (H0 : ∀ n, C (succ n) 0)
  (Hs : ∀ n i, C n i → C (succ n) i.succ) : ∀ {n : ℕ} (i : fin n), C n i
| 0        i           := i.elim0
| (succ n) ⟨0, _⟩      := H0 _
| (succ n) ⟨succ i, h⟩ := Hs _ _ (succ_rec ⟨i, lt_of_succ_lt_succ h⟩)

@[elab_as_eliminator] def succ_rec_on {n : ℕ} (i : fin n)
  {C : ∀ n, fin n → Sort*}
  (H0 : ∀ n, C (succ n) 0)
  (Hs : ∀ n i, C n i → C (succ n) i.succ) : C n i :=
i.succ_rec H0 Hs

@[simp] theorem succ_rec_on_zero
  {C : ∀ n, fin n → Sort*} {H0 Hs} (n) :
  @fin.succ_rec_on (succ n) 0 C H0 Hs = H0 n := rfl

@[simp] theorem succ_rec_on_succ
  {C : ∀ n, fin n → Sort*} {H0 Hs} {n} (i : fin n) :
  @fin.succ_rec_on (succ n) i.succ C H0 Hs = Hs n i (fin.succ_rec_on i H0 Hs) :=
by cases i; refl

@[elab_as_eliminator] def cases {n} {C : fin (succ n) → Sort*}
  (H0 : C 0) (Hs : ∀ i : fin n, C (i.succ)) :
  ∀ (i : fin (succ n)), C i
| ⟨0, h⟩ := H0
| ⟨succ i, h⟩ := Hs ⟨i, lt_of_succ_lt_succ h⟩

@[simp] theorem cases_zero
  {n} {C : fin (succ n) → Sort*} {H0 Hs} :
  @fin.cases n C H0 Hs 0 = H0 := rfl

@[simp] theorem cases_succ
  {n} {C : fin (succ n) → Sort*} {H0 Hs} (i : fin n) :
  @fin.cases n C H0 Hs i.succ = Hs i :=
by cases i; refl

end succ

def fin_zero_elim {C : Sort*} : fin 0 → C :=
λ x, false.elim $ nat.not_lt_zero x.1 x.2

/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : fin (n+1) := ⟨_, n.lt_succ_self⟩

/-- Embedding of `fin n` in `fin (n+1)`, ignoring the `last n` -/
def raise (k : fin n) : fin (n + 1) := ⟨val k, lt_succ_of_lt (is_lt k)⟩

/-- Embedding of `fin (n+1)` in `fin n`, assuming that the argument is not `last n`. -/
def lower (i : fin (n+1)) (h : i.1 < n) : fin n := ⟨i.1, h⟩

/-- Embedding of `fin n` in `fin (n+1)`, around `p`. -/
def ascend (p : fin (n+1)) (i : fin n) : fin (n+1) :=
if i.1 < p.1 then i.raise else i.succ

/-- Embedding of `fin (n+1)` in `fin n`, around `p`. -/
def descend (p : fin (n+1)) (i : fin (n+1)) (hi : i ≠ p) : fin n :=
begin
  refine if h : i.1 < p.1
    then i.lower (lt_of_lt_of_le h $ nat.le_of_lt_succ p.2)
    else i.pred (mt (assume eq, _) hi),
  subst eq,
  exact fin.eq_of_veq (nat.eq_zero_of_le_zero (le_of_not_gt h)).symm
end

theorem le_last (i : fin (n+1)) : i ≤ last n :=
le_of_lt_succ i.is_lt

@[simp] lemma succ_val (j : fin n) : j.succ.val = j.val.succ :=
by cases j; simp [fin.succ]

@[simp] lemma pred_val (j : fin (n+1)) (h : j ≠ 0) : (j.pred h).val = j.val.pred :=
by cases j; simp [fin.pred]

@[simp] lemma succ_pred : ∀(i : fin (n+1)) (h : i ≠ 0), (i.pred h).succ = i
| ⟨0,     h⟩ hi := by contradiction
| ⟨n + 1, h⟩ hi := rfl

@[simp] lemma pred_succ (i : fin n) {h : i.succ ≠ 0} : i.succ.pred h = i :=
by cases i; refl

@[simp] lemma raise_val (k : fin n) : k.raise.val = k.val := rfl

@[simp] lemma lower_val (k : fin (n+1)) (h : k.1 < n) : (k.lower h).val = k.val := rfl

@[simp] lemma raise_lower (i : fin (n + 1)) (h : i.val < n): raise (lower i h) = i :=
fin.eq_of_veq rfl

theorem ascend_ne (p : fin (n+1)) (i : fin n) : p.ascend i ≠ p :=
begin
  assume eq,
  unfold fin.ascend at eq,
  split_ifs at eq with h;
    simpa [lt_irrefl, nat.lt_succ_self, eq.symm] using h
end

@[simp] lemma ascend_descend : ∀(p i : fin (n+1)) (h : i ≠ p), p.ascend (p.descend i h) = i
| ⟨p, hp⟩ ⟨0,   hi⟩ h := fin.eq_of_veq $ by simp [ascend, descend]; split_ifs; simp * at *
| ⟨p, hp⟩ ⟨i+1, hi⟩ h := fin.eq_of_veq
  begin
    have : i + 1 ≠ p, by rwa [(≠), fin.ext_iff] at h,
    unfold ascend descend,
    split_ifs with h1 h2; simp at *,
    exact (this (le_antisymm h2 (le_of_not_gt h1))).elim
  end

@[simp] lemma descend_ascend (p : fin (n+1)) (i : fin n) (h : p.ascend i ≠ p) :
  p.descend (p.ascend i) h = i :=
begin
  unfold fin.ascend,
  apply fin.eq_of_veq,
  split_ifs with h₀,
  { simp [descend, h₀] },
  { unfold descend,
    split_ifs with h₁,
    { exfalso,
      rw [succ_val] at h₁,
      exact h₀ (lt_trans (nat.lt_succ_self _) h₁) },
    { rw [pred_succ] } }
end

end fin
