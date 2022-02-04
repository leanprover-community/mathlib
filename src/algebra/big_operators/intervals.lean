/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import algebra.big_operators.basic
import data.nat.interval
import tactic.linarith

/-!
# Results about big operators over intervals

We prove results about big operators over intervals (mostly the `ℕ`-valued `Ico m n`).
-/

universes u v w

open_locale big_operators nat

namespace finset

section generic

variables {α : Type u} {β : Type v} {γ : Type w} {s₂ s₁ s : finset α} {a : α}
  {g f : α → β}

lemma sum_Ico_add [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α]
  [locally_finite_order α] [add_comm_monoid β] (f : α → β) (a b c : α) :
  (∑ x in Ico a b, f (c + x)) = (∑ x in Ico (a + c) (b + c), f x) :=
begin
  classical,
  rw [←image_add_right_Ico, sum_image (λ x hx y hy h, add_right_cancel h)],
  simp_rw add_comm,
end

@[to_additive]
lemma prod_Ico_add [ordered_cancel_add_comm_monoid α] [has_exists_add_of_le α]
  [locally_finite_order α] [comm_monoid β] (f : α → β) (a b c : α) :
  (∏ x in Ico a b, f (c + x)) = (∏ x in Ico (a + c) (b + c), f x) :=
@sum_Ico_add _ (additive β) _ _ _ _ f a b c

variables [comm_monoid β]

lemma sum_Ico_succ_top {δ : Type*} [add_comm_monoid δ] {a b : ℕ}
  (hab : a ≤ b) (f : ℕ → δ) : (∑ k in Ico a (b + 1), f k) = (∑ k in Ico a b, f k) + f b :=
by rw [nat.Ico_succ_right_eq_insert_Ico hab, sum_insert right_not_mem_Ico, add_comm]

@[to_additive]
lemma prod_Ico_succ_top {a b : ℕ} (hab : a ≤ b) (f : ℕ → β) :
  (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b :=
@sum_Ico_succ_top (additive β) _ _ _ hab _

lemma sum_eq_sum_Ico_succ_bot {δ : Type*} [add_comm_monoid δ] {a b : ℕ}
  (hab : a < b) (f : ℕ → δ) : (∑ k in Ico a b, f k) = f a + (∑ k in Ico (a + 1) b, f k) :=
have ha : a ∉ Ico (a + 1) b, by simp,
by rw [← sum_insert ha, nat.Ico_insert_succ_left hab]

@[to_additive]
lemma prod_eq_prod_Ico_succ_bot {a b : ℕ} (hab : a < b) (f : ℕ → β) :
  (∏ k in Ico a b, f k) = f a * (∏ k in Ico (a + 1) b, f k) :=
@sum_eq_sum_Ico_succ_bot (additive β) _ _ _ hab _

@[to_additive]
lemma prod_Ico_consecutive (f : ℕ → β) {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k) :
  (∏ i in Ico m n, f i) * (∏ i in Ico n k, f i) = (∏ i in Ico m k, f i) :=
Ico_union_Ico_eq_Ico hmn hnk ▸ eq.symm $ prod_union $ Ico_disjoint_Ico_consecutive m n k

@[to_additive]
lemma prod_range_mul_prod_Ico (f : ℕ → β) {m n : ℕ} (h : m ≤ n) :
  (∏ k in range m, f k) * (∏ k in Ico m n, f k) = (∏ k in range n, f k) :=
nat.Ico_zero_eq_range ▸ nat.Ico_zero_eq_range ▸ prod_Ico_consecutive f m.zero_le h

@[to_additive]
lemma prod_Ico_eq_mul_inv {δ : Type*} [comm_group δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∏ k in Ico m n, f k) = (∏ k in range n, f k) * (∏ k in range m, f k)⁻¹ :=
eq_mul_inv_iff_mul_eq.2 $ by rw [mul_comm]; exact prod_range_mul_prod_Ico f h

lemma sum_Ico_eq_sub {δ : Type*} [add_comm_group δ] (f : ℕ → δ) {m n : ℕ} (h : m ≤ n) :
  (∑ k in Ico m n, f k) = (∑ k in range n, f k) - (∑ k in range m, f k) :=
by simpa only [sub_eq_add_neg] using sum_Ico_eq_add_neg f h

/-- The two ways of summing over `(i,j)` in the range `a<=i<=j<b` are equal. -/
lemma sum_Ico_Ico_comm {M : Type*} [add_comm_monoid M]
  (a b : ℕ) (f : ℕ → ℕ → M) :
  ∑ i in finset.Ico a b, ∑ j in finset.Ico i b, f i j =
  ∑ j in finset.Ico a b, ∑ i in finset.Ico a (j+1), f i j :=
begin
  rw [finset.sum_sigma', finset.sum_sigma'],
  refine finset.sum_bij'
    (λ (x : Σ (i : ℕ), ℕ) _, (⟨x.2, x.1⟩ : Σ (i : ℕ), ℕ)) _ (λ _ _, rfl)
    (λ (x : Σ (i : ℕ), ℕ) _, (⟨x.2, x.1⟩ : Σ (i : ℕ), ℕ)) _
    (by rintro ⟨⟩ _; refl) (by rintro ⟨⟩ _; refl);
  simp only [finset.mem_Ico, sigma.forall, finset.mem_sigma];
  rintros a b ⟨⟨h₁,h₂⟩, ⟨h₃, h₄⟩⟩; refine ⟨⟨_, _⟩, ⟨_, _⟩⟩; linarith
end

@[to_additive]
lemma prod_Ico_eq_prod_range (f : ℕ → β) (m n : ℕ) :
  (∏ k in Ico m n, f k) = (∏ k in range (n - m), f (m + k)) :=
begin
  by_cases h : m ≤ n,
  { rw [←nat.Ico_zero_eq_range, prod_Ico_add, zero_add, tsub_add_cancel_of_le h] },
  { replace h : n ≤ m :=  le_of_not_ge h,
     rw [Ico_eq_empty_of_le h, tsub_eq_zero_iff_le.mpr h, range_zero, prod_empty, prod_empty] }
end

lemma prod_Ico_reflect (f : ℕ → β) (k : ℕ) {m n : ℕ} (h : m ≤ n + 1) :
  ∏ j in Ico k m, f (n - j) = ∏ j in Ico (n + 1 - m) (n + 1 - k), f j :=
begin
  have : ∀ i < m, i ≤ n,
  { intros i hi,
    exact (add_le_add_iff_right 1).1 (le_trans (nat.lt_iff_add_one_le.1 hi) h) },
  cases lt_or_le k m with hkm hkm,
  { rw [← nat.Ico_image_const_sub_eq_Ico (this _ hkm)],
    refine (prod_image _).symm,
    simp only [mem_Ico],
    rintros i ⟨ki, im⟩ j ⟨kj, jm⟩ Hij,
    rw [← tsub_tsub_cancel_of_le (this _ im), Hij, tsub_tsub_cancel_of_le (this _ jm)] },
  { simp [Ico_eq_empty_of_le, tsub_le_tsub_left, hkm] }
end

lemma sum_Ico_reflect {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (k : ℕ) {m n : ℕ}
  (h : m ≤ n + 1) :
  ∑ j in Ico k m, f (n - j) = ∑ j in Ico (n + 1 - m) (n + 1 - k), f j :=
@prod_Ico_reflect (multiplicative δ) _ f k m n h

lemma prod_range_reflect (f : ℕ → β) (n : ℕ) :
  ∏ j in range n, f (n - 1 - j) = ∏ j in range n, f j :=
begin
  cases n,
  { simp },
  { simp only [←nat.Ico_zero_eq_range, nat.succ_sub_succ_eq_sub, tsub_zero],
    rw prod_Ico_reflect _ _ le_rfl,
    simp }
end

lemma sum_range_reflect {δ : Type*} [add_comm_monoid δ] (f : ℕ → δ) (n : ℕ) :
  ∑ j in range n, f (n - 1 - j) = ∑ j in range n, f j :=
@prod_range_reflect (multiplicative δ) _ f n

@[simp] lemma prod_Ico_id_eq_factorial : ∀ n : ℕ, ∏ x in Ico 1 (n + 1), x = n!
| 0 := rfl
| (n+1) := by rw [prod_Ico_succ_top $ nat.succ_le_succ $ zero_le n,
  nat.factorial_succ, prod_Ico_id_eq_factorial n, nat.succ_eq_add_one, mul_comm]

@[simp] lemma prod_range_add_one_eq_factorial : ∀ n : ℕ, ∏ x in range n, (x+1) = n!
| 0 := rfl
| (n+1) := by simp [finset.range_succ, prod_range_add_one_eq_factorial n]

section gauss_sum

/-- Gauss' summation formula -/
lemma sum_range_id_mul_two (n : ℕ) :
  (∑ i in range n, i) * 2 = n * (n - 1) :=
calc (∑ i in range n, i) * 2 = (∑ i in range n, i) + (∑ i in range n, (n - 1 - i)) :
  by rw [sum_range_reflect (λ i, i) n, mul_two]
... = ∑ i in range n, (i + (n - 1 - i)) : sum_add_distrib.symm
... = ∑ i in range n, (n - 1) : sum_congr rfl $ λ i hi, add_tsub_cancel_of_le $
  nat.le_pred_of_lt $ mem_range.1 hi
... = n * (n - 1) : by rw [sum_const, card_range, nat.nsmul_eq_mul]

/-- Gauss' summation formula -/
lemma sum_range_id (n : ℕ) : (∑ i in range n, i) = (n * (n - 1)) / 2 :=
by rw [← sum_range_id_mul_two n, nat.mul_div_cancel]; exact dec_trivial

end gauss_sum

end generic

section nat

variable {β : Type*}
variables (f g : ℕ → β) {m n : ℕ}

-- The partial sums (starting from `0`) of `f` and `g` respectively.
local notation `F` n:80 := ∑ i in range n, f i
local notation `G` n:80 := ∑ i in range n, g i

section monoid
variable [add_comm_monoid β]

lemma sum_Ico_empty : (∑ i in Ico n n, f i) = 0 :=
begin
  convert sum_empty,
  exact Ico_self n,
end

lemma sum_Ico_single : (∑ i in Ico n (n+1), f i) = f n :=
by rw [sum_eq_sum_Ico_succ_bot (lt_add_one n), sum_Ico_empty, add_zero]

lemma sum_Ico_sub {c: ℕ} (hm : c ≤ m) (hmn : m ≤ n) :
  ∑ (i : ℕ) in Ico (m-c) (n-c), f (i+c) = ∑ (i : ℕ) in Ico m n, f i :=
begin
  have hn : c ≤ n := le_trans hm hmn,
  conv in (f (_+c)) { rw add_comm },
  rw [sum_Ico_add f (m-c) (n-c), nat.sub_add_cancel hm, nat.sub_add_cancel hn],
end

end monoid

section group
variable [add_comm_group β]

lemma sum_Ico_succ_sub_sum_eq_top : F (n+1) - F n = f n :=
sub_eq_iff_eq_add'.mpr $ sum_range_succ f n

lemma sum_Ico_succ_sub_top_eq_sum : F (n+1) - f n = F n :=
by rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', sum_Ico_succ_sub_sum_eq_top]

lemma sum_Ico_succ_bot' (hmn : m < n) :
  ∑ i in Ico m n, f i - f m = ∑ i in Ico (m + 1) n, f i :=
begin
  have hmn1 : (m+1) ≤ n := nat.succ_le_iff.mpr hmn,
  rw [sub_eq_iff_eq_add', ← sum_Ico_single f, sum_Ico_consecutive _ m.le_succ hmn1],
end

lemma sum_Ico_succ_top' (hmn : m ≤ n) :
  ∑ i in Ico m (n+1), f i - f n = ∑ i in Ico m n, f i :=
by rw [sub_eq_iff_eq_add', add_comm (f n), ← sum_Ico_succ_top hmn]

end group

variable [comm_ring β]

/-- **Summation by parts**, also known as **Abel's lemma** or an **Abel transformation** -/
theorem sum_by_parts (hmn : m < n) :
  ∑ i in Ico m n, (f i * g i) =
    f (n-1) * G n - f m * G m - ∑ i in Ico m (n-1), G (i+1) * (f (i+1) - f i) :=
begin
  have hn   : 0 < n     := pos_of_gt hmn,
  have hmn1 : m ≤ n - 1 := nat.le_pred_of_lt hmn,
  have hm1  : 0 < m + 1 := m.succ_pos,
  have hm1n : m + 1 ≤ n := nat.succ_le_iff.mpr hmn,

  have h₁ : ∑ i in Ico (m+1) n, (f i * G i) = ∑ i in Ico m (n-1), (f (i+1) * G (i+1)) :=
    (sum_Ico_sub _ hm1 hm1n).symm,

  have h₂ := calc
        ∑ i in Ico (m+1) n, (f i * G (i+1))
      = ∑ i in Ico m n, (f i * G (i+1)) - f m * G(m+1) : by rw ← sum_Ico_succ_bot' _ hmn
  ... = ∑ i in Ico m (n-1), (f i * G (i+1)) + f (n-1) * G n - f m * G (m+1) :
          by rw [← sum_Ico_succ_top' _ hmn1, nat.sub_add_cancel hn, sub_add_cancel],

  have h₃ := calc
        ∑ i in Ico (m+1) n, (f i * g i)
      = ∑ i in Ico (m+1) n, (f i * G (i+1) - f i * G i) :
        by conv in (_ * _) { rw [← sum_Ico_succ_sub_sum_eq_top g, mul_sub_left_distrib] }
  ... = ∑ i in Ico (m+1) n, (f i * G (i+1)) - ∑ i in Ico (m+1) n, (f i * G i) :
        by rw sum_sub_distrib
  ... = ∑ i in Ico (m+1) n, (f i * G (i+1)) - ∑ i in Ico m (n-1), (f (i+1) * G (i+1)) : by rw h₁
  ... = ∑ i in Ico m (n-1), (f i * G (i+1)) + f (n-1) * G n - f m * G (m+1)
      - ∑ i in Ico m (n-1), (f (i+1) * G (i+1)) : by rw h₂
  ... = f (n-1) * G n - f m * G (m+1)
      + (∑ i in Ico m (n-1), (f i * G (i+1)) - ∑ i in Ico m (n-1), (f (i+1) * G (i+1))) : by ring
  ... = f (n-1) * G n - f m * G (m+1) + ∑ i in Ico m (n-1), (f i * G (i+1) - f (i+1) * G (i+1)) :
        by rw ← sum_sub_distrib
  ... = f (n-1) * G n - f m * G (m+1) + ∑ i in Ico m (n-1), -(G (i+1) * (f (i+1) - f i)) :
        begin congr' 2, funext, ring end
  ... = f (n-1) * G n - f m * G (m+1) - ∑ i in Ico m (n-1), G (i+1) * (f (i+1) - f i) :
        by rw [sum_neg_distrib, ← sub_eq_add_neg],

  exact calc
        ∑ i in Ico m n, (f i * g i)
      = f m * g m + ∑ i in Ico (m+1) n, (f i * g i)    : sum_eq_sum_Ico_succ_bot hmn _
  ... = f m * g m + (f (n-1) * G n - f m * G (m+1)
      - ∑ i in Ico m (n-1), G (i+1) * (f (i+1) - f i)) : by rw h₃
  ... = f (n-1) * G n - f m * (G (m+1) - g m)
      - ∑ i in Ico m (n-1), G (i+1) * (f (i+1) - f i)  : by ring
  ... = f (n-1) * G n - f m * G m
      - ∑ i in Ico m (n-1), G (i+1) * (f (i+1) - f i)  : by rw sum_Ico_succ_sub_top_eq_sum,
end

/-- **Summation by parts** for ranges -/
lemma sum_by_parts_range (hn : 0 < n) :
  ∑ i in range n, (f i * g i) =
    f (n-1) * G n - ∑ i in range (n-1), G (i+1) * (f (i+1) - f i) :=
begin
  rw [range_eq_Ico, sum_by_parts f g hn, sum_range_zero, mul_zero, sub_zero, range_eq_Ico],
end

end nat

end finset
