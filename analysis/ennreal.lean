/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Extended non-negative reals

TODO: base ennreal on nnreal!
-/
import order.bounds algebra.ordered_group analysis.nnreal analysis.topology.infinite_sum
noncomputable theory
open classical set lattice filter
local attribute [instance] prop_decidable
variables {α : Type*} {β : Type*}

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
inductive ennreal : Type
| of_nonneg_real : Πr:real, 0 ≤ r → ennreal
| infinity : ennreal

local notation `∞` := ennreal.infinity

namespace ennreal
variables {a b c d : ennreal} {r p q : ℝ}

section projections

/-- `of_real r` is the nonnegative extended real number `r` if `r` is nonnegative,
  otherwise 0. -/
def of_real (r : ℝ) : ennreal := of_nonneg_real (max 0 r) (le_max_left 0 r)

/-- `of_ennreal x` returns `x` if it is real, otherwise 0. -/
def of_ennreal : ennreal → ℝ
| (of_nonneg_real r _) := r
| ∞ := 0

@[simp] lemma of_ennreal_of_real (h : 0 ≤ r) : of_ennreal (of_real r) = r := max_eq_right h

lemma zero_le_of_ennreal : ∀{a}, 0 ≤ of_ennreal a
| (of_nonneg_real r hr) := hr
| ∞ := le_refl 0

@[simp] lemma of_real_of_ennreal : ∀{a}, a ≠ ∞ → of_real (of_ennreal a) = a
| (of_nonneg_real r hr) h := by simp [of_real, of_ennreal, max, hr]
| ∞ h := false.elim $ h rfl

lemma forall_ennreal {p : ennreal → Prop} : (∀a, p a) ↔ (∀r (h : 0 ≤ r), p (of_real r)) ∧ p ∞ :=
⟨assume h, ⟨assume r hr, h _, h _⟩,
  assume ⟨h₁, h₂⟩, ennreal.rec
    begin
      intros r hr,
      let h₁ := h₁ r hr,
      simp [of_real, max, hr] at h₁,
      exact h₁
    end
    h₂⟩

end projections

section semiring

instance : has_zero ennreal := ⟨of_real 0⟩
instance : has_one ennreal := ⟨of_real 1⟩
instance : inhabited ennreal := ⟨0⟩

@[simp] lemma of_real_zero : of_real 0 = 0 := rfl
@[simp] lemma of_real_one : of_real 1 = 1 := rfl

@[simp] lemma zero_ne_infty : 0 ≠ ∞ := assume h, ennreal.no_confusion h
@[simp] lemma infty_ne_zero : ∞ ≠ 0 := assume h, ennreal.no_confusion h

@[simp] lemma of_real_ne_infty : of_real r ≠ ∞ := assume h, ennreal.no_confusion h
@[simp] lemma infty_ne_of_real : ∞ ≠ of_real r := assume h, ennreal.no_confusion h

@[simp] lemma of_real_eq_of_real_of (hr : 0 ≤ r) (hq : 0 ≤ q) : of_real r = of_real q ↔ r = q :=
by simp [of_real, max, hr, hq]; exact ⟨ennreal.of_nonneg_real.inj, by simp {contextual := tt}⟩

lemma of_real_ne_of_real_of (hr : 0 ≤ r) (hq : 0 ≤ q) : of_real r ≠ of_real q ↔ r ≠ q :=
by simp [hr, hq]

lemma of_real_of_nonpos (hr : r ≤ 0) : of_real r = 0 :=
have ∀r₁ r₂ : real, r₁ = r₂ → ∀h₁:0≤r₁, ∀h₂:0≤r₂, of_nonneg_real r₁ h₁ = of_nonneg_real r₂ h₂,
  from assume r₁ r₂ h, match r₁, r₂, h with _, _, rfl := assume _ _, rfl end,
this _ _ (by simp [hr, max_eq_left]) _ _

lemma of_real_of_not_nonneg (hr : ¬ 0 ≤ r) : of_real r = 0 :=
of_real_of_nonpos $ le_of_lt $ lt_of_not_ge hr

instance : zero_ne_one_class ennreal :=
{ zero := 0, one := 1, zero_ne_one := (of_real_ne_of_real_of (le_refl 0) zero_le_one).mpr zero_ne_one }

@[simp] lemma of_real_eq_zero_iff (hr : 0 ≤ r) : of_real r = 0 ↔ r = 0 :=
of_real_eq_of_real_of hr (le_refl 0)

@[simp] lemma zero_eq_of_real_iff (hr : 0 ≤ r) : 0 = of_real r ↔ 0 = r :=
of_real_eq_of_real_of (le_refl 0) hr

@[simp] lemma of_real_eq_one_iff : of_real r = 1 ↔ r = 1 :=
match le_total 0 r with
| or.inl h := of_real_eq_of_real_of h zero_le_one
| or.inr h :=
  have r ≠ 1, from assume h', lt_irrefl (0:ℝ) $ lt_of_lt_of_le (by rw [h']; exact zero_lt_one) h,
  by simp [of_real_of_nonpos h, this]
end

@[simp] lemma one_eq_of_real_iff : 1 = of_real r ↔ 1 = r :=
by rw [eq_comm, of_real_eq_one_iff, eq_comm]

lemma of_nonneg_real_eq_of_real (hr : 0 ≤ r) : of_nonneg_real r hr = of_real r :=
by simp [of_real, hr, max]

protected def add : ennreal → ennreal → ennreal
| (of_nonneg_real a ha) (of_nonneg_real b hb) := of_real (a + b)
| _ _ := ∞

protected def mul : ennreal → ennreal → ennreal
| (of_nonneg_real a ha) (of_nonneg_real b hb) := of_real (a * b)
| ∞ (of_nonneg_real b hb) := if b = 0 then 0 else ∞
| (of_nonneg_real a ha) ∞ := if a = 0 then 0 else ∞
| _ _ := ∞

instance : has_add ennreal := ⟨ennreal.add⟩
instance : has_mul ennreal := ⟨ennreal.mul⟩

@[simp] lemma of_real_add (hr : 0 ≤ r) (hq : 0 ≤ p) :
  of_real r + of_real p = of_real (r + p) :=
by simp [of_real, max, hr, hq, add_comm]; refl

@[simp] lemma add_infty : a + ∞ = ∞ :=
by cases a; refl

@[simp] lemma infty_add : ∞ + a = ∞ :=
by cases a; refl

@[simp] lemma of_real_mul_of_real (hr : 0 ≤ r) (hq : 0 ≤ p) :
  of_real r * of_real p = of_real (r * p) :=
by simp [of_real, max, hr, hq]; refl

@[simp] lemma of_real_mul_infty (hr : 0 ≤ r) : of_real r * ∞ = (if r = 0 then 0 else ∞) :=
by simp [of_real, max, hr]; refl

@[simp] lemma infty_mul_of_real (hr : 0 ≤ r) : ∞ * of_real r = (if r = 0 then 0 else ∞) :=
by simp [of_real, max, hr]; refl

@[simp] lemma mul_infty : ∀{a}, a * ∞ = (if a = 0 then 0 else ∞) :=
forall_ennreal.mpr ⟨assume r hr, by simp [hr]; by_cases r = 0; simp [h], by simp; refl⟩

@[simp] lemma infty_mul : ∀{a}, ∞ * a = (if a = 0 then 0 else ∞) :=
forall_ennreal.mpr ⟨assume r hr, by simp [hr]; by_cases r = 0; simp [h], by simp; refl⟩

instance : add_comm_monoid ennreal :=
{ zero := 0,
  add  := (+),
  add_zero := forall_ennreal.2 ⟨λ a ha,
    by rw [← of_real_zero, of_real_add ha (le_refl _), add_zero], by simp⟩,
  zero_add := forall_ennreal.2 ⟨λ a ha,
    by rw [← of_real_zero, of_real_add (le_refl _) ha, zero_add], by simp⟩,
  add_comm := begin
    refine forall_ennreal.2 ⟨λ a ha, _, by simp⟩,
    refine forall_ennreal.2 ⟨λ b hb, _, by simp⟩,
    rw [of_real_add ha hb, of_real_add hb ha, add_comm]
  end,
  add_assoc := begin
    refine forall_ennreal.2 ⟨λ a ha, _, by simp⟩,
    refine forall_ennreal.2 ⟨λ b hb, _, by simp⟩,
    refine forall_ennreal.2 ⟨λ c hc, _, by simp⟩,
    rw [of_real_add ha hb, of_real_add (add_nonneg ha hb) hc,
        of_real_add hb hc, of_real_add ha (add_nonneg hb hc), add_assoc],
  end }

@[simp] lemma sum_of_real {α : Type*} {s : finset α} {f : α → ℝ} :
  (∀a∈s, 0 ≤ f a) → s.sum (λa, of_real (f a)) = of_real (s.sum f) :=
finset.induction_on s (by simp) $ assume a s has ih h,
  have 0 ≤ s.sum f, from finset.zero_le_sum $ assume a ha, h a $ finset.mem_insert_of_mem ha,
  by simp [has, *] {contextual := tt}

protected lemma mul_zero : ∀a:ennreal, a * 0 = 0 :=
by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual := tt}

protected lemma mul_comm : ∀a b:ennreal, a * b = b * a :=
by simp [forall_ennreal, mul_comm] {contextual := tt}

protected lemma zero_mul : ∀a:ennreal, 0 * a = 0 :=
by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual := tt}

protected lemma mul_assoc : ∀a b c:ennreal, a * b * c = a * (b * c) :=
begin
  rw [forall_ennreal], constructor,
  { intros ra ha,
    by_cases ha' : ra = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rb hrb,
      by_cases hb' : rb = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
      rw [forall_ennreal], constructor,
      { intros rc hrc, simp [*, zero_le_mul, mul_assoc] },
      simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
    rw [forall_ennreal], constructor,
      { intros rc hrc,
        by_cases hc' : rc = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
        simp [*, zero_le_mul] },
    simp [*] },
  rw [forall_ennreal], constructor,
  { intros rb hrb,
    by_cases hb' : rb = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rc hrc,
      by_cases hb' : rc = 0;
        simp [*, zero_le_mul, ennreal.mul_zero, mul_eq_zero_iff_eq_zero_or_eq_zero] },
    simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
  intro c, by_cases c = 0; simp *
end

protected lemma left_distrib : ∀a b c:ennreal, a * (b + c) = a * b + a * c :=
begin
  rw [forall_ennreal], constructor,
  { intros ra ha,
    by_cases ha' : ra = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rb hrb,
      by_cases hb' : rb = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
      rw [forall_ennreal], constructor,
      { intros rc hrc, simp [*, zero_le_mul, add_nonneg, left_distrib] },
      simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
    rw [forall_ennreal], constructor,
      { intros rc hrc,
        by_cases hv' : rc = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
        simp [*, zero_le_mul] },
    simp [*] },
  rw [forall_ennreal], constructor,
  { intros rb hrb,
    by_cases hb' : rb = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rc hrc,
      by_cases hb' : rc = 0;
        simp [*, zero_le_mul, ennreal.mul_zero, mul_eq_zero_iff_eq_zero_or_eq_zero, add_nonneg,
          add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg] },
    simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
  intro c, by_cases c = 0; simp [*]
end

instance : comm_semiring ennreal :=
{ one  := 1,
  mul  := (*),
  mul_zero := ennreal.mul_zero,
  zero_mul := ennreal.zero_mul,
  one_mul := by simp [forall_ennreal, -of_real_one, of_real_one.symm, zero_le_one] {contextual := tt},
  mul_one := by simp [forall_ennreal, -of_real_one, of_real_one.symm, zero_le_one] {contextual := tt},
  mul_comm := ennreal.mul_comm,
  mul_assoc := ennreal.mul_assoc,
  left_distrib := ennreal.left_distrib,
  right_distrib := assume a b c, by rw [ennreal.mul_comm, ennreal.left_distrib,
    ennreal.mul_comm, ennreal.mul_comm b c]; refl,
  ..ennreal.add_comm_monoid }

end semiring

section order

instance : has_le ennreal := ⟨λ a b, b = ∞ ∨ (∃r p, 0 ≤ r ∧ r ≤ p ∧ a = of_real r ∧ b = of_real p)⟩

theorem le_def : a ≤ b ↔ b = ∞ ∨ (∃r p, 0 ≤ r ∧ r ≤ p ∧ a = of_real r ∧ b = of_real p) := iff.rfl

@[simp] lemma infty_le_iff : ∞ ≤ a ↔ a = ∞ :=
by simp [le_def]

@[simp] lemma le_infty : a ≤ ∞ :=
by simp [le_def]

@[simp] lemma of_real_le_of_real_iff (hr : 0 ≤ r) (hp : 0 ≤ p) :
  of_real r ≤ of_real p ↔ r ≤ p :=
by simpa [le_def] using show (∃ (r' : ℝ), 0 ≤ r' ∧ ∃ (q : ℝ), r' ≤ q ∧
  of_real r = of_real r' ∧ of_real p = of_real q) ↔ r ≤ p, from
⟨λ ⟨r', hr', q, hrq, h₁, h₂⟩,
  by simp [hr, hr', le_trans hr' hrq, hp] at h₁ h₂; simp *,
 λ h, ⟨r, hr, p, h, rfl, rfl⟩⟩

@[simp] lemma one_le_of_real_iff (hr : 0 ≤ r) : 1 ≤ of_real r ↔ 1 ≤ r :=
of_real_le_of_real_iff zero_le_one hr

instance : decidable_linear_order ennreal :=
{ le           := (≤),
  le_refl      := by simp [forall_ennreal, le_refl] {contextual := tt},
  le_trans     := by simp [forall_ennreal] {contextual := tt}; exact assume a ha b hb c hc, le_trans,
  le_antisymm  := by simp [forall_ennreal] {contextual := tt}; exact assume a ha b hb, le_antisymm,
  le_total     := by simp [forall_ennreal] {contextual := tt}; exact assume a ha b hb, le_total _ _,
  decidable_le := by apply_instance }

@[simp] lemma not_infty_lt : ¬ ∞ < a :=
by simp

@[simp] lemma of_real_lt_infty : of_real r < ∞ :=
⟨le_infty, assume h, ennreal.no_confusion $ infty_le_iff.mp h⟩

lemma le_of_real_iff (hr : 0 ≤ r) : ∀{a}, a ≤ of_real r ↔ (∃p, 0 ≤ p ∧ p ≤ r ∧ a = of_real p) :=
have ∀p, 0 ≤ p → (of_real p ≤ of_real r ↔ ∃ (q : ℝ), 0 ≤ q ∧ q ≤ r ∧ of_real p = of_real q),
  from assume p hp, ⟨assume h, ⟨p, hp, (of_real_le_of_real_iff hp hr).mp h, rfl⟩,
    assume ⟨q, hq, hqr, heq⟩, calc of_real p = of_real q : heq
      ... ≤ _ : (of_real_le_of_real_iff hq hr).mpr hqr⟩,
forall_ennreal.mpr $ ⟨this, by simp⟩

@[simp] lemma of_real_lt_of_real_iff :
  0 ≤ r → 0 ≤ p → (of_real r < of_real p ↔ r < p) :=
by simp [lt_iff_le_not_le, -not_le] {contextual:=tt}

lemma lt_iff_exists_of_real : ∀{a b}, a < b ↔ (∃p, 0 ≤ p ∧ a = of_real p ∧ of_real p < b) :=
by simp [forall_ennreal]; exact λ r hr,
⟨λ p hp, ⟨λ h, ⟨r, by simp *⟩, λ ⟨q, h₁, h₂, h₃⟩, by simp * at *⟩, r, hr, rfl⟩

@[simp] protected lemma zero_le : ∀{a:ennreal}, 0 ≤ a :=
by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual:=tt}

@[simp] lemma le_zero_iff_eq : a ≤ 0 ↔ a = 0 :=
⟨assume h, le_antisymm h ennreal.zero_le, assume h, h ▸ le_refl a⟩

@[simp] lemma zero_lt_of_real_iff : 0 < of_real p ↔ 0 < p :=
by_cases
  (assume : 0 ≤ p, of_real_lt_of_real_iff (le_refl _) this)
  (by simp [lt_irrefl, not_imp_not, le_of_lt, of_real_of_not_nonneg] {contextual := tt})

@[simp] lemma not_lt_zero : ¬ a < 0 :=
by simp

protected lemma zero_lt_one : 0 < (1 : ennreal) :=
zero_lt_of_real_iff.mpr zero_lt_one

lemma of_real_le_of_real (h : r ≤ p) : of_real r ≤ of_real p :=
match le_total 0 r with
| or.inl hr := (of_real_le_of_real_iff hr $ le_trans hr h).mpr h
| or.inr hr := by simp [of_real_of_nonpos, hr, zero_le]
end

lemma of_real_lt_of_real_iff_cases : of_real r < of_real p ↔ 0 < p ∧ r < p :=
begin
  by_cases hp : 0 ≤ p,
  { by_cases hr : 0 ≤ r,
    { simp [*, iff_def] {contextual := tt},
      show r < p → 0 < p, from lt_of_le_of_lt hr },
    { have h : r ≤ 0, from le_of_lt (lt_of_not_ge hr),
      simp [*, of_real_of_not_nonneg, and_iff_left_of_imp (lt_of_le_of_lt h)] } },
  simp [*, not_le, not_lt, le_of_lt, of_real_of_not_nonneg, and_comm] at *
end

instance : densely_ordered ennreal :=
⟨by simp [forall_ennreal, of_real_lt_of_real_iff_cases]; exact
λ r hr, ⟨λ p _ _ h,
  let ⟨q, h₁, h₂⟩ := dense h in
  have 0 ≤ q, from le_trans hr $ le_of_lt h₁,
  ⟨of_real q, by simp *⟩,
of_real (r + 1), by simp [hr, add_nonneg, lt_add_of_le_of_pos, zero_le_one, zero_lt_one]⟩⟩

private lemma add_le_add : ∀{b d}, a ≤ b → c ≤ d → a + c ≤ b + d :=
forall_ennreal.mpr ⟨assume r hr, forall_ennreal.mpr ⟨assume p hp,
  by simp [le_of_real_iff, *, exists_imp_distrib, -and_imp] {contextual:=tt};
    simp [*, add_nonneg, add_le_add] {contextual := tt}, by simp⟩, by simp⟩

private lemma lt_of_add_lt_add_left (h : a + b < a + c) : b < c :=
lt_of_not_ge $ assume h', lt_irrefl (a + b) (lt_of_lt_of_le h $ add_le_add (le_refl a) h')

instance : ordered_comm_monoid ennreal :=
{ add_le_add_left       := assume a b h c, add_le_add (le_refl c) h,
  lt_of_add_lt_add_left := assume a b c, lt_of_add_lt_add_left,
  ..ennreal.add_comm_monoid, ..ennreal.decidable_linear_order }

lemma le_add_left (h : a ≤ c) : a ≤ b + c :=
calc a = 0 + a : by simp
  ... ≤ b + c : add_le_add ennreal.zero_le h

lemma le_add_right (h : a ≤ b) : a ≤ b + c :=
calc a = a + 0 : by simp
  ... ≤ b + c : add_le_add h ennreal.zero_le

lemma lt_add_right : ∀{a b}, a < ∞ → 0 < b → a < a + b :=
by simp [forall_ennreal, of_real_lt_of_real_iff, add_nonneg, lt_add_of_le_of_pos] {contextual := tt}

instance : canonically_ordered_monoid ennreal :=
{ le_iff_exists_add := by simp [forall_ennreal] {contextual:=tt}; exact
    λ r hr, ⟨λ p hp,
      ⟨λ h, ⟨of_real (p - r),
        by rw [of_real_add (sub_nonneg.2 h) hr, sub_add_cancel]⟩,
      λ ⟨c, hc⟩, by rw [← of_real_le_of_real_iff hr hp, hc]; exact le_add_left (le_refl _)⟩,
    ⟨∞, by simp⟩⟩,
  ..ennreal.ordered_comm_monoid }

lemma mul_le_mul : ∀{b d}, a ≤ b → c ≤ d → a * c ≤ b * d :=
forall_ennreal.mpr ⟨assume r hr, forall_ennreal.mpr ⟨assume p hp,
  by simp [le_of_real_iff, *, exists_imp_distrib, -and_imp] {contextual:=tt};
    simp [*, zero_le_mul, mul_le_mul] {contextual := tt},
    by by_cases r = 0; simp [*] {contextual:=tt}⟩,
    assume d, by by_cases d = 0; simp [*] {contextual:=tt}⟩

lemma le_of_forall_epsilon_le (h : ∀ε>0, b < ∞ → a ≤ b + of_real ε) : a ≤ b :=
suffices ∀r, 0 ≤ r → of_real r > b → a ≤ of_real r,
  from le_of_forall_le_of_dense $ forall_ennreal.mpr $ by simp; assumption,
assume r hr hrb,
let ⟨p, hp, b_eq, hpr⟩ := lt_iff_exists_of_real.mp hrb in
have p < r, by simp [hp, hr] at hpr; assumption,
have pos : 0 < r - p, from lt_sub_iff_add_lt.mpr $ by simp [this],
calc a ≤ b + of_real (r - p) : h _ pos (by simp [b_eq])
  ... = of_real r :
    by simp [-sub_eq_add_neg, le_of_lt pos, hp, hr, b_eq]; simp [sub_eq_add_neg]

protected lemma lt_iff_exists_rat_btwn :
  a < b ↔ (∃q:ℚ, 0 ≤ q ∧ a < of_real q ∧ of_real q < b) :=
⟨λ h, by
  rcases lt_iff_exists_of_real.1 h with ⟨p, p0, rfl, _⟩;
  rcases dense h with ⟨c, pc, cb⟩;
  rcases lt_iff_exists_of_real.1 cb with ⟨r, r0, rfl, _⟩;
  rcases exists_rat_btwn ((of_real_lt_of_real_iff p0 r0).1 pc) with ⟨q, pq, qr⟩;
  have q0 := le_trans p0 (le_of_lt pq); exact
  ⟨q, rat.cast_nonneg.1 q0, (of_real_lt_of_real_iff p0 q0).2 pq,
    lt_trans ((of_real_lt_of_real_iff q0 r0).2 qr) cb⟩,
λ ⟨q, q0, qa, qb⟩, lt_trans qa qb⟩

end order

section complete_lattice

@[simp] lemma infty_mem_upper_bounds {s : set ennreal} : ∞ ∈ upper_bounds s :=
assume x hx, le_infty

lemma of_real_mem_upper_bounds {s : set real} (hs : ∀x∈s, (0:real) ≤ x) (hr : 0 ≤ r) :
  of_real r ∈ upper_bounds (of_real '' s) ↔ r ∈ upper_bounds s :=
by simp [upper_bounds, ball_image_iff, -mem_image, *] {contextual := tt}

lemma is_lub_of_real {s : set real} (hs : ∀x∈s, (0:real) ≤ x) (hr : 0 ≤ r) (h : s ≠ ∅) :
  is_lub (of_real '' s) (of_real r) ↔ is_lub s r :=
let ⟨x, hx₁⟩ := exists_mem_of_ne_empty h in
have hx₂ : 0 ≤ x, from hs _ hx₁,
begin
  simp [is_lub, is_least, lower_bounds, of_real_mem_upper_bounds, hs, hr, forall_ennreal]
    {contextual := tt},
  exact (and_congr_right $ assume hrb,
    ⟨assume h p hp, h _ (le_trans hx₂ $ hp _ hx₁) hp, assume h p _ hp, h _ hp⟩)
end

protected lemma exists_is_lub (s : set ennreal) : ∃x, is_lub s x :=
by_cases (assume h : s = ∅, ⟨0, by simp [h, is_lub, is_least, lower_bounds, upper_bounds]⟩) $
  assume h : s ≠ ∅,
  let ⟨x, hx⟩ := exists_mem_of_ne_empty h in
  by_cases
    (assume : ∃r, 0 ≤ r ∧ of_real r ∈ upper_bounds s,
      let ⟨r, hr, hb⟩ := this in
      let s' := of_real ⁻¹' s ∩ {x | 0 ≤ x} in
      have s'_nn : ∀x∈s', (0:real) ≤ x, from assume x h, h.right,
      have s_eq : s = of_real '' s',
        from set.ext $ assume a, ⟨assume ha,
          let ⟨q, hq₁, hq₂, hq₃⟩ := (le_of_real_iff hr).mp (hb _ ha) in
          ⟨q, ⟨show of_real q ∈ s, from hq₃ ▸ ha, hq₁⟩, hq₃ ▸ rfl⟩,
          assume ⟨r, ⟨hr₁, hr₂⟩, hr₃⟩, hr₃ ▸ hr₁⟩,
      have x ∈ of_real '' s', from s_eq ▸ hx,
      let ⟨x', hx', hx'_eq⟩ := this in
      have ∃x, is_lub s' x, from exists_supremum_real ‹x' ∈ s'› $
        (of_real_mem_upper_bounds s'_nn hr).mp $ s_eq ▸ hb,
      let ⟨x, hx⟩ := this in
      have 0 ≤ x, from le_trans hx'.right $ hx.left _ hx',
      ⟨of_real x, by rwa [s_eq, is_lub_of_real s'_nn this]; exact ne_empty_of_mem hx'⟩)
    begin
      intro h,
      existsi ∞,
      simp [is_lub, is_least, lower_bounds, forall_ennreal, not_exists, not_and] at h ⊢,
      assumption
    end

instance : has_Sup ennreal := ⟨λs, some (ennreal.exists_is_lub s)⟩

protected lemma is_lub_Sup {s : set ennreal} : is_lub s (Sup s) :=
some_spec _

protected lemma le_Sup {s : set ennreal} : a ∈ s → a ≤ Sup s :=
ennreal.is_lub_Sup.left a

protected lemma Sup_le {s : set ennreal} : (∀b ∈ s, b ≤ a) → Sup s ≤ a :=
ennreal.is_lub_Sup.right _

instance : complete_linear_order ennreal :=
{ top := ∞,
  bot := 0,
  inf := min,
  sup := max,
  Sup := Sup,
  Inf := λs, Sup {a | ∀b ∈ s, a ≤ b},
  le_top       := assume a, le_infty,
  bot_le       := assume a, ennreal.zero_le,
  le_sup_left  := le_max_left,
  le_sup_right := le_max_right,
  sup_le       := assume a b c, max_le,
  inf_le_left  := min_le_left,
  inf_le_right := min_le_right,
  le_inf       := assume a b c, le_min,
  le_Sup       := assume s a, ennreal.le_Sup,
  Sup_le       := assume s a, ennreal.Sup_le,
  le_Inf       := assume s a h, ennreal.le_Sup h,
  Inf_le       := assume s a ha, ennreal.Sup_le $ assume b hb, hb _ ha,
  ..ennreal.decidable_linear_order }

@[simp] protected lemma bot_eq_zero : (⊥ : ennreal) = 0 := rfl
@[simp] protected lemma top_eq_infty : (⊤ : ennreal) = ∞ := rfl

end complete_lattice

section topological_space
open topological_space

instance : topological_space ennreal :=
topological_space.generate_from {s | ∃a, s = {b | a < b} ∨ s = {b | b < a}}

instance : orderable_topology ennreal := ⟨rfl⟩

instance : t2_space ennreal := by apply_instance

instance : second_countable_topology ennreal :=
⟨⟨⋃q ≥ (0:ℚ), {{a : ennreal | a < of_real q}, {a : ennreal | of_real ↑q < a}},
  countable_bUnion countable_encodable $ assume a ha, countable_insert countable_singleton,
  le_antisymm
    (generate_from_le $ λ s h, begin
      rcases h with ⟨a, hs | hs⟩;
      [ rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ a < of_real q}, {b | of_real q < b},
           from set.ext (assume b, by simp [hs, @ennreal.lt_iff_exists_rat_btwn a b, and_assoc]),
        rw show s = ⋃q∈{q:ℚ | 0 ≤ q ∧ of_real q < a}, {b | b < of_real q},
           from set.ext (assume b, by simp [hs, @ennreal.lt_iff_exists_rat_btwn b a, and_comm, and_assoc])];
      { apply is_open_Union, intro q,
        apply is_open_Union, intro hq,
        exact generate_open.basic _ (mem_bUnion hq.1 $ by simp) }
    end)
    (generate_from_le $ by simp [or_imp_distrib, is_open_lt', is_open_gt'] {contextual := tt})⟩⟩

lemma continuous_of_real : continuous of_real :=
have ∀x:ennreal, is_open {a : ℝ | x < of_real a},
  from forall_ennreal.mpr ⟨assume r hr,
    by simp [of_real_lt_of_real_iff_cases]; exact is_open_and (is_open_lt' 0) (is_open_lt' r),
    by simp⟩,
have ∀x:ennreal, is_open {a : ℝ | of_real a < x},
  from forall_ennreal.mpr ⟨assume r hr,
    by simp [of_real_lt_of_real_iff_cases]; exact is_open_and is_open_const (is_open_gt' r),
    by simp [is_open_const]⟩,
continuous_generated_from $ begin simp [or_imp_distrib, *] {contextual := tt} end

lemma tendsto_of_real : tendsto of_real (nhds r) (nhds (of_real r)) :=
continuous_iff_tendsto.mp continuous_of_real r

lemma tendsto_of_ennreal (hr : 0 ≤ r) : tendsto of_ennreal (nhds (of_real r)) (nhds r) :=
tendsto_orderable_unbounded (no_top _) (no_bot _) $
assume l u hl hu,
by_cases
  (assume hr : r = 0,
    have hl : l < 0, by rw [hr] at hl; exact hl,
    have hu : 0 < u, by rw [hr] at hu; exact hu,
    have nhds (of_real r) = (⨅l (h₂ : 0 < l), principal {x | x < l}),
      from calc nhds (of_real r) = nhds ⊥ : by simp [hr]; refl
        ... = (⨅u (h₂ : 0 < u), principal {x | x < u}) : nhds_bot_orderable,
    have {x | x < of_real u} ∈ (nhds (of_real r)).sets,
      by rw [this];
      from mem_infi_sets (of_real u) (mem_infi_sets (by simp *) (subset.refl _)),
    ((nhds (of_real r)).upwards_sets this $ forall_ennreal.mpr $
        by simp [le_of_lt, hu, hl] {contextual := tt}; exact assume p hp _, lt_of_lt_of_le hl hp))
  (assume hr_ne : r ≠ 0,
    have hu0 : 0 < u, from lt_of_le_of_lt hr hu,
    have hu_nn: 0 ≤ u, from le_of_lt hu0,
    have hr' : 0 < r, from lt_of_le_of_ne hr hr_ne.symm,
    have hl' : ∃l, l < of_real r, from ⟨0, by simp [hr, hr']⟩,
    have hu' : ∃u, of_real r < u, from ⟨of_real u, by simp [hr, hu_nn, hu]⟩,
    begin
      rw [mem_nhds_unbounded hu' hl'],
      existsi (of_real l), existsi (of_real u),
      simp [*, of_real_lt_of_real_iff_cases, forall_ennreal] {contextual := tt}
    end)

lemma nhds_of_real_eq_map_of_real_nhds {r : ℝ} (hr : 0 ≤ r) :
  nhds (of_real r) = (nhds r).map of_real :=
have h₁ : {x | x < ∞} ∈ (nhds (of_real r)).sets,
  from mem_nhds_sets (is_open_gt' ∞) of_real_lt_infty,
have h₂ : {x | x < ∞} ∈ ((nhds r).map of_real).sets,
  from mem_map.mpr $ univ_mem_sets' $ assume a, of_real_lt_infty,
have h : ∀x<∞, ∀y<∞, of_ennreal x = of_ennreal y → x = y,
  by simp [forall_ennreal] {contextual:=tt},
le_antisymm
  (by_cases
    (assume (hr : r = 0) s (hs : {x | of_real x ∈ s} ∈ (nhds r).sets),
      have hs : {x | of_real x ∈ s} ∈ (nhds (0:ℝ)).sets, from hr ▸ hs,
      let ⟨l, u, hl, hu, h⟩ := (mem_nhds_unbounded (no_top 0) (no_bot 0)).mp hs in
      have nhds (of_real r) = nhds ⊥, by simp [hr]; refl,
      begin
        rw [this, nhds_bot_orderable],
        apply mem_infi_sets (of_real u) _,
        apply mem_infi_sets (zero_lt_of_real_iff.mpr hu) _,
        simp [set.subset_def],
        intro x, rw [lt_iff_exists_of_real],
        simp [le_of_lt hu] {contextual := tt},
        exact assume p hp _ hpu, h _ (lt_of_lt_of_le hl hp) hpu
      end)
    (assume : r ≠ 0,
      have hr' : 0 < r, from lt_of_le_of_ne hr this.symm,
      have h' : map (of_ennreal ∘ of_real) (nhds r) = map id (nhds r),
        from map_cong $ (nhds r).upwards_sets (mem_nhds_sets (is_open_lt' 0) hr') $
          assume r hr, by simp [le_of_lt hr, (∘)],
      le_of_map_le_map_inj' h₁ h₂ h $ le_trans (tendsto_of_ennreal hr) $ by simp [h']))
  tendsto_of_real

lemma nhds_of_real_eq_map_of_real_nhds_nonneg {r : ℝ} (hr : 0 ≤ r) :
  nhds (of_real r) = (nhds r ⊓ principal {x | 0 ≤ x}).map of_real :=
by rw [nhds_of_real_eq_map_of_real_nhds hr];
from by_cases
  (assume : r = 0,
    le_antisymm
      (assume s (hs : {a | of_real a ∈ s} ∈ (nhds r ⊓ principal {x | 0 ≤ x}).sets),
        let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := mem_inf_sets.mp hs in
        show {a | of_real a ∈ s} ∈ (nhds r).sets,
          from (nhds r).upwards_sets ht₁ $ assume a ha,
          match le_total 0 a with
          | or.inl h := have a ∈ t₂, from ht₂ h, ht ⟨ha, this⟩
          | or.inr h :=
            have r ∈ t₁ ∩ t₂, from ⟨mem_of_nhds ht₁, ht₂ (le_of_eq ‹r = 0›.symm)⟩,
            have of_real 0 ∈ s, from ‹r = 0› ▸ ht this,
            by simp [of_real_of_nonpos h]; assumption
          end)
      (map_mono inf_le_left))
  (assume : r ≠ 0,
    have 0 < r, from lt_of_le_of_ne hr this.symm,
    have nhds r ⊓ principal {x : ℝ | 0 ≤ x} = nhds r,
      from inf_of_le_left $ le_principal_iff.mpr $ le_mem_nhds this,
    by simp [*])

instance : topological_add_monoid ennreal :=
have hinf : ∀a, tendsto (λ(p : ennreal × ennreal), p.1 + p.2) ((nhds ∞).prod (nhds a)) (nhds ⊤),
begin
  intro a,
  rw [nhds_top_orderable],
  apply tendsto_infi.2 _, intro b,
  apply tendsto_infi.2 _, intro hb,
  apply tendsto_principal.2 _,
  revert b,
  simp [forall_ennreal],
  exact assume r hr, mem_prod_iff.mpr ⟨
    {a | of_real r < a}, mem_nhds_sets (is_open_lt' _) of_real_lt_infty,
    univ, univ_mem_sets, assume ⟨c, d⟩ ⟨hc, _⟩, lt_of_lt_of_le hc $ le_add_right $ le_refl _⟩
end,
have h : ∀{p r : ℝ}, 0 ≤ p → 0 ≤ r → tendsto (λp:ennreal×ennreal, p.1 + p.2)
    ((nhds (of_real r)).prod (nhds (of_real p))) (nhds (of_real (r + p))),
  from assume p r hp hr,
  begin
    rw [nhds_of_real_eq_map_of_real_nhds_nonneg hp, nhds_of_real_eq_map_of_real_nhds_nonneg hr,
      prod_map_map_eq, ←prod_inf_prod, prod_principal_principal, ←nhds_prod_eq],
    exact tendsto_map' (tendsto_cong
      (tendsto_le_left inf_le_left $ tendsto_add'.comp tendsto_of_real)
      (mem_inf_sets_of_right $ mem_principal_sets.mpr $ by simp [subset_def, (∘)] {contextual:=tt}))
  end,
have ∀{a₁ a₂ : ennreal}, tendsto (λp:ennreal×ennreal, p.1 + p.2) (nhds (a₁, a₂)) (nhds (a₁ + a₂)),
  from forall_ennreal.mpr ⟨assume r hr, forall_ennreal.mpr
    ⟨assume p hp, by simp [*, nhds_prod_eq]; exact h _ _,
      begin
        rw [nhds_prod_eq, prod_comm],
        apply tendsto_map' _,
        simp [(∘)],
        exact hinf _
      end⟩,
    by simp [nhds_prod_eq]; exact hinf⟩,
⟨continuous_iff_tendsto.mpr $ assume ⟨a₁, a₂⟩, this⟩

protected lemma tendsto_mul : ∀{a b : ennreal}, b ≠ 0 → tendsto ((*) a) (nhds b) (nhds (a * b)) :=
forall_ennreal.mpr $ and.intro
  (assume p hp, forall_ennreal.mpr $ and.intro
    (assume r hr hr0,
      have r ≠ 0, from assume h, by simp [h] at hr0; contradiction,
      have 0 < r, from lt_of_le_of_ne hr this.symm,
      have tendsto (λr, of_real (p * r)) (nhds r ⊓ principal {x : ℝ | 0 ≤ x}) (nhds (of_real (p * r))),
        from tendsto.comp (tendsto_mul tendsto_const_nhds $ tendsto_id' inf_le_left) tendsto_of_real,
      begin
        rw [nhds_of_real_eq_map_of_real_nhds_nonneg hr, of_real_mul_of_real hp hr],
        apply tendsto_map' (tendsto_cong this $ mem_inf_sets_of_right $ mem_principal_sets.mpr _),
        simp [subset_def, (∘), hp] {contextual := tt}
      end)
    (assume _, by_cases
      (assume : p = 0,
        tendsto_cong tendsto_const_nhds $
        (nhds ∞).upwards_sets (mem_nhds_sets (is_open_lt' _) (@of_real_lt_infty 1)) $
        by simp [this])
      (assume p0 : p ≠ 0,
        have p_pos : 0 < p, from lt_of_le_of_ne hp p0.symm,
        suffices tendsto ((*) (of_real p)) (nhds ⊤) (nhds ⊤), { simpa [hp, p0] },
        by rw [nhds_top_orderable];
        from (tendsto_infi.2 $ assume l, tendsto_infi.2 $ assume hl,
          let ⟨q, hq, hlq, _⟩ := ennreal.lt_iff_exists_of_real.mp hl in
          tendsto_infi' (of_real (q / p)) $ tendsto_infi' of_real_lt_infty $ tendsto_principal_principal.2 $
          forall_ennreal.mpr $ and.intro
            begin
              have : ∀r:ℝ, 0 < r → q / p < r → q < p * r ∧ 0 < p * r,
                from assume r r_pos qpr,
                have q < p * r,
                  from calc q = (q / p) * p : by rw [div_mul_cancel _ (ne_of_gt p_pos)]
                    ... < r * p : mul_lt_mul_of_pos_right qpr p_pos
                    ... = p * r : mul_comm _ _,
                ⟨this, mul_pos p_pos r_pos⟩,
              simp [hlq, hp, of_real_lt_of_real_iff_cases, this] {contextual := tt}
            end
            begin simp [hp, p0]; exact hl end))))
  begin
    assume b hb0,
    have : 0 < b, from lt_of_le_of_ne ennreal.zero_le hb0.symm,
    suffices : tendsto ((*) ∞) (nhds b) (nhds ∞), { simpa [hb0] },
    apply (tendsto_cong tendsto_const_nhds $
      (nhds b).upwards_sets (mem_nhds_sets (is_open_lt' _) this) _),
    { assume c hc,
      have : c ≠ 0, from assume h, by simp [h] at hc; contradiction,
      simp [this] }
  end

lemma supr_of_real {s : set ℝ} {a : ℝ} (h : is_lub s a) : (⨆a∈s, of_real a) = of_real a :=
suffices Sup (of_real '' s) = of_real a, by simpa [Sup_image],
is_lub_iff_Sup_eq.mp $ is_lub_of_is_lub_of_tendsto
  (assume x _ y _, of_real_le_of_real) h (ne_empty_of_is_lub h)
  (tendsto.comp (tendsto_id' inf_le_left) tendsto_of_real)

lemma infi_of_real {s : set ℝ} {a : ℝ} (h : is_glb s a) : (⨅a∈s, of_real a) = of_real a :=
suffices Inf (of_real '' s) = of_real a, by simpa [Inf_image],
is_glb_iff_Inf_eq.mp $ is_glb_of_is_glb_of_tendsto
  (assume x _ y _, of_real_le_of_real) h (ne_empty_of_is_glb h)
  (tendsto.comp (tendsto_id' inf_le_left) tendsto_of_real)

lemma Inf_add {s : set ennreal} : Inf s + a = ⨅b∈s, b + a :=
by_cases
  (assume : s = ∅, by simp [this, ennreal.top_eq_infty])
  (assume : s ≠ ∅,
    have Inf ((λb, b + a) '' s) = Inf s + a,
      from is_glb_iff_Inf_eq.mp $ is_glb_of_is_glb_of_tendsto
        (assume x _ y _ h, add_le_add' h (le_refl _))
        is_glb_Inf
        this
        (tendsto_add (tendsto_id' inf_le_left) tendsto_const_nhds),
    by simp [Inf_image, -add_comm] at this; exact this.symm)

lemma Sup_add {s : set ennreal} (hs : s ≠ ∅) : Sup s + a = ⨆b∈s, b + a :=
have Sup ((λb, b + a) '' s) = Sup s + a,
  from is_lub_iff_Sup_eq.mp $ is_lub_of_is_lub_of_tendsto
    (assume x _ y _ h, add_le_add' h (le_refl _))
    is_lub_Sup
    hs
    (tendsto_add (tendsto_id' inf_le_left) tendsto_const_nhds),
by simp [Sup_image, -add_comm] at this; exact this.symm

lemma supr_add {ι : Sort*} {s : ι → ennreal} [h : nonempty ι] : supr s + a = ⨆b, s b + a :=
let ⟨x⟩ := h in
calc supr s + a = Sup (range s) + a : by simp [Sup_range]
  ... = (⨆b∈range s, b + a) : Sup_add $ ne_empty_iff_exists_mem.mpr ⟨s x, x, rfl⟩
  ... = _ : by simp [supr_range, -mem_range]

lemma infi_add {ι : Sort*} {s : ι → ennreal} {a : ennreal} : infi s + a = ⨅b, s b + a :=
calc infi s + a = Inf (range s) + a : by simp [Inf_range]
  ... = (⨅b∈range s, b + a) : Inf_add
  ... = _ : by simp [infi_range, -mem_range]

lemma add_infi {ι : Sort*} {s : ι → ennreal} {a : ennreal} : a + infi s = ⨅b, a + s b :=
by rw [add_comm, infi_add]; simp

lemma infi_add_infi {ι : Sort*} {f g : ι → ennreal} (h : ∀i j, ∃k, f k + g k ≤ f i + g j) :
  infi f + infi g = (⨅a, f a + g a) :=
suffices (⨅a, f a + g a) ≤ infi f + infi g,
  from le_antisymm (le_infi $ assume a, add_le_add' (infi_le _ _) (infi_le _ _)) this,
calc (⨅a, f a + g a) ≤ (⨅a', ⨅a, f a + g a') :
    le_infi $ assume a', le_infi $ assume a, let ⟨k, h⟩ := h a a' in infi_le_of_le k h
  ... ≤ infi f + infi g :
    by simp [infi_add, add_infi, -add_comm, -le_infi_iff]

lemma infi_sum {α : Type*} {ι : Sort*} {f : ι → α → ennreal} {s : finset α} [inhabited ι]
  (h : ∀(t : finset α) (i j : ι), ∃k, ∀a∈t, f k a ≤ f i a ∧ f k a ≤ f j a) :
  (⨅i, s.sum (f i)) = s.sum (λa, ⨅i, f i a) :=
finset.induction_on s (by simp) $ assume a s ha ih,
  have ∀ (i j : ι), ∃ (k : ι), f k a + s.sum (f k) ≤ f i a + s.sum (f j),
    from assume i j,
    let ⟨k, hk⟩ := h (insert a s) i j in
    ⟨k, add_le_add' (hk a (finset.mem_insert_self _ _)).left $ finset.sum_le_sum' $
      assume a ha, (hk _ $ finset.mem_insert_of_mem ha).right⟩,
  by simp [ha, ih.symm, infi_add_infi this]

end topological_space

section sub
instance : has_sub ennreal := ⟨λa b, Inf {d | a ≤ d + b}⟩

@[simp] lemma sub_eq_zero_of_le (h : a ≤ b) : a - b = 0 :=
le_antisymm (Inf_le $ le_add_left h) ennreal.zero_le

@[simp] lemma sub_add_cancel_of_le (h : b ≤ a) : (a - b) + b = a :=
let ⟨c, hc⟩ := le_iff_exists_add.mp h in
eq.trans Inf_add $ le_antisymm
  (infi_le_of_le c $ infi_le_of_le (by simp [hc]) $ by simp [hc])
  (le_infi $ assume d, le_infi $ assume hd, hd)

@[simp] lemma add_sub_cancel_of_le (h : b ≤ a) : b + (a - b) = a :=
by rwa [add_comm, sub_add_cancel_of_le]

lemma sub_add_self_eq_max : (a - b) + b = max a b :=
match le_total a b with
| or.inl h := by simp [h, max_eq_right]
| or.inr h := by simp [h, max_eq_left]
end

lemma sub_le_sub (h₁ : a ≤ b) (h₂ : d ≤ c) : a - c ≤ b - d :=
Inf_le_Inf $ assume e (h : b ≤ e + d),
  calc a ≤ b : h₁
    ... ≤ e + d : h
    ... ≤ e + c : add_le_add (le_refl _) h₂

@[simp] protected lemma sub_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b :=
iff.intro
  (assume h : a - b ≤ c,
    calc a ≤ (a - b) + b : by rw [sub_add_self_eq_max]; exact le_max_left _ _
      ... ≤ c + b : add_le_add h (le_refl _))
  (assume h : a ≤ c + b,
    calc a - b ≤ (c + b) - b : sub_le_sub h (le_refl _)
      ... ≤ c : Inf_le (le_refl (c + b)))

@[simp] lemma zero_sub : 0 - a = 0 :=
le_antisymm (Inf_le ennreal.zero_le) ennreal.zero_le

@[simp] lemma sub_infty : a - ∞ = 0 :=
le_antisymm (Inf_le le_infty) ennreal.zero_le

@[simp] lemma sub_zero : a - 0 = a :=
eq.trans (add_zero (a - 0)).symm $ by simp

@[simp] lemma infty_sub_of_real (hr : 0 ≤ r) : ∞ - of_real r = ∞ :=
top_unique $ le_Inf $ by simp [forall_ennreal, hr] {contextual := tt}; refl

@[simp] lemma of_real_sub_of_real (hr : 0 ≤ r) : of_real p - of_real r = of_real (p - r) :=
match le_total p r with
| or.inr h :=
  have 0 ≤ p - r, from le_sub_iff_add_le.mpr $ by simp [h],
  have eq : r + (p - r) = p, by rw [add_comm, sub_add_cancel],
  le_antisymm
    (Inf_le $ by simp [-sub_eq_add_neg, this, hr, le_trans hr h, eq, le_refl])
    (le_Inf $
      by simp [forall_ennreal, hr, le_trans hr h, add_nonneg, -sub_eq_add_neg,
        this, sub_le_iff_le_add]
        {contextual := tt})
| or.inl h :=
  begin
    rw [sub_eq_zero_of_le, of_real_of_nonpos],
    { rw [sub_le_iff_le_add], simp [h] },
    { exact of_real_le_of_real h }
  end
end

@[simp] lemma add_sub_self : ∀{a b : ennreal}, b < ∞ → (a + b) - b = a :=
by simp [forall_ennreal] {contextual:=tt}

protected lemma tendsto_of_real_sub (hr : 0 ≤ r) :
  tendsto (λb, of_real r - b) (nhds b) (nhds (of_real r - b)) :=
by_cases
  (assume h : of_real r < b,
    suffices tendsto (λb, of_real r - b) (nhds b) (nhds ⊥),
      by simpa [le_of_lt h],
    by rw [nhds_bot_orderable];
    from (tendsto_infi.2 $ assume p, tendsto_infi.2 $ assume hp : 0 < p, tendsto_principal.2 $
      (nhds b).upwards_sets (mem_nhds_sets (is_open_lt' (of_real r)) h) $
        by simp [forall_ennreal, hr, le_of_lt, hp] {contextual := tt}))
  (assume h : ¬ of_real r < b,
    let ⟨p, hp, hpr, eq⟩ := (le_of_real_iff hr).mp $ not_lt.1 h in
    have tendsto (λb, of_real ((r - b))) (nhds p ⊓ principal {x | 0 ≤ x}) (nhds (of_real (r - p))),
      from tendsto.comp (tendsto_sub tendsto_const_nhds (tendsto_id' inf_le_left)) tendsto_of_real,
    have tendsto (λb, of_real r - b) (map of_real (nhds p ⊓ principal {x | 0 ≤ x}))
      (nhds (of_real (r - p))),
      from tendsto_map' $ tendsto_cong this $ mem_inf_sets_of_right $
        by simp [(∘), -sub_eq_add_neg] {contextual:=tt},
    by simp at this; simp [eq, hr, hp, hpr, nhds_of_real_eq_map_of_real_nhds_nonneg, this])

lemma sub_supr {ι : Sort*} [hι : nonempty ι] {b : ι → ennreal} (hr : a < ⊤) :
  a - (⨆i, b i) = (⨅i, a - b i) :=
let ⟨i⟩ := hι in
let ⟨r, hr, eq, _⟩ := lt_iff_exists_of_real.mp hr in
have Inf ((λb, of_real r - b) '' range b) = of_real r - (⨆i, b i),
  from is_glb_iff_Inf_eq.mp $ is_glb_of_is_lub_of_tendsto
    (assume x _ y _, sub_le_sub (le_refl _))
    is_lub_supr
    (ne_empty_of_mem ⟨i, rfl⟩)
    (tendsto.comp (tendsto_id' inf_le_left) (ennreal.tendsto_of_real_sub hr)),
by rw [eq, ←this]; simp [Inf_image, infi_range, -mem_range]

end sub

section inv
instance : has_inv ennreal := ⟨λa, Inf {b | 1 ≤ a * b}⟩
instance : has_div ennreal := ⟨λa b, a * b⁻¹⟩

@[simp] lemma inv_zero : (0 : ennreal)⁻¹ = ∞ :=
show Inf {b : ennreal | 1 ≤ 0 * b} = ∞, by simp; refl

@[simp] lemma inv_infty : (∞ : ennreal)⁻¹ = 0 :=
bot_unique $ le_of_forall_le_of_dense $ λ a (h : a > 0), Inf_le $ by simp [*, ne_of_gt h]

@[simp] lemma inv_of_real (hr : 0 < r) : (of_real r)⁻¹ = of_real (r⁻¹) :=
have 0 ≤ r⁻¹, from le_of_lt (inv_pos hr),
have r0 : 0 ≤ r, from le_of_lt hr,
le_antisymm
  (Inf_le $ by simp [*, inv_pos hr, mul_inv_cancel (ne_of_gt hr)])
  (le_Inf $ forall_ennreal.mpr ⟨λ p hp,
    by simp [*, show 0 ≤ r*p, from mul_nonneg r0 hp];
       intro; rwa [inv_eq_one_div, div_le_iff hr, mul_comm],
    λ h, le_top⟩)

lemma inv_inv : ∀{a:ennreal}, (a⁻¹)⁻¹ = a :=
forall_ennreal.mpr $ and.intro
  (assume r hr, by_cases
    (assume : r = 0, by simp [this])
    (assume : r ≠ 0,
      have 0 < r, from lt_of_le_of_ne hr this.symm,
      by simp [*, inv_pos, inv_inv']))
  (by simp)

end inv

section tsum

variables {f g : α → ennreal}

protected lemma is_sum : is_sum f (⨆s:finset α, s.sum f) :=
tendsto_orderable.2
  ⟨assume a' ha',
    let ⟨s, hs⟩ := lt_supr_iff.mp ha' in
    mem_at_top_sets.mpr ⟨s, assume t ht, lt_of_lt_of_le hs $ finset.sum_le_sum_of_subset ht⟩,
  assume a' ha',
    univ_mem_sets' $ assume s,
    have s.sum f ≤ ⨆(s : finset α), s.sum f,
      from le_supr (λ(s : finset α), s.sum f) s,
    lt_of_le_of_lt this ha'⟩

@[simp] protected lemma has_sum : has_sum f := ⟨_, ennreal.is_sum⟩

protected lemma tsum_eq_supr_sum : (∑a, f a) = (⨆s:finset α, s.sum f) :=
tsum_eq_is_sum ennreal.is_sum

protected lemma tsum_sigma {β : α → Type*} (f : Πa, β a → ennreal) :
  (∑p:Σa, β a, f p.1 p.2) = (∑a, ∑b, f a b) :=
tsum_sigma (assume b, ennreal.has_sum) ennreal.has_sum

protected lemma tsum_prod {f : α → β → ennreal} : (∑p:α×β, f p.1 p.2) = (∑a, ∑b, f a b) :=
let j : α × β → (Σa:α, β) := λp, sigma.mk p.1 p.2 in
let i : (Σa:α, β) → α × β := λp, (p.1, p.2) in
let f' : (Σa:α, β) → ennreal := λp, f p.1 p.2 in
calc (∑p:α×β, f' (j p)) = (∑p:Σa:α, β, f p.1 p.2) :
    tsum_eq_tsum_of_iso j i (assume ⟨a, b⟩, rfl) (assume ⟨a, b⟩, rfl)
   ... = (∑a, ∑b, f a b) : ennreal.tsum_sigma f

protected lemma tsum_of_real {f : α → ℝ} (h : is_sum f r) (hf : ∀a, 0 ≤ f a) :
  (∑a, of_real (f a)) = of_real r :=
have (λs:finset α, s.sum (of_real ∘ f)) = of_real ∘ (λs:finset α, s.sum f),
  from funext $ assume s, sum_of_real $ assume a _, hf a,
have tendsto (λs:finset α, s.sum (of_real ∘ f)) at_top (nhds (of_real r)),
  by rw [this]; exact h.comp tendsto_of_real,
tsum_eq_is_sum this

protected lemma tsum_comm {f : α → β → ennreal} : (∑a, ∑b, f a b) = (∑b, ∑a, f a b) :=
let f' : α×β → ennreal := λp, f p.1 p.2 in
calc (∑a, ∑b, f a b) = (∑p:α×β, f' p) : ennreal.tsum_prod.symm
  ... = (∑p:β×α, f' (prod.swap p)) :
    (tsum_eq_tsum_of_iso prod.swap (@prod.swap α β) (assume ⟨a, b⟩, rfl) (assume ⟨a, b⟩, rfl)).symm
  ... = (∑b, ∑a, f' (prod.swap (b, a))) : @ennreal.tsum_prod β α (λb a, f' (prod.swap (b, a)))

protected lemma tsum_le_tsum (h : ∀a, f a ≤ g a) : (∑a, f a) ≤ (∑a, g a) :=
tsum_le_tsum h ennreal.has_sum ennreal.has_sum

protected lemma tsum_eq_supr_nat {f : ℕ → ennreal} :
  (∑i:ℕ, f i) = (⨆i:ℕ, (finset.range i).sum f) :=
calc _ = (⨆s:finset ℕ, s.sum f) : ennreal.tsum_eq_supr_sum
  ... = (⨆i:ℕ, (finset.range i).sum f) : le_antisymm
    (supr_le_supr2 $ assume s,
      let ⟨n, hn⟩ := finset.exists_nat_subset_range s in
      ⟨n, finset.sum_le_sum_of_subset hn⟩)
    (supr_le_supr2 $ assume i, ⟨finset.range i, le_refl _⟩)

protected lemma le_tsum {a : α} : f a ≤ (∑a, f a) :=
calc f a = ({a} : finset α).sum f : by simp
  ... ≤ (⨆s:finset α, s.sum f) : le_supr (λs:finset α, s.sum f) _
  ... = (∑a, f a) : by rw [ennreal.tsum_eq_supr_sum]

protected lemma mul_tsum : (∑i, a * f i) = a * (∑i, f i) :=
if h : ∀i, f i = 0 then by simp [h] else
let ⟨i, (hi : f i ≠ 0)⟩ := classical.not_forall.mp h in
have sum_ne_0 : (∑i, f i) ≠ 0, from ne_of_gt $
  calc 0 < f i : lt_of_le_of_ne ennreal.zero_le hi.symm
    ... ≤ (∑i, f i) : ennreal.le_tsum,
have tendsto (λs:finset α, s.sum ((*) a ∘ f)) at_top (nhds (a * (∑i, f i))),
  by rw [← show (*) a ∘ (λs:finset α, s.sum f) = λs, s.sum ((*) a ∘ f),
         from funext $ λ s, finset.mul_sum];
  exact (is_sum_tsum ennreal.has_sum).comp (ennreal.tendsto_mul sum_ne_0),
tsum_eq_is_sum this

protected lemma tsum_mul : (∑i, f i * a) = (∑i, f i) * a :=
by simp [mul_comm, ennreal.mul_tsum]

@[simp] lemma tsum_supr_eq {α : Type*} (a : α) {f : α → ennreal} :
  (∑b:α, ⨆ (h : a = b), f b) = f a :=
le_antisymm
  (by rw [ennreal.tsum_eq_supr_sum]; exact supr_le (assume s,
    calc s.sum (λb, ⨆ (h : a = b), f b) ≤ (finset.singleton a).sum (λb, ⨆ (h : a = b), f b) :
        finset.sum_le_sum_of_ne_zero $ assume b _ hb,
          suffices a = b, by simpa using this.symm,
          classical.by_contradiction $ assume h,
            by simpa [h] using hb
      ... = f a : by simp))
  (calc f a ≤ (⨆ (h : a = a), f a) : le_supr (λh:a=a, f a) rfl
    ... ≤ (∑b:α, ⨆ (h : a = b), f b) : ennreal.le_tsum)

end tsum

section nnreal
-- TODO: use nnreal to define ennreal

instance : has_coe nnreal ennreal := ⟨ennreal.of_real ∘ coe⟩

lemma tendsto_of_real_iff {f : filter α} {m : α → ℝ} {r : ℝ} (hm : ∀a, 0 ≤ m a) (hr : 0 ≤ r) :
  tendsto (λx, of_real (m x)) f (nhds (of_real r)) ↔ tendsto m f (nhds r) :=
iff.intro
  (assume h,
    have tendsto (λ (x : α), of_ennreal (of_real (m x))) f (nhds r), from
      h.comp (tendsto_of_ennreal hr),
    by simpa [hm])
  (assume h, h.comp tendsto_of_real)

lemma tendsto_coe_iff {f : filter α} {m : α → nnreal} {r : nnreal} :
  tendsto (λx, (m x : ennreal)) f (nhds r) ↔ tendsto m f (nhds r) :=
iff.trans (tendsto_of_real_iff (assume a, (m a).2) r.2) nnreal.tendsto_coe

protected lemma is_sum_of_real_iff {f : α → ℝ} {r : ℝ} (hf : ∀a, 0 ≤ f a) (hr : 0 ≤ r) :
  is_sum (λa, of_real (f a)) (of_real r) ↔ is_sum f r :=
by simp [is_sum, sum_of_real, hf];
  exact tendsto_of_real_iff (assume s, finset.zero_le_sum $ assume a ha, hf a) hr

protected lemma is_sum_coe_iff {f : α → nnreal} {r : nnreal} :
  is_sum (λa, (f a : ennreal)) r ↔ is_sum f r :=
iff.trans (ennreal.is_sum_of_real_iff (assume a, (f a).2) r.2) nnreal.is_sum_coe

protected lemma coe_tsum {f : α → nnreal} (h : has_sum f) : ↑(∑a, f a) = (∑a, f a : ennreal) :=
eq.symm (tsum_eq_is_sum $ ennreal.is_sum_coe_iff.2 $ is_sum_tsum h)

@[simp] lemma coe_mul (a b : nnreal) : ↑(a * b) = (a * b : ennreal) :=
(ennreal.of_real_mul_of_real a.2 b.2).symm

@[simp] lemma coe_one : ↑(1 : nnreal) = (1 : ennreal) := rfl

@[simp] lemma coe_eq_coe {n m : nnreal} : (↑n : ennreal) = m ↔ n = m :=
iff.trans (of_real_eq_of_real_of n.2 m.2) (iff.intro subtype.eq $ assume eq, eq ▸ rfl)

end nnreal

end ennreal

lemma has_sum_of_nonneg_of_le {f g : β → ℝ} (hg : ∀b, 0 ≤ g b) (hgf : ∀b, g b ≤ f b) :
  has_sum f → has_sum g
| ⟨r, hfr⟩ :=
  have hf : ∀a, 0 ≤ f a, from assume a, le_trans (hg a) (hgf a),
  have hr : 0 ≤ r, from is_sum_le hf is_sum_zero hfr,
  have is_sum (λa, ennreal.of_real (f a)) (ennreal.of_real r), from
    (ennreal.is_sum_of_real_iff hf hr).2 hfr,
  have (∑b, ennreal.of_real (g b)) ≤ ennreal.of_real r,
  begin
    refine is_sum_le (assume b, _) (is_sum_tsum ennreal.has_sum) this,
    exact ennreal.of_real_le_of_real (hgf _)
  end,
  let ⟨p, hp, hpr, eq⟩ := (ennreal.le_of_real_iff hr).1 this in
  have is_sum g p, from
    (ennreal.is_sum_of_real_iff hg hp).1 (eq ▸ is_sum_tsum ennreal.has_sum),
  has_sum_spec this

lemma nnreal.has_sum_of_le {f g : β → nnreal} (hgf : ∀b, g b ≤ f b) (hf : has_sum f) : has_sum g :=
nnreal.has_sum_coe.1 $ has_sum_of_nonneg_of_le (assume b, (g b).2) hgf $ nnreal.has_sum_coe.2 hf
