/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.alias
import tactic.lint

/-!
# Lemmas about inequalities

This file contains some lemmas about `≤`/`≥`/`<`/`>`, and `cmp`.

* We simplify `a ≥ b` and `a > b` to `b ≤ a` and `b < a`, respectively. This way we can formulate
  all lemmas using `≤`/`<` avoiding duplication.

* In some cases we introduce dot syntax aliases so that, e.g., from
  `(hab : a ≤ b) (hbc : b ≤ c) (hbc' : b < c)` one can prove `hab.trans hbc : a ≤ c` and
  `hab.trans_lt hbc' : a < c`.
-/

universe u
variables {α : Type u}

alias le_trans ← has_le.le.trans
alias lt_of_le_of_lt ← has_le.le.trans_lt
alias le_antisymm ← has_le.le.antisymm
alias lt_of_le_of_ne ← has_le.le.lt_of_ne
alias le_of_lt ← has_lt.lt.le
alias lt_trans ← has_lt.lt.trans
alias lt_of_lt_of_le ← has_lt.lt.trans_le
alias ne_of_lt ← has_lt.lt.ne
alias lt_asymm ← has_lt.lt.asymm has_lt.lt.not_lt
alias le_of_eq ← eq.le

/-- A version of `le_refl` where the argument is implicit -/
lemma le_rfl [preorder α] {x : α} : x ≤ x := le_refl x

namespace eq
/--
If `x = y` then `y ≤ x`. Note: this lemma uses `y ≤ x` instead of `x ≥ y`,
because `le` is used almost exclusively in mathlib.
-/
protected lemma ge [preorder α] {x y : α} (h : x = y) : y ≤ x := h.symm.le

lemma trans_le [preorder α] {x y z : α} (h1 : x = y) (h2 : y ≤ z) : x ≤ z := h1.le.trans h2
end eq

namespace has_le
namespace le
@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma ge [has_le α] {x y : α} (h : x ≤ y) : y ≥ x := h
lemma trans_eq [preorder α] {x y z : α} (h1 : x ≤ y) (h2 : y = z) : x ≤ z := h1.trans h2.le
end le
end has_le

namespace has_lt
namespace lt
@[nolint ge_or_gt] -- see Note [nolint_ge]
protected lemma gt [has_lt α] {x y : α} (h : x < y) : y > x := h
protected lemma false [preorder α] {x : α} : x < x → false := lt_irrefl x
end lt
end has_lt

namespace ge
protected lemma le [has_le α] {x y : α} (h : x ≥ y) : y ≤ x := h
end ge

namespace gt
protected lemma lt [has_lt α] {x y : α} (h : x > y) : y < x := h
end gt

@[nolint ge_or_gt] -- see Note [nolint_ge]
theorem ge_of_eq [preorder α] {a b : α} (h : a = b) : a ≥ b :=
h.ge

@[simp, nolint ge_or_gt] -- see Note [nolint_ge]
lemma ge_iff_le [preorder α] {a b : α} : a ≥ b ↔ b ≤ a := iff.rfl
@[simp, nolint ge_or_gt] -- see Note [nolint_ge]
lemma gt_iff_lt [preorder α] {a b : α} : a > b ↔ b < a := iff.rfl

lemma not_le_of_lt [preorder α] {a b : α} (h : a < b) : ¬ b ≤ a :=
(le_not_le_of_lt h).right

alias not_le_of_lt ← has_lt.lt.not_le

lemma not_lt_of_le [preorder α] {a b : α} (h : a ≤ b) : ¬ b < a
| hab := not_le_of_gt hab h

alias not_lt_of_le ← has_le.le.not_lt

lemma le_iff_eq_or_lt [partial_order α] {a b : α} : a ≤ b ↔ a = b ∨ a < b :=
le_iff_lt_or_eq.trans or.comm

lemma lt_iff_le_and_ne [partial_order α] {a b : α} : a < b ↔ a ≤ b ∧ a ≠ b :=
⟨λ h, ⟨le_of_lt h, ne_of_lt h⟩, λ ⟨h1, h2⟩, lt_of_le_of_ne h1 h2⟩

lemma eq_iff_le_not_lt [partial_order α] {a b : α} : a = b ↔ a ≤ b ∧ ¬ a < b :=
⟨λ h, ⟨le_of_eq h, h ▸ lt_irrefl _⟩, λ ⟨h₁, h₂⟩, le_antisymm h₁ $
  classical.by_contradiction $ λ h₃, h₂ (lt_of_le_not_le h₁ h₃)⟩

lemma eq_or_lt_of_le [partial_order α] {a b : α} (h : a ≤ b) : a = b ∨ a < b :=
(lt_or_eq_of_le h).symm

alias eq_or_lt_of_le ← has_le.le.eq_or_lt
alias lt_or_eq_of_le ← has_le.le.lt_or_eq

lemma lt_of_not_ge' [linear_order α] {a b : α} (h : ¬ b ≤ a) : a < b :=
lt_of_le_not_le ((le_total _ _).resolve_right h) h

lemma lt_iff_not_ge' [linear_order α] {x y : α} : x < y ↔ ¬ y ≤ x :=
⟨not_le_of_gt, lt_of_not_ge'⟩

@[simp] lemma not_lt [linear_order α] {a b : α} : ¬ a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩

lemma le_of_not_lt [linear_order α] {a b : α} : ¬ a < b → b ≤ a := not_lt.1

@[simp] lemma not_le [linear_order α] {a b : α} : ¬ a ≤ b ↔ b < a := lt_iff_not_ge'.symm

lemma lt_or_le [linear_order α] : ∀ a b : α, a < b ∨ b ≤ a := lt_or_ge
lemma le_or_lt [linear_order α] : ∀ a b : α, a ≤ b ∨ b < a := le_or_gt

lemma has_le.le.lt_or_le [linear_order α] {a b : α} (h : a ≤ b) (c : α) : a < c ∨ c ≤ b :=
(lt_or_le a c).imp id (λ hc, hc.trans h)

lemma has_le.le.le_or_lt [linear_order α] {a b : α} (h : a ≤ b) (c : α) : a ≤ c ∨ c < b :=
(le_or_lt a c).imp id (λ hc, hc.trans_le h)

lemma not_lt_iff_eq_or_lt [linear_order α] {a b : α} : ¬ a < b ↔ a = b ∨ b < a :=
not_lt.trans $ le_iff_eq_or_lt.trans $ or_congr eq_comm iff.rfl

lemma exists_ge_of_linear [linear_order α] (a b : α) : ∃ c, a ≤ c ∧ b ≤ c :=
match le_total a b with
| or.inl h := ⟨_, h, le_refl _⟩
| or.inr h := ⟨_, le_refl _, h⟩
end

lemma lt_imp_lt_of_le_imp_le {β} [linear_order α] [preorder β] {a b : α} {c d : β}
  (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
lt_of_not_ge' $ λ h', not_lt_of_ge (H h') h

lemma le_imp_le_of_lt_imp_lt {β} [preorder α] [linear_order β] {a b : α} {c d : β}
  (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
le_of_not_gt $ λ h', not_le_of_gt (H h') h

lemma le_imp_le_iff_lt_imp_lt {β} [linear_order α] [linear_order β] {a b : α} {c d : β} :
  (a ≤ b → c ≤ d) ↔ (d < c → b < a) :=
⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

lemma lt_iff_lt_of_le_iff_le' {β} [preorder α] [preorder β] {a b : α} {c d : β}
  (H : a ≤ b ↔ c ≤ d) (H' : b ≤ a ↔ d ≤ c) : b < a ↔ d < c :=
lt_iff_le_not_le.trans $ (and_congr H' (not_congr H)).trans lt_iff_le_not_le.symm

lemma lt_iff_lt_of_le_iff_le {β} [linear_order α] [linear_order β] {a b : α} {c d : β}
  (H : a ≤ b ↔ c ≤ d) : b < a ↔ d < c :=
not_le.symm.trans $ iff.trans (not_congr H) $ not_le

lemma le_iff_le_iff_lt_iff_lt {β} [linear_order α] [linear_order β] {a b : α} {c d : β} :
  (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
⟨lt_iff_lt_of_le_iff_le, λ H, not_lt.symm.trans $ iff.trans (not_congr H) $ not_lt⟩

lemma eq_of_forall_le_iff [partial_order α] {a b : α}
  (H : ∀ c, c ≤ a ↔ c ≤ b) : a = b :=
le_antisymm ((H _).1 (le_refl _)) ((H _).2 (le_refl _))

lemma le_of_forall_le [preorder α] {a b : α}
  (H : ∀ c, c ≤ a → c ≤ b) : a ≤ b :=
H _ (le_refl _)

lemma le_of_forall_le' [preorder α] {a b : α}
  (H : ∀ c, a ≤ c → b ≤ c) : b ≤ a :=
H _ (le_refl _)

lemma le_of_forall_lt [linear_order α] {a b : α}
  (H : ∀ c, c < a → c < b) : a ≤ b :=
le_of_not_lt $ λ h, lt_irrefl _ (H _ h)

lemma forall_lt_iff_le [linear_order α] {a b : α} :
  (∀ ⦃c⦄, c < a → c < b) ↔ a ≤ b :=
⟨le_of_forall_lt, λ h c hca, lt_of_lt_of_le hca h⟩

lemma le_of_forall_lt' [linear_order α] {a b : α}
  (H : ∀ c, a < c → b < c) : b ≤ a :=
le_of_not_lt $ λ h, lt_irrefl _ (H _ h)

lemma forall_lt_iff_le' [linear_order α] {a b : α} :
  (∀ ⦃c⦄, a < c → b < c) ↔ b ≤ a :=
⟨le_of_forall_lt', λ h c hac, lt_of_le_of_lt h hac⟩

lemma eq_of_forall_ge_iff [partial_order α] {a b : α}
  (H : ∀ c, a ≤ c ↔ b ≤ c) : a = b :=
le_antisymm ((H _).2 (le_refl _)) ((H _).1 (le_refl _))

/-- monotonicity of `≤` with respect to `→` -/
lemma le_implies_le_of_le_of_le {a b c d : α} [preorder α] (h₀ : c ≤ a) (h₁ : b ≤ d) :
  a ≤ b → c ≤ d :=
assume h₂ : a ≤ b,
calc  c
    ≤ a : h₀
... ≤ b : h₂
... ≤ d : h₁

namespace decidable

local attribute [instance, priority 10] classical.prop_decidable

lemma lt_or_eq_of_le [partial_order α] {a b : α} (hab : a ≤ b) : a < b ∨ a = b :=
if hba : b ≤ a then or.inr (le_antisymm hab hba)
else or.inl (lt_of_le_not_le hab hba)

lemma eq_or_lt_of_le [partial_order α] {a b : α} (hab : a ≤ b) : a = b ∨ a < b :=
(lt_or_eq_of_le hab).swap

lemma le_iff_lt_or_eq [partial_order α] {a b : α} : a ≤ b ↔ a < b ∨ a = b :=
⟨lt_or_eq_of_le, le_of_lt_or_eq⟩

lemma le_of_not_lt [linear_order α] {a b : α} (h : ¬ b < a) : a ≤ b :=
decidable.by_contradiction $ λ h', h $ lt_of_le_not_le ((le_total _ _).resolve_right h') h'

lemma not_lt [linear_order α] {a b : α} : ¬ a < b ↔ b ≤ a :=
⟨le_of_not_lt, not_lt_of_ge⟩

lemma lt_or_le [linear_order α] (a b : α) : a < b ∨ b ≤ a :=
if hba : b ≤ a then or.inr hba else or.inl $ not_le.1 hba

lemma le_or_lt [linear_order α] (a b : α) : a ≤ b ∨ b < a :=
(lt_or_le b a).swap

lemma lt_trichotomy [linear_order α] (a b : α) : a < b ∨ a = b ∨ b < a :=
(lt_or_le _ _).imp_right $ λ h, (eq_or_lt_of_le h).imp_left eq.symm

lemma lt_or_gt_of_ne [linear_order α] {a b : α} (h : a ≠ b) : a < b ∨ b < a :=
(lt_trichotomy a b).imp_right $ λ h', h'.resolve_left h

/-- Perform a case-split on the ordering of `x` and `y` in a decidable linear order. -/
def lt_by_cases [decidable_linear_order α] (x y : α) {P : Sort*}
  (h₁ : x < y → P) (h₂ : x = y → P) (h₃ : y < x → P) : P :=
begin
  by_cases h : x < y, { exact h₁ h },
  by_cases h' : y < x, { exact h₃ h' },
  apply h₂, apply le_antisymm; apply le_of_not_gt; assumption
end

lemma ne_iff_lt_or_gt [linear_order α] {a b : α} : a ≠ b ↔ a < b ∨ b < a :=
⟨lt_or_gt_of_ne, λo, o.elim ne_of_lt ne_of_gt⟩

lemma le_imp_le_of_lt_imp_lt {β} [preorder α] [linear_order β]
  {a b : α} {c d : β} (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
le_of_not_lt $ λ h', not_le_of_gt (H h') h

lemma le_imp_le_iff_lt_imp_lt {β} [linear_order α] [linear_order β]
  {a b : α} {c d : β} : (a ≤ b → c ≤ d) ↔ (d < c → b < a) :=
⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

lemma le_iff_le_iff_lt_iff_lt {β} [linear_order α] [linear_order β]
  {a b : α} {c d : β} : (a ≤ b ↔ c ≤ d) ↔ (b < a ↔ d < c) :=
⟨lt_iff_lt_of_le_iff_le, λ H, not_lt.symm.trans $ iff.trans (not_congr H) $ not_lt⟩

end decidable

namespace ordering

/-- `compares o a b` means that `a` and `b` have the ordering relation
  `o` between them, assuming that the relation `a < b` is defined -/
@[simp] def compares [has_lt α] : ordering → α → α → Prop
| lt a b := a < b
| eq a b := a = b
| gt a b := a > b

theorem compares.eq_lt [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = lt ↔ a < b)
| lt a b h := ⟨λ _, h, λ _, rfl⟩
| eq a b h := ⟨λ h, by injection h, λ h', (ne_of_lt h' h).elim⟩
| gt a b h := ⟨λ h, by injection h, λ h', (lt_asymm h h').elim⟩

theorem compares.eq_eq [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = eq ↔ a = b)
| lt a b h := ⟨λ h, by injection h, λ h', (ne_of_lt h h').elim⟩
| eq a b h := ⟨λ _, h, λ _, rfl⟩
| gt a b h := ⟨λ h, by injection h, λ h', (ne_of_gt h h').elim⟩

theorem compares.eq_gt [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = gt ↔ b < a)
| lt a b h := ⟨λ h, by injection h, λ h', (lt_asymm h h').elim⟩
| eq a b h := ⟨λ h, by injection h, λ h', (ne_of_gt h' h).elim⟩
| gt a b h := ⟨λ _, h, λ _, rfl⟩

theorem compares.inj [preorder α] {o₁} :
  ∀ {o₂} {a b : α}, compares o₁ a b → compares o₂ a b → o₁ = o₂
| lt a b h₁ h₂ := h₁.eq_lt.2 h₂
| eq a b h₁ h₂ := h₁.eq_eq.2 h₂
| gt a b h₁ h₂ := h₁.eq_gt.2 h₂

theorem compares_iff_of_compares_impl {β : Type*} [linear_order α] [preorder β] {a b : α}
  {a' b' : β} (h : ∀ {o}, compares o a b → compares o a' b') (o) :
  compares o a b ↔ compares o a' b' :=
begin
  refine ⟨h, λ ho, _⟩,
  cases lt_trichotomy a b with hab hab,
  { change compares ordering.lt a b at hab,
    rwa [ho.inj (h hab)] },
  { cases hab with hab hab,
    { change compares ordering.eq a b at hab,
      rwa [ho.inj (h hab)] },
    { change compares ordering.gt a b at hab,
      rwa [ho.inj (h hab)] } }
end

theorem swap_or_else (o₁ o₂) : (or_else o₁ o₂).swap = or_else o₁.swap o₂.swap :=
by cases o₁; try {refl}; cases o₂; refl

theorem or_else_eq_lt (o₁ o₂) : or_else o₁ o₂ = lt ↔ o₁ = lt ∨ (o₁ = eq ∧ o₂ = lt) :=
by cases o₁; cases o₂; exact dec_trivial

end ordering

theorem cmp_compares [decidable_linear_order α] (a b : α) : (cmp a b).compares a b :=
begin
  unfold cmp cmp_using,
  by_cases a < b; simp [h],
  by_cases h₂ : b < a; simp [h₂, gt],
  exact (lt_or_eq_of_le (le_of_not_gt h₂)).resolve_left h
end

theorem cmp_swap [preorder α] [@decidable_rel α (<)] (a b : α) : (cmp a b).swap = cmp b a :=
begin
  unfold cmp cmp_using,
  by_cases a < b; by_cases h₂ : b < a; simp [h, h₂, gt, ordering.swap],
  exact lt_asymm h h₂
end
