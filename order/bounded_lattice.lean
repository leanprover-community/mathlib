/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Defines bounded lattice type class hierarchy.

Includes the Prop and fun instances.
-/

import order.lattice data.option

set_option old_structure_cmd true

universes u v
variable {α : Type u}

namespace lattice

/-- Typeclass for the `⊤` (`\top`) notation -/
class has_top (α : Type u) := (top : α)
/-- Typeclass for the `⊥` (`\bot`) notation -/
class has_bot (α : Type u) := (bot : α)

notation `⊤` := has_top.top _
notation `⊥` := has_bot.bot _

/-- An `order_top` is a partial order with a maximal element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_top (α : Type u) extends has_top α, partial_order α :=
(le_top : ∀ a : α, a ≤ ⊤)

section order_top
variables [order_top α] {a : α}

@[simp] theorem le_top : a ≤ ⊤ :=
order_top.le_top a

theorem top_unique (h : ⊤ ≤ a) : a = ⊤ :=
le_antisymm le_top h

-- TODO: delete in favor of the next?
theorem eq_top_iff : a = ⊤ ↔ ⊤ ≤ a :=
⟨assume eq, eq.symm ▸ le_refl ⊤, top_unique⟩

@[simp] theorem top_le_iff : ⊤ ≤ a ↔ a = ⊤ :=
⟨top_unique, λ h, h.symm ▸ le_refl ⊤⟩

@[simp] theorem not_top_lt : ¬ ⊤ < a :=
assume h, lt_irrefl a (lt_of_le_of_lt le_top h)

end order_top

/-- An `order_bot` is a partial order with a minimal element.
  (We could state this on preorders, but then it wouldn't be unique
  so distinguishing one would seem odd.) -/
class order_bot (α : Type u) extends has_bot α, partial_order α :=
(bot_le : ∀ a : α, ⊥ ≤ a)

section order_bot
variables [order_bot α] {a : α}

@[simp] theorem bot_le : ⊥ ≤ a := order_bot.bot_le a

theorem bot_unique (h : a ≤ ⊥) : a = ⊥ :=
le_antisymm h bot_le

-- TODO: delete?
theorem eq_bot_iff : a = ⊥ ↔ a ≤ ⊥ :=
⟨assume eq, eq.symm ▸ le_refl ⊥, bot_unique⟩

@[simp] theorem le_bot_iff : a ≤ ⊥ ↔ a = ⊥ :=
⟨bot_unique, assume h, h.symm ▸ le_refl ⊥⟩

@[simp] theorem not_lt_bot : ¬ a < ⊥ :=
assume h, lt_irrefl a (lt_of_lt_of_le h bot_le)

theorem neq_bot_of_le_neq_bot {a b : α} (hb : b ≠ ⊥) (hab : b ≤ a) : a ≠ ⊥ :=
assume ha, hb $ bot_unique $ ha ▸ hab

end order_bot

/-- A `semilattice_sup_top` is a semilattice with top and join. -/
class semilattice_sup_top (α : Type u) extends order_top α, semilattice_sup α

section semilattice_sup_top
variables [semilattice_sup_top α] {a : α}

@[simp] theorem top_sup_eq : ⊤ ⊔ a = ⊤ :=
sup_of_le_left le_top

@[simp] theorem sup_top_eq : a ⊔ ⊤ = ⊤ :=
sup_of_le_right le_top

end semilattice_sup_top

/-- A `semilattice_sup_bot` is a semilattice with bottom and join. -/
class semilattice_sup_bot (α : Type u) extends order_bot α, semilattice_sup α

section semilattice_sup_bot
variables [semilattice_sup_bot α] {a b : α}

@[simp] theorem bot_sup_eq : ⊥ ⊔ a = a :=
sup_of_le_right bot_le

@[simp] theorem sup_bot_eq : a ⊔ ⊥ = a :=
sup_of_le_left bot_le

@[simp] theorem sup_eq_bot_iff : a ⊔ b = ⊥ ↔ (a = ⊥ ∧ b = ⊥) :=
by rw [eq_bot_iff, sup_le_iff]; simp

end semilattice_sup_bot

instance nat.semilattice_sup_bot : semilattice_sup_bot ℕ :=
{ bot := 0, bot_le := nat.zero_le, .. nat.distrib_lattice }

/-- A `semilattice_inf_top` is a semilattice with top and meet. -/
class semilattice_inf_top (α : Type u) extends order_top α, semilattice_inf α

section semilattice_inf_top
variables [semilattice_inf_top α] {a b : α}

@[simp] theorem top_inf_eq : ⊤ ⊓ a = a :=
inf_of_le_right le_top

@[simp] theorem inf_top_eq : a ⊓ ⊤ = a :=
inf_of_le_left le_top

@[simp] theorem inf_eq_top_iff : a ⊓ b = ⊤ ↔ (a = ⊤ ∧ b = ⊤) :=
by rw [eq_top_iff, le_inf_iff]; simp

end semilattice_inf_top

/-- A `semilattice_inf_bot` is a semilattice with bottom and meet. -/
class semilattice_inf_bot (α : Type u) extends order_bot α, semilattice_inf α

section semilattice_inf_bot
variables [semilattice_inf_bot α] {a : α}

@[simp] theorem bot_inf_eq : ⊥ ⊓ a = ⊥ :=
inf_of_le_left bot_le

@[simp] theorem inf_bot_eq : a ⊓ ⊥ = ⊥ :=
inf_of_le_right bot_le

end semilattice_inf_bot

/- Bounded lattices -/

/-- A bounded lattice is a lattice with a top and bottom element,
  denoted `⊤` and `⊥` respectively. This allows for the interpretation
  of all finite suprema and infima, taking `inf ∅ = ⊤` and `sup ∅ = ⊥`. -/
class bounded_lattice (α : Type u) extends lattice α, order_top α, order_bot α

instance semilattice_inf_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_inf_top α :=
{ le_top := assume x, @le_top α _ x, ..bl }

instance semilattice_inf_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_inf_bot α :=
{ bot_le := assume x, @bot_le α _ x, ..bl }

instance semilattice_sup_top_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_sup_top α :=
{ le_top := assume x, @le_top α _ x, ..bl }

instance semilattice_sup_bot_of_bounded_lattice (α : Type u) [bl : bounded_lattice α] : semilattice_sup_bot α :=
{ bot_le := assume x, @bot_le α _ x, ..bl }

/-- A bounded distributive lattice is exactly what it sounds like. -/
class bounded_distrib_lattice α extends distrib_lattice α, bounded_lattice α

lemma inf_eq_bot_iff_le_compl {α : Type u} [bounded_distrib_lattice α] {a b c : α}
  (h₁ : b ⊔ c = ⊤) (h₂ : b ⊓ c = ⊥) : a ⊓ b = ⊥ ↔ a ≤ c :=
⟨assume : a ⊓ b = ⊥,
  calc a ≤ a ⊓ (b ⊔ c) : by simp [h₁]
    ... = (a ⊓ b) ⊔ (a ⊓ c) : by simp [inf_sup_left]
    ... ≤ c : by simp [this, inf_le_right],
  assume : a ≤ c,
  bot_unique $
    calc a ⊓ b ≤ b ⊓ c : by rw [inf_comm]; exact inf_le_inf (le_refl _) this
      ... = ⊥ : h₂⟩

/- Prop instance -/
instance bounded_lattice_Prop : bounded_lattice Prop :=
{ lattice.bounded_lattice .
  le           := λa b, a → b,
  le_refl      := assume _, id,
  le_trans     := assume a b c f g, g ∘ f,
  le_antisymm  := assume a b Hab Hba, propext ⟨Hab, Hba⟩,

  sup          := or,
  le_sup_left  := @or.inl,
  le_sup_right := @or.inr,
  sup_le       := assume a b c, or.rec,

  inf          := and,
  inf_le_left  := @and.left,
  inf_le_right := @and.right,
  le_inf       := assume a b c Hab Hac Ha, and.intro (Hab Ha) (Hac Ha),

  top          := true,
  le_top       := assume a Ha, true.intro,

  bot          := false,
  bot_le       := @false.elim }

section logic
variable [preorder α]

theorem monotone_and {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λx, p x ∧ q x) :=
assume a b h, and.imp (m_p h) (m_q h)
-- Note: by finish [monotone] doesn't work

theorem monotone_or {p q : α → Prop} (m_p : monotone p) (m_q : monotone q) :
  monotone (λx, p x ∨ q x) :=
assume a b h, or.imp (m_p h) (m_q h)
end logic

/- Function lattices -/

/- TODO:
 * build up the lattice hierarchy for `fun`-functor piecewise. semilattic_*, bounded_lattice, lattice ...
 * can this be generalized to the dependent function space?
-/
instance bounded_lattice_fun {α : Type u} {β : Type v} [bounded_lattice β] :
  bounded_lattice (α → β) :=
{ sup          := λf g a, f a ⊔ g a,
  le_sup_left  := assume f g a, le_sup_left,
  le_sup_right := assume f g a, le_sup_right,
  sup_le       := assume f g h Hfg Hfh a, sup_le (Hfg a) (Hfh a),

  inf          := λf g a, f a ⊓ g a,
  inf_le_left  := assume f g a, inf_le_left,
  inf_le_right := assume f g a, inf_le_right,
  le_inf       := assume f g h Hfg Hfh a, le_inf (Hfg a) (Hfh a),

  top          := λa, ⊤,
  le_top       := assume f a, le_top,

  bot          := λa, ⊥,
  bot_le       := assume f a, bot_le,
  ..partial_order_fun }

end lattice

def with_bot (α : Type*) := option α

namespace with_bot
open lattice

instance : has_coe_t α (with_bot α) := ⟨some⟩

instance partial_order [partial_order α] : partial_order (with_bot α) :=
{ le          := λ o₁ o₂ : option α, ∀ a ∈ o₁, ∃ b ∈ o₂, a ≤ b,
  le_refl     := λ o a ha, ⟨a, ha, le_refl _⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ a ha,
    let ⟨b, hb, ab⟩ := h₁ a ha, ⟨c, hc, bc⟩ := h₂ b hb in
    ⟨c, hc, le_trans ab bc⟩,
  le_antisymm := λ o₁ o₂ h₁ h₂, begin
    cases o₁ with a,
    { cases o₂ with b, {refl},
      rcases h₂ b rfl with ⟨_, ⟨⟩, _⟩ },
    { rcases h₁ a rfl with ⟨b, ⟨⟩, h₁'⟩,
      rcases h₂ b rfl with ⟨_, ⟨⟩, h₂'⟩,
      rw le_antisymm h₁' h₂' }
  end }

instance order_bot [partial_order α] : order_bot (with_bot α) :=
{ bot := none,
  bot_le := λ a a' h, option.no_confusion h,
  ..with_bot.partial_order }

@[simp] theorem coe_le_coe [partial_order α] {a b : α} :
  (a : with_bot α) ≤ b ↔ a ≤ b :=
⟨λ h, by rcases h a rfl with ⟨_, ⟨⟩, h⟩; exact h,
 λ h a' e, option.some_inj.1 e ▸ ⟨b, rfl, h⟩⟩

@[simp] theorem some_le_some [partial_order α] {a b : α} :
  @has_le.le (with_bot α) _ (some a) (some b) ↔ a ≤ b := coe_le_coe

theorem coe_le [partial_order α] {a b : α} :
  ∀ {o : option α}, b ∈ o → ((a : with_bot α) ≤ o ↔ a ≤ b)
| _ rfl := coe_le_coe

@[simp] theorem some_lt_some [partial_order α] {a b : α} :
  @has_lt.lt (with_bot α) _ (some a) (some b) ↔ a < b :=
(and_congr some_le_some (not_congr some_le_some))
  .trans lt_iff_le_not_le.symm

instance linear_order [linear_order α] : linear_order (with_bot α) :=
{ le_total := λ o₁ o₂, begin
    cases o₁ with a, {exact or.inl bot_le},
    cases o₂ with b, {exact or.inr bot_le},
    simp [le_total]
  end,
  ..with_bot.partial_order }

instance decidable_linear_order [decidable_linear_order α] : decidable_linear_order (with_bot α) :=
{ decidable_le := λ a b, begin
    cases a with a,
    { exact is_true bot_le },
    cases b with b,
    { exact is_false (mt (le_antisymm bot_le) (by simp)) },
    { exact decidable_of_iff _ some_le_some }
  end,
  ..with_bot.linear_order }

instance semilattice_sup [semilattice_sup α] : semilattice_sup_bot (with_bot α) :=
{ sup          := option.lift_or_get (⊔),
  le_sup_left  := λ o₁ o₂ a ha,
    by cases ha; cases o₂; simp [option.lift_or_get],
  le_sup_right := λ o₁ o₂ a ha,
    by cases ha; cases o₁; simp [option.lift_or_get],
  sup_le       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases o₁ with b; cases o₂ with c; cases ha,
    { exact h₂ a rfl },
    { exact h₁ a rfl },
    { rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩,
      simp at h₂,
      exact ⟨d, rfl, sup_le h₁' h₂⟩ }
  end,
  ..with_bot.order_bot }

instance semilattice_inf [semilattice_inf α] : semilattice_inf_bot (with_bot α) :=
{ inf          := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a ⊓ b)),
  inf_le_left  := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, inf_le_left⟩
  end,
  inf_le_right := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, inf_le_right⟩
  end,
  le_inf       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases ha,
    rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩,
    rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩,
    exact ⟨_, rfl, le_inf ab ac⟩
  end,
  ..with_bot.order_bot }

instance lattice [lattice α] : lattice (with_bot α) :=
{ ..with_bot.semilattice_sup, ..with_bot.semilattice_inf }

instance order_top [order_top α] : order_top (with_bot α) :=
{ top := some ⊤,
  le_top := λ o a ha, by cases ha; exact ⟨_, rfl, le_top⟩,
  ..with_bot.partial_order }

instance bounded_lattice [bounded_lattice α] : bounded_lattice (with_bot α) :=
{ ..with_bot.lattice, ..with_bot.order_top, ..with_bot.order_bot }

@[simp] lemma sup_eq_max [decidable_linear_order α] (a b : with_bot α) : a ⊔ b = max a b :=
le_antisymm (sup_le (le_max_left a b) (le_max_right a b)) (max_le le_sup_left le_sup_right)

lemma well_founded_lt [partial_order α] (h : well_founded ((<) : α → α → Prop)) :
  well_founded ((<) : with_bot α → with_bot α → Prop) :=
have acc_bot : acc ((<) : with_bot α → with_bot α → Prop) ⊥ :=
  acc.intro _ (λ b h, (not_le_of_gt h lattice.bot_le).elim),
⟨λ a, option.rec_on a acc_bot
  (λ a, acc.intro _ (well_founded.induction h a
    (show ∀ b, (∀ c, c < b → ∀ (d : with_bot α), d < some c → acc (<) d) →
      ∀ c : with_bot α, c < some b → acc (<) c,
    from λ b ih c, option.rec_on c (λ hc, acc_bot)
      (λ c hc, acc.intro _ (ih _ (with_bot.some_lt_some.1 hc))))))⟩

end with_bot

--TODO(Mario): Construct using order dual on with_bot
def with_top (α : Type*) := option α

namespace with_top
open lattice

instance : has_coe_t α (with_top α) := ⟨some⟩

instance partial_order [partial_order α] : partial_order (with_top α) :=
{ le          := λ o₁ o₂ : option α, ∀ b ∈ o₂, ∃ a ∈ o₁, a ≤ b,
  le_refl     := λ o a ha, ⟨a, ha, le_refl _⟩,
  le_trans    := λ o₁ o₂ o₃ h₁ h₂ c hc,
    let ⟨b, hb, bc⟩ := h₂ c hc, ⟨a, ha, ab⟩ := h₁ b hb in
    ⟨a, ha, le_trans ab bc⟩,
  le_antisymm := λ o₁ o₂ h₁ h₂, begin
    cases o₂ with b,
    { cases o₁ with a, {refl},
      rcases h₂ a rfl with ⟨_, ⟨⟩, _⟩ },
    { rcases h₁ b rfl with ⟨a, ⟨⟩, h₁'⟩,
      rcases h₂ a rfl with ⟨_, ⟨⟩, h₂'⟩,
      rw le_antisymm h₁' h₂' }
  end }

instance order_top [partial_order α] : order_top (with_top α) :=
{ top := none,
  le_top := λ a a' h, option.no_confusion h,
  ..with_top.partial_order }

@[simp] theorem coe_le_coe [partial_order α] {a b : α} :
  (a : with_top α) ≤ b ↔ a ≤ b :=
⟨λ h, by rcases h b rfl with ⟨_, ⟨⟩, h⟩; exact h,
 λ h a' e, option.some_inj.1 e ▸ ⟨a, rfl, h⟩⟩

@[simp] theorem some_le_some [partial_order α] {a b : α} :
  @has_le.le (with_top α) _ (some a) (some b) ↔ a ≤ b := coe_le_coe

theorem le_coe [partial_order α] {a b : α} :
  ∀ {o : option α}, a ∈ o →
  (@has_le.le (with_top α) _ o b ↔ a ≤ b)
| _ rfl := coe_le_coe

@[simp] theorem some_lt_some [partial_order α] {a b : α} :
  @has_lt.lt (with_top α) _ (some a) (some b) ↔ a < b :=
(and_congr some_le_some (not_congr some_le_some))
  .trans lt_iff_le_not_le.symm

instance linear_order [linear_order α] : linear_order (with_top α) :=
{ le_total := λ o₁ o₂, begin
    cases o₁ with a, {exact or.inr le_top},
    cases o₂ with b, {exact or.inl le_top},
    simp [le_total]
  end,
  ..with_top.partial_order }

instance decidable_linear_order [decidable_linear_order α] : decidable_linear_order (with_top α) :=
{ decidable_le := λ a b, begin
    cases b with b,
    { exact is_true le_top },
    cases a with a,
    { exact is_false (mt (le_antisymm le_top) (by simp)) },
    { exact decidable_of_iff _ some_le_some }
  end,
  ..with_top.linear_order }

instance semilattice_inf [semilattice_inf α] : semilattice_inf_top (with_top α) :=
{ inf          := option.lift_or_get (⊓),
  inf_le_left  := λ o₁ o₂ a ha,
    by cases ha; cases o₂; simp [option.lift_or_get],
  inf_le_right := λ o₁ o₂ a ha,
    by cases ha; cases o₁; simp [option.lift_or_get],
  le_inf       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases o₂ with b; cases o₃ with c; cases ha,
    { exact h₂ a rfl },
    { exact h₁ a rfl },
    { rcases h₁ b rfl with ⟨d, ⟨⟩, h₁'⟩,
      simp at h₂,
      exact ⟨d, rfl, le_inf h₁' h₂⟩ }
  end,
  ..with_top.order_top }

instance semilattice_sup [semilattice_sup α] : semilattice_sup_top (with_top α) :=
{ sup          := λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a ⊔ b)),
  le_sup_left  := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, le_sup_left⟩
  end,
  le_sup_right := λ o₁ o₂ a ha, begin
    simp at ha, rcases ha with ⟨b, rfl, c, rfl, rfl⟩,
    exact ⟨_, rfl, le_sup_right⟩
  end,
  sup_le       := λ o₁ o₂ o₃ h₁ h₂ a ha, begin
    cases ha,
    rcases h₁ a rfl with ⟨b, ⟨⟩, ab⟩,
    rcases h₂ a rfl with ⟨c, ⟨⟩, ac⟩,
    exact ⟨_, rfl, sup_le ab ac⟩
  end,
  ..with_top.order_top }

instance lattice [lattice α] : lattice (with_top α) :=
{ ..with_top.semilattice_sup, ..with_top.semilattice_inf }

instance order_bot [order_bot α] : order_bot (with_top α) :=
{ bot := some ⊥,
  bot_le := λ o a ha, by cases ha; exact ⟨_, rfl, bot_le⟩,
  ..with_top.partial_order }

instance bounded_lattice [bounded_lattice α] : bounded_lattice (with_top α) :=
{ ..with_top.lattice, ..with_top.order_top, ..with_top.order_bot }

@[simp] lemma inf_eq_max [decidable_linear_order α] (a b : with_top α) : a ⊓ b = min a b :=
le_antisymm (le_min inf_le_left inf_le_right) (le_inf (min_le_left a b) (min_le_right a b))

end with_top
