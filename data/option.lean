/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import logic.basic data.bool init.data.option.instances

namespace option
universe u
variables {α β : Type u}

instance has_mem : has_mem α (option α) := ⟨λ a b, b = some a⟩

@[simp] theorem mem_def {a : α} {b : option α} : a ∈ b ↔ b = some a :=
iff.rfl

@[simp] theorem get_mem : ∀ {o : option α} (h : is_some o), option.get h ∈ o
| (some a) _ := rfl

theorem get_of_mem {a : α} : ∀ {o : option α} (h : is_some o), a ∈ o → option.get h = a
| _ _ rfl := rfl

theorem some_inj {a b : α} : some a = some b ↔ a = b := by simp

@[simp] theorem none_bind (f : α → option β) : none >>= f = none := rfl

@[simp] theorem some_bind (a : α) (f : α → option β) : some a >>= f = f a := rfl

@[simp] theorem bind_some : ∀ x : option α, x >>= some = x :=
@bind_pure α option _ _

@[simp] theorem bind_eq_some {x : option α} {f : α → option β} {b : β} : x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
by cases x; simp

@[simp] theorem map_none {f : α → β} : f <$> none = none := rfl

@[simp] theorem map_some {a : α} {f : α → β} : f <$> some a = some (f a) := rfl

@[simp] theorem map_none' {f : α → β} : option.map f none = none := rfl

@[simp] theorem map_some' {a : α} {f : α → β} : option.map f (some a) = some (f a) := rfl

@[simp] theorem map_eq_some {x : option α} {f : α → β} {b : β} : f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b :=
by cases x; simp

@[simp] theorem map_id' : option.map (@id α) = id := map_id

@[simp] theorem seq_some {a : α} {f : α → β} : some f <*> some a = some (f a) := rfl

theorem is_some_iff_exists {x : option α} : is_some x ↔ ∃ a, x = some a :=
by cases x; simp [is_some]; exact ⟨_, rfl⟩

theorem is_none_iff_eq_none {o : option α} : o.is_none ↔ o = none :=
⟨option.eq_none_of_is_none, λ e, e.symm ▸ rfl⟩

instance decidable_eq_none {o : option α} : decidable (o = none) :=
decidable_of_bool _ is_none_iff_eq_none

instance decidable_forall_mem {p : α → Prop} [decidable_pred p] :
  ∀ o : option α, decidable (∀ a ∈ o, p a)
| none     := is_true (by simp)
| (some a) := decidable_of_iff (p a) (by simp)

instance decidable_exists_mem {p : α → Prop} [decidable_pred p] :
  ∀ o : option α, decidable (∃ a ∈ o, p a)
| none     := is_false (by simp)
| (some a) := decidable_of_iff (p a) (by simp)

/-- inhabited `get` function. Returns `a` if the input is `some a`,
  otherwise returns `default`. -/
@[reducible] def iget [inhabited α] : option α → α
| (some x) := x
| none     := default α

@[simp] theorem iget_some [inhabited α] {a : α} : (some a).iget = a := rfl

theorem iget_mem [inhabited α] : ∀ {o : option α}, is_some o → o.iget ∈ o
| (some a) _ := rfl

theorem iget_of_mem [inhabited α] {a : α} : ∀ {o : option α}, a ∈ o → o.iget = a
| _ rfl := rfl

/-- `guard p a` returns `some a` if `p a` holds, otherwise `none`. -/
def guard (p : α → Prop) [decidable_pred p] (a : α) : option α :=
if p a then some a else none

/-- `filter p o` returns `some a` if `o` is `some a`
  and `p a` holds, otherwise `none`. -/
def filter (p : α → Prop) [decidable_pred p] (o : option α) : option α :=
o.bind (guard p)

@[simp] theorem guard_eq_some {p : α → Prop} [decidable_pred p] {a b : α} :
  option.guard p a = some b ↔ a = b ∧ p a :=
by by_cases p a; simp [option.guard, h]; intro; contradiction

def to_list : option α → list α
| none     := []
| (some a) := [a]

@[simp] theorem mem_to_list {a : α} {o : option α} : a ∈ to_list o ↔ a ∈ o :=
by cases o; simp [to_list, eq_comm]

end option
