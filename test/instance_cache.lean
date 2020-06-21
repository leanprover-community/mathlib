import tactic.cache

meta def assert_frozen_instances : tactic unit := do
frozen ← tactic.frozen_local_instances,
when frozen.is_none $ tactic.fail "instances are not frozen"

example (α) (a : α) :=
begin
  haveI h : inhabited α := ⟨a⟩,
  assert_frozen_instances,
  exact default α
end

example (α) (a : α) :=
begin
  haveI h := inhabited.mk a,
  assert_frozen_instances,
  exact default α
end

example (α) (a : α) :=
begin
  letI h : inhabited α := ⟨a⟩,
  assert_frozen_instances,
  exact default α
end

example (α) (a : α) :=
begin
  letI h : inhabited α,
  all_goals { assert_frozen_instances },
  exact ⟨a⟩,
  exact default α
end

example (α) (a : α) :=
begin
  letI h := inhabited.mk a,
  exact default α
end

example (α) : inhabited α → α :=
by intro a; exactI default α

example (α) : inhabited α → α :=
begin
  introsI a,
  assert_frozen_instances,
  exact default α
end
