/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/

import tactic.interactive tactic.finish tactic.ext tactic.lift tactic.apply

example (m n p q : nat) (h : m + n = p) : true :=
begin
  have : m + n = q,
  { generalize_hyp h' : m + n = x at h,
    guard_hyp h' := m + n = x,
    guard_hyp h := x = p,
    guard_target m + n = q,
    admit },
  have : m + n = q,
  { generalize_hyp h' : m + n = x at h ⊢,
    guard_hyp h' := m + n = x,
    guard_hyp h := x = p,
    guard_target x = q,
    admit },
  trivial
end

example (α : Sort*) (L₁ L₂ L₃ : list α)
  (H : L₁ ++ L₂ = L₃) : true :=
begin
  have : L₁ ++ L₂ = L₂,
  { generalize_hyp h : L₁ ++ L₂ = L at H,
    induction L with hd tl ih,
    case list.nil
    { tactic.cleanup,
      change list.nil = L₃ at H,
      admit },
    case list.cons
    { change list.cons hd tl = L₃ at H,
      admit } },
  trivial
end

example (x y : ℕ) (p q : Prop) (h : x = y) (h' : p ↔ q) : true :=
begin
  symmetry' at h,
  guard_hyp' h := y = x,
  guard_hyp' h' := p ↔ q,
  symmetry' at *,
  guard_hyp' h := x = y,
  guard_hyp' h' := q ↔ p,
  trivial
end

section apply_rules

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
add_le_add (add_le_add (add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_right h2 h3)) h1 ) h2) h3

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by apply_rules [add_le_add, mul_le_mul_of_nonneg_right]

@[user_attribute]
meta def mono_rules : user_attribute :=
{ name := `mono_rules,
  descr := "lemmas usable to prove monotonicity" }
attribute [mono_rules] add_le_add mul_le_mul_of_nonneg_right

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by apply_rules [mono_rules]

example {a b c d e : nat} (h1 : a ≤ b) (h2 : c ≤ d) (h3 : 0 ≤ e) :
a + c * e + a + c + 0 ≤ b + d * e + b + d + e :=
by apply_rules mono_rules

end apply_rules

section h_generalize

variables {α β γ φ ψ : Type} (f : α → α → α → φ → γ)
          (x y : α) (a b : β) (z : φ)
          (h₀ : β = α) (h₁ : β = α) (h₂ : φ = β)
          (hx : x == a) (hy : y == b) (hz : z == a)
include f x y z a b hx hy hz

example : f x y x z = f (eq.rec_on h₀ a) (cast h₀ b) (eq.mpr h₁.symm a) (eq.mpr h₂ a) :=
begin
  guard_hyp_nums 16,
  h_generalize hp : a == p with hh,
  guard_hyp_nums 19,
  guard_hyp' hh := β = α,
  guard_target f x y x z = f p (cast h₀ b) p (eq.mpr h₂ a),
  h_generalize hq : _ == q,
  guard_hyp_nums 21,
  guard_target f x y x z = f p q p (eq.mpr h₂ a),
  h_generalize _ : _ == r,
  guard_hyp_nums 23,
  guard_target f x y x z = f p q p r,
  casesm* [_ == _, _ = _], refl
end

end h_generalize

section h_generalize

variables {α β γ φ ψ : Type} (f : list α → list α → γ)
          (x : list α) (a : list β) (z : φ)
          (h₀ : β = α) (h₁ : list β = list α)
          (hx : x == a)
include f x z a hx h₀ h₁

example : true :=
begin
  have : f x x = f (eq.rec_on h₀ a) (cast h₁ a),
  { guard_hyp_nums 11,
    h_generalize : a == p with _,
    guard_hyp_nums 13,
    guard_hyp' h := β = α,
    guard_target f x x = f p (cast h₁ a),
    h_generalize! : a == q ,
    guard_hyp_nums 13,
    guard_target ∀ q, f x x = f p q,
    casesm* [_ == _, _ = _],
    success_if_fail { refl },
    admit },
  trivial
end

end h_generalize

-- section tfae

-- example (p q r s : Prop)
--   (h₀ : p ↔ q)
--   (h₁ : q ↔ r)
--   (h₂ : r ↔ s) :
--   p ↔ s :=
-- begin
--   scc,
-- end

-- example (p' p q r r' s s' : Prop)
--   (h₀ : p' → p)
--   (h₀ : p → q)
--   (h₁ : q → r)
--   (h₁ : r' → r)
--   (h₂ : r ↔ s)
--   (h₂ : s → p)
--   (h₂ : s → s') :
--   p ↔ s :=
-- begin
--   scc,
-- end

-- example (p' p q r r' s s' : Prop)
--   (h₀ : p' → p)
--   (h₀ : p → q)
--   (h₁ : q → r)
--   (h₁ : r' → r)
--   (h₂ : r ↔ s)
--   (h₂ : s → p)
--   (h₂ : s → s') :
--   p ↔ s :=
-- begin
--   scc',
--   assumption
-- end

-- example : tfae [true, ∀ n : ℕ, 0 ≤ n * n, true, true] := begin
--   tfae_have : 3 → 1, { intro h, constructor },
--   tfae_have : 2 → 3, { intro h, constructor },
--   tfae_have : 2 ← 1, { intros h n, apply nat.zero_le },
--   tfae_have : 4 ↔ 2, { tauto },
--   tfae_finish,
-- end

-- example : tfae [] := begin
--   tfae_finish,
-- end

-- end tfae

section clear_aux_decl

example (n m : ℕ) (h₁ : n = m) (h₂ : ∃ a : ℕ, a = n ∧ a = m) : 2 * m = 2 * n :=
let ⟨a, ha⟩ := h₂ in
begin
  clear_aux_decl, -- subst will fail without this line
  subst h₁
end

example (x y : ℕ) (h₁ : ∃ n : ℕ, n * 1 = 2) (h₂ : 1 + 1 = 2 → x * 1 = y) : x = y :=
let ⟨n, hn⟩ := h₁ in
begin
  clear_aux_decl, -- finish produces an error without this line
  finish
end

end clear_aux_decl

section congr

example (c : Prop → Prop → Prop → Prop) (x x' y z z' : Prop)
  (h₀ : x ↔ x')
  (h₁ : z ↔ z') :
  c x y z ↔ c x' y z' :=
begin
  congr',
  { guard_target x = x', ext, assumption },
  { guard_target z = z', ext, assumption },
end

end congr

section convert_to

example {a b c d : ℕ} (H : a = c) (H' : b = d) : a + b = d + c :=
by {convert_to c + d = _ using 2, from H, from H', rw[add_comm]}

example {a b c d : ℕ} (H : a = c) (H' : b = d) : a + b = d + c :=
by {convert_to c + d = _ using 0, congr' 2, from H, from H', rw[add_comm]}

example (a b c d e f g N : ℕ) : (a + b) + (c + d) + (e + f) + g ≤ a + d + e + f + c + g + b :=
by {ac_change a + d + e + f + c + g + b ≤ _, refl}

end convert_to

section swap

example {α₁ α₂ α₃ : Type} : true :=
by {have : α₁, have : α₂, have : α₃, swap, swap,
    rotate, rotate, rotate, rotate 2, rotate 2, triv, recover}

end swap

section lift

example (n m k x z u : ℤ) (hn : 0 < n) (hk : 0 ≤ k + n) (hu : 0 ≤ u) (h : k + n = 2 + x) :
  k + n = m + x :=
begin
  lift n to ℕ using le_of_lt hn,
    guard_target (k + ↑n = m + x), guard_hyp hn := (0 : ℤ) < ↑n,
  lift m to ℕ,
    guard_target (k + ↑n = ↑m + x), tactic.swap, guard_target (0 ≤ m), tactic.swap,
    tactic.num_goals >>= λ n, guard (n = 2),
  lift (k + n) to ℕ using hk with l hl,
    guard_hyp l := ℕ, guard_hyp hl := ↑l = k + ↑n, guard_target (↑l = ↑m + x),
    tactic.success_if_fail (tactic.get_local `hk),
  lift x to ℕ with y hy,
    guard_hyp y := ℕ, guard_hyp hy := ↑y = x, guard_target (↑l = ↑m + x),
  lift z to ℕ with w,
    guard_hyp w := ℕ, tactic.success_if_fail (tactic.get_local `z),
  lift u to ℕ using hu with u rfl hu,
    guard_hyp hu := (0 : ℤ) ≤ ↑u,
  all_goals { admit }
end

instance can_lift_unit : can_lift unit unit :=
⟨id, λ x, true, λ x _, ⟨x, rfl⟩⟩

/- test whether new instances of `can_lift` are added as simp lemmas -/
run_cmd do l ← can_lift_attr.get_cache, guard (`can_lift_unit ∈ l)

end lift

private meta def get_exception_message (t : lean.parser unit) : lean.parser string
| s := match t s with
       | result.success a s' := result.success "No exception" s
       | result.exception none pos s' := result.success "Exception no msg" s
       | result.exception (some msg) pos s' := result.success (msg ()).to_string s
       end

@[user_command] meta def test_parser1_fail_cmd
(_ : interactive.parse (lean.parser.tk "test_parser1")) : lean.parser unit :=
do
  let msg := "oh, no!",
  let t : lean.parser unit := tactic.fail msg,
  s ← get_exception_message t,
  if s = msg then tactic.skip
  else interaction_monad.fail "Message was corrupted while being passed through `lean.parser.of_tactic`"
.

-- Due to `lean.parser.of_tactic'` priority, the following *should not* fail with
-- a VM check error, and instead catch the error gracefully and just
-- run and succeed silently.
test_parser1
