/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Quotients -- extends the core library
-/
variables {α : Sort*} {β : Sort*}

@[simp] theorem quotient.eq [r : setoid α] {x y : α} : ⟦x⟧ = ⟦y⟧ ↔ x ≈ y :=
⟨quotient.exact, quotient.sound⟩

theorem forall_quotient_iff {α : Type*} [r : setoid α] {p : quotient r → Prop} :
  (∀a:quotient r, p a) ↔ (∀a:α, p ⟦a⟧) :=
⟨assume h x, h _, assume h a, a.induction_on h⟩

noncomputable def quot.out {r : α → α → Prop} (q : quot r) : α :=
classical.some (quot.exists_rep q)

@[simp] theorem quot.out_eq {r : α → α → Prop} (q : quot r) : quot.mk r q.out = q :=
classical.some_spec (quot.exists_rep q)

noncomputable def quotient.out [s : setoid α] : quotient s → α := quot.out

@[simp] theorem quotient.out_eq [s : setoid α] (q : quotient s) : ⟦q.out⟧ = q := q.out_eq

theorem quotient.mk_out [s : setoid α] (a : α) : ⟦a⟧.out ≈ a :=
quotient.exact (quotient.out_eq _)

def {u} trunc (α : Sort u) : Sort u := @quot α (λ _ _, true)

namespace trunc

def mk (a : α) : trunc α := quot.mk _ a

def lift (f : α → β) (c : ∀ a b : α, f a = f b) : trunc α → β :=
quot.lift f (λ a b _, c a b)

theorem ind {β : trunc α → Prop} : (∀ a : α, β (mk a)) → ∀ q : trunc α, β q := quot.ind

protected theorem lift_beta (f : α → β) (c) (a : α) : lift f c (mk a) = f a := rfl

@[reducible, elab_as_eliminator]
protected def lift_on (q : trunc α) (f : α → β)
  (c : ∀ a b : α, f a = f b) : β := lift f c q

@[elab_as_eliminator]
protected theorem induction_on {β : trunc α → Prop} (q : trunc α)
  (h : ∀ a, β (mk a)) : β q := ind h q

theorem exists_rep (q : trunc α) : ∃ a : α, mk a = q := quot.exists_rep q

attribute [elab_as_eliminator]
protected theorem induction_on₂
   {C : trunc α → trunc β → Prop} (q₁ : trunc α) (q₂ : trunc β) (h : ∀ a b, C (mk a) (mk b)) : C q₁ q₂ :=
trunc.induction_on q₁ $ λ a₁, trunc.induction_on q₂ (h a₁)

protected theorem eq (a b : trunc α) : a = b :=
trunc.induction_on₂ a b (λ x y, quot.sound trivial)

instance : subsingleton (trunc α) := ⟨trunc.eq⟩

variable {C : trunc α → Sort*}

@[reducible, elab_as_eliminator]
protected def rec
   (f : Π a, C (mk a)) (h : ∀ (a b : α), (eq.rec (f a) (trunc.eq (mk a) (mk b)) : C (mk b)) = f b)
   (q : trunc α) : C q :=
quot.rec f (λ a b _, h a b) q

@[reducible, elab_as_eliminator]
protected def rec_on (q : trunc α) (f : Π a, C (mk a))
  (h : ∀ (a b : α), (eq.rec (f a) (trunc.eq (mk a) (mk b)) : C (mk b)) = f b) : C q :=
trunc.rec f h q

@[reducible, elab_as_eliminator]
protected def rec_on_subsingleton
   [∀ a, subsingleton (C (mk a))] (q : trunc α) (f : Π a, C (mk a)) : C q :=
trunc.rec f (λ a b, subsingleton.elim _ (f b)) q

noncomputable def out : trunc α → α := quot.out

@[simp] theorem out_eq (q : trunc α) : mk q.out = q := trunc.eq _ _

end trunc

