/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Seul Baek

Linear natural number arithmetic terms in pre-normalized form.
-/

import tactic.omega.term

open tactic

namespace omega
namespace nat 

@[derive has_reflect, derive decidable_eq]
inductive preterm : Type
| cst : nat → preterm 
| var : nat → nat → preterm
| add : preterm → preterm → preterm 
| sub : preterm → preterm → preterm 

local notation `&` k := preterm.cst k
local infix `**` : 300 := preterm.var 
local notation t `+*` s := preterm.add t s
local notation t `-*` s := preterm.sub t s

namespace preterm 

meta def induce (tac : tactic unit := tactic.skip) : tactic unit := 
`[ intro t, induction t with m m n t s iht ihs t s iht ihs; tac]

def val (v : nat → nat) : preterm → nat 
| (& i) := i
| (i ** n) := 
  if i = 1 
  then v n
  else (v n) * i
| (t1 +* t2) := t1.val + t2.val 
| (t1 -* t2) := t1.val - t2.val 

@[simp] lemma val_const {v : nat → nat} {m : nat} :
  (& m).val v = m := rfl

@[simp] lemma val_var {v : nat → nat} {m n : nat} :
  (m ** n).val v = m * (v n) :=
begin
  simp only [val], by_cases h1 : m = 1,
  rw [if_pos h1, h1, one_mul],
  rw [if_neg h1, mul_comm], 
end

@[simp] lemma val_add {v : nat → nat} {t s : preterm} : 
  (t +* s).val v = t.val v + s.val v := rfl
  
@[simp] lemma val_sub {v : nat → nat} {t s : preterm} : 
  (t -* s).val v = t.val v - s.val v := rfl

def fresh_index : preterm → nat 
| (& _)      := 0
| (i ** n)   := n + 1
| (t1 +* t2) := max t1.fresh_index t2.fresh_index 
| (t1 -* t2) := max t1.fresh_index t2.fresh_index 

def val_constant (v w : nat → nat) :
  ∀ t : preterm, (∀ x < t.fresh_index, v x = w x) → 
  t.val v = t.val w 
| (& n)      h1 := rfl 
| (m ** n)   h1 := 
  begin
    simp only [val_var], 
    apply congr_arg (λ y, m * y),
    apply h1 _ (lt_add_one _) 
  end 
| (t +* s) h1 := 
  begin
    simp only [val_add], 
    have ht := val_constant t 
      (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_left _ _))),
    have hs := val_constant s 
      (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_right _ _))),
    rw [ht, hs]
  end 
| (t -* s) h1 := 
  begin
    simp only [val_sub],
    have ht := val_constant t 
      (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_left _ _))),
    have hs := val_constant s 
      (λ x hx, h1 _ (lt_of_lt_of_le hx (le_max_right _ _))),
    rw [ht, hs]
  end 

def repr : preterm → string 
| (& i)      := i.repr
| (i ** n)   := i.repr ++ "*x" ++ n.repr
| (t1 +* t2) := "(" ++ t1.repr ++ " + " ++ t2.repr ++ ")"
| (t1 -* t2) := "(" ++ t1.repr ++ " - " ++ t2.repr ++ ")"

@[simp] def add_one (t : preterm) : preterm := t +* (&1)

def sub_free : preterm → Prop 
| (& m)    := true
| (m ** n) := true
| (t +* s) := t.sub_free ∧ s.sub_free
| (_ -* _) := false

end preterm

local notation as `{` m `↦` a `;` a' `}` := list.func.set a' a as m

@[simp] def canonize : preterm → term 
| (& m)    := ⟨↑m,[]⟩  
| (m ** n) := ⟨0,[]{n ↦ ↑m ; 0}⟩ 
| (t +* s) := term.add (canonize t) (canonize s)
| (_ -* _) := ⟨0,[]⟩ 

@[simp] lemma val_canonize {v : nat → nat} : 
  ∀ {t : preterm}, t.sub_free → 
  (canonize t).val (λ x, ↑(v x)) = t.val v
| (& i) h1 := 
  by simp only [canonize, preterm.val_const, 
     term.val, coeffs.val_nil, add_zero]
| (i ** n) h1 := 
  by simp only [preterm.val_var, coeffs.val_set,
      term.val, zero_add, int.coe_nat_mul, canonize]
| (t +* s) h1 := 
  by simp only [val_canonize h1.left, 
     val_canonize h1.right, int.coe_nat_add,
     canonize, term.val_add, preterm.val_add] 

end nat

end omega
