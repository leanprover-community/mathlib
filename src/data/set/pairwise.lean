/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.lattice
import tactic.wlog

/-!
# Relations holding pairwise

This file defines pairwise relations and pairwise disjoint sets.

## Main declarations

* `pairwise p`: States that `p i j` for all `i ≠ j`.
* `pairwise_disjoint`: `pairwise_disjoint s` states that all elements in `s` are either equal or
  `disjoint`.
-/

open set

universes u v
variables {α : Type u} {β : Type v} {s t u : set α}

/-- A relation `p` holds pairwise if `p i j` for all `i ≠ j`. -/
def pairwise {α : Type*} (p : α → α → Prop) := ∀ i j, i ≠ j → p i j

theorem set.pairwise_on_univ {r : α → α → Prop} :
  (univ : set α).pairwise_on r ↔ pairwise r :=
by simp only [pairwise_on, pairwise, mem_univ, forall_const]

theorem set.pairwise_on.on_injective {s : set α} {r : α → α → Prop} (hs : pairwise_on s r)
  {f : β → α} (hf : function.injective f) (hfs : ∀ x, f x ∈ s) :
  pairwise (r on f) :=
λ i j hij, hs _ (hfs i) _ (hfs j) (hf.ne hij)

theorem pairwise.mono {p q : α → α → Prop} (hp : pairwise p) (h : ∀ ⦃i j⦄, p i j → q i j) :
  pairwise q :=
λ i j hij, h (hp i j hij)

theorem pairwise_on_bool {r} (hr : symmetric r) {a b : α} :
  pairwise (r on (λ c, cond c a b)) ↔ r a b :=
by simpa [pairwise, function.on_fun] using @hr a b

theorem pairwise_disjoint_on_bool [semilattice_inf_bot α] {a b : α} :
  pairwise (disjoint on (λ c, cond c a b)) ↔ disjoint a b :=
pairwise_on_bool disjoint.symm

lemma symmetric.pairwise_on [linear_order β] {r} (hr : symmetric r) (f : β → α) :
  pairwise (r on f) ↔ ∀ m n, m < n → r (f m) (f n) :=
⟨λ h m n hmn, h m n hmn.ne, λ h m n hmn, begin
  obtain hmn' | hmn' := hmn.lt_or_lt,
  { exact h _ _ hmn' },
  { exact hr (h _ _ hmn') }
end⟩

theorem pairwise_disjoint_on [semilattice_inf_bot α] [linear_order β] (f : β → α) :
  pairwise (disjoint on f) ↔ ∀ m n, m < n → disjoint (f m) (f n) :=
symmetric.pairwise_on disjoint.symm f

theorem pairwise.pairwise_on {p : α → α → Prop} (h : pairwise p) (s : set α) : s.pairwise_on p :=
λ x hx y hy, h x y

theorem pairwise_disjoint_fiber (f : α → β) : pairwise (disjoint on (λ y : β, f ⁻¹' {y})) :=
set.pairwise_on_univ.1 $ pairwise_on_disjoint_fiber f univ

variables [semilattice_inf_bot α]

/-- A collection of sets is `pairwise_disjoint`, if any two different sets in this collection
are disjoint. -/
def pairwise_disjoint (s : set α) : Prop :=
pairwise_on s disjoint

lemma pairwise_disjoint.subset {s t : set α} (ht : pairwise_disjoint t) (h : s ⊆ t) :
  pairwise_disjoint s :=
pairwise_on.mono h ht

lemma pairwise_disjoint.range {s : set α} (f : s → α) (hf : ∀ (x : s), f x ≤ x.1)
  (ht : pairwise_disjoint s) : pairwise_disjoint (range f) :=
begin
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy,
  exact (ht _ x.2 _ y.2 $ λ h, hxy $ congr_arg f $ subtype.ext h).mono (hf x) (hf y),
end

-- classical
lemma pairwise_disjoint.elim {s : set α} (hs : pairwise_disjoint s) {x y : α} (hx : x ∈ s)
  (hy : y ∈ s) (h : ¬ disjoint x y) :
  x = y :=
of_not_not $ λ hxy, h $ hs _ hx _ hy hxy

-- classical
lemma pairwise_disjoint.elim' {s : set α} (hs : pairwise_disjoint s) {x y : α} (hx : x ∈ s)
  (hy : y ∈ s) (h : x ⊓ y ≠ ⊥) :
  x = y :=
hs.elim hx hy $ λ hxy, h hxy.eq_bot

-- classical
lemma pairwise_disjoint.elim_set {s : set (set β)} (hs : pairwise_disjoint s) {x y : set β}
  (hx : x ∈ s) (hy : y ∈ s) (z : β) (hzx : z ∈ x) (hzy : z ∈ y) : x = y :=
hs.elim hx hy (not_disjoint_iff.2 ⟨z, hzx, hzy⟩)
