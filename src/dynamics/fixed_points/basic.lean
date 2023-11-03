/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.set.function
import logic.function.iterate
import group_theory.perm.basic

/-!
# Fixed points of a self-map

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define

* the predicate `is_fixed_pt f x := f x = x`;
* the set `fixed_points f` of fixed points of a self-map `f`.

We also prove some simple lemmas about `is_fixed_pt` and `∘`, `iterate`, and `semiconj`.

## Tags

fixed point
-/

open equiv

universes u v

variables {α : Type u} {β : Type v} {f fa g : α → α} {x y : α} {fb : β → β} {m n k : ℕ} {e : perm α}

namespace function

/-- A point `x` is a fixed point of `f : α → α` if `f x = x`. -/
def is_fixed_pt (f : α → α) (x : α) := f x = x

/-- Every point is a fixed point of `id`. -/
lemma is_fixed_pt_id (x : α) : is_fixed_pt id x := (rfl : _)

namespace is_fixed_pt

instance [h : decidable_eq α] {f : α → α} {x : α} : decidable (is_fixed_pt f x) :=
h (f x) x

/-- If `x` is a fixed point of `f`, then `f x = x`. This is useful, e.g., for `rw` or `simp`.-/
protected lemma eq (hf : is_fixed_pt f x) : f x = x := hf

/-- If `x` is a fixed point of `f` and `g`, then it is a fixed point of `f ∘ g`. -/
protected lemma comp (hf : is_fixed_pt f x) (hg : is_fixed_pt g x) : is_fixed_pt (f ∘ g) x :=
calc f (g x) = f x : congr_arg f hg
         ... = x   : hf

/-- If `x` is a fixed point of `f`, then it is a fixed point of `f^[n]`. -/
protected lemma iterate (hf : is_fixed_pt f x) (n : ℕ) : is_fixed_pt (f^[n]) x :=
iterate_fixed hf n

/-- If `x` is a fixed point of `f ∘ g` and `g`, then it is a fixed point of `f`. -/
lemma left_of_comp (hfg : is_fixed_pt (f ∘ g) x) (hg : is_fixed_pt g x) : is_fixed_pt f x :=
calc f x = f (g x) : congr_arg f hg.symm
     ... = x       : hfg

/-- If `x` is a fixed point of `f` and `g` is a left inverse of `f`, then `x` is a fixed
point of `g`. -/
lemma to_left_inverse (hf : is_fixed_pt f x) (h : left_inverse g f) : is_fixed_pt g x :=
calc g x = g (f x) : congr_arg g hf.symm
     ... = x       : h x

/-- If `g` (semi)conjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
protected lemma map {x : α} (hx : is_fixed_pt fa x) {g : α → β} (h : semiconj g fa fb) :
  is_fixed_pt fb (g x) :=
calc fb (g x) = g (fa x) : (h.eq x).symm
          ... = g x      : congr_arg g hx

protected lemma apply {x : α} (hx : is_fixed_pt f x) : is_fixed_pt f (f x) :=
by convert hx

lemma preimage_iterate {s : set α} (h : is_fixed_pt (set.preimage f) s) (n : ℕ) :
  is_fixed_pt (set.preimage (f^[n])) s :=
by { rw set.preimage_iterate_eq, exact h.iterate n, }

protected lemma equiv_symm (h : is_fixed_pt e x) : is_fixed_pt e.symm x :=
h.to_left_inverse e.left_inverse_symm

protected lemma perm_inv (h : is_fixed_pt e x) : is_fixed_pt ⇑(e⁻¹) x := h.equiv_symm

protected lemma perm_pow (h : is_fixed_pt e x) (n : ℕ) : is_fixed_pt ⇑(e ^ n) x := h.iterate _

protected lemma perm_zpow (h : is_fixed_pt e x) : ∀ n : ℤ, is_fixed_pt ⇑(e ^ n) x
| (int.of_nat n) := h.perm_pow _
| (int.neg_succ_of_nat n) := (h.perm_pow $ n + 1).perm_inv

end is_fixed_pt

@[simp] lemma injective.is_fixed_pt_apply_iff (hf : injective f) {x : α} :
  is_fixed_pt f (f x) ↔ is_fixed_pt f x :=
⟨λ h, hf h.eq, is_fixed_pt.apply⟩

/-- The set of fixed points of a map `f : α → α`. -/
def fixed_points (f : α → α) : set α := {x : α | is_fixed_pt f x}

instance fixed_points.decidable [decidable_eq α] (f : α → α) (x : α) :
  decidable (x ∈ fixed_points f) :=
is_fixed_pt.decidable

@[simp] lemma mem_fixed_points : x ∈ fixed_points f ↔ is_fixed_pt f x := iff.rfl

lemma mem_fixed_points_iff {α : Type*} {f : α → α} {x : α} :
  x ∈ fixed_points f ↔ f x = x :=
by refl

@[simp] lemma fixed_points_id : fixed_points (@id α) = set.univ :=
set.ext $ λ _, by simpa using is_fixed_pt_id _

lemma fixed_points_subset_range : fixed_points f ⊆ set.range f :=
λ x hx, ⟨x, hx⟩

/-- If `g` semiconjugates `fa` to `fb`, then it sends fixed points of `fa` to fixed points
of `fb`. -/
lemma semiconj.maps_to_fixed_pts {g : α → β} (h : semiconj g fa fb) :
  set.maps_to g (fixed_points fa) (fixed_points fb) :=
λ x hx, hx.map h

/-- Any two maps `f : α → β` and `g : β → α` are inverse of each other on the sets of fixed points
of `f ∘ g` and `g ∘ f`, respectively. -/
lemma inv_on_fixed_pts_comp (f : α → β) (g : β → α) :
  set.inv_on f g (fixed_points $ f ∘ g) (fixed_points $ g ∘ f) :=
⟨λ x, id, λ x, id⟩

/-- Any map `f` sends fixed points of `g ∘ f` to fixed points of `f ∘ g`. -/
lemma maps_to_fixed_pts_comp (f : α → β) (g : β → α) :
  set.maps_to f (fixed_points $ g ∘ f) (fixed_points $ f ∘ g) :=
λ x hx, hx.map $ λ x, rfl

/-- Given two maps `f : α → β` and `g : β → α`, `g` is a bijective map between the fixed points
of `f ∘ g` and the fixed points of `g ∘ f`. The inverse map is `f`, see `inv_on_fixed_pts_comp`. -/
lemma bij_on_fixed_pts_comp (f : α → β) (g : β → α) :
  set.bij_on g (fixed_points $ f ∘ g) (fixed_points $ g ∘ f) :=
(inv_on_fixed_pts_comp f g).bij_on (maps_to_fixed_pts_comp g f) (maps_to_fixed_pts_comp f g)

/-- If self-maps `f` and `g` commute, then they are inverse of each other on the set of fixed points
of `f ∘ g`. This is a particular case of `function.inv_on_fixed_pts_comp`. -/
lemma commute.inv_on_fixed_pts_comp (h : commute f g) :
  set.inv_on f g (fixed_points $ f ∘ g) (fixed_points $ f ∘ g) :=
by simpa only [h.comp_eq] using inv_on_fixed_pts_comp f g

/-- If self-maps `f` and `g` commute, then `f` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `function.bij_on_fixed_pts_comp`. -/
lemma commute.left_bij_on_fixed_pts_comp (h : commute f g) :
  set.bij_on f (fixed_points $ f ∘ g) (fixed_points $ f ∘ g) :=
by simpa only [h.comp_eq] using bij_on_fixed_pts_comp g f

/-- If self-maps `f` and `g` commute, then `g` is bijective on the set of fixed points of `f ∘ g`.
This is a particular case of `function.bij_on_fixed_pts_comp`. -/
lemma commute.right_bij_on_fixed_pts_comp (h : commute f g) :
  set.bij_on g (fixed_points $ f ∘ g) (fixed_points $ f ∘ g) :=
by simpa only [h.comp_eq] using bij_on_fixed_pts_comp f g

end function
