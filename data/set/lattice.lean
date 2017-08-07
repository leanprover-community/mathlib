/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors Jeremy Avigad, Leonardo de Moura, Johannes Hölzl

-- QUESTION: can make the first argument in ∀ x ∈ a, ... implicit?
-/
import logic.basic data.set.basic
import algebra.lattice algebra.order algebra.lattice.complete_boolean_algebra
import tactic.finish

open function tactic set lattice auto

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace set

instance lattice_set : complete_lattice (set α) :=
{ lattice.complete_lattice .
  le           := (⊆),
  le_refl      := subset.refl,
  le_trans     := assume a b c, subset.trans,
  le_antisymm  := assume a b, subset.antisymm,

  lt           := λ x y, x ⊆ y ∧ ¬ y ⊆ x,
  lt_iff_le_not_le := λ x y, iff.refl _,

  sup          := (∪),
  le_sup_left  := subset_union_left,
  le_sup_right := subset_union_right,
  sup_le       := assume a b c, union_subset,

  inf          := (∩),
  inf_le_left  := inter_subset_left,
  inf_le_right := inter_subset_right,
  le_inf       := assume a b c, subset_inter,

  top          := {a | true },
  le_top       := assume s a h, trivial,

  bot          := ∅,
  bot_le       := assume s a, false.elim,

  Sup          := λs, {a | ∃ t ∈ s, a ∈ t },
  le_Sup       := assume s t t_in a a_in, ⟨t, ⟨t_in, a_in⟩⟩,
  Sup_le       := assume s t h a ⟨t', ⟨t'_in, a_in⟩⟩, h t' t'_in a_in,

  Inf          := λs, {a | ∀ t ∈ s, a ∈ t },
  le_Inf       := assume s t h a a_in t' t'_in, h t' t'_in a_in,
  Inf_le       := assume s t t_in a h, h _ t_in }

instance : distrib_lattice (set α) :=
{ set.lattice_set with
  le_sup_inf     := assume s t u x ⟨h₁, h₂⟩,
    match h₁ with
    | or.inl h₁ := or.inl h₁
    | or.inr h₁ :=
      match h₂ with
      | or.inl h₂ := or.inl h₂
      | or.inr h₂ := or.inr ⟨h₁, h₂⟩
      end
    end }

lemma monotone_image {f : α → β} : monotone (image f) :=
assume s t, assume h : s ⊆ t, image_subset _ h

/- union and intersection over a family of sets indexed by a type -/

@[reducible] def Union (s : ι → set β) : set β := supr s

@[reducible] def Inter (s : ι → set β) : set β := infi s

notation `⋃` binders `, ` r:(scoped f, Union f) := r
notation `⋂` binders `, ` r:(scoped f, Inter f) := r

@[simp] theorem mem_Union_eq (x : β) (s : ι → set β) : (x ∈ ⋃ i, s i) = (∃ i, x ∈ s i) :=
propext
  ⟨assume ⟨t, ⟨⟨a, (t_eq : t = s a)⟩, (h : x ∈ t)⟩⟩, ⟨a, t_eq ▸ h⟩,
  assume ⟨a, h⟩, ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩
/- alternative proof: dsimp [Union, supr, Sup]; simp -/
  -- TODO: more rewrite rules wrt forall / existentials and logical connectives
  -- TODO: also eliminate ∃i, ... ∧ i = t ∧ ...

@[simp] theorem mem_Inter_eq (x : β) (s : ι → set β) : (x ∈ ⋂ i, s i) = (∀ i, x ∈ s i) :=
propext
  ⟨assume (h : ∀a ∈ {a : set β | ∃i, a = s i}, x ∈ a) a, h (s a) ⟨a, rfl⟩,
  assume h t ⟨a, (eq : t = s a)⟩, eq.symm ▸ h a⟩


theorem Union_subset {s : ι → set β} {t : set β} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
-- TODO: should be simpler when sets' order is based on lattices
@supr_le (set β) _ set.lattice_set _ _ h

theorem Union_subset_iff {α : Sort u} {s : α → set β} {t : set β} : (⋃ i, s i) ⊆ t ↔ (∀ i, s i ⊆ t):=
⟨assume h i, subset.trans (le_supr s _) h, Union_subset⟩

theorem mem_Inter {α : Sort u} {x : β} {s : α → set β} : (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) :=
assume h t ⟨a, (eq : t = s a)⟩, eq.symm ▸ h a

theorem subset_Inter {t : set β} {s : α → set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
-- TODO: should be simpler when sets' order is based on lattices
@le_infi (set β) _ set.lattice_set _ _ h

@[simp] -- complete_boolean_algebra
theorem compl_Union (s : α → set β) : - (⋃ i, s i) = (⋂ i, - s i) :=
ext (λ x, begin simp, apply not_exists_iff end)

-- classical -- complete_boolean_algebra
theorem compl_Inter (s : α → set β) : -(⋂ i, s i) = (⋃ i, - s i) :=
ext (λ x, begin simp, apply classical.not_forall_iff end)

-- classical -- complete_boolean_algebra
theorem Union_eq_comp_Inter_comp (s : α → set β) : (⋃ i, s i) = - (⋂ i, - s i) :=
by simp [compl_Inter, compl_compl]

-- classical -- complete_boolean_algebra
theorem Inter_eq_comp_Union_comp (s : α → set β) : (⋂ i, s i) = - (⋃ i, -s i) :=
by simp [compl_compl]

theorem inter_distrib_Union_left (s : set β) (t : α → set β) :
  s ∩ (⋃ i, t i) = ⋃ i, s ∩ t i :=
set.ext (by simp)

-- classical
theorem union_distrib_Inter_left (s : set β) (t : α → set β) :
  s ∪ (⋂ i, t i) = ⋂ i, s ∪ t i :=
set.ext $ assume x, by simp [classical.forall_or_distrib_left]

/- bounded unions and intersections -/

theorem mem_bUnion {s : set α} {t : α → set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
  y ∈ ⋃ x ∈ s, t x :=
by simp; exact ⟨x, ⟨xs, ytx⟩⟩

theorem mem_bInter {s : set α} {t : α → set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) :
  y ∈ ⋂ x ∈ s, t x :=
by simp; assumption

theorem bUnion_subset {s : set α} {t : set β} {u : α → set β} (h : ∀ x ∈ s, u x ⊆ t) :
  (⋃ x ∈ s, u x) ⊆ t :=
show (⨆ x ∈ s, u x) ≤ t, -- TODO: should not be necessary when sets' order is based on lattices
  from supr_le $ assume x, supr_le (h x)

theorem subset_bInter {s : set α} {t : set β} {u : α → set β} (h : ∀ x ∈ s, t ⊆ u x) :
  t ⊆ (⋂ x ∈ s, u x) :=
show t ≤ (⨅ x ∈ s, u x), -- TODO: should not be necessary when sets' order is based on lattices
  from le_infi $ assume x, le_infi (h x)

theorem subset_bUnion_of_mem {s : set α} {u : α → set β} {x : α} (xs : x ∈ s) :
  u x ⊆ (⋃ x ∈ s, u x) :=
show u x ≤ (⨆ x ∈ s, u x),
  from le_supr_of_le x $ le_supr _ xs

theorem bInter_subset_of_mem {s : set α} {t : α → set β} {x : α} (xs : x ∈ s) :
  (⋂ x ∈ s, t x) ⊆ t x :=
show (⨅x ∈ s, t x) ≤ t x,
  from infi_le_of_le x $ infi_le _ xs

@[simp] theorem bInter_empty (u : α → set β) : (⋂ x ∈ (∅ : set α), u x) = univ :=
show (⨅x ∈ (∅ : set α), u x) = ⊤, -- simplifier should be able to rewrite x ∈ ∅ to false.
  from infi_emptyset

@[simp] theorem bInter_univ (u : α → set β) : (⋂ x ∈ @univ α, u x) = ⋂ x, u x :=
infi_univ

-- TODO(Jeremy): here is an artifact of the the encoding of bounded intersection:
-- without dsimp, the next theorem fails to type check, because there is a lambda
-- in a type that needs to be contracted. Using simp [eq_of_mem_singleton xa] also works.

@[simp] theorem bInter_singleton (a : α) (s : α → set β) : (⋂ x ∈ ({a} : set α), s x) = s a :=
show (⨅ x ∈ ({a} : set α), s x) = s a, by simp

theorem bInter_union (s t : set α) (u : α → set β) :
  (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ (⋂ x ∈ t, u x) :=
show (⨅ x ∈ s ∪ t, u x) = (⨅ x ∈ s, u x) ⊓ (⨅ x ∈ t, u x),
  from infi_union

-- TODO(Jeremy): simp [insert_eq, bInter_union] doesn't work
@[simp] theorem bInter_insert (a : α) (s : set α) (t : α → set β) :
  (⋂ x ∈ insert a s, t x) = t a ∩ (⋂ x ∈ s, t x) :=
begin rw insert_eq, simp [bInter_union] end

-- TODO(Jeremy): another example of where an annotation is needed

theorem bInter_pair (a b : α) (s : α → set β) :
  (⋂ x ∈ ({a, b} : set α), s x) = s a ∩ s b :=
by rw insert_of_has_insert; simp

@[simp] theorem bUnion_empty (s : α → set β) : (⋃ x ∈ (∅ : set α), s x) = ∅ :=
supr_emptyset

@[simp] theorem bUnion_univ (s : α → set β) : (⋃ x ∈ @univ α, s x) = ⋃ x, s x :=
supr_univ

@[simp] theorem bUnion_singleton (a : α) (s : α → set β) : (⋃ x ∈ ({a} : set α), s x) = s a :=
supr_singleton

theorem bUnion_union (s t : set α) (u : α → set β) :
  (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ (⋃ x ∈ t, u x) :=
supr_union

-- TODO(Jeremy): once again, simp doesn't do it alone.

@[simp] theorem bUnion_insert (a : α) (s : set α) (t : α → set β) :
  (⋃ x ∈ insert a s, t x) = t a ∪ (⋃ x ∈ s, t x) :=
begin rw [insert_eq], simp [bUnion_union] end

theorem bUnion_pair (a b : α) (s : α → set β) :
  (⋃ x ∈ ({a, b} : set α), s x) = s a ∪ s b :=
by rw insert_of_has_insert; simp

@[reducible] def sInter (S : set (set α)) : set α := Inf S

prefix `⋂₀`:110 := sInter

theorem mem_sUnion {x : α} {t : set α} {S : set (set α)} (hx : x ∈ t) (ht : t ∈ S) :
  x ∈ ⋃₀ S :=
⟨t, ⟨ht, hx⟩⟩

@[simp] theorem mem_sUnion_eq {x : α} {S : set (set α)} : x ∈ ⋃₀ S = (∃t ∈ S, x ∈ t) := rfl

-- is this theorem really necessary?
theorem not_mem_of_not_mem_sUnion {x : α} {t : set α} {S : set (set α)}
    (hx : x ∉ ⋃₀ S) (ht : t ∈ S) :
  x ∉ t :=
assume : x ∈ t,
have x ∈ ⋃₀ S, from mem_sUnion this ht,
show false, from hx this

theorem mem_sInter {x : α} {t : set α} {S : set (set α)} (h : ∀ t ∈ S, x ∈ t) : x ∈ ⋂₀ S := h

@[simp] theorem mem_sInter_eq {x : α} {S : set (set α)} : x ∈ ⋂₀ S = (∀ t ∈ S, x ∈ t) := rfl

theorem sInter_subset_of_mem {S : set (set α)} {t : set α} (tS : t ∈ S) : (⋂₀ S) ⊆ t :=
Inf_le tS

theorem subset_sUnion_of_mem {S : set (set α)} {t : set α} (tS : t ∈ S) : t ⊆ (⋃₀ S) :=
le_Sup tS

theorem sUnion_subset {S : set (set α)} {t : set α} (h : ∀t' ∈ S, t' ⊆ t) : (⋃₀ S) ⊆ t :=
Sup_le h

theorem sUnion_subset_iff {s : set (set α)} {t : set α} : (⋃₀ s) ⊆ t ↔ ∀t' ∈ s, t' ⊆ t :=
⟨assume h t' ht', subset.trans (subset_sUnion_of_mem ht') h, sUnion_subset⟩

theorem subset_sInter {S : set (set α)} {t : set α} (h : ∀t' ∈ S, t ⊆ t') : t ⊆ (⋂₀ S) :=
le_Inf h

@[simp] theorem sUnion_empty : ⋃₀ ∅ = (∅ : set α) := Sup_empty

@[simp] theorem sInter_empty : ⋂₀ ∅ = (univ : set α) := Inf_empty

@[simp] theorem sUnion_singleton (s : set α) : ⋃₀ {s} = s := Sup_singleton

@[simp] theorem sInter_singleton (s : set α) : ⋂₀ {s} = s := Inf_singleton

theorem sUnion_union (S T : set (set α)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T := Sup_union

theorem sInter_union (S T : set (set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T := Inf_union

@[simp] theorem sUnion_insert (s : set α) (T : set (set α)) : ⋃₀ (insert s T) = s ∪ ⋃₀ T := Sup_insert

@[simp] theorem sInter_insert (s : set α) (T : set (set α)) : ⋂₀ (insert s T) = s ∩ ⋂₀ T := Inf_insert

@[simp] theorem sUnion_image (f : α → set β) (s : set α) : ⋃₀ (f '' s) = ⋃ x ∈ s, f x := Sup_image

@[simp] theorem sInter_image (f : α → set β) (s : set α) : ⋂₀ (f '' s) = ⋂ x ∈ s, f x := Inf_image

theorem compl_sUnion (S : set (set α)) :
  - ⋃₀ S = ⋂₀ (compl '' S) :=
set.ext $ assume x,
  ⟨assume : ¬ (∃s∈S, x ∈ s), assume s h,
    match s, h with
    ._, ⟨t, hs, rfl⟩ := assume h, this ⟨t, hs, h⟩
    end,
    assume : ∀s, s ∈ compl '' S → x ∈ s,
    assume ⟨t, tS, xt⟩, this (compl t) (mem_image_of_mem _ tS) xt⟩

-- classical
theorem sUnion_eq_compl_sInter_compl (S : set (set α)) :
  ⋃₀ S = - ⋂₀ (compl '' S) :=
by rw [←compl_compl (⋃₀ S), compl_sUnion]

-- classical
theorem compl_sInter (S : set (set α)) :
  - ⋂₀ S = ⋃₀ (compl '' S) :=
by rw [sUnion_eq_compl_sInter_compl, compl_compl_image]

-- classical
theorem sInter_eq_comp_sUnion_compl (S : set (set α)) :
   ⋂₀ S = -(⋃₀ (compl '' S)) :=
by rw [←compl_compl (⋂₀ S), compl_sInter]

theorem inter_empty_of_inter_sUnion_empty {s t : set α} {S : set (set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀ S = ∅) :
  s ∩ t = ∅ :=
eq_empty_of_subset_empty
  begin rw ←h, apply inter_subset_inter_left, apply subset_sUnion_of_mem hs end

theorem Union_eq_sUnion_image (s : α → set β) : (⋃ i, s i) = ⋃₀ (s '' univ) :=
by simp

theorem Inter_eq_sInter_image {α I : Type} (s : I → set α) : (⋂ i, s i) = ⋂₀ (s '' univ) :=
by simp

instance : complete_boolean_algebra (set α) :=
{ set.lattice_set with
  neg                 := compl,
  sub                 := (\),
  inf_neg_eq_bot      := assume s, ext $ assume x, ⟨assume ⟨h, nh⟩, nh h, false.elim⟩,
  sup_neg_eq_top      := assume s, ext $ assume x, ⟨assume h, trivial, assume _, classical.em $ x ∈ s⟩,
  le_sup_inf          := distrib_lattice.le_sup_inf,
  sub_eq              := assume x y, rfl,
  infi_sup_le_sup_Inf := assume s t x, show x ∈ (⋂ b ∈ t, s ∪ b) → x ∈ s ∪ (⋂₀ t),
    by simp; exact assume h,
      or.imp_right
        (assume hn : x ∉ s, assume i hi, or.resolve_left (h i hi) hn)
        (classical.em $ x ∈ s),
  inf_Sup_le_supr_inf := assume s t x, show x ∈ s ∩ (⋃₀ t) → x ∈ (⋃ b ∈ t, s ∩ b), by simp; exact id }

theorem union_sdiff_same {a b : set α} : a ∪ (b \ a) = a ∪ b :=
lattice.sup_sub_same

@[simp] theorem union_same_compl {a : set α} : a ∪ (-a) = univ :=
sup_neg_eq_top

@[simp] theorem sdiff_singleton_eq_same {a : α} {s : set α} (h : a ∉ s) : s \ {a} = s :=
sub_eq_left $ eq_empty_of_forall_not_mem $ assume x ⟨ht, ha⟩,
  begin simp at ha, simp [ha] at ht, exact h ht end

@[simp] theorem insert_sdiff_singleton {a : α} {s : set α} :
  insert a (s \ {a}) = insert a s :=
by simp [insert_eq, union_sdiff_same]

theorem monotone_preimage {f : α → β} : monotone (preimage f) := assume a b h, preimage_mono h

@[simp] theorem preimage_Union {ι : Sort w} {f : α → β} {s : ι → set β} :
  preimage f (⋃i, s i) = (⋃i, preimage f (s i)) :=
set.ext $ by simp [preimage]

@[simp] theorem preimage_sUnion {f : α → β} {s : set (set β)} :
  preimage f (⋃₀ s) = (⋃t ∈ s, preimage f t) :=
set.ext $ by simp [preimage]

/- disjoint sets -/

section disjoint
variable [semilattice_inf_bot α]
def disjoint (a b : α) : Prop := a ⊓ b = ⊥

theorem disjoint_symm {a b : α} : disjoint a b → disjoint b a :=
assume : a ⊓ b = ⊥, show b ⊓ a = ⊥, from this ▸ inf_comm

theorem disjoint_bot_left {a : α} : disjoint ⊥ a := bot_inf_eq
theorem disjoint_bot_right {a : α} : disjoint a ⊥ := inf_bot_eq

end disjoint

end set
