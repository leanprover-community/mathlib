/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import data.set.lattice data.prod

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
variables {s s₁ s₂ : set α} {t t₁ t₂ : set β}

namespace set

protected def prod (s : set α) (t : set β) : set (α × β) :=
{p | p.1 ∈ s ∧ p.2 ∈ t}

lemma mem_prod_eq {p : α × β} : p ∈ set.prod s t = (p.1 ∈ s ∧ p.2 ∈ t) := rfl

@[simp] lemma mem_prod {p : α × β} : p ∈ set.prod s t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

@[simp] lemma prod_empty {s : set α} : set.prod s ∅ = (∅ : set (α × β)) :=
set.ext $ by simp [set.prod]

@[simp] lemma empty_prod {t : set β} : set.prod ∅ t = (∅ : set (α × β)) :=
set.ext $ by simp [set.prod]

lemma insert_prod {a : α} {s : set α} {t : set β} :
  set.prod (insert a s) t = (prod.mk a '' t) ∪ set.prod s t :=
set.ext begin simp [set.prod, image, iff_def, or_imp_distrib] {contextual := tt}; cc end

lemma prod_insert {b : β} {s : set α} {t : set β} :
  set.prod s (insert b t) = ((λa, (a, b)) '' s) ∪ set.prod s t :=
set.ext begin simp [set.prod, image, iff_def, or_imp_distrib] {contextual := tt}; cc end

theorem prod_preimage_eq {f : γ → α} {g : δ → β} :
  set.prod (preimage f s) (preimage g t) = preimage (λp, (f p.1, g p.2)) (set.prod s t) := rfl

lemma prod_mono {s₁ s₂ : set α} {t₁ t₂ : set β} (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
  set.prod s₁ t₁ ⊆ set.prod s₂ t₂ :=
assume x ⟨h₁, h₂⟩, ⟨hs h₁, ht h₂⟩

lemma prod_inter_prod : set.prod s₁ t₁ ∩ set.prod s₂ t₂ = set.prod (s₁ ∩ s₂) (t₁ ∩ t₂) :=
subset.antisymm
  (assume ⟨a, b⟩ ⟨⟨ha₁, hb₁⟩, ⟨ha₂, hb₂⟩⟩, ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩)
  (subset_inter
    (prod_mono (inter_subset_left _ _) (inter_subset_left _ _))
    (prod_mono (inter_subset_right _ _) (inter_subset_right _ _)))

theorem monotone_prod [preorder α] {f : α → set β} {g : α → set γ}
  (hf : monotone f) (hg : monotone g) : monotone (λx, set.prod (f x) (g x)) :=
assume a b h, prod_mono (hf h) (hg h)

lemma image_swap_prod : (λp:β×α, (p.2, p.1)) '' set.prod t s = set.prod s t :=
set.ext $ assume ⟨a, b⟩, by simp [mem_image_eq, set.prod, and_comm]; exact
⟨ assume ⟨b', a', ⟨h_a, h_b⟩, h⟩, by substs a' b'; assumption,
  assume h, ⟨b, a, ⟨rfl, rfl⟩, h⟩⟩

theorem image_swap_eq_preimage_swap : image (@prod.swap α β) = preimage prod.swap :=
image_eq_preimage_of_inverse prod.swap_left_inverse prod.swap_right_inverse

lemma prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
  set.prod (image m₁ s) (image m₂ t) = image (λp:α×β, (m₁ p.1, m₂ p.2)) (set.prod s t) :=
set.ext $ by simp [-exists_and_distrib_right, exists_and_distrib_right.symm, and.left_comm, and.assoc, and.comm]

@[simp] lemma prod_singleton_singleton {a : α} {b : β} :
  set.prod {a} {b} = ({(a, b)} : set (α×β)) :=
set.ext $ by simp [set.prod]

lemma prod_neq_empty_iff {s : set α} {t : set β} :
  set.prod s t ≠ ∅ ↔ (s ≠ ∅ ∧ t ≠ ∅) :=
by simp [not_eq_empty_iff_exists]

@[simp] lemma prod_mk_mem_set_prod_eq {a : α} {b : β} {s : set α} {t : set β} :
  (a, b) ∈ set.prod s t = (a ∈ s ∧ b ∈ t) := rfl

@[simp] lemma univ_prod_univ : set.prod univ univ = (univ : set (α×β)) :=
set.ext $ assume ⟨a, b⟩, by simp

end set