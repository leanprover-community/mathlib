/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import order.filter.extr topology.continuous_on

/-! # Local extrema of functions on topological spaces

This file defines special versions of `is_*_filter f a l`, `*=min/max/extr`,
from `order/filter/extr` for two kinds of filters: `nhds_within` and `nhds`.

Most statements in this file repeat those from `order/filter/extr`, and are needed only to make
dot notation return output of a correct type instead of just `is_min/max_filter`.
-/

universes u v w x

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} [topological_space α]

open set filter
open_locale topological_space

section preorder

variables [preorder β] [preorder γ] (f : α → β) (a : α) (s : set α)

/-- `is_local_min_on f a s` means that `f a ≤ f x` for all `x ∈ s` in some neighborhood of `a`. -/
def is_local_min_on := is_min_filter f a (nhds_within a s)

/-- `is_local_max_on f a s` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def is_local_max_on := is_max_filter f a (nhds_within a s)

/-- `is_local_extr_on f a s` means `is_local_min_on f a s ∨ is_local_max_on f a s`. -/
def is_local_extr_on := is_extr_filter f a (nhds_within a s)

/-- `is_local_min f a` means that `f a ≤ f x` for all `x` in some neighborhood of `a`. -/
def is_local_min := is_min_filter f a (𝓝 a)

/-- `is_local_max f a` means that `f x ≤ f a` for all `x ∈ s` in some neighborhood of `a`. -/
def is_local_max := is_max_filter f a (𝓝 a)

/-- `is_local_extr_on f a s` means `is_local_min_on f a s ∨ is_local_max_on f a s`. -/
def is_local_extr := is_extr_filter f a (𝓝 a)

variables {f a s}

lemma is_local_extr_on.elim {p : Prop} :
  is_local_extr_on f a s → (is_local_min_on f a s → p) → (is_local_max_on f a s → p) → p :=
or.elim

lemma is_local_extr.elim {p : Prop} :
  is_local_extr f a → (is_local_min f a → p) → (is_local_max f a → p) → p :=
or.elim


/-! ### Restriction to (sub)sets -/

lemma is_local_min.on (h : is_local_min f a) (s) : is_local_min_on f a s :=
h.filter_inf _

lemma is_local_max.on (h : is_local_max f a) (s) : is_local_max_on f a s :=
h.filter_inf _

lemma is_local_extr.on (h : is_local_extr f a) (s) : is_local_extr_on f a s :=
h.filter_inf _

lemma is_local_min_on.on_subset {t : set α} (hf : is_local_min_on f a t) (h : s ⊆ t) :
  is_local_min_on f a s :=
hf.filter_mono $ nhds_within_mono a h

lemma is_local_max_on.on_subset {t : set α} (hf : is_local_max_on f a t) (h : s ⊆ t) :
  is_local_max_on f a s :=
hf.filter_mono $ nhds_within_mono a h

lemma is_local_extr_on.on_subset {t : set α} (hf : is_local_extr_on f a t) (h : s ⊆ t) :
  is_local_extr_on f a s :=
hf.filter_mono $ nhds_within_mono a h

lemma is_local_min_on.inter (hf : is_local_min_on f a s) (t) : is_local_min_on f a (s ∩ t) :=
hf.on_subset (inter_subset_left s t)

lemma is_local_max_on.inter (hf : is_local_max_on f a s) (t) : is_local_max_on f a (s ∩ t) :=
hf.on_subset (inter_subset_left s t)

lemma is_local_extr_on.inter (hf : is_local_extr_on f a s) (t) : is_local_extr_on f a (s ∩ t) :=
hf.on_subset (inter_subset_left s t)

/-! ### Constant -/

lemma is_local_min_on_const {b : β} : is_local_min_on (λ _, b) a s := is_min_filter_const
lemma is_local_max_on_const {b : β} : is_local_max_on (λ _, b) a s := is_max_filter_const
lemma is_local_extr_on_const {b : β} : is_local_extr_on (λ _, b) a s := is_extr_filter_const

lemma is_local_min_const {b : β} : is_local_min (λ _, b) a := is_min_filter_const
lemma is_local_max_const {b : β} : is_local_max (λ _, b) a := is_max_filter_const
lemma is_local_extr_const {b : β} : is_local_extr (λ _, b) a := is_extr_filter_const

/-! ### Composition with (anti)monotone functions -/

lemma is_local_min.comp_mono (hf : is_local_min f a) {g : β → γ} (hg : monotone g) :
  is_local_min (g ∘ f) a :=
hf.comp_mono hg

lemma is_local_max.comp_mono (hf : is_local_max f a) {g : β → γ} (hg : monotone g) :
  is_local_max (g ∘ f) a :=
hf.comp_mono hg

lemma is_local_extr.comp_mono (hf : is_local_extr f a) {g : β → γ} (hg : monotone g) :
  is_local_extr (g ∘ f) a :=
hf.comp_mono hg

lemma is_local_min.comp_antimono (hf : is_local_min f a) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_max (g ∘ f) a :=
hf.comp_antimono hg

lemma is_local_max.comp_antimono (hf : is_local_max f a) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_min (g ∘ f) a :=
hf.comp_antimono hg

lemma is_local_extr.comp_antimono (hf : is_local_extr f a) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_extr (g ∘ f) a :=
hf.comp_antimono hg

lemma is_local_min_on.comp_mono (hf : is_local_min_on f a s) {g : β → γ} (hg : monotone g) :
  is_local_min_on (g ∘ f) a s :=
hf.comp_mono hg

lemma is_local_max_on.comp_mono (hf : is_local_max_on f a s) {g : β → γ} (hg : monotone g) :
  is_local_max_on (g ∘ f) a s :=
hf.comp_mono hg

lemma is_local_extr_on.comp_mono (hf : is_local_extr_on f a s) {g : β → γ} (hg : monotone g) :
  is_local_extr_on (g ∘ f) a s :=
hf.comp_mono hg

lemma is_local_min_on.comp_antimono (hf : is_local_min_on f a s) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_max_on (g ∘ f) a s :=
hf.comp_antimono hg

lemma is_local_max_on.comp_antimono (hf : is_local_max_on f a s) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_min_on (g ∘ f) a s :=
hf.comp_antimono hg

lemma is_local_extr_on.comp_antimono (hf : is_local_extr_on f a s) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_local_extr_on (g ∘ f) a s :=
hf.comp_antimono hg

lemma is_local_min.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_local_min f a) {g : α → γ} (hg : is_local_min g a) :
  is_local_min (λ x, op (f x) (g x)) a :=
hf.bicomp_mono hop hg

lemma is_local_max.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_local_max f a) {g : α → γ} (hg : is_local_max g a) :
  is_local_max (λ x, op (f x) (g x)) a :=
hf.bicomp_mono hop hg

-- No `extr` version because we need `hf` and `hg` to be of the same kind

lemma is_local_min_on.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_local_min_on f a s) {g : α → γ} (hg : is_local_min_on g a s) :
  is_local_min_on (λ x, op (f x) (g x)) a s :=
hf.bicomp_mono hop hg

lemma is_local_max_on.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_local_max_on f a s) {g : α → γ} (hg : is_local_max_on g a s) :
  is_local_max_on (λ x, op (f x) (g x)) a s :=
hf.bicomp_mono hop hg

/-! ### Composition with `continuous_at` -/

lemma is_local_min.comp_continuous [topological_space δ] {g : δ → α} {b : δ}
  (hf : is_local_min f (g b)) (hg : continuous_at g b) :
  is_local_min (f ∘ g) b :=
hg hf

lemma is_local_max.comp_continuous [topological_space δ] {g : δ → α} {b : δ}
  (hf : is_local_max f (g b)) (hg : continuous_at g b) :
  is_local_max (f ∘ g) b :=
hg hf

lemma is_local_extr.comp_continuous [topological_space δ] {g : δ → α} {b : δ}
  (hf : is_local_extr f (g b)) (hg : continuous_at g b) :
  is_local_extr (f ∘ g) b :=
hf.comp_tendsto hg

lemma is_local_min.comp_continuous_on [topological_space δ] {s : set δ} {g : δ → α} {b : δ}
  (hf : is_local_min f (g b)) (hg : continuous_on g s) (hb : b ∈ s) :
  is_local_min_on (f ∘ g) b s :=
hf.comp_tendsto (hg b hb)

lemma is_local_max.comp_continuous_on [topological_space δ] {s : set δ} {g : δ → α} {b : δ}
  (hf : is_local_max f (g b)) (hg : continuous_on g s) (hb : b ∈ s) :
  is_local_max_on (f ∘ g) b s :=
hf.comp_tendsto (hg b hb)

lemma is_local_extr.comp_continuous_on [topological_space δ] {s : set δ} (g : δ → α) {b : δ}
  (hf : is_local_extr f (g b)) (hg : continuous_on g s) (hb : b ∈ s) :
  is_local_extr_on (f ∘ g) b s :=
hf.elim (λ hf, (hf.comp_continuous_on hg hb).is_extr)
  (λ hf, (is_local_max.comp_continuous_on hf hg hb).is_extr)

end preorder

/-! ### Pointwise addition -/
section ordered_comm_monoid

variables [ordered_comm_monoid β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.add (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, f x + g x) a :=
hf.add hg

lemma is_local_max.add (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, f x + g x) a :=
hf.add hg

lemma is_local_min_on.add (hf : is_local_min_on f a s) (hg : is_local_min_on g a s) :
  is_local_min_on (λ x, f x + g x) a s :=
hf.add hg

lemma is_local_max_on.add (hf : is_local_max_on f a s) (hg : is_local_max_on g a s) :
  is_local_max_on (λ x, f x + g x) a s :=
hf.add hg

end ordered_comm_monoid

/-! ### Pointwise negation and subtraction -/

section ordered_comm_group

variables [ordered_comm_group β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.neg (hf : is_local_min f a) : is_local_max (λ x, -f x) a :=
hf.neg

lemma is_local_max.neg (hf : is_local_max f a) : is_local_min (λ x, -f x) a :=
hf.neg

lemma is_local_extr.neg (hf : is_local_extr f a) : is_local_extr (λ x, -f x) a :=
hf.neg

lemma is_local_min_on.neg (hf : is_local_min_on f a s) : is_local_max_on (λ x, -f x) a s :=
hf.neg

lemma is_local_max_on.neg (hf : is_local_max_on f a s) : is_local_min_on (λ x, -f x) a s :=
hf.neg

lemma is_local_extr_on.neg (hf : is_local_extr_on f a s) : is_local_extr_on (λ x, -f x) a s :=
hf.neg

lemma is_local_min.sub (hf : is_local_min f a) (hg : is_local_max g a) :
  is_local_min (λ x, f x - g x) a :=
hf.sub hg

lemma is_local_max.sub (hf : is_local_max f a) (hg : is_local_min g a) :
  is_local_max (λ x, f x - g x) a :=
hf.sub hg

lemma is_local_min_on.sub (hf : is_local_min_on f a s) (hg : is_local_max_on g a s) :
  is_local_min_on (λ x, f x - g x) a s :=
hf.sub hg

lemma is_local_max_on.sub (hf : is_local_max_on f a s) (hg : is_local_min_on g a s) :
  is_local_max_on (λ x, f x - g x) a s :=
hf.sub hg

end ordered_comm_group

open lattice

/-! ### Pointwise `sup`/`inf` -/

section semilattice_sup

variables [semilattice_sup β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.sup (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, f x ⊔ g x) a :=
hf.sup hg

lemma is_local_max.sup (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, f x ⊔ g x) a :=
hf.sup hg

lemma is_local_min_on.sup (hf : is_local_min_on f a s) (hg : is_local_min_on g a s) :
  is_local_min_on (λ x, f x ⊔ g x) a s :=
hf.sup hg

lemma is_local_max_on.sup (hf : is_local_max_on f a s) (hg : is_local_max_on g a s) :
  is_local_max_on (λ x, f x ⊔ g x) a s :=
hf.sup hg

end semilattice_sup

section semilattice_inf

variables [semilattice_inf β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.inf (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, f x ⊓ g x) a :=
hf.inf hg

lemma is_local_max.inf (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, f x ⊓ g x) a :=
hf.inf hg

lemma is_local_min_on.inf (hf : is_local_min_on f a s) (hg : is_local_min_on g a s) :
  is_local_min_on (λ x, f x ⊓ g x) a s :=
hf.inf hg

lemma is_local_max_on.inf (hf : is_local_max_on f a s) (hg : is_local_max_on g a s) :
  is_local_max_on (λ x, f x ⊓ g x) a s :=
hf.inf hg

end semilattice_inf

/-! ### Pointwise `min`/`max` -/

section decidable_linear_order

variables [decidable_linear_order β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_local_min.min (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, min (f x) (g x)) a :=
hf.min hg

lemma is_local_max.min (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, min (f x) (g x)) a :=
hf.min hg

lemma is_local_min_on.min (hf : is_local_min_on f a s) (hg : is_local_min_on g a s) :
  is_local_min_on (λ x, min (f x) (g x)) a s :=
hf.min hg

lemma is_local_max_on.min (hf : is_local_max_on f a s) (hg : is_local_max_on g a s) :
  is_local_max_on (λ x, min (f x) (g x)) a s :=
hf.min hg

lemma is_local_min.max (hf : is_local_min f a) (hg : is_local_min g a) :
  is_local_min (λ x, max (f x) (g x)) a :=
hf.max hg

lemma is_local_max.max (hf : is_local_max f a) (hg : is_local_max g a) :
  is_local_max (λ x, max (f x) (g x)) a :=
hf.max hg

lemma is_local_min_on.max (hf : is_local_min_on f a s) (hg : is_local_min_on g a s) :
  is_local_min_on (λ x, max (f x) (g x)) a s :=
hf.max hg

lemma is_local_max_on.max (hf : is_local_max_on f a s) (hg : is_local_max_on g a s) :
  is_local_max_on (λ x, max (f x) (g x)) a s :=
hf.max hg

end decidable_linear_order
