/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Countable sets.
-/

import data.encodable data.set.finite logic.function
noncomputable theory

open function set encodable

open classical (hiding some)
local attribute [instance] prop_decidable
universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace set

/-- Countable sets

A set is countable if there exists a injective functions from the set into the natural numbers.
This is choosen instead of surjective functions, as this would require that α is non empty.
-/
def countable (s : set α) : Prop := ∃f:α → ℕ, ∀x ∈ s, ∀y ∈ s, f x = f y → x = y

lemma countable_iff_exists_surjective [ne : inhabited α] {s : set α} :
  countable s ↔ (∃f:ℕ → α, s ⊆ range f) :=
iff.intro
  (assume ⟨f, hf⟩, ⟨inv_fun_on f s, assume a ha, ⟨f a, inv_fun_on_eq' hf ha⟩⟩)
  (assume ⟨f, hf⟩, ⟨inv_fun f, assume x hx y hy h,
    calc x = f (inv_fun f x) : (inv_fun_eq $ hf hx).symm
      ... = f (inv_fun f y) : by rw [h]
      ... = y : inv_fun_eq $ hf hy⟩)

lemma countable.to_encodable {s : set α} (h : countable s) : encodable s :=
let f := classical.some h in
have hf : ∀x∈s, ∀y∈s, f x = f y → x = y, from classical.some_spec h,
let f' : {a // a ∈ s} → ℕ := f ∘ subtype.val in
encodable.of_inj f' $ assume ⟨a, ha⟩ ⟨b, hb⟩ (h : f a = f b), subtype.eq $ hf a ha b hb h

lemma countable_encodable' (s : set α) [encodable s] : countable s :=
⟨λx, if h : x ∈ s then @encode s _ ⟨x, h⟩ else 0, assume x hx y hy h,
  have @encode s _ ⟨x, hx⟩ = @encode s _ ⟨y, hy⟩,
    by simp [hx, hy] at h; assumption,
  have decode s (@encode s _ ⟨x, hx⟩) = decode s (@encode s _ ⟨y, hy⟩),
    from congr_arg _ this,
  by simpa [encodek]⟩

lemma countable_encodable [e : encodable α] {s : set α} : countable s :=
⟨encode, assume x _ y _ eq,
  have decode α (encode x) = decode α (encode y), from congr_arg _ eq,
  by simpa [encodek]⟩

@[simp] lemma countable_empty : countable (∅ : set α) :=
⟨λ_, 0, by simp⟩

@[simp] lemma countable_singleton {a : α} : countable ({a} : set α) :=
⟨λ_, 0, by simp⟩

lemma countable_subset {s₁ s₂ : set α} (h : s₁ ⊆ s₂) : countable s₂ → countable s₁
| ⟨f, hf⟩ := ⟨f, assume x hx y hy eq, hf x (h hx) y (h hy) eq⟩

lemma countable_image {s : set α} {f : α → β} (hs : countable s) : countable (f '' s) :=
let f' : s → f '' s := λ⟨a, ha⟩, ⟨f a, mem_image_of_mem f ha⟩ in
have hf' : surjective f', from assume ⟨b, a, ha, hab⟩, ⟨⟨a, ha⟩, subtype.eq hab⟩,
@countable_encodable' _ _ $ @encodable.of_inj _ _ hs.to_encodable (surj_inv hf') (injective_surj_inv hf')

lemma countable_sUnion {s : set (set α)} (hs : countable s) (h : ∀a∈s, countable a) :
  countable (⋃₀ s) :=
by_cases
  (assume : nonempty α, let ⟨a⟩ := this, inh : inhabited α := ⟨a⟩ in
    let ⟨fs, hfs⟩ := countable_iff_exists_surjective.mp hs in
    have ∀t, ∃ft:ℕ → α, t ∈ s → t ⊆ range ft,
      from assume t,
      by_cases
        (assume : t ∈ s,
          let ⟨ft, hft⟩ := (@countable_iff_exists_surjective α inh _).mp $ h t this in
          ⟨ft, assume _, hft⟩)
        (assume : t ∉ s, ⟨λ_, a, assume h, (this h).elim⟩),
    have ∃ft:(∀t:set α, ℕ → α), ∀t∈s, t ⊆ range (ft t),
      by simp [classical.skolem] at this; assumption,
    let ⟨ft, hft⟩ := this in
    (@countable_iff_exists_surjective α inh _).mpr
      ⟨(λp:ℕ×ℕ, ft (fs p.1) p.2) ∘ nat.unpair,
        by simp [subset_def];
        from assume a t ht ha,
        let ⟨i, hi⟩ := hfs ht, ⟨j, hj⟩ := hft t ht ha in
        ⟨nat.mkpair i j, by simp [function.comp, nat.unpair_mkpair, hi, hj]⟩⟩)
  (assume : ¬ nonempty α, ⟨λ_, 0, assume a, (this ⟨a⟩).elim⟩)

lemma countable_bUnion {s : set α} {t : α → set β} (hs : countable s) (ht : ∀a∈s, countable (t a)) :
  countable (⋃a∈s, t a) :=
have ⋃₀ (t '' s) = (⋃a∈s, t a), from lattice.Sup_image,
by rw [←this];
from (countable_sUnion (countable_image hs) $ assume a ⟨s', hs', eq⟩, eq ▸ ht s' hs')

lemma countable_Union {t : α → set β} [encodable α] (ht : ∀a, countable (t a)) :
  countable (⋃a, t a) :=
suffices countable (⋃a∈(univ : set α), t a), by simpa,
countable_bUnion countable_encodable (assume a _, ht a)

lemma countable_Union_Prop {p : Prop} {t : p → set β} (ht : ∀h:p, countable (t h)) :
  countable (⋃h:p, t h) :=
by by_cases p; simp [h, ht]

lemma countable_union {s₁ s₂ : set α} (h₁ : countable s₁) (h₂ : countable s₂) : countable (s₁ ∪ s₂) :=
have s₁ ∪ s₂ = (⨆b ∈ ({tt, ff} : set bool), bool.cases_on b s₁ s₂),
  by simp [lattice.supr_or, lattice.supr_sup_eq]; refl,
by rw [this]; from countable_bUnion countable_encodable (assume b,
  match b with
  | tt := by simp [h₂]
  | ff := by simp [h₁]
  end)

lemma countable_insert {s : set α} {a : α} (h : countable s) : countable (insert a s) :=
by rw [set.insert_eq]; from countable_union countable_singleton h

lemma countable_finite {s : set α} : finite s → countable s
| ⟨h⟩ := by resetI; haveI := (trunc_encodable_of_fintype s).out; apply countable_encodable'

lemma countable_set_of_finite_subset {s : set α} (h : countable s) :
  countable {t | finite t ∧ t ⊆ s } :=
have {t | finite t ∧ t ⊆ s } ⊆
  (λt : finset {a:α // a ∈ s}, {a:α | ∃h:a∈s, subtype.mk a h ∈ t}) '' univ,
  from assume t ht,
  begin
    cases ht with ht₁ ht₂, revert ht₂,
    refine finite.induction_on ht₁ _ (λ a t ha ht ih, _); intro ht₂,
    { exact ⟨∅, mem_univ _, by simp⟩ },
    { exact
        have has : a ∈ s, from ht₂ $ mem_insert _ _,
        have t ⊆ s, from assume x hx, ht₂ $ mem_insert_of_mem _ hx,
        let ⟨t', ht', eq⟩ := ih this in
        ⟨insert ⟨a, has⟩ t', mem_univ _,
          set.ext $ assume x,
          begin
            simp [eq.symm, iff_def, or_imp_distrib, has] {contextual:=tt},
            constructor,
            exact assume hxs, or.imp_right (assume hxt', ⟨hxs, hxt'⟩),
            exact assume hxs hxt', ⟨hxs, or.inr hxt'⟩,
          end⟩ }
  end,
by haveI enc := h.to_encodable; exact
countable_subset this (countable_image countable_encodable)

end set
