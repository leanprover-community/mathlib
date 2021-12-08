/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.pairwise
import data.set.finite

/-!
# Finite supremum independence

In this file, we define supremum independence of indexed sets. An indexed family `f : ι → α` is
sup-independent if, for all `a`, `f a` and the supremum of the rest are disjoint.

In distributive lattices, this is equivalent to being pairwise disjoint.

## TODO

`complete_lattice.independent` and `complete_lattice.set_independent` should live in this file.
-/

variables {α β ι ι' : Type*}

namespace finset
section lattice
variables [lattice α] [order_bot α]

/-- Supremum independence of finite sets. -/
def sup_indep (s : finset ι) (f : ι → α) : Prop :=
∀ ⦃t⦄, t ⊆ s → ∀ ⦃i⦄, i ∈ s → i ∉ t → disjoint (f i) (t.sup f)

variables {s t : finset ι} {f : ι → α} {i : ι}

lemma sup_indep.subset (ht : t.sup_indep f) (h : s ⊆ t) : s.sup_indep f :=
λ u hu i hi, ht (hu.trans h) (h hi)

lemma sup_indep_empty (f : ι → α) : (∅ : finset ι).sup_indep f := λ _ _ a ha, ha.elim

lemma sup_indep_singleton (i : ι) (f : ι → α) : ({i} : finset ι).sup_indep f :=
λ s hs j hji hj, begin
  suffices h : s = ∅,
  { rw [h, sup_empty],
    exact disjoint_bot_right },
  refine eq_empty_iff_forall_not_mem.2 (λ k hk, ne_of_mem_of_not_mem hk hj _),
  rw [mem_singleton.1 hji, mem_singleton.1 (hs hk)],
end

lemma sup_indep.pairwise_disjoint (hs : s.sup_indep f) : (s : set ι).pairwise_disjoint f :=
λ a ha b hb hab, sup_singleton.subst $ hs (singleton_subset_iff.2 hb) ha $ not_mem_singleton.2 hab

lemma sup_indep.le_sup_iff (hs : s.sup_indep f) (hts : t ⊆ s) (hi : i ∈ s) (hf : ∀ i, f i ≠ ⊥) :
  f i ≤ t.sup f ↔ i ∈ t :=
begin
  refine ⟨λ h, _, le_sup⟩,
  by_contra hit,
  exact hf i (disjoint_self.1 $ (hs hts hi hit).mono_right h),
end

/-- The RHS looks like the definition of `complete_lattice.independent`. -/
lemma sup_indep_iff_disjoint_erase [decidable_eq ι] :
  s.sup_indep f ↔ ∀ i ∈ s, disjoint (f i) ((s.erase i).sup f) :=
⟨λ hs i hi, hs (erase_subset _ _) hi (not_mem_erase _ _), λ hs t ht i hi hit,
  (hs i hi).mono_right (sup_mono $ λ j hj, mem_erase.2 ⟨ne_of_mem_of_not_mem hj hit, ht hj⟩)⟩

lemma sup_indep.image [decidable_eq ι] {s : finset ι'} {g : ι' → ι} (hs : s.sup_indep (f ∘ g)) :
  (s.image g).sup_indep f :=
begin
  intros t ht i hi hit,
  rw mem_image at hi,
  obtain ⟨i, hi, rfl⟩ := hi,
  haveI : decidable_eq ι' := classical.dec_eq _,
  suffices hts : t ⊆ (s.erase i).image g,
  { refine (sup_indep_iff_disjoint_erase.1 hs i hi).mono_right ((sup_mono hts).trans _),
    rw sup_image },
  rintro j hjt,
  obtain ⟨j, hj, rfl⟩ := mem_image.1 (ht hjt),
  exact mem_image_of_mem _ (mem_erase.2 ⟨ne_of_apply_ne g (ne_of_mem_of_not_mem hjt hit), hj⟩),
end

lemma sup_indep_map {s : finset ι'} {g : ι' ↪ ι} : (s.map g).sup_indep f ↔ s.sup_indep (f ∘ g) :=
begin
  refine ⟨λ hs t ht i hi hit, _, λ hs, _⟩,
  { rw ←sup_map,
    exact hs (map_subset_map.2 ht) ((mem_map' _).2 hi) (by rwa mem_map') },
  { classical,
    rw map_eq_image,
    exact hs.image }
end

lemma sup_indep.attach (hs : s.sup_indep f) : s.attach.sup_indep (f ∘ subtype.val) :=
begin
  intros t ht i _ hi,
  classical,
  rw ←finset.sup_image,
  refine hs (image_subset_iff.2 $ λ (j : {x // x ∈ s}) _, j.2) i.2 (λ hi', hi _),
  rw mem_image at hi',
  obtain ⟨j, hj, hji⟩ := hi',
  rwa subtype.ext hji at hj,
end

lemma sup_indep_subtype {p : ι → Prop} {s : finset (subtype p)} :
  s.sup_indep (f ∘ subtype.val) ↔ (s.map $ function.embedding.subtype p).sup_indep f :=
begin
  classical,
  split,
  { rintro hs t ht i hi hit,
    rw mem_map at hi,
    obtain ⟨i, hi, rfl⟩ := hi,
    suffices h : t.sup f ≤ ((s.erase i).map $ function.embedding.subtype p).sup f,
    { rw sup_map at h,
      exact (hs (erase_subset _ _) hi $ not_mem_erase _ _).mono_right h },
    refine sup_mono _,
    rw map_erase,
    exact subset_erase.2 ⟨ht, hit⟩ },
  { rintro hs t ht i hi hit,
    suffices h : disjoint (f i) ((t.map $ function.embedding.subtype p).sup f),
    { rwa sup_map at h },
    exact hs (map_subset_map.2 ht) (mem_map_of_mem _ hi) (λ h, hit ((mem_map' _).1 h)) }
end

end lattice

section distrib_lattice
variables [distrib_lattice α] [order_bot α] {s : finset ι} {f : ι → α}

lemma sup_indep_iff_pairwise_disjoint : s.sup_indep f ↔ (s : set ι).pairwise_disjoint f :=
⟨sup_indep.pairwise_disjoint, λ hs t ht i hi hit,
  disjoint_sup_right.2 $ λ j hj, hs _ hi _ (ht hj) (ne_of_mem_of_not_mem hj hit).symm⟩

alias sup_indep_iff_pairwise_disjoint ↔ finset.sup_indep.pairwise_disjoint
  set.pairwise_disjoint.sup_indep

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.sup [decidable_eq ι] {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.sup g).sup_indep f :=
begin
  simp_rw sup_indep_iff_pairwise_disjoint at ⊢ hs hg,
  rw [sup_eq_bUnion, coe_bUnion],
  exact hs.bUnion_finset hg,
end

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.bUnion [decidable_eq ι] {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.bUnion g).sup_indep f :=
by { rw ←sup_eq_bUnion, exact hs.sup hg }

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.sigma {β : ι → Type*} {s : finset ι} {g : Π i, finset (β i)} {f : sigma β → α}
  (hs : s.sup_indep $ λ i, (g i).sup $ λ b, f ⟨i, b⟩)
  (hg : ∀ i ∈ s, (g i).sup_indep $ λ b, f ⟨i, b⟩) :
  (s.sigma g).sup_indep f :=
begin
  rintro t ht ⟨i, b⟩ hi hit,
  rw disjoint_sup_right,
  rintro ⟨j, c⟩ hj,
  have hbc := (ne_of_mem_of_not_mem hj hit).symm,
  replace hj := ht hj,
  rw mem_sigma at hi hj,
  obtain rfl | hij := eq_or_ne i j,
  { exact (hg _ hj.1).pairwise_disjoint _ hi.2 _ hj.2 (sigma_mk_injective.ne_iff.1 hbc) },
  { refine (hs.pairwise_disjoint _ hi.1 _ hj.1 hij).mono _ _,
    { convert le_sup hi.2 },
    { convert le_sup hj.2 } }
end

lemma sup_indep.product {s : finset ι} {t : finset ι'} {f : ι × ι' → α}
  (hs : s.sup_indep $ λ i, t.sup $ λ i', f (i, i'))
  (ht : t.sup_indep $ λ i', s.sup $ λ i, f (i, i')) :
  (s.product t).sup_indep f :=
begin
  rintro u hu ⟨i, i'⟩ hi hiu,
  rw disjoint_sup_right,
  rintro ⟨j, j'⟩ hj,
  have hij := (ne_of_mem_of_not_mem hj hiu).symm,
  replace hj := hu hj,
  rw mem_product at hi hj,
  obtain rfl | hij := eq_or_ne i j,
  { refine (ht.pairwise_disjoint _ hi.2 _ hj.2 $ (prod.mk.inj_left _).ne_iff.1 hij).mono _ _,
    { convert le_sup hi.1 },
    { convert le_sup hj.1 } },
  { refine (hs.pairwise_disjoint _ hi.1 _ hj.1 hij).mono _ _,
    { convert le_sup hi.2 },
    { convert le_sup hj.2 } }
end

end distrib_lattice
end finset

-- TODO: Relax `complete_distrib_lattice` to `complete_lattice` once `finset.sup_indep` is general
-- enough
lemma complete_lattice.independent_iff_sup_indep [complete_distrib_lattice α] {s : finset ι}
  {f : ι → α} :
  complete_lattice.independent (f ∘ (coe : s → ι)) ↔ s.sup_indep f :=
begin
  classical,
  rw finset.sup_indep_iff_disjoint_erase,
  refine subtype.forall.trans (forall_congr $ λ a, forall_congr $ λ b, _),
  rw finset.sup_eq_supr,
  congr' 2,
  refine supr_subtype.trans _,
  congr' 1 with x,
  simp [supr_and, @supr_comm _ (x ∈ s)],
end

alias complete_lattice.independent_iff_sup_indep ↔ complete_lattice.independent.sup_indep
  finset.sup_indep.independent
