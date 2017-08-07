/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of topological spaces.

Parts of the formalization is based on the books:
  N. Bourbaki: General Topology
  I. M. James: Topologies and Uniformities
A major difference is that this formalization is heavily based on the filter library.
-/
import algebra.lattice.filter
open set filter lattice classical

universes u v w

lemma compl_subset_of_compl_subset {α : Type u} {s t : set α} (h : -s ⊆ t) : -t ⊆ s :=
assume x hx, by_contradiction $ assume : x ∉ s, hx $ h $ this

lemma diff_subset_diff {α : Type u} {s₁ s₂ t₁ t₂ : set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
by finish [subset_def]

@[trans] lemma mem_of_mem_of_subset {α : Type u} {x : α} {s t : set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
h hx

structure topological_space (α : Type u) :=
(open'       : set α → Prop)
(open_univ   : open' univ)
(open_inter  : ∀s t, open' s → open' t → open' (s ∩ t))
(open_sUnion : ∀s, (∀t∈s, open' t) → open' (⋃₀ s))

attribute [class] topological_space

section topological_space

variables {α : Type u} {β : Type v} {ι : Sort w} {a a₁ a₂ : α} {s s₁ s₂ : set α}

lemma topological_space_eq {f g : topological_space α} (h' : f.open' = g.open') : f = g :=
begin
  cases f with a, cases g with b,
  have h : a = b, assumption,
  clear h',
  subst h
end

section
variables [t : topological_space α]
include t

/- open -/
def open' (s : set α) : Prop := topological_space.open' t s

@[simp]
lemma open_univ : open' (univ : set α) := topological_space.open_univ t

lemma open_inter (h₁ : open' s₁) (h₂ : open' s₂) : open' (s₁ ∩ s₂) :=
topological_space.open_inter t s₁ s₂ h₁ h₂

lemma open_sUnion {s : set (set α)} (h : ∀t ∈ s, open' t) : open' (⋃₀ s) :=
topological_space.open_sUnion t s h

end

variables [topological_space α]

lemma open_union (h₁ : open' s₁) (h₂ : open' s₂) : open' (s₁ ∪ s₂) :=
have (⋃₀ {s₁, s₂}) = (s₁ ∪ s₂), by simp,
this ▸ open_sUnion $ show ∀(t : set α), t ∈ ({s₁, s₂} : set (set α)) → open' t,
  by finish

lemma open_Union {f : ι → set α} (h : ∀i, open' (f i)) : open' (⋃i, f i) :=
open_sUnion $ assume t ⟨i, (heq : t = f i)⟩, heq.symm ▸ h i

@[simp] lemma open_empty : open' (∅ : set α) :=
have open' (⋃₀ ∅ : set α), from open_sUnion (assume a, false.elim),
by simp at this; assumption

/- closed -/
def closed (s : set α) : Prop := open' (-s)

@[simp] lemma closed_empty : closed (∅ : set α) := by simp [closed]

@[simp] lemma closed_univ : closed (univ : set α) := by simp [closed]

lemma closed_union : closed s₁ → closed s₂ → closed (s₁ ∪ s₂) :=
by simp [closed]; exact open_inter

lemma closed_sInter {s : set (set α)} : (∀t ∈ s, closed t) → closed (⋂₀ s) :=
by simp [closed, compl_sInter]; exact assume h, open_Union $ assume t, open_Union $ assume ht, h t ht

lemma closed_Inter {f : ι → set α} (h : ∀i, closed (f i)) : closed (⋂i, f i ) :=
closed_sInter $ assume t ⟨i, (heq : t = f i)⟩, heq.symm ▸ h i

@[simp] lemma open_compl_iff {s : set α} : open' (-s) ↔ closed s := iff.rfl

@[simp] lemma closed_compl_iff {s : set α} : closed (-s) ↔ open' s :=
by rw [←open_compl_iff, compl_compl]

lemma open_diff {s t : set α} (h₁ : open' s) (h₂ : closed t) : open' (s - t) :=
open_inter h₁ $ open_compl_iff.mpr h₂

lemma closed_inter (h₁ : closed s₁) (h₂ : closed s₂) : closed (s₁ ∩ s₂) :=
by rw [closed, compl_inter]; exact open_union h₁ h₂

lemma closed_Union {s : set β} {f : β → set α} (hs : finite s) :
  (∀i∈s, closed (f i)) → closed (⋃i∈s, f i) :=
begin
  induction hs,
  simp,
  simp,
  exact assume h, closed_union (h _ $ or.inl rfl) (by finish)
end

/- interior -/
def interior (s : set α) : set α := ⋃₀ {t | open' t ∧ t ⊆ s}

@[simp] lemma open_interior {s : set α} : open' (interior s) :=
open_sUnion $ assume t ⟨h₁, h₂⟩, h₁

lemma interior_subset {s : set α} : interior s ⊆ s :=
sUnion_subset $ assume t ⟨h₁, h₂⟩, h₂

lemma interior_maximal {s t : set α} (h₁ : t ⊆ s) (h₂ : open' t) : t ⊆ interior s :=
subset_sUnion_of_mem ⟨h₂, h₁⟩

lemma interior_eq_of_open {s : set α} (h : open' s) : interior s = s :=
subset.antisymm interior_subset (interior_maximal (subset.refl s) h)

lemma interior_eq_iff_open {s : set α} : interior s = s ↔ open' s :=
⟨assume h, h ▸ open_interior, interior_eq_of_open⟩

lemma subset_interior_iff_subset_of_open {s t : set α} (h₁ : open' s) :
  s ⊆ interior t ↔ s ⊆ t :=
⟨assume h, subset.trans h interior_subset, assume h₂, interior_maximal h₂ h₁⟩

lemma interior_mono {s t : set α} (h : s ⊆ t) : interior s ⊆ interior t :=
interior_maximal (subset.trans interior_subset h) open_interior

@[simp] lemma interior_empty : interior (∅ : set α) = ∅ :=
interior_eq_of_open open_empty

@[simp] lemma interior_univ : interior (univ : set α) = univ :=
interior_eq_of_open open_univ

@[simp] lemma interior_interior {s : set α} : interior (interior s) = interior s :=
interior_eq_of_open open_interior

@[simp] lemma interior_inter {s t : set α} : interior (s ∩ t) = interior s ∩ interior t :=
subset.antisymm
  (subset_inter (interior_mono $ inter_subset_left s t) (interior_mono $ inter_subset_right s t))
  (interior_maximal (inter_subset_inter interior_subset interior_subset) $ by simp [open_inter])

lemma interior_union_closed_of_interior_empty {s t : set α} (h₁ : closed s) (h₂ : interior t = ∅) :
  interior (s ∪ t) = interior s :=
have interior (s ∪ t) ⊆ s, from
  assume x ⟨u, ⟨(hu₁ : open' u), (hu₂ : u ⊆ s ∪ t)⟩, (hx₁ : x ∈ u)⟩,
  classical.by_contradiction $ assume hx₂ : x ∉ s,
    have u - s ⊆ t,
      from assume x ⟨h₁, h₂⟩, or.resolve_left (hu₂ h₁) h₂,
    have u - s ⊆ interior t,
      by simp [subset_interior_iff_subset_of_open, this, open_diff hu₁ h₁],
    have u - s ⊆ ∅,
      by rw [h₂] at this; assumption,
    this ⟨hx₁, hx₂⟩,
subset.antisymm
  (interior_maximal this open_interior)
  (interior_mono $ subset_union_left _ _)

/- closure -/
def closure (s : set α) : set α := ⋂₀ {t | closed t ∧ s ⊆ t}

@[simp] lemma closed_closure {s : set α} : closed (closure s) :=
closed_sInter $ assume t ⟨h₁, h₂⟩, h₁

lemma subset_closure {s : set α} : s ⊆ closure s :=
subset_sInter $ assume t ⟨h₁, h₂⟩, h₂

lemma closure_minimal {s t : set α} (h₁ : s ⊆ t) (h₂ : closed t) : closure s ⊆ t :=
sInter_subset_of_mem ⟨h₂, h₁⟩

lemma closure_eq_of_closed {s : set α} (h : closed s) : closure s = s :=
subset.antisymm (closure_minimal (subset.refl s) h) subset_closure

lemma closure_eq_iff_closed {s : set α} : closure s = s ↔ closed s :=
⟨assume h, h ▸ closed_closure, closure_eq_of_closed⟩

lemma closure_subset_iff_subset_of_closed {s t : set α} (h₁ : closed t) :
  closure s ⊆ t ↔ s ⊆ t :=
⟨subset.trans subset_closure, assume h, closure_minimal h h₁⟩

lemma closure_mono {s t : set α} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_minimal (subset.trans h subset_closure) closed_closure

@[simp] lemma closure_empty : closure (∅ : set α) = ∅ :=
closure_eq_of_closed closed_empty

@[simp] lemma closure_univ : closure (univ : set α) = univ :=
closure_eq_of_closed closed_univ

@[simp] lemma closure_closure {s : set α} : closure (closure s) = closure s :=
closure_eq_of_closed closed_closure

@[simp] lemma closure_union {s t : set α} : closure (s ∪ t) = closure s ∪ closure t :=
subset.antisymm
  (closure_minimal (union_subset_union subset_closure subset_closure) $ by simp [closed_union])
  (union_subset (closure_mono $ subset_union_left _ _) (closure_mono $ subset_union_right _ _))

lemma interior_subset_closure {s : set α} : interior s ⊆ closure s :=
subset.trans interior_subset subset_closure

lemma closure_eq_compl_interior_compl {s : set α} : closure s = - interior (- s) :=
begin
  simp [interior, closure],
  rw [compl_sUnion, compl_image_set_of],
  simp [neg_subset_neg_iff_subset]
end

@[simp] lemma interior_compl_eq {s : set α} : interior (- s) = - closure s :=
by simp [closure_eq_compl_interior_compl]

@[simp] lemma closure_compl_eq {s : set α} : closure (- s) = - interior s :=
by simp [closure_eq_compl_interior_compl]

/- neighbourhood filter -/
def nhds (a : α) : filter α := (⨅ s ∈ {s : set α | a ∈ s ∧ open' s}, principal s)

lemma towards_nhds {m : β → α} {f : filter β} (h : ∀s, a ∈ s → open' s → preimage m s ∈ f.sets) :
  towards m f (nhds a) :=
show map m f ≤ (⨅ s ∈ {s : set α | a ∈ s ∧ open' s}, principal s),
  from le_infi $ assume s, le_infi $ assume ⟨ha, hs⟩, le_principal_iff.mpr $ h s ha hs

lemma towards_const_nhds {a : α} {f : filter β} : towards (λb:β, a) f (nhds a) :=
towards_nhds $ assume s ha hs, univ_mem_sets' $ assume _, ha

lemma nhds_sets {a : α} : (nhds a).sets = {s | ∃t⊆s, open' t ∧ a ∈ t} :=
calc (nhds a).sets = (⋃s∈{s : set α| a ∈ s ∧ open' s}, (principal s).sets) : infi_sets_eq'
  begin
    simp,
    exact assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨_, ⟨open_inter hx₁ hy₁, ⟨hx₂, hy₂⟩⟩,
      ⟨inter_subset_left _ _, inter_subset_right _ _⟩⟩
  end
  ⟨univ, by simp⟩
  ... = {s | ∃t⊆s, open' t ∧ a ∈ t} :
    le_antisymm
      (supr_le $ assume i, supr_le $ assume ⟨hi₁, hi₂⟩ t ht, ⟨i, ht, hi₂, hi₁⟩)
      (assume t ⟨i, hi₁, hi₂, hi₃⟩, begin simp; exact ⟨i, hi₂, hi₁, hi₃⟩ end)

lemma map_nhds {a : α} {f : α → β} :
  map f (nhds a) = (⨅ s ∈ {s : set α | a ∈ s ∧ open' s}, principal (image f s)) :=
calc map f (nhds a) = (⨅ s ∈ {s : set α | a ∈ s ∧ open' s}, map f (principal s)) :
    map_binfi_eq
    begin
      simp,
      exact assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨_, ⟨open_inter hx₁ hy₁, ⟨hx₂, hy₂⟩⟩,
        ⟨inter_subset_left _ _, inter_subset_right _ _⟩⟩
    end
    ⟨univ, by simp⟩
  ... = _ : by simp

lemma mem_nhds_sets_iff {a : α} {s : set α} :
 s ∈ (nhds a).sets ↔ ∃t⊆s, open' t ∧ a ∈ t :=
by simp [nhds_sets]

lemma mem_of_nhds {a : α} {s : set α} : s ∈ (nhds a).sets → a ∈ s :=
begin simp [mem_nhds_sets_iff]; exact assume ⟨t, _, ht, hs⟩, ht hs end

lemma mem_nhds_sets {a : α} {s : set α} (hs : open' s) (ha : a ∈ s) :
 s ∈ (nhds a).sets :=
by simp [nhds_sets]; exact ⟨s, hs, subset.refl _, ha⟩

lemma return_le_nhds : return ≤ (nhds : α → filter α) :=
assume a, le_infi $ assume s, le_infi $ assume ⟨h₁, _⟩, principal_mono.mpr $ by simp [h₁]

@[simp] lemma nhds_neq_bot {a : α} : nhds a ≠ ⊥ :=
assume : nhds a = ⊥,
have return a = (⊥ : filter α),
  from lattice.bot_unique $ this ▸ return_le_nhds a,
return_neq_bot this

lemma interior_eq_nhds {s : set α} : interior s = {a | nhds a ≤ principal s} :=
set.ext $ by simp [interior, nhds_sets]

lemma open_iff_nhds {s : set α} : open' s ↔ (∀a∈s, nhds a ≤ principal s) :=
calc open' s ↔ interior s = s : by rw [interior_eq_iff_open]
  ... ↔ s ⊆ interior s : ⟨assume h, by simp [*, subset.refl], subset.antisymm interior_subset⟩
  ... ↔ (∀a∈s, nhds a ≤ principal s) : by rw [interior_eq_nhds]; refl

lemma closure_eq_nhds {s : set α} : closure s = {a | nhds a ⊓ principal s ≠ ⊥} :=
calc closure s = - interior (- s) : closure_eq_compl_interior_compl
  ... = {a | ¬ nhds a ≤ principal (-s)} : by rw [interior_eq_nhds]; refl
  ... = {a | nhds a ⊓ principal s ≠ ⊥} : set.ext $ assume a, not_congr
    (inf_eq_bot_iff_le_compl
      (show principal s ⊔ principal (-s) = ⊤, by simp [principal_univ])
      (by simp)).symm

lemma closed_iff_nhds {s : set α} : closed s ↔ (∀a, nhds a ⊓ principal s ≠ ⊥ → a ∈ s) :=
calc closed s ↔ closure s = s : by rw [closure_eq_iff_closed]
  ... ↔ closure s ⊆ s : ⟨assume h, by simp [*, subset.refl], assume h, subset.antisymm h subset_closure⟩
  ... ↔ (∀a, nhds a ⊓ principal s ≠ ⊥ → a ∈ s) : by rw [closure_eq_nhds]; refl

lemma closure_inter_open {s t : set α} (h : open' s) : s ∩ closure t ⊆ closure (s ∩ t) :=
assume a ⟨hs, ht⟩,
have s ∈ (nhds a).sets, from mem_nhds_sets h hs,
have nhds a ⊓ principal s = nhds a, from inf_of_le_left $ by simp [this],
have nhds a ⊓ principal (s ∩ t) ≠ ⊥,
  from calc nhds a ⊓ principal (s ∩ t) = nhds a ⊓ (principal s ⊓ principal t) : by simp
    ... = nhds a ⊓ principal t : by rw [←inf_assoc, this]
    ... ≠ ⊥ : by rw [closure_eq_nhds] at ht; assumption,
by rw [closure_eq_nhds]; assumption

lemma closure_diff [topological_space α] {s t : set α} : closure s - closure t ⊆ closure (s - t) :=
calc closure s \ closure t = (- closure t) ∩ closure s : by simp [diff_eq]
  ... ⊆ closure (- closure t ∩ s) : closure_inter_open $ open_compl_iff.mpr $ closed_closure
  ... = closure (s \ closure t) : by simp [diff_eq]
  ... ⊆ closure (s \ t) : closure_mono $ diff_subset_diff (subset.refl s) subset_closure

/- locally finite family [General Topology (Bourbaki, 1995)] -/
section locally_finite

def locally_finite (f : β → set α) :=
∀x:α, ∃t∈(nhds x).sets, finite {i | f i ∩ t ≠ ∅ }

lemma locally_finite_of_finite {f : β → set α} (h : finite (univ : set β)) : locally_finite f :=
assume x, ⟨univ, univ_mem_sets, finite_subset h $ by simp⟩

lemma locally_finite_subset
  {f₁ f₂ : β → set α} (hf₂ : locally_finite f₂) (hf : ∀b, f₁ b ⊆ f₂ b) : locally_finite f₁ :=
assume a,
let ⟨t, ht₁, ht₂⟩ := hf₂ a in
⟨t, ht₁, finite_subset ht₂ $ assume i hi,
  neq_bot_of_le_neq_bot hi $ inter_subset_inter (hf i) $ subset.refl _⟩

lemma closed_Union_of_locally_finite {f : β → set α}
  (h₁ : locally_finite f) (h₂ : ∀i, closed (f i)) : closed (⋃i, f i) :=
open_iff_nhds.mpr $ assume a, assume h : a ∉ (⋃i, f i),
  have ∀i, a ∈ -f i,
    from assume i hi, by simp at h; exact h ⟨i, hi⟩,
  have ∀i, - f i ∈ (nhds a).sets,
    by rw [nhds_sets]; exact assume i, ⟨- f i, subset.refl _, h₂ i, this i⟩,
  let ⟨t, h_sets, (h_fin : finite {i | f i ∩ t ≠ ∅ })⟩ := h₁ a in

  calc nhds a ≤ principal (t ∩ (⋂ i∈{i | f i ∩ t ≠ ∅ }, - f i)) :
  begin
    simp,
    apply @filter.inter_mem_sets _ (nhds a) _ _ h_sets,
    apply @filter.Inter_mem_sets _ _ (nhds a) _ _ h_fin,
    exact assume i h, this i
  end
  ... ≤ principal (- ⋃i, f i) :
  begin
    simp,
    intro x,
    simp [not_eq_empty_iff_exists],
    exact assume ⟨xt, ht⟩ i xfi, ht i ⟨x, xt, xfi⟩ xfi
  end

end locally_finite

section compact

def compact (s : set α) := ∀{f}, f ≠ ⊥ → f ≤ principal s → ∃a∈s, f ⊓ nhds a ≠ ⊥

lemma compact_adherence_nhdset {s t : set α} {f : filter α}
  (hs : compact s) (hf₂ : f ≤ principal s) (ht₁ : open' t) (ht₂ : ∀a∈s, nhds a ⊓ f ≠ ⊥ → a ∈ t) :
  t ∈ f.sets :=
classical.by_cases mem_sets_of_neq_bot $
  assume : f ⊓ principal (- t) ≠ ⊥,
  let ⟨a, ha, (hfa : f ⊓ principal (-t) ⊓ nhds a ≠ ⊥)⟩ := hs this $ inf_le_left_of_le hf₂ in
  have a ∈ t,
    from ht₂ a ha $ neq_bot_of_le_neq_bot hfa $ le_inf inf_le_right $ inf_le_left_of_le inf_le_left,
  have nhds a ⊓ principal (-t) ≠ ⊥,
    from neq_bot_of_le_neq_bot hfa $ le_inf inf_le_right $ inf_le_left_of_le inf_le_right,
  have ∀s∈(nhds a ⊓ principal (-t)).sets, s ≠ ∅,
    from forall_sets_neq_empty_iff_neq_bot.mpr this,
  have false,
    from this _ ⟨t, mem_nhds_sets ht₁ ‹a ∈ t ›, -t, subset.refl _, subset.refl _⟩ (by simp),
  by contradiction

lemma compact_iff_ultrafilter_le_nhds {s : set α} :
  compact s ↔ (∀f, ultrafilter f → f ≤ principal s → ∃a∈s, f ≤ nhds a) :=
⟨assume hs : compact s, assume f hf hfs,
  let ⟨a, ha, h⟩ := hs hf.left hfs in
  ⟨a, ha, le_of_ultrafilter hf h⟩,

  assume hs : (∀f, ultrafilter f → f ≤ principal s → ∃a∈s, f ≤ nhds a),
  assume f hf hfs,
  let ⟨a, ha, (h : ultrafilter_of f ≤ nhds a)⟩ :=
    hs (ultrafilter_of f) (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hfs) in
  have ultrafilter_of f ⊓ nhds a ≠ ⊥,
    by simp [inf_of_le_left, h]; exact (ultrafilter_ultrafilter_of hf).left,
  ⟨a, ha, neq_bot_of_le_neq_bot this (inf_le_inf ultrafilter_of_le (le_refl _))⟩⟩

lemma finite_subcover_of_compact {s : set α} {c : set (set α)}
  (hs : compact s) (hc₁ : ∀t∈c, open' t) (hc₂ : s ⊆ ⋃₀ c) : ∃c'⊆c, finite c' ∧ s ⊆ ⋃₀ c' :=
classical.by_contradiction $ assume h,
  have h : ∀{c'}, c' ⊆ c → finite c' → ¬ s ⊆ ⋃₀ c',
    from assume c' h₁ h₂ h₃, h ⟨c', h₁, h₂, h₃⟩,
  let
    f : filter α := (⨅c':{c' : set (set α) // c' ⊆ c ∧ finite c'}, principal (s - ⋃₀ c')),
    ⟨a, ha⟩ := @exists_mem_of_ne_empty α s
      (assume h', h (empty_subset _) finite.empty $ h'.symm ▸ empty_subset _)
  in
  have f ≠ ⊥, from infi_neq_bot_of_directed ⟨a⟩
    (assume ⟨c₁, hc₁, hc'₁⟩ ⟨c₂, hc₂, hc'₂⟩, ⟨⟨c₁ ∪ c₂, union_subset hc₁ hc₂, finite_union hc'₁ hc'₂⟩,
      principal_mono.mpr $ diff_right_antimono $ sUnion_mono $ subset_union_left _ _,
      principal_mono.mpr $ diff_right_antimono $ sUnion_mono $ subset_union_right _ _⟩)
    (assume ⟨c', hc'₁, hc'₂⟩, by simp [diff_neq_empty]; exact h hc'₁ hc'₂),
  have f ≤ principal s, from infi_le_of_le ⟨∅, empty_subset _, finite.empty⟩ $
    show principal (s - ⋃₀∅) ≤ principal s, by simp; exact subset.refl s,
  let
    ⟨a, ha, (h : f ⊓ nhds a ≠ ⊥)⟩ := hs ‹f ≠ ⊥› this,
    ⟨t, ht₁, (ht₂ : a ∈ t)⟩ := hc₂ ha
  in
  have f ≤ principal (-t), from infi_le_of_le ⟨{t}, by simp [ht₁], finite_insert finite.empty⟩ $
    principal_mono.mpr $ show s - ⋃₀{t} ⊆ - t, begin simp; exact assume x ⟨_, hnt⟩, hnt end,
  have closed (- t), from open_compl_iff.mp $ by simp; exact hc₁ t ht₁,
  have a ∈ - t, from closed_iff_nhds.mp this _ $ neq_bot_of_le_neq_bot h $
    le_inf inf_le_right (inf_le_left_of_le $ ‹f ≤ principal (- t)›),
  this ‹a ∈ t›

end compact

section separation

class t1_space (α : Type u) [topological_space α] :=
(t1 : ∀x, closed ({x} : set α))

lemma closed_singleton [t1_space α] {x : α} : closed ({x} : set α) :=
t1_space.t1 _ x

lemma compl_singleton_mem_nhds [t1_space α] {x y : α} (h : y ≠ x) : - {x} ∈ (nhds y).sets :=
mem_nhds_sets closed_singleton $ by simp; exact h

@[simp] lemma closure_singleton [topological_space α] [t1_space α] {a : α} :
  closure ({a} : set α) = {a} :=
closure_eq_of_closed closed_singleton

class t2_space (α : Type u) [topological_space α] :=
(t2 : ∀x y, x ≠ y → ∃u v : set α, open' u ∧ open' v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅)

lemma t2_separation [t2_space α] {x y : α} (h : x ≠ y) : 
  ∃u v : set α, open' u ∧ open' v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅ :=
t2_space.t2 _ _ _ h

instance t2_space.t1_space [topological_space α] [t2_space α] : t1_space α :=
⟨assume x,
  have ∀y, y ≠ x ↔ ∃ (i : set α), open' i ∧ y ∈ i ∧ x ∉ i,
    from assume y, ⟨assume h',
      let ⟨u, v, hu, hv, hy, hx, h⟩ := t2_separation h' in
      have x ∉ u,
        from assume : x ∈ u,
        have x ∈ u ∩ v, from ⟨this, hx⟩,
        by rwa [h] at this,
      ⟨u, hu, hy, this⟩,
      assume ⟨s, hs, hy, hx⟩ h, hx $ h ▸ hy⟩,
  have (-{x} : set α) = (⋃s∈{s : set α | x ∉ s ∧ open' s}, s),
    by apply set.ext; simp; exact this,
  show open' (- {x}),
    by rw [this]; exact (open_Union $ assume s, open_Union $ assume ⟨_, hs⟩, hs)⟩

lemma eq_of_nhds_neq_bot [ht : t2_space α] {x y : α} (h : nhds x ⊓ nhds y ≠ ⊥) : x = y :=
classical.by_contradiction $ assume : x ≠ y,
let ⟨u, v, hu, hv, hx, hy, huv⟩ := t2_space.t2 _ x y this in
have u ∩ v ∈ (nhds x ⊓ nhds y).sets,
  from inter_mem_inf_sets (mem_nhds_sets hu hx) (mem_nhds_sets hv hy),
h $ empty_in_sets_eq_bot.mp $ huv ▸ this

@[simp] lemma nhds_eq_nhds_iff {a b : α} [t2_space α] : nhds a = nhds b ↔ a = b :=
⟨assume h, eq_of_nhds_neq_bot $ by simp [h], assume h, h ▸ rfl⟩

@[simp] lemma nhds_le_nhds_iff {a b : α} [t2_space α] : nhds a ≤ nhds b ↔ a = b :=
⟨assume h, eq_of_nhds_neq_bot $ by simp [inf_of_le_left h], assume h, h ▸ le_refl _⟩

lemma towards_nhds_unique [t2_space α] {f : β → α} {l : filter β} {a b : α}
  (hl : l ≠ ⊥) (ha : towards f l (nhds a)) (hb : towards f l (nhds b)) : a = b :=
eq_of_nhds_neq_bot $ neq_bot_of_le_neq_bot (@map_ne_bot _ _ f _ hl) $ le_inf ha hb

end separation

section regularity

class regular_space (α : Type u) [topological_space α] extends t2_space α :=
(regular : ∀{s:set α} {a}, closed s → a ∉ s → ∃t, open' t ∧ s ⊆ t ∧ nhds a ⊓ principal t = ⊥)

lemma nhds_closed [regular_space α] {a : α} {s : set α} (h : s ∈ (nhds a).sets) :
  ∃t∈(nhds a).sets, t ⊆ s ∧ closed t :=
let ⟨s', h₁, h₂, h₃⟩ := mem_nhds_sets_iff.mp h in
have ∃t, open' t ∧ -s' ⊆ t ∧ nhds a ⊓ principal t = ⊥,
  from regular_space.regular (closed_compl_iff.mpr h₂) (not_not_intro h₃),
let ⟨t, ht₁, ht₂, ht₃⟩ := this in
⟨-t,
  mem_sets_of_neq_bot $ by simp; exact ht₃,
  subset.trans (compl_subset_of_compl_subset ht₂) h₁,
  closed_compl_iff.mpr ht₁⟩

end regularity

end topological_space

namespace topological_space
variables {α : Type u}

inductive generate_open (g : set (set α)) : set α → Prop
| basic  : ∀s∈g, generate_open s
| univ   : generate_open univ
| inter  : ∀s t, generate_open s → generate_open t → generate_open (s ∩ t)
| sUnion : ∀k, (∀s∈k, generate_open s) → generate_open (⋃₀ k)

def generate_from (g : set (set α)) : topological_space α :=
{ topological_space .
  open'       := generate_open g,
  open_univ   := generate_open.univ g,
  open_inter  := generate_open.inter,
  open_sUnion := generate_open.sUnion  }

lemma nhds_generate_from {g : set (set α)} {a : α} :
  @nhds α (generate_from g) a = (⨅s∈{s | a ∈ s ∧ s ∈ g}, principal s) :=
le_antisymm
  (infi_le_infi $ assume s, infi_le_infi_const $ assume ⟨as, sg⟩, ⟨as, generate_open.basic _ sg⟩)
  (le_infi $ assume s, le_infi $ assume ⟨as, hs⟩,
    have ∀s, generate_open g s → a ∈ s → (⨅s∈{s | a ∈ s ∧ s ∈ g}, principal s) ≤ principal s,
    begin
      intros s hs,
      induction hs,
      case generate_open.basic s hs
      { exact assume as, infi_le_of_le s $ infi_le _ ⟨as, hs⟩ },
      case generate_open.univ
      { rw [principal_univ],
        exact assume _, le_top },
      case generate_open.inter s t hs' ht' hs ht
      { exact assume ⟨has, hat⟩, calc _ ≤ principal s ⊓ principal t : le_inf (hs has) (ht hat)
          ... = _ : by simp },
      case generate_open.sUnion k hk' hk
      { intro h,
        simp at h,
        revert h,
        exact assume ⟨t, hat, htk⟩, calc _ ≤ principal t : hk t htk hat
          ... ≤ _ : begin simp; exact subset_sUnion_of_mem htk end },
    end,
    this s hs as)

end topological_space

section constructions

variables {α : Type u} {β : Type v}

instance : partial_order (topological_space α) :=
{ le            := λt s, t.open' ≤ s.open',
  le_antisymm   := assume t s h₁ h₂, topological_space_eq $ le_antisymm h₁ h₂,
  le_refl       := assume t, le_refl t.open',
  le_trans      := assume a b c h₁ h₂, @le_trans _ _ a.open' b.open' c.open' h₁ h₂ }

instance : has_Inf (topological_space α) :=
⟨assume (tt : set (topological_space α)), { topological_space .
  open' := λs, ∀t∈tt, topological_space.open' t s,
  open_univ   := assume t h, t.open_univ,
  open_inter  := assume s₁ s₂ h₁ h₂ t ht, t.open_inter s₁ s₂ (h₁ t ht) (h₂ t ht),
  open_sUnion := assume s h t ht, t.open_sUnion _ $ assume s' hss', h _ hss' _ ht }⟩

private lemma Inf_le {tt : set (topological_space α)} {t : topological_space α} (h : t ∈ tt) :
  Inf tt ≤ t :=
assume s hs, hs t h

private lemma le_Inf {tt : set (topological_space α)} {t : topological_space α} (h : ∀t'∈tt, t ≤ t') :
  t ≤ Inf tt :=
assume s hs t' ht', h t' ht' s hs

def topological_space.induced {α : Type u} {β : Type v} (f : α → β) (t : topological_space β) :
  topological_space α :=
{ topological_space .
  open'       := λs, ∃s', t.open' s' ∧ s = preimage f s',
  open_univ   := ⟨univ, by simp; exact t.open_univ⟩,
  open_inter  := assume s₁ s₂ ⟨s'₁, hs₁, eq₁⟩ ⟨s'₂, hs₂, eq₂⟩,
    ⟨s'₁ ∩ s'₂, by simp [eq₁, eq₂]; exact t.open_inter _ _ hs₁ hs₂⟩,
  open_sUnion := assume s h,
  begin
    simp [classical.skolem] at h,
    cases h with f hf,
    apply exists.intro (⋃(x : set α) (h : x ∈ s), f x h),
    simp [sUnion_eq_Union, (λx h, (hf x h).right.symm)],
    exact (@open_Union β _ t _ $ assume i,
      show open' (⋃h, f i h), from @open_Union β _ t _ $ assume h, (hf i h).left)
  end }

lemma closed_induced_iff [t : topological_space β] {s : set α} {f : α → β} :
  @closed α (t.induced f) s ↔ (∃t, closed t ∧ s = preimage f t) :=
⟨assume ⟨t, ht, heq⟩, ⟨-t, by simp; assumption, by simp [preimage_compl, heq.symm]⟩,
  assume ⟨t, ht, heq⟩, ⟨-t, ht, by simp [preimage_compl, heq.symm]⟩⟩

def topological_space.coinduced {α : Type u} {β : Type v} (f : α → β) (t : topological_space α) :
  topological_space β :=
{ topological_space .
  open'       := λs, t.open' (preimage f s),
  open_univ   := by simp; exact t.open_univ,
  open_inter  := assume s₁ s₂ h₁ h₂, by simp; exact t.open_inter _ _ h₁ h₂,
  open_sUnion := assume s h, by rw [preimage_sUnion]; exact (@open_Union _ _ t _ $ assume i,
    show open' (⋃ (H : i ∈ s), preimage f i), from
      @open_Union _ _ t _ $ assume hi, h i hi) }

instance : has_inf (topological_space α) :=
⟨assume t₁ t₂ : topological_space α, { topological_space .
  open'       := λs, t₁.open' s ∧ t₂.open' s,
  open_univ   := ⟨t₁.open_univ, t₂.open_univ⟩,
  open_inter  := assume s₁ s₂ ⟨h₁₁, h₁₂⟩ ⟨h₂₁, h₂₂⟩, ⟨t₁.open_inter s₁ s₂ h₁₁ h₂₁, t₂.open_inter s₁ s₂ h₁₂ h₂₂⟩,
  open_sUnion := assume s h, ⟨t₁.open_sUnion _ $ assume t ht, (h t ht).left, t₂.open_sUnion _ $ assume t ht, (h t ht).right⟩ }⟩

instance : has_top (topological_space α) :=
⟨{topological_space .
  open'       := λs, true,
  open_univ   := trivial,
  open_inter  := assume a b ha hb, trivial,
  open_sUnion := assume s h, trivial }⟩

instance {α : Type u} : complete_lattice (topological_space α) :=
{ topological_space.partial_order with
  sup           := λa b, Inf {x | a ≤ x ∧ b ≤ x},
  le_sup_left   := assume a b, le_Inf $ assume x, assume h : a ≤ x ∧ b ≤ x, h.left,
  le_sup_right  := assume a b, le_Inf $ assume x, assume h : a ≤ x ∧ b ≤ x, h.right,
  sup_le        := assume a b c h₁ h₂, Inf_le $ show c ∈ {x | a ≤ x ∧ b ≤ x}, from ⟨h₁, h₂⟩,
  inf           := (⊓),
  le_inf        := assume a b h h₁ h₂ s hs, ⟨h₁ s hs, h₂ s hs⟩,
  inf_le_left   := assume a b s ⟨h₁, h₂⟩, h₁,
  inf_le_right  := assume a b s ⟨h₁, h₂⟩, h₂,
  top           := ⊤,
  le_top        := assume a t ht, trivial,
  bot           := Inf univ,
  bot_le        := assume a, Inf_le $ mem_univ a,
  Sup           := λtt, Inf {t | ∀t'∈tt, t' ≤ t},
  le_Sup        := assume s f h, le_Inf $ assume t ht, ht _ h,
  Sup_le        := assume s f h, Inf_le $ assume t ht, h _ ht,
  Inf           := Inf,
  le_Inf        := assume s a, le_Inf,
  Inf_le        := assume s a, Inf_le }

instance inhabited_topological_space {α : Type u} : inhabited (topological_space α) :=
⟨⊤⟩

lemma t2_space_top : @t2_space α ⊤ :=
⟨assume x y hxy, ⟨{x}, {y}, trivial, trivial, mem_insert _ _, mem_insert _ _,
  eq_empty_of_forall_not_mem $ by intros z hz; simp at hz; cc⟩⟩

lemma le_of_nhds_le_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₂ x ≤ @nhds α t₁ x) :
  t₁ ≤ t₂ :=
assume s, show @open' α t₁ s → @open' α t₂ s,
  begin simp [open_iff_nhds]; exact assume hs a ha, h _ $ hs _ ha end

lemma eq_of_nhds_eq_nhds {t₁ t₂ : topological_space α} (h : ∀x, @nhds α t₂ x = @nhds α t₁ x) :
  t₁ = t₂ :=
le_antisymm
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ h x)
  (le_of_nhds_le_nhds $ assume x, le_of_eq $ (h x).symm)

instance : topological_space empty := ⊤
instance : topological_space unit := ⊤
instance : topological_space bool := ⊤
instance : topological_space ℕ := ⊤
instance : topological_space ℤ := ⊤

instance sierpinski_space : topological_space Prop :=
topological_space.generate_from {{true}}

instance {p : α → Prop} [t : topological_space α] : topological_space (subtype p) :=
topological_space.induced subtype.val t

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α × β) :=
topological_space.induced prod.fst t₁ ⊔ topological_space.induced prod.snd t₂

instance [t₁ : topological_space α] [t₂ : topological_space β] : topological_space (α ⊕ β) :=
topological_space.coinduced sum.inl t₁ ⊓ topological_space.coinduced sum.inr t₂

instance {β : α → Type v} [t₂ : Πa, topological_space (β a)] : topological_space (sigma β) :=
⨅a, topological_space.coinduced (sigma.mk a) (t₂ a)

instance topological_space_Pi {β : α → Type v} [t₂ : Πa, topological_space (β a)] : topological_space (Πa, β a) :=
⨆a, topological_space.induced (λf, f a) (t₂ a)

section
open topological_space

lemma generate_from_le {t : topological_space α} { g : set (set α) } (h : ∀s∈g, open' s) :
  generate_from g ≤ t :=
assume s (hs : generate_open g s), generate_open.rec_on hs h
  open_univ
  (assume s t _ _ hs ht, open_inter hs ht)
  (assume k _ hk, open_sUnion hk)

lemma supr_eq_generate_from {ι : Sort w} { g : ι → topological_space α } :
  supr g = generate_from (⋃i, {s | (g i).open' s}) :=
le_antisymm
  (supr_le $ assume i s open_s,
    generate_open.basic _ $ by simp; exact ⟨i, open_s⟩)
  (generate_from_le $ assume s,
    begin
      simp,
      exact assume ⟨i, open_s⟩,
        have g i ≤ supr g, from le_supr _ _,
        this s open_s
    end)

lemma sup_eq_generate_from { g₁ g₂ : topological_space α } :
  g₁ ⊔ g₂ = generate_from {s | g₁.open' s ∨ g₂.open' s} :=
le_antisymm
  (sup_le (assume s, generate_open.basic _ ∘ or.inl) (assume s, generate_open.basic _ ∘ or.inr))
  (generate_from_le $ assume s hs,
    have h₁ : g₁ ≤ g₁ ⊔ g₂, from le_sup_left,
    have h₂ : g₂ ≤ g₁ ⊔ g₂, from le_sup_right,
    or.rec_on hs (h₁ s) (h₂ s))

lemma nhds_mono {t₁ t₂ : topological_space α} {a : α} (h : t₁ ≤ t₂) : @nhds α t₂ a ≤ @nhds α t₁ a :=
infi_le_infi $ assume s, infi_le_infi2 $ assume ⟨ha, hs⟩, ⟨⟨ha, h _ hs⟩, le_refl _⟩

lemma nhds_supr {ι : Sort w} {t : ι → topological_space α} {a : α} :
  @nhds α (supr t) a = (⨅i, @nhds α (t i) a) :=
le_antisymm
  (le_infi $ assume i, nhds_mono $ le_supr _ _)
  begin
    rw [supr_eq_generate_from, nhds_generate_from],
    exact (le_infi $ assume s, le_infi $ assume ⟨hs, hi⟩,
      begin
        simp at hi, cases hi with i hi,
        exact (infi_le_of_le i $ le_principal_iff.mpr $ @mem_nhds_sets α (t i) _ _ hi hs)
      end)
  end

end

end constructions

section limit
variables {α : Type u} [inhabited α] [topological_space α]
open classical

noncomputable def lim (f : filter α) : α := epsilon $ λa, f ≤ nhds a

lemma lim_spec {f : filter α} (h : ∃a, f ≤ nhds a) : f ≤ nhds (lim f) := epsilon_spec h

variables [t2_space α] {f : filter α}

lemma lim_eq {a : α} (hf : f ≠ ⊥) (h : f ≤ nhds a) : lim f = a :=
eq_of_nhds_neq_bot $ neq_bot_of_le_neq_bot hf $ le_inf (lim_spec ⟨_, h⟩) h

@[simp] lemma lim_nhds_eq {a : α} : lim (nhds a) = a :=
lim_eq nhds_neq_bot (le_refl _)

@[simp] lemma lim_nhds_eq_of_closure {a : α} {s : set α} (h : a ∈ closure s) :
  lim (nhds a ⊓ principal s) = a :=
lim_eq begin rw [closure_eq_nhds] at h, exact h end inf_le_left

end limit
