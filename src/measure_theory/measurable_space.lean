/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Measurable spaces -- σ-algberas
-/
import data.set.disjointed order.galois_connection data.set.countable
open set lattice encodable
local attribute [instance] classical.prop_decidable

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ι : Sort x}
  {s t u : set α}

structure measurable_space (α : Type u) :=
(is_measurable : set α → Prop)
(is_measurable_empty : is_measurable ∅)
(is_measurable_compl : ∀s, is_measurable s → is_measurable (- s))
(is_measurable_Union : ∀f:ℕ → set α, (∀i, is_measurable (f i)) → is_measurable (⋃i, f i))

attribute [class] measurable_space

section
variable [measurable_space α]

/-- `is_measurable s` means that `s` is measurable (in the ambient measure space on `α`) -/
def is_measurable : set α → Prop := ‹measurable_space α›.is_measurable

lemma is_measurable.empty : is_measurable (∅ : set α) :=
‹measurable_space α›.is_measurable_empty

lemma is_measurable.compl : is_measurable s → is_measurable (-s) :=
‹measurable_space α›.is_measurable_compl s

lemma is_measurable.compl_iff : is_measurable (-s) ↔ is_measurable s :=
⟨λ h, by simpa using h.compl, is_measurable.compl⟩

lemma is_measurable.univ : is_measurable (univ : set α) :=
by simpa using (@is_measurable.empty α _).compl

lemma encodable.Union_decode2 {α} [encodable β] (f : β → set α) :
  (⋃ b, f b) = ⋃ (i : ℕ) (b ∈ decode2 β i), f b :=
ext $ by simp [mem_decode2, exists_swap]

@[elab_as_eliminator] lemma encodable.Union_decode2_cases
  {α} [encodable β] {f : β → set α} {C : set α → Prop}
  (H0 : C ∅) (H1 : ∀ b, C (f b)) {n} :
  C (⋃ b ∈ decode2 β n, f b) :=
match decode2 β n with
| none := by simp; apply H0
| (some b) := by convert H1 b; simp [ext_iff]
end

lemma is_measurable.Union [encodable β] {f : β → set α} (h : ∀b, is_measurable (f b)) :
  is_measurable (⋃b, f b) :=
by rw encodable.Union_decode2; exact
‹measurable_space α›.is_measurable_Union
  (λ n, ⋃ b ∈ decode2 β n, f b)
  (λ n, encodable.Union_decode2_cases is_measurable.empty h)

lemma is_measurable.bUnion {f : β → set α} {s : set β} (hs : countable s)
  (h : ∀b∈s, is_measurable (f b)) : is_measurable (⋃b∈s, f b) :=
begin
  rw bUnion_eq_Union,
  haveI := hs.to_encodable,
  exact is_measurable.Union (by simpa using h)
end

lemma is_measurable.sUnion {s : set (set α)} (hs : countable s) (h : ∀t∈s, is_measurable t) :
  is_measurable (⋃₀ s) :=
by rw sUnion_eq_bUnion; exact is_measurable.bUnion hs h

lemma is_measurable.Union_Prop {p : Prop} {f : p → set α} (hf : ∀b, is_measurable (f b)) :
  is_measurable (⋃b, f b) :=
by by_cases p; simp [h, hf, is_measurable.empty]

lemma is_measurable.Inter [encodable β] {f : β → set α} (h : ∀b, is_measurable (f b)) :
  is_measurable (⋂b, f b) :=
is_measurable.compl_iff.1 $
by rw compl_Inter; exact is_measurable.Union (λ b, (h b).compl)

lemma is_measurable.bInter {f : β → set α} {s : set β} (hs : countable s)
  (h : ∀b∈s, is_measurable (f b)) : is_measurable (⋂b∈s, f b) :=
is_measurable.compl_iff.1 $
by rw compl_bInter; exact is_measurable.bUnion hs (λ b hb, (h b hb).compl)

lemma is_measurable.sInter {s : set (set α)} (hs : countable s) (h : ∀t∈s, is_measurable t) :
  is_measurable (⋂₀ s) :=
by rw sInter_eq_bInter; exact is_measurable.bInter hs h

lemma is_measurable.Inter_Prop {p : Prop} {f : p → set α} (hf : ∀b, is_measurable (f b)) :
  is_measurable (⋂b, f b) :=
by by_cases p; simp [h, hf, is_measurable.univ]

lemma is_measurable.union {s₁ s₂ : set α}
  (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) : is_measurable (s₁ ∪ s₂) :=
by rw union_eq_Union; exact
is_measurable.Union (bool.forall_bool.2 ⟨h₂, h₁⟩)

lemma is_measurable.inter {s₁ s₂ : set α}
  (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) : is_measurable (s₁ ∩ s₂) :=
by rw inter_eq_compl_compl_union_compl; exact
(h₁.compl.union h₂.compl).compl

lemma is_measurable.diff {s₁ s₂ : set α}
  (h₁ : is_measurable s₁) (h₂ : is_measurable s₂) : is_measurable (s₁ \ s₂) :=
h₁.inter h₂.compl

lemma is_measurable.sub {s₁ s₂ : set α} :
  is_measurable s₁ → is_measurable s₂ → is_measurable (s₁ - s₂) :=
is_measurable.diff

lemma is_measurable.disjointed {f : ℕ → set α} (h : ∀i, is_measurable (f i)) (n) :
  is_measurable (disjointed f n) :=
disjointed_induct (h n) (assume t i ht, is_measurable.diff ht $ h _)

lemma is_measurable.const (p : Prop) : is_measurable {a : α | p} :=
by by_cases p; simp [h, is_measurable.empty]; apply is_measurable.univ

end

@[extensionality] lemma measurable_space.ext :
  ∀{m₁ m₂ : measurable_space α}, (∀s:set α, m₁.is_measurable s ↔ m₂.is_measurable s) → m₁ = m₂
| ⟨s₁, _, _, _⟩ ⟨s₂, _, _, _⟩ h :=
  have s₁ = s₂, from funext $ assume x, propext $ h x,
  by subst this

namespace measurable_space

section complete_lattice

instance : partial_order (measurable_space α) :=
{ le          := λm₁ m₂, m₁.is_measurable ≤ m₂.is_measurable,
  le_refl     := assume a b, le_refl _,
  le_trans    := assume a b c, le_trans,
  le_antisymm := assume a b h₁ h₂, measurable_space.ext $ assume s, ⟨h₁ s, h₂ s⟩ }

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive generate_measurable (s : set (set α)) : set α → Prop
| basic : ∀u∈s, generate_measurable u
| empty : generate_measurable ∅
| compl : ∀s, generate_measurable s → generate_measurable (-s)
| union : ∀f:ℕ → set α, (∀n, generate_measurable (f n)) → generate_measurable (⋃i, f i)

/-- Construct the smallest measure space containing a collection of basic sets -/
def generate_from (s : set (set α)) : measurable_space α :=
{ is_measurable       := generate_measurable s,
  is_measurable_empty := generate_measurable.empty s,
  is_measurable_compl := generate_measurable.compl,
  is_measurable_Union := generate_measurable.union }

lemma is_measurable_generate_from {s : set (set α)} {t : set α} (ht : t ∈ s) :
  (generate_from s).is_measurable t :=
generate_measurable.basic t ht

lemma generate_from_le {s : set (set α)} {m : measurable_space α} (h : ∀t∈s, m.is_measurable t) :
  generate_from s ≤ m :=
assume t (ht : generate_measurable s t), ht.rec_on h
  (is_measurable_empty m)
  (assume s _ hs, is_measurable_compl m s hs)
  (assume f _ hf, is_measurable_Union m f hf)

lemma generate_from_le_iff {s : set (set α)} {m : measurable_space α} :
  generate_from s ≤ m ↔ s ⊆ {t | m.is_measurable t} :=
iff.intro
  (assume h u hu, h _ $ is_measurable_generate_from hu)
  (assume h, generate_from_le h)

protected def mk_of_closure (g : set (set α)) (hg : {t | (generate_from g).is_measurable t} = g) :
  measurable_space α :=
{ is_measurable := λs, s ∈ g,
  is_measurable_empty := hg ▸ is_measurable_empty _,
  is_measurable_compl := hg ▸ is_measurable_compl _,
  is_measurable_Union := hg ▸ is_measurable_Union _ }

lemma mk_of_closure_sets {s : set (set α)}
  {hs : {t | (generate_from s).is_measurable t} = s} :
  measurable_space.mk_of_closure s hs = generate_from s :=
measurable_space.ext $ assume t, show t ∈ s ↔ _, by rw [← hs] {occs := occurrences.pos [1] }; refl

def gi_generate_from : galois_insertion (@generate_from α) (λm, {t | @is_measurable α m t}) :=
{ gc        := assume s m, generate_from_le_iff,
  le_l_u    := assume m s, is_measurable_generate_from,
  choice    :=
    λg hg, measurable_space.mk_of_closure g $ le_antisymm hg $ generate_from_le_iff.1 $ le_refl _,
  choice_eq := assume g hg, mk_of_closure_sets }

instance : complete_lattice (measurable_space α) :=
gi_generate_from.lift_complete_lattice

instance : inhabited (measurable_space α) := ⟨⊤⟩

lemma is_measurable_bot_iff {s : set α} : @is_measurable α ⊥ s ↔ (s = ∅ ∨ s = univ) :=
let b : measurable_space α :=
{ is_measurable       := λs, s = ∅ ∨ s = univ,
  is_measurable_empty := or.inl rfl,
  is_measurable_compl := by simp [or_imp_distrib] {contextual := tt},
  is_measurable_Union := assume f hf, classical.by_cases
    (assume h : ∃i, f i = univ,
      let ⟨i, hi⟩ := h in
      or.inr $ eq_univ_of_univ_subset $ hi ▸ le_supr f i)
    (assume h : ¬ ∃i, f i = univ,
      or.inl $ eq_empty_of_subset_empty $ Union_subset $ assume i,
        (hf i).elim (by simp {contextual := tt}) (assume hi, false.elim $ h ⟨i, hi⟩)) } in
have b = ⊥, from bot_unique $ assume s hs,
  hs.elim (assume s, s.symm ▸ @is_measurable_empty _ ⊥) (assume s, s.symm ▸ @is_measurable.univ _ ⊥),
this ▸ iff.refl _

@[simp] theorem is_measurable_top {s : set α} : @is_measurable _ ⊤ s := trivial

@[simp] theorem is_measurable_inf {m₁ m₂ : measurable_space α} {s : set α} :
  @is_measurable _ (m₁ ⊓ m₂) s ↔ @is_measurable _ m₁ s ∧ @is_measurable _ m₂ s :=
iff.rfl

@[simp] theorem is_measurable_Inf {ms : set (measurable_space α)} {s : set α} :
  @is_measurable _ (Inf ms) s ↔ ∀ m ∈ ms, @is_measurable _ m s :=
show s ∈ (⋂m∈ms, {t | @is_measurable _ m t }) ↔ _, by simp

@[simp] theorem is_measurable_infi {ι} {m : ι → measurable_space α} {s : set α} :
  @is_measurable _ (infi m) s ↔ ∀ i, @is_measurable _ (m i) s :=
show s ∈ (λm, {s | @is_measurable _ m s }) (infi m) ↔ _, by rw (@gi_generate_from α).gc.u_infi; simp; refl

end complete_lattice

section functors
variables {m m₁ m₂ : measurable_space α} {m' : measurable_space β} {f : α → β} {g : β → α}

/-- The forward image of a measure space under a function. `map f m` contains the sets `s : set β`
  whose preimage under `f` is measurable. -/
protected def map (f : α → β) (m : measurable_space α) : measurable_space β :=
{ is_measurable       := λs, m.is_measurable $ f ⁻¹' s,
  is_measurable_empty := m.is_measurable_empty,
  is_measurable_compl := assume s hs, m.is_measurable_compl _ hs,
  is_measurable_Union := assume f hf, by rw [preimage_Union]; exact m.is_measurable_Union _ hf }

@[simp] lemma map_id : m.map id = m :=
measurable_space.ext $ assume s, iff.rfl

@[simp] lemma map_comp {f : α → β} {g : β → γ} : (m.map f).map g = m.map (g ∘ f) :=
measurable_space.ext $ assume s, iff.rfl

/-- The reverse image of a measure space under a function. `comap f m` contains the sets `s : set α`
  such that `s` is the `f`-preimage of a measurable set in `β`. -/
protected def comap (f : α → β) (m : measurable_space β) : measurable_space α :=
{ is_measurable       := λs, ∃s', m.is_measurable s' ∧ f ⁻¹' s' = s,
  is_measurable_empty := ⟨∅, m.is_measurable_empty, rfl⟩,
  is_measurable_compl := assume s ⟨s', h₁, h₂⟩, ⟨-s', m.is_measurable_compl _ h₁, h₂ ▸ rfl⟩,
  is_measurable_Union := assume s hs,
    let ⟨s', hs'⟩ := classical.axiom_of_choice hs in
    ⟨⋃i, s' i, m.is_measurable_Union _ (λi, (hs' i).left), by simp [hs'] ⟩ }

@[simp] lemma comap_id : m.comap id = m :=
measurable_space.ext $ assume s, ⟨assume ⟨s', hs', h⟩, h ▸ hs', assume h, ⟨s, h, rfl⟩⟩

@[simp] lemma comap_comp {f : β → α} {g : γ → β} : (m.comap f).comap g = m.comap (f ∘ g) :=
measurable_space.ext $ assume s,
  ⟨assume ⟨t, ⟨u, h, hu⟩, ht⟩, ⟨u, h, ht ▸ hu ▸ rfl⟩, assume ⟨t, h, ht⟩, ⟨f ⁻¹' t, ⟨_, h, rfl⟩, ht⟩⟩

lemma comap_le_iff_le_map {f : α → β} : m'.comap f ≤ m ↔ m' ≤ m.map f :=
⟨assume h s hs, h _ ⟨_, hs, rfl⟩, assume h s ⟨t, ht, heq⟩, heq ▸ h _ ht⟩

lemma gc_comap_map (f : α → β) :
  galois_connection (measurable_space.comap f) (measurable_space.map f) :=
assume f g, comap_le_iff_le_map

lemma map_mono (h : m₁ ≤ m₂) : m₁.map f ≤ m₂.map f := (gc_comap_map f).monotone_u h
lemma monotone_map : monotone (measurable_space.map f) := assume a b h, map_mono h
lemma comap_mono (h : m₁ ≤ m₂) : m₁.comap g ≤ m₂.comap g := (gc_comap_map g).monotone_l h
lemma monotone_comap : monotone (measurable_space.comap g) := assume a b h, comap_mono h

@[simp] lemma comap_bot : (⊥:measurable_space α).comap g = ⊥ := (gc_comap_map g).l_bot
@[simp] lemma comap_sup : (m₁ ⊔ m₂).comap g = m₁.comap g ⊔ m₂.comap g := (gc_comap_map g).l_sup
@[simp] lemma comap_supr {m : ι → measurable_space α} :(⨆i, m i).comap g = (⨆i, (m i).comap g) :=
(gc_comap_map g).l_supr

@[simp] lemma map_top : (⊤:measurable_space α).map f = ⊤ := (gc_comap_map f).u_top
@[simp] lemma map_inf : (m₁ ⊓ m₂).map f = m₁.map f ⊓ m₂.map f := (gc_comap_map f).u_inf
@[simp] lemma map_infi {m : ι → measurable_space α} : (⨅i, m i).map f = (⨅i, (m i).map f) :=
(gc_comap_map f).u_infi

lemma comap_map_le : (m.map f).comap f ≤ m := (gc_comap_map f).l_u_le _
lemma le_map_comap : m ≤ (m.comap g).map g := (gc_comap_map g).le_u_l _

end functors

lemma generate_from_le_generate_from {s t : set (set α)} (h : s ⊆ t) :
  generate_from s ≤ generate_from t :=
gi_generate_from.gc.monotone_l h

lemma generate_from_sup_generate_from {s t : set (set α)} :
  generate_from s ⊔ generate_from t = generate_from (s ∪ t) :=
(@gi_generate_from α).gc.l_sup.symm

lemma comap_generate_from {f : α → β} {s : set (set β)} :
  (generate_from s).comap f = generate_from (preimage f '' s) :=
le_antisymm
  (comap_le_iff_le_map.2 $ generate_from_le $ assume t hts,
    generate_measurable.basic _ $ mem_image_of_mem _ $ hts)
  (generate_from_le $ assume t ⟨u, hu, eq⟩, eq ▸ ⟨u, generate_measurable.basic _ hu, rfl⟩)

end measurable_space

section measurable_functions
open measurable_space

/-- A function `f` between measurable spaces is measurable if the preimage of every
  measurable set is measurable. -/
def measurable [m₁ : measurable_space α] [m₂ : measurable_space β] (f : α → β) : Prop :=
m₂ ≤ m₁.map f

lemma measurable_id [measurable_space α] : measurable (@id α) := le_refl _

lemma measurable.preimage [measurable_space α] [measurable_space β]
  {f : α → β} (hf : measurable f) {s : set β} : is_measurable s → is_measurable (f ⁻¹' s) := hf _

lemma measurable.comp [measurable_space α] [measurable_space β] [measurable_space γ]
  {g : β → γ} {f : α → β} (hg : measurable g) (hf : measurable f) : measurable (g ∘ f) :=
le_trans hg $ map_mono hf

lemma measurable_generate_from [measurable_space α] {s : set (set β)} {f : α → β}
  (h : ∀t∈s, is_measurable (f ⁻¹' t)) : @measurable _ _ _ (generate_from s) f :=
generate_from_le h

lemma measurable.if [measurable_space α] [measurable_space β]
  {p : α → Prop} {h : decidable_pred p} {f g : α → β}
  (hp : is_measurable {a | p a}) (hf : measurable f) (hg : measurable g) :
  measurable (λa, if p a then f a else g a) :=
λ s hs, show is_measurable {a | (if p a then f a else g a) ∈ s},
begin
  convert (hp.inter $ hf s hs).union (hp.compl.inter $ hg s hs),
  exact ext (λ a, by by_cases p a; simp [h, mem_def])
end

lemma measurable_const {α β} [measurable_space α] [measurable_space β] {a : α} : measurable (λb:β, a) :=
assume s hs, show is_measurable {b : β | a ∈ s}, from
  classical.by_cases
    (assume h : a ∈ s, by simp [h]; from is_measurable.univ)
    (assume h : a ∉ s, by simp [h]; from is_measurable.empty)

end measurable_functions

section constructions

instance : measurable_space empty := ⊤
instance : measurable_space unit := ⊤
instance : measurable_space bool := ⊤
instance : measurable_space ℕ := ⊤
instance : measurable_space ℤ := ⊤

lemma measurable_unit [measurable_space α] (f : unit → α) : measurable f :=
have f = (λu, f ()) := funext $ assume ⟨⟩, rfl,
by rw this; exact measurable_const

section subtype

instance {p : α → Prop} [m : measurable_space α] : measurable_space (subtype p) :=
m.comap subtype.val

lemma measurable_subtype_val [measurable_space α] [measurable_space β] {p : β → Prop}
  {f : α → subtype p} (hf : measurable f) : measurable (λa:α, (f a).val) :=
measurable.comp (measurable_space.comap_le_iff_le_map.mp (le_refl _)) hf

lemma measurable_subtype_mk [measurable_space α] [measurable_space β] {p : β → Prop}
  {f : α → subtype p} (hf : measurable (λa, (f a).val)) : measurable f :=
measurable_space.comap_le_iff_le_map.mpr $ by rw [measurable_space.map_comp]; exact hf

lemma is_measurable_subtype_image [measurable_space α] {s : set α} {t : set s}
  (hs : is_measurable s) : is_measurable t → is_measurable ((coe : s → α) '' t)
| ⟨u, (hu : is_measurable u), (eq : coe ⁻¹' u = t)⟩ :=
  begin
    rw [← eq, image_preimage_eq_inter_range, range_coe_subtype],
    exact is_measurable.inter hu hs
  end

lemma measurable_of_measurable_union_cover
  [measurable_space α] [measurable_space β]
  {f : α → β} (s t : set α) (hs : is_measurable s) (ht : is_measurable t) (h : univ ⊆ s ∪ t)
  (hc : measurable (λa:s, f a)) (hd : measurable (λa:t, f a)) :
  measurable f :=
assume u (hu : is_measurable u), show is_measurable (f ⁻¹' u), from
begin
  rw show f ⁻¹' u = coe '' (coe ⁻¹' (f ⁻¹' u) : set s) ∪ coe '' (coe ⁻¹' (f ⁻¹' u) : set t),
    by rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, range_coe_subtype, range_coe_subtype, ← inter_distrib_left, univ_subset_iff.1 h, inter_univ],
  exact is_measurable.union
    (is_measurable_subtype_image hs (hc _ hu))
    (is_measurable_subtype_image ht (hd _ hu))
end

end subtype

section prod

instance [m₁ : measurable_space α] [m₂ : measurable_space β] : measurable_space (α × β) :=
m₁.comap prod.fst ⊔ m₂.comap prod.snd

lemma measurable_fst [measurable_space α] [measurable_space β] [measurable_space γ]
  {f : α → β × γ} (hf : measurable f) : measurable (λa:α, (f a).1) :=
measurable.comp (measurable_space.comap_le_iff_le_map.mp le_sup_left) hf

lemma measurable_snd [measurable_space α] [measurable_space β] [measurable_space γ]
  {f : α → β × γ} (hf : measurable f) : measurable (λa:α, (f a).2) :=
measurable.comp (measurable_space.comap_le_iff_le_map.mp le_sup_right) hf

lemma measurable.prod [measurable_space α] [measurable_space β] [measurable_space γ]
  {f : α → β × γ} (hf₁ : measurable (λa, (f a).1)) (hf₂ : measurable (λa, (f a).2)) :
  measurable f :=
sup_le
  (by rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp]; exact hf₁)
  (by rw [measurable_space.comap_le_iff_le_map, measurable_space.map_comp]; exact hf₂)

lemma measurable_prod_mk [measurable_space α] [measurable_space β] [measurable_space γ]
  {f : α → β} {g : α → γ} (hf : measurable f) (hg : measurable g) : measurable (λa:α, (f a, g a)) :=
measurable.prod hf hg

lemma is_measurable_set_prod [measurable_space α] [measurable_space β] {s : set α} {t : set β}
  (hs : is_measurable s) (ht : is_measurable t) : is_measurable (set.prod s t) :=
is_measurable.inter (measurable_fst measurable_id _ hs) (measurable_snd measurable_id _ ht)

end prod

instance [m₁ : measurable_space α] [m₂ : measurable_space β] : measurable_space (α ⊕ β) :=
m₁.map sum.inl ⊓ m₂.map sum.inr

section sum
variables [measurable_space α] [measurable_space β] [measurable_space γ]

lemma measurable_inl : measurable (@sum.inl α β) := inf_le_left

lemma measurable_inr : measurable (@sum.inr α β) := inf_le_right

lemma measurable_sum {f : α ⊕ β → γ}
  (hl : measurable (f ∘ sum.inl)) (hr : measurable (f ∘ sum.inr)) : measurable f :=
measurable_space.comap_le_iff_le_map.1 $ le_inf
  (measurable_space.comap_le_iff_le_map.2 $ hl)
  (measurable_space.comap_le_iff_le_map.2 $ hr)

lemma measurable_sum_rec {f : α → γ} {g : β → γ}
  (hf : measurable f) (hg : measurable g) : @measurable (α ⊕ β) γ _ _ (@sum.rec α β (λ_, γ) f g) :=
measurable_sum hf hg

lemma is_measurable_inl_image [measurable_space α] [measurable_space β] {s : set α}
  (hs : is_measurable s) : is_measurable (sum.inl '' s : set (α ⊕ β)) :=
⟨show is_measurable (sum.inl ⁻¹' _), by rwa [preimage_image_eq]; exact (assume a b, sum.inl.inj),
  have sum.inr ⁻¹' (sum.inl '' s : set (α ⊕ β)) = ∅ :=
    eq_empty_of_subset_empty $ assume x ⟨y, hy, eq⟩, by contradiction,
  show is_measurable (sum.inr ⁻¹' _), by rw [this]; exact is_measurable.empty⟩

lemma is_measurable_range_inl [measurable_space α] [measurable_space β] :
  is_measurable (range sum.inl : set (α ⊕ β)) :=
by rw [← image_univ]; exact is_measurable_inl_image is_measurable.univ

lemma is_measurable_inr_image [measurable_space α] [measurable_space β] {s : set β}
  (hs : is_measurable s) : is_measurable (sum.inr '' s : set (α ⊕ β)) :=
⟨ have sum.inl ⁻¹' (sum.inr '' s : set (α ⊕ β)) = ∅ :=
    eq_empty_of_subset_empty $ assume x ⟨y, hy, eq⟩, by contradiction,
  show is_measurable (sum.inl ⁻¹' _), by rw [this]; exact is_measurable.empty,
  show is_measurable (sum.inr ⁻¹' _), by rwa [preimage_image_eq]; exact (assume a b, sum.inr.inj)⟩

lemma is_measurable_range_inr [measurable_space α] [measurable_space β] :
  is_measurable (range sum.inr : set (α ⊕ β)) :=
by rw [← image_univ]; exact is_measurable_inr_image is_measurable.univ

end sum

instance {β : α → Type v} [m : Πa, measurable_space (β a)] : measurable_space (sigma β) :=
⨅a, (m a).map (sigma.mk a)

end constructions

/-- Equivalences between measurable spaces. Main application is the simplification of measurability
statements along measurable equivalences. -/
structure measurable_equiv (α β : Type*) [measurable_space α] [measurable_space β] extends α ≃ β :=
(measurable_to_fun : measurable to_fun)
(measurable_inv_fun : measurable inv_fun)


namespace measurable_equiv

instance (α β) [measurable_space α] [measurable_space β] : has_coe_to_fun (measurable_equiv α β) :=
⟨λ_, α → β, λe, e.to_equiv⟩

lemma coe_eq {α β} [measurable_space α] [measurable_space β] (e : measurable_equiv α β) :
  (e : α → β) = e.to_equiv := rfl

def refl (α : Type*) [measurable_space α] : measurable_equiv α α :=
{ to_equiv := equiv.refl α,
  measurable_to_fun := measurable_id, measurable_inv_fun := measurable_id }

def trans [measurable_space α] [measurable_space β] [measurable_space γ]
  (ab : measurable_equiv α β) (bc : measurable_equiv β γ) :
  measurable_equiv α γ :=
{ to_equiv := ab.to_equiv.trans bc.to_equiv,
  measurable_to_fun := bc.measurable_to_fun.comp ab.measurable_to_fun,
  measurable_inv_fun := ab.measurable_inv_fun.comp bc.measurable_inv_fun }

lemma trans_to_equiv {α β} [measurable_space α] [measurable_space β] [measurable_space γ]
  (e : measurable_equiv α β) (f : measurable_equiv β γ) :
  (e.trans f).to_equiv = e.to_equiv.trans f.to_equiv := rfl

def symm [measurable_space α] [measurable_space β] (ab : measurable_equiv α β) :
  measurable_equiv β α :=
{ to_equiv := ab.to_equiv.symm,
  measurable_to_fun := ab.measurable_inv_fun,
  measurable_inv_fun := ab.measurable_to_fun }

lemma symm_to_equiv {α β} [measurable_space α] [measurable_space β] (e : measurable_equiv α β) :
  e.symm.to_equiv = e.to_equiv.symm := rfl

protected def cast {α β} [i₁ : measurable_space α] [i₂ : measurable_space β]
  (h : α = β) (hi : i₁ == i₂) : measurable_equiv α β :=
{ to_equiv := equiv.cast h,
  measurable_to_fun  := by unfreezeI; subst h; subst hi; exact measurable_id,
  measurable_inv_fun := by unfreezeI; subst h; subst hi; exact measurable_id }

protected lemma measurable {α β} [measurable_space α] [measurable_space β]
  (e : measurable_equiv α β) : measurable (e : α → β) :=
e.measurable_to_fun

protected lemma measurable_coe_iff {α β γ} [measurable_space α] [measurable_space β] [measurable_space γ]
  {f : β → γ} (e : measurable_equiv α β) : measurable (f ∘ e) ↔ measurable f :=
iff.intro
  (assume hfe,
    have measurable (f ∘ (e.symm.trans e).to_equiv) := hfe.comp e.symm.measurable,
    by rwa [trans_to_equiv, symm_to_equiv, equiv.symm_trans] at this)
  (λh, h.comp e.measurable)

def prod_congr [measurable_space α] [measurable_space β] [measurable_space γ] [measurable_space δ]
  (ab : measurable_equiv α β) (cd : measurable_equiv γ δ) :
  measurable_equiv (α × γ) (β × δ) :=
{ to_equiv := equiv.prod_congr ab.to_equiv cd.to_equiv,
  measurable_to_fun := measurable_prod_mk
    (ab.measurable_to_fun.comp (measurable_fst measurable_id))
    (cd.measurable_to_fun.comp (measurable_snd measurable_id)),
  measurable_inv_fun := measurable_prod_mk
    (ab.measurable_inv_fun.comp (measurable_fst measurable_id))
    (cd.measurable_inv_fun.comp (measurable_snd measurable_id)) }

def prod_comm [measurable_space α] [measurable_space β] : measurable_equiv (α × β) (β × α) :=
{ to_equiv := equiv.prod_comm α β,
  measurable_to_fun  := measurable_prod_mk (measurable_snd measurable_id) (measurable_fst measurable_id),
  measurable_inv_fun := measurable_prod_mk (measurable_snd measurable_id) (measurable_fst measurable_id) }

def sum_congr [measurable_space α] [measurable_space β] [measurable_space γ] [measurable_space δ]
  (ab : measurable_equiv α β) (cd : measurable_equiv γ δ) :
  measurable_equiv (α ⊕ γ) (β ⊕ δ) :=
{ to_equiv := equiv.sum_congr ab.to_equiv cd.to_equiv,
  measurable_to_fun :=
    begin
      cases ab with ab' abm, cases ab', cases cd with cd' cdm, cases cd',
      refine measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
    end,
  measurable_inv_fun :=
    begin
      cases ab with ab' _ abm, cases ab', cases cd with cd' _ cdm, cases cd',
      refine measurable_sum (measurable_inl.comp abm) (measurable_inr.comp cdm)
    end }

def set.prod [measurable_space α] [measurable_space β] (s : set α) (t : set β) :
  measurable_equiv (set.prod s t) (s × t) :=
{ to_equiv := equiv.set.prod s t,
  measurable_to_fun := measurable_prod_mk
    (measurable_subtype_mk $ measurable_fst $ measurable_subtype_val $ measurable_id)
    (measurable_subtype_mk $ measurable_snd $ measurable_subtype_val $ measurable_id),
  measurable_inv_fun := measurable_subtype_mk $ measurable_prod_mk
    (measurable_subtype_val $ measurable_fst $ measurable_id)
    (measurable_subtype_val $ measurable_snd $ measurable_id) }

def set.univ (α : Type*) [measurable_space α] : measurable_equiv (univ : set α) α :=
{ to_equiv := equiv.set.univ α,
  measurable_to_fun := measurable_subtype_val measurable_id,
  measurable_inv_fun := measurable_subtype_mk measurable_id }

def set.singleton [measurable_space α] (a:α) : measurable_equiv ({a} : set α) unit :=
{ to_equiv := equiv.set.singleton a,
  measurable_to_fun := measurable_const,
  measurable_inv_fun := measurable_subtype_mk $ show measurable (λu:unit, a), from
    measurable_const }

noncomputable def set.image [measurable_space α] [measurable_space β]
  (f : α → β) (s : set α)
  (hf : function.injective f)
  (hfm : measurable f) (hfi : ∀s, is_measurable s → is_measurable (f '' s)) :
  measurable_equiv s (f '' s) :=
{ to_equiv := equiv.set.image f s hf,
  measurable_to_fun  :=
  begin
    have : measurable (λa:s, f a) := hfm.comp (measurable_subtype_val measurable_id),
    refine measurable_subtype_mk _,
    convert this,
    ext ⟨a, h⟩, refl
  end,
  measurable_inv_fun :=
    assume t ⟨u, (hu : is_measurable u), eq⟩,
    begin
      clear_, subst eq,
      show is_measurable {x : f '' s | ((equiv.set.image f s hf).inv_fun x).val ∈ u},
      have : ∀(a ∈ s) (h : ∃a', a' ∈ s ∧ a' = a), classical.some h = a :=
        λa ha h, (classical.some_spec h).2,
      rw show {x:f '' s | ((equiv.set.image f s hf).inv_fun x).val ∈ u} = subtype.val ⁻¹' (f '' u),
        by ext ⟨b, a, hbs, rfl⟩; simp [equiv.set.image, equiv.set.image_of_inj_on, hf, this _ hbs],
      exact (measurable_subtype_val measurable_id) (f '' u) (hfi u hu)
    end }

noncomputable def set.range [measurable_space α] [measurable_space β]
  (f : α → β) (hf : function.injective f) (hfm : measurable f)
  (hfi : ∀s, is_measurable s → is_measurable (f '' s)) :
  measurable_equiv α (range f) :=
(measurable_equiv.set.univ _).symm.trans $
  (measurable_equiv.set.image f univ hf hfm hfi).trans $
  measurable_equiv.cast (by rw image_univ) (by rw image_univ)

def set.range_inl [measurable_space α] [measurable_space β] :
  measurable_equiv (range sum.inl : set (α ⊕ β)) α :=
{ to_fun    := λab, match ab with
    | ⟨sum.inl a, _⟩ := a
    | ⟨sum.inr b, p⟩ := have false, by cases p; contradiction, this.elim
    end,
  inv_fun   := λa, ⟨sum.inl a, a, rfl⟩,
  left_inv  := assume ⟨ab, a, eq⟩, by subst eq; refl,
  right_inv := assume a, rfl,
  measurable_to_fun  := assume s (hs : is_measurable s),
    begin
      refine ⟨_, is_measurable_inl_image hs, set.ext _⟩,
      rintros ⟨ab, a, rfl⟩,
      simp [set.range_inl._match_1]
    end,
  measurable_inv_fun := measurable_subtype_mk measurable_inl }

def set.range_inr [measurable_space α] [measurable_space β] :
  measurable_equiv (range sum.inr : set (α ⊕ β)) β :=
{ to_fun    := λab, match ab with
    | ⟨sum.inr b, _⟩ := b
    | ⟨sum.inl a, p⟩ := have false, by cases p; contradiction, this.elim
    end,
  inv_fun   := λb, ⟨sum.inr b, b, rfl⟩,
  left_inv  := assume ⟨ab, b, eq⟩, by subst eq; refl,
  right_inv := assume b, rfl,
  measurable_to_fun  := assume s (hs : is_measurable s),
    begin
      refine ⟨_, is_measurable_inr_image hs, set.ext _⟩,
      rintros ⟨ab, b, rfl⟩,
      simp [set.range_inr._match_1]
    end,
  measurable_inv_fun := measurable_subtype_mk measurable_inr }

def sum_prod_distrib (α β γ) [measurable_space α] [measurable_space β] [measurable_space γ] :
  measurable_equiv ((α ⊕ β) × γ) ((α × γ) ⊕ (β × γ)) :=
{ to_equiv := equiv.sum_prod_distrib α β γ,
  measurable_to_fun  :=
  begin
    refine measurable_of_measurable_union_cover
      ((range sum.inl).prod univ)
      ((range sum.inr).prod univ)
      (is_measurable_set_prod is_measurable_range_inl is_measurable.univ)
      (is_measurable_set_prod is_measurable_range_inr is_measurable.univ)
      (assume ⟨ab, c⟩ s, by cases ab; simp [set.prod_eq])
      _
      _,
    { refine (set.prod (range sum.inl) univ).symm.measurable_coe_iff.1 _,
      refine (prod_congr set.range_inl (set.univ _)).symm.measurable_coe_iff.1 _,
      dsimp [(∘)],
      convert measurable_inl,
      ext ⟨a, c⟩, refl },
    { refine (set.prod (range sum.inr) univ).symm.measurable_coe_iff.1 _,
      refine (prod_congr set.range_inr (set.univ _)).symm.measurable_coe_iff.1 _,
      dsimp [(∘)],
      convert measurable_inr,
      ext ⟨b, c⟩, refl }
  end,
  measurable_inv_fun :=
    begin
      refine measurable_sum _ _,
      { convert measurable_prod_mk
          (measurable_inl.comp (measurable_fst measurable_id)) (measurable_snd measurable_id),
        ext ⟨a, c⟩; refl },
      { convert measurable_prod_mk
          (measurable_inr.comp (measurable_fst measurable_id)) (measurable_snd measurable_id),
        ext ⟨b, c⟩; refl }
    end }

def prod_sum_distrib (α β γ) [measurable_space α] [measurable_space β] [measurable_space γ] :
  measurable_equiv (α × (β ⊕ γ)) ((α × β) ⊕ (α × γ)) :=
prod_comm.trans $ (sum_prod_distrib _ _ _).trans $ sum_congr prod_comm prod_comm

def sum_prod_sum (α β γ δ)
  [measurable_space α] [measurable_space β] [measurable_space γ] [measurable_space δ] :
  measurable_equiv ((α ⊕ β) × (γ ⊕ δ)) (((α × γ) ⊕ (α × δ)) ⊕ ((β × γ) ⊕ (β × δ))) :=
(sum_prod_distrib _ _ _).trans $ sum_congr (prod_sum_distrib _ _ _) (prod_sum_distrib _ _ _)

end measurable_equiv


namespace measurable_equiv

end measurable_equiv

namespace measurable_space

/-- Dynkin systems
The main purpose of Dynkin systems is to provide a powerful induction rule for σ-algebras generated
by intersection stable set systems.
-/
structure dynkin_system (α : Type*) :=
(has : set α → Prop)
(has_empty : has ∅)
(has_compl : ∀{a}, has a → has (-a))
(has_Union_nat : ∀{f:ℕ → set α}, pairwise (disjoint on f) → (∀i, has (f i)) → has (⋃i, f i))

theorem Union_decode2_disjoint_on
  {β} [encodable β] {f : β → set α} (hd : pairwise (disjoint on f)) :
  pairwise (disjoint on λ i, ⋃ b ∈ decode2 β i, f b) :=
begin
  rintro i j ij x ⟨h₁, h₂⟩,
  revert h₁ h₂,
  simp, intros b₁ e₁ h₁ b₂ e₂ h₂,
  refine hd _ _ _ ⟨h₁, h₂⟩,
  cases encodable.mem_decode2.1 e₁,
  cases encodable.mem_decode2.1 e₂,
  exact mt (congr_arg _) ij
end

namespace dynkin_system

@[extensionality] lemma ext :
  ∀{d₁ d₂ : dynkin_system α}, (∀s:set α, d₁.has s ↔ d₂.has s) → d₁ = d₂
| ⟨s₁, _, _, _⟩ ⟨s₂, _, _, _⟩ h :=
  have s₁ = s₂, from funext $ assume x, propext $ h x,
  by subst this

variable (d : dynkin_system α)

lemma has_compl_iff {a} : d.has (-a) ↔ d.has a :=
⟨λ h, by simpa using d.has_compl h, λ h, d.has_compl h⟩

lemma has_univ : d.has univ :=
by simpa using d.has_compl d.has_empty

theorem has_Union {β} [encodable β] {f : β → set α}
  (hd : pairwise (disjoint on f)) (h : ∀i, d.has (f i)) : d.has (⋃i, f i) :=
by rw encodable.Union_decode2; exact
d.has_Union_nat (Union_decode2_disjoint_on hd)
  (λ n, encodable.Union_decode2_cases d.has_empty h)

theorem has_union {s₁ s₂ : set α}
  (h₁ : d.has s₁) (h₂ : d.has s₂) (h : s₁ ∩ s₂ ⊆ ∅) : d.has (s₁ ∪ s₂) :=
by rw union_eq_Union; exact
d.has_Union (pairwise_disjoint_on_bool.2 h)
  (bool.forall_bool.2 ⟨h₂, h₁⟩)

lemma has_diff {s₁ s₂ : set α} (h₁ : d.has s₁) (h₂ : d.has s₂) (h : s₂ ⊆ s₁) : d.has (s₁ \ s₂) :=
d.has_compl_iff.1 begin
  simp [diff_eq, compl_inter],
  exact d.has_union (d.has_compl h₁) h₂ (λ x ⟨h₁, h₂⟩, h₁ (h h₂)),
end

instance : partial_order (dynkin_system α) :=
{ le          := λm₁ m₂, m₁.has ≤ m₂.has,
  le_refl     := assume a b, le_refl _,
  le_trans    := assume a b c, le_trans,
  le_antisymm := assume a b h₁ h₂, ext $ assume s, ⟨h₁ s, h₂ s⟩ }

def of_measurable_space (m : measurable_space α) : dynkin_system α :=
{ has       := m.is_measurable,
  has_empty := m.is_measurable_empty,
  has_compl := m.is_measurable_compl,
  has_Union_nat := assume f _ hf, m.is_measurable_Union f hf }

lemma of_measurable_space_le_of_measurable_space_iff {m₁ m₂ : measurable_space α} :
  of_measurable_space m₁ ≤ of_measurable_space m₂ ↔ m₁ ≤ m₂ :=
iff.rfl

/-- The least Dynkin system containing a collection of basic sets. -/
inductive generate_has (s : set (set α)) : set α → Prop
| basic : ∀t∈s, generate_has t
| empty : generate_has ∅
| compl : ∀{a}, generate_has a → generate_has (-a)
| Union : ∀{f:ℕ → set α}, pairwise (disjoint on f) →
    (∀i, generate_has (f i)) → generate_has (⋃i, f i)

def generate (s : set (set α)) : dynkin_system α :=
{ has := generate_has s,
  has_empty := generate_has.empty s,
  has_compl := assume a, generate_has.compl,
  has_Union_nat := assume f, generate_has.Union }

def to_measurable_space (h_inter : ∀s₁ s₂, d.has s₁ → d.has s₂ → d.has (s₁ ∩ s₂)) :=
{ measurable_space .
  is_measurable := d.has,
  is_measurable_empty := d.has_empty,
  is_measurable_compl := assume s h, d.has_compl h,
  is_measurable_Union := assume f hf,
    have ∀n, d.has (disjointed f n),
      from assume n, disjointed_induct (hf n)
        (assume t i h, h_inter _ _ h $ d.has_compl $ hf i),
    have d.has (⋃n, disjointed f n), from d.has_Union disjoint_disjointed this,
    by rwa [Union_disjointed] at this }

lemma of_measurable_space_to_measurable_space
  (h_inter : ∀s₁ s₂, d.has s₁ → d.has s₂ → d.has (s₁ ∩ s₂)) :
  of_measurable_space (d.to_measurable_space h_inter) = d :=
ext $ assume s, iff.rfl

def restrict_on {s : set α} (h : d.has s) : dynkin_system α :=
{ has       := λt, d.has (t ∩ s),
  has_empty := by simp [d.has_empty],
  has_compl := assume t hts,
    have -t ∩ s = (- (t ∩ s)) \ -s,
      from set.ext $ assume x, by by_cases x ∈ s; simp [h],
    by rw [this]; from d.has_diff (d.has_compl hts) (d.has_compl h)
      (compl_subset_compl.mpr $ inter_subset_right _ _),
  has_Union_nat := assume f hd hf,
    begin
      rw [inter_comm, inter_Union_left],
      apply d.has_Union_nat,
      { exact λ i j h x ⟨⟨_, h₁⟩, _, h₂⟩, hd i j h ⟨h₁, h₂⟩ },
      { simpa [inter_comm] using hf },
    end }

lemma generate_le {s : set (set α)} (h : ∀t∈s, d.has t) : generate s ≤ d :=
λ t ht, ht.rec_on h d.has_empty
  (assume a _ h, d.has_compl h)
  (assume f hd _ hf, d.has_Union hd hf)

lemma generate_inter {s : set (set α)}
  (hs : ∀t₁ t₂, t₁ ∈ s → t₂ ∈ s → t₁ ∩ t₂ ≠ ∅ → t₁ ∩ t₂ ∈ s) {t₁ t₂ : set α}
  (ht₁ : (generate s).has t₁) (ht₂ : (generate s).has t₂) : (generate s).has (t₁ ∩ t₂) :=
have generate s ≤ (generate s).restrict_on ht₂,
  from generate_le _ $ assume s₁ hs₁,
  have (generate s).has s₁, from generate_has.basic s₁ hs₁,
  have generate s ≤ (generate s).restrict_on this,
    from generate_le _ $ assume s₂ hs₂,
      show (generate s).has (s₂ ∩ s₁), from
        if h : s₂ ∩ s₁ = ∅ then by rw [h]; exact generate_has.empty _
        else generate_has.basic _ (hs _ _ hs₂ hs₁ h),
  have (generate s).has (t₂ ∩ s₁), from this _ ht₂,
  show (generate s).has (s₁ ∩ t₂), by rwa [inter_comm],
this _ ht₁

lemma generate_from_eq {s : set (set α)}
  (hs : ∀t₁ t₂, t₁ ∈ s → t₂ ∈ s → t₁ ∩ t₂ ≠ ∅ → t₁ ∩ t₂ ∈ s) :
generate_from s = (generate s).to_measurable_space (assume t₁ t₂, generate_inter hs) :=
le_antisymm
  (generate_from_le $ assume t ht, generate_has.basic t ht)
  (of_measurable_space_le_of_measurable_space_iff.mp $
    by rw [of_measurable_space_to_measurable_space];
    from (generate_le _ $ assume t ht, is_measurable_generate_from ht))

end dynkin_system

lemma induction_on_inter {C : set α → Prop} {s : set (set α)} {m : measurable_space α}
  (h_eq : m = generate_from s)
  (h_inter : ∀t₁ t₂, t₁ ∈ s → t₂ ∈ s → t₁ ∩ t₂ ≠ ∅ → t₁ ∩ t₂ ∈ s)
  (h_empty : C ∅) (h_basic : ∀t∈s, C t) (h_compl : ∀t, m.is_measurable t → C t → C (- t))
  (h_union : ∀f:ℕ → set α, (∀i j, i ≠ j → f i ∩ f j ⊆ ∅) →
    (∀i, m.is_measurable (f i)) → (∀i, C (f i)) → C (⋃i, f i)) :
  ∀{t}, m.is_measurable t → C t :=
have eq : m.is_measurable = dynkin_system.generate_has s,
  by rw [h_eq, dynkin_system.generate_from_eq h_inter]; refl,
assume t ht,
have dynkin_system.generate_has s t, by rwa [eq] at ht,
this.rec_on h_basic h_empty
  (assume t ht, h_compl t $ by rw [eq]; exact ht)
  (assume f hf ht, h_union f hf $ assume i, by rw [eq]; exact ht _)

end measurable_space
