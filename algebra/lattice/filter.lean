/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of filters on sets.
-/
import algebra.lattice.complete_lattice data.set algebra.lattice.zorn
open lattice set

universes u v w x y

open set classical
local attribute [instance] decidable_inhabited
local attribute [instance] prop_decidable

lemma classical.cases {p : Prop → Prop} (h1 : p true) (h2 : p false) : ∀a, p a :=
assume a, classical.cases_on a h1 h2

@[simp] lemma false_neq_true : false ≠ true :=
begin intro h, rw [h], trivial end

section applicative
variables {f : Type u → Type v} [applicative f] {α β : Type u}

lemma pure_seq_eq_map : ∀ {α β : Type u} (g : α → β) (x : f α), pure g <*> x = g <$> x :=
@applicative.pure_seq_eq_map f _

end applicative

section monad
variables {α β γ : Type u} {m : Type u → Type v} [monad m]

lemma map_bind (x : m α) {g : α → m β} {f : β → γ} : f <$> (x >>= g) = (x >>= λa, f <$> g a) :=
by simp [monad.bind_assoc, (∘), (monad.bind_pure_comp_eq_map _ _ _).symm]

lemma seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} : (f <$> x) >>= g = (x >>= g ∘ f) :=
show bind (f <$> x) g = bind x (g ∘ f),
by rw [←monad.bind_pure_comp_eq_map, monad.bind_assoc]; simp [monad.pure_bind]

lemma seq_eq_bind_map {x : m α} {f : m (α → β)} : f <*> x = (f >>= (<$> x)) :=
(monad.bind_map_eq_seq m f x).symm

lemma bind_assoc : ∀ {α β γ : Type u} (x : m α) (f : α → m β) (g : β → m γ),
  x >>= f >>= g = x >>= λ x, f x >>= g :=
@monad.bind_assoc m _

end monad

section prod
variables {α : Type u} {β : Type v}

-- copied from parser
@[simp] lemma prod.mk.eta : ∀{p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

def prod.swap : (α×β) → (β×α) := λp, (p.2, p.1)

@[simp] lemma prod.swap_swap : ∀x:α×β, prod.swap (prod.swap x) = x
| ⟨a, b⟩ := rfl

@[simp] lemma prod.fst_swap {p : α×β} : (prod.swap p).1 = p.2 := rfl

@[simp] lemma prod.snd_swap {p : α×β} : (prod.swap p).2 = p.1 := rfl

@[simp] lemma prod.swap_prod_mk {a : α} {b : β} : prod.swap (a, b) = (b, a) := rfl

@[simp] lemma prod.swap_swap_eq : prod.swap ∘ prod.swap = @id (α × β) :=
funext $ prod.swap_swap

end prod

namespace lattice
variables {α : Type u} {ι : Sort v} [complete_lattice α]

lemma Inf_eq_finite_sets {s : set α} :
  Inf s = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t) :=
le_antisymm
  (le_infi $ assume t, le_infi $ assume ⟨_, h⟩, Inf_le_Inf h)
  (le_Inf $ assume b h, infi_le_of_le {b} $ infi_le_of_le (by simp [h]) $ Inf_le $ by simp)

end lattice

instance : monad set :=
{ monad .
  pure       := λ(α : Type u) a, {a},
  bind       := λ(α β : Type u) s f, ⋃i∈s, f i,
  map        := λ(α β : Type u), set.image,
  pure_bind  := assume α β x f, by simp,
  bind_assoc := assume α β γ s f g, set.ext $ assume a,
    by simp; exact ⟨assume ⟨b, ag, a, as, bf⟩, ⟨a, as, b, bf, ag⟩,
      assume ⟨a, as, b, bf, ag⟩, ⟨b, ag, a, as, bf⟩⟩,
  id_map     := assume α, functor.id_map,
  bind_pure_comp_eq_map := assume α β f s, set.ext $ by simp [set.image, eq_comm] }

namespace set

section
variables {α β : Type u}

@[simp] lemma bind_def (s : set α) (f : α → set β) : s >>= f = ⋃i∈s, f i := rfl

lemma ne_empty_iff_exists_mem {s : set α} : s ≠ ∅ ↔ ∃ x, x ∈ s :=
⟨exists_mem_of_ne_empty, assume ⟨x, (hx : x ∈ s)⟩ h, by rw [h] at hx; assumption⟩

lemma fmap_eq_image {f : α → β} {s : set α} : f <$> s = f '' s := rfl

lemma mem_seq_iff {f : set (α → β)} {s : set α} {b : β} :
  b ∈ (f <*> s) ↔ (∃(f' : α → β), ∃a ∈ s, f' ∈ f ∧ b = f' a) :=
begin
  simp [seq_eq_bind_map],
  apply exists_congr,
  intro f',
  exact ⟨assume ⟨hf', a, ha, h_eq⟩, ⟨a, h_eq.symm, ha, hf'⟩,
    assume ⟨a, h_eq, ha, hf'⟩, ⟨hf', a, ha, h_eq.symm⟩⟩
end

lemma univ_eq_true_false : univ = ({true, false} : set Prop) :=
eq.symm $ top_unique $ classical.cases (by simp) (by simp)

end

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ι : Sort y}

lemma not_eq_empty_iff_exists {s : set α} : ¬ (s = ∅) ↔ ∃ x, x ∈ s :=
ne_empty_iff_exists_mem

lemma image_inter {f : α → β} {s t : set α} (h : ∀ x y, f x = f y → x = y) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
subset.antisymm
  (assume b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩,
    have a₂ = a₁, from h a₂ a₁ $ h₁.symm ▸ h₂.symm ▸ rfl,
    ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩)
  (subset_inter (mono_image $ inter_subset_left _ _) (mono_image $ inter_subset_right _ _))

lemma image_Union {f : α → β} {s : ι → set α} : f '' (⋃ i, s i) = (⋃i, f '' s i) :=
begin
  apply set.ext, intro x,
  simp [image],
  exact ⟨assume ⟨a, h, i, hi⟩, ⟨i, a, h, hi⟩, assume ⟨i, a, h, hi⟩, ⟨a, h, i, hi⟩⟩
end

@[simp] lemma image_singleton {f : α → β} {a : α} : f '' {a} = {f a} :=
begin
  apply set.ext, intro x,
  simp [image],
  exact ⟨assume ⟨a', ha', hx⟩, hx ▸ ha' ▸ rfl, assume h, ⟨a, rfl, h.symm⟩⟩
end

protected def prod (s : set α) (t : set β) : set (α × β) :=
{p | p.1 ∈ s ∧ p.2 ∈ t}

lemma mem_prod_eq {s : set α} {t : set β} {p : α × β} :
  p ∈ set.prod s t = (p.1 ∈ s ∧ p.2 ∈ t) := rfl

theorem prod_preimage_eq {s : set α} {t : set β} {f : γ → α} {g : δ → β} :
  set.prod (preimage f s) (preimage g t) = preimage (λp, (f p.1, g p.2)) (set.prod s t) := rfl

lemma prod_mono {s₁ s₂ : set α} {t₁ t₂ : set β} (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
  set.prod s₁ t₁ ⊆ set.prod s₂ t₂ :=
assume x ⟨h₁, h₂⟩, ⟨hs h₁, ht h₂⟩

lemma prod_inter_prod {s₁ s₂ : set α} {t₁ t₂ : set β} :
  set.prod s₁ t₁ ∩ set.prod s₂ t₂ = set.prod (s₁ ∩ s₂) (t₁ ∩ t₂) :=
subset.antisymm
  (assume ⟨a, b⟩ ⟨⟨ha₁, hb₁⟩, ⟨ha₂, hb₂⟩⟩, ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩)
  (subset_inter
    (prod_mono (inter_subset_left _ _) (inter_subset_left _ _))
    (prod_mono (inter_subset_right _ _) (inter_subset_right _ _)))

theorem monotone_prod [preorder α] {f : α → set β} {g : α → set γ}
  (hf : monotone f) (hg : monotone g) : monotone (λx, set.prod (f x) (g x)) :=
assume a b h, prod_mono (hf h) (hg h)

lemma image_swap_prod {s : set α} {t : set β} :
  image (λp:β×α, (p.2, p.1)) (set.prod t s) = set.prod s t :=
set.ext $ assume ⟨a, b⟩, by simp [mem_image_eq, set.prod]; exact
⟨ assume ⟨b', a', h_a, h_b, h⟩, by rw [h_a, h_b] at h; assumption,
  assume ⟨ha, hb⟩, ⟨b, a, rfl, rfl, ⟨ha, hb⟩⟩⟩

lemma prod_image_image_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {s₁ : set α₁} {s₂ : set α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  set.prod (image m₁ s₁) (image m₂ s₂) = image (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) (set.prod s₁ s₂) :=
set.ext $ assume ⟨b₁, b₂⟩,
  ⟨assume ⟨⟨a₁, ha₁, (eq₁ : m₁ a₁ = b₁)⟩, ⟨a₂, ha₂, (eq₂ : m₂ a₂ = b₂)⟩⟩,
    mem_image
      (show (a₁, a₂) ∈ set.prod s₁ s₂, from ⟨ha₁, ha₂⟩)
      (by simp [eq₁, eq₂]),
    assume ⟨⟨a₁, a₂⟩, ⟨ha₁, ha₂⟩, eq⟩, eq ▸ ⟨mem_image_of_mem m₁ ha₁, mem_image_of_mem m₂ ha₂⟩⟩

@[simp] lemma prod_singleton_singleton {a : α} {b : β} :
  set.prod {a} {b} = ({(a, b)} : set (α×β)) :=
set.ext $ assume ⟨a', b'⟩, by simp [set.prod]

lemma prod_neq_empty_iff {s : set α} {t : set β} :
  set.prod s t ≠ ∅ ↔ (s ≠ ∅ ∧ t ≠ ∅) :=
begin
  rw [ne_empty_iff_exists_mem, ne_empty_iff_exists_mem, ne_empty_iff_exists_mem,
    prod.exists],
  exact ⟨assume ⟨a, b, ha, hb⟩, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩,
    assume ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨a, b, ha, hb⟩⟩
end

@[simp] lemma prod_mk_mem_set_prod_eq {a : α} {b : β} {s : set α} {t : set β} :
  (a, b) ∈ set.prod s t = (a ∈ s ∧ b ∈ t) := rfl

theorem monotone_inter [preorder β] {f g : β → set α}
  (hf : monotone f) (hg : monotone g) : monotone (λx, (f x) ∩ (g x)) :=
assume a b h x ⟨h₁, h₂⟩, ⟨hf h h₁, hg h h₂⟩

@[simp] theorem preimage_set_of_eq {p : α → Prop} {f : β → α} :
  preimage f {a | p a} = {a | p (f a)} := rfl

@[simp] lemma set_of_mem_eq {s : set α} : {x | x ∈ s} = s := rfl

lemma mem_image_iff_of_inverse (f : α → β) (g : β → α) {b : β} {s : set α}
  (h₁ : ∀a, g (f a) = a ) (h₂ : ∀b, f (g b) = b ) : b ∈ f '' s ↔ g b ∈ s :=
⟨assume ⟨a, ha, fa_eq⟩, fa_eq ▸ (h₁ a).symm ▸ ha,
  assume h, ⟨g b, h, h₂ b⟩⟩

theorem image_eq_preimage_of_inverse (f : α → β) (g : β → α)
  (h₁ : ∀a, g (f a) = a ) (h₂ : ∀b, f (g b) = b ) : image f = preimage g :=
funext $ assume s, set.ext $ assume b, mem_image_iff_of_inverse f g h₁ h₂

theorem image_swap_eq_preimage_swap : image (@prod.swap α β) = preimage prod.swap :=
image_eq_preimage_of_inverse (@prod.swap α β) (@prod.swap β α)
  begin simp; intros; trivial end
  begin simp; intros; trivial end

theorem monotone_set_of [preorder α] {p : α → β → Prop}
  (hp : ∀b, monotone (λa, p a b)) : monotone (λa, {b | p a b}) :=
assume a a' h b, hp b h

lemma diff_right_antimono {s t u : set α} (h : t ⊆ u) : s - u ⊆ s - t :=
assume x ⟨hs, hnx⟩, ⟨hs, assume hx, hnx $ h hx⟩

end set

section
variables {α : Type u} {ι : Sort v}

lemma sUnion_mono {s t : set (set α)} (h : s ⊆ t) : (⋃₀ s) ⊆ (⋃₀ t) :=
sUnion_subset $ assume t' ht', subset_sUnion_of_mem $ h ht'

lemma Union_subset_Union {s t : ι → set α} (h : ∀i, s i ⊆ t i) : (⋃i, s i) ⊆ (⋃i, t i) :=
@supr_le_supr (set α) ι _ s t h

lemma Union_subset_Union2 {ι₂ : Sort x} {s : ι → set α} {t : ι₂ → set α} (h : ∀i, ∃j, s i ⊆ t j) :
  (⋃i, s i) ⊆ (⋃i, t i) :=
@supr_le_supr2 (set α) ι ι₂ _ s t h

lemma Union_subset_Union_const {ι₂ : Sort x} {s : set α} (h : ι → ι₂) : (⋃ i:ι, s) ⊆ (⋃ j:ι₂, s) :=
@supr_le_supr_const (set α) ι ι₂ _ s h

lemma diff_neq_empty {s t : set α} : s - t = ∅ ↔ s ⊆ t :=
⟨assume h x hx, classical.by_contradiction $ assume : x ∉ t, show x ∈ (∅ : set α), from h ▸ ⟨hx, this⟩,
  assume h, bot_unique $ assume x ⟨hx, hnx⟩, hnx $ h hx⟩

@[simp] lemma diff_empty {s : set α} : s - ∅ = s :=
set.ext $ assume x, ⟨assume ⟨hx, _⟩, hx, assume h, ⟨h, not_false⟩⟩

end

-- should be handled by implies_true_iff
@[simp] lemma implies_implies_true_iff {α : Sort u} {β : Sort v} : (α → β → true) ↔ true :=
⟨assume _, trivial, assume _ _ _ , trivial⟩

@[simp] lemma not_not_mem_iff {α : Type u} {a : α} {s : set α} : ¬ (a ∉ s) ↔ a ∈ s :=
not_not_iff

@[simp] lemma singleton_neq_emptyset {α : Type u} {a : α} : {a} ≠ (∅ : set α) :=
assume h,
have a ∉ ({a} : set α),
  by simp [h],
this $ mem_singleton a

lemma eq_of_sup_eq_inf_eq {α : Type u} [distrib_lattice α] {a b c : α}
  (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
le_antisymm
  (calc b ≤ (c ⊓ a) ⊔ b     : le_sup_right
    ... = (c ⊔ b) ⊓ (a ⊔ b) : sup_inf_right
    ... = c ⊔ (c ⊓ a)       : by rw [←h₁, sup_inf_left, ←h₂]; simp [sup_comm]
    ... = c                 : sup_inf_self)
  (calc c ≤ (b ⊓ a) ⊔ c     : le_sup_right
    ... = (b ⊔ c) ⊓ (a ⊔ c) : sup_inf_right
    ... = b ⊔ (b ⊓ a)       : by rw [h₁, sup_inf_left, h₂]; simp [sup_comm]
    ... = b                 : sup_inf_self)

lemma inf_eq_bot_iff_le_compl {α : Type u} [bounded_distrib_lattice α] {a b c : α}
  (h₁ : b ⊔ c = ⊤) (h₂ : b ⊓ c = ⊥) : a ⊓ b = ⊥ ↔ a ≤ c :=
⟨assume : a ⊓ b = ⊥,
  calc a ≤ a ⊓ (b ⊔ c) : by simp [h₁]
    ... = (a ⊓ b) ⊔ (a ⊓ c) : by simp [inf_sup_left]
    ... ≤ c : by simp [this, inf_le_right],
  assume : a ≤ c,
  bot_unique $
    calc a ⊓ b ≤ b ⊓ c : by rw [inf_comm]; exact inf_le_inf (le_refl _) this
      ... = ⊥ : h₂⟩

lemma compl_image_set_of {α : Type u} {p : set α → Prop} :
  compl '' {x | p x} = {x | p (- x)} :=
set.ext $ assume x, ⟨assume ⟨y, (hy : p y), (h_eq : -y = x)⟩,
  show p (- x), by rw [←h_eq, lattice.neg_neg]; assumption,
  assume h : p (-x), ⟨_, h, lattice.neg_neg⟩⟩

lemma neg_subset_neg_iff_subset {α : Type u} {x y : set α} : - y ⊆ - x ↔ x ⊆ y :=
@neg_le_neg_iff_le (set α) _ _ _

lemma sUnion_eq_Union {α : Type u} {s : set (set α)} :
  (⋃₀ s) = (⋃ (i : set α) (h : i ∈ s), i) :=
set.ext $ by simp

lemma not_or_iff_implies {a b : Prop} : (¬ a ∨ b) ↔ (a → b) :=
⟨assume h ha, h.neg_resolve_left ha, not_or_of_implies⟩

section order
variables {α : Type u} (r : α → α → Prop)
local infix `≼` : 50 := r

def directed {ι : Sort v} (f : ι → α) := ∀x, ∀y, ∃z, f z ≼ f x ∧ f z ≼ f y
def directed_on (s : set α) := ∀x ∈ s, ∀y ∈ s, ∃z ∈ s, z ≼ x ∧ z ≼ y

lemma directed_on_Union {r} {ι : Sort v} {f : ι → set α} (hd : directed (⊇) f)
  (h : ∀x, directed_on r (f x)) : directed_on r (⋃x, f x) :=
by simp [directed_on]; exact
  assume a₁ ⟨b₁, fb₁⟩ a₂ ⟨b₂, fb₂⟩,
  let
    ⟨z, zb₁, zb₂⟩ := hd b₁ b₂,
    ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
  in
    ⟨x, xa₁, xa₂, z, xf⟩

def upwards (s : set α) := ∀{x y}, x ∈ s → x ≼ y → y ∈ s

end order

theorem directed_of_chain {α : Type u} {β : Type v} [preorder β] {f : α → β} {c : set α}
  (h : @zorn.chain α (λa b, f b ≤ f a) c) :
  directed (≤) (λx:{a:α // a ∈ c}, f (x.val)) :=
assume ⟨a, ha⟩ ⟨b, hb⟩, classical.by_cases
  (assume : a = b, begin simp [this]; exact ⟨⟨b, hb⟩, le_refl _⟩ end)
  (assume : a ≠ b,
    have f b ≤ f a ∨ f a ≤ f b, from h a ha b hb this,
    or.elim this
      (assume : f b ≤ f a, ⟨⟨b, hb⟩, this, le_refl _⟩)
      (assume : f a ≤ f b, ⟨⟨a, ha⟩, le_refl _, this⟩))

structure filter (α : Type u) :=
(sets           : set (set α))
(inhabited      : ∃x, x ∈ sets)
(upwards_sets   : upwards (⊆) sets)
(directed_sets  : directed_on (⊆) sets)

namespace filter
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

lemma filter_eq : ∀{f g : filter α}, f.sets = g.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl

lemma univ_mem_sets' {f : filter α} {s : set α} (h : ∀ a, a ∈ s): s ∈ f.sets :=
let ⟨x, x_in_s⟩ := f.inhabited in
f.upwards_sets x_in_s (assume x _, h x)

lemma univ_mem_sets {f : filter α} : univ ∈ f.sets :=
univ_mem_sets' mem_univ

lemma inter_mem_sets {f : filter α} {x y : set α} (hx : x ∈ f.sets) (hy : y ∈ f.sets) :
  x ∩ y ∈ f.sets :=
let ⟨z, ⟨z_in_s, z_le_x, z_le_y⟩⟩ := f.directed_sets _ hx _ hy in
f.upwards_sets z_in_s (subset_inter z_le_x z_le_y)

lemma Inter_mem_sets {f : filter α} {s : β → set α}
  {is : set β} (hf : finite is) (hs : ∀i∈is, s i ∈ f.sets) : (⋂i∈is, s i) ∈ f.sets :=
begin /- equation compiler complains that this is requires well-founded recursion -/
  induction hf with i is _ hf hi,
  { simp [univ_mem_sets] },
  begin
    simp,
    apply inter_mem_sets,
    apply hs i,
    simp,
    exact (hi $ assume a ha, hs _ $ by simp [ha])
  end
end

lemma exists_sets_subset_iff {f : filter α} {x : set α} :
  (∃y∈f.sets, y ⊆ x) ↔ x ∈ f.sets :=
⟨assume ⟨y, hy, yx⟩, f.upwards_sets hy yx,
  assume hx, ⟨x, hx, subset.refl _⟩⟩

lemma monotone_mem_sets {f : filter α} : monotone (λs, s ∈ f.sets) :=
assume s t hst h, f.upwards_sets h hst

def principal (s : set α) : filter α :=
{ filter .
  sets          := {t | s ⊆ t},
  inhabited     := ⟨s, subset.refl _⟩,
  upwards_sets  := assume x y hx hy, subset.trans hx hy,
  directed_sets := assume x hx y hy, ⟨s, subset.refl _, hx, hy⟩ }

def join (f : filter (filter α)) : filter α :=
{ filter .
  sets          := {s | {t | s ∈ filter.sets t} ∈ f.sets},
  inhabited     := ⟨univ, by simp [univ_mem_sets]; exact univ_mem_sets⟩,
  upwards_sets  := assume x y hx xy, f.upwards_sets hx $ assume a h, a.upwards_sets h xy,
  directed_sets := assume x hx y hy, ⟨x ∩ y,
    f.upwards_sets (inter_mem_sets hx hy) $ assume z ⟨h₁, h₂⟩, inter_mem_sets h₁ h₂,
    inter_subset_left _ _,  inter_subset_right _ _⟩ }

def map (m : α → β) (f : filter α) : filter β :=
{ filter .
  sets          := preimage (preimage m) f.sets,
  inhabited     := ⟨univ, univ_mem_sets⟩,
  upwards_sets  := assume s t hs st, f.upwards_sets hs (assume x h, st h),
  directed_sets := assume s hs t ht, ⟨s ∩ t, inter_mem_sets hs ht,
    inter_subset_left _ _,  inter_subset_right _ _⟩ }

def vmap (m : α → β) (f : filter β) : filter α :=
{ filter .
  sets          := { s | ∃t∈f.sets, preimage m t ⊆ s },
  inhabited     := ⟨univ, univ, univ_mem_sets, by simp⟩,
  upwards_sets  := assume a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', subset.trans ma'a ab⟩,
  directed_sets := assume a ⟨a', ha₁, ha₂⟩ b ⟨b', hb₁, hb₂⟩,
    ⟨preimage m (a' ∩ b'),
      ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, subset.refl _⟩,
      subset.trans (preimage_mono $ inter_subset_left _ _) ha₂,
      subset.trans (preimage_mono $ inter_subset_right _ _) hb₂⟩ }

protected def sup (f g : filter α) : filter α :=
{ filter .
  sets          := f.sets ∩ g.sets,
  inhabited     := ⟨univ, by simp [univ_mem_sets]; exact univ_mem_sets⟩,
  upwards_sets  := assume x y hx xy,
    and.imp (assume h, f.upwards_sets h xy) (assume h, g.upwards_sets h xy) hx,
  directed_sets := assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨x ∩ y,
    ⟨inter_mem_sets hx₁ hy₁, inter_mem_sets hx₂ hy₂⟩,
    inter_subset_left _ _,  inter_subset_right _ _⟩ }

protected def inf (f g : filter α) :=
{ filter .
  sets          := {s | ∃ a ∈ f.sets, ∃ b ∈ g.sets, a ∩ b ⊆ s },
  inhabited     := ⟨univ, univ, univ_mem_sets, univ, univ_mem_sets, subset_univ _⟩,
  upwards_sets  := assume x y ⟨a, ha, b, hb, h⟩ xy,
    ⟨a, ha, b, hb, subset.trans h xy⟩,
  directed_sets := assume x ⟨a₁, ha₁, b₁, hb₁, h₁⟩ y ⟨a₂, ha₂, b₂, hb₂, h₂⟩,
    ⟨x ∩ y,
      ⟨_, inter_mem_sets ha₁ ha₂, _, inter_mem_sets hb₁ hb₂,
        calc (a₁ ⊓ a₂) ⊓ (b₁ ⊓ b₂) = (a₁ ⊓ b₁) ⊓ (a₂ ⊓ b₂) : by ac_refl
                                ... ≤ x ∩ y : inf_le_inf h₁ h₂ ⟩,
      inter_subset_left _ _, inter_subset_right _ _⟩ }

def cofinite : filter α :=
{ filter .
  sets          := {s | finite (- s)},
  inhabited     := ⟨univ, by simp⟩,
  upwards_sets  := assume s t, assume hs : finite (-s), assume st: s ⊆ t,
    finite_subset hs $ @lattice.neg_le_neg (set α) _ _ _ st,
  directed_sets := assume s, assume hs : finite (-s), assume t, assume ht : finite (-t),
    ⟨s ∩ t, by simp [compl_inter, finite_union, ht, hs],
      inter_subset_left _ _, inter_subset_right _ _⟩ }

instance partial_order_filter : partial_order (filter α) :=
{ partial_order .
  le            := λf g, g.sets ⊆ f.sets,
  le_antisymm   := assume a b h₁ h₂, filter_eq $ subset.antisymm h₂ h₁,
  le_refl       := assume a, subset.refl _,
  le_trans      := assume a b c h₁ h₂, subset.trans h₂ h₁ }

instance : has_Sup (filter α) := ⟨join ∘ principal⟩

instance inhabited' : _root_.inhabited (filter α) :=
⟨principal ∅⟩

protected lemma le_Sup {s : set (filter α)} {f : filter α} : f ∈ s → f ≤ Sup s :=
assume f_in_s t' h, h f_in_s

protected lemma Sup_le {s : set (filter α)} {f : filter α} : (∀g∈s, g ≤ f) → Sup s ≤ f :=
assume h a ha g hg, h g hg ha

@[simp] lemma mem_join_sets {s : set α} {f : filter (filter α)} :
  s ∈ (join f).sets = ({t | s ∈ filter.sets t} ∈ f.sets) := rfl

@[simp] lemma mem_principal_sets {s t : set α} : s ∈ (principal t).sets = (t ⊆ s) := rfl

@[simp] lemma le_principal_iff {s : set α} {f : filter α} : f ≤ principal s ↔ s ∈ f.sets :=
show (∀{t}, s ⊆ t → t ∈ f.sets) ↔ s ∈ f.sets,
  from ⟨assume h, h (subset.refl s), assume hs t ht, f.upwards_sets hs ht⟩

lemma principal_mono {s t : set α} : principal s ≤ principal t ↔ s ⊆ t :=
by simp

lemma monotone_principal : monotone (principal : set α → filter α) :=
by simp [monotone, principal_mono]; exact assume a b h, h

@[simp] lemma principal_eq_iff_eq {s t : set α} : principal s = principal t ↔ s = t :=
by simp [eq_iff_le_and_le]; refl

instance complete_lattice_filter : complete_lattice (filter α) :=
{ filter.partial_order_filter with
  sup           := filter.sup,
  le_sup_left   := assume a b, inter_subset_left _ _,
  le_sup_right  := assume a b, inter_subset_right _ _,
  sup_le        := assume a b c h₁ h₂, subset_inter h₁ h₂,
  inf           := filter.inf,
  le_inf        := assume f g h fg fh s ⟨a, ha, b, hb, h⟩,
    f.upwards_sets (inter_mem_sets (fg ha) (fh hb)) h,
  inf_le_left   := assume f g s h, ⟨s, h, univ, univ_mem_sets, inter_subset_left _ _⟩,
  inf_le_right  := assume f g s h, ⟨univ, univ_mem_sets, s, h, inter_subset_right _ _⟩,
  top           := principal univ,
  le_top        := assume a, show a ≤ principal univ, by simp [univ_mem_sets],
  bot           := principal ∅,
  bot_le        := assume a, show a.sets ⊆ {x | ∅ ⊆ x}, by simp; apply subset_univ,
  Sup           := Sup,
  le_Sup        := assume s f, filter.le_Sup,
  Sup_le        := assume s f, filter.Sup_le,
  Inf           := λs, Sup {x | ∀y∈s, x ≤ y},
  le_Inf        := assume s a h, filter.le_Sup h,
  Inf_le        := assume s a ha, filter.Sup_le $ assume b h, h _ ha }

@[simp] lemma map_principal {s : set α} {f : α → β} :
  map f (principal s) = principal (set.image f s) :=
filter_eq $ set.ext $ assume a, image_subset_iff_subset_preimage.symm

@[simp] lemma join_principal_eq_Sup {s : set (filter α)} : join (principal s) = Sup s := rfl

instance monad_filter : monad filter :=
{ monad .
  bind       := λ(α β : Type u) f m, join (map m f),
  pure       := λ(α : Type u) x, principal {x},
  map        := λ(α β : Type u), filter.map,
  id_map     := assume α f, filter_eq $ rfl,
  pure_bind  := assume α β a f, by simp [Sup_image],
  bind_assoc := assume α β γ f m₁ m₂, filter_eq $ rfl,
  bind_pure_comp_eq_map := assume α β f x, filter_eq $ by simp [join, map, preimage, principal] }

@[simp] lemma pure_def (x : α) : pure x = principal {x} := rfl

@[simp] lemma bind_def {α β} (f : filter α) (m : α → filter β) : f >>= m = join (map m f) := rfl

instance : alternative filter :=
{ filter.monad_filter with
  failure := λα, ⊥,
  orelse  := λα x y, x ⊔ y }

def at_top [preorder α] : filter α := ⨅ a, principal {b | a ≤ b}
def at_bot [preorder α] : filter α := ⨅ a, principal {b | b ≤ a}

/- lattice equations -/

lemma mem_inf_sets_of_left {f g : filter α} {s : set α} :
  s ∈ f.sets → s ∈ (f ⊓ g).sets :=
have f ⊓ g ≤ f, from inf_le_left,
assume hs, this hs

lemma mem_inf_sets_of_right {f g : filter α} {s : set α} :
  s ∈ g.sets → s ∈ (f ⊓ g).sets :=
have f ⊓ g ≤ g, from inf_le_right,
assume hs, this hs

@[simp] lemma mem_bot_sets {s : set α} : s ∈ (⊥ : filter α).sets :=
assume x, false.elim

lemma empty_in_sets_eq_bot {f : filter α} : ∅ ∈ f.sets ↔ f = ⊥ :=
⟨assume h, bot_unique $ assume s _, f.upwards_sets h (empty_subset s),
  assume : f = ⊥, this.symm ▸ mem_bot_sets⟩

lemma inhabited_of_mem_sets {f : filter α} {s : set α} (hf : f ≠ ⊥) (hs : s ∈ f.sets) :
  ∃x, x ∈ s :=
have ∅ ∉ f.sets, from assume h, hf $ empty_in_sets_eq_bot.mp h,
have s ≠ ∅, from assume h, this (h ▸ hs),
exists_mem_of_ne_empty this

lemma filter_eq_bot_of_not_nonempty {f : filter α} (ne : ¬ nonempty α) : f = ⊥ :=
empty_in_sets_eq_bot.mp $ f.upwards_sets univ_mem_sets $
  assume x, false.elim (ne ⟨x⟩)

lemma forall_sets_neq_empty_iff_neq_bot {f : filter α} :
  (∀ (s : set α), s ∈ f.sets → s ≠ ∅) ↔ f ≠ ⊥ :=
by
  simp [(@empty_in_sets_eq_bot α f).symm];
  exact ⟨assume h hs, h _ hs rfl, assume h s hs eq, h $ eq ▸ hs⟩

lemma mem_sets_of_neq_bot {f : filter α} {s : set α} (h : f ⊓ principal (-s) = ⊥) : s ∈ f.sets :=
have ∅ ∈ (f ⊓ principal (- s)).sets, from h.symm ▸ mem_bot_sets,
let ⟨s₁, hs₁, s₂, (hs₂ : -s ⊆ s₂), (hs : s₁ ∩ s₂ ⊆ ∅)⟩ := this in
have s₁ ⊆ s, from assume a ha, classical.by_contradiction $ assume ha', hs ⟨ha, hs₂ ha'⟩,
f.upwards_sets hs₁ this

@[simp] lemma mem_sup_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊔ g).sets = (s ∈ f.sets ∧ s ∈ g.sets) := rfl

@[simp] lemma mem_inf_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊓ g).sets = (∃t₁∈f.sets, ∃t₂∈g.sets, t₁ ∩ t₂ ⊆ s) :=
by refl

lemma inter_mem_inf_sets {α : Type u} {f g : filter α} {s t : set α}
  (hs : s ∈ f.sets) (ht : t ∈ g.sets) : s ∩ t ∈ (f ⊓ g).sets :=
inter_mem_sets (mem_inf_sets_of_left hs) (mem_inf_sets_of_right ht)

lemma infi_sets_eq {f : ι → filter α} (h : directed (≤) f) (ne : nonempty ι) :
  (infi f).sets = (⋃ i, (f i).sets) :=
let
  ⟨i⟩          := ne,
  u           := { filter .
    sets          := (⋃ i, (f i).sets),
    inhabited     := ⟨univ, begin simp, exact ⟨i, univ_mem_sets⟩ end⟩,
    directed_sets := directed_on_Union (show directed (≤) f, from h) (assume i, (f i).directed_sets),
    upwards_sets  := by simp [upwards]; exact assume x y ⟨j, xf⟩ xy, ⟨j, (f j).upwards_sets xf xy⟩ }
in
  subset.antisymm
    (show u ≤ infi f, from le_infi $ assume i, le_supr (λi, (f i).sets) i)
    (Union_subset $ assume i, infi_le f i)

lemma infi_sets_eq' {f : β → filter α} {s : set β} (h : directed_on (λx y, f x ≤ f y) s) (ne : ∃i, i ∈ s) :
  (⨅ i∈s, f i).sets = (⋃ i ∈ s, (f i).sets) :=
let ⟨i, hi⟩ := ne in
calc (⨅ i ∈ s, f i).sets  = (⨅ t : {t // t ∈ s}, (f t.val)).sets : by simp [infi_subtype]; refl
  ... = (⨆ t : {t // t ∈ s}, (f t.val).sets) : infi_sets_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨆ t ∈ {t | t ∈ s}, (f t).sets) : by simp [supr_subtype]; refl

lemma Inf_sets_eq_finite {s : set (filter α)} :
  (complete_lattice.Inf s).sets = (⋃ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t).sets) :=
calc (Inf s).sets = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t).sets : by rw [lattice.Inf_eq_finite_sets]
  ... = (⨆ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t).sets) : infi_sets_eq'
    (assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨x ∪ y, ⟨finite_union hx₁ hy₁, union_subset hx₂ hy₂⟩,
      Inf_le_Inf $ subset_union_left _ _, Inf_le_Inf $ subset_union_right _ _⟩)
    ⟨∅, by simp⟩

lemma supr_sets_eq {f : ι → filter α} : (supr f).sets = (⋂i, (f i).sets) :=
set.ext $ assume s,
show s ∈ (join (principal {a : filter α | ∃i : ι, a = f i})).sets ↔ s ∈ (⋂i, (f i).sets),
begin
  rw [mem_join_sets],
  simp,
  exact ⟨assume h i, h (f i) ⟨_, rfl⟩, assume h x ⟨i, eq⟩, eq.symm ▸ h i⟩
end

@[simp] lemma sup_join {f₁ f₂ : filter (filter α)} : (join f₁ ⊔ join f₂) = join (f₁ ⊔ f₂) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq, join]

@[simp] lemma supr_join {ι : Sort w} {f : ι → filter (filter α)} : (⨆x, join (f x)) = join (⨆x, f x) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq, join]

instance : bounded_distrib_lattice (filter α) :=
{ filter.complete_lattice_filter with
  le_sup_inf := assume x y z s h,
  begin
    cases h with h₁ h₂, revert h₂,
    simp,
    exact assume ⟨t₁, ht₁, t₂, ht₂, hs⟩, ⟨s ∪ t₁,
      x.upwards_sets h₁ $ subset_union_left _ _,
      y.upwards_sets ht₁ $ subset_union_right _ _,
      s ∪ t₂,
      x.upwards_sets h₁ $ subset_union_left _ _,
      z.upwards_sets ht₂ $ subset_union_right _ _,
      subset.trans (@le_sup_inf (set α) _ _ _ _) (union_subset (subset.refl _) hs)⟩
  end }

private lemma infi_finite_distrib {s : set (filter α)} {f : filter α} (h : finite s) :
  (⨅ a ∈ s, f ⊔ a) = f ⊔ (Inf s) :=
begin
  induction h with a s hn hs hi,
  { simp },
  { rw [infi_insert], simp [hi, infi_or, sup_inf_left] }
end

/- the complementary version with ⨆ g∈s, f ⊓ g does not hold! -/
lemma binfi_sup_eq { f : filter α } {s : set (filter α)} :
  (⨅ g∈s, f ⊔ g) = f ⊔ complete_lattice.Inf s :=
le_antisymm
  begin
    intros t h,
    cases h with h₁ h₂,
    rw [Inf_sets_eq_finite] at h₂,
    simp at h₂,
    cases h₂ with s' hs', cases hs' with hs' hs'', cases hs'' with hs's ht',
    have ht : t ∈ (⨅ a ∈ s', f ⊔ a).sets,
    { rw [infi_finite_distrib], exact ⟨h₁, ht'⟩, exact hs' },
    clear h₁ ht',
    revert ht t,
    change (⨅ a ∈ s, f ⊔ a) ≤ (⨅ a ∈ s', f ⊔ a),
    apply infi_le_infi2 _,
    exact assume i, ⟨i, infi_le_infi2 $ assume h, ⟨hs's h, le_refl _⟩⟩
  end
  (le_infi $ assume g, le_infi $ assume h, sup_le_sup (le_refl f) $ Inf_le h)

lemma infi_sup_eq { f : filter α } {g : ι → filter α} :
  (⨅ x, f ⊔ g x) = f ⊔ infi g :=
calc (⨅ x, f ⊔ g x) = (⨅ x (h : ∃i, g i = x), f ⊔ x) : by simp; rw [infi_comm]; simp
  ... = f ⊔ Inf {x | ∃i, g i = x} : binfi_sup_eq
  ... = f ⊔ infi g : by rw [Inf_eq_infi]; dsimp; simp; rw [infi_comm]; simp

/- principal equations -/

@[simp] lemma inf_principal {s t : set α} : principal s ⊓ principal t = principal (s ∩ t) :=
le_antisymm
  (by simp; exact ⟨s, subset.refl s, t, subset.refl t, subset.refl _⟩)
  (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp] lemma sup_principal {s t : set α} : principal s ⊔ principal t = principal (s ∪ t) :=
filter_eq $ set.ext $ by simp [union_subset_iff]

@[simp] lemma supr_principal {ι : Sort w} {s : ι → set α} : (⨆x, principal (s x)) = principal (⋃i, s i) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq]; exact (@supr_le_iff (set α) _ _ _ _).symm

lemma principal_univ : principal (univ : set α) = ⊤ := rfl

lemma principal_empty : principal (∅ : set α) = ⊥ := rfl

@[simp] lemma principal_eq_bot_iff {s : set α} : principal s = ⊥ ↔ s = ∅ :=
⟨assume h, principal_eq_iff_eq.mp $ by simp [principal_empty, h], assume h, by simp [*, principal_empty]⟩

@[simp] lemma mem_pure {a : α} {s : set α} : a ∈ s → s ∈ (pure a : filter α).sets :=
by simp; exact id

/- map equations -/

@[simp] lemma mem_map {f : filter α} {s : set β} {m : α → β} :
  (s ∈ (map m f).sets) = ({x | m x ∈ s} ∈ f.sets) := rfl

lemma image_mem_map {f : filter α} {m : α → β} {s : set α} (hs : s ∈ f.sets):
  m '' s ∈ (map m f).sets :=
f.upwards_sets hs $ assume x hx, ⟨x, hx, rfl⟩

@[simp] lemma map_id {f : filter α} : filter.map id f = f :=
filter_eq $ rfl
  
@[simp] lemma map_compose {γ : Type w} {f : α → β} {g : β → γ} :
  filter.map g ∘ filter.map f = filter.map (g ∘ f) :=
funext $ assume _, filter_eq $ rfl

@[simp] lemma map_map {f : α → β} {g : β → γ} {x : filter α} :
  filter.map g (filter.map f x) = filter.map (g ∘ f) x :=
congr_fun (@@filter.map_compose f g) x

@[simp] lemma map_sup {f g : filter α} {m : α → β} : map m (f ⊔ g) = map m f ⊔ map m g :=
filter_eq $ set.ext $ assume x, by simp

@[simp] lemma supr_map {ι : Sort w} {f : ι → filter α} {m : α → β} :
  (⨆x, map m (f x)) = map m (⨆x, f x) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq, map]

@[simp] lemma map_bot {m : α → β} : map m ⊥ = ⊥ :=
filter_eq $ set.ext $ assume x, by simp

@[simp] lemma map_eq_bot_iff {f : filter α} {m : α → β} : map m f = ⊥ ↔ f = ⊥ :=
⟨by rw [←empty_in_sets_eq_bot, ←empty_in_sets_eq_bot]; exact id,
  assume h, by simp [*]⟩

lemma map_ne_bot {m : α → β} {f : filter α} (hf : f ≠ ⊥) : map m f ≠ ⊥ :=
assume h, hf $ by rwa [map_eq_bot_iff] at h

lemma map_mono {f g : filter α} {m : α → β} (h : f ≤ g) : map m f ≤ map m g :=
le_of_sup_eq $ calc
  map m f ⊔ map m g = map m (f ⊔ g) : map_sup
                ... = map m g : congr_arg (map m) $ sup_of_le_right h

lemma monotone_map {m : α → β} : monotone (map m : filter α → filter β) :=
assume a b h, map_mono h

lemma map_cong {m₁ m₂ : α → β} {f : filter α} (h : {x | m₁ x = m₂ x} ∈ f.sets) :
  map m₁ f = map m₂ f :=
have ∀(m₁ m₂ : α → β) (h : {x | m₁ x = m₂ x} ∈ f.sets), map m₁ f ≤ map m₂ f,
  from assume m₁ m₂ h s (hs : {x | m₂ x ∈ s} ∈ f.sets),
  show {x | m₁ x ∈ s} ∈ f.sets,
    from f.upwards_sets (inter_mem_sets hs h) $
    assume x ⟨(h₁ : m₂ x ∈ s), (h₂ : m₁ x = m₂ x)⟩, show m₁ x ∈ s, from h₂.symm ▸ h₁,
le_antisymm (this m₁ m₂ h) (this m₂ m₁ $ f.upwards_sets h $ assume x, eq.symm)

-- this is a generic rule for monotone functions:
lemma map_infi_le {f : ι → filter α} {m : α → β} :
  map m (infi f) ≤ (⨅ i, map m (f i)) :=
le_infi $ assume i, map_mono $ infi_le _ _

lemma map_infi_eq {f : ι → filter α} {m : α → β} (hf : directed (≤) f) (hι : nonempty ι) :
  map m (infi f) = (⨅ i, map m (f i)) :=
le_antisymm
  map_infi_le
  (assume s (hs : preimage m s ∈ (infi f).sets),
    have ∃i, preimage m s ∈ (f i).sets,
      by simp [infi_sets_eq hf hι] at hs; assumption,
    let ⟨i, hi⟩ := this in
    have (⨅ i, map m (f i)) ≤ principal s,
      from infi_le_of_le i $ by simp; assumption,
    by simp at this; assumption)

lemma map_binfi_eq {ι : Type w} {f : ι → filter α} {m : α → β} {s : set ι}
  (h : directed_on (λx y, f x ≤ f y) s) (ne : ∃i, i ∈ s) : map m (⨅i∈s, f i) = (⨅i∈s, map m (f i)) :=
let ⟨i, hi⟩ := ne in
calc map m (⨅i∈s, f i) = map m (⨅i:{i // i ∈ s}, f i.val) : by simp [infi_subtype]
  ... = (⨅i:{i // i ∈ s}, map m (f i.val)) : map_infi_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨅i∈s, map m (f i)) : by simp [infi_subtype]

lemma map_inf {f g : filter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  map m (f ⊓ g) = map m f ⊓ map m g :=
le_antisymm
  (le_inf (map_mono inf_le_left) (map_mono inf_le_right))
  (assume s hs,
  begin
    simp [map, mem_inf_sets] at hs,
    simp [map, mem_inf_sets],
    exact (let ⟨t₁, h₁, t₂, h₂, hs⟩ := hs in
      ⟨m '' t₁, f.upwards_sets h₁ $ image_subset_iff_subset_preimage.mp $ subset.refl _,
        m '' t₂,
        by rwa [set.image_inter h, image_subset_iff_subset_preimage],
        g.upwards_sets h₂ $ image_subset_iff_subset_preimage.mp $ subset.refl _⟩)
  end)

/- bind equations -/

lemma mem_bind_sets {β : Type u} {s : set β} {f : filter α} {m : α → filter β} :
  s ∈ (f >>= m).sets ↔ (∃t ∈ f.sets, ∀x ∈ t, s ∈ (m x).sets) :=
calc s ∈ (f >>= m).sets ↔ {a | s ∈ (m a).sets} ∈ f.sets : by simp
                     ... ↔ (∃t ∈ f.sets, t ⊆ {a | s ∈ (m a).sets}) : exists_sets_subset_iff.symm
                     ... ↔ (∃t ∈ f.sets, ∀x ∈ t, s ∈ (m x).sets) : iff.refl _

lemma bind_mono {β : Type u} {f : filter α} {g h : α → filter β} (h₁ : {a | g a ≤ h a} ∈ f.sets) :
  f >>= g ≤ f >>= h :=
assume x h₂, f.upwards_sets (inter_mem_sets h₁ h₂) $ assume s ⟨gh', h'⟩, gh' h'

lemma bind_sup {β : Type u} {f g : filter α} {h : α → filter β} :
  (f ⊔ g) >>= h = (f >>= h) ⊔ (g >>= h) :=
by simp

lemma bind_mono2 {β : Type u} {f g : filter α} {h : α → filter β} (h₁ : f ≤ g) :
  f >>= h ≤ g >>= h :=
assume s h', h₁ h'

lemma principal_bind {β : Type u} {s : set α} {f : α → filter β} :
  (principal s >>= f) = (⨆x ∈ s, f x) :=
show join (map f (principal s)) = (⨆x ∈ s, f x),
  by simp [Sup_image]

lemma seq_mono {β : Type u} {f₁ f₂ : filter (α → β)} {g₁ g₂ : filter α}
  (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁ <*> g₁ ≤ f₂ <*> g₂ :=
le_trans (bind_mono2 hf) (bind_mono $ univ_mem_sets' $ assume f, map_mono hg)

@[simp] lemma fmap_principal {β : Type u} {s : set α} {f : α → β} :
  f <$> principal s = principal (set.image f s) :=
filter_eq $ set.ext $ assume a, image_subset_iff_subset_preimage.symm

lemma mem_return_sets {a : α} {s : set α} : s ∈ (return a : filter α).sets ↔ a ∈ s :=
show s ∈ (principal {a}).sets ↔ a ∈ s,
  by simp

lemma infi_neq_bot_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≤) f) (hb : ∀i, f i ≠ ⊥): (infi f) ≠ ⊥ :=
let ⟨x⟩ := hn in
assume h, have he: ∅ ∈ (infi f).sets, from h.symm ▸ mem_bot_sets,
classical.by_cases
  (assume : nonempty ι,
    have ∃i, ∅ ∈ (f i).sets,
      by rw [infi_sets_eq hd this] at he; simp at he; assumption,
    let ⟨i, hi⟩ := this in
    hb i $ bot_unique $
    assume s _, (f i).upwards_sets hi $ empty_subset _)
  (assume : ¬ nonempty ι,
    have univ ⊆ (∅ : set α),
    begin
      rw [←principal_mono, principal_univ, principal_empty, ←h],
      exact (le_infi $ assume i, false.elim $ this ⟨i⟩)
    end,
    this $ mem_univ x)

lemma infi_neq_bot_iff_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≤) f) : (infi f) ≠ ⊥ ↔ (∀i, f i ≠ ⊥) :=
⟨assume neq_bot i eq_bot, neq_bot $ bot_unique $ infi_le_of_le i $ eq_bot ▸ le_refl _,
  infi_neq_bot_of_directed hn hd⟩

@[simp] lemma return_neq_bot {α : Type u} {a : α} : return a ≠ (⊥ : filter α) :=
by simp [return]

section vmap
variables {f f₁ f₂ : filter β} {m : α → β}

theorem mem_vmap_of_mem {s : set β} (h : s ∈ f.sets) : preimage m s ∈ (vmap m f).sets :=
⟨s, h, subset.refl _⟩

lemma vmap_mono (h : f₁ ≤ f₂) : vmap m f₁ ≤ vmap m f₂ :=
assume s ⟨t, ht, h_sub⟩, ⟨t, h ht, h_sub⟩

lemma monotone_vmap : monotone (vmap m : filter β → filter α) :=
assume a b h, vmap_mono h

@[simp] lemma vmap_bot : vmap m ⊥ = ⊥ :=
bot_unique $ assume s _, ⟨∅, by simp, by simp⟩

@[simp] theorem vmap_principal {t : set β} : vmap m (principal t) = principal (preimage m t) :=
filter_eq $ set.ext $ assume s,
  ⟨assume ⟨u, (hu : t ⊆ u), (b : preimage m u ⊆ s)⟩, subset.trans (preimage_mono hu) b,
    assume : preimage m t ⊆ s, ⟨t, subset.refl t, this⟩⟩


theorem preimage_mem_vmap {f : filter β} {m : α → β} {s : set β} (hs : s ∈ f.sets):
  preimage m s ∈ (vmap m f).sets :=
⟨s, hs, subset.refl _⟩

lemma vmap_sup : vmap m (f₁ ⊔ f₂) = vmap m f₁ ⊔ vmap m f₂ :=
le_antisymm
  (assume s ⟨⟨t₁, ht₁, hs₁⟩, ⟨t₂, ht₂, hs₂⟩⟩,
    ⟨t₁ ∪ t₂,
      ⟨f₁.upwards_sets ht₁ (subset_union_left _ _), f₂.upwards_sets ht₂ (subset_union_right _ _)⟩,
      union_subset hs₁ hs₂⟩)
  (sup_le (vmap_mono le_sup_left) (vmap_mono le_sup_right))

lemma vmap_inf : vmap m (f₁ ⊓ f₂) = vmap m f₁ ⊓ vmap m f₂ :=
le_antisymm
  (le_inf (vmap_mono inf_le_left) (vmap_mono inf_le_right))
  (assume s ⟨t, ht, (hs : preimage m t ⊆ s)⟩,
    let ⟨t₁, ht₁, t₂, ht₂, (ht : t₁ ∩ t₂ ⊆ t)⟩ := mem_inf_sets.mp ht in
    have preimage m t₁ ∩ preimage m t₂ ∈ (vmap m f₁ ⊓ vmap m f₂).sets,
      from inter_mem_inf_sets (mem_vmap_of_mem ht₁) (mem_vmap_of_mem ht₂),
    filter.upwards_sets _ this $
      calc preimage m (t₁ ∩ t₂) ⊆ preimage m t : preimage_mono ht
        ... ⊆ s : hs)

lemma le_map_vmap {f : filter β} {m : α → β} (hm : ∀x, ∃y, m y = x) :
  f ≤ map m (vmap m f) :=
assume s ⟨t, ht, (sub : ∀x, m x ∈ t → m x ∈ s)⟩,
f.upwards_sets ht $
  assume x, let ⟨y, (hy : m y = x)⟩ := hm x in
  hy ▸ sub y

lemma vmap_map {f : filter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  vmap m (map m f) = f :=
have ∀s, preimage m (image m s) = s,
  from assume s, preimage_image_eq h,
le_antisymm
  (assume s hs, ⟨
    image m s,
    f.upwards_sets hs $ by simp [this, subset.refl],
    by simp [this, subset.refl]⟩)
  (assume s ⟨t, (h₁ : preimage m t ∈ f.sets), (h₂ : preimage m t ⊆ s)⟩,
    f.upwards_sets h₁ h₂)

lemma map_inj {f g : filter α} {m : α → β} (hm : ∀ x y, m x = m y → x = y) (h : map m f = map m g) :
  f = g :=
have vmap m (map m f) = vmap m (map m g), by rw h,
by rwa [vmap_map hm, vmap_map hm] at this

lemma vmap_neq_bot {f : filter β} {m : α → β}
  (hm : ∀t∈f.sets, ∃a, m a ∈ t) : vmap m f ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $ assume s ⟨t, ht, t_s⟩,
  let ⟨a, (ha : a ∈ preimage m t)⟩ := hm t ht in
  neq_bot_of_le_neq_bot (ne_empty_of_mem ha) t_s

lemma vmap_neq_bot_of_surj {f : filter β} {m : α → β}
  (hf : f ≠ ⊥) (hm : ∀b, ∃a, m a = b) : vmap m f ≠ ⊥ :=
vmap_neq_bot $ assume t ht,
  let
    ⟨b, (hx : b ∈ t)⟩ := inhabited_of_mem_sets hf ht,
    ⟨a, (ha : m a = b)⟩ := hm b
  in ⟨a, ha.symm ▸ hx⟩

lemma map_vmap_le {f : filter β} {m : α → β} : map m (vmap m f) ≤ f :=
assume s hs, ⟨s, hs, subset.refl _⟩

lemma le_vmap_map {f : filter α} {m : α → β} : f ≤ vmap m (map m f) :=
assume s ⟨t, ht, h_eq⟩, f.upwards_sets ht h_eq

lemma vmap_vmap_comp {f : filter α} {m : γ → β} {n : β → α} :
  vmap m (vmap n f) = vmap (n ∘ m) f :=
le_antisymm
  (assume c ⟨b, hb, (h : preimage (n ∘ m) b ⊆ c)⟩, ⟨preimage n b, preimage_mem_vmap hb, h⟩)
  (assume c ⟨b, ⟨a, ha, (h₁ : preimage n a ⊆ b)⟩, (h₂ : preimage m b ⊆ c)⟩,
    ⟨a, ha, show preimage m (preimage n a) ⊆ c, from subset.trans (preimage_mono h₁) h₂⟩)

lemma le_vmap_iff_map_le {f : filter α} {g : filter β} {m : α → β} :
  f ≤ vmap m g ↔ map m f ≤ g :=
⟨assume h, le_trans (map_mono h) map_vmap_le,
  assume h, le_trans le_vmap_map (vmap_mono h)⟩

end vmap

/- towards -/
def towards (f : α → β) (l₁ : filter α) (l₂ : filter β) := filter.map f l₁ ≤ l₂

lemma towards_cong {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (h : towards f₁ l₁ l₂) (hl : {x | f₁ x = f₂ x} ∈ l₁.sets) : towards f₂ l₁ l₂ :=
by rwa [towards, ←map_cong hl]

lemma towards_id' {x y : filter α} : x ≤ y → towards id x y :=
by simp [towards] { contextual := tt }

lemma towards_id {x : filter α} : towards id x x := towards_id' $ le_refl x

lemma towards_compose {f : α → β} {g : β → γ} {x : filter α} {y : filter β} {z : filter γ}
  (hf : towards f x y) (hg : towards g y z) : towards (g ∘ f) x z :=
calc map (g ∘ f) x = map g (map f x) : by rw [map_map]
  ... ≤ map g y : map_mono hf
  ... ≤ z : hg

lemma towards_map {f : α → β} {x : filter α} : towards f x (map f x) := le_refl (map f x)

lemma towards_map' {f : β → γ} {g : α → β} {x : filter α} {y : filter γ}
  (h : towards (f ∘ g) x y) : towards f (map g x) y :=
by rwa [towards, map_map]

lemma towards_vmap {f : α → β} {x : filter β} : towards f (vmap f x) x :=
map_vmap_le

lemma towards_vmap' {f : β → γ} {g : α → β} {x : filter α} {y : filter γ}
  (h : towards (f ∘ g) x y) : towards g x (vmap f y) :=
le_vmap_iff_map_le.mpr $ by rwa [map_map]

lemma towards_inf {f : α → β} {x : filter α} {y₁ y₂ : filter β}
  (h₁ : towards f x y₁) (h₂ : towards f x y₂) : towards f x (y₁ ⊓ y₂) :=
le_inf h₁ h₂

section lift

protected def lift (f : filter α) (g : set α → filter β) :=
(⨅s ∈ f.sets, g s)

section
variables {f f₁ f₂ : filter α} {g g₁ g₂ : set α → filter β}

lemma lift_sets_eq (hg : monotone g) : (f.lift g).sets = (⋃t∈f.sets, (g t).sets) :=
infi_sets_eq'
  (assume s hs t ht, ⟨s ∩ t, inter_mem_sets hs ht,
    hg $ inter_subset_left s t, hg $ inter_subset_right s t⟩)
  ⟨univ, univ_mem_sets⟩

lemma mem_lift {s : set β} {t : set α} (ht : t ∈ f.sets) (hs : s ∈ (g t).sets) :
  s ∈ (f.lift g).sets :=
le_principal_iff.mp $ show f.lift g ≤ principal s,
  from infi_le_of_le t $ infi_le_of_le ht $ le_principal_iff.mpr hs

lemma mem_lift_iff (hg : monotone g) {s : set β} :
  s ∈ (f.lift g).sets ↔ (∃t∈f.sets, s ∈ (g t).sets) :=
by rw [lift_sets_eq hg]; simp

lemma lift_le {f : filter α} {g : set α → filter β}  {h : filter β} {s : set α}
  (hs : s ∈ f.sets) (hg : g s ≤ h) : f.lift g ≤ h :=
infi_le_of_le s $ infi_le_of_le hs $ hg

lemma lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi2 $ assume hs, ⟨hf hs, hg s⟩

lemma lift_mono' (hg : ∀s∈f.sets, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, hg s hs

lemma map_lift_eq {m : β → γ} (hg : monotone g) :
  map m (f.lift g) = f.lift (map m ∘ g) :=
have monotone (map m ∘ g),
  from monotone_comp hg monotone_map,
filter_eq $ set.ext $
  by simp [mem_lift_iff, hg, @mem_lift_iff _ _ f _ this]

lemma vmap_lift_eq {m : γ → β} (hg : monotone g) :
  vmap m (f.lift g) = f.lift (vmap m ∘ g) :=
have monotone (vmap m ∘ g),
  from monotone_comp hg monotone_vmap,
filter_eq $ set.ext $
begin
  simp [vmap, mem_lift_iff, hg, @mem_lift_iff _ _ f _ this],
  simp [vmap, function.comp],
  exact assume s, ⟨assume ⟨t₁, hs, t₂, ht, ht₁⟩, ⟨t₂, ht, t₁, hs, ht₁⟩,
    assume ⟨t₂, ht, t₁, hs, ht₁⟩, ⟨t₁, hs, t₂, ht, ht₁⟩⟩
end

theorem vmap_lift_eq2 {m : β → α} {g : set β → filter γ} (hg : monotone g) :
  (vmap m f).lift g = f.lift (g ∘ preimage m) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs,
    infi_le_of_le (preimage m s) $ infi_le _ ⟨s, hs, subset.refl _⟩)
  (le_infi $ assume s, le_infi $ assume ⟨s', hs', (h_sub : preimage m s' ⊆ s)⟩,
    infi_le_of_le s' $ infi_le_of_le hs' $ hg h_sub)

lemma map_lift_eq2 {g : set β → filter γ} {m : α → β} (hg : monotone g) :
  (map m f).lift g = f.lift (g ∘ image m) :=
le_antisymm
  (infi_le_infi2 $ assume s, ⟨image m s,
    infi_le_infi2 $ assume hs, ⟨
      f.upwards_sets hs $ assume a h, mem_image_of_mem _ h,
      le_refl _⟩⟩)
  (infi_le_infi2 $ assume t, ⟨preimage m t,
    infi_le_infi2 $ assume ht, ⟨ht,
      hg $ assume x, assume h : x ∈ m '' preimage m t,
        let ⟨y, hy, h_eq⟩ := h in
        show x ∈ t, from h_eq ▸ hy⟩⟩)

lemma lift_comm {g : filter β} {h : set α → set β → filter γ} :
  f.lift (λs, g.lift (h s)) = g.lift (λt, f.lift (λs, h s t)) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)

lemma lift_assoc {h : set β → filter γ} (hg : monotone g)  :
  (f.lift g).lift h = f.lift (λs, (g s).lift h) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le t $ infi_le _ $ (mem_lift_iff hg).mpr ⟨_, hs, ht⟩)
  (le_infi $ assume t, le_infi $ assume ht,
    let ⟨s, hs, h'⟩ := (mem_lift_iff hg).mp ht in
    infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le t $ infi_le _ h')

lemma lift_lift_same_le_lift {g : set α → set α → filter β} :
  f.lift (λs, f.lift (g s)) ≤ f.lift (λs, g s s) :=
le_infi $ assume s, le_infi $ assume hs, infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le s $ infi_le _ hs

lemma lift_lift_same_eq_lift {g : set α → set α → filter β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)):
  f.lift (λs, f.lift (g s)) = f.lift (λs, g s s) :=
le_antisymm
  lift_lift_same_le_lift
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le (s ∩ t) $
    infi_le_of_le (inter_mem_sets hs ht) $
    calc g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) : hg₂ (s ∩ t) (inter_subset_left _ _)
      ... ≤ g s t                        : hg₁ s (inter_subset_right _ _))

lemma lift_principal {s : set α} (hg : monotone g) :
  (principal s).lift g = g s :=
le_antisymm
  (infi_le_of_le s $ infi_le _ $ subset.refl _)
  (le_infi $ assume t, le_infi $ assume hi, hg hi)

theorem monotone_lift [preorder γ] {f : γ → filter α} {g : γ → set α → filter β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift (g c)) :=
assume a b h, lift_mono (hf h) (hg h)

lemma lift_neq_bot_iff (hm : monotone g) : (f.lift g ≠ ⊥) ↔ (∀s∈f.sets, g s ≠ ⊥) :=
classical.by_cases
  (assume hn : nonempty β,
    calc f.lift g ≠ ⊥ ↔ (⨅s : { s // s ∈ f.sets}, g s.val) ≠ ⊥ : by simp [filter.lift, infi_subtype]
      ... ↔ (∀s:{ s // s ∈ f.sets}, g s.val ≠ ⊥) :
        infi_neq_bot_iff_of_directed hn
          (assume ⟨a, ha⟩ ⟨b, hb⟩, ⟨⟨a ∩ b, inter_mem_sets ha hb⟩,
            hm $ inter_subset_left _ _, hm $ inter_subset_right _ _⟩)
      ... ↔ (∀s∈f.sets, g s ≠ ⊥) : ⟨assume h s hs, h ⟨s, hs⟩, assume h ⟨s, hs⟩, h s hs⟩)
  (assume hn : ¬ nonempty β,
    have h₁ : f.lift g = ⊥, from filter_eq_bot_of_not_nonempty hn,
    have h₂ : ∀s, g s = ⊥, from assume s, filter_eq_bot_of_not_nonempty hn,
    calc (f.lift g ≠ ⊥) ↔ false : by simp [h₁]
      ... ↔ (∀s∈f.sets, false) : ⟨false.elim, assume h, h univ univ_mem_sets⟩
      ... ↔ (∀s∈f.sets, g s ≠ ⊥) : by simp [h₂])

end

section
protected def lift' (f : filter α) (h : set α → set β) :=
f.lift (principal ∘ h)

variables {f f₁ f₂ : filter α} {h h₁ h₂ : set α → set β}

lemma mem_lift' {t : set α} (ht : t ∈ f.sets) : h t ∈ (f.lift' h).sets :=
le_principal_iff.mp $ show f.lift' h ≤ principal (h t),
  from infi_le_of_le t $ infi_le_of_le ht $ le_refl _

lemma mem_lift'_iff (hh : monotone h) {s : set β} : s ∈ (f.lift' h).sets ↔ (∃t∈f.sets, h t ⊆ s) :=
have monotone (principal ∘ h),
  from assume a b h, principal_mono.mpr $ hh h,
by simp [filter.lift', @mem_lift_iff α β f _ this]

lemma lift'_le {f : filter α} {g : set α → set β} {h : filter β} {s : set α}
  (hs : s ∈ f.sets) (hg : principal (g s) ≤ h) : f.lift' g ≤ h :=
lift_le hs hg

lemma lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
lift_mono hf $ assume s, principal_mono.mpr $ hh s

lemma lift'_mono' (hh : ∀s∈f.sets, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, principal_mono.mpr $ hh s hs

lemma lift'_cong (hh : ∀s∈f.sets, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
le_antisymm (lift'_mono' $ assume s hs, le_of_eq $ hh s hs) (lift'_mono' $ assume s hs, le_of_eq $ (hh s hs).symm)

lemma map_lift'_eq {m : β → γ} (hh : monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
calc map m (f.lift' h) = f.lift (map m ∘ principal ∘ h) :
    map_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (image m ∘ h) : by simp [function.comp, filter.lift']

lemma map_lift'_eq2 {g : set β → set γ} {m : α → β} (hg : monotone g) :
  (map m f).lift' g = f.lift' (g ∘ image m) :=
map_lift_eq2 $ monotone_comp hg monotone_principal

theorem vmap_lift'_eq {m : γ → β} (hh : monotone h) :
  vmap m (f.lift' h) = f.lift' (preimage m ∘ h) :=
calc vmap m (f.lift' h) = f.lift (vmap m ∘ principal ∘ h) :
    vmap_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (preimage m ∘ h) : by simp [function.comp, filter.lift']

theorem vmap_lift'_eq2 {m : β → α} {g : set β → set γ} (hg : monotone g) :
  (vmap m f).lift' g = f.lift' (g ∘ preimage m) :=
vmap_lift_eq2 $ monotone_comp hg monotone_principal

lemma lift'_principal {s : set α} (hh : monotone h) :
  (principal s).lift' h = principal (h s) :=
lift_principal $ monotone_comp hh monotone_principal

lemma principal_le_lift' {t : set β} (hh : ∀s∈f.sets, t ⊆ h s) :
  principal t ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, principal_mono.mpr (hh s hs)

theorem monotone_lift' [preorder γ] {f : γ → filter α} {g : γ → set α → set β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift' (g c)) :=
assume a b h, lift'_mono (hf h) (hg h)

lemma lift_lift'_assoc {g : set α → set β} {h : set β → filter γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift h = f.lift (λs, h (g s)) :=
calc (f.lift' g).lift h = f.lift (λs, (principal (g s)).lift h) :
    lift_assoc (monotone_comp hg monotone_principal)
  ... = f.lift (λs, h (g s)) : by simp [lift_principal, hh]

lemma lift'_lift'_assoc {g : set α → set β} {h : set β → set γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift' h = f.lift' (λs, h (g s)) :=
lift_lift'_assoc hg (monotone_comp hh monotone_principal)

lemma lift'_lift_assoc {g : set α → filter β} {h : set β → set γ}
  (hg : monotone g) : (f.lift g).lift' h = f.lift (λs, (g s).lift' h) :=
lift_assoc hg

lemma lift_lift'_same_le_lift' {g : set α → set α → set β} :
  f.lift (λs, f.lift' (g s)) ≤ f.lift' (λs, g s s) :=
lift_lift_same_le_lift

lemma lift_lift'_same_eq_lift' {g : set α → set α → set β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)):
  f.lift (λs, f.lift' (g s)) = f.lift' (λs, g s s) :=
lift_lift_same_eq_lift
  (assume s, monotone_comp monotone_id $ monotone_comp (hg₁ s) monotone_principal)
  (assume t, monotone_comp (hg₂ t) monotone_principal)

lemma lift'_inf_principal_eq {h : set α → set β} {s : set β} :
  f.lift' h ⊓ principal s = f.lift' (λt, h t ∩ s) :=
le_antisymm
  (le_infi $ assume t, le_infi $ assume ht,
    calc filter.lift' f h ⊓ principal s ≤ principal (h t) ⊓ principal s :
        inf_le_inf (infi_le_of_le t $ infi_le _ ht) (le_refl _)
      ... = _ : by simp)
  (le_inf
    (le_infi $ assume t, le_infi $ assume ht,
      infi_le_of_le t $ infi_le_of_le ht $ by simp; exact inter_subset_right _ _)
    (infi_le_of_le univ $ infi_le_of_le univ_mem_sets $ by simp; exact inter_subset_left _ _))

lemma lift'_neq_bot_iff (hh : monotone h) : (f.lift' h ≠ ⊥) ↔ (∀s∈f.sets, h s ≠ ∅) :=
calc (f.lift' h ≠ ⊥) ↔ (∀s∈f.sets, principal (h s) ≠ ⊥) :
    lift_neq_bot_iff (monotone_comp hh monotone_principal)
  ... ↔ (∀s∈f.sets, h s ≠ ∅) : by simp [principal_eq_bot_iff]

@[simp] lemma lift'_id {f : filter α} : f.lift' id = f :=
le_antisymm
  (assume s hs, mem_lift' hs)
  (le_infi $ assume s, le_infi $ assume hs, by simp [hs])

lemma le_lift' {f : filter α} {h : set α → set β} {g : filter β}
  (h_le : ∀s∈f.sets, h s ∈ g.sets) : g ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, by simp [h_le]; exact h_le s hs

end

end lift

theorem vmap_eq_lift' {f : filter β} {m : α → β} :
  vmap m f = f.lift' (preimage m) :=
filter_eq $ set.ext $ by simp [mem_lift'_iff, monotone_preimage, vmap]

/- product filter -/

/- The product filter cannot be defined using the monad structure on filters. For example:

  F := do {x <- seq, y <- top, return (x, y)}
  hence:
    s ∈ F  <->  ∃n, [n..∞] × univ ⊆ s

  G := do {y <- top, x <- seq, return (x, y)}
  hence:
    s ∈ G  <->  ∀i:ℕ, ∃n, [n..∞] × {i} ⊆ s

  Now ⋃i, [i..∞] × {i}  is in G but not in F.

  As product filter we want to have F as result.
-/

section prod

protected def prod (f : filter α) (g : filter β) : filter (α × β) :=
f.lift $ λs, g.lift' $ λt, set.prod s t

lemma prod_mem_prod {s : set α} {t : set β} {f : filter α} {g : filter β}
  (hs : s ∈ f.sets) (ht : t ∈ g.sets) : set.prod s t ∈ (filter.prod f g).sets :=
le_principal_iff.mp $ show filter.prod f g ≤ principal (set.prod s t),
  from infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le t $ infi_le _ ht

lemma prod_same_eq {f : filter α} : filter.prod f f = f.lift' (λt, set.prod t t) :=
lift_lift'_same_eq_lift'
  (assume s, set.monotone_prod monotone_const monotone_id)
  (assume t, set.monotone_prod monotone_id monotone_const)

lemma mem_prod_iff {s : set (α×β)} {f : filter α} {g : filter β} :
  s ∈ (filter.prod f g).sets ↔ (∃t₁∈f.sets, ∃t₂∈g.sets, set.prod t₁ t₂ ⊆ s) :=
begin
  delta filter.prod,
  rw [mem_lift_iff],
  apply exists_congr, intro t₁,
  apply exists_congr, intro ht₁,
  rw [mem_lift'_iff],
  exact set.monotone_prod monotone_const monotone_id,
  exact (monotone_lift' monotone_const $ monotone_lam $ assume b, set.monotone_prod monotone_id monotone_const)
end

lemma mem_prod_same_iff {s : set (α×α)} {f : filter α} :
  s ∈ (filter.prod f f).sets ↔ (∃t∈f.sets, set.prod t t ⊆ s) :=
by rw [prod_same_eq, mem_lift'_iff]; exact set.monotone_prod monotone_id monotone_id

lemma prod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  filter.prod f₁ g₁ ≤ filter.prod f₂ g₂ :=
lift_mono hf $ assume s, lift'_mono hg $ le_refl _

lemma prod_comm {f : filter α} {g : filter β} :
  filter.prod f g = map (λp:β×α, (p.2, p.1)) (filter.prod g f) :=
eq.symm $ calc map (λp:β×α, (p.2, p.1)) (filter.prod g f) =
        (g.lift $ λt, map (λp:β×α, (p.2, p.1)) (f.lift' $ λs, set.prod t s)) :
    map_lift_eq $ assume a b h, lift'_mono (le_refl f) (assume t, set.prod_mono h (subset.refl t))
  ... = (g.lift $ λt, f.lift' $ λs, image (λp:β×α, (p.2, p.1)) (set.prod t s)) :
    congr_arg (filter.lift g) $ funext $ assume s, map_lift'_eq $ assume a b h, set.prod_mono (subset.refl s) h
  ... = (g.lift $ λt, f.lift' $ λs, set.prod s t) : by simp [set.image_swap_prod]
  ... = filter.prod f g : lift_comm

lemma prod_lift_lift {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → filter β₁} {g₂ : set α₂ → filter β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  filter.prod (f₁.lift g₁) (f₂.lift g₂) = f₁.lift (λs, f₂.lift (λt, filter.prod (g₁ s) (g₂ t))) :=
begin
  delta filter.prod,
  rw [lift_assoc],
  apply congr_arg, apply funext, intro x,
  rw [lift_comm],
  apply congr_arg, apply funext, intro y,
  rw [lift'_lift_assoc],
  exact hg₂,
  exact hg₁
end

lemma prod_lift'_lift' {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → set β₁} {g₂ : set α₂ → set β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  filter.prod (f₁.lift' g₁) (f₂.lift' g₂) = f₁.lift (λs, f₂.lift' (λt, set.prod (g₁ s) (g₂ t))) :=
begin
  delta filter.prod,
  rw [lift_lift'_assoc],
  apply congr_arg, apply funext, intro x,
  rw [lift'_lift'_assoc],
  exact hg₂,
  exact set.monotone_prod monotone_const monotone_id,
  exact hg₁,
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume x, set.monotone_prod monotone_id monotone_const)
end

lemma towards_fst {f : filter α} {g : filter β} : towards prod.fst (filter.prod f g) f :=
assume s hs, (filter.prod f g).upwards_sets (prod_mem_prod hs univ_mem_sets) $
  show set.prod s univ ⊆ preimage prod.fst s, by simp [set.prod, preimage] {contextual := tt}

lemma towards_snd {f : filter α} {g : filter β} : towards prod.snd (filter.prod f g) g :=
assume s hs, (filter.prod f g).upwards_sets (prod_mem_prod univ_mem_sets hs) $
  show set.prod univ s ⊆ preimage prod.snd s, by simp [set.prod, preimage] {contextual := tt}

lemma towards_prod_mk {f : filter α} {g : filter β} {h : filter γ} {m₁ : α → β} {m₂ : α → γ}
  (h₁ : towards m₁ f g) (h₂ : towards m₂ f h) : towards (λx, (m₁ x, m₂ x)) f (filter.prod g h) :=
assume s hs,
let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
f.upwards_sets (inter_mem_sets (h₁ hs₁) (h₂ hs₂)) $
  calc preimage m₁ s₁ ∩ preimage m₂ s₂ ⊆ preimage (λx, (m₁ x, m₂ x)) (set.prod s₁ s₂) : λx ⟨h₁, h₂⟩, ⟨h₁, h₂⟩
    ... ⊆ preimage (λx, (m₁ x, m₂ x)) s : preimage_mono h

lemma prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  filter.prod (map m₁ f₁) (map m₂ f₂) = map (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) (filter.prod f₁ f₂) :=
le_antisymm
  (assume s hs,
    let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
    filter.upwards_sets _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) $
      calc set.prod (m₁ '' s₁) (m₂ '' s₂) = (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) '' set.prod s₁ s₂ :
          set.prod_image_image_eq
        ... ⊆ _ : by rwa [image_subset_iff_subset_preimage])
  (towards_prod_mk (towards_compose towards_fst (le_refl _)) (towards_compose towards_snd (le_refl _)))

lemma prod_vmap_vmap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
  filter.prod (vmap m₁ f₁) (vmap m₂ f₂) = vmap (λp:β₁×β₂, (m₁ p.1, m₂ p.2)) (filter.prod f₁ f₂) :=
have ∀s t, set.prod (preimage m₁ s) (preimage m₂ t) = preimage (λp:β₁×β₂, (m₁ p.1, m₂ p.2)) (set.prod s t),
  from assume s t, rfl,
begin
  rw [vmap_eq_lift', vmap_eq_lift', prod_lift'_lift'],
  simp [this, filter.prod],
  rw [vmap_lift_eq], tactic.swap, exact (monotone_lift' monotone_const $
    monotone_lam $ assume t, set.monotone_prod monotone_id monotone_const),
  apply congr_arg, apply funext, intro t',
  dsimp [function.comp],
  rw [vmap_lift'_eq],
  exact set.monotone_prod monotone_const monotone_id,
  exact monotone_preimage,
  exact monotone_preimage
end

lemma prod_inf_prod {f₁ f₂ : filter α} {g₁ g₂ : filter β} :
  filter.prod f₁ g₁ ⊓ filter.prod f₂ g₂ = filter.prod (f₁ ⊓ f₂) (g₁ ⊓ g₂) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
  begin
    revert s hs t ht,
    simp,
    exact assume s ⟨s₁, hs₁, s₂, hs₂, hs⟩ t ⟨t₁, ht₁, t₂, ht₂, ht⟩,
      ⟨set.prod s₁ t₁, prod_mem_prod hs₁ ht₁, set.prod s₂ t₂, prod_mem_prod hs₂ ht₂,
      by rw [set.prod_inter_prod]; exact set.prod_mono hs ht⟩
  end)
  (le_inf (prod_mono inf_le_left inf_le_left) (prod_mono inf_le_right inf_le_right))

lemma prod_neq_bot {f : filter α} {g : filter β} :
  filter.prod f g ≠ ⊥ ↔ (f ≠ ⊥ ∧ g ≠ ⊥) :=
calc filter.prod f g ≠ ⊥ ↔ (∀s∈f.sets, g.lift' (set.prod s) ≠ ⊥) :
  begin
    delta filter.prod,
    rw [lift_neq_bot_iff],
    exact (monotone_lift' monotone_const $ monotone_lam $ assume s, set.monotone_prod monotone_id monotone_const)
  end
  ... ↔ (∀s∈f.sets, ∀t∈g.sets, s ≠ ∅ ∧ t ≠ ∅) :
  begin
    apply forall_congr, intro s,
    apply forall_congr, intro hs,
    rw [lift'_neq_bot_iff],
    apply forall_congr, intro t,
    apply forall_congr, intro ht,
    rw [set.prod_neq_empty_iff],
    exact set.monotone_prod monotone_const monotone_id
  end
  ... ↔ (∀s∈f.sets, s ≠ ∅) ∧ (∀t∈g.sets, t ≠ ∅) :
    ⟨assume h, ⟨assume s hs, (h s hs univ univ_mem_sets).left,
        assume t ht, (h univ univ_mem_sets t ht).right⟩,
      assume ⟨h₁, h₂⟩ s hs t ht, ⟨h₁ s hs, h₂ t ht⟩⟩
  ... ↔ _ : by simp [forall_sets_neq_empty_iff_neq_bot]

lemma prod_principal_principal {s : set α} {t : set β} :
  filter.prod (principal s) (principal t) = principal (set.prod s t) :=
begin
  delta filter.prod,
  rw [lift_principal, lift'_principal],
  exact set.monotone_prod monotone_const monotone_id,
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume s, set.monotone_prod monotone_id monotone_const)
end

end prod

lemma mem_infi_sets {f : ι → filter α} (i : ι) : ∀{s}, s ∈ (f i).sets → s ∈ (⨅i, f i).sets :=
show (⨅i, f i) ≤ f i, from infi_le _ _

@[simp] lemma mem_top_sets_iff {s : set α} : s ∈ (⊤ : filter α).sets ↔ s = univ :=
⟨assume h, top_unique $ h, assume h, h.symm ▸ univ_mem_sets⟩

@[elab_as_eliminator]
lemma infi_sets_induct {f : ι → filter α} {s : set α} (hs : s ∈ (infi f).sets) {p : set α → Prop}
  (uni : p univ)
  (ins : ∀{i s₁ s₂}, s₁ ∈ (f i).sets → p s₂ → p (s₁ ∩ s₂))
  (upw : ∀{s₁ s₂}, s₁ ⊆ s₂ → p s₁ → p s₂) : p s :=
begin
  have hs' : s ∈ (complete_lattice.Inf {a : filter α | ∃ (i : ι), a = f i}).sets := hs,
  rw [Inf_sets_eq_finite] at hs',
  simp at hs',
  cases hs' with is hs, cases hs with fin_is hs, cases hs with hs his,
  induction fin_is generalizing s,
  case finite.empty hs' s hs' hs {
    simp at hs, subst hs, assumption },
  case finite.insert fi is fi_ne_is fin_is ih fi_sub s hs' hs {
    simp at hs,
    cases hs with s₁ hs, cases hs with hs₁ hs, cases hs with s₂ hs, cases hs with hs hs₂,
    have hi : ∃i, fi = f i := fi_sub (mem_insert _ _),
    cases hi with i hi,
    exact have hs₁ : s₁ ∈ (f i).sets, from hi ▸ hs₁,
    have hs₂ : p s₂, from
      have his : is ⊆ {x | ∃i, x = f i}, from assume i hi, fi_sub $  mem_insert_of_mem _ hi,
      have infi f ≤ Inf is, from Inf_le_Inf his,
      ih his (this hs₂) hs₂,
    show p s, from upw hs $ ins hs₁ hs₂ }
end

lemma lift_infi {f : ι → filter α} {g : set α → filter β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ⊓ g t = g (s ∩ t)) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
    have g_mono : monotone g,
      from assume s t h, le_of_inf_eq $ eq.trans hg $ congr_arg g $ inter_eq_self_of_subset_left h,
    have ∀t∈(infi f).sets, (⨅ (i : ι), filter.lift (f i) g) ≤ g t,
      from assume t ht, infi_sets_induct ht
        (let ⟨i⟩ := hι in infi_le_of_le i $ infi_le_of_le univ $ infi_le _ univ_mem_sets)
        (assume i s₁ s₂ hs₁ hs₂,
          @hg s₁ s₂ ▸ le_inf (infi_le_of_le i $ infi_le_of_le s₁ $ infi_le _ hs₁) hs₂)
        (assume s₁ s₂ hs₁ hs₂, le_trans hs₂ $ g_mono hs₁),
    by rw [lift_sets_eq g_mono]; simp; exact assume ⟨t, hs, ht⟩, this t ht hs)

lemma lift_infi' {f : ι → filter α} {g : set α → filter β}
  (hι : nonempty ι) (hf : directed (≤) f) (hg : monotone g) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
  begin
    rw [lift_sets_eq hg],
    simp [infi_sets_eq hf hι],
    exact assume ⟨t, hs, i, ht⟩, mem_infi_sets i $ mem_lift ht hs
  end)

lemma lift'_infi {f : ι → filter α} {g : set α → set β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ∩ g t = g (s ∩ t)) : (infi f).lift' g = (⨅i, (f i).lift' g) :=
lift_infi hι $ by simp; apply assume s t, hg

lemma map_eq_vmap_of_inverse {f : filter α} {m : α → β} {n : β → α}
  (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = vmap n f :=
le_antisymm
  (assume b ⟨a, ha, (h : preimage n a ⊆ b)⟩, f.upwards_sets ha $
    calc a = preimage (n ∘ m) a : by simp [h₂, preimage_id]
      ... ⊆ preimage m b : preimage_mono h)
  (assume b (hb : preimage m b ∈ f.sets),
    ⟨preimage m b, hb, show preimage (m ∘ n) b ⊆ b, by simp [h₁]; apply subset.refl⟩)

lemma map_swap_vmap_swap_eq {f : filter (α × β)} : prod.swap <$> f = vmap prod.swap f :=
map_eq_vmap_of_inverse prod.swap_swap_eq prod.swap_swap_eq

/- ultrafilter -/

section ultrafilter
open classical zorn
local attribute [instance] prop_decidable

variables {f g : filter α}

def ultrafilter (f : filter α) := f ≠ ⊥ ∧ ∀g, g ≠ ⊥ → g ≤ f → f ≤ g

lemma ultrafilter_pure {a : α} : ultrafilter (pure a) :=
⟨return_neq_bot,
  assume g hg ha,
  have {a} ∈ g.sets, by simp at ha; assumption,
  show ∀s∈g.sets, {a} ⊆ s, from classical.by_contradiction $
  begin
    simp [classical.not_forall_iff, not_implies_iff],
    exact assume ⟨s, hna, hs⟩,
      have {a} ∩ s ∈ g.sets, from inter_mem_sets ‹{a} ∈ g.sets› hs,
      have ∅ ∈ g.sets, from g.upwards_sets this $
        assume x ⟨hxa, hxs⟩, begin simp at hxa; simp [hxa] at hxs, exact hna hxs end,
      have g = ⊥, from empty_in_sets_eq_bot.mp this,
      hg this
  end⟩

lemma ultrafilter_unique (hg : ultrafilter g) (hf : f ≠ ⊥) (h : f ≤ g) : f = g :=
le_antisymm h (hg.right _ hf h)

lemma exists_ultrafilter (h : f ≠ ⊥) : ∃u, u ≤ f ∧ ultrafilter u :=
let
  τ                := {f' // f' ≠ ⊥ ∧ f' ≤ f},
  r : τ → τ → Prop := λt₁ t₂, t₂.val ≤ t₁.val,
  ⟨a, ha⟩          := inhabited_of_mem_sets h univ_mem_sets,
  top : τ          := ⟨f, h, le_refl f⟩,
  sup : Π(c:set τ), chain c → τ :=
    λc hc, ⟨⨅a:{a:τ // a ∈ insert top c}, a.val.val,
      infi_neq_bot_of_directed ⟨a⟩
        (directed_of_chain $ chain_insert hc $ assume ⟨b, _, hb⟩ _ _, or.inl hb)
        (assume ⟨⟨a, ha, _⟩, _⟩, ha),
      infi_le_of_le ⟨top, mem_insert _ _⟩ (le_refl _)⟩
in
have ∀c (hc: chain c) a (ha : a ∈ c), r a (sup c hc),
  from assume c hc a ha, infi_le_of_le ⟨a, mem_insert_of_mem _ ha⟩ (le_refl _),
have (∃ (u : τ), ∀ (a : τ), r u a → r a u),
  from zorn (assume c hc, ⟨sup c hc, this c hc⟩) (assume f₁ f₂ f₃ h₁ h₂, le_trans h₂ h₁),
let ⟨uτ, hmin⟩ := this in
⟨uτ.val, uτ.property.right, uτ.property.left, assume g hg₁ hg₂,
  hmin ⟨g, hg₁, le_trans hg₂ uτ.property.right⟩ hg₂⟩

lemma le_of_ultrafilter {g : filter α} (hf : ultrafilter f) (h : f ⊓ g ≠ ⊥) :
  f ≤ g :=
le_of_inf_eq $ ultrafilter_unique hf h inf_le_left

lemma mem_or_compl_mem_of_ultrafilter (hf : ultrafilter f) (s : set α) :
  s ∈ f.sets ∨ - s ∈ f.sets :=
or_of_not_implies' $ assume : - s ∉ f.sets,
  have f ≤ principal s,
    from le_of_ultrafilter hf $ assume h, this $ mem_sets_of_neq_bot $ by simp [*],
  by simp at this; assumption

lemma mem_or_mem_of_ultrafilter {s t : set α} (hf : ultrafilter f) (h : s ∪ t ∈ f.sets) :
  s ∈ f.sets ∨ t ∈ f.sets :=
(mem_or_compl_mem_of_ultrafilter hf s).imp_right
  (assume : -s ∈ f.sets, f.upwards_sets (inter_mem_sets this h) $
    assume x ⟨hnx, hx⟩, hx.resolve_left hnx)

lemma mem_of_finite_sUnion_ultrafilter {s : set (set α)} (hf : ultrafilter f) (hs : finite s)
  : ⋃₀ s ∈ f.sets → ∃t∈s, t ∈ f.sets :=
begin
  induction hs,
  case finite.empty { simp [empty_in_sets_eq_bot, hf.left] },
  case finite.insert t s' ht' hs' ih {
    simp,
    exact assume h, (mem_or_mem_of_ultrafilter hf h).elim
      (assume : t ∈ f.sets, ⟨t, this, or.inl rfl⟩)
      (assume h, let ⟨t, hts', ht⟩ := ih h in ⟨t, ht, or.inr hts'⟩) }
end

lemma mem_of_finite_Union_ultrafilter {is : set β} {s : β → set α}
  (hf : ultrafilter f) (his : finite is) (h : (⋃i∈is, s i) ∈ f.sets) : ∃i∈is, s i ∈ f.sets :=
have his : finite (image s is), from finite_image his,
have h : (⋃₀ image s is) ∈ f.sets, from by simp [sUnion_image]; assumption,
let ⟨t, ⟨i, hi, h_eq⟩, (ht : t ∈ f.sets)⟩ := mem_of_finite_sUnion_ultrafilter hf his h in
⟨i, hi, h_eq.symm ▸ ht⟩

lemma ultrafilter_of_split {f : filter α} (hf : f ≠ ⊥) (h : ∀s, s ∈ f.sets ∨ - s ∈ f.sets) :
  ultrafilter f :=
⟨hf, assume g hg g_le s hs, (h s).elim id $
  assume : - s ∈ f.sets,
  have s ∩ -s ∈ g.sets, from inter_mem_sets hs (g_le this),
  by simp [empty_in_sets_eq_bot, hg] at this; contradiction⟩

lemma ultrafilter_map {f : filter α} {m : α → β} (h : ultrafilter f) : ultrafilter (map m f) :=
ultrafilter_of_split (by simp [map_eq_bot_iff, h.left]) $
  assume s, show preimage m s ∈ f.sets ∨ - preimage m s ∈ f.sets,
    from mem_or_compl_mem_of_ultrafilter h (preimage m s)

noncomputable def ultrafilter_of (f : filter α) : filter α :=
if h : f = ⊥ then ⊥ else epsilon (λu, u ≤ f ∧ ultrafilter u)

lemma ultrafilter_of_spec (h : f ≠ ⊥) : ultrafilter_of f ≤ f ∧ ultrafilter (ultrafilter_of f) :=
begin
  have h' := epsilon_spec (exists_ultrafilter h),
  simp [ultrafilter_of, dif_neg, h],
  simp at h',
  assumption
end

lemma ultrafilter_of_le : ultrafilter_of f ≤ f :=
if h : f = ⊥ then by simp [ultrafilter_of, dif_pos, h]; exact le_refl _
  else (ultrafilter_of_spec h).left

lemma ultrafilter_ultrafilter_of (h : f ≠ ⊥) : ultrafilter (ultrafilter_of f) :=
(ultrafilter_of_spec h).right

lemma ultrafilter_of_ultrafilter (h : ultrafilter f) : ultrafilter_of f = f :=
ultrafilter_unique h (ultrafilter_ultrafilter_of h.left).left ultrafilter_of_le

end ultrafilter

end filter
