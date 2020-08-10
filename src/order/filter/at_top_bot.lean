/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov, Patrick Massot
-/
import order.filter.bases

/-!
# `at_top` and `at_bot` filters on preorded sets, monoids and groups.

In this file we define the filters

* `at_top`: corresponds to `n → +∞`;
* `at_bot`: corresponds to `n → -∞`.

Then we prove many lemmas like “if `f → +∞`, then `f ± c → +∞`”.
-/

variables {ι ι' α β γ : Type*}

open set
open_locale classical filter big_operators

namespace filter
/-- `at_top` is the filter representing the limit `→ ∞` on an ordered set.
  It is generated by the collection of up-sets `{b | a ≤ b}`.
  (The preorder need not have a top element for this to be well defined,
  and indeed is trivial when a top element exists.) -/
def at_top [preorder α] : filter α := ⨅ a, 𝓟 {b | a ≤ b}

/-- `at_bot` is the filter representing the limit `→ -∞` on an ordered set.
  It is generated by the collection of down-sets `{b | b ≤ a}`.
  (The preorder need not have a bottom element for this to be well defined,
  and indeed is trivial when a bottom element exists.) -/
def at_bot [preorder α] : filter α := ⨅ a, 𝓟 {b | b ≤ a}

lemma mem_at_top [preorder α] (a : α) : {b : α | a ≤ b} ∈ @at_top α _ :=
mem_infi_sets a $ subset.refl _

lemma Ioi_mem_at_top [preorder α] [no_top_order α] (x : α) : Ioi x ∈ (at_top : filter α) :=
let ⟨z, hz⟩ := no_top x in mem_sets_of_superset (mem_at_top z) $ λ y h,  lt_of_lt_of_le hz h

lemma mem_at_bot [preorder α] (a : α) : {b : α | b ≤ a} ∈ @at_bot α _ :=
mem_infi_sets a $ subset.refl _

lemma Iio_mem_at_bot [preorder α] [no_bot_order α] (x : α) : Iio x ∈ (at_bot : filter α) :=
let ⟨z, hz⟩ := no_bot x in mem_sets_of_superset (mem_at_bot z) $ λ y h, lt_of_le_of_lt h hz

lemma at_top_basis [nonempty α] [semilattice_sup α] :
  (@at_top α _).has_basis (λ _, true) Ici :=
has_basis_infi_principal (directed_of_sup $ λ a b, Ici_subset_Ici.2)

lemma at_bot_basis {α : Type*} [nonempty α] [semilattice_inf α] :
  (@at_bot α _).has_basis (λ _, true) Iic :=
has_basis_infi_principal (directed_of_inf $ λ a b, Iic_subset_Iic.2)

lemma at_top_basis' [semilattice_sup α] (a : α) :
  (@at_top α _).has_basis (λ x, a ≤ x) Ici :=
⟨λ t, (@at_top_basis α ⟨a⟩ _).mem_iff.trans
  ⟨λ ⟨x, _, hx⟩, ⟨x ⊔ a, le_sup_right, λ y hy, hx (le_trans le_sup_left hy)⟩,
    λ ⟨x, _, hx⟩, ⟨x, trivial, hx⟩⟩⟩

@[instance]
lemma at_top_ne_bot [nonempty α] [semilattice_sup α] : ne_bot (at_top : filter α) :=
at_top_basis.forall_nonempty_iff_ne_bot.1 $ λ a _, nonempty_Ici

@[simp, nolint ge_or_gt]
lemma mem_at_top_sets [nonempty α] [semilattice_sup α] {s : set α} :
  s ∈ (at_top : filter α) ↔ ∃a:α, ∀b≥a, b ∈ s :=
at_top_basis.mem_iff.trans $ exists_congr $ λ _, exists_const _

@[simp]
lemma mem_at_bot_sets {α : Type*} [nonempty α] [semilattice_inf α] {s : set α} :
  s ∈ (at_bot : filter α) ↔ ∃a:α, ∀b≤a, b ∈ s :=
at_bot_basis.mem_iff.trans $ exists_congr $ λ _, exists_const _

@[simp, nolint ge_or_gt]
lemma eventually_at_top [semilattice_sup α] [nonempty α] {p : α → Prop} :
  (∀ᶠ x in at_top, p x) ↔ (∃ a, ∀ b ≥ a, p b) :=
mem_at_top_sets

lemma eventually_ge_at_top [preorder α] (a : α) : ∀ᶠ x in at_top, a ≤ x := mem_at_top a

lemma at_top_countable_basis [nonempty α] [semilattice_sup α] [encodable α] :
  has_countable_basis (at_top : filter α) (λ _, true) Ici :=
{ countable := countable_encodable _,
  .. at_top_basis }

lemma is_countably_generated_at_top [nonempty α] [semilattice_sup α] [encodable α] :
  (at_top : filter $ α).is_countably_generated :=
at_top_countable_basis.is_countably_generated

lemma order_top.at_top_eq (α) [order_top α] : (at_top : filter α) = pure ⊤ :=
le_antisymm (le_pure_iff.2 $ (eventually_ge_at_top ⊤).mono $ λ b, top_unique)
  (le_infi $ λ b, le_principal_iff.2 le_top)

lemma tendsto_at_top_pure [order_top α] (f : α → β) :
  tendsto f at_top (pure $ f ⊤) :=
(order_top.at_top_eq α).symm ▸ tendsto_pure_pure _ _

@[nolint ge_or_gt]
lemma eventually.exists_forall_of_at_top [semilattice_sup α] [nonempty α] {p : α → Prop}
  (h : ∀ᶠ x in at_top, p x) : ∃ a, ∀ b ≥ a, p b :=
eventually_at_top.mp h

@[nolint ge_or_gt]
lemma frequently_at_top [semilattice_sup α] [nonempty α] {p : α → Prop} :
  (∃ᶠ x in at_top, p x) ↔ (∀ a, ∃ b ≥ a, p b) :=
by simp only [filter.frequently, eventually_at_top, not_exists, not_forall, not_not]

@[nolint ge_or_gt]
lemma frequently_at_top' [semilattice_sup α] [nonempty α] [no_top_order α] {p : α → Prop} :
  (∃ᶠ x in at_top, p x) ↔ (∀ a, ∃ b > a, p b) :=
begin
  rw frequently_at_top,
  split ; intros h a,
  { cases no_top a with a' ha',
    rcases h a' with ⟨b, hb, hb'⟩,
    exact ⟨b, lt_of_lt_of_le ha' hb, hb'⟩ },
  { rcases h a with ⟨b, hb, hb'⟩,
    exact ⟨b, le_of_lt hb, hb'⟩ },
end

@[nolint ge_or_gt]
lemma frequently.forall_exists_of_at_top [semilattice_sup α] [nonempty α] {p : α → Prop}
  (h : ∃ᶠ x in at_top, p x) : ∀ a, ∃ b ≥ a, p b :=
frequently_at_top.mp h

lemma map_at_top_eq [nonempty α] [semilattice_sup α] {f : α → β} :
  at_top.map f = (⨅a, 𝓟 $ f '' {a' | a ≤ a'}) :=
(at_top_basis.map _).eq_infi

lemma tendsto_at_top [preorder β] (m : α → β) (f : filter α) :
  tendsto m f at_top ↔ (∀b, ∀ᶠ a in f, b ≤ m a) :=
by simp only [at_top, tendsto_infi, tendsto_principal, mem_set_of_eq]

lemma tendsto_at_bot [preorder β] (m : α → β) (f : filter α) :
  tendsto m f at_bot ↔ (∀b, ∀ᶠ a in f, m a ≤ b) :=
@tendsto_at_top α (order_dual β) _ m f

lemma tendsto_at_top_mono' [preorder β] (l : filter α) ⦃f₁ f₂ : α → β⦄ (h : f₁ ≤ᶠ[l] f₂) :
  tendsto f₁ l at_top → tendsto f₂ l at_top :=
assume h₁, (tendsto_at_top _ _).2 $ λ b, mp_sets ((tendsto_at_top _ _).1 h₁ b)
  (monotone_mem_sets (λ a ha ha₁, le_trans ha₁ ha) h)

lemma tendsto_at_top_mono [preorder β] {l : filter α} {f g : α → β} (h : ∀ n, f n ≤ g n) :
  tendsto f l at_top → tendsto g l at_top :=
tendsto_at_top_mono' l $ eventually_of_forall h

/-!
### Sequences
-/

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma inf_map_at_top_ne_bot_iff [semilattice_sup α] [nonempty α] {F : filter β} {u : α → β} :
  ne_bot (F ⊓ (map u at_top)) ↔ ∀ U ∈ F, ∀ N, ∃ n ≥ N, u n ∈ U :=
by simp_rw [inf_ne_bot_iff_frequently_left, frequently_map, frequently_at_top]; refl

lemma extraction_of_frequently_at_top' {P : ℕ → Prop} (h : ∀ N, ∃ n > N, P n) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P (φ n) :=
begin
  choose u hu using h,
  cases forall_and_distrib.mp hu with hu hu',
  exact ⟨u ∘ (nat.rec 0 (λ n v, u v)), strict_mono.nat (λ n, hu _), λ n, hu' _⟩,
end

lemma extraction_of_frequently_at_top {P : ℕ → Prop} (h : ∃ᶠ n in at_top, P n) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P (φ n) :=
begin
  rw frequently_at_top' at h,
  exact extraction_of_frequently_at_top' h,
end

lemma extraction_of_eventually_at_top {P : ℕ → Prop} (h : ∀ᶠ n in at_top, P n) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, P (φ n) :=
extraction_of_frequently_at_top h.frequently

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma exists_le_of_tendsto_at_top [semilattice_sup α] [preorder β] {u : α → β}
  (h : tendsto u at_top at_top) : ∀ a b, ∃ a' ≥ a, b ≤ u a' :=
begin
  intros a b,
  have : ∀ᶠ x in at_top, a ≤ x ∧ b ≤ u x :=
    (eventually_ge_at_top a).and (h.eventually $ eventually_ge_at_top b),
  haveI : nonempty α := ⟨a⟩,
  rcases this.exists with ⟨a', ha, hb⟩,
  exact ⟨a', ha, hb⟩
end

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma exists_lt_of_tendsto_at_top [semilattice_sup α] [preorder β] [no_top_order β]
  {u : α → β} (h : tendsto u at_top at_top) : ∀ a b, ∃ a' ≥ a, b < u a' :=
begin
  intros a b,
  cases no_top b with b' hb',
  rcases exists_le_of_tendsto_at_top h a b' with ⟨a', ha', ha''⟩,
  exact ⟨a', ha', lt_of_lt_of_le hb' ha''⟩
end

/--
If `u` is a sequence which is unbounded above,
then after any point, it reaches a value strictly greater than all previous values.
-/
@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma high_scores [linear_order β] [no_top_order β] {u : ℕ → β}
  (hu : tendsto u at_top at_top) : ∀ N, ∃ n ≥ N, ∀ k < n, u k < u n :=
begin
  letI := classical.DLO β,
  intros N,
  let A := finset.image u (finset.range $ N+1), -- A = {u 0, ..., u N}
  have Ane : A.nonempty,
    from ⟨u 0, finset.mem_image_of_mem _ (finset.mem_range.mpr $ nat.zero_lt_succ _)⟩,
  let M := finset.max' A Ane,
  have ex : ∃ n ≥ N, M < u n,
    from exists_lt_of_tendsto_at_top hu _ _,
  obtain ⟨n, hnN, hnM, hn_min⟩ : ∃ n, N ≤ n ∧ M < u n ∧ ∀ k, N ≤ k → k < n → u k ≤ M,
  { use nat.find ex,
    rw ← and_assoc,
    split,
    { simpa using nat.find_spec ex },
    { intros k hk hk',
      simpa [hk] using nat.find_min ex hk' } },
  use [n, hnN],
  intros k hk,
  by_cases H : k ≤ N,
  { have : u k ∈ A,
      from finset.mem_image_of_mem _ (finset.mem_range.mpr $ nat.lt_succ_of_le H),
    have : u k ≤ M,
      from finset.le_max' A Ane (u k) this,
    exact lt_of_le_of_lt this hnM },
  { push_neg at H,
    calc u k ≤ M   : hn_min k (le_of_lt H) hk
         ... < u n : hnM },
end

/--
If `u` is a sequence which is unbounded above,
then it `frequently` reaches a value strictly greater than all previous values.
-/
lemma frequently_high_scores [linear_order β] [no_top_order β] {u : ℕ → β}
  (hu : tendsto u at_top at_top) : ∃ᶠ n in at_top, ∀ k < n, u k < u n :=
by simpa [frequently_at_top] using high_scores hu

lemma strict_mono_subseq_of_tendsto_at_top
  {β : Type*} [linear_order β] [no_top_order β]
  {u : ℕ → β} (hu : tendsto u at_top at_top) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ strict_mono (u ∘ φ) :=
let ⟨φ, h, h'⟩ := extraction_of_frequently_at_top (frequently_high_scores hu) in
⟨φ, h, λ n m hnm, h' m _ (h hnm)⟩

lemma strict_mono_subseq_of_id_le {u : ℕ → ℕ} (hu : ∀ n, n ≤ u n) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ strict_mono (u ∘ φ) :=
strict_mono_subseq_of_tendsto_at_top (tendsto_at_top_mono hu tendsto_id)

lemma strict_mono_tendsto_at_top {φ : ℕ → ℕ} (h : strict_mono φ) :
  tendsto φ at_top at_top :=
tendsto_at_top_mono h.id_le tendsto_id

section ordered_add_comm_monoid

variables [ordered_add_comm_monoid β] {l : filter α} {f g : α → β}

lemma tendsto_at_top_add_nonneg_left' (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : tendsto g l at_top) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_mono' l (hf.mono (λ x, le_add_of_nonneg_left)) hg

lemma tendsto_at_top_add_nonneg_left (hf : ∀ x, 0 ≤ f x) (hg : tendsto g l at_top) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_add_nonneg_left' (eventually_of_forall hf) hg

lemma tendsto_at_top_add_nonneg_right' (hf : tendsto f l at_top) (hg : ∀ᶠ x in l, 0 ≤ g x) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_mono' l (monotone_mem_sets (λ x, le_add_of_nonneg_right) hg) hf

lemma tendsto_at_top_add_nonneg_right (hf : tendsto f l at_top) (hg : ∀ x, 0 ≤ g x) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_add_nonneg_right' hf (eventually_of_forall hg)

end ordered_add_comm_monoid

section ordered_cancel_add_comm_monoid

variables [ordered_cancel_add_comm_monoid β] {l : filter α} {f g : α → β}

lemma tendsto_at_top_of_add_const_left (C : β) (hf : tendsto (λ x, C + f x) l at_top) :
  tendsto f l at_top :=
(tendsto_at_top _ l).2 $ assume b,
  ((tendsto_at_top _ _).1 hf (C + b)).mono (λ x, le_of_add_le_add_left)

lemma tendsto_at_top_of_add_const_right (C : β) (hf : tendsto (λ x, f x + C) l at_top) :
  tendsto f l at_top :=
(tendsto_at_top _ l).2 $ assume b,
  ((tendsto_at_top _ _).1 hf (b + C)).mono (λ x, le_of_add_le_add_right)

lemma tendsto_at_top_of_add_bdd_above_left' (C) (hC : ∀ᶠ x in l, f x ≤ C)
  (h : tendsto (λ x, f x + g x) l at_top) :
  tendsto g l at_top :=
tendsto_at_top_of_add_const_left C
  (tendsto_at_top_mono' l (hC.mono (λ x hx, add_le_add_right hx (g x))) h)

lemma tendsto_at_top_of_add_bdd_above_left (C) (hC : ∀ x, f x ≤ C) :
  tendsto (λ x, f x + g x) l at_top → tendsto g l at_top :=
tendsto_at_top_of_add_bdd_above_left' C (univ_mem_sets' hC)

lemma tendsto_at_top_of_add_bdd_above_right' (C) (hC : ∀ᶠ x in l, g x ≤ C)
  (h : tendsto (λ x, f x + g x) l at_top) :
  tendsto f l at_top :=
tendsto_at_top_of_add_const_right C
  (tendsto_at_top_mono' l (hC.mono (λ x hx, add_le_add_left hx (f x))) h)

lemma tendsto_at_top_of_add_bdd_above_right (C) (hC : ∀ x, g x ≤ C) :
  tendsto (λ x, f x + g x) l at_top → tendsto f l at_top :=
tendsto_at_top_of_add_bdd_above_right' C (univ_mem_sets' hC)

end ordered_cancel_add_comm_monoid

section ordered_group

variables [ordered_add_comm_group β] (l : filter α) {f g : α → β}

lemma tendsto_at_top_add_left_of_le' (C : β) (hf : ∀ᶠ x in l, C ≤ f x) (hg : tendsto g l at_top) :
  tendsto (λ x, f x + g x) l at_top :=
@tendsto_at_top_of_add_bdd_above_left' _ _ _ l (λ x, -(f x)) (λ x, f x + g x) (-C)
  (by simpa) (by simpa)

lemma tendsto_at_top_add_left_of_le (C : β) (hf : ∀ x, C ≤ f x) (hg : tendsto g l at_top) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_add_left_of_le' l C (univ_mem_sets' hf) hg

lemma tendsto_at_top_add_right_of_le' (C : β) (hf : tendsto f l at_top) (hg : ∀ᶠ x in l, C ≤ g x) :
  tendsto (λ x, f x + g x) l at_top :=
@tendsto_at_top_of_add_bdd_above_right' _ _ _ l (λ x, f x + g x) (λ x, -(g x)) (-C)
  (by simp [hg]) (by simp [hf])

lemma tendsto_at_top_add_right_of_le (C : β) (hf : tendsto f l at_top) (hg : ∀ x, C ≤ g x) :
  tendsto (λ x, f x + g x) l at_top :=
tendsto_at_top_add_right_of_le' l C hf (univ_mem_sets' hg)

lemma tendsto_at_top_add_const_left (C : β) (hf : tendsto f l at_top) :
  tendsto (λ x, C + f x) l at_top :=
tendsto_at_top_add_left_of_le' l C (univ_mem_sets' $ λ _, le_refl C) hf

lemma tendsto_at_top_add_const_right (C : β) (hf : tendsto f l at_top) :
  tendsto (λ x, f x + C) l at_top :=
tendsto_at_top_add_right_of_le' l C hf (univ_mem_sets' $ λ _, le_refl C)

end ordered_group

open_locale filter

@[nolint ge_or_gt]
lemma tendsto_at_top' [nonempty α] [semilattice_sup α] (f : α → β) (l : filter β) :
  tendsto f at_top l ↔ (∀s ∈ l, ∃a, ∀b≥a, f b ∈ s) :=
by simp only [tendsto_def, mem_at_top_sets]; refl

lemma tendsto_at_bot' [nonempty α] [semilattice_inf α] (f : α → β) (l : filter β) :
  tendsto f at_bot l ↔ (∀s ∈ l, ∃a, ∀b≤a, f b ∈ s) :=
@tendsto_at_top' (order_dual α) _ _ _ _ _

@[nolint ge_or_gt]
theorem tendsto_at_top_principal [nonempty β] [semilattice_sup β] {f : β → α} {s : set α} :
  tendsto f at_top (𝓟 s) ↔ ∃N, ∀n≥N, f n ∈ s :=
by rw [tendsto_iff_comap, comap_principal, le_principal_iff, mem_at_top_sets]; refl

/-- A function `f` grows to infinity independent of an order-preserving embedding `e`. -/
lemma tendsto_at_top_embedding [preorder β] [preorder γ]
  {f : α → β} {e : β → γ} {l : filter α}
  (hm : ∀b₁ b₂, e b₁ ≤ e b₂ ↔ b₁ ≤ b₂) (hu : ∀c, ∃b, c ≤ e b) :
  tendsto (e ∘ f) l at_top ↔ tendsto f l at_top :=
begin
  rw [tendsto_at_top, tendsto_at_top],
  split,
  { assume hc b,
    filter_upwards [hc (e b)] assume a, (hm b (f a)).1 },
  { assume hb c,
    rcases hu c with ⟨b, hc⟩,
    filter_upwards [hb b] assume a ha, le_trans hc ((hm b (f a)).2 ha) }
end

lemma tendsto_at_top_at_top [nonempty α] [semilattice_sup α] [preorder β] (f : α → β) :
  tendsto f at_top at_top ↔ ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → b ≤ f a :=
iff.trans tendsto_infi $ forall_congr $ assume b, tendsto_at_top_principal

lemma tendsto_at_top_at_bot [nonempty α] [semilattice_sup α] [preorder β] (f : α → β) :
  tendsto f at_top at_bot ↔ ∀ (b : β), ∃ (i : α), ∀ (a : α), i ≤ a → f a ≤ b :=
@tendsto_at_top_at_top α (order_dual β) _ _ _ f

lemma tendsto_at_bot_at_top [nonempty α] [semilattice_inf α] [preorder β] (f : α → β) :
  tendsto f at_bot at_top ↔ ∀ (b : β), ∃ (i : α), ∀ (a : α), a ≤ i → b ≤ f a :=
@tendsto_at_top_at_top (order_dual α) β _ _ _ f

lemma tendsto_at_bot_at_bot [nonempty α] [semilattice_inf α] [preorder β] (f : α → β) :
  tendsto f at_bot at_bot ↔ ∀ (b : β), ∃ (i : α), ∀ (a : α), a ≤ i → f a ≤ b :=
@tendsto_at_top_at_top (order_dual α) (order_dual β) _ _ _ f

lemma tendsto_at_top_at_top_of_monotone [preorder α] [preorder β] {f : α → β} (hf : monotone f)
  (h : ∀ b, ∃ a, b ≤ f a) :
  tendsto f at_top at_top :=
tendsto_infi.2 $ λ b, tendsto_principal.2 $ let ⟨a, ha⟩ := h b in
mem_sets_of_superset (mem_at_top a) $ λ a' ha', le_trans ha (hf ha')

lemma tendsto_at_top_at_top_iff_of_monotone [nonempty α] [semilattice_sup α] [preorder β]
  {f : α → β} (hf : monotone f) :
  tendsto f at_top at_top ↔ ∀ b : β, ∃ a : α, b ≤ f a :=
(tendsto_at_top_at_top f).trans $ forall_congr $ λ b, exists_congr $ λ a,
  ⟨λ h, h a (le_refl a), λ h a' ha', le_trans h $ hf ha'⟩

alias tendsto_at_top_at_top_of_monotone ← monotone.tendsto_at_top_at_top
alias tendsto_at_top_at_top_iff_of_monotone ← monotone.tendsto_at_top_at_top_iff

lemma tendsto_finset_range : tendsto finset.range at_top at_top :=
finset.range_mono.tendsto_at_top_at_top finset.exists_nat_subset_range

lemma at_top_finset_eq_infi : (at_top : filter $ finset α) = ⨅ x : α, 𝓟 (Ici {x}) :=
begin
  refine le_antisymm (le_infi (λ i, le_principal_iff.2 $ mem_at_top {i})) _,
  refine le_infi (λ s, le_principal_iff.2 $ mem_infi_iff.2 _),
  refine ⟨↑s, s.finite_to_set, _, λ i, mem_principal_self _, _⟩,
  simp only [subset_def, mem_Inter, set_coe.forall, mem_Ici, finset.le_iff_subset,
    finset.mem_singleton, finset.subset_iff, forall_eq], dsimp,
  exact λ t, id
end

/-- If `f` is a monotone sequence of `finset`s and each `x` belongs to one of `f n`, then
`tendsto f at_top at_top`. -/
lemma monotone.tendsto_at_top_finset [preorder β]
  {f : β → finset α} (h : monotone f) (h' : ∀ x : α, ∃ n, x ∈ f n) :
  tendsto f at_top at_top :=
begin
  simp only [at_top_finset_eq_infi, tendsto_infi, tendsto_principal],
  intro a,
  rcases h' a with ⟨b, hb⟩,
  exact eventually.mono (mem_at_top b)
    (λ b' hb', le_trans (finset.singleton_subset_iff.2 hb) (h hb')),
end

lemma tendsto_finset_image_at_top_at_top {i : β → γ} {j : γ → β} (h : function.left_inverse j i) :
  tendsto (finset.image j) at_top at_top :=
(finset.image_mono j).tendsto_at_top_at_top $ assume s,
  ⟨s.image i, by simp only [finset.image_image, h.comp_eq_id, finset.image_id, le_refl]⟩

lemma prod_at_top_at_top_eq {β₁ β₂ : Type*} [semilattice_sup β₁] [semilattice_sup β₂] :
  (at_top : filter β₁) ×ᶠ (at_top : filter β₂) = (at_top : filter (β₁ × β₂)) :=
begin
  by_cases ne : nonempty β₁ ∧ nonempty β₂,
  { cases ne,
    resetI,
    simp [at_top, prod_infi_left, prod_infi_right, infi_prod],
    exact infi_comm },
  { rw not_and_distrib at ne,
    cases ne;
    { have : ¬ (nonempty (β₁ × β₂)), by simp [ne],
      rw [at_top.filter_eq_bot_of_not_nonempty ne, at_top.filter_eq_bot_of_not_nonempty this],
      simp only [bot_prod, prod_bot] } }
end

lemma prod_map_at_top_eq {α₁ α₂ β₁ β₂ : Type*} [semilattice_sup β₁] [semilattice_sup β₂]
  (u₁ : β₁ → α₁) (u₂ : β₂ → α₂) :
  (map u₁ at_top) ×ᶠ (map u₂ at_top) = map (prod.map u₁ u₂) at_top :=
by rw [prod_map_map_eq, prod_at_top_at_top_eq, prod.map_def]

/-- A function `f` maps upwards closed sets (at_top sets) to upwards closed sets when it is a
Galois insertion. The Galois "insertion" and "connection" is weakened to only require it to be an
insertion and a connetion above `b'`. -/
lemma map_at_top_eq_of_gc [semilattice_sup α] [semilattice_sup β] {f : α → β} (g : β → α) (b' : β)
  (hf : monotone f) (gc : ∀a, ∀b≥b', f a ≤ b ↔ a ≤ g b) (hgi : ∀b≥b', b ≤ f (g b)) :
  map f at_top = at_top :=
begin
  rw [@map_at_top_eq α _ ⟨g b'⟩],
  refine le_antisymm
    (le_infi $ assume b, infi_le_of_le (g (b ⊔ b')) $ principal_mono.2 $ image_subset_iff.2 _)
    (le_infi $ assume a, infi_le_of_le (f a ⊔ b') $ principal_mono.2 _),
  { assume a ha, exact (le_trans le_sup_left $ le_trans (hgi _ le_sup_right) $ hf ha) },
  { assume b hb,
    have hb' : b' ≤ b := le_trans le_sup_right hb,
    exact ⟨g b, (gc _ _ hb').1 (le_trans le_sup_left hb),
      le_antisymm ((gc _ _ hb').2 (le_refl _)) (hgi _ hb')⟩ }
end

lemma map_add_at_top_eq_nat (k : ℕ) : map (λa, a + k) at_top = at_top :=
map_at_top_eq_of_gc (λa, a - k) k
  (assume a b h, add_le_add_right h k)
  (assume a b h, (nat.le_sub_right_iff_add_le h).symm)
  (assume a h, by rw [nat.sub_add_cancel h])

lemma map_sub_at_top_eq_nat (k : ℕ) : map (λa, a - k) at_top = at_top :=
map_at_top_eq_of_gc (λa, a + k) 0
  (assume a b h, nat.sub_le_sub_right h _)
  (assume a b _, nat.sub_le_right_iff_le_add)
  (assume b _, by rw [nat.add_sub_cancel])

lemma tendsto_add_at_top_nat (k : ℕ) : tendsto (λa, a + k) at_top at_top :=
le_of_eq (map_add_at_top_eq_nat k)

lemma tendsto_sub_at_top_nat (k : ℕ) : tendsto (λa, a - k) at_top at_top :=
le_of_eq (map_sub_at_top_eq_nat k)

lemma tendsto_add_at_top_iff_nat {f : ℕ → α} {l : filter α} (k : ℕ) :
  tendsto (λn, f (n + k)) at_top l ↔ tendsto f at_top l :=
show tendsto (f ∘ (λn, n + k)) at_top l ↔ tendsto f at_top l,
  by rw [← tendsto_map'_iff, map_add_at_top_eq_nat]

lemma map_div_at_top_eq_nat (k : ℕ) (hk : k > 0) : map (λa, a / k) at_top = at_top :=
map_at_top_eq_of_gc (λb, b * k + (k - 1)) 1
  (assume a b h, nat.div_le_div_right h)
  (assume a b _,
    calc a / k ≤ b ↔ a / k < b + 1 : by rw [← nat.succ_eq_add_one, nat.lt_succ_iff]
      ... ↔ a < (b + 1) * k : nat.div_lt_iff_lt_mul _ _ hk
      ... ↔ _ :
      begin
        cases k,
        exact (lt_irrefl _ hk).elim,
        simp [mul_add, add_mul, nat.succ_add, nat.lt_succ_iff]
      end)
  (assume b _,
    calc b = (b * k) / k : by rw [nat.mul_div_cancel b hk]
      ... ≤ (b * k + (k - 1)) / k : nat.div_le_div_right $ nat.le_add_right _ _)

/-- If `u` is a monotone function with linear ordered codomain and the range of `u` is not bounded
above, then `tendsto u at_top at_top`. -/
lemma tendsto_at_top_at_top_of_monotone' [preorder ι] [linear_order α]
  {u : ι → α} (h : monotone u) (H : ¬bdd_above (range u)) :
  tendsto u at_top at_top :=
begin
  apply h.tendsto_at_top_at_top,
  intro b,
  rcases not_bdd_above_iff.1 H b with ⟨_, ⟨N, rfl⟩, hN⟩,
  exact ⟨N, le_of_lt hN⟩,
end

lemma unbounded_of_tendsto_at_top [nonempty α] [semilattice_sup α] [preorder β] [no_top_order β]
  {f : α → β} (h : tendsto f at_top at_top) :
  ¬ bdd_above (range f) :=
begin
  rintros ⟨M, hM⟩,
  cases mem_at_top_sets.mp (h $ Ioi_mem_at_top M) with a ha,
  apply lt_irrefl M,
  calc
  M < f a : ha a (le_refl _)
  ... ≤ M : hM (set.mem_range_self a)
end

/-- If a monotone function `u : ι → α` tends to `at_top` along *some* non-trivial filter `l`, then
it tends to `at_top` along `at_top`. -/
lemma tendsto_at_top_of_monotone_of_filter [preorder ι] [preorder α] {l : filter ι}
  {u : ι → α} (h : monotone u) [ne_bot l] (hu : tendsto u l at_top) :
  tendsto u at_top at_top :=
h.tendsto_at_top_at_top $ λ b, (hu.eventually (mem_at_top b)).exists

lemma tendsto_at_top_of_monotone_of_subseq [preorder ι] [preorder α] {u : ι → α}
  {φ : ι' → ι} (h : monotone u) {l : filter ι'} [ne_bot l]
  (H : tendsto (u ∘ φ) l at_top) :
  tendsto u at_top at_top :=
tendsto_at_top_of_monotone_of_filter h (tendsto_map' H)

lemma tendsto_neg_at_top_at_bot [ordered_add_comm_group α] :
  tendsto (has_neg.neg : α → α) at_top at_bot :=
begin
  simp only [tendsto_at_bot, neg_le],
  exact λ b, eventually_ge_at_top _
end

lemma tendsto_neg_at_bot_at_top [ordered_add_comm_group α] :
  tendsto (has_neg.neg : α → α) at_bot at_top :=
@tendsto_neg_at_top_at_bot (order_dual α) _

/-- Let `f` and `g` be two maps to the same commutative monoid. This lemma gives a sufficient
condition for comparison of the filter `at_top.map (λ s, ∏ b in s, f b)` with
`at_top.map (λ s, ∏ b in s, g b)`. This is useful to compare the set of limit points of
`Π b in s, f b` as `s → at_top` with the similar set for `g`. -/
@[to_additive]
lemma map_at_top_finset_prod_le_of_prod_eq [comm_monoid α] {f : β → α} {g : γ → α}
  (h_eq : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ ∏ x in u', g x = ∏ b in v', f b) :
  at_top.map (λs:finset β, ∏ b in s, f b) ≤ at_top.map (λs:finset γ, ∏ x in s, g x) :=
by rw [map_at_top_eq, map_at_top_eq];
from (le_infi $ assume b, let ⟨v, hv⟩ := h_eq b in infi_le_of_le v $
  by simp [set.image_subset_iff]; exact hv)

lemma has_antimono_basis.tendsto [semilattice_sup ι] [nonempty ι] {l : filter α}
  {p : ι → Prop} {s : ι → set α} (hl : l.has_antimono_basis p s) {φ : ι → α}
  (h : ∀ i : ι, φ i ∈ s i) : tendsto φ at_top l  :=
(at_top_basis.tendsto_iff hl.to_has_basis).2 $ assume i hi,
  ⟨i, trivial, λ j hij, hl.decreasing hi (hl.mono hij hi) hij (h j)⟩

namespace is_countably_generated

/-- An abstract version of continuity of sequentially continuous functions on metric spaces:
if a filter `k` is countably generated then `tendsto f k l` iff for every sequence `u`
converging to `k`, `f ∘ u` tends to `l`. -/
lemma tendsto_iff_seq_tendsto {f : α → β} {k : filter α} {l : filter β}
  (hcb : k.is_countably_generated) :
  tendsto f k l ↔ (∀ x : ℕ → α, tendsto x at_top k → tendsto (f ∘ x) at_top l) :=
suffices (∀ x : ℕ → α, tendsto x at_top k → tendsto (f ∘ x) at_top l) → tendsto f k l,
  from ⟨by intros; apply tendsto.comp; assumption, by assumption⟩,
begin
  rcases hcb.exists_antimono_seq with ⟨g, gmon, gbasis⟩,
  have gbasis : k.has_basis (λ _, true) (λ i, (g i)),
  { subst gbasis,
    exact has_basis_infi_principal (directed_of_sup gmon) },
  contrapose,
  simp only [not_forall, gbasis.tendsto_left_iff, exists_const, not_exists, not_imp],
  rintro ⟨B, hBl, hfBk⟩,
  choose x h using hfBk,
  use x, split,
  { exact (at_top_basis.tendsto_iff gbasis).2 (λ i _, ⟨i, trivial, λ j hj, gmon hj (h j).1⟩) },
  { simp only [tendsto_at_top', (∘), not_forall, not_exists],
    use [B, hBl],
    intro i, use [i, (le_refl _)],
    apply (h i).right },
end

lemma tendsto_of_seq_tendsto {f : α → β} {k : filter α} {l : filter β}
  (hcb : k.is_countably_generated) :
  (∀ x : ℕ → α, tendsto x at_top k → tendsto (f ∘ x) at_top l) → tendsto f k l :=
hcb.tendsto_iff_seq_tendsto.2

lemma subseq_tendsto {f : filter α} (hf : is_countably_generated f)
  {u : ℕ → α}
  (hx : ne_bot (f ⊓ map u at_top)) :
  ∃ (θ : ℕ → ℕ), (strict_mono θ) ∧ (tendsto (u ∘ θ) at_top f) :=
begin
  rcases hf.has_antimono_basis with ⟨B, h⟩,
  have : ∀ N, ∃ n ≥ N, u n ∈ B N,
    from λ N, filter.inf_map_at_top_ne_bot_iff.mp hx _ (h.to_has_basis.mem_of_mem trivial) N,
  choose φ hφ using this,
  cases forall_and_distrib.mp hφ with φ_ge φ_in,
  have lim_uφ : tendsto (u ∘ φ) at_top f,
    from h.tendsto φ_in,
  have lim_φ : tendsto φ at_top at_top,
    from (tendsto_at_top_mono φ_ge tendsto_id),
  obtain ⟨ψ, hψ, hψφ⟩ : ∃ ψ : ℕ → ℕ, strict_mono ψ ∧ strict_mono (φ ∘ ψ),
    from strict_mono_subseq_of_tendsto_at_top lim_φ,
  exact ⟨φ ∘ ψ, hψφ, lim_uφ.comp $ strict_mono_tendsto_at_top hψ⟩,
end

end is_countably_generated

end filter

open filter finset

/-- Let `g : γ → β` be an injective function and `f : β → α` be a function from the codomain of `g`
to a commutative monoid. Suppose that `f x = 1` outside of the range of `g`. Then the filters
`at_top.map (λ s, ∏ i in s, f (g i))` and `at_top.map (λ s, ∏ i in s, f i)` coincide.

The additive version of this lemma is used to prove the equality `∑' x, f (g x) = ∑' y, f y` under
the same assumptions.-/
@[to_additive]
lemma function.injective.map_at_top_finset_prod_eq [comm_monoid α] {g : γ → β}
  (hg : function.injective g) {f : β → α} (hf : ∀ x ∉ set.range g, f x = 1) :
  map (λ s, ∏ i in s, f (g i)) at_top = map (λ s, ∏ i in s, f i) at_top :=
begin
  apply le_antisymm; refine map_at_top_finset_prod_le_of_prod_eq (λ s, _),
  { refine ⟨s.preimage (hg.inj_on _), λ t ht, _⟩,
    refine ⟨t.image g ∪ s, finset.subset_union_right _ _, _⟩,
    rw [← finset.prod_image (hg.inj_on _)],
    refine (prod_subset (subset_union_left _ _) _).symm,
    simp only [finset.mem_union, finset.mem_image],
    refine λ y hy hyt, hf y (mt _ hyt),
    rintros ⟨x, rfl⟩,
    exact ⟨x, ht (finset.mem_preimage.2 $ hy.resolve_left hyt), rfl⟩ },
  { refine ⟨s.image g, λ t ht, _⟩,
    simp only [← prod_preimage _ _ (hg.inj_on _) _ (λ x _, hf x)],
    exact ⟨_, (image_subset_iff_subset_preimage _).1 ht, rfl⟩ }
end

/-- Let `g : γ → β` be an injective function and `f : β → α` be a function from the codomain of `g`
to an additive commutative monoid. Suppose that `f x = 0` outside of the range of `g`. Then the
filters `at_top.map (λ s, ∑ i in s, f (g i))` and `at_top.map (λ s, ∑ i in s, f i)` coincide.

This lemma is used to prove the equality `∑' x, f (g x) = ∑' y, f y` under
the same assumptions.-/
add_decl_doc function.injective.map_at_top_finset_sum_eq
