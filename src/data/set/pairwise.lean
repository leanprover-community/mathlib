/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.lattice

/-!
# Relations holding pairwise

This file defines pairwise relations and pairwise disjoint indexed sets.

## Main declarations

* `pairwise`: `pairwise r` states that `r i j` for all `i ≠ j`.
* `set.pairwise_on`: `s.pairwise_on r` states that `r i j` for all `i ≠ j` with `i, j ∈ s`.
* `set.pairwise_disjoint`: `s.pairwise_disjoint f` states that images under `f` of distinct elements
  of `s` are either equal or `disjoint`.
-/

open set

variables {α ι ι' : Type*} {r p q : α → α → Prop}

section pairwise
variables {f : ι → α} {s t u : set α} {a b : α}

/-- A relation `r` holds pairwise if `r i j` for all `i ≠ j`. -/
def pairwise (r : α → α → Prop) := ∀ i j, i ≠ j → r i j

lemma pairwise.mono (hr : pairwise r) (h : ∀ ⦃i j⦄, r i j → p i j) : pairwise p :=
λ i j hij, h $ hr i j hij

lemma pairwise_on_bool (hr : symmetric r) {a b : α} : pairwise (r on (λ c, cond c a b)) ↔ r a b :=
by simpa [pairwise, function.on_fun] using @hr a b

lemma pairwise_disjoint_on_bool [semilattice_inf_bot α] {a b : α} :
  pairwise (disjoint on (λ c, cond c a b)) ↔ disjoint a b :=
pairwise_on_bool disjoint.symm

lemma symmetric.pairwise_on [linear_order ι] (hr : symmetric r) (f : ι → α) :
  pairwise (r on f) ↔ ∀ m n, m < n → r (f m) (f n) :=
⟨λ h m n hmn, h m n hmn.ne, λ h m n hmn, begin
  obtain hmn' | hmn' := hmn.lt_or_lt,
  { exact h _ _ hmn' },
  { exact hr (h _ _ hmn') }
end⟩

lemma pairwise_disjoint_on [semilattice_inf_bot α] [linear_order ι] (f : ι → α) :
  pairwise (disjoint on f) ↔ ∀ m n, m < n → disjoint (f m) (f n) :=
symmetric.pairwise_on disjoint.symm f

namespace set

/-- The relation `r` holds pairwise on the set `s` if `r x y` for all *distinct* `x y ∈ s`. -/
def pairwise_on (s : set α) (r : α → α → Prop) := ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r x y

lemma pairwise_on_of_forall (s : set α) (r : α → α → Prop) (h : ∀ a b, r a b) : s.pairwise_on r :=
λ a _ b _ _, h a b

lemma pairwise_on.imp_on (h : s.pairwise_on r) (hrp : s.pairwise_on (λ ⦃a b : α⦄, r a b → p a b)) :
  s.pairwise_on p :=
λ a ha b hb hab, hrp a ha b hb hab (h a ha b hb hab)

lemma pairwise_on.imp (h : s.pairwise_on r) (hpq : ∀ ⦃a b : α⦄, r a b → p a b) : s.pairwise_on p :=
h.imp_on $ pairwise_on_of_forall s _ hpq

lemma pairwise_on.mono (h : t ⊆ s) (hs : s.pairwise_on r) : t.pairwise_on r :=
λ x xt y yt, hs x (h xt) y (h yt)

lemma pairwise_on.mono' (H : r ≤ p) (hr : s.pairwise_on r) : s.pairwise_on p := hr.imp H

lemma pairwise_on_top (s : set α) : s.pairwise_on ⊤ := pairwise_on_of_forall s _ (λ a b, trivial)

protected lemma subsingleton.pairwise_on (h : s.subsingleton) (r : α → α → Prop) :
  s.pairwise_on r :=
λ x hx y hy hne, (hne (h hx hy)).elim

@[simp] lemma pairwise_on_empty (r : α → α → Prop) : (∅ : set α).pairwise_on r :=
subsingleton_empty.pairwise_on r

@[simp] lemma pairwise_on_singleton (a : α) (r : α → α → Prop) : pairwise_on {a} r :=
subsingleton_singleton.pairwise_on r

lemma nonempty.pairwise_on_iff_exists_forall [is_equiv α r] {s : set ι} (hs : s.nonempty) :
  (s.pairwise_on (r on f)) ↔ ∃ z, ∀ x ∈ s, r (f x) z :=
begin
  fsplit,
  { rcases hs with ⟨y, hy⟩,
    refine λ H, ⟨f y, λ x hx, _⟩,
    rcases eq_or_ne x y with rfl|hne,
    { apply is_refl.refl },
    { exact H _ hx _ hy hne } },
  { rintro ⟨z, hz⟩ x hx y hy hne,
    exact @is_trans.trans α r _ (f x) z (f y) (hz _ hx) (is_symm.symm _ _ $ hz _ hy) }
end

/-- For a nonempty set `s`, a function `f` takes pairwise equal values on `s` if and only if
for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`set.pairwise_on_eq_iff_exists_eq` for a version that assumes `[nonempty ι]` instead of
`set.nonempty s`. -/
lemma nonempty.pairwise_on_eq_iff_exists_eq {s : set α} (hs : s.nonempty) {f : α → ι} :
  (s.pairwise_on (λ x y, f x = f y)) ↔ ∃ z, ∀ x ∈ s, f x = z :=
hs.pairwise_on_iff_exists_forall

lemma pairwise_on_iff_exists_forall [nonempty ι] (s : set α) (f : α → ι) {r : ι → ι → Prop}
  [is_equiv ι r] :
  (s.pairwise_on (r on f)) ↔ ∃ z, ∀ x ∈ s, r (f x) z :=
begin
  rcases s.eq_empty_or_nonempty with rfl|hne,
  { simp },
  { exact hne.pairwise_on_iff_exists_forall }
end

/-- A function `f : α → ι` with nonempty codomain takes pairwise equal values on a set `s` if and
only if for some `z` in the codomain, `f` takes value `z` on all `x ∈ s`. See also
`set.nonempty.pairwise_on_eq_iff_exists_eq` for a version that assumes `set.nonempty s` instead of
`[nonempty ι]`. -/
lemma pairwise_on_eq_iff_exists_eq [nonempty ι] (s : set α) (f : α → ι) :
  (s.pairwise_on (λ x y, f x = f y)) ↔ ∃ z, ∀ x ∈ s, f x = z :=
pairwise_on_iff_exists_forall s f

lemma pairwise_on_union :
  (s ∪ t).pairwise_on r ↔
    s.pairwise_on r ∧ t.pairwise_on r ∧ ∀ (a ∈ s) (b ∈ t), a ≠ b → r a b ∧ r b a :=
begin
  simp only [pairwise_on, mem_union_eq, or_imp_distrib, forall_and_distrib],
  exact ⟨λ H, ⟨H.1.1, H.2.2, H.2.1, λ x hx y hy hne, H.1.2 y hy x hx hne.symm⟩,
    λ H, ⟨⟨H.1, λ x hx y hy hne, H.2.2.2 y hy x hx hne.symm⟩, H.2.2.1, H.2.1⟩⟩
end

lemma pairwise_on_union_of_symmetric (hr : symmetric r) :
  (s ∪ t).pairwise_on r ↔
    s.pairwise_on r ∧ t.pairwise_on r ∧ ∀ (a ∈ s) (b ∈ t), a ≠ b → r a b :=
pairwise_on_union.trans $ by simp only [hr.iff, and_self]

lemma pairwise_on_insert :
  (insert a s).pairwise_on r ↔ s.pairwise_on r ∧ ∀ b ∈ s, a ≠ b → r a b ∧ r b a :=
by simp only [insert_eq, pairwise_on_union, pairwise_on_singleton, true_and,
  mem_singleton_iff, forall_eq]

lemma pairwise_on_insert_of_symmetric (hr : symmetric r) :
  (insert a s).pairwise_on r ↔ s.pairwise_on r ∧ ∀ b ∈ s, a ≠ b → r a b :=
by simp only [pairwise_on_insert, hr.iff a, and_self]

lemma pairwise_on_pair : pairwise_on {a, b} r ↔ (a ≠ b → r a b ∧ r b a) :=
by simp [pairwise_on_insert]

lemma pairwise_on_pair_of_symmetric (hr : symmetric r) : pairwise_on {a, b} r ↔ (a ≠ b → r a b) :=
by simp [pairwise_on_insert_of_symmetric hr]

lemma pairwise_on_univ : (univ : set α).pairwise_on r ↔ pairwise r :=
by simp only [pairwise_on, pairwise, mem_univ, forall_const]

lemma pairwise_on.on_injective (hs : s.pairwise_on r) (hf : function.injective f)
  (hfs : ∀ x, f x ∈ s) :
  pairwise (r on f) :=
λ i j hij, hs _ (hfs i) _ (hfs j) (hf.ne hij)

lemma inj_on.pairwise_on_image {s : set ι} (h : s.inj_on f) :
  (f '' s).pairwise_on r ↔ s.pairwise_on (r on f) :=
by simp [h.eq_iff, pairwise_on] {contextual := tt}

lemma pairwise_on_Union {f : ι → set α} (h : directed (⊆) f) :
  (⋃ n, f n).pairwise_on r ↔ ∀ n, (f n).pairwise_on r :=
begin
  split,
  { assume H n,
    exact pairwise_on.mono (subset_Union _ _) H },
  { assume H i hi j hj hij,
    rcases mem_Union.1 hi with ⟨m, hm⟩,
    rcases mem_Union.1 hj with ⟨n, hn⟩,
    rcases h m n with ⟨p, mp, np⟩,
    exact H p i (mp hm) j (np hn) hij }
end

lemma pairwise_on_sUnion {r : α → α → Prop} {s : set (set α)} (h : directed_on (⊆) s) :
  (⋃₀ s).pairwise_on r ↔ (∀ a ∈ s, set.pairwise_on a r) :=
by { rw [sUnion_eq_Union, pairwise_on_Union (h.directed_coe), set_coe.forall], refl }

end set

lemma pairwise.pairwise_on (h : pairwise r) (s : set α) : s.pairwise_on r := λ x hx y hy, h x y

end pairwise

namespace set
section semilattice_inf_bot
variables [semilattice_inf_bot α] {s t : set ι} {f g : ι → α}

/-- A set is `pairwise_disjoint` under `f`, if the images of any distinct two elements under `f`
are disjoint. -/
def pairwise_disjoint (s : set ι) (f : ι → α) : Prop := s.pairwise_on (disjoint on f)

lemma pairwise_disjoint.subset (ht : t.pairwise_disjoint f) (h : s ⊆ t) : s.pairwise_disjoint f :=
pairwise_on.mono h ht

lemma pairwise_disjoint.mono_on (hs : s.pairwise_disjoint f) (h : ∀ ⦃i⦄, i ∈ s → g i ≤ f i) :
  s.pairwise_disjoint g :=
λ a ha b hb hab, (hs a ha b hb hab).mono (h ha) (h hb)

lemma pairwise_disjoint.mono (hs : s.pairwise_disjoint f) (h : g ≤ f) : s.pairwise_disjoint g :=
hs.mono_on (λ i _, h i)

lemma pairwise_disjoint_empty : (∅ : set ι).pairwise_disjoint f := pairwise_on_empty _

lemma pairwise_disjoint_singleton (i : ι) (f : ι → α) : pairwise_disjoint {i} f :=
pairwise_on_singleton i _

lemma pairwise_disjoint_insert {i : ι} :
  (insert i s).pairwise_disjoint f
    ↔ s.pairwise_disjoint f ∧ ∀ j ∈ s, i ≠ j → disjoint (f i) (f j) :=
set.pairwise_on_insert_of_symmetric $ symmetric_disjoint.comap f

lemma pairwise_disjoint.insert (hs : s.pairwise_disjoint f) {i : ι}
  (h : ∀ j ∈ s, i ≠ j → disjoint (f i) (f j)) :
  (insert i s).pairwise_disjoint f :=
set.pairwise_disjoint_insert.2 ⟨hs, h⟩

lemma pairwise_disjoint.image_of_le (hs : s.pairwise_disjoint f) {g : ι → ι} (hg : f ∘ g ≤ f) :
  (g '' s).pairwise_disjoint f :=
begin
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h,
  exact (hs a ha b hb $ ne_of_apply_ne _ h).mono (hg a) (hg b),
end

lemma pairwise_disjoint.range (g : s → ι) (hg : ∀ (i : s), f (g i) ≤ f i)
  (ht : s.pairwise_disjoint f) :
  (range g).pairwise_disjoint f :=
begin
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy,
  exact (ht _ x.2 _ y.2 $ λ h, hxy $ congr_arg g $ subtype.ext h).mono (hg x) (hg y),
end

lemma pairwise_disjoint_union :
  (s ∪ t).pairwise_disjoint f ↔ s.pairwise_disjoint f ∧ t.pairwise_disjoint f ∧
    ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → disjoint (f i) (f j) :=
pairwise_on_union_of_symmetric $ symmetric_disjoint.comap f

lemma pairwise_disjoint.union (hs : s.pairwise_disjoint f) (ht : t.pairwise_disjoint f)
  (h : ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ t → i ≠ j → disjoint (f i) (f j)) :
  (s ∪ t).pairwise_disjoint f :=
pairwise_disjoint_union.2 ⟨hs, ht, h⟩

lemma pairwise_disjoint_Union {g : ι' → set ι} (h : directed (⊆) g) :
  (⋃ n, g n).pairwise_disjoint f ↔ ∀ ⦃n⦄, (g n).pairwise_disjoint f :=
pairwise_on_Union h

lemma pairwise_disjoint_sUnion {s : set (set ι)} (h : directed_on (⊆) s) :
  (⋃₀ s).pairwise_disjoint f ↔ ∀ ⦃a⦄, a ∈ s → set.pairwise_disjoint a f :=
pairwise_on_sUnion h

-- classical
lemma pairwise_disjoint.elim (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
  (h : ¬ disjoint (f i) (f j)) :
  i = j :=
of_not_not $ λ hij, h $ hs _ hi _ hj hij

-- classical
lemma pairwise_disjoint.elim' (hs : s.pairwise_disjoint f) {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
  (h : f i ⊓ f j ≠ ⊥) :
  i = j :=
hs.elim hi hj $ λ hij, h hij.eq_bot

end semilattice_inf_bot

/-! ### Pairwise disjoint set of sets -/

lemma pairwise_disjoint_range_singleton :
  (set.range (singleton : ι → set ι)).pairwise_disjoint id :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h,
  exact disjoint_singleton.2 (ne_of_apply_ne _ h),
end

lemma pairwise_disjoint_fiber (f : ι → α) (s : set α) : s.pairwise_disjoint (λ a, f ⁻¹' {a}) :=
λ a _ b _ h i ⟨hia, hib⟩, h $ (eq.symm hia).trans hib

-- classical
lemma pairwise_disjoint.elim_set {s : set ι} {f : ι → set α} (hs : s.pairwise_disjoint f) {i j : ι}
  (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
hs.elim hi hj $ not_disjoint_iff.2 ⟨a, hai, haj⟩

lemma bUnion_diff_bUnion_eq {s t : set ι} {f : ι → set α} (h : (s ∪ t).pairwise_disjoint f) :
  (⋃ i ∈ s, f i) \ (⋃ i ∈ t, f i) = (⋃ i ∈ s \ t, f i) :=
begin
  refine (bUnion_diff_bUnion_subset f s t).antisymm
    (bUnion_subset $ λ i hi a ha, (mem_diff _).2 ⟨mem_bUnion hi.1 ha, _⟩),
  rw mem_bUnion_iff, rintro ⟨j, hj, haj⟩,
  exact h i (or.inl hi.1) j (or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm ⟨ha, haj⟩,
end

/-- Equivalence between a disjoint bounded union and a dependent sum. -/
noncomputable def bUnion_eq_sigma_of_disjoint {s : set ι} {f : ι → set α}
  (h : pairwise_on s (disjoint on f)) :
  (⋃ i ∈ s, f i) ≃ (Σ i : s, f i) :=
(equiv.set_congr (bUnion_eq_Union _ _)).trans $ Union_eq_sigma_of_disjoint $
  λ ⟨i, hi⟩ ⟨j, hj⟩ ne, h _ hi _ hj $ λ eq, ne $ subtype.eq eq

end set

lemma pairwise_disjoint_fiber (f : ι → α) : pairwise (disjoint on (λ a : α, f ⁻¹' {a})) :=
set.pairwise_on_univ.1 $ set.pairwise_disjoint_fiber f univ
