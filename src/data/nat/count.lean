/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Scott Morrison, Eric Rodriguez
-/
import data.list.basic
import data.nat.prime
import order.order_iso_nat
import set_theory.fincard

/-!
# Counting on ℕ

This files defines ways to get basic properties of a predicate on ℕ, such as "how many numbers
under `k` satisfy the predicate" and "what is the `n`th number that satisifies this predicate".
We define these as two functions, `count` and `nth`, that answer these questions, and prove
the expected theorems about them.

## Main definitions

* `count p n`: The number of naturals `k < n` such that `p k`.
* `nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `nth p n = 0`.

## Main results

* `nat.nth_eq_order_iso_of_nat`: An infinite set of natural numbers is order-isomorphic to the
  natural numbers.

## TODO

There has been some discussion on the subject of whether both of `nth` and
`nat.subtype.order_iso_of_nat` should exist. See discussion
[here](https://github.com/leanprover-community/mathlib/pull/9457#pullrequestreview-767221180).
Future work should address how lemmas that use these should be written.

-/

lemma list.range_add (a : ℕ) :
  ∀ b, list.range (a + b) = list.range a ++ (list.range b).map (λ x, a + x)
| 0 := by rw [add_zero, list.range_zero, list.map_nil, list.append_nil]
| (b + 1) := by rw [nat.add_succ, list.range_succ, list.range_add b, list.range_succ,
  list.map_append, list.map_singleton, list.append_assoc]

lemma multiset.range_add (a b : ℕ) :
  multiset.range (a + b) = multiset.range a ∪ (multiset.range b).map (λ x, a + x) :=
begin
  rw [multiset.range, list.range_add, ←multiset.coe_add, ←multiset.coe_map],
  refine multiset.add_eq_union_iff_disjoint.2 (λ x hxa hxb, _),
  rw [multiset.mem_coe, list.mem_range] at hxa,
  obtain ⟨c, _, rfl⟩ := multiset.mem_map.1 hxb,
  exact (self_le_add_right _ _).not_lt hxa,
end

lemma finset.range_add (a b : ℕ) :
  finset.range (a + b) = finset.range a ∪ (finset.range b).image (λ x, a + x) :=
begin
  rw [←finset.val_inj, finset.range, finset.union_val,
    finset.image_val_of_inj_on ((add_right_injective a).inj_on _)],
  exact multiset.range_add a b,
end

lemma galois_connection.lt_iff_lt {α β : Type*} [linear_order α] [linear_order β] {l : α → β}
  {u : β → α} (gc : galois_connection l u) {a : α} {b : β} :
  b < l a ↔ u b < a :=
lt_iff_lt_of_le_iff_le (gc a b)

open finset

namespace nat
variable (p : ℕ → Prop)

section count
variable [decidable_pred p]

/-- Count the number of naturals `k < n` satisfying `p k`. -/
def count (n : ℕ) : ℕ := (list.range n).countp p

@[simp] lemma count_zero : count p 0 = 0 :=
by rw [count, list.range_zero, list.countp]

/-- A fintype instance for the set relevant to `nat.count`. Locally an instance in locale `count` -/
def count_set.fintype (n : ℕ) : fintype {i // i < n ∧ p i} :=
begin
  apply fintype.of_finset ((finset.range n).filter p),
  intro x,
  rw [mem_filter, mem_range],
  refl,
end

localized "attribute [instance] count_set.fintype" in count

lemma count_eq_card_filter_range (n : ℕ) : count p n = ((range n).filter p).card :=
by { rw [count, list.countp_eq_length_filter], refl,}

/-- `count p n` can be expressed as the cardinality of `{k // k < n ∧ p k}`. -/
lemma count_eq_card_fintype (n : ℕ) : count p n = fintype.card {k : ℕ // k < n ∧ p k} :=
begin
  rw [count_eq_card_filter_range, ←fintype.card_of_finset],
  congr,
  intro i,
  rw [mem_filter, mem_range],
  refl,
end

lemma count_monotone : monotone (count p) :=
begin
  intros a b h,
  rw [count, list.countp_eq_length_filter, count, list.countp_eq_length_filter],
  exact list.length_le_of_sublist (list.sublist.filter p (list.range_sublist.mpr h)),
end

@[simp] lemma count_succ (n : ℕ) : count p (n + 1) = count p n + (if p n then 1 else 0) :=
by split_ifs; simp [count, list.range_succ, h]

lemma count_add (a b : ℕ) : count p (a + b) = count p a + count (λ k, p (a + k)) b :=
begin
  rw [count_eq_card_filter_range, count_eq_card_filter_range, count_eq_card_filter_range, range_add,
    filter_union, card_disjoint_union, image_filter,
    card_image_of_injective _ (add_right_injective a)],
  intros x hx,
  simp_rw [inf_eq_inter, mem_inter, mem_filter, mem_image, mem_range] at hx,
  obtain ⟨⟨hx, _⟩, ⟨c, _, rfl⟩, _⟩ := hx,
  exact (self_le_add_right _ _).not_lt hx,
end

lemma count_add' (a b : ℕ) : count p (a + b) = count (λ k, p (k + b)) a + count p b :=
by { rw [add_comm, count_add, add_comm], simp_rw add_comm b, congr' 2 }

lemma count_one : count p 1 = if p 0 then 1 else 0 := by simp

lemma count_succ' (n : ℕ) : count p (n + 1) = count (λ k, p (k + 1)) n + if p 0 then 1 else 0 :=
by rw [count_add', count_one]

variables {p}

lemma count_succ_eq_succ_count_iff {n : ℕ} : count p (n + 1) = count p n + 1 ↔ p n :=
by by_cases h : p n; simp [h]

lemma count_succ_eq_count_iff {n : ℕ} : count p (n + 1) = count p n ↔ ¬p n :=
by by_cases h : p n; simp [h]

alias count_succ_eq_succ_count_iff ↔ _ count_succ_eq_succ_count
alias count_succ_eq_count_iff ↔ _ count_succ_eq_count

lemma count_le_cardinal (n : ℕ) : (count p n : cardinal) ≤ cardinal.mk (set_of p) :=
begin
  obtain h | h := lt_or_le (cardinal.mk (set_of p)) cardinal.omega,
  { haveI := (cardinal.lt_omega_iff_fintype.mp h).some,
    simp [cardinal.mk_fintype],
    rw count_eq_card_fintype,
    apply fintype.card_le_of_injective,
    swap,
    exact λ ⟨i, _, hi⟩, ⟨i, hi⟩,
    tidy, },
  { exact trans (le_of_lt (cardinal.nat_lt_omega (count p n))) h},
end

variables {p}

lemma lt_of_count_lt_count {a b : ℕ} (h : count p a < count p b) : a < b :=
(count_monotone p).reflect_lt h

end count

/-- Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is the first
natural number satisfying `p`), or `0` if there is no such number. See also
`subtype.order_iso_of_nat` for the order isomorphism with ℕ when `p` is infinitely often true. -/
noncomputable def nth : ℕ → ℕ
| n := Inf { i : ℕ | p i ∧ ∀ k < n, nth k < i }

instance decidable_pred_mem_set_of [h : decidable_pred p] : decidable_pred (∈ set_of p) := h

lemma nth_zero : nth p 0 = Inf { i : ℕ | p i } := by { rw nth, simp }

@[simp]
lemma nth_zero_of_zero (h : p 0) : nth p 0 = 0 :=
begin
  rw nth,
  refine nat.eq_zero_of_le_zero (nat.Inf_le _),
  simp [h],
end

lemma nth_zero_of_exists [decidable_pred p] (h : ∃ n, p n) : nth p 0 = nat.find h :=
by { rw [nth_zero], convert nat.Inf_def h }

lemma nth_set_card_aux {n : ℕ} (hp : (set_of p).finite)
  (hp' : {i : ℕ | p i ∧ ∀ t < n, nth p t < i}.finite) (hle : n ≤ hp.to_finset.card) :
  hp'.to_finset.card = hp.to_finset.card - n :=
begin
  unfreezingI { induction n with k hk },
  { congr,
    simp only [forall_false_left, nat.not_lt_zero, forall_const, and_true] },
  have hp'': {i : ℕ | p i ∧ ∀ t, t < k → nth p t < i}.finite,
  { refine hp.subset (λ x hx, _),
    rw set.mem_set_of_eq at hx,
    exact hx.left },
  have hle' := nat.sub_pos_of_lt hle,
  specialize hk hp'' (k.le_succ.trans hle),
  rw [nat.sub_succ', ←hk],
  convert_to (finset.erase hp''.to_finset (nth p k)).card = _,
  { congr,
    ext a,
    simp only [set.finite.mem_to_finset, ne.def, set.mem_set_of_eq, finset.mem_erase],
    refine ⟨λ ⟨hp, hlt⟩,
              ⟨(hlt _ (lt_add_one k)).ne', ⟨hp, λ n hn, hlt n (hn.trans_le k.le_succ)⟩⟩, _⟩,
    rintro ⟨hak : _ ≠ _, hp, hlt⟩,
    refine ⟨hp, λ n hn, _⟩,
    rw lt_succ_iff at hn,
    obtain hnk | rfl := hn.lt_or_eq,
    { exact hlt _ hnk },
    { refine lt_of_le_of_ne _ (ne.symm hak),
      rw nth,
      apply nat.Inf_le,
      simpa [hp] using hlt } },
  apply finset.card_erase_of_mem,
  rw [nth, set.finite.mem_to_finset],
  apply Inf_mem,
  rwa [←set.finite.to_finset.nonempty hp'', ←finset.card_pos, hk],
end

lemma nth_set_card {n : ℕ} (hp : (set_of p).finite)
  (hp' : {i : ℕ | p i ∧ ∀ k < n, nth p k < i}.finite) :
  hp'.to_finset.card = hp.to_finset.card - n :=
begin
  obtain hn | hn := le_or_lt n hp.to_finset.card,
  { exact nth_set_card_aux p hp _ hn },
  rw nat.sub_eq_zero_of_le hn.le,
  simp only [finset.card_eq_zero, set.finite_to_finset_eq_empty_iff, ←set.subset_empty_iff],
  convert_to _ ⊆ {i : ℕ | p i ∧ ∀ (k : ℕ), k < hp.to_finset.card → nth p k < i},
  { symmetry,
    rw [←set.finite_to_finset_eq_empty_iff, ←finset.card_eq_zero,
        ←nat.sub_self hp.to_finset.card],
    { apply nth_set_card_aux p hp _ le_rfl },
    { exact hp.subset (λ x hx, hx.1) } },
  exact λ x hx, ⟨hx.1, λ k hk, hx.2 _ (hk.trans hn)⟩,
end

lemma nth_set_nonempty_of_lt_card {n : ℕ} (hp : (set_of p).finite) (hlt: n < hp.to_finset.card) :
  {i : ℕ | p i ∧ ∀ k < n, nth p k < i}.nonempty :=
begin
  have hp': {i : ℕ | p i ∧ ∀ (k : ℕ), k < n → nth p k < i}.finite,
  { exact hp.subset (λ x hx, hx.1) },
  rw [←hp'^.to_finset.nonempty, ←finset.card_pos, nth_set_card p hp],
  exact nat.sub_pos_of_lt hlt,
end

lemma nth_mem_of_lt_card_finite_aux (n : ℕ) (hp : (set_of p).finite) (hlt : n < hp.to_finset.card) :
  nth p n ∈ {i : ℕ | p i ∧ ∀ k < n, nth p k < i} :=
begin
  rw nth,
  apply Inf_mem,
  exact nth_set_nonempty_of_lt_card _ _ hlt,
end

lemma nth_mem_of_lt_card_finite {n : ℕ} (hp : (set_of p).finite) (hlt : n < hp.to_finset.card) :
  p (nth p n) := (nth_mem_of_lt_card_finite_aux p n hp hlt).1

lemma nth_strict_mono_of_finite {m n : ℕ} (hp : (set_of p).finite)
  (hlt : n < hp.to_finset.card) (hmn : m < n) : nth p m < nth p n :=
(nth_mem_of_lt_card_finite_aux p _ hp hlt).2 _ hmn

lemma nth_mem_of_infinite_aux (hp : (set_of p).infinite) (n : ℕ) :
  nth p n ∈ { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
begin
  rw nth,
  apply Inf_mem,
  let s : set ℕ := ⋃ (k < n), { i : ℕ | nth p k ≥ i },
  convert_to ((set_of p) \ s).nonempty,
  { ext i,
    simp },
  refine (hp.diff $ (set.finite_lt_nat _).bUnion _).nonempty,
  exact λ k h, set.finite_le_nat _,
end

lemma nth_mem_of_infinite (hp : (set_of p).infinite) (n : ℕ) : p (nth p n) :=
(nth_mem_of_infinite_aux p hp n).1

lemma nth_strict_mono (hp : (set_of p).infinite) : strict_mono (nth p) :=
λ a b, (nth_mem_of_infinite_aux p hp b).2 _

lemma nth_monotone (hp : (set_of p).infinite) : monotone (nth p) :=
(nth_strict_mono p hp).monotone

lemma nth_mono_of_finite {a b : ℕ} (hp : (set_of p).finite) (hb : b < hp.to_finset.card)
  (hab : a ≤ b) : nth p a ≤ nth p b :=
begin
  obtain rfl | h := hab.eq_or_lt,
  { exact le_rfl },
  { exact (nth_strict_mono_of_finite p hp hb h).le }
end

lemma le_nth_of_lt_nth_succ_finite {k a : ℕ} (hp : (set_of p).finite)
  (hlt : k.succ < hp.to_finset.card) (h : a < nth p k.succ) (ha : p a) :
  a ≤ nth p k :=
begin
  by_contra hak,
  push_neg at hak,
  refine h.not_le _,
  rw nth,
  apply nat.Inf_le,
  refine ⟨ha, λ n hn, lt_of_le_of_lt _ hak⟩,
  exact nth_mono_of_finite p hp (k.le_succ.trans_lt hlt) (le_of_lt_succ hn),
end

lemma le_nth_of_lt_nth_succ_infinite {k a : ℕ} (hp : (set_of p).infinite)
  (h : a < nth p k.succ) (ha : p a) :
  a ≤ nth p k :=
begin
  by_contra hak,
  push_neg at hak,
  refine h.not_le _,
  rw nth,
  apply nat.Inf_le,
  exact ⟨ha, λ n hn, (nth_monotone p hp (le_of_lt_succ hn)).trans_lt hak⟩,
end

section count
variables [decidable_pred p]

@[simp] lemma count_nth_zero : count p (nth p 0) = 0 :=
begin
  rw [count_eq_card_filter_range, finset.card_eq_zero, nth_zero],
  ext a,
  simp_rw [not_mem_empty, mem_filter, mem_range, iff_false],
  rintro ⟨ha, hp⟩,
  exact ha.not_le (nat.Inf_le hp),
end

lemma filter_range_nth_eq_insert_of_finite (hp : (set_of p).finite) {k : ℕ}
  (hlt : k.succ < hp.to_finset.card) :
  finset.filter p (finset.range (nth p k.succ)) =
    insert (nth p k) (finset.filter p (finset.range (nth p k))) :=
begin
  ext a,
  simp_rw [mem_insert, mem_filter, mem_range],
  split,
  { rintro ⟨ha, hpa⟩,
    refine or_iff_not_imp_left.mpr (λ h, ⟨lt_of_le_of_ne _ h, hpa⟩),
    exact le_nth_of_lt_nth_succ_finite p hp hlt ha hpa },
  { rintro (ha | ⟨ha, hpa⟩),
    { rw ha,
      refine ⟨nth_strict_mono_of_finite p hp hlt (lt_add_one _), _⟩,
      apply nth_mem_of_lt_card_finite p hp,
      exact (k.le_succ).trans_lt hlt },
    refine ⟨ha.trans _, hpa⟩,
    exact nth_strict_mono_of_finite p hp hlt (lt_add_one _) }
end

lemma count_nth_of_lt_card_finite {n : ℕ} (hp : (set_of p).finite)
  (hlt : n < hp.to_finset.card) : count p (nth p n) = n :=
begin
  induction n with k hk,
  { exact count_nth_zero _ },
  rw [count_eq_card_filter_range, filter_range_nth_eq_insert_of_finite p hp hlt,
      finset.card_insert_of_not_mem, ←count_eq_card_filter_range, hk (lt_of_succ_lt hlt)],
  { simp }
end

lemma filter_range_nth_eq_insert_of_infinite (hp : (set_of p).infinite) (k : ℕ) :
  (finset.range (nth p k.succ)).filter p = insert (nth p k) ((finset.range (nth p k)).filter p) :=
begin
  ext a,
  simp_rw [mem_insert, mem_filter, mem_range],
  split,
  { rintro ⟨ha, hpa⟩,
    rw nth at ha,
    refine or_iff_not_imp_left.mpr (λ hne, ⟨(le_of_not_lt $ λ h, _).lt_of_ne hne, hpa⟩),
    exact ha.not_le (nat.Inf_le ⟨hpa, λ b hb, (nth_monotone p hp (le_of_lt_succ hb)).trans_lt h⟩) },
  { rintro (rfl | ⟨ha, hpa⟩),
    { exact ⟨nth_strict_mono p hp (lt_succ_self k), nth_mem_of_infinite p hp _⟩ },
    { exact ⟨ha.trans (nth_strict_mono p hp (lt_succ_self k)), hpa⟩ } }
end

lemma count_nth_of_infinite (hp : (set_of p).infinite) (n : ℕ) : count p (nth p n) = n :=
begin
  induction n with k hk,
  { exact count_nth_zero _ },
  rw [count_eq_card_filter_range, filter_range_nth_eq_insert_of_infinite p hp,
      finset.card_insert_of_not_mem, ←count_eq_card_filter_range, hk],
  { simp }
end

lemma count_strict_mono {m n : ℕ} (hm : p m) (hmn : m < n) : count p m < count p n :=
begin
  rw [count_eq_card_filter_range, count_eq_card_filter_range],
  apply finset.card_lt_card,
  refine ⟨λ a, _, _⟩,
  { simp only [and_imp, mem_filter, mem_range],
    exact λ ha hp, ⟨ha.trans hmn, hp⟩ },
  { rw finset.not_subset,
    exact ⟨m, by simp [hm, hmn]⟩ }
end

lemma count_injective {m n : ℕ} (hm : p m) (hn : p n) (heq : count p m = count p n) : m = n :=
begin
  by_contra,
  wlog hmn : m < n,
  { exact ne.lt_or_lt h },
  { simpa [heq] using count_strict_mono _ hm hmn }
end

lemma count_lt_card {n : ℕ} (hp : (set_of p).finite) (hpn : p n) :
  count p n < hp.to_finset.card :=
begin
  rw count_eq_card_filter_range,
  refine finset.card_lt_card ⟨λ x hx, hp.mem_to_finset.2 (mem_filter.1 hx).2, _⟩,
  rw finset.not_subset,
  exact ⟨n, (set.finite.mem_to_finset _).2 hpn, λ h, not_mem_range_self (mem_filter.1 h).1⟩
end

lemma nth_count {n : ℕ} (hpn : p n) : nth p (count p n) = n :=
begin
  obtain hp | hp := em (set_of p).finite,
  { refine count_injective p _ hpn _,
    { apply nth_mem_of_lt_card_finite p hp,
      exact count_lt_card p hp hpn },
    { exact count_nth_of_lt_card_finite _ _ (count_lt_card _ hp hpn) } },
  { apply count_injective p (nth_mem_of_infinite _ hp _) hpn,
  apply count_nth_of_infinite p hp }
end

lemma nth_count_eq_Inf {n : ℕ} : nth p (count p n) = Inf {i : ℕ | p i ∧ n ≤ i} :=
begin
  rw nth,
  congr,
  ext a,
  simp only [set.mem_set_of_eq, and.congr_right_iff],
  intro hpa,
  refine ⟨λ h, _, λ hn k hk, lt_of_lt_of_le _ hn⟩,
  { by_contra ha,
    simp only [not_le] at ha,
    have hn : nth p (count p a) < a := h _ (count_strict_mono p hpa ha),
    rwa [nth_count p hpa, lt_self_iff_false] at hn },
  { apply (count_monotone p).reflect_lt,
    convert hk,
    obtain hp | hp : (set_of p).finite ∨ (set_of p).infinite := em (set_of p).finite,
    { rw count_nth_of_lt_card_finite _ hp,
      exact hk.trans ((count_monotone _ hn).trans_lt (count_lt_card _ hp hpa)) },
    { apply count_nth_of_infinite p hp } }
end

lemma nth_count_le (hp : (set_of p).infinite) (n : ℕ) : n ≤ nth p (count p n) :=
begin
  rw nth_count_eq_Inf,
  suffices h : Inf {i : ℕ | p i ∧ n ≤ i} ∈ {i : ℕ | p i ∧ n ≤ i},
  { exact h.2 },
  apply Inf_mem,
  obtain ⟨m, hp, hn⟩ := hp.exists_nat_lt n,
  exact ⟨m, hp, hn.le⟩
end

lemma count_nth_gc (hp : (set_of p).infinite) : galois_connection (count p) (nth p) :=
begin
  rintro x y,
  rw [nth, le_cInf_iff ⟨0, λ _ _, nat.zero_le _⟩ ⟨nth p y, nth_mem_of_infinite_aux p hp y⟩],
  dsimp,
  refine ⟨_, λ h, _⟩,
  { rintro hy n ⟨hn, h⟩,
    obtain hy' | rfl := hy.lt_or_eq,
    { exact (nth_count_le p hp x).trans (h (count p x) hy').le },
    { specialize h (count p n),
      replace hn : nth p (count p n) = n := nth_count _ hn,
      replace h : count p x ≤ count p n := by rwa [hn, lt_self_iff_false, imp_false, not_lt] at h,
      refine (nth_count_le p hp x).trans _,
      rw ← hn,
      exact nth_monotone p hp h }, },
  { rw ←count_nth_of_infinite p hp y,
    exact count_monotone _ (h (nth p y) ⟨nth_mem_of_infinite p hp y,
      λ k hk, nth_strict_mono p hp hk⟩) }
end

lemma count_le_iff_le_nth (hp : (set_of p).infinite) {a b : ℕ} :
  count p a ≤ b ↔ a ≤ nth p b := count_nth_gc p hp _ _

lemma lt_nth_iff_count_lt (hp : (set_of p).infinite) {a b : ℕ} :
  a < count p b ↔ nth p a < b := lt_iff_lt_of_le_iff_le $ count_le_iff_le_nth p hp

lemma nth_lt_of_lt_count (n k : ℕ) (h : k < count p n) : nth p k < n :=
begin
  obtain hp | hp := em (set_of p).finite,
  { refine (count_monotone p).reflect_lt _,
    rwa count_nth_of_lt_card_finite p hp,
    refine h.trans_le _,
    rw count_eq_card_filter_range,
    exact finset.card_le_of_subset (λ x hx, hp.mem_to_finset.2 (mem_filter.1 hx).2) },
  { rwa ← lt_nth_iff_count_lt _ hp }
end

lemma le_nth_of_count_le (n k : ℕ) (h: n ≤ nth p k) : count p n ≤ k :=
begin
  by_contra hc,
  apply not_lt.mpr h,
  apply nth_lt_of_lt_count,
  simpa using hc
end

end count

lemma nth_zero_of_nth_zero (h₀ : ¬p 0) {a b : ℕ} (hab : a ≤ b) (ha : nth p a = 0) :
  nth p b = 0 :=
begin
  rw [nth, Inf_eq_zero] at ⊢ ha,
  cases ha,
  { exact (h₀ ha.1).elim },
  { refine or.inr (set.eq_empty_of_subset_empty $ λ x hx, _),
    rw ←ha,
    exact ⟨hx.1, λ k hk, hx.2 k $ hk.trans_le hab⟩ }
end

/-- When `p` is true infinitely often, `nth` agrees with `nat.subtype.order_iso_of_nat`. -/
lemma nth_eq_order_iso_of_nat [decidable_pred p] (i : infinite (set_of p)) (n : ℕ) :
  nth p n = nat.subtype.order_iso_of_nat (set_of p) n :=
begin
  have hi := set.infinite_coe_iff.mp i,
  induction n with k hk;
  simp only [subtype.order_iso_of_nat_apply, subtype.of_nat, nat_zero_eq_zero],
  { rw [nat.subtype.coe_bot, nth_zero_of_exists], },
  { simp only [nat.subtype.succ, set.mem_set_of_eq, subtype.coe_mk, subtype.val_eq_coe],
    rw [subtype.order_iso_of_nat_apply] at hk,
    set b := nth p k.succ - nth p k - 1 with hb,
    replace hb : p (↑(subtype.of_nat (set_of p) k) + b + 1),
    { rw [hb, ←hk, tsub_right_comm],
      have hn11: nth p k.succ - 1 + 1 = nth p k.succ,
      { rw tsub_add_cancel_iff_le,
        exact succ_le_of_lt (pos_of_gt (nth_strict_mono p hi (lt_add_one k))), },
      rw add_tsub_cancel_of_le,
      { rw hn11,
        apply nth_mem_of_infinite p hi },
      { rw [← lt_succ_iff, ← nat.add_one, hn11],
        apply nth_strict_mono p hi,
        exact lt_add_one k } },
    have H : (∃ n: ℕ , p (↑(subtype.of_nat (set_of p) k) + n + 1)) := ⟨b, hb⟩,
    set t := nat.find H with ht,
    obtain ⟨hp, hmin⟩ := (nat.find_eq_iff _).mp ht,
    rw [←ht, ←hk] at hp hmin ⊢,
    rw [nth, Inf_def ⟨_, nth_mem_of_infinite_aux p hi k.succ⟩, nat.find_eq_iff],
    refine ⟨⟨by convert hp, λ r hr, _⟩, λ n hn, _⟩,
    { rw lt_succ_iff at ⊢ hr,
      exact (nth_monotone p hi hr).trans (by simp) },
    simp only [exists_prop, not_and, not_lt, set.mem_set_of_eq, not_forall],
    refine λ hpn, ⟨k, lt_add_one k, _⟩,
    by_contra hlt,
    push_neg at hlt,
    replace hn : n - nth p k - 1 < t,
    { rw tsub_lt_iff_left,
      { rw tsub_lt_iff_left hlt.le,
        convert hn using 1,
        ac_refl },
      exact le_tsub_of_add_le_left (succ_le_of_lt hlt) },
    apply hmin,
    apply hn,
    convert hpn,
    have hn11 : n - 1 + 1 = n := nat.sub_add_cancel (pos_of_gt hlt),
    rwa [tsub_right_comm, add_tsub_cancel_of_le],
    rwa [←hn11, lt_succ_iff] at hlt },
end

end nat
