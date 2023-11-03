/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import algebra.gcd_monoid.multiset
import combinatorics.partition
import data.list.rotate
import group_theory.perm.cycle.basic
import ring_theory.int.basic
import tactic.linarith

/-!
# Cycle Types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the cycle type of a permutation.

## Main definitions

- `σ.cycle_type` where `σ` is a permutation of a `fintype`
- `σ.partition` where `σ` is a permutation of a `fintype`

## Main results

- `sum_cycle_type` : The sum of `σ.cycle_type` equals `σ.support.card`
- `lcm_cycle_type` : The lcm of `σ.cycle_type` equals `order_of σ`
- `is_conj_iff_cycle_type_eq` : Two permutations are conjugate if and only if they have the same
  cycle type.
- `exists_prime_order_of_dvd_card`: For every prime `p` dividing the order of a finite group `G`
  there exists an element of order `p` in `G`. This is known as Cauchy's theorem.
-/

namespace equiv.perm
open equiv list multiset

variables {α : Type*} [fintype α]

section cycle_type

variables [decidable_eq α]

/-- The cycle type of a permutation -/
def cycle_type (σ : perm α) : multiset ℕ :=
σ.cycle_factors_finset.1.map (finset.card ∘ support)

lemma cycle_type_def (σ : perm α) :
  σ.cycle_type = σ.cycle_factors_finset.1.map (finset.card ∘ support) := rfl

lemma cycle_type_eq' {σ : perm α} (s : finset (perm α))
  (h1 : ∀ f : perm α, f ∈ s → f.is_cycle) (h2 : (s : set (perm α)).pairwise disjoint)
  (h0 : s.noncomm_prod id (h2.imp $ λ _ _, disjoint.commute) = σ) :
  σ.cycle_type = s.1.map (finset.card ∘ support) :=
begin
  rw cycle_type_def,
  congr,
  rw cycle_factors_finset_eq_finset,
  exact ⟨h1, h2, h0⟩
end

lemma cycle_type_eq {σ : perm α} (l : list (perm α)) (h0 : l.prod = σ)
  (h1 : ∀ σ : perm α, σ ∈ l → σ.is_cycle) (h2 : l.pairwise disjoint) :
  σ.cycle_type = l.map (finset.card ∘ support) :=
begin
  have hl : l.nodup := nodup_of_pairwise_disjoint_cycles h1 h2,
  rw cycle_type_eq' l.to_finset,
  { simp [list.dedup_eq_self.mpr hl] },
  { simpa using h1 },
  { simpa [hl] using h0 },
  { simpa [list.dedup_eq_self.mpr hl] using h2.forall disjoint.symmetric }
end

lemma cycle_type_one : (1 : perm α).cycle_type = 0 :=
cycle_type_eq [] rfl (λ _, false.elim) pairwise.nil

lemma cycle_type_eq_zero {σ : perm α} : σ.cycle_type = 0 ↔ σ = 1 :=
by simp [cycle_type_def, cycle_factors_finset_eq_empty_iff]

lemma card_cycle_type_eq_zero {σ : perm α} : σ.cycle_type.card = 0 ↔ σ = 1 :=
by rw [card_eq_zero, cycle_type_eq_zero]

lemma two_le_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 2 ≤ n :=
begin
  simp only [cycle_type_def, ←finset.mem_def, function.comp_app, multiset.mem_map,
    mem_cycle_factors_finset_iff] at h,
  obtain ⟨_, ⟨hc, -⟩, rfl⟩ := h,
  exact hc.two_le_card_support
end

lemma one_lt_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : 1 < n :=
two_le_of_mem_cycle_type h

lemma is_cycle.cycle_type {σ : perm α} (hσ : is_cycle σ) : σ.cycle_type = [σ.support.card] :=
cycle_type_eq [σ] (mul_one σ) (λ τ hτ, (congr_arg is_cycle (list.mem_singleton.mp hτ)).mpr hσ)
  (pairwise_singleton disjoint σ)

lemma card_cycle_type_eq_one {σ : perm α} : σ.cycle_type.card = 1 ↔ σ.is_cycle :=
begin
  rw card_eq_one,
  simp_rw [cycle_type_def, multiset.map_eq_singleton, ←finset.singleton_val,
           finset.val_inj, cycle_factors_finset_eq_singleton_iff],
  split,
  { rintro ⟨_, _, ⟨h, -⟩, -⟩,
    exact h },
  { intro h,
    use [σ.support.card, σ],
    simp [h] }
end

lemma disjoint.cycle_type {σ τ : perm α} (h : disjoint σ τ) :
  (σ * τ).cycle_type = σ.cycle_type + τ.cycle_type :=
begin
  rw [cycle_type_def, cycle_type_def, cycle_type_def, h.cycle_factors_finset_mul_eq_union,
      ←multiset.map_add, finset.union_val, multiset.add_eq_union_iff_disjoint.mpr _],
  exact finset.disjoint_val.2 h.disjoint_cycle_factors_finset
end

lemma cycle_type_inv (σ : perm α) : σ⁻¹.cycle_type = σ.cycle_type :=
cycle_induction_on (λ τ : perm α, τ⁻¹.cycle_type = τ.cycle_type) σ rfl
  (λ σ hσ, by rw [hσ.cycle_type, hσ.inv.cycle_type, support_inv])
  (λ σ τ hστ hc hσ hτ, by rw [mul_inv_rev, hστ.cycle_type, ←hσ, ←hτ, add_comm,
    disjoint.cycle_type (λ x, or.imp (λ h : τ x = x, inv_eq_iff_eq.mpr h.symm)
    (λ h : σ x = x, inv_eq_iff_eq.mpr h.symm) (hστ x).symm)])

lemma cycle_type_conj {σ τ : perm α} : (τ * σ * τ⁻¹).cycle_type = σ.cycle_type :=
begin
  revert τ,
  apply cycle_induction_on _ σ,
  { intro,
    simp },
  { intros σ hσ τ,
    rw [hσ.cycle_type, hσ.conj.cycle_type, card_support_conj] },
  { intros σ τ hd hc hσ hτ π,
    rw [← conj_mul, hd.cycle_type, disjoint.cycle_type, hσ, hτ],
    intro a,
    apply (hd (π⁻¹ a)).imp _ _;
    { intro h, rw [perm.mul_apply, perm.mul_apply, h, apply_inv_self] } }
end

lemma sum_cycle_type (σ : perm α) : σ.cycle_type.sum = σ.support.card :=
cycle_induction_on (λ τ : perm α, τ.cycle_type.sum = τ.support.card) σ
  (by rw [cycle_type_one, sum_zero, support_one, finset.card_empty])
  (λ σ hσ, by rw [hσ.cycle_type, coe_sum, list.sum_singleton])
  (λ σ τ hστ hc hσ hτ, by rw [hστ.cycle_type, sum_add, hσ, hτ, hστ.card_support_mul])

lemma sign_of_cycle_type' (σ : perm α) :
  sign σ = (σ.cycle_type.map (λ n, -(-1 : ℤˣ) ^ n)).prod :=
cycle_induction_on (λ τ : perm α, sign τ = (τ.cycle_type.map (λ n, -(-1 : ℤˣ) ^ n)).prod) σ
  (by rw [sign_one, cycle_type_one, multiset.map_zero, prod_zero])
  (λ σ hσ, by rw [hσ.sign, hσ.cycle_type, coe_map, coe_prod,
    list.map_singleton, list.prod_singleton])
  (λ σ τ hστ hc hσ hτ, by rw [sign_mul, hσ, hτ, hστ.cycle_type, multiset.map_add, prod_add])

lemma sign_of_cycle_type (f : perm α) :
  sign f = (-1 : ℤˣ)^(f.cycle_type.sum + f.cycle_type.card) :=
cycle_induction_on
  (λ f : perm α, sign f = (-1 : ℤˣ)^(f.cycle_type.sum + f.cycle_type.card))
  f
  ( -- base_one
    by rw [equiv.perm.cycle_type_one, sign_one, multiset.sum_zero, multiset.card_zero, pow_zero] )
  ( -- base_cycles
    λ f hf,
      by rw [equiv.perm.is_cycle.cycle_type hf, hf.sign,
      coe_sum, list.sum_cons, sum_nil, add_zero, coe_card, length_singleton,
      pow_add, pow_one, mul_comm, neg_mul, one_mul] )
  ( -- induction_disjoint
    λ f g hfg hf Pf Pg,
    by rw [equiv.perm.disjoint.cycle_type hfg,
      multiset.sum_add, multiset.card_add,← add_assoc,
      add_comm f.cycle_type.sum g.cycle_type.sum,
      add_assoc g.cycle_type.sum _ _,
      add_comm g.cycle_type.sum _,
      add_assoc, pow_add,
      ← Pf, ← Pg,
      equiv.perm.sign_mul])

lemma lcm_cycle_type (σ : perm α) : σ.cycle_type.lcm = order_of σ :=
cycle_induction_on (λ τ : perm α, τ.cycle_type.lcm = order_of τ) σ
  (by rw [cycle_type_one, lcm_zero, order_of_one])
  (λ σ hσ, by rw [hσ.cycle_type, coe_singleton, lcm_singleton, hσ.order_of,
    normalize_eq])
  (λ σ τ hστ hc hσ hτ, by rw [hστ.cycle_type, lcm_add, lcm_eq_nat_lcm, hστ.order_of, hσ, hτ])

lemma dvd_of_mem_cycle_type {σ : perm α} {n : ℕ} (h : n ∈ σ.cycle_type) : n ∣ order_of σ :=
begin
  rw ← lcm_cycle_type,
  exact dvd_lcm h,
end

lemma order_of_cycle_of_dvd_order_of (f : perm α) (x : α) :
  order_of (cycle_of f x) ∣ order_of f :=
begin
  by_cases hx : f x = x,
  { rw ←cycle_of_eq_one_iff at hx,
    simp [hx] },
  { refine dvd_of_mem_cycle_type _,
    rw [cycle_type, multiset.mem_map],
    refine ⟨f.cycle_of x, _, _⟩,
    { rwa [←finset.mem_def, cycle_of_mem_cycle_factors_finset_iff, mem_support] },
    { simp [(is_cycle_cycle_of _ hx).order_of] } }
end

lemma two_dvd_card_support {σ : perm α} (hσ : σ ^ 2 = 1) : 2 ∣ σ.support.card :=
(congr_arg (has_dvd.dvd 2) σ.sum_cycle_type).mp
  (multiset.dvd_sum (λ n hn, by rw le_antisymm (nat.le_of_dvd zero_lt_two $
  (dvd_of_mem_cycle_type hn).trans $ order_of_dvd_of_pow_eq_one hσ) (two_le_of_mem_cycle_type hn)))

lemma cycle_type_prime_order {σ : perm α} (hσ : (order_of σ).prime) :
  ∃ n : ℕ, σ.cycle_type = replicate (n + 1) (order_of σ) :=
begin
  rw eq_replicate_of_mem (λ n hn, or_iff_not_imp_left.mp
    (hσ.eq_one_or_self_of_dvd n (dvd_of_mem_cycle_type hn)) (one_lt_of_mem_cycle_type hn).ne'),
  use σ.cycle_type.card - 1,
  rw tsub_add_cancel_of_le,
  rw [nat.succ_le_iff, pos_iff_ne_zero, ne, card_cycle_type_eq_zero],
  intro H,
  rw [H, order_of_one] at hσ,
  exact hσ.ne_one rfl,
end

lemma is_cycle_of_prime_order {σ : perm α} (h1 : (order_of σ).prime)
  (h2 : σ.support.card < 2 * (order_of σ)) : σ.is_cycle :=
begin
  obtain ⟨n, hn⟩ := cycle_type_prime_order h1,
  rw [←σ.sum_cycle_type, hn, multiset.sum_replicate, nsmul_eq_mul, nat.cast_id, mul_lt_mul_right
      (order_of_pos σ), nat.succ_lt_succ_iff, nat.lt_succ_iff, le_zero_iff] at h2,
  rw [←card_cycle_type_eq_one, hn, card_replicate, h2],
end

lemma cycle_type_le_of_mem_cycle_factors_finset {f g : perm α}
  (hf : f ∈ g.cycle_factors_finset) :
  f.cycle_type ≤ g.cycle_type :=
begin
  rw mem_cycle_factors_finset_iff at hf,
  rw [cycle_type_def, cycle_type_def, hf.left.cycle_factors_finset_eq_singleton],
  refine map_le_map _,
  simpa [←finset.mem_def, mem_cycle_factors_finset_iff] using hf
end

lemma cycle_type_mul_mem_cycle_factors_finset_eq_sub {f g : perm α}
  (hf : f ∈ g.cycle_factors_finset) :
  (g * f⁻¹).cycle_type = g.cycle_type - f.cycle_type :=
begin
  suffices : (g * f⁻¹).cycle_type + f.cycle_type = g.cycle_type - f.cycle_type + f.cycle_type,
  { rw tsub_add_cancel_of_le (cycle_type_le_of_mem_cycle_factors_finset hf) at this,
    simp [←this] },
  simp [←(disjoint_mul_inv_of_mem_cycle_factors_finset hf).cycle_type,
    tsub_add_cancel_of_le (cycle_type_le_of_mem_cycle_factors_finset hf)]
end

theorem is_conj_of_cycle_type_eq {σ τ : perm α} (h : cycle_type σ = cycle_type τ) : is_conj σ τ :=
begin
  revert τ,
  apply cycle_induction_on _ σ,
  { intros τ h,
    rw [cycle_type_one, eq_comm, cycle_type_eq_zero] at h,
    rw h },
  { intros σ hσ τ hστ,
    have hτ := card_cycle_type_eq_one.2 hσ,
    rw [hστ, card_cycle_type_eq_one] at hτ,
    apply hσ.is_conj hτ,
    rw [hσ.cycle_type, hτ.cycle_type, coe_eq_coe, singleton_perm] at hστ,
    simp only [and_true, eq_self_iff_true] at hστ,
    exact hστ },
  { intros σ τ hστ hσ h1 h2 π hπ,
    rw [hστ.cycle_type] at hπ,
    { have h : σ.support.card ∈ map (finset.card ∘ perm.support) π.cycle_factors_finset.val,
      { simp [←cycle_type_def, ←hπ, hσ.cycle_type] },
      obtain ⟨σ', hσ'l, hσ'⟩ := multiset.mem_map.mp h,
      have key : is_conj (σ' * (π * σ'⁻¹)) π,
      { rw is_conj_iff,
        use σ'⁻¹,
        simp [mul_assoc] },
      refine is_conj.trans _ key,
      have hs : σ.cycle_type = σ'.cycle_type,
      { rw [←finset.mem_def, mem_cycle_factors_finset_iff] at hσ'l,
        rw [hσ.cycle_type, ←hσ', hσ'l.left.cycle_type] },
      refine hστ.is_conj_mul (h1 hs) (h2 _) _,
      { rw [cycle_type_mul_mem_cycle_factors_finset_eq_sub, ←hπ, add_comm, hs,
            add_tsub_cancel_right],
        rwa finset.mem_def },
      { exact (disjoint_mul_inv_of_mem_cycle_factors_finset hσ'l).symm } } }
end

theorem is_conj_iff_cycle_type_eq {σ τ : perm α} :
  is_conj σ τ ↔ σ.cycle_type = τ.cycle_type :=
⟨λ h, begin
  obtain ⟨π, rfl⟩ := is_conj_iff.1 h,
  rw cycle_type_conj,
end, is_conj_of_cycle_type_eq⟩

@[simp] lemma cycle_type_extend_domain {β : Type*} [fintype β] [decidable_eq β]
  {p : β → Prop} [decidable_pred p] (f : α ≃ subtype p) {g : perm α} :
  cycle_type (g.extend_domain f) = cycle_type g :=
begin
  apply cycle_induction_on _ g,
  { rw [extend_domain_one, cycle_type_one, cycle_type_one] },
  { intros σ hσ,
    rw [(hσ.extend_domain f).cycle_type, hσ.cycle_type, card_support_extend_domain] },
  { intros σ τ hd hc hσ hτ,
    rw [hd.cycle_type, ← extend_domain_mul, (hd.extend_domain f).cycle_type, hσ, hτ] }
end

lemma cycle_type_of_subtype {p : α → Prop} [decidable_pred p] {g : perm (subtype p)}:
  cycle_type (g.of_subtype) = cycle_type g := cycle_type_extend_domain (equiv.refl (subtype p))

lemma mem_cycle_type_iff {n : ℕ} {σ : perm α} :
  n ∈ cycle_type σ ↔ ∃ c τ : perm α, σ = c * τ ∧ disjoint c τ ∧ is_cycle c ∧ c.support.card = n :=
begin
  split,
  { intro h,
    obtain ⟨l, rfl, hlc, hld⟩ := trunc_cycle_factors σ,
    rw cycle_type_eq _ rfl hlc hld at h,
    obtain ⟨c, cl, rfl⟩ := list.exists_of_mem_map h,
    rw (list.perm_cons_erase cl).pairwise_iff (λ _ _ hd, _) at hld,
    swap, { exact hd.symm },
    refine ⟨c, (l.erase c).prod, _, _, hlc _ cl, rfl⟩,
    { rw [← list.prod_cons,
        (list.perm_cons_erase cl).symm.prod_eq' (hld.imp (λ _ _, disjoint.commute))] },
    { exact disjoint_prod_right _ (λ g, list.rel_of_pairwise_cons hld) } },
  { rintros ⟨c, t, rfl, hd, hc, rfl⟩,
    simp [hd.cycle_type, hc.cycle_type] }
end

lemma le_card_support_of_mem_cycle_type {n : ℕ} {σ : perm α} (h : n ∈ cycle_type σ) :
  n ≤ σ.support.card :=
(le_sum_of_mem h).trans (le_of_eq σ.sum_cycle_type)

lemma cycle_type_of_card_le_mem_cycle_type_add_two {n : ℕ} {g : perm α}
  (hn2 : fintype.card α < n + 2) (hng : n ∈ g.cycle_type) :
  g.cycle_type = {n} :=
begin
  obtain ⟨c, g', rfl, hd, hc, rfl⟩ := mem_cycle_type_iff.1 hng,
  by_cases g'1 : g' = 1,
  { rw [hd.cycle_type, hc.cycle_type, coe_singleton, g'1, cycle_type_one, add_zero] },
  contrapose! hn2,
  apply le_trans _ (c * g').support.card_le_univ,
  rw [hd.card_support_mul],
  exact add_le_add_left (two_le_card_support_of_ne_one g'1) _,
end

end cycle_type

lemma card_compl_support_modeq [decidable_eq α] {p n : ℕ} [hp : fact p.prime] {σ : perm α}
  (hσ : σ ^ p ^ n = 1) : σ.supportᶜ.card ≡ fintype.card α [MOD p] :=
begin
  rw [nat.modeq_iff_dvd' σ.supportᶜ.card_le_univ, ←finset.card_compl, compl_compl],
  refine (congr_arg _ σ.sum_cycle_type).mp (multiset.dvd_sum (λ k hk, _)),
  obtain ⟨m, -, hm⟩ := (nat.dvd_prime_pow hp.out).mp (order_of_dvd_of_pow_eq_one hσ),
  obtain ⟨l, -, rfl⟩ := (nat.dvd_prime_pow hp.out).mp
    ((congr_arg _ hm).mp (dvd_of_mem_cycle_type hk)),
  exact dvd_pow_self _ (λ h, (one_lt_of_mem_cycle_type hk).ne $ by rw [h, pow_zero]),
end

lemma exists_fixed_point_of_prime {p n : ℕ} [hp : fact p.prime] (hα : ¬ p ∣ fintype.card α)
  {σ : perm α} (hσ : σ ^ p ^ n = 1) : ∃ a : α, σ a = a :=
begin
  classical,
  contrapose! hα,
  simp_rw ← mem_support at hα,
  exact nat.modeq_zero_iff_dvd.mp ((congr_arg _ (finset.card_eq_zero.mpr (compl_eq_bot.mpr
    (finset.eq_univ_iff_forall.mpr hα)))).mp (card_compl_support_modeq hσ).symm),
end

lemma exists_fixed_point_of_prime' {p n : ℕ} [hp : fact p.prime] (hα : p ∣ fintype.card α)
  {σ : perm α} (hσ : σ ^ p ^ n = 1) {a : α} (ha : σ a = a) : ∃ b : α, σ b = b ∧ b ≠ a :=
begin
  classical,
  have h : ∀ b : α, b ∈ σ.supportᶜ ↔ σ b = b :=
  λ b, by rw [finset.mem_compl, mem_support, not_not],
  obtain ⟨b, hb1, hb2⟩ := finset.exists_ne_of_one_lt_card (lt_of_lt_of_le hp.out.one_lt
    (nat.le_of_dvd (finset.card_pos.mpr ⟨a, (h a).mpr ha⟩) (nat.modeq_zero_iff_dvd.mp
    ((card_compl_support_modeq hσ).trans (nat.modeq_zero_iff_dvd.mpr hα))))) a,
  exact ⟨b, (h b).mp hb1, hb2⟩,
end

lemma is_cycle_of_prime_order' {σ : perm α} (h1 : (order_of σ).prime)
  (h2 : fintype.card α < 2 * (order_of σ)) : σ.is_cycle :=
begin
  classical,
  exact is_cycle_of_prime_order h1 (lt_of_le_of_lt σ.support.card_le_univ h2),
end

lemma is_cycle_of_prime_order'' {σ : perm α} (h1 : (fintype.card α).prime)
  (h2 : order_of σ = fintype.card α) : σ.is_cycle :=
is_cycle_of_prime_order' ((congr_arg nat.prime h2).mpr h1)
begin
  classical,
  rw [←one_mul (fintype.card α), ←h2, mul_lt_mul_right (order_of_pos σ)],
  exact one_lt_two,
end

section cauchy

variables (G : Type*) [group G] (n : ℕ)

/-- The type of vectors with terms from `G`, length `n`, and product equal to `1:G`. -/
def vectors_prod_eq_one : set (vector G n) :=
{v | v.to_list.prod = 1}

namespace vectors_prod_eq_one

lemma mem_iff {n : ℕ} (v : vector G n) :
v ∈ vectors_prod_eq_one G n ↔ v.to_list.prod = 1 := iff.rfl

lemma zero_eq : vectors_prod_eq_one G 0 = {vector.nil} :=
set.eq_singleton_iff_unique_mem.mpr ⟨eq.refl (1 : G), λ v hv, v.eq_nil⟩

lemma one_eq : vectors_prod_eq_one G 1 = {vector.nil.cons 1} :=
begin
  simp_rw [set.eq_singleton_iff_unique_mem, mem_iff,
    vector.to_list_singleton, list.prod_singleton, vector.head_cons],
  exact ⟨rfl, λ v hv, v.cons_head_tail.symm.trans (congr_arg2 vector.cons hv v.tail.eq_nil)⟩,
end

instance zero_unique : unique (vectors_prod_eq_one G 0) :=
by { rw zero_eq, exact set.unique_singleton vector.nil }

instance one_unique : unique (vectors_prod_eq_one G 1) :=
by { rw one_eq, exact set.unique_singleton (vector.nil.cons 1) }

/-- Given a vector `v` of length `n`, make a vector of length `n + 1` whose product is `1`,
by appending the inverse of the product of `v`. -/
@[simps] def vector_equiv : vector G n ≃ vectors_prod_eq_one G (n + 1) :=
{ to_fun := λ v, ⟨v.to_list.prod⁻¹ ::ᵥ v,
    by rw [mem_iff, vector.to_list_cons, list.prod_cons, inv_mul_self]⟩,
  inv_fun := λ v, v.1.tail,
  left_inv := λ v, v.tail_cons v.to_list.prod⁻¹,
  right_inv := λ v, subtype.ext ((congr_arg2 vector.cons (eq_inv_of_mul_eq_one_left (by
  { rw [←list.prod_cons, ←vector.to_list_cons, v.1.cons_head_tail],
    exact v.2 })).symm rfl).trans v.1.cons_head_tail) }

/-- Given a vector `v` of length `n` whose product is 1, make a vector of length `n - 1`,
by deleting the last entry of `v`. -/
def equiv_vector : vectors_prod_eq_one G n ≃ vector G (n - 1) :=
((vector_equiv G (n - 1)).trans (if hn : n = 0 then (show vectors_prod_eq_one G (n - 1 + 1) ≃
  vectors_prod_eq_one G n, by { rw hn, apply equiv_of_unique })
  else by rw tsub_add_cancel_of_le (nat.pos_of_ne_zero hn).nat_succ_le)).symm

instance [fintype G] : fintype (vectors_prod_eq_one G n) :=
fintype.of_equiv (vector G (n - 1)) (equiv_vector G n).symm

lemma card [fintype G] :
  fintype.card (vectors_prod_eq_one G n) = fintype.card G ^ (n - 1) :=
(fintype.card_congr (equiv_vector G n)).trans (card_vector (n - 1))

variables {G n} {g : G} (v : vectors_prod_eq_one G n) (j k : ℕ)

/-- Rotate a vector whose product is 1. -/
def rotate : vectors_prod_eq_one G n :=
⟨⟨_, (v.1.1.length_rotate k).trans v.1.2⟩, list.prod_rotate_eq_one_of_prod_eq_one v.2 k⟩

lemma rotate_zero : rotate v 0 = v :=
subtype.ext (subtype.ext v.1.1.rotate_zero)

lemma rotate_rotate : rotate (rotate v j) k = rotate v (j + k) :=
subtype.ext (subtype.ext (v.1.1.rotate_rotate j k))

lemma rotate_length : rotate v n = v :=
subtype.ext (subtype.ext ((congr_arg _ v.1.2.symm).trans v.1.1.rotate_length))

end vectors_prod_eq_one

/-- For every prime `p` dividing the order of a finite group `G` there exists an element of order
`p` in `G`. This is known as Cauchy's theorem. -/
lemma _root_.exists_prime_order_of_dvd_card {G : Type*} [group G] [fintype G] (p : ℕ)
  [hp : fact p.prime] (hdvd : p ∣ fintype.card G) : ∃ x : G, order_of x = p :=
begin
  have hp' : p - 1 ≠ 0 := mt tsub_eq_zero_iff_le.mp (not_le_of_lt hp.out.one_lt),
  have Scard := calc p ∣ fintype.card G ^ (p - 1) : hdvd.trans (dvd_pow (dvd_refl _) hp')
  ... = fintype.card (vectors_prod_eq_one G p) : (vectors_prod_eq_one.card G p).symm,
  let f : ℕ → vectors_prod_eq_one G p → vectors_prod_eq_one G p :=
  λ k v, vectors_prod_eq_one.rotate v k,
  have hf1 : ∀ v, f 0 v = v := vectors_prod_eq_one.rotate_zero,
  have hf2 : ∀ j k v, f k (f j v) = f (j + k) v :=
  λ j k v, vectors_prod_eq_one.rotate_rotate v j k,
  have hf3 : ∀ v, f p v = v := vectors_prod_eq_one.rotate_length,
  let σ := equiv.mk (f 1) (f (p - 1))
    (λ s, by rw [hf2, add_tsub_cancel_of_le hp.out.one_lt.le, hf3])
    (λ s, by rw [hf2, tsub_add_cancel_of_le hp.out.one_lt.le, hf3]),
  have hσ : ∀ k v, (σ ^ k) v = f k v :=
  λ k v, nat.rec (hf1 v).symm (λ k hk, by { rw pow_succ,
    exact eq.trans (by exact congr_arg σ hk) (hf2 k 1 v)}) k,
  replace hσ : σ ^ (p ^ 1) = 1 := perm.ext (λ v, by rw [pow_one, hσ, hf3, one_apply]),
  let v₀ : vectors_prod_eq_one G p :=
    ⟨vector.replicate p 1, (list.prod_replicate p 1).trans (one_pow p)⟩,
  have hv₀ : σ v₀ = v₀ := subtype.ext (subtype.ext (list.rotate_replicate (1 : G) p 1)),
  obtain ⟨v, hv1, hv2⟩ := exists_fixed_point_of_prime' Scard hσ hv₀,
  refine exists_imp_exists (λ g hg, order_of_eq_prime _ (λ hg', hv2 _))
    (list.rotate_one_eq_self_iff_eq_replicate.mp (subtype.ext_iff.mp (subtype.ext_iff.mp hv1))),
  { rw [←list.prod_replicate, ←v.1.2, ←hg, (show v.val.val.prod = 1, from v.2)] },
  { rw [subtype.ext_iff_val, subtype.ext_iff_val, hg, hg', v.1.2],
    refl },
end

/-- For every prime `p` dividing the order of a finite additive group `G` there exists an element of
order `p` in `G`. This is the additive version of Cauchy's theorem. -/
lemma _root_.exists_prime_add_order_of_dvd_card {G : Type*} [add_group G] [fintype G] (p : ℕ)
  [hp : fact p.prime] (hdvd : p ∣ fintype.card G) : ∃ x : G, add_order_of x = p :=
@exists_prime_order_of_dvd_card (multiplicative G) _ _ _ _ hdvd

attribute [to_additive exists_prime_add_order_of_dvd_card] exists_prime_order_of_dvd_card

end cauchy

lemma subgroup_eq_top_of_swap_mem [decidable_eq α] {H : subgroup (perm α)}
  [d : decidable_pred (∈ H)] {τ : perm α} (h0 : (fintype.card α).prime)
  (h1 : fintype.card α ∣ fintype.card H) (h2 : τ ∈ H) (h3 : is_swap τ) :
  H = ⊤ :=
begin
  haveI : fact (fintype.card α).prime := ⟨h0⟩,
  obtain ⟨σ, hσ⟩ := exists_prime_order_of_dvd_card (fintype.card α) h1,
  have hσ1 : order_of (σ : perm α) = fintype.card α := (order_of_subgroup σ).trans hσ,
  have hσ2 : is_cycle ↑σ := is_cycle_of_prime_order'' h0 hσ1,
  have hσ3 : (σ : perm α).support = ⊤ :=
    finset.eq_univ_of_card (σ : perm α).support (hσ2.order_of.symm.trans hσ1),
  have hσ4 : subgroup.closure {↑σ, τ} = ⊤ := closure_prime_cycle_swap h0 hσ2 hσ3 h3,
  rw [eq_top_iff, ←hσ4, subgroup.closure_le, set.insert_subset, set.singleton_subset_iff],
  exact ⟨subtype.mem σ, h2⟩,
end

section partition

variables [decidable_eq α]

/-- The partition corresponding to a permutation -/
def partition (σ : perm α) : (fintype.card α).partition :=
{ parts := σ.cycle_type + replicate (fintype.card α - σ.support.card) 1,
  parts_pos := λ n hn,
  begin
    cases mem_add.mp hn with hn hn,
    { exact zero_lt_one.trans (one_lt_of_mem_cycle_type hn) },
    { exact lt_of_lt_of_le zero_lt_one (ge_of_eq (multiset.eq_of_mem_replicate hn)) },
  end,
  parts_sum := by rw [sum_add, sum_cycle_type, multiset.sum_replicate, nsmul_eq_mul,
    nat.cast_id, mul_one, add_tsub_cancel_of_le σ.support.card_le_univ] }

lemma parts_partition {σ : perm α} :
  σ.partition.parts = σ.cycle_type + replicate (fintype.card α - σ.support.card) 1 := rfl

lemma filter_parts_partition_eq_cycle_type {σ : perm α} :
  (partition σ).parts.filter (λ n, 2 ≤ n) = σ.cycle_type :=
begin
  rw [parts_partition, filter_add, multiset.filter_eq_self.2 (λ _, two_le_of_mem_cycle_type),
    multiset.filter_eq_nil.2 (λ a h, _), add_zero],
  rw multiset.eq_of_mem_replicate h,
  dec_trivial
end

lemma partition_eq_of_is_conj {σ τ : perm α} :
  is_conj σ τ ↔ σ.partition = τ.partition :=
begin
  rw [is_conj_iff_cycle_type_eq],
  refine ⟨λ h, _, λ h, _⟩,
  { rw [nat.partition.ext_iff, parts_partition, parts_partition,
      ← sum_cycle_type, ← sum_cycle_type, h] },
  { rw [← filter_parts_partition_eq_cycle_type, ← filter_parts_partition_eq_cycle_type, h] }
end

end partition

/-!
### 3-cycles
-/

/-- A three-cycle is a cycle of length 3. -/
def is_three_cycle [decidable_eq α] (σ : perm α) : Prop := σ.cycle_type = {3}

namespace is_three_cycle

variables [decidable_eq α] {σ : perm α}

lemma cycle_type (h : is_three_cycle σ) : σ.cycle_type = {3} := h

lemma card_support (h : is_three_cycle σ) : σ.support.card = 3 :=
by rw [←sum_cycle_type, h.cycle_type, multiset.sum_singleton]

lemma _root_.card_support_eq_three_iff : σ.support.card = 3 ↔ σ.is_three_cycle :=
begin
  refine ⟨λ h, _, is_three_cycle.card_support⟩,
  by_cases h0 : σ.cycle_type = 0,
  { rw [←sum_cycle_type, h0, sum_zero] at h,
    exact (ne_of_lt zero_lt_three h).elim },
  obtain ⟨n, hn⟩ := exists_mem_of_ne_zero h0,
  by_cases h1 : σ.cycle_type.erase n = 0,
  { rw [←sum_cycle_type, ←cons_erase hn, h1, cons_zero, multiset.sum_singleton] at h,
    rw [is_three_cycle, ←cons_erase hn, h1, h, ←cons_zero] },
  obtain ⟨m, hm⟩ := exists_mem_of_ne_zero h1,
  rw [←sum_cycle_type, ←cons_erase hn, ←cons_erase hm, multiset.sum_cons, multiset.sum_cons] at h,
  -- TODO: linarith [...] should solve this directly
  have : ∀ {k}, 2 ≤ m → 2 ≤ n → n + (m + k) = 3 → false, { intros, linarith },
  cases this (two_le_of_mem_cycle_type (mem_of_mem_erase hm)) (two_le_of_mem_cycle_type hn) h,
end

lemma is_cycle (h : is_three_cycle σ) : is_cycle σ :=
by rw [←card_cycle_type_eq_one, h.cycle_type, card_singleton]

lemma sign (h : is_three_cycle σ) : sign σ = 1 :=
begin
  rw [equiv.perm.sign_of_cycle_type, h.cycle_type],
  refl,
end

lemma inv {f : perm α} (h : is_three_cycle f) : is_three_cycle (f⁻¹) :=
by rwa [is_three_cycle, cycle_type_inv]

@[simp] lemma inv_iff {f : perm α} : is_three_cycle (f⁻¹) ↔ is_three_cycle f :=
⟨by { rw ← inv_inv f, apply inv }, inv⟩

lemma order_of {g : perm α} (ht : is_three_cycle g) :
  order_of g = 3 :=
by rw [←lcm_cycle_type, ht.cycle_type, multiset.lcm_singleton, normalize_eq]

lemma is_three_cycle_sq {g : perm α} (ht : is_three_cycle g) :
  is_three_cycle (g * g) :=
begin
  rw [←pow_two, ←card_support_eq_three_iff, support_pow_coprime, ht.card_support],
  rw [ht.order_of, nat.coprime_iff_gcd_eq_one],
  norm_num,
end

end is_three_cycle

section
variable [decidable_eq α]

lemma is_three_cycle_swap_mul_swap_same
  {a b c : α} (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) :
  is_three_cycle (swap a b * swap a c) :=
begin
  suffices h : support (swap a b * swap a c) = {a, b, c},
  { rw [←card_support_eq_three_iff, h],
    simp [ab, ac, bc] },
  apply le_antisymm ((support_mul_le _ _).trans (λ x, _)) (λ x hx, _),
  { simp [ab, ac, bc] },
  { simp only [finset.mem_insert, finset.mem_singleton] at hx,
    rw mem_support,
    simp only [perm.coe_mul, function.comp_app, ne.def],
    obtain rfl | rfl | rfl := hx,
    { rw [swap_apply_left, swap_apply_of_ne_of_ne ac.symm bc.symm],
      exact ac.symm },
    { rw [swap_apply_of_ne_of_ne ab.symm bc, swap_apply_right],
      exact ab },
    { rw [swap_apply_right, swap_apply_left],
      exact bc } }
end

open subgroup

lemma swap_mul_swap_same_mem_closure_three_cycles
  {a b c : α} (ab : a ≠ b) (ac : a ≠ c) :
  (swap a b * swap a c) ∈ closure {σ : perm α | is_three_cycle σ } :=
begin
  by_cases bc : b = c,
  { subst bc,
    simp [one_mem] },
  exact subset_closure (is_three_cycle_swap_mul_swap_same ab ac bc)
end

lemma is_swap.mul_mem_closure_three_cycles {σ τ : perm α}
  (hσ : is_swap σ) (hτ : is_swap τ) :
  σ * τ ∈ closure {σ : perm α | is_three_cycle σ } :=
begin
  obtain ⟨a, b, ab, rfl⟩ := hσ,
  obtain ⟨c, d, cd, rfl⟩ := hτ,
  by_cases ac : a = c,
  { subst ac,
    exact swap_mul_swap_same_mem_closure_three_cycles ab cd },
  have h' : swap a b * swap c d = swap a b * swap a c * (swap c a * swap c d),
  { simp [swap_comm c a, mul_assoc] },
  rw h',
  exact mul_mem (swap_mul_swap_same_mem_closure_three_cycles ab ac)
    (swap_mul_swap_same_mem_closure_three_cycles (ne.symm ac) cd),
end

end

end equiv.perm
