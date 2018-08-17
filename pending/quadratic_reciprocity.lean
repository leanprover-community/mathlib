import data.zmod data.polynomial group_theory.order_of_element data.set.finite data.nat.gcd

def units_of_nonzero {α : Type*} [field α] {a : α} (ha : a ≠ 0) : units α :=
⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩

lemma units.coe_pow {α : Type*} [monoid α] (u : units α) (n : ℕ) :
  ((u ^ n : units α) : α) = u ^ n :=
by induction n; simp [*, pow_succ]

@[simp] lemma units_of_nonzero_inj {α : Type*} [field α] {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
  units_of_nonzero ha = units_of_nonzero hb ↔ a = b :=
⟨λ h, by injection h, λ h, units.ext h⟩

@[simp] lemma coe_units_of_nonzero {α : Type*} [field α] {a : α} (ha : a ≠ 0) :
  (units_of_nonzero ha : α) = a := rfl

def units_equiv_ne_zero (α : Type*) [field α] : units α ≃ {a : α | a ≠ 0} :=
⟨λ a, ⟨a.1, units.ne_zero _⟩, λ a, units_of_nonzero a.2, λ ⟨_, _, _, _⟩, units.ext rfl, λ ⟨_, _⟩, rfl⟩

@[simp] lemma coe_units_equiv_ne_zero {α : Type*} [field α] (a : units α) :
  ((units_equiv_ne_zero α a) : α) = a := rfl

instance units.fintype {α : Type*} [field α] [fintype α] [decidable_eq α] : fintype (units α) :=
by haveI := set_fintype {a : α | a ≠ 0}; exact
fintype.of_equiv _ (units_equiv_ne_zero α).symm

def equiv_univ (α : Type*) : α ≃ @set.univ α :=
⟨λ a, ⟨a, trivial⟩, λ a, a.1, λ _, rfl, λ ⟨_, _⟩, rfl⟩

instance univ_decidable {α : Sort*} : decidable_pred (@set.univ α) :=
by unfold set.univ; apply_instance

lemma two_le_card_fintype_domain (α : Type*) [domain α] [fintype α] : 2 ≤ fintype.card α :=
nat.succ_le_of_lt (lt_of_not_ge (mt fintype.card_le_one_iff.1 (λ h, zero_ne_one (h _ _))))

lemma card_units {α : Type*} [field α] [fintype α] [decidable_eq α] :
  fintype.card (units α) = fintype.card α - 1 :=
begin
  rw [eq_comm, nat.sub_eq_iff_eq_add (nat.le_of_succ_le (two_le_card_fintype_domain α))],
  haveI := set_fintype {a : α | a ≠ 0},
  haveI := set_fintype (@set.univ α),
  rw [fintype.card_congr (units_equiv_ne_zero _),
    ← @set.card_insert _ _ {a : α | a ≠ 0} _ (not_not.2 (eq.refl (0 : α)))
    (set.fintype_insert _ _), fintype.card_congr (equiv_univ α)],
  congr; simp [set.ext_iff, classical.em]
end

lemma two_mul_odd_div_two {n : ℕ} (hn : n % 2 = 1) : 2 * (n / 2) = n - 1 :=
by conv {to_rhs, rw [← nat.mod_add_div n 2, hn, nat.add_sub_cancel_left]}

@[simp] lemma pow_card_eq_one {α : Type*} [group α] [fintype α] [decidable_eq α]
  (a : α) : a ^ fintype.card α = 1 :=
let ⟨m, hm⟩ := @order_of_dvd_card_univ _ a _ _ _ in
by simp [hm, pow_mul, pow_order_of_eq_one]

-- @[simp] lemma fermat_little (p : ℕ) {a : zmod p} (ha : a ≠ 0) : a ^ (p - 1) = 1 :=
-- have p - 1 = fintype.card (units (zmod p)) := by rw [card_units, zmod.card_zmod],
-- by rw [← coe_units_of_nonzero ha, ← @units.one_coe (zmod p), ← units.coe_pow, ← units.ext_iff,
--   this, pow_card_eq_one]

open polynomial finset nat

def totient (n : ℕ) : ℕ := ((range n).filter (nat.coprime n)).card

local notation `φ` := totient

lemma totient_le (n : ℕ) : φ n ≤ n :=
calc totient n ≤ (range n).card : card_le_of_subset (filter_subset _)
           ... = n              : card_range _

lemma totient_pos : ∀ {n : ℕ}, 0 < n → 0 < φ n
| 0 := dec_trivial
| 1 := dec_trivial
| (n+2) := λ h, card_pos.2 (mt eq_empty_iff_forall_not_mem.1
(classical.not_forall.2 ⟨1, not_not.2 $ mem_filter.2 ⟨mem_range.2 dec_trivial, by simp [coprime]⟩⟩))

lemma card_congr {α β : Type*} {s : finset α} {t : finset β} (f : Π a ∈ s, β)
  (h₁ : ∀ a ha, f a ha ∈ t) (h₂ : ∀ a b ha hb, f a ha = f b hb → a = b)
  (h₃ : ∀ b ∈ t, ∃ a ha, f a ha = b) : s.card = t.card :=
by haveI := classical.prop_decidable; exact
calc s.card = s.attach.card : card_attach.symm
... = (s.attach.image (λ (a : {a // a ∈ s}), f a.1 a.2)).card :
  eq.symm (card_image_of_injective _ (λ a b h, subtype.eq (h₂ _ _ _ _ h)))
... = t.card : congr_arg card (finset.ext.2 $ λ b,
    ⟨λ h, let ⟨a, ha₁, ha₂⟩ := mem_image.1 h in ha₂ ▸ h₁ _ _,
      λ h, let ⟨a, ha₁, ha₂⟩ := h₃ b h in mem_image.2 ⟨⟨a, ha₁⟩, by simp [ha₂]⟩⟩)

lemma card_bind {α β : Type*} [decidable_eq β] {s : finset α} {t : α → finset β}
  (h : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → x ≠ y → t x ∩ t y = ∅) :
  (s.bind t).card = s.sum (λ u, card (t u)) :=
calc (s.bind t).card = (s.bind t).sum (λ _, 1) : by simp
... = s.sum (λ a, (t a).sum (λ _, 1) ) : finset.sum_bind h
... = s.sum (card ∘ t) : by simp

lemma sum_totient (n : ℕ) : ((range n.succ).filter (∣ n)).sum φ = n :=
if hn0 : n = 0 then by rw hn0; refl
else
calc ((range n.succ).filter (∣ n)).sum φ
    = ((range n.succ).filter (∣ n)).sum (λ d, ((range (n / d)).filter (λ m, gcd (n / d) m = 1)).card) :
eq.symm $ sum_bij (λ d _, n / d)
  (λ d hd, mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $ nat.div_le_self _ _,
    by conv {to_rhs, rw ← nat.mul_div_cancel' (mem_filter.1 hd).2}; simp⟩)
  (λ _ _, rfl)
  (λ a b ha hb h,
    have ha : a * (n / a) = n, from nat.mul_div_cancel' (mem_filter.1 ha).2,
    have (n / a) > 0, from nat.pos_of_ne_zero (λ h, by simp [*, lt_irrefl] at *),
    by rw [← nat.mul_right_inj this, ha, h, nat.mul_div_cancel' (mem_filter.1 hb).2])
  (λ b hb,
    have hb : b < n.succ ∧ b ∣ n, by simpa [-range_succ] using hb,
    have hbn : (n / b) ∣ n, from ⟨b, by rw nat.div_mul_cancel hb.2⟩,
    have hnb0 : (n / b) ≠ 0, from λ h, by simpa [h, ne.symm hn0] using nat.div_mul_cancel hbn,
    ⟨n / b, mem_filter.2 ⟨mem_range.2 $ lt_succ_of_le $ nat.div_le_self _ _, hbn⟩,
      by rw [← nat.mul_right_inj (nat.pos_of_ne_zero hnb0),
        nat.mul_div_cancel' hb.2, nat.div_mul_cancel hbn]⟩)
... = ((range n.succ).filter (∣ n)).sum (λ d, ((range n).filter (λ m, gcd n m = d)).card) :
sum_congr rfl (λ d hd,
  have hd : d ∣ n, from (mem_filter.1 hd).2,
  have hd0 : 0 < d, from nat.pos_of_ne_zero (λ h, hn0 (eq_zero_of_zero_dvd $ h ▸ hd)),
  card_congr (λ m hm, d * m)
    (λ m hm, have hm : m < n / d ∧ gcd (n / d) m = 1, by simpa using hm,
      mem_filter.2 ⟨mem_range.2 $ nat.mul_div_cancel' hd ▸
        (mul_lt_mul_left hd0).2 hm.1,
        by rw [← nat.mul_div_cancel' hd, gcd_mul_left, hm.2, mul_one]⟩)
    (λ a b ha hb h, (nat.mul_left_inj hd0).1 h)
    (λ b hb, have hb : b < n ∧ gcd n b = d, by simpa using hb,
      ⟨b / d, mem_filter.2 ⟨mem_range.2 ((mul_lt_mul_left (show 0 < d, from hb.2 ▸ hb.2.symm ▸ hd0)).1
          (by rw [← hb.2, nat.mul_div_cancel' (gcd_dvd_left _ _),
            nat.mul_div_cancel' (gcd_dvd_right _ _)]; exact hb.1)),
              hb.2 ▸ coprime_div_gcd_div_gcd (hb.2.symm ▸ hd0)⟩,
        hb.2 ▸ nat.mul_div_cancel' (gcd_dvd_right _ _)⟩))
... = ((filter (∣ n) (range n.succ)).bind (λ d, (range n).filter (λ m, gcd n m = d))).card :
(card_bind (by simp [finset.ext]; cc)).symm
... = (range n).card :
congr_arg card (finset.ext.2 (λ m, ⟨by finish,
  λ hm, have h : m < n, from mem_range.1 hm,
    mem_bind.2 ⟨gcd n m, mem_filter.2 ⟨mem_range.2 (lt_succ_of_le (le_of_dvd (lt_of_le_of_lt (zero_le _) h)
      (gcd_dvd_left _ _))), gcd_dvd_left _ _⟩, mem_filter.2 ⟨hm, rfl⟩⟩⟩))
... = n : card_range _

lemma order_of_dvd_of_pow_eq_one {α : Type*} [fintype α] [group α] [decidable_eq α] {a : α}
  {n : ℕ} (h : a ^ n = 1) : order_of a ∣ n :=
by_contradiction
(λ h₁, nat.find_min _ (show n % order_of a < order_of a,
from nat.mod_lt _ (order_of_pos _))
⟨nat.pos_of_ne_zero (mt nat.dvd_of_mod_eq_zero h₁), by rwa ← pow_eq_mod_order_of⟩)

lemma order_of_le_of_pow_eq_one {α : Type*} [fintype α] [group α] [decidable_eq α] {a : α}
  {n : ℕ} (hn : 0 < n) (h : a ^ n = 1) : order_of a ≤ n :=
nat.find_min' (exists_pow_eq_one a) ⟨hn, h⟩

lemma sum_card_order_of_eq_card_pow_eq_one {α : Type*} [fintype α] [group α] [decidable_eq α] {n : ℕ} (hn : 0 < n) :
  ((range n.succ).filter (∣ n)).sum (λ m, (univ.filter (λ a : α, order_of a = m)).card)
  = (univ.filter (λ a : α, a ^ n = 1)).card :=
calc ((range n.succ).filter (∣ n)).sum (λ m, (univ.filter (λ a : α, order_of a = m)).card)
    = _ : (card_bind (by simp [finset.ext]; cc)).symm
... = _ : congr_arg card (finset.ext.2 (begin
  assume a,
  suffices : order_of a ≤ n ∧ order_of a ∣ n ↔ a ^ n = 1,
  { simpa [-range_succ, lt_succ_iff] },
  exact ⟨λ h, let ⟨m, hm⟩ := h.2 in by rw [hm, pow_mul, pow_order_of_eq_one, _root_.one_pow],
    λ h, ⟨order_of_le_of_pow_eq_one hn h, order_of_dvd_of_pow_eq_one h⟩⟩
end))

lemma order_of_pow {α : Type*} [group α] [fintype α] [decidable_eq α] (a : α) (n : ℕ) :
  order_of (a ^ n) = order_of a / gcd (order_of a) n :=
dvd_antisymm
(order_of_dvd_of_pow_eq_one
  (by rw [← pow_mul, ← nat.mul_div_assoc _ (gcd_dvd_left _ _), mul_comm,
    nat.mul_div_assoc _ (gcd_dvd_right _ _), pow_mul, pow_order_of_eq_one, _root_.one_pow]))
(have gcd_pos : 0 < gcd (order_of a) n, from gcd_pos_of_pos_left n (order_of_pos a),
  have hdvd : order_of a ∣ n * order_of (a ^ n),
    from order_of_dvd_of_pow_eq_one (by rw [pow_mul, pow_order_of_eq_one]),
  coprime.dvd_of_dvd_mul_right (coprime_div_gcd_div_gcd gcd_pos)
    (dvd_of_mul_dvd_mul_right gcd_pos
  (by rwa [nat.div_mul_cancel (gcd_dvd_left _ _), mul_assoc,
      nat.div_mul_cancel (gcd_dvd_right _ _), mul_comm])))

lemma div_dvd_of_dvd {a b : ℕ} (h : b ∣ a) : (a / b) ∣ a :=
⟨b, (nat.div_mul_cancel h).symm⟩

lemma nat.div_pos {a b : ℕ} (hba : b ≤ a) (hb : 0 < b) : 0 < a / b :=
nat.pos_of_ne_zero (λ h, lt_irrefl a
(calc a = a % b : by simpa [h] using (nat.mod_add_div a b).symm
    ... < b : nat.mod_lt a hb
    ... ≤ a : hba))

lemma div_div_self : ∀ {a b : ℕ}, b ∣ a → 0 < a → a / (a / b) = b
| a     0     h₁ h₂ := by rw eq_zero_of_zero_dvd h₁; refl
| 0     b     h₁ h₂ := absurd h₂ dec_trivial
| (a+1) (b+1) h₁ h₂ :=
(nat.mul_right_inj (nat.div_pos (le_of_dvd (succ_pos a) h₁) (succ_pos b))).1 $
  by rw [nat.div_mul_cancel (div_dvd_of_dvd h₁), nat.mul_div_cancel' h₁]

lemma zero_pow {α : Type*} [semiring α] {n : ℕ} (hn : 0 < n) : (0 : α) ^ n = 0 :=
by cases n; simpa [_root_.pow_succ, lt_irrefl] using hn

lemma card_pow_eq_one_eq_order_of {α : Type*} [fintype α] [field α] [decidable_eq α] (a : units α) :
  (univ.filter (λ b : units α, b ^ order_of a = 1)).card = order_of a :=
le_antisymm
(calc (univ.filter (λ b : units α, b ^ order_of a = 1)).card
      = (univ.filter (λ b : α, b ^ order_of a = 1)).card :
    card_congr (λ a ha, units_equiv_ne_zero α a) (λ a ha, mem_filter.2
      ⟨mem_univ _, by rw [coe_units_equiv_ne_zero,
        ← units.coe_pow, (mem_filter.1 ha).2, units.one_coe]⟩)
      (by simp [units.ext_iff]) (λ b hb,
        have hb : b ^ order_of a = 1, from (mem_filter.1 hb).2,
        have hb0 : b ≠ 0, from λ h,
          by simpa [h, _root_.zero_pow (order_of_pos a), zero_ne_one] using hb,
        ⟨(units_equiv_ne_zero α).symm ⟨b, hb0⟩, mem_filter.2
          ⟨mem_univ _, units.ext $ by rw [units.coe_pow]; exact hb⟩, rfl⟩)
  ... = (nth_roots (order_of a) (1 : α)).card :
    congr_arg card (by simp [finset.ext, mem_nth_roots (order_of_pos a)])
  ... ≤ order_of a : card_nth_roots _ _)
(calc order_of a = @fintype.card (gpowers a) (id _) : order_eq_card_gpowers
  ... ≤ @fintype.card (↑(univ.filter (λ b : units α, b ^ order_of a = 1)) : set (units α))
    (set.fintype_of_finset _ (λ _, iff.rfl)) :
  @fintype.card_le_of_injective (gpowers a) (↑(univ.filter (λ b : units α, b ^ order_of a = 1)) : set (units α))
    (id _) (id _) (λ b, ⟨b.1, mem_filter.2 ⟨mem_univ _,
    let ⟨i, hi⟩ := b.2 in
    by rw [← hi, ← gpow_coe_nat, ← gpow_mul, mul_comm, gpow_mul, gpow_coe_nat,
      pow_order_of_eq_one, one_gpow]⟩⟩) (λ _ _ h, subtype.eq (subtype.mk.inj h))
  ... = (univ.filter (λ b : units α, b ^ order_of a = 1)).card : set.card_fintype_of_finset _ (by simp))

lemma finite_field_cyclic_aux {α : Type*} [fintype α] [field α] [decidable_eq α] :
  ∀ {d : ℕ}, d ∣ fintype.card (units α) → 0 < (univ.filter (λ a : units α, order_of a = d)).card →
  (univ.filter (λ a : units α, order_of a = d)).card = φ d
| 0     := λ hd hd0, absurd hd0 (mt card_pos.1 (by simp [finset.ext, nat.pos_iff_ne_zero.1 (order_of_pos _)]))
| (d+1) := λ hd hd0,
let ⟨a, ha⟩ := exists_mem_of_ne_empty (card_pos.1 hd0) in
have ha : order_of a = d.succ, from (mem_filter.1 ha).2,
have h : ((range d.succ).filter (∣ d.succ)).sum (λ m, (univ.filter (λ a : units α, order_of a = m)).card) =
    ((range d.succ).filter (∣ d.succ)).sum φ, from
  finset.sum_congr rfl
    (λ m hm, have hmd : m < d.succ, from mem_range.1 (mem_filter.1 hm).1,
      have hm : m ∣ d.succ, from (mem_filter.1 hm).2,
      finite_field_cyclic_aux (dvd.trans hm hd) (finset.card_pos.2 (ne_empty_of_mem (show a ^ (d.succ / m) ∈ _,
        from mem_filter.2 ⟨mem_univ _,
        by rw [order_of_pow, ha, gcd_eq_right (div_dvd_of_dvd hm),
          div_div_self hm (succ_pos _)]⟩)))),
have hinsert : insert d.succ ((range d.succ).filter (∣ d.succ))
    = ((range d.succ.succ).filter (∣ d.succ)),
  from (finset.ext.2 $ λ x, ⟨λ h, (mem_insert.1 h).elim (λ h, by simp [h])
    (by clear _let_match; simp; tauto), by clear _let_match; simp {contextual := tt}; tauto⟩),
have hinsert₁ : d.succ ∉ (range d.succ).filter (∣ d.succ),
  by simp [-range_succ, mem_range, zero_le_one, le_succ],
(add_right_inj (((range d.succ).filter (∣ d.succ)).sum
  (λ m, (univ.filter (λ a : units α, order_of a = m)).card))).1
(calc _ = (insert d.succ (filter (∣ d.succ) (range d.succ))).sum
      (λ m, (univ.filter (λ (a : units α), order_of a = m)).card) :
eq.symm (finset.sum_insert (by simp [-range_succ, mem_range, zero_le_one, le_succ]))
... = ((range d.succ.succ).filter (∣ d.succ)).sum (λ m, (univ.filter (λ a : units α, order_of a = m)).card) :
sum_congr hinsert (λ _ _, rfl)
... = (univ.filter (λ a : units α, a ^ d.succ = 1)).card :
sum_card_order_of_eq_card_pow_eq_one (succ_pos d)
... = ((range d.succ.succ).filter (∣ d.succ)).sum φ :
ha ▸ (card_pow_eq_one_eq_order_of a).symm ▸ (sum_totient _).symm
... = _ : by rw [h, ← sum_insert hinsert₁];
  exact finset.sum_congr hinsert.symm (λ _ _, rfl))

lemma finite_field_cyclic {α : Type*} [field α] [fintype α] [decidable_eq α] {d : ℕ}
  (hd : d ∣ fintype.card (units α)) : (univ.filter (λ a : units α, order_of a = d)).card = φ d :=
by_contradiction (λ h,
have h0 : card (filter (λ (a : units α), order_of a = d) univ) = 0 :=
  not_not.1 (mt nat.pos_iff_ne_zero.2 (mt (finite_field_cyclic_aux hd) h)),
let c := fintype.card (units α) in
have hc0 : 0 < c, from fintype.card_pos_iff.2 ⟨1⟩,
lt_irrefl c $
calc c = (univ.filter (λ a : units α, a ^ c = 1)).card :
congr_arg card $ by simp [finset.ext]
... = ((range c.succ).filter (∣ c)).sum
    (λ m, (univ.filter (λ a : units α, order_of a = m)).card) :
(sum_card_order_of_eq_card_pow_eq_one hc0).symm
... = (((range c.succ).filter (∣ c)).erase d).sum
    (λ m, (univ.filter (λ a : units α, order_of a = m)).card) :
eq.symm (sum_subset (erase_subset _ _) (λ m hm₁ hm₂,
  have m = d, by simp at *; cc,
  by simp [*, finset.ext] at *))
... ≤ (((range c.succ).filter (∣ c)).erase d).sum φ :
sum_le_sum (λ m hm,
  have hmc : m ∣ c, by simp at hm; tauto,
  (imp_iff_not_or.1 (finite_field_cyclic_aux hmc)).elim
    (λ h, by simp [nat.le_zero_iff.1 (le_of_not_gt h), nat.zero_le])
    (by simp [le_refl] {contextual := tt}))
... < φ d + (((range c.succ).filter (∣ c)).erase d).sum φ :
lt_add_of_pos_left _ (totient_pos (nat.pos_of_ne_zero
  (λ h, nat.pos_iff_ne_zero.1 hc0 (eq_zero_of_zero_dvd $ h ▸ hd))))
... = (insert d (((range c.succ).filter (∣ c)).erase d)).sum φ : eq.symm (sum_insert (by simp))
... = ((range c.succ).filter (∣ c)).sum φ : finset.sum_congr
  (finset.insert_erase (mem_filter.2 ⟨mem_range.2 (lt_succ_of_le (le_of_dvd hc0 hd)), hd⟩)) (λ _ _, rfl)
... = c : sum_totient _)

#print axioms finite_field_cyclic