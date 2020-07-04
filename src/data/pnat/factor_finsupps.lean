/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson.
 -/

import data.finsupp
import data.pnat.factors
import order.conditionally_complete_lattice
import order.lattice
import order.order_iso
import tactic.pi_instances

/-!
# Factor Finsupps

A new version of prime factorisation and some facts about lattice isomorphisms

## Notations

## Implementation Notes
factor_finsupp is similar to pnat.factor_multiset, but a finsupp of exponents
Most of the sorries will be solved by proving some facts about lattice isomorphisms.

## References

 -/

set_option old_structure_cmd true

open_locale classical
open_locale big_operators


noncomputable theory

section basics

/-- Changes the domain to ℕ+. -/
def finsupp.primes_to_pnat : (nat.primes →₀ ℕ) → ℕ+ →₀ ℕ := finsupp.map_domain coe

@[instance]
instance finsupp.coe_primes_to_pnat : has_coe (nat.primes →₀ ℕ) (ℕ+ →₀ ℕ) :=
⟨finsupp.primes_to_pnat⟩

lemma finsupp.coe_primes_to_pnat_to_multiset (x : nat.primes →₀ ℕ) :
  prime_multiset.to_pnat_multiset x.to_multiset = (x : ℕ+ →₀ ℕ).to_multiset :=
finsupp.to_multiset_map x coe

/-- Take the product of a function of prime powers with exponents given by a finsupp. -/
def finsupp.primes_prod_apply_pow {α : Type} [comm_monoid α] (x : nat.primes →₀ ℕ) (f : ℕ+ → α) : α :=
x.prod (λ p : nat.primes, λ k : ℕ, f (p ^ k))

/-- Take the product of prime powers with exponents given by a finsupp. -/
def finsupp.primes_prod_pow (x : nat.primes →₀ ℕ) := x.primes_prod_apply_pow id

lemma finsupp.primes_prod_pow_eq (x : nat.primes →₀ ℕ) :
  x.primes_prod_pow= x.prod (λ p : nat.primes, λ k : ℕ, (p ^ k)) := rfl

lemma finsupp.primes_prod_pow_eq_coe_prod_pow (x : nat.primes →₀ ℕ) :
  x.primes_prod_pow= (x : ℕ+ →₀ ℕ).prod pow :=
begin
  change x.primes_prod_pow = (finsupp.map_domain coe x).prod pow,
  rw [finsupp.prod_map_domain_index, finsupp.primes_prod_pow_eq], simp,
  intros, rw pow_add,
end

lemma finsupp.primes_prod_pow_eq_prod_to_multiset (x : nat.primes →₀ ℕ) :
  x.primes_prod_pow= prime_multiset.prod x.to_multiset :=
begin
  rw [prime_multiset.prod, finsupp.primes_prod_pow_eq_coe_prod_pow,
    ← finsupp.prod_to_multiset, ← finsupp.coe_primes_to_pnat_to_multiset], refl
end

/-- The value of this finsupp at a prime is the multiplicity of that prime in n. -/
def factor_finsupp (n : ℕ+) : nat.primes →₀ ℕ := n.factor_multiset.to_finsupp

end basics

section finsupp_lattice

variables {α β : Type} [has_zero β]

@[simp]
lemma nat.inf_zero_iff {m n : ℕ} : m ⊓ n = 0 ↔ m = 0 ∨ n = 0 :=
begin
  split, swap, intro h, cases h; rw h; simp,
  unfold has_inf.inf, unfold semilattice_inf.inf, unfold lattice.inf, unfold min,
  intro hmin, by_cases m = 0, left, apply h,
  rw if_neg _ at hmin, right, apply hmin, contrapose hmin,
  simp only [not_lt, not_le] at hmin, rw if_pos hmin, apply h
end

lemma nat.zero_eq_bot : (0 : ℕ) = ⊥ := rfl

instance finsupp.has_inf [semilattice_inf β] :
  has_inf (α →₀ β) :=
begin
  refine ⟨_⟩, intros v1 v2,
  refine ⟨(v1.support ∪ v2.support).filter (λ x, v1 x ⊓ v2 x ≠ 0),
    (λ (a : α), (v1 a ⊓ v2 a)), _⟩,
  intro a, simp only [finsupp.mem_support_iff, ne.def, finset.mem_union, finset.mem_filter],
  apply and_iff_right_of_imp, contrapose, push_neg,
  intro h, rw [h.left, h.right], apply inf_idem,
end

@[simp]
lemma finsupp.inf_apply [semilattice_inf β] {a : α} {f g : α →₀ β} : (f ⊓ g) a = f a ⊓ g a := rfl

@[simp]
lemma finsupp.nat.support_inf {f g : α →₀ ℕ} : (f ⊓ g).support = f.support ∩ g.support :=
begin
  unfold has_inf.inf, dsimp,
  have h : ∀ m n : ℕ, m ⊓ n = semilattice_inf.inf m n, intros, refl,
  ext, simp [← h], tauto,
end

instance finsupp.has_sup [semilattice_sup β]:
  has_sup (α →₀ β) :=
begin
  refine ⟨_⟩, intros v1 v2,
  refine ⟨(v1.support ∪ v2.support).filter (λ x, v1 x ⊔ v2 x ≠ 0),
    (λ (a : α), (v1 a ⊔ v2 a)), _⟩,
  intro a, simp only [finsupp.mem_support_iff, ne.def, finset.mem_union, finset.mem_filter],
  apply and_iff_right_of_imp, contrapose, push_neg,
  intro h, rw [h.left, h.right], apply sup_idem,
end

@[simp]
lemma finsupp.sup_apply [semilattice_sup β] {a : α} {f g : α →₀ β} : (f ⊔ g) a = f a ⊔ g a := rfl

@[simp]
lemma finsupp.nat.support_sup {f g : α →₀ ℕ} : (f ⊔ g).support = f.support ∪ g.support :=
begin
  unfold has_sup.sup, dsimp, ext,
  simp only [finsupp.mem_support_iff, ne.def, finset.mem_union, finset.mem_filter],
  apply and_iff_left_of_imp, repeat {rw ← bot_eq_zero}, contrapose, push_neg,
  rw ← sup_eq_bot_iff, intro h, rw ← h, refl,
end



@[instance]
instance finsupp.lattice : lattice (α →₀ ℕ) :=
begin
  refine lattice.mk has_sup.sup has_le.le has_lt.lt _ _ _ _ _ _ _ has_inf.inf _ _ _,
  exact (finsupp.preorder).le_refl,
  exact (finsupp.preorder).le_trans,
  { simp only [auto_param_eq], intros a b, apply lt_iff_le_not_le,
  },
  exact (finsupp.partial_order).le_antisymm,
  intros, rw finsupp.le_iff, intros, simp,
  intros, rw finsupp.le_iff, intros, simp,
  { intros, rw finsupp.le_iff at *,
    intros, rw finsupp.sup_apply, apply sup_le,
    { by_cases s ∈ a.support, apply a_1 s h,
      simp only [finsupp.mem_support_iff, classical.not_not] at h, rw h, simp },
    { by_cases s ∈ b.support, apply a_2 s h,
      simp only [finsupp.mem_support_iff, classical.not_not] at h, rw h, simp }
    },
  intros, rw finsupp.le_iff, intros, simp,
  intros, rw finsupp.le_iff, intros, simp,
  { intros, rw finsupp.le_iff at *, intros,
    rw finsupp.inf_apply, apply le_inf, apply a_1 s H, apply a_2 s H }
end

@[instance]
instance finsupp.semilattice_inf_bot : semilattice_inf_bot (α →₀ ℕ) :=
{ bot := 0,
  bot_le := by { intro a, simp [finsupp.le_iff] },
..finsupp.lattice}

@[simp]
lemma factor_finsupp_to_multiset_eq_factor_multiset {n : ℕ+} :
  (factor_finsupp n).to_multiset = n.factor_multiset :=
by { unfold factor_finsupp, simp }

lemma finsupp.of_multiset_strict_mono : strict_mono (@finsupp.of_multiset α) :=
begin
  unfold strict_mono, intros, rw lt_iff_le_and_ne at *, split,
  { rw finsupp.le_iff, intros s hs, repeat {rw finsupp.of_multiset_apply},
    rw multiset.le_iff_count at a_1, apply a_1.left },
  { have h := a_1.right, contrapose h, simp at *,
    apply finsupp.equiv_multiset.symm.injective h }
end

lemma finsupp.nat.bot_eq_zero : (⊥ : α →₀ ℕ) = 0 := rfl

@[simp]
lemma finsupp.nat.disjoint_iff {x y : α →₀ ℕ} : disjoint x y ↔ disjoint x.support y.support :=
begin
  unfold disjoint, repeat {rw le_bot_iff},
  rw [finsupp.nat.bot_eq_zero, ← finsupp.support_eq_empty, finsupp.nat.support_inf], refl,
end

end finsupp_lattice

section lattice_isos

variables {α β : Type}

lemma order_embedding.map_inf_le [semilattice_inf α] [semilattice_inf β]
  (f : (has_le.le : α → α → Prop) ≼o (has_le.le : β → β → Prop))
  {a₁ a₂ : α}:
  f (a₁ ⊓ a₂) ≤ f a₁ ⊓ f a₂ :=
by { apply le_inf; rw ← f.ord; simp }

lemma order_iso.map_inf [semilattice_inf α] [semilattice_inf β]
  (f : (has_le.le : α → α → Prop) ≃o (has_le.le : β → β → Prop))
  {a₁ a₂ : α}:
  f (a₁ ⊓ a₂) = f a₁ ⊓ f a₂ :=
begin
  apply le_antisymm, apply f.to_order_embedding.map_inf_le,
  rw f.symm.ord, rw order_iso.symm_apply_apply,
  conv_rhs {rw [← order_iso.symm_apply_apply f a₁, ← order_iso.symm_apply_apply f a₂]},
  apply f.symm.to_order_embedding.map_inf_le
end

lemma order_embedding.le_map_sup [semilattice_sup α] [semilattice_sup β]
  (f : (has_le.le : α → α → Prop) ≼o (has_le.le : β → β → Prop))
  {a₁ a₂ : α}:
  f a₁ ⊔ f a₂ ≤ f (a₁ ⊔ a₂) :=
by { apply sup_le; rw ← f.ord; simp }

lemma order_iso.map_sup [semilattice_sup α] [semilattice_sup β]
  (f : (has_le.le : α → α → Prop) ≃o (has_le.le : β → β → Prop))
  {a₁ a₂ : α}:
  f (a₁ ⊔ a₂) = f a₁ ⊔ f a₂ :=
begin
  apply le_antisymm, swap, apply f.to_order_embedding.le_map_sup,
  rw f.symm.ord, rw order_iso.symm_apply_apply,
  conv_lhs {rw [← order_iso.symm_apply_apply f a₁, ← order_iso.symm_apply_apply f a₂]},
  apply f.symm.to_order_embedding.le_map_sup
end


end lattice_isos

section finsupp_lattice_iso_multiset

/-- The lattice of finsupps to ℕ is order isomorphic to that of multisets.  -/
def finsupp.order_iso_multiset (α : Type) :
  (has_le.le : (α →₀ ℕ) → (α →₀ ℕ) → Prop) ≃o (has_le.le : (multiset α) → (multiset α) → Prop) :=
⟨finsupp.equiv_multiset, begin
  intros a b, unfold finsupp.equiv_multiset, dsimp,
  rw multiset.le_iff_count, simp only [finsupp.count_to_multiset], refl
end ⟩

@[simp]
lemma finsupp.order_iso_multiset_factor_finsupp {n : ℕ+} :
  finsupp.order_iso_multiset nat.primes (factor_finsupp n) = n.factor_multiset :=
by { simp [finsupp.order_iso_multiset, finsupp.equiv_multiset] }

@[simp]
lemma finsupp.order_iso_multiset_symm_factor_multiset {n : ℕ+} :
  (finsupp.order_iso_multiset nat.primes).symm n.factor_multiset = factor_finsupp n :=
by { apply (finsupp.order_iso_multiset nat.primes).to_order_embedding.inj, simp }

/-- Factorization is a bijection from ℕ+ to finsupp.primes_ -/
def pnat.prime_finsupp_equiv : ℕ+ ≃ (nat.primes →₀ ℕ) :=
equiv.trans pnat.factor_multiset_equiv ((finsupp.order_iso_multiset nat.primes).to_equiv.symm)

@[simp]
lemma pnat.prime_finsupp_equiv_eq_factor_finsupp :
  ⇑pnat.prime_finsupp_equiv = factor_finsupp :=
begin
  transitivity finsupp.of_multiset ∘ pnat.factor_multiset, refl,
  ext, unfold factor_finsupp, simp,
end

@[simp]
lemma pnat.prime_finsupp_equiv_symm_eq_prod_pow :
  ⇑pnat.prime_finsupp_equiv.symm = finsupp.primes_prod_pow :=
begin
  transitivity prime_multiset.prod ∘ finsupp.to_multiset, refl,
  ext, rw finsupp.primes_prod_pow_eq_prod_to_multiset,
end

end finsupp_lattice_iso_multiset

section basic_number_theory_definitions

lemma dvd_iff_le_factor_finsupps {m n : ℕ+} :
  m ∣ n ↔ factor_finsupp m ≤ factor_finsupp n :=
begin
  rw (finsupp.order_iso_multiset nat.primes).ord, simp [pnat.factor_multiset_le_iff],
end

@[simp]
lemma factor_finsupp_mul {m n : ℕ+} :
  factor_finsupp (m * n) = factor_finsupp m + factor_finsupp n :=
begin
  apply finsupp.equiv_multiset.injective,
  change finsupp.to_multiset (factor_finsupp (m * n)) =
    finsupp.to_multiset (factor_finsupp m + factor_finsupp n),
  simp [finsupp.to_multiset_add, factor_finsupp, pnat.factor_multiset_mul]
end

lemma factor_finsupp_gcd_eq_inf_factor_finsupps {m n : ℕ+} :
  factor_finsupp (m.gcd n) = (factor_finsupp m) ⊓ (factor_finsupp n) :=
begin
  repeat {rw ← finsupp.order_iso_multiset_symm_factor_multiset},
  rw [pnat.factor_multiset_gcd, order_iso.map_inf],
end

@[simp]
lemma factor_finsupp_one : factor_finsupp 1 = 0 :=
begin
  apply finsupp.equiv_multiset.injective,
  change finsupp.to_multiset (factor_finsupp 1) = finsupp.to_multiset 0,
  rw [finsupp.to_multiset_zero, factor_finsupp_to_multiset_eq_factor_multiset,
    pnat.factor_multiset_one]
 end

lemma coprime_iff_disjoint_factor_finsupps {m n : ℕ+} :
  m.coprime n ↔ disjoint (factor_finsupp m) (factor_finsupp n) :=
begin
  rw [pnat.coprime, disjoint_iff, ← factor_finsupp_gcd_eq_inf_factor_finsupps,
    finsupp.nat.bot_eq_zero],
  rw ← factor_finsupp_one, split; intro h, rw h,
  apply pnat.prime_finsupp_equiv.injective, simpa,
end

lemma coprime_iff_disjoint_supports {m n : ℕ+} :
  m.coprime n ↔ disjoint (factor_finsupp m).support (factor_finsupp n).support :=
begin
  rw coprime_iff_disjoint_factor_finsupps, rw finsupp.nat.disjoint_iff,
  unfold disjoint, repeat {rw le_bot_iff},
  split; intro h; rw ← h; ext; simp, --WHY DOESN'T REFL WORK???
end

end basic_number_theory_definitions

/-- Just wraps to_multiset in the prime_multiset type for the next lemma to typecheck. -/
def finsupp.to_prime_multiset (f : nat.primes →₀ ℕ) : prime_multiset := f.to_multiset

lemma coe_pnat_commute_to_multiset {f : nat.primes →₀ ℕ} :
(↑f : ℕ+ →₀ ℕ).to_multiset =  prime_multiset.to_pnat_multiset f.to_prime_multiset :=
begin
  unfold prime_multiset.to_pnat_multiset, unfold finsupp.to_prime_multiset,
  rw finsupp.to_multiset_map, refl
end

lemma prod_pow_factor_finsupp (n : ℕ+) :
  (factor_finsupp n).primes_prod_pow = n :=
begin
  rw finsupp.primes_prod_pow_eq_prod_to_multiset,
  rw factor_finsupp_to_multiset_eq_factor_multiset,
  rw pnat.prod_factor_multiset
end

lemma factor_finsupp_prod_pow (f : nat.primes →₀ ℕ) :
factor_finsupp (f.primes_prod_pow) = f :=
begin
  unfold factor_finsupp, conv_rhs {rw ← f.to_multiset_to_finsupp},
  rw ← prime_multiset.factor_multiset_prod f.to_multiset,
  rw finsupp.primes_prod_pow_eq_prod_to_multiset
end

lemma factor_finsupp_inj : function.injective factor_finsupp :=
begin
  unfold function.injective, intros a b h,
  rw [← prod_pow_factor_finsupp a, ← prod_pow_factor_finsupp b, h]
end

section prime_powers

variables {p : nat.primes} {n : ℕ+} {k : ℕ}

@[simp]
lemma factor_finsupp_prime : factor_finsupp ↑p = finsupp.single p 1 :=
begin
  apply finsupp.equiv_multiset.injective,
  change finsupp.to_multiset (factor_finsupp ↑p) = finsupp.to_multiset (finsupp.single p 1),
  rw [finsupp.to_multiset_single, factor_finsupp_to_multiset_eq_factor_multiset,
    pnat.factor_multiset_of_prime, prime_multiset.of_prime],
  simp
end

@[simp]
lemma factor_finsupp_pow : factor_finsupp (n ^ k) = k • factor_finsupp n :=
begin
  induction k, simp,
  rw [pow_succ, nat.succ_eq_add_one, add_smul, ← k_ih, mul_comm], simp
end


@[simp]
lemma nat.smul_one : k • 1 = k := by { rw nat.smul_def, simp }

@[simp]
lemma factor_finsupp_pow_prime : factor_finsupp (p ^ k) = finsupp.single p k := by simp

end prime_powers


section coprime_part

variables (p : nat.primes) (n : ℕ+)

/-- The greatest divisor n coprime to prime p. -/
def coprime_part : ℕ+ :=
finsupp.primes_prod_pow ((factor_finsupp n).erase p)

variables {p} {n}

@[simp]
lemma factor_finsupp_coprime_part_eq_erase_factor_finsupp :
  factor_finsupp (coprime_part p n) = (factor_finsupp n).erase p :=
by { rw coprime_part, apply factor_finsupp_prod_pow _, }

variable (p)
lemma factor_finsupp_coprime_part_add_single_eq_self :
  factor_finsupp (coprime_part p n) + finsupp.single p ((factor_finsupp n) p) = factor_finsupp n :=
by { simp [finsupp.erase_add_single] }

variables {p} (n)
lemma pow_mult_coprime_part_eq_self : (coprime_part p n) * p ^ ((factor_finsupp n) p) = n :=
begin
  apply factor_finsupp_inj, rw factor_finsupp_mul,
  rw factor_finsupp_pow_prime,
  rw factor_finsupp_coprime_part_add_single_eq_self
end

variable {n}

lemma prime_dvd_iff_mem_support_factor_finsupp : ↑p ∣ n ↔ p ∈ (factor_finsupp n).support :=
begin
  rw dvd_iff_le_factor_finsupps, rw finsupp.le_iff, simp [finsupp.mem_support_single],
  cases (factor_finsupp n) p, simp, omega
end

lemma prime_dvd_iff_factor_finsupp_pos : ↑p ∣ n ↔ 0 < factor_finsupp n p :=
by { rw prime_dvd_iff_mem_support_factor_finsupp, simp [nat.pos_iff_ne_zero] }

lemma not_dvd_coprime_part : ¬ (↑p ∣ (coprime_part p n)) :=
begin
  rw [dvd_iff_le_factor_finsupps, finsupp.le_iff], push_neg, existsi p,
  rw [factor_finsupp_prime, factor_finsupp_coprime_part_eq_erase_factor_finsupp],
  simp,
end

lemma coprime_pow_coprime_part {k : ℕ} (pos : 0 < k): ((p : ℕ+) ^ k).coprime (coprime_part p n) :=
begin
  rw coprime_iff_disjoint_supports,
  rw [factor_finsupp_pow, factor_finsupp_prime, factor_finsupp_coprime_part_eq_erase_factor_finsupp],
  simp only [finsupp.support_erase, nat.smul_one, finsupp.smul_single],
  rw finsupp.support_single_ne_zero, simp, omega
end

lemma coprime_of_prime_not_dvd (h : ¬ ↑p ∣ n) : n.coprime p :=
begin
  rw coprime_iff_disjoint_supports,
  rw prime_dvd_iff_factor_finsupp_pos at h,
  rw factor_finsupp_prime, rw finsupp.support_single_ne_zero, swap, omega,
  rw finset.disjoint_singleton, simp only [finsupp.mem_support_iff, classical.not_not],
  simp only [nat.pos_iff_ne_zero, classical.not_not] at h, apply h
end

lemma dvd_coprime_part_of_coprime_dvd {m : ℕ+} (hmn : has_dvd.dvd m n) (hmp : ¬ ↑p ∣ m) :
  m ∣ (coprime_part p n) :=
begin
  rw prime_dvd_iff_mem_support_factor_finsupp at hmp,
  rw dvd_iff_le_factor_finsupps at *, rw finsupp.le_iff at *, intro q,
  intro h, simp only [factor_finsupp_coprime_part_eq_erase_factor_finsupp],
  rw finsupp.erase_ne, apply hmn q h, intro qp, rw qp at h, apply hmp h
end

@[simp]
lemma coprime_part_prime_mul_eq_coprime_part : coprime_part p (p * n) = coprime_part p n :=
by { apply factor_finsupp_inj, simp }

/-- 2 as an element of nat.primes. -/
def two_prime : nat.primes := ⟨2, nat.prime_two⟩

variable (n)
/-- The greatest odd factor of a pnat. -/
def odd_part : ℕ+ := coprime_part two_prime n
variable {n}

lemma dvd_odd_part_of_odd_dvd {m : ℕ+} (hmn : has_dvd.dvd m n) (hmp : ¬ 2 ∣ m) :
  m ∣ (odd_part n) :=
begin
  apply dvd_coprime_part_of_coprime_dvd hmn, apply hmp
end

lemma coprime_pow_odd_part {k : ℕ} (pos : 0 < k) : ((2 : ℕ+) ^ k).coprime (odd_part n) :=
begin
  have h : pnat.coprime (↑two_prime ^ k) (coprime_part two_prime n) := coprime_pow_coprime_part pos,
  apply h
end

variable (n)
lemma pow_mult_odd_part_eq_self : (odd_part n) * 2 ^ (factor_finsupp n two_prime) = n :=
begin
  rw odd_part,
  --conv_rhs {rw ← prod_pow_factor_finsupp n},
  change coprime_part two_prime n * ↑two_prime ^ (factor_finsupp n) two_prime = n,
  rw pow_mult_coprime_part_eq_self n,
end
variable {n}

@[simp]
lemma odd_part_two_mul_eq_odd_part : odd_part (2 * n) = odd_part n :=
coprime_part_prime_mul_eq_coprime_part

end coprime_part

section multiplicative

--in newest algebra/big_operators
lemma finset.prod_induction {α : Type} {s : finset α} {M : Type*} [comm_monoid M] (f : α → M) (p : M → Prop)
(p_mul : ∀ a b, p a → p b → p (a * b)) (p_one : p 1) (p_s : ∀ x ∈ s, p $ f x) :
p $ ∏ x in s, f x :=
begin
  classical,
  induction s using finset.induction with x hx s hs, simpa,
  rw finset.prod_insert, swap, assumption,
  apply p_mul, apply p_s, simp,
  apply hs, intros a ha, apply p_s, simp [ha],
end

variables {α : Type} [comm_monoid α]
/-- Determines if a function is multiplicative (in the number-theoretic sense). -/
def is_multiplicative (f : ℕ+ → α): Prop :=
f 1 = 1 ∧ ∀ m n : ℕ+, nat.coprime m n → f (m * n) = f m * f n

variables {f : ℕ+ → α}

lemma multiplicative_prod_eq_prod_multiplicative
  (h : is_multiplicative f) {x : nat.primes →₀ ℕ} {s : finset nat.primes} :
  f (∏ (a : nat.primes) in s, ↑a ^ x a) = ∏ (a : nat.primes) in s, f (↑a ^ x a) :=
begin
  apply finset.induction_on s, simp [h.left],
  intros a s anins ih, repeat {rw finset.prod_insert anins}, rw [h.right, ih],
  rw pnat.coprime_coe, rw ← pow_one (∏ (x_1 : nat.primes) in s, ↑x_1 ^ x x_1),
  apply pnat.coprime.pow, apply finset.prod_induction, swap, simp,
  { intros, apply pnat.coprime.symm, apply pnat.coprime.mul a_2.symm a_3.symm, },
  { intros p hp, rw ← pnat.coprime_coe, rw ← nat.pow_one ↑↑a, rw pnat.pow_coe,
    apply nat.coprime_pow_primes,
    rw nat.primes.coe_pnat_nat, apply a.property,
    rw nat.primes.coe_pnat_nat, apply p.property,
    intro ap, apply anins, rw nat.primes.coe_nat_inj a p _, apply hp,
    repeat {rw nat.primes.coe_pnat_nat at ap}, apply ap,
  }
end

lemma multiplicative_from_prime_pow (h : is_multiplicative f) :
  ∀ n : ℕ+, f(n) = (factor_finsupp n).primes_prod_apply_pow f :=
begin
  intro n, rw finsupp.primes_prod_apply_pow,
  conv_lhs {rw ← prod_pow_factor_finsupp n}, rw finsupp.primes_prod_pow_eq, unfold finsupp.prod,
  apply multiplicative_prod_eq_prod_multiplicative h,
end

end multiplicative
