/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.complement
import group_theory.sylow

/-!
# The Transfer Homomorphism

In this file we construct the transfer homomorphism.

## Main definitions

- `diff ϕ S T` : The difference of two left transversals `S` and `T` under the homomorphism `ϕ`.
- `transfer ϕ` : The transfer homomorphism induced by `ϕ`.
- `transfer_center_pow`: The transfer homomorphism `G →*  center G`.
-/

open_locale big_operators

variables {G : Type*} [group G] {H : subgroup G} {A : Type*} [comm_group A] (ϕ : H →* A)

namespace subgroup

namespace left_transversals

open finset mul_action

open_locale pointwise

variables (R S T : left_transversals (H : set G)) [finite_index H]

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff : A :=
let α := mem_left_transversals.to_equiv S.2, β := mem_left_transversals.to_equiv T.2 in
(@finset.univ (G ⧸ H) H.fintype_quotient_of_finite_index).prod $
  λ q, ϕ ⟨(α q)⁻¹ * β q, quotient_group.left_rel_apply.mp $
  quotient.exact' ((α.symm_apply_apply q).trans (β.symm_apply_apply q).symm)⟩

@[to_additive] lemma diff_mul_diff : diff ϕ R S * diff ϕ S T = diff ϕ R T :=
prod_mul_distrib.symm.trans (prod_congr rfl (λ q hq, (ϕ.map_mul _ _).symm.trans (congr_arg ϕ
  (by simp_rw [subtype.ext_iff, coe_mul, coe_mk, mul_assoc, mul_inv_cancel_left]))))

@[to_additive] lemma diff_self : diff ϕ T T = 1 :=
mul_right_eq_self.mp (diff_mul_diff ϕ T T T)

@[to_additive] lemma diff_inv : (diff ϕ S T)⁻¹ = diff ϕ T S :=
inv_eq_of_mul_eq_one_right $ (diff_mul_diff ϕ S T S).trans $ diff_self ϕ S

@[to_additive] lemma smul_diff_smul (g : G) : diff ϕ (g • S) (g • T) = diff ϕ S T :=
let h := H.fintype_quotient_of_finite_index in by exactI
prod_bij' (λ q _, g⁻¹ • q) (λ _ _, mem_univ _) (λ _ _, congr_arg ϕ (by simp_rw [coe_mk,
  smul_apply_eq_smul_apply_inv_smul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]))
  (λ q _, g • q) (λ _ _, mem_univ _) (λ q _, smul_inv_smul g q) (λ q _, inv_smul_smul g q)

end left_transversals

end subgroup

namespace monoid_hom

open mul_action subgroup subgroup.left_transversals

/-- Given `ϕ : H →* A` from `H : subgroup G` to a commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →* A`. -/
@[to_additive "Given `ϕ : H →+ A` from `H : add_subgroup G` to an additive commutative group `A`,
the transfer homomorphism is `transfer ϕ : G →+ A`."]
noncomputable def transfer [finite_index H] : G →* A :=
let T : left_transversals (H : set G) := inhabited.default in
{ to_fun := λ g, diff ϕ T (g • T),
  map_one' := by rw [one_smul, diff_self],
  map_mul' := λ g h, by rw [mul_smul, ←diff_mul_diff, smul_diff_smul] }

variables (T : left_transversals (H : set G))

@[to_additive] lemma transfer_def [finite_index H] (g : G) : transfer ϕ g = diff ϕ T (g • T) :=
by rw [transfer, ←diff_mul_diff, ←smul_diff_smul, mul_comm, diff_mul_diff]; refl

/-- Explicit computation of the transfer homomorphism. -/
lemma transfer_eq_prod_quotient_orbit_rel_zpowers_quot [finite_index H]
  (g : G) [fintype (quotient (orbit_rel (zpowers g) (G ⧸ H)))] :
  transfer ϕ g = ∏ (q : quotient (orbit_rel (zpowers g) (G ⧸ H))),
    ϕ ⟨q.out'.out'⁻¹ * g ^ function.minimal_period ((•) g) q.out' * q.out'.out',
      quotient_group.out'_conj_pow_minimal_period_mem H g q.out'⟩ :=
begin
  classical,
  letI := H.fintype_quotient_of_finite_index,
  calc transfer ϕ g = ∏ (q : G ⧸ H), _ : transfer_def ϕ (transfer_transversal H g) g
  ... = _ : ((quotient_equiv_sigma_zmod H g).symm.prod_comp _).symm
  ... = _ : finset.prod_sigma _ _ _
  ... = _ : fintype.prod_congr _ _ (λ q, _),
  simp only [quotient_equiv_sigma_zmod_symm_apply,
    transfer_transversal_apply', transfer_transversal_apply''],
  rw fintype.prod_eq_single (0 : zmod (function.minimal_period ((•) g) q.out')) (λ k hk, _),
  { simp only [if_pos, zmod.cast_zero, zpow_zero, one_mul, mul_assoc] },
  { simp only [if_neg hk, inv_mul_self],
    exact map_one ϕ },
end

/-- Auxillary lemma in order to state `transfer_eq_pow`. -/
lemma transfer_eq_pow_aux (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  g ^ H.index ∈ H :=
begin
  by_cases hH : H.index = 0,
  { rw [hH, pow_zero],
    exact H.one_mem },
  letI := fintype_of_index_ne_zero hH,
  classical,
  replace key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g ^ k ∈ H :=
  λ k g₀ hk, (_root_.congr_arg (∈ H) (key k g₀ hk)).mp hk,
  replace key : ∀ q : G ⧸ H, g ^ function.minimal_period ((•) g) q ∈ H :=
  λ q, key (function.minimal_period ((•) g) q) q.out'
    (quotient_group.out'_conj_pow_minimal_period_mem H g q),
  let f : quotient (orbit_rel (zpowers g) (G ⧸ H)) → zpowers g :=
  λ q, (⟨g, mem_zpowers g⟩ : zpowers g) ^ function.minimal_period ((•) g) q.out',
  have hf : ∀ q, f q ∈ H.subgroup_of (zpowers g) := λ q, key q.out',
  replace key := subgroup.prod_mem (H.subgroup_of (zpowers g)) (λ q (hq : q ∈ finset.univ), hf q),
  simpa only [minimal_period_eq_card, finset.prod_pow_eq_pow_sum, fintype.card_sigma,
    fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)), index_eq_card] using key,
end

lemma transfer_eq_pow [finite_index H] (g : G)
  (key : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * g ^ k * g₀ ∈ H → g₀⁻¹ * g ^ k * g₀ = g ^ k) :
  transfer ϕ g = ϕ ⟨g ^ H.index, transfer_eq_pow_aux g key⟩ :=
begin
  classical,
  letI := H.fintype_quotient_of_finite_index,
  change ∀ k g₀ (hk : g₀⁻¹ * g ^ k * g₀ ∈ H), ↑(⟨g₀⁻¹ * g ^ k * g₀, hk⟩ : H) = g ^ k at key,
  rw [transfer_eq_prod_quotient_orbit_rel_zpowers_quot, ←finset.prod_to_list, list.prod_map_hom],
  refine congr_arg ϕ (subtype.coe_injective _),
  rw [H.coe_mk, ←(zpowers g).coe_mk g (mem_zpowers g), ←(zpowers g).coe_pow, (zpowers g).coe_mk,
      index_eq_card, fintype.card_congr (self_equiv_sigma_orbits (zpowers g) (G ⧸ H)),
      fintype.card_sigma, ←finset.prod_pow_eq_pow_sum, ←finset.prod_to_list],
  simp only [coe_list_prod, list.map_map, ←minimal_period_eq_card],
  congr' 2,
  funext,
  apply key,
end

lemma transfer_center_eq_pow [finite_index (center G)] (g : G) :
  transfer (monoid_hom.id (center G)) g = ⟨g ^ (center G).index, (center G).pow_index_mem g⟩ :=
transfer_eq_pow (id (center G)) g (λ k _ hk, by rw [←mul_right_inj, hk, mul_inv_cancel_right])

variables (G)

/-- The transfer homomorphism `G →* center G`. -/
noncomputable def transfer_center_pow [finite_index (center G)] : G →* center G :=
{ to_fun := λ g, ⟨g ^ (center G).index, (center G).pow_index_mem g⟩,
  map_one' := subtype.ext (one_pow (center G).index),
  map_mul' := λ a b, by simp_rw [←show ∀ g, (_ : center G) = _,
    from transfer_center_eq_pow, map_mul] }

variables {G}

@[simp] lemma transfer_center_pow_apply [finite_index (center G)] (g : G) :
  ↑(transfer_center_pow G g) = g ^ (center G).index :=
rfl

section burnside_transfer

variables {p : ℕ} (P : sylow p G) (hP : (P : subgroup G).normalizer ≤ (P : subgroup G).centralizer)

include hP

/-- The homomorphism `G →* P` in Burnside's transfer theorem. -/
noncomputable def transfer_sylow [finite_index (P : subgroup G)] : G →* (P : subgroup G) :=
@transfer G _ P P (@subgroup.is_commutative.comm_group G _ P
  ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩) (monoid_hom.id P) _

variables [fact p.prime] [finite (sylow p G)]

/-- Auxillary lemma in order to state `transfer_sylow_eq_pow`. -/
lemma transfer_sylow_eq_pow_aux (g : G) (hg : g ∈ P) (k : ℕ) (g₀ : G) (h : g₀⁻¹ * g ^ k * g₀ ∈ P) :
  g₀⁻¹ * g ^ k * g₀ = g ^ k :=
begin
  haveI : (P : subgroup G).is_commutative := ⟨⟨λ a b, subtype.ext (hP (le_normalizer b.2) a a.2)⟩⟩,
  replace hg := (P : subgroup G).pow_mem hg k,
  obtain ⟨n, hn, h⟩ := P.conj_eq_normalizer_conj_of_mem (g ^ k) g₀ hg h,
  exact h.trans (commute.inv_mul_cancel (hP hn (g ^ k) hg).symm),
end

variables [finite_index (P : subgroup G)]

lemma transfer_sylow_eq_pow (g : G) (hg : g ∈ P) : transfer_sylow P hP g =
  ⟨g ^ (P : subgroup G).index, transfer_eq_pow_aux g (transfer_sylow_eq_pow_aux P hP g hg)⟩ :=
by apply transfer_eq_pow

lemma ker_transfer_sylow_disjoint : disjoint (transfer_sylow P hP).ker ↑P :=
begin
  intros g hg,
  obtain ⟨j, hj⟩ := P.2 ⟨g, hg.2⟩,
  have := pow_gcd_eq_one (⟨g, hg.2⟩ : (P : subgroup G))
    ((transfer_sylow_eq_pow P hP g hg.2).symm.trans hg.1) hj,
  rwa [((fact.out p.prime).coprime_pow_of_not_dvd (not_dvd_index_sylow P _)).gcd_eq_one,
    pow_one, subtype.ext_iff] at this,
  exact index_ne_zero_of_finite ∘ (relindex_top_right (P : subgroup G)).symm.trans ∘
    relindex_eq_zero_of_le_right le_top,
end

lemma ker_transfer_sylow_disjoint' (Q : sylow p G) : disjoint (transfer_sylow P hP).ker ↑Q :=
begin
  obtain ⟨g, hg⟩ := exists_smul_eq G Q P,
  rw [disjoint_iff, ←smul_left_cancel_iff (mul_aut.conj g), smul_bot, smul_inf, smul_normal,
    ←sylow.coe_subgroup_smul, hg, ←disjoint_iff],
  exact ker_transfer_sylow_disjoint P hP,
end

lemma ker_transfer_sylow_disjoint'' (Q : subgroup G) (hQ : is_p_group p Q) :
  disjoint (transfer_sylow P hP).ker Q :=
let ⟨R, hR⟩ := hQ.exists_le_sylow in (ker_transfer_sylow_disjoint' P hP R).mono_right hR

end burnside_transfer

end monoid_hom
