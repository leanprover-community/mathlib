/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris Van Doorn
-/

import measure_theory.borel_space

/-!
# Regular measures

A measure is `regular` if it satisfies the following properties:
* it is finite on compact sets;
* it is outer regular: the measure of any measurable set `A` is the infimum of `μ U` over all
  open sets `U` containing `A`;
* it is inner regular for open sets: the measure of any open set `U` is the supremum of `μ K`
  over all compact sets `K` contained in `U`.

These conditions imply inner regularity for all measurable sets of finite measure, but in general
not for all sets. For a counterexample, consider the group `ℝ × ℝ` where the first factor has
the discrete topology and the second one the usual topology. It is a locally compact Hausdorff
topological group, with Haar measure equal to Lebesgue measure on each vertical fiber. The set
`ℝ × {0}` has infinite measure (by outer regularity), but any compact set it contains has zero
measure (as it is finite).

Several authors require as a definition of regularity that all measurable sets are inner regular.
We have opted for the slightly weaker definition above as it holds for all Haar measures, it is
enough for essentially all applications, and it is equivalent to the other definition when the
measure is sigma-finite.
-/

open set
open_locale ennreal

namespace measure_theory
namespace measure

variables {α β : Type*} [measurable_space α] [topological_space α] {μ : measure α}
/-- A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf { μ(U) | A ⊆ U open }` for `A` measurable;
  - it is inner regular: `μ(U) = sup { μ(K) | K ⊆ U compact }` for `U` open. -/
class regular (μ : measure α) : Prop :=
(lt_top_of_is_compact : ∀ {{K : set α}}, is_compact K → μ K < ∞)
(outer_regular : ∀ {{A : set α}}, measurable_set A →
  (⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U) ≤ μ A)
(inner_regular : ∀ {{U : set α}}, is_open U →
  μ U ≤ ⨆ (K : set α) (h : is_compact K) (h2 : K ⊆ U), μ K)

/-- A measure `μ` is regular if
  - it is finite on all compact sets;
  - it is outer regular: `μ(A) = inf { μ(U) | A ⊆ U open }` for `A` measurable;
  - it is inner regular: `μ(U) = sup { μ(K) | K ⊆ U compact }` for `U` open. -/
class weakly_regular (μ : measure α) : Prop :=
(outer_regular : ∀ {{A : set α}}, measurable_set A →
  (⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U) ≤ μ A)
(inner_regular : ∀ {{U : set α}}, is_open U →
  μ U ≤ ⨆ (F : set α) (h : is_compact F) (h2 : F ⊆ U), μ F)

instance regular.weakly_regular [regular μ] : weakly_regular μ :=
{ outer_regular := regular.outer_regular,
  inner_regular

}

namespace regular

lemma outer_regular_eq [regular μ] {{A : set α}}
  (hA : measurable_set A) : (⨅ (U : set α) (h : is_open U) (h2 : A ⊆ U), μ U) = μ A :=
le_antisymm (regular.outer_regular hA) $ le_infi $ λ s, le_infi $ λ hs, le_infi $ λ h2s, μ.mono h2s

lemma inner_regular_eq [regular μ] {{U : set α}}
  (hU : is_open U) : (⨆ (K : set α) (h : is_compact K) (h2 : K ⊆ U), μ K) = μ U :=
le_antisymm (supr_le $ λ s, supr_le $ λ hs, supr_le $ λ h2s, μ.mono h2s) (regular.inner_regular hU)

lemma exists_compact_not_null [regular μ] : (∃ K, is_compact K ∧ μ K ≠ 0) ↔ μ ≠ 0 :=
by simp_rw [ne.def, ← measure_univ_eq_zero, ← regular.inner_regular_eq is_open_univ,
    ennreal.supr_eq_zero, not_forall, exists_prop, subset_univ, true_and]

protected lemma map [opens_measurable_space α] [measurable_space β] [topological_space β]
  [t2_space β] [borel_space β] [regular μ] (f : α ≃ₜ β) :
  (measure.map f μ).regular :=
begin
  have hf := f.measurable,
  have h2f := f.to_equiv.injective.preimage_surjective,
  have h3f := f.to_equiv.surjective,
  split,
  { intros K hK, rw [map_apply hf hK.measurable_set],
    apply regular.lt_top_of_is_compact,
    rwa f.compact_preimage },
  { intros A hA,
    rw [map_apply hf hA, ← regular.outer_regular_eq (hf hA)], swap, { apply_instance },
    refine le_of_eq _,
    apply infi_congr (preimage f) h2f,
    intro U,
    apply infi_congr_Prop f.is_open_preimage,
    intro hU,
    apply infi_congr_Prop h3f.preimage_subset_preimage_iff,
    intro h2U,
    rw [map_apply hf hU.measurable_set], },
  { intros U hU,
    rw [map_apply hf hU.measurable_set, ← regular.inner_regular_eq (hU.preimage f.continuous)],
    swap, { apply_instance },
    refine ge_of_eq _,
    apply supr_congr (preimage f) h2f,
    intro K,
    apply supr_congr_Prop f.compact_preimage,
    intro hK,
    apply supr_congr_Prop h3f.preimage_subset_preimage_iff,
    intro h2U,
    rw [map_apply hf hK.measurable_set] }
end

protected lemma smul [regular μ] {x : ℝ≥0∞} (hx : x < ∞) :
  (x • μ).regular :=
begin
  split,
  { intros K hK, exact ennreal.mul_lt_top hx (regular.lt_top_of_is_compact hK) },
  { intros A hA, rw [coe_smul],
    refine le_trans _ (ennreal.mul_left_mono $ regular.outer_regular hA),
    simp only [infi_and'], simp only [infi_subtype'],
    haveI : nonempty {s : set α // is_open s ∧ A ⊆ s} := ⟨⟨set.univ, is_open_univ, subset_univ _⟩⟩,
    rw [ennreal.mul_infi], refl', exact ne_of_lt hx },
  { intros U hU,
    rw [coe_smul],
    refine le_trans (ennreal.mul_left_mono $ regular.inner_regular hU) _,
    simp only [supr_and'],
    simp only [supr_subtype'],
    rw [ennreal.mul_supr], refl' }
end

/-- A regular measure in a σ-compact space is σ-finite. -/
@[priority 100] -- see Note [lower instance priority]
instance sigma_finite [opens_measurable_space α] [t2_space α] [sigma_compact_space α]
  [regular μ] : sigma_finite μ :=
⟨⟨{ set := compact_covering α,
  set_mem := λ n, (is_compact_compact_covering α n).measurable_set,
  finite := λ n, regular.lt_top_of_is_compact $ is_compact_compact_covering α n,
  spanning := Union_compact_covering α }⟩⟩

end regular

open filter
open_locale topological_space nnreal ennreal big_operators

section zoug

variables {X : Type*} [pseudo_emetric_space X] [measurable_space X] [borel_space X] {ν : measure X}
  [finite_measure ν]

lemma weakly_regular_aux1 (U : set X) (hU : is_open U) (ε : ℝ≥0∞) (hε : 0 < ε) :
  ∃ (F : set X), is_closed F ∧ F ⊆ U ∧ ν U ≤ ν F + ε :=
begin
  rcases hU.exists_Union_is_closed with ⟨F, F_closed, F_subset, F_Union, F_mono⟩,
  have L : tendsto (λ n, ν (F n) + ε) at_top (𝓝 (ν U + ε)),
  { rw ← F_Union,
    refine tendsto.add _ tendsto_const_nhds,
    apply tendsto_measure_Union (λ n, is_closed.measurable_set (F_closed n)) F_mono },
  have nu_lt : ν U < ν U + ε,
    by simpa using (ennreal.add_lt_add_iff_left (measure_lt_top ν U)).2 hε,
  rcases ((tendsto_order.1 L).1 _ nu_lt).exists with ⟨n, hn⟩,
  exact ⟨F n, F_closed n, F_subset n, hn.le⟩
end

lemma weakly_regular : ∀ ⦃s : set X⦄ (hs : measurable_set s),
  ∀ ε > 0, (∃ (U : set X), is_open U ∧ s ⊆ U ∧ ν U ≤ ν s + ε)
    ∧ (∃ (F : set X), is_closed F ∧ F ⊆ s ∧ ν s ≤ ν F + ε) :=
begin
  refine measurable_space.induction_on_inter borel_space.measurable_eq is_pi_system_is_open _ _ _ _,
  { assume ε hε,
    exact ⟨⟨∅, is_open_empty, subset.refl _, by simp only [measure_empty, zero_le]⟩,
            ⟨∅, is_closed_empty, subset.refl _, by simp only [measure_empty, zero_le]⟩⟩ },
  { assume U hU ε hε,
    exact ⟨⟨U, hU, subset.refl _, le_self_add⟩, weakly_regular_aux1 U hU ε hε⟩ },
  { assume s hs h ε εpos,
    rcases h ε εpos with ⟨⟨U, U_open, U_subset, nu_U⟩, ⟨F, F_closed, F_subset, nu_F⟩⟩,
    refine ⟨⟨Fᶜ, is_open_compl_iff.2 F_closed, compl_subset_compl.2 F_subset, _⟩,
            ⟨Uᶜ, is_closed_compl_iff.2 U_open, compl_subset_compl.2 U_subset, _⟩⟩,
    { apply ennreal.le_of_add_le_add_left (measure_lt_top ν F),
      calc
        ν F + ν Fᶜ = ν s + ν sᶜ :
          by rw [measure_add_measure_compl hs, measure_add_measure_compl F_closed.measurable_set]
        ... ≤ (ν F + ε) + ν sᶜ : add_le_add nu_F (le_refl _)
        ... = ν F + (ν sᶜ + ε) : by abel },
    { apply ennreal.le_of_add_le_add_left (measure_lt_top ν s),
      calc
        ν s + ν sᶜ = ν U + ν Uᶜ :
          by rw [measure_add_measure_compl hs, measure_add_measure_compl U_open.measurable_set]
        ... ≤ (ν s + ε) + ν Uᶜ : add_le_add nu_U (le_refl _)
        ... = ν s + (ν Uᶜ + ε) : by abel } },
  { assume s s_disj s_meas hs ε εpos,
    set δ := ε / 2 with hδ,
    have δpos : 0 < δ := ennreal.half_pos εpos,
    let a : ℝ≥0∞ := 2⁻¹,
    have a_pos : 0 < a, by simp [a],
    split,
    { have : ∀ n, ∃ (U : set X), is_open U ∧ s n ⊆ U ∧ ν U ≤ ν (s n) + δ * a ^ n :=
        λ n, (hs n _ (ennreal.mul_pos.2 ⟨δpos, ennreal.pow_pos a_pos n⟩)).1,
      choose U hU using this,
      refine ⟨(⋃ n, U n), is_open_Union (λ n, (hU n).1), Union_subset_Union (λ n, (hU n).2.1), _⟩,
      calc
      ν (⋃ (n : ℕ), U n)
          ≤ ∑' n, ν (U n) : measure_Union_le _
      ... ≤ ∑' n, (ν (s n) + δ * a ^ n) : ennreal.tsum_le_tsum (λ n, (hU n).2.2)
      ... = ∑' n, ν (s n) + δ * ∑' n, a ^ n : by rw [ennreal.tsum_add, ennreal.tsum_mul_left]
      ... = ν (⋃ (i : ℕ), s i) + ε :
      begin
        congr' 1, { rw measure_Union s_disj s_meas },
        simp only [δ, ennreal.tsum_geometric, ennreal.inv_inv, ennreal.one_sub_inv_two],
        exact ennreal.mul_div_cancel two_ne_zero' ennreal.coe_ne_top,
      end },
    { have L : tendsto (λ n, ∑ i in finset.range n, ν (s i) + δ) at_top (𝓝 (ν (⋃ i, s i) + δ)),
      { rw measure_Union s_disj s_meas,
        refine tendsto.add (ennreal.tendsto_nat_tsum _) tendsto_const_nhds },
      have nu_lt : ν (⋃ i, s i) < ν (⋃ i, s i) + δ,
        by simpa only [add_zero] using (ennreal.add_lt_add_iff_left (measure_lt_top ν _)).mpr δpos,
      obtain ⟨n, hn, npos⟩ :
        ∃ n, (ν (⋃ (i : ℕ), s i) < ∑ (i : ℕ) in finset.range n, ν (s i) + δ) ∧ (0 < n) :=
      (((tendsto_order.1 L).1 _ nu_lt).and (eventually_gt_at_top 0)).exists,
      have : ∀ i, ∃ (F : set X), is_closed F ∧ F ⊆ s i ∧ ν (s i) ≤ ν F + δ / n :=
        λ i, (hs i _ (ennreal.div_pos_iff.2 ⟨ne_of_gt δpos, ennreal.nat_ne_top n⟩)).2,
      choose F hF using this,
      have F_disj: pairwise (disjoint on F) :=
        pairwise.mono (λ i j hij, disjoint.mono (hF i).2.1 (hF j).2.1 hij) s_disj,
      refine ⟨⋃ i ∈ finset.range n, F i, _, _, _⟩,
      { exact is_closed_bUnion (by simpa using finite_lt_nat n) (λ i hi, (hF i).1) },
      { assume x hx,
        simp only [exists_prop, mem_Union, finset.mem_range] at hx,
        rcases hx with ⟨i, i_lt, hi⟩,
        simp only [mem_Union],
        exact ⟨i, (hF i).2.1 hi⟩ },
      { calc
        ν (⋃ (i : ℕ), s i)
            ≤ ∑ (i : ℕ) in finset.range n, ν (s i) + δ : hn.le
        ... ≤ (∑ (i : ℕ) in finset.range n, (ν (F i) + δ / n)) + δ :
          add_le_add (finset.sum_le_sum (λ i hi, (hF i).2.2)) (le_refl _)
        ... = ν (⋃ i ∈ finset.range n, F i) + ε :
        begin
          simp only [finset.sum_add_distrib, finset.sum_const, nsmul_eq_mul, finset.card_range],
          rw [ennreal.mul_div_cancel' _ (ennreal.nat_ne_top n),
              measure_bUnion_finset (F_disj.pairwise_on _) (λ i hi, (hF i).1.measurable_set),
              hδ, add_assoc, ennreal.add_halves],
          simpa only [ne.def, nat.cast_eq_zero] using ne_of_gt npos
        end } } }
end

end zoug

end measure
end measure_theory
