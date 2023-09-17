/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.instances.irrational
import topology.algebra.order.archimedean
import topology.paracompact
import topology.metric_space.metrizable
import topology.metric_space.emetric_paracompact
import data.set.intervals.monotone

/-!
# Sorgenfrey line

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `sorgenfrey_line` (notation: `ℝₗ`) to be the Sorgenfrey line. It is the real
line with the topology space structure generated by half-open intervals `set.Ico a b`.

We prove that this line is a completely normal Hausdorff space but its product with itself is not a
normal space. In particular, this implies that the topology on `ℝₗ` is neither metrizable, nor
second countable.

## Notations

- `ℝₗ`: Sorgenfrey line.

## TODO

Prove that the Sorgenfrey line is a paracompact space.

-/

open set filter topological_space
open_locale topology filter
namespace counterexample

noncomputable theory

/-- The Sorgenfrey line. It is the real line with the topology space structure generated by
half-open intervals `set.Ico a b`. -/
@[derive [conditionally_complete_linear_order, linear_ordered_field, archimedean]]
def sorgenfrey_line : Type := ℝ

localized "notation (name := sorgenfrey_line) `ℝₗ` := sorgenfrey_line" in sorgenfrey_line

namespace sorgenfrey_line

/-- Ring homomorphism between the Sorgenfrey line and the standard real line. -/
def to_real : ℝₗ ≃+* ℝ := ring_equiv.refl ℝ

instance : topological_space ℝₗ :=
topological_space.generate_from {s : set ℝₗ | ∃ a b : ℝₗ, Ico a b = s}

lemma is_open_Ico (a b : ℝₗ) : is_open (Ico a b) :=
topological_space.generate_open.basic _ ⟨a, b, rfl⟩

lemma is_open_Ici (a : ℝₗ) : is_open (Ici a) :=
Union_Ico_right a ▸ is_open_Union (is_open_Ico a)

lemma nhds_basis_Ico (a : ℝₗ) : (𝓝 a).has_basis (λ b, a < b) (λ b, Ico a b) :=
begin
  rw topological_space.nhds_generate_from,
  haveI : nonempty {x // x ≤ a} := set.nonempty_Iic_subtype,
  have : (⨅ (x : {i // i ≤ a}), 𝓟 (Ici ↑x)) = 𝓟 (Ici a),
  { refine (is_least.is_glb _).infi_eq,
    exact ⟨⟨⟨a, le_rfl⟩, rfl⟩, forall_range_iff.2 $
      λ b, principal_mono.2 $ Ici_subset_Ici.2 b.2⟩, },
  simp only [mem_set_of_eq, infi_and, infi_exists, @infi_comm _ (_ ∈ _),
    @infi_comm _ (set ℝₗ), infi_infi_eq_right],
  simp_rw [@infi_comm _ ℝₗ (_ ≤ _), infi_subtype', ← Ici_inter_Iio, ← inf_principal, ← inf_infi,
    ← infi_inf, this, infi_subtype],
  suffices : (⨅ x ∈ Ioi a, 𝓟 (Iio x)).has_basis ((<) a) Iio, from this.principal_inf _,
  refine has_basis_binfi_principal _ nonempty_Ioi,
  exact directed_on_iff_directed.2 (directed_of_inf $ λ x y hxy, Iio_subset_Iio hxy),
end

lemma nhds_basis_Ico_rat (a : ℝₗ) :
  (𝓝 a).has_countable_basis (λ r : ℚ, a < r) (λ r, Ico a r) :=
begin
  refine ⟨(nhds_basis_Ico a).to_has_basis (λ b hb, _) (λ r hr, ⟨_, hr, subset.rfl⟩),
    set.to_countable _⟩,
  rcases exists_rat_btwn hb with ⟨r, har, hrb⟩,
  exact ⟨r, har, Ico_subset_Ico_right hrb.le⟩
end

lemma nhds_basis_Ico_inv_pnat (a : ℝₗ) :
  (𝓝 a).has_basis (λ n : ℕ+, true) (λ n, Ico a (a + n⁻¹)) :=
begin
  refine (nhds_basis_Ico a).to_has_basis (λ b hb, _)
    (λ n hn, ⟨_, lt_add_of_pos_right _ (inv_pos.2 $ nat.cast_pos.2 n.pos), subset.rfl⟩),
  rcases exists_nat_one_div_lt (sub_pos.2 hb) with ⟨k, hk⟩,
  rw [one_div] at hk,
  rw [← nat.cast_add_one] at hk,
  exact ⟨k.succ_pnat, trivial, Ico_subset_Ico_right (le_sub_iff_add_le'.1 hk.le)⟩
end

lemma nhds_countable_basis_Ico_inv_pnat (a : ℝₗ) :
  (𝓝 a).has_countable_basis (λ n : ℕ+, true) (λ n, Ico a (a + n⁻¹)) :=
⟨nhds_basis_Ico_inv_pnat a, set.to_countable _⟩

lemma nhds_antitone_basis_Ico_inv_pnat (a : ℝₗ) :
  (𝓝 a).has_antitone_basis (λ n : ℕ+, Ico a (a + n⁻¹)) :=
⟨nhds_basis_Ico_inv_pnat a, monotone_const.Ico $
  antitone.const_add (λ k l hkl, inv_le_inv_of_le (nat.cast_pos.2 k.pos) (nat.mono_cast hkl)) _⟩

lemma is_open_iff {s : set ℝₗ} : is_open s ↔ ∀ x ∈ s, ∃ y > x, Ico x y ⊆ s :=
is_open_iff_mem_nhds.trans $ forall₂_congr $ λ x hx, (nhds_basis_Ico x).mem_iff

lemma is_closed_iff {s : set ℝₗ} : is_closed s ↔ ∀ x ∉ s, ∃ y > x, disjoint (Ico x y) s :=
by simp only [← is_open_compl_iff, is_open_iff, mem_compl_iff, subset_compl_iff_disjoint_right]

lemma exists_Ico_disjoint_closed {a : ℝₗ} {s : set ℝₗ} (hs : is_closed s) (ha : a ∉ s) :
  ∃ b > a, disjoint (Ico a b) s :=
is_closed_iff.1 hs a ha

@[simp] lemma map_to_real_nhds (a : ℝₗ) : map to_real (𝓝 a) = 𝓝[≥] (to_real a) :=
begin
  refine ((nhds_basis_Ico a).map _).eq_of_same_basis _,
  simpa only [to_real.image_eq_preimage] using nhds_within_Ici_basis_Ico (to_real a)
end

lemma nhds_eq_map (a : ℝₗ) : 𝓝 a = map to_real.symm (𝓝[≥] a.to_real) :=
by simp_rw [← map_to_real_nhds, map_map, (∘), to_real.symm_apply_apply, map_id']

lemma nhds_eq_comap (a : ℝₗ) : 𝓝 a = comap to_real (𝓝[≥] a.to_real) :=
by rw [← map_to_real_nhds, comap_map to_real.injective]

@[continuity] lemma continuous_to_real : continuous to_real :=
continuous_iff_continuous_at.2 $ λ x,
  by { rw [continuous_at, tendsto, map_to_real_nhds], exact inf_le_left }

instance : order_closed_topology ℝₗ :=
⟨is_closed_le_prod.preimage (continuous_to_real.prod_map continuous_to_real)⟩

instance : has_continuous_add ℝₗ :=
begin
  refine ⟨continuous_iff_continuous_at.2 _⟩,
  rintro ⟨x, y⟩,
  simp only [continuous_at, nhds_prod_eq, nhds_eq_map, nhds_eq_comap (x + y), prod_map_map_eq,
    tendsto_comap_iff, tendsto_map'_iff, (∘), ← nhds_within_prod_eq],
  exact (continuous_add.tendsto _).inf (maps_to.tendsto $ λ x hx, add_le_add hx.1 hx.2)
end

lemma is_clopen_Ici (a : ℝₗ) : is_clopen (Ici a) := ⟨is_open_Ici a, is_closed_Ici⟩

lemma is_clopen_Iio (a : ℝₗ) : is_clopen (Iio a) :=
by simpa only [compl_Ici] using (is_clopen_Ici a).compl

lemma is_clopen_Ico (a b : ℝₗ) : is_clopen (Ico a b) :=
(is_clopen_Ici a).inter (is_clopen_Iio b)

instance : totally_disconnected_space ℝₗ :=
⟨λ s hs' hs x hx y hy, le_antisymm (hs.subset_clopen (is_clopen_Ici x) ⟨x, hx, le_rfl⟩ hy)
  (hs.subset_clopen (is_clopen_Ici y) ⟨y, hy, le_rfl⟩ hx)⟩

instance : first_countable_topology ℝₗ := ⟨λ x, (nhds_basis_Ico_rat x).is_countably_generated⟩

/-- Sorgenfrey line is a completely normal Hausdorff topological space. -/
instance : t5_space ℝₗ :=
begin
  /- Let `s` and `t` be disjoint closed sets. For each `x ∈ s` we choose `X x` such that
  `set.Ico x (X x)` is disjoint with `t`. Similarly, for each `y ∈ t` we choose `Y y` such that
  `set.Ico y (Y y)` is disjoint with `s`. Then `⋃ x ∈ s, Ico x (X x)` and `⋃ y ∈ t, Ico y (Y y)` are
  disjoint open sets that include `s` and `t`. -/
  refine ⟨λ s t hd₁ hd₂, _⟩,
  choose! X hX hXd
    using λ x (hx : x ∈ s), exists_Ico_disjoint_closed is_closed_closure (disjoint_left.1 hd₂ hx),
  choose! Y hY hYd
    using λ y (hy : y ∈ t), exists_Ico_disjoint_closed is_closed_closure (disjoint_right.1 hd₁ hy),
  refine disjoint_of_disjoint_of_mem _
    (bUnion_mem_nhds_set $ λ x hx, (is_open_Ico x (X x)).mem_nhds $ left_mem_Ico.2 (hX x hx))
    (bUnion_mem_nhds_set $ λ y hy, (is_open_Ico y (Y y)).mem_nhds $ left_mem_Ico.2 (hY y hy)),
  simp only [disjoint_Union_left, disjoint_Union_right, Ico_disjoint_Ico],
  intros y hy x hx,
  cases le_total x y with hle hle,
  { calc min (X x) (Y y) ≤ X x : min_le_left _ _
    ... ≤ y : not_lt.1 (λ hyx, (hXd x hx).le_bot ⟨⟨hle, hyx⟩, subset_closure hy⟩)
    ... ≤ max x y : le_max_right _ _ },
  { calc min (X x) (Y y) ≤ Y y : min_le_right _ _
    ... ≤ x : not_lt.1 $ λ hxy, (hYd y hy).le_bot ⟨⟨hle, hxy⟩, subset_closure hx⟩
    ... ≤ max x y : le_max_left _ _ }
end

lemma dense_range_coe_rat : dense_range (coe : ℚ → ℝₗ) :=
begin
  refine dense_iff_inter_open.2 _,
  rintro U Uo ⟨x, hx⟩,
  rcases is_open_iff.1 Uo _ hx with ⟨y, hxy, hU⟩,
  rcases exists_rat_btwn hxy with ⟨z, hxz, hzy⟩,
  exact ⟨z, hU ⟨hxz.le, hzy⟩, mem_range_self _⟩
end

instance : separable_space ℝₗ := ⟨⟨_, countable_range _, dense_range_coe_rat⟩⟩

lemma is_closed_antidiagonal (c : ℝₗ) : is_closed {x : ℝₗ × ℝₗ | x.1 + x.2 = c} :=
is_closed_singleton.preimage continuous_add

lemma is_clopen_Ici_prod (x : ℝₗ × ℝₗ) : is_clopen (Ici x) :=
(Ici_prod_eq x).symm ▸ (is_clopen_Ici _).prod (is_clopen_Ici _)

/-- Any subset of an antidiagonal `{(x, y) : ℝₗ × ℝₗ| x + y = c}` is a closed set. -/
lemma is_closed_of_subset_antidiagonal {s : set (ℝₗ × ℝₗ)} {c : ℝₗ}
  (hs : ∀ x : ℝₗ × ℝₗ, x ∈ s → x.1 + x.2 = c) : is_closed s :=
begin
  rw [← closure_subset_iff_is_closed],
  rintro ⟨x, y⟩ H,
  obtain rfl : x + y = c,
  { change (x, y) ∈ {p : ℝₗ × ℝₗ | p.1 + p.2 = c},
    exact closure_minimal (hs : s ⊆ {x | x.1 + x.2 = c}) (is_closed_antidiagonal c) H },
  rcases mem_closure_iff.1 H (Ici (x, y)) (is_clopen_Ici_prod _).1 le_rfl
    with ⟨⟨x', y'⟩, ⟨hx : x ≤ x', hy : y ≤ y'⟩, H⟩,
  convert H,
  { refine hx.antisymm _,
    rwa [← add_le_add_iff_right, hs _ H, add_le_add_iff_left] },
  { refine hy.antisymm _,
    rwa [← add_le_add_iff_left, hs _ H, add_le_add_iff_right] }
end

lemma nhds_prod_antitone_basis_inv_pnat (x y : ℝₗ) :
  (𝓝 (x, y)).has_antitone_basis (λ n : ℕ+, Ico x (x + n⁻¹) ×ˢ Ico y (y + n⁻¹)) :=
begin
  rw [nhds_prod_eq],
  exact (nhds_antitone_basis_Ico_inv_pnat x).prod (nhds_antitone_basis_Ico_inv_pnat y)
end

/-- The product of the Sorgenfrey line and itself is not a normal topological space. -/
lemma not_normal_space_prod : ¬normal_space (ℝₗ × ℝₗ) :=
begin
  have h₀ : ∀ {n : ℕ+}, (0 : ℝ) < n⁻¹, from λ n, inv_pos.2 (nat.cast_pos.2 n.pos),
  have h₀' : ∀ {n : ℕ+} {x : ℝ}, x < x + n⁻¹, from λ n x, lt_add_of_pos_right _ h₀,
  introI,
  /- Let `S` be the set of points `(x, y)` on the line `x + y = 0` such that `x` is rational.
  Let `T` be the set of points `(x, y)` on the line `x + y = 0` such that `x` is irrational.
  These sets are closed, see `sorgenfrey_line.is_closed_of_subset_antidiagonal`, and disjoint. -/
  set S := {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ ∃ r : ℚ, ↑r = x.1},
  set T := {x : ℝₗ × ℝₗ | x.1 + x.2 = 0 ∧ irrational x.1.to_real},
  have hSc : is_closed S, from is_closed_of_subset_antidiagonal (λ x hx, hx.1),
  have hTc : is_closed T, from is_closed_of_subset_antidiagonal (λ x hx, hx.1),
  have hd : disjoint S T,
  { rw disjoint_iff_inf_le,
    rintro ⟨x, y⟩ ⟨⟨-, r, rfl : _ = x⟩, -, hr⟩,
    exact r.not_irrational hr },
  /- Consider disjoint open sets `U ⊇ S` and `V ⊇ T`. -/
  rcases normal_separation hSc hTc hd with ⟨U, V, Uo, Vo, SU, TV, UV⟩,
  /- For each point `(x, -x) ∈ T`, choose a neighborhood
  `Ico x (x + k⁻¹) ×ˢ Ico (-x) (-x + k⁻¹) ⊆ V`. -/
  have : ∀ x : ℝₗ, irrational x.to_real →
    ∃ k : ℕ+, Ico x (x + k⁻¹) ×ˢ Ico (-x) (-x + k⁻¹) ⊆ V,
  { intros x hx,
    have hV : V ∈ 𝓝 (x, -x), from Vo.mem_nhds (@TV (x, -x) ⟨add_neg_self x, hx⟩),
    exact (nhds_prod_antitone_basis_inv_pnat _ _).mem_iff.1 hV },
  choose! k hkV,
  /- Since the set of irrational numbers is a dense Gδ set in the usual topology of `ℝ`, there
  exists `N > 0` such that the set `C N = {x : ℝ | irrational x ∧ k x = N}` is dense in a nonempty
  interval. In other words, the closure of this set has a nonempty interior. -/
  set C : ℕ+ → set ℝ := λ n, closure {x | irrational x ∧ k (to_real.symm x) = n},
  have H : {x : ℝ | irrational x} ⊆ ⋃ n, C n,
    from λ x hx, mem_Union.2 ⟨_, subset_closure ⟨hx, rfl⟩⟩,
  have Hd : dense (⋃ n, interior (C n)) :=
    is_Gδ_irrational.dense_Union_interior_of_closed dense_irrational (λ _, is_closed_closure) H,
  obtain ⟨N, hN⟩ : ∃ n : ℕ+, (interior $ C n).nonempty, from nonempty_Union.mp Hd.nonempty,
  /- Choose a rational number `r` in the interior of the closure of `C N`, then choose `n ≥ N > 0`
  such that `Ico r (r + n⁻¹) × Ico (-r) (-r + n⁻¹) ⊆ U`. -/
  rcases rat.dense_range_cast.exists_mem_open is_open_interior hN with ⟨r, hr⟩,
  have hrU : ((r, -r) : ℝₗ × ℝₗ) ∈ U, from @SU (r, -r) ⟨add_neg_self _, r, rfl⟩,
  obtain ⟨n, hnN, hn⟩ : ∃ n  (hnN : N ≤ n), Ico (r : ℝₗ) (r + n⁻¹) ×ˢ Ico (-r : ℝₗ) (-r + n⁻¹) ⊆ U,
    from ((nhds_prod_antitone_basis_inv_pnat _ _).has_basis_ge N).mem_iff.1 (Uo.mem_nhds hrU),
  /- Finally, choose `x ∈ Ioo (r : ℝ) (r + n⁻¹) ∩ C N`. Then `(x, -r)` belongs both to `U` and `V`,
  so they are not disjoint. This contradiction completes the proof. -/
  obtain ⟨x, hxn, hx_irr, rfl⟩ :
    ∃ x : ℝ, x ∈ Ioo (r : ℝ) (r + n⁻¹) ∧ irrational x ∧ k (to_real.symm x) = N,
  { have : (r : ℝ) ∈ closure (Ioo (r : ℝ) (r + n⁻¹)),
    { rw [closure_Ioo h₀'.ne, left_mem_Icc], exact h₀'.le },
    rcases mem_closure_iff_nhds.1 this _ (mem_interior_iff_mem_nhds.1 hr) with ⟨x', hx', hx'ε⟩,
    exact mem_closure_iff.1 hx' _ is_open_Ioo hx'ε },
  refine UV.le_bot (_ : (to_real.symm x, -↑r) ∈ _),
  refine ⟨hn ⟨_, _⟩, hkV (to_real.symm x) hx_irr ⟨_, _⟩⟩,
  { exact Ioo_subset_Ico_self hxn },
  { exact left_mem_Ico.2 h₀' },
  { exact left_mem_Ico.2 h₀' },
  { refine (nhds_antitone_basis_Ico_inv_pnat (-x)).2 hnN ⟨neg_le_neg hxn.1.le, _⟩,
    simp only [add_neg_lt_iff_le_add', lt_neg_add_iff_add_lt],
    exact hxn.2 }
end

/-- Topology on the Sorgenfrey line is not metrizable. -/
lemma not_metrizable_space : ¬metrizable_space ℝₗ :=
begin
  introI,
  letI := metrizable_space_metric ℝₗ,
  exact not_normal_space_prod infer_instance
end

/-- Topology on the Sorgenfrey line is not second countable. -/
lemma not_second_countable_topology : ¬second_countable_topology ℝₗ :=
by { introI, exact not_metrizable_space (metrizable_space_of_t3_second_countable _) }

end sorgenfrey_line

end counterexample
