/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Continuous linear functions -- functions between normed vector spaces which are bounded and linear.
-/
import algebra.field
import tactic.norm_num
import analysis.normed_space.basic
import analysis.asymptotics

@[simp] lemma mul_inv_eq' {α} [discrete_field α] (a b : α) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
classical.by_cases (assume : a = 0, by simp [this]) $ assume ha,
classical.by_cases (assume : b = 0, by simp [this]) $ assume hb,
mul_inv_eq hb ha

noncomputable theory
local attribute [instance] classical.prop_decidable

local notation f ` →_{`:50 a `} `:0 b := filter.tendsto f (nhds a) (nhds b)

open filter (tendsto)
open metric

variables {k : Type*} [normed_field k]
variables {E : Type*} [normed_space k E]
variables {F : Type*} [normed_space k F]
variables {G : Type*} [normed_space k G]

structure is_bounded_linear_map (k : Type*)
  [normed_field k] {E : Type*} [normed_space k E] {F : Type*} [normed_space k F] (L : E → F)
  extends is_linear_map k L : Prop :=
(bound : ∃ M, M > 0 ∧ ∀ x : E, ∥ L x ∥ ≤ M * ∥ x ∥)

include k

lemma is_linear_map.with_bound
  {L : E → F} (hf : is_linear_map k L) (M : ℝ) (h : ∀ x : E, ∥ L x ∥ ≤ M * ∥ x ∥) :
  is_bounded_linear_map k L :=
⟨ hf, classical.by_cases
  (assume : M ≤ 0, ⟨1, zero_lt_one, assume x,
    le_trans (h x) $ mul_le_mul_of_nonneg_right (le_trans this zero_le_one) (norm_nonneg x)⟩)
  (assume : ¬ M ≤ 0, ⟨M, lt_of_not_ge this, h⟩)⟩

namespace is_bounded_linear_map

def to_linear_map (f : E → F) (h : is_bounded_linear_map k f) : E →ₗ[k] F :=
(is_linear_map.mk' _ h.to_is_linear_map)

lemma zero : is_bounded_linear_map k (λ (x:E), (0:F)) :=
(0 : E →ₗ F).is_linear.with_bound 0 $ by simp [le_refl]

lemma id : is_bounded_linear_map k (λ (x:E), x) :=
linear_map.id.is_linear.with_bound 1 $ by simp [le_refl]

set_option class.instance_max_depth 43
lemma smul {f : E → F} (c : k) : is_bounded_linear_map k f → is_bounded_linear_map k (λ e, c • f e)
| ⟨hf, ⟨M, hM, h⟩⟩ := (c • hf.mk' f).is_linear.with_bound (∥c∥ * M) $ assume x,
  calc ∥c • f x∥ = ∥c∥ * ∥f x∥ : norm_smul c (f x)
    ... ≤ ∥c∥ * (M * ∥x∥) : mul_le_mul_of_nonneg_left (h x) (norm_nonneg c)
    ... = (∥c∥ * M) * ∥x∥ : (mul_assoc _ _ _).symm

lemma neg {f : E → F} (hf : is_bounded_linear_map k f) : is_bounded_linear_map k (λ e, -f e) :=
begin
  rw show (λ e, -f e) = (λ e, (-1 : k) • f e), { funext, simp },
  exact smul (-1) hf
end

lemma add {f : E → F} {g : E → F} :
  is_bounded_linear_map k f → is_bounded_linear_map k g → is_bounded_linear_map k (λ e, f e + g e)
| ⟨hlf, Mf, hMf, hf⟩  ⟨hlg, Mg, hMg, hg⟩ := (hlf.mk' _ + hlg.mk' _).is_linear.with_bound (Mf + Mg) $ assume x,
  calc ∥f x + g x∥ ≤ ∥f x∥ + ∥g x∥ : norm_triangle _ _
    ... ≤ Mf * ∥x∥ + Mg * ∥x∥ : add_le_add (hf x) (hg x)
    ... ≤ (Mf + Mg) * ∥x∥ : by rw add_mul

lemma sub {f : E → F} {g : E → F} (hf : is_bounded_linear_map k f) (hg : is_bounded_linear_map k g) :
  is_bounded_linear_map k (λ e, f e - g e) := add hf (neg hg)

lemma comp {f : E → F} {g : F → G} :
  is_bounded_linear_map k g → is_bounded_linear_map k f → is_bounded_linear_map k (g ∘ f)
| ⟨hlg, Mg, hMg, hg⟩ ⟨hlf, Mf, hMf, hf⟩ := ((hlg.mk' _).comp (hlf.mk' _)).is_linear.with_bound (Mg * Mf) $ assume x,
  calc ∥g (f x)∥ ≤ Mg * ∥f x∥ : hg _
    ... ≤ Mg * (Mf * ∥x∥) : mul_le_mul_of_nonneg_left (hf _) (le_of_lt hMg)
    ... = Mg * Mf * ∥x∥ : (mul_assoc _ _ _).symm

lemma tendsto {L : E → F} (x : E) : is_bounded_linear_map k L → L →_{x} (L x)
| ⟨hL, M, hM, h_ineq⟩ := tendsto_iff_norm_tendsto_zero.2 $
  squeeze_zero (assume e, norm_nonneg _)
    (assume e, calc ∥L e - L x∥ = ∥hL.mk' L (e - x)∥ : by rw (hL.mk' _).map_sub e x; refl
      ... ≤ M*∥e-x∥ : h_ineq (e-x))
    (suffices (λ (e : E), M * ∥e - x∥) →_{x} (M * 0), by simpa,
      tendsto_mul tendsto_const_nhds (lim_norm _))

lemma continuous {L : E → F} (hL : is_bounded_linear_map k L) : continuous L :=
continuous_iff_continuous_at.2 $ assume x, hL.tendsto x

lemma lim_zero_bounded_linear_map {L : E → F} (H : is_bounded_linear_map k L) : (L →_{0} 0) :=
(H.1.mk' _).map_zero ▸ continuous_iff_continuous_at.1 H.continuous 0

section
open asymptotics filter

theorem is_O_id {L : E → F} (h : is_bounded_linear_map k L) (l : filter E) :
  is_O L (λ x, x) l :=
let ⟨M, Mpos, hM⟩ := h.bound in
⟨M, Mpos, mem_sets_of_superset univ_mem_sets (λ x _, hM x)⟩

theorem is_O_comp {L : F → G} (h : is_bounded_linear_map k L)
  {f : E → F} (l : filter E) : is_O (λ x', L (f x')) f l :=
((h.is_O_id ⊤).comp _).mono (map_le_iff_le_comap.mp lattice.le_top)

theorem is_O_sub {L : E → F} (h : is_bounded_linear_map k L) (l : filter E) (x : E) :
  is_O (λ x', L (x' - x)) (λ x', x' - x) l :=
is_O_comp h l

end

end is_bounded_linear_map

set_option class.instance_max_depth 60

/-- A continuous linear map between normed spaces is bounded when the field is nondiscrete.
The continuity ensures boundedness on a ball of some radius δ. The nondiscreteness is then
used to rescale any element into an element of norm in [δ/C, δ], whose image has a controlled norm.
The norm control for the original element follows by rescaling. -/
theorem is_linear_map.bounded_of_continuous_at {k : Type*} [nondiscrete_normed_field k]
  {E : Type*} [normed_space k E] {F : Type*} [normed_space k F] {L : E → F} {x₀ : E}
  (lin : is_linear_map k L) (cont : continuous_at L x₀) : is_bounded_linear_map k L :=
begin
  rcases tendsto_nhds_nhds.1 cont 1 zero_lt_one with ⟨ε, ε_pos, hε⟩,
  let δ := ε/2,
  have δ_pos : δ > 0 := half_pos ε_pos,
  have H : ∀{a}, ∥a∥ ≤ δ → ∥L a∥ ≤ 1,
  { assume a ha,
    have : dist (L (x₀+a)) (L x₀) ≤ 1,
    { apply le_of_lt (hε _),
      have : dist x₀ (x₀ + a) = ∥a∥, by { rw dist_eq_norm, simp },
      rw [dist_comm, this],
      exact lt_of_le_of_lt ha (half_lt_self ε_pos) },
    simpa [dist_eq_norm, lin.add] using this },
  rcases exists_one_lt_norm k with ⟨c, hc⟩,
  refine lin.with_bound (δ⁻¹ * ∥c∥) (λx, _),
  by_cases h : x = 0,
  { simp only [h, lin.map_zero, norm_zero, mul_zero] },
  { rcases rescale_to_shell hc δ_pos h with ⟨d, hd, dxle, ledx, dinv⟩,
    calc ∥L x∥
      = ∥L ((d⁻¹ * d) • x)∥ : by rwa [inv_mul_cancel, one_smul]
      ... = ∥d∥⁻¹ * ∥L (d • x)∥ :
        by rw [mul_smul, lin.smul, norm_smul, norm_inv]
      ... ≤ ∥d∥⁻¹ * 1 :
        mul_le_mul_of_nonneg_left (H dxle) (by { rw ← norm_inv, exact norm_nonneg _ })
      ... ≤ δ⁻¹ * ∥c∥ * ∥x∥ : by { rw mul_one, exact dinv } }
end
