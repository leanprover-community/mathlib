/-
Copyright (c) 2019 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/

import topology.metric_space.lipschitz analysis.specific_limits data.setoid

/-!
# Contracting maps

A Lipschitz continuous self-map with Lipschitz constant `K < 1` is called a *contracting map*.
In this file we prove the Banach fixed point theorem, some explicit estimates on the rate
of convergence, and some properties of the map sending a contracting map to its fixed point.

## Main definitions

* `contracting_with K f` : a Lipschitz continuous self-map with `K < 1`;
* `efixed_point` : given a contracting map `f` on a complete emetric space and a point `x`
  such that `edist x (f x) < ∞`, `efixed_point f hf x hx` is the unique fixed point of `f`
  in `emetric.ball x ∞`;
* `fixed_point` : the unique fixed point of a contracting map on a complete nonempty metric space.

-/

open_locale nnreal topological_space classical
open filter

variables {α : Type*}

/-- If the iterates `f^[n] x₀` converge to `x` and `f` is continuous at `x`,
then `x` is a fixed point for `f`. -/
lemma fixed_point_of_tendsto_iterate [topological_space α] [t2_space α] {f : α → α} {x : α}
  (hf : continuous_at f x) (hx : ∃ x₀ : α, tendsto (λ n, f^[n] x₀) at_top (𝓝 x)) :
  f x = x :=
begin
  rcases hx with ⟨x₀, hx⟩,
  refine tendsto_nhds_unique at_top_ne_bot _ hx,
  rw [← tendsto_add_at_top_iff_nat 1, funext (assume n, nat.iterate_succ' f n x₀)],
  exact tendsto.comp hf hx
end

/-- A map is said to be `contracting_with K`, if `K < 1` and `f` is `lipschitz_with K`. -/
def contracting_with [emetric_space α] (K : ℝ≥0) (f : α → α) :=
(K < 1) ∧ lipschitz_with K f

namespace contracting_with

variables [emetric_space α] [cs : complete_space α] {K : ℝ≥0} {f : α → α}
  (hf : contracting_with K f)
include hf

open emetric set

lemma to_lipschitz_with : lipschitz_with K f := hf.2

lemma one_sub_K_pos' : (0:ennreal) < 1 - K := by simp [hf.1]

lemma one_sub_K_ne_zero : (1:ennreal) - K ≠ 0 := ne_of_gt hf.one_sub_K_pos'

lemma one_sub_K_ne_top : (1:ennreal) - K ≠ ⊤ :=
by { norm_cast, exact ennreal.coe_ne_top }

lemma edist_inequality (hf : contracting_with K f) {x y} (h : edist x y < ⊤) :
  edist x y ≤ (edist x (f x) + edist y (f y)) / (1 - K) :=
suffices edist x y ≤ edist x (f x) + edist y (f y) + K * edist x y,
  by rwa [ennreal.le_div_iff_mul_le (or.inl hf.one_sub_K_ne_zero) (or.inl hf.one_sub_K_ne_top),
    mul_comm, ennreal.sub_mul (λ _ _, ne_of_lt h), one_mul, ennreal.sub_le_iff_le_add],
calc edist x y ≤ edist x (f x) + edist (f x) (f y) + edist (f y) y : edist_triangle4 _ _ _ _
  ... = edist x (f x) + edist y (f y) + edist (f x) (f y) : by rw [edist_comm y, add_right_comm]
  ... ≤ edist x (f x) + edist y (f y) + K * edist x y : add_le_add' (le_refl _) (hf.2 _ _)

lemma edist_le_of_fixed_point {x y} (h : edist x y < ⊤) (hy : f y = y) :
  edist x y ≤ (edist x (f x)) / (1 - K) :=
by simpa only [hy, edist_self, add_zero] using hf.edist_inequality h

lemma eq_or_edist_eq_top_of_fixed_points {x y} (hx : f x = x) (hy : f y = y) :
  x = y ∨ edist x y = ⊤ :=
begin
  cases eq_or_lt_of_le (le_top : edist x y ≤ ⊤), from or.inr h,
  refine or.inl (edist_le_zero.1 _),
  simpa only [hx, edist_self, add_zero, ennreal.zero_div]
    using hf.edist_le_of_fixed_point h hy
end

/-- Banach fixed-point theorem, contraction mapping theorem, `emetric_space` version.
This version assumes that `f` is contracting in the whole space and sends a point `x`
of a forward-invariant complete set `s` to the same ball of radius infinity.

See also functions `efixed_point'`, `efixed_point`, `fixed_point`, and lemmas about
these functions.  -/
theorem exists_fixed_point {x : α} (hx : edist x (f x) < ⊤) {s : set α} (hxs : x ∈ s)
  (hsc : is_complete s) (hsf : maps_to f s s) :
  ∃ y ∈ s, f y = y ∧ tendsto (λ n, f^[n] x) at_top (𝓝 y) ∧
    ∀ n:ℕ, edist (f^[n] x) y ≤ (edist x (f x)) * K^n / (1 - K) :=
have cauchy_seq (λ n, f^[n] x),
from cauchy_seq_of_edist_le_geometric K (edist x (f x)) (ennreal.coe_lt_one_iff.2 hf.1)
  (ne_of_lt hx) (hf.to_lipschitz_with.edist_iterate_succ_le_geometric x),
let ⟨y, hys, hy⟩ :=
  cauchy_seq_tendsto_of_is_complete hsc (λ n:ℕ, (hsf.iterate n hxs : _ ∈ s)) this in
⟨y, hys, fixed_point_of_tendsto_iterate hf.2.continuous.continuous_at ⟨x, hy⟩, hy,
  edist_le_of_edist_le_geometric_of_tendsto K (edist x (f x))
    (hf.to_lipschitz_with.edist_iterate_succ_le_geometric x) hy⟩

variable (f) -- avoid `efixed_point' _` in pretty printer

/-- Let `x` be a point such that `edist x (f x) < ∞`, and `s ∋ x` be a forward-invariant complete
set. Then `efixed_point'` is the unique fixed point of `f` in `emetric.ball x ∞`. -/
noncomputable def efixed_point' (x : α) (hx : edist x (f x) < ⊤) (s : set α) (hxs : x ∈ s)
  (hsc : is_complete s) (hsf : maps_to f s s) : α :=
classical.some (hf.exists_fixed_point hx hxs hsc hsf)

/-- Let `x` be a point of a complete emetric space. Suppose that `f` is a contracting map,
and `edist x (f x) < ∞`. Then `efixed_point` is the unique fixed point of `f`
in `emetric.ball x ∞`. -/
noncomputable def efixed_point [complete_space α] (x : α) (hx : edist x (f x) < ⊤) : α :=
efixed_point' f hf x hx univ (mem_univ x) complete_univ (maps_to_univ _ _)

variable {f}

lemma efixed_point_mem' {x : α} (hx : edist x (f x) < ⊤) {s : set α} (hxs : x ∈ s)
  (hsc : is_complete s) (hsf : maps_to f s s) :
  efixed_point' f hf x hx s hxs hsc hsf ∈ s :=
(classical.some_spec (hf.exists_fixed_point hx hxs hsc hsf)).fst

lemma efixed_point_is_fixed' {x : α} (hx : edist x (f x) < ⊤) {s : set α} (hxs : x ∈ s)
  (hsc : is_complete s) (hsf : maps_to f s s) :
  f (efixed_point' f hf x hx s hxs hsc hsf) = efixed_point' f hf x hx s hxs hsc hsf :=
(classical.some_spec (hf.exists_fixed_point hx hxs hsc hsf)).snd.1

lemma tendsto_iterate_efixed_point' {x : α} (hx : edist x (f x) < ⊤)
  {s : set α} (hxs : x ∈ s) (hsc : is_complete s) (hsf : maps_to f s s) :
  tendsto (λn, f^[n] x) at_top (𝓝 $ efixed_point' f hf x hx s hxs hsc hsf) :=
(classical.some_spec (hf.exists_fixed_point hx hxs hsc hsf)).snd.2.1

lemma apriori_edist_iterate_efixed_point_le' {x : α} (hx : edist x (f x) < ⊤)
  {s : set α} (hxs : x ∈ s) (hsc : is_complete s) (hsf : maps_to f s s) (n : ℕ) :
  edist (f^[n] x) (efixed_point' f hf x hx s hxs hsc hsf) ≤ (edist x (f x)) * K^n / (1 - K) :=
(classical.some_spec (hf.exists_fixed_point hx hxs hsc hsf)).snd.2.2 n

lemma edist_efixed_point_le' {x : α} (hx : edist x (f x) < ⊤)
  {s : set α} (hxs : x ∈ s) (hsc : is_complete s) (hsf : maps_to f s s) :
  edist x (efixed_point' f hf x hx s hxs hsc hsf) ≤ (edist x (f x)) / (1 - K) :=
by simpa only [mul_one, nat.iterate, pow_zero]
  using apriori_edist_iterate_efixed_point_le' hf hx hxs hsc hsf 0

lemma edist_efixed_point_lt_top' {x : α} (hx : edist x (f x) < ⊤) {s : set α} (hxs : x ∈ s)
  (hsc : is_complete s) (hsf : maps_to f s s) :
  edist x (efixed_point' f hf x hx s hxs hsc hsf) < ⊤ :=
lt_of_le_of_lt (hf.edist_efixed_point_le' hx hxs hsc hsf) (ennreal.mul_lt_top hx $
  ennreal.lt_top_iff_ne_top.2 $ ennreal.inv_ne_top.2 hf.one_sub_K_ne_zero)

lemma efixed_point_eq_of_edist_lt_top' {x : α} (hx : edist x (f x) < ⊤)
  {s : set α} (hxs : x ∈ s) (hsc : is_complete s) (hsf : maps_to f s s)
  {y : α} (hy : edist y (f y) < ⊤)
  {t : set α} (hyt : y ∈ t) (htc : is_complete t) (htf : maps_to f t t)
  (h : edist x y < ⊤) :
  efixed_point' f hf x hx s hxs hsc hsf = efixed_point' f hf y hy t hyt htc htf :=
begin
  refine (hf.eq_or_edist_eq_top_of_fixed_points _ _).elim id (λ h', false.elim (ne_of_lt _ h'));
    try { apply efixed_point_is_fixed' },
  change edist_lt_top_setoid.rel _ _,
  transitivity x, by { symmetry, exact hf.edist_efixed_point_lt_top' hx hxs hsc hsf },
  transitivity y,
  exacts [h, hf.edist_efixed_point_lt_top' hy hyt htc htf]
end

include cs

lemma efixed_point_is_fixed {x : α} (hx : edist x (f x) < ⊤) :
  f (efixed_point f hf x hx) = efixed_point f hf x hx :=
by apply efixed_point_is_fixed'

lemma tendsto_iterate_efixed_point {x : α} (hx : edist x (f x) < ⊤) :
  tendsto (λn, f^[n] x) at_top (𝓝 $ efixed_point f hf x hx) :=
by apply tendsto_iterate_efixed_point'

lemma apriori_edist_iterate_efixed_point_le {x : α} (hx : edist x (f x) < ⊤) (n : ℕ) :
  edist (f^[n] x) (efixed_point f hf x hx) ≤ (edist x (f x)) * K^n / (1 - K) :=
by apply apriori_edist_iterate_efixed_point_le'

lemma edist_efixed_point_le {x : α} (hx : edist x (f x) < ⊤) :
  edist x (efixed_point f hf x hx) ≤ (edist x (f x)) / (1 - K) :=
by apply edist_efixed_point_le'

lemma edist_efixed_point_lt_top {x : α} (hx : edist x (f x) < ⊤) :
  edist x (efixed_point f hf x hx) < ⊤ :=
by apply edist_efixed_point_lt_top'

lemma efixed_point_eq_of_edist_lt_top {x : α} (hx : edist x (f x) < ⊤)
  {y : α} (hy : edist y (f y) < ⊤) (h : edist x y < ⊤) :
  efixed_point f hf x hx = efixed_point f hf y hy :=
by apply efixed_point_eq_of_edist_lt_top'; assumption

end contracting_with

namespace contracting_with

variables [metric_space α] {K : ℝ≥0} {f : α → α} (hf : contracting_with K f)
include hf

lemma one_sub_K_pos (hf : contracting_with K f) : (0:ℝ) < 1 - K := sub_pos.2 hf.1

lemma dist_le_mul (x y : α) : dist (f x) (f y) ≤ K * dist x y :=
hf.to_lipschitz_with.dist_le x y

lemma dist_inequality (x y) : dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
suffices dist x y ≤ dist x (f x) + dist y (f y) + K * dist x y,
  by rwa [le_div_iff hf.one_sub_K_pos, mul_comm, sub_mul, one_mul, sub_le_iff_le_add],
calc dist x y ≤ dist x (f x) + dist y (f y) + dist (f x) (f y) : dist_triangle4_right _ _ _ _
          ... ≤ dist x (f x) + dist y (f y) + K * dist x y :
  add_le_add_left (hf.dist_le_mul _ _) _

lemma dist_le_of_fixed_point (x) {y} (hy : f y = y) :
  dist x y ≤ (dist x (f x)) / (1 - K) :=
by simpa only [hy, dist_self, add_zero] using hf.dist_inequality x y

theorem fixed_point_unique' {x y} (hx : f x = x) (hy : f y = y) : x = y :=
(hf.eq_or_edist_eq_top_of_fixed_points hx hy).elim id (λ h, (edist_ne_top _ _ h).elim)

/-- Let `f` be a contracting map with constant `K`; let `g` be another map uniformly
`C`-close to `f`. If `x` and `y` are their fixed points, then `dist x y ≤ C / (1 - K)`. -/
lemma dist_fixed_point_fixed_point_of_dist_le' (g : α → α)
  {x y} (hx : f x = x) (hy : g y = y) {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) :
  dist x y ≤ C / (1 - K) :=
calc dist x y = dist y x : dist_comm x y
          ... ≤ (dist y (f y)) / (1 - K) : hf.dist_le_of_fixed_point y hx
          ... = (dist (f y) (g y)) / (1 - K) : by rw [hy, dist_comm]
          ... ≤ C / (1 - K) : (div_le_div_right hf.one_sub_K_pos).2 (hfg y)

noncomputable theory

variables [nonempty α] [complete_space α]

variable (f)
/-- The unique fixed point of a contracting map in a nonempty complete metric space. -/
def fixed_point : α :=
efixed_point f hf _ (edist_lt_top (classical.choice ‹nonempty α›) _)
variable {f}

/-- The point provided by `contracting_with.fixed_point` is actually a fixed point. -/
lemma fixed_point_is_fixed : f (fixed_point f hf) = fixed_point f hf :=
hf.efixed_point_is_fixed _

lemma fixed_point_unique {x} (hx : f x = x) : x = fixed_point f hf :=
hf.fixed_point_unique' hx hf.fixed_point_is_fixed

lemma dist_fixed_point_le (x) : dist x (fixed_point f hf) ≤ (dist x (f x)) / (1 - K) :=
hf.dist_le_of_fixed_point x hf.fixed_point_is_fixed

/-- Aposteriori estimates on the convergence of iterates to the fixed point. -/
lemma aposteriori_dist_iterate_fixed_point_le (x n) :
  dist (f^[n] x) (fixed_point f hf) ≤ (dist (f^[n] x) (f^[n+1] x)) / (1 - K) :=
by { rw [nat.iterate_succ'], apply hf.dist_fixed_point_le }

lemma apriori_dist_iterate_fixed_point_le (x n) :
  dist (f^[n] x) (fixed_point f hf) ≤ (dist x (f x)) * K^n / (1 - K) :=
le_trans (hf.aposteriori_dist_iterate_fixed_point_le x n) $
  (div_le_div_right hf.one_sub_K_pos).2 $
    hf.to_lipschitz_with.dist_iterate_succ_le_geometric x n

lemma tendsto_iterate_fixed_point (x) :
  tendsto (λn, f^[n] x) at_top (𝓝 $ fixed_point f hf) :=
begin
  convert tendsto_iterate_efixed_point hf (edist_lt_top x _),
  refine (fixed_point_unique _ _).symm,
  apply efixed_point_is_fixed
end

lemma fixed_point_lipschitz_in_map {g : α → α} (hg : contracting_with K g)
  {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) :
  dist (fixed_point f hf) (fixed_point g hg) ≤ C / (1 - K) :=
hf.dist_fixed_point_fixed_point_of_dist_le' g hf.fixed_point_is_fixed hg.fixed_point_is_fixed hfg

end contracting_with
