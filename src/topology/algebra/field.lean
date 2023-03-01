/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import topology.algebra.ring.basic
import topology.algebra.group_with_zero
import topology.local_extr
import field_theory.subfield

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/


namespace topological_ring
open topological_space function
variables (R : Type*) [semiring R]

variables  [topological_space R]

/-- The induced topology on units of a topological semiring.
This is not a global instance since other topologies could be relevant. Instead there is a class
`induced_units` asserting that something equivalent to this construction holds. -/
def topological_space_units : topological_space Rˣ := induced (coe : Rˣ → R) ‹_›

/-- Asserts the topology on units is the induced topology.

 Note: this is not always the correct topology.
 Another good candidate is the subspace topology of $R \times R$,
 with the units embedded via $u \mapsto (u, u^{-1})$.
 These topologies are not (propositionally) equal in general. -/
class induced_units [t : topological_space $ Rˣ] : Prop :=
(top_eq : t = induced (coe : Rˣ → R) ‹_›)

variables [topological_space $ Rˣ]

lemma units_topology_eq [induced_units R] :
  ‹topological_space Rˣ› = induced (coe : Rˣ → R) ‹_› :=
induced_units.top_eq

lemma induced_units.continuous_coe [induced_units R] : continuous (coe : Rˣ → R) :=
(units_topology_eq R).symm ▸ continuous_induced_dom

lemma units_embedding [induced_units R] :
  embedding (coe : Rˣ → R) :=
{ induced := units_topology_eq R,
  inj := λ x y h, units.ext h }

instance top_monoid_units [topological_semiring R] [induced_units R] :
  has_continuous_mul Rˣ :=
⟨begin
  let mulR := (λ (p : R × R), p.1*p.2),
  let mulRx := (λ (p : Rˣ × Rˣ), p.1*p.2),
  have key : coe ∘ mulRx = mulR ∘ (λ p, (p.1.val, p.2.val)), from rfl,
  rw [continuous_iff_le_induced, units_topology_eq R, prod_induced_induced,
      induced_compose, key, ← induced_compose],
  apply induced_mono,
  rw ← continuous_iff_le_induced,
  exact continuous_mul,
end⟩
end topological_ring

variables {K : Type*} [division_ring K] [topological_space K]

/-- Left-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_left₀ [has_continuous_mul K] {a : K} (ha : a ≠ 0) :
  filter.tendsto (λ x : K, a * x) (filter.cocompact K) (filter.cocompact K) :=
filter.tendsto_cocompact_mul_left (inv_mul_cancel ha)

/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_right₀ [has_continuous_mul K] {a : K} (ha : a ≠ 0) :
  filter.tendsto (λ x : K, x * a) (filter.cocompact K) (filter.cocompact K) :=
filter.tendsto_cocompact_mul_right (mul_inv_cancel ha)

variables (K)

/-- A topological division ring is a division ring with a topology where all operations are
    continuous, including inversion. -/
class topological_division_ring extends topological_ring K, has_continuous_inv₀ K : Prop

namespace topological_division_ring
open filter set
/-!
In this section, we show that units of a topological division ring endowed with the
induced topology form a topological group. These are not global instances because
one could want another topology on units. To turn on this feature, use:

```lean
local attribute [instance]
topological_semiring.topological_space_units topological_division_ring.units_top_group
```
-/

local attribute [instance] topological_ring.topological_space_units

@[priority 100] instance induced_units : topological_ring.induced_units K := ⟨rfl⟩

variables [topological_division_ring K]

lemma units_top_group : topological_group Kˣ :=
{ continuous_inv := begin
    rw continuous_iff_continuous_at,
    intros x,
    rw [continuous_at, nhds_induced, nhds_induced, tendsto_iff_comap,
      ←function.semiconj.filter_comap units.coe_inv _],
    apply comap_mono,
    rw [← tendsto_iff_comap, units.coe_inv],
    exact continuous_at_inv₀ x.ne_zero
  end,
  ..topological_ring.top_monoid_units K}

local attribute [instance] units_top_group

lemma continuous_units_inv : continuous (λ x : Kˣ, (↑(x⁻¹) : K)) :=
(topological_ring.induced_units.continuous_coe K).comp continuous_inv

end topological_division_ring

section subfield

variables {α : Type*} [field α] [topological_space α] [topological_division_ring α]

/-- The (topological-space) closure of a subfield of a topological field is
itself a subfield. -/
def subfield.topological_closure (K : subfield α) : subfield α :=
{ carrier := closure (K : set α),
  inv_mem' :=
  begin
    intros x hx,
    by_cases h : x = 0,
    { rwa [h, inv_zero, ← h], },
    { convert mem_closure_image (continuous_at_inv₀ h) hx using 2,
      ext x, split,
      { exact λ hx, ⟨x⁻¹, ⟨K.inv_mem hx, inv_inv x⟩⟩, },
      { rintros ⟨y, ⟨hy, rfl⟩⟩, exact K.inv_mem hy, }},
  end,
  ..K.to_subring.topological_closure, }

lemma subfield.le_topological_closure (s : subfield α) :
  s ≤ s.topological_closure := subset_closure

lemma subfield.is_closed_topological_closure (s : subfield α) :
  is_closed (s.topological_closure : set α) := is_closed_closure

lemma subfield.topological_closure_minimal
  (s : subfield α) {t : subfield α} (h : s ≤ t) (ht : is_closed (t : set α)) :
  s.topological_closure ≤ t := closure_minimal h ht

end subfield

section affine_homeomorph
/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/
variables {𝕜 : Type*} [field 𝕜] [topological_space 𝕜] [topological_ring 𝕜]

/--
The map `λ x, a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself, when `a ≠ 0`.
-/
@[simps]
def affine_homeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 :=
{ to_fun := λ x, a * x + b,
  inv_fun := λ y, (y - b) / a,
  left_inv := λ x, by { simp only [add_sub_cancel], exact mul_div_cancel_left x h, },
  right_inv := λ y, by { simp [mul_div_cancel' _ h], }, }

end affine_homeomorph

section local_extr

variables {α β : Type*} [topological_space α] [linear_ordered_semifield β] {a : α}
open_locale topology

lemma is_local_min.inv {f : α → β} {a : α} (h1 : is_local_min f a) (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
  is_local_max f⁻¹ a :=
by filter_upwards [h1, h2] with z h3 h4 using (inv_le_inv h4 h2.self_of_nhds).mpr h3

end local_extr

section preconnected
/-! Some results about functions on preconnected sets valued in a ring or field with a topology. -/

open set
variables {α 𝕜 : Type*} {f g : α → 𝕜} {S : set α}
  [topological_space α] [topological_space 𝕜] [t1_space 𝕜]

/-- If `f` is a function `α → 𝕜` which is continuous on a preconnected set `S`, and
`f ^ 2 = 1` on `S`, then either `f = 1` on `S`, or `f = -1` on `S`. -/
lemma is_preconnected.eq_one_or_eq_neg_one_of_sq_eq [ring 𝕜] [no_zero_divisors 𝕜]
  (hS : is_preconnected S) (hf : continuous_on f S) (hsq : eq_on (f ^ 2) 1 S) :
  (eq_on f 1 S) ∨ (eq_on f (-1) S) :=
begin
  simp_rw [eq_on, pi.one_apply, pi.pow_apply, sq_eq_one_iff] at hsq,
  -- First deal with crazy case where `S` is empty.
  by_cases hSe : ∀ (x:α), x ∉ S,
  { left, intros x hx,
    exfalso, exact hSe x hx, },
  push_neg at hSe,
  choose y hy using hSe,
  suffices : ∀ (x:α), x ∈ S → f x = f y,
  { rcases (hsq hy),
    { left, intros z hz, rw [pi.one_apply z, ←h], exact this z hz, },
    { right, intros z hz, rw [pi.neg_apply, pi.one_apply, ←h], exact this z hz, } },
  refine λ x hx, hS.constant_of_maps_to hf (λ z hz, _) hx hy,
  show f z ∈ ({-1, 1} : set 𝕜),
  { exact mem_insert_iff.mpr (hsq hz).symm,  },
  exact discrete_of_t1_of_finite,
end

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then either `f = g` or `f = -g` on
`S`. -/
lemma is_preconnected.eq_or_eq_neg_of_sq_eq [field 𝕜] [has_continuous_inv₀ 𝕜] [has_continuous_mul 𝕜]
  (hS : is_preconnected S) (hf : continuous_on f S) (hg : continuous_on g S)
  (hsq : eq_on (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x:α}, x ∈ S → g x ≠ 0) :
  (eq_on f g S) ∨ (eq_on f (-g) S) :=
begin
  rcases hS.eq_one_or_eq_neg_one_of_sq_eq (hf.div hg (λ z hz, hg_ne hz)) (λ x hx, _) with h | h,
  { refine or.inl (λ x hx, _),
    rw ←div_eq_one_iff_eq (hg_ne hx),
    exact h hx },
  { refine or.inr (λ x hx, _),
    specialize h hx,
    rwa [pi.div_apply, pi.neg_apply, pi.one_apply, div_eq_iff (hg_ne hx), neg_one_mul] at h,  },
  { rw [pi.one_apply, div_pow, pi.div_apply, hsq hx, div_self],
    exact pow_ne_zero _ (hg_ne hx) },
end

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then as soon as `f = g` holds at
one point of `S` it holds for all points. -/
lemma is_preconnected.eq_of_sq_eq [field 𝕜] [has_continuous_inv₀ 𝕜] [has_continuous_mul 𝕜]
  (hS : is_preconnected S) (hf : continuous_on f S) (hg : continuous_on g S)
  (hsq : eq_on (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x:α}, x ∈ S → g x ≠ 0)
  {y : α} (hy : y ∈ S) (hy' : f y = g y) : eq_on f g S :=
λ x hx, begin
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with h | h,
  { exact h hx },
  { rw [h hy, eq_comm, ←sub_eq_zero, sub_eq_add_neg, pi.neg_apply,
      neg_neg, ←mul_two, mul_eq_zero] at hy',
    cases hy', -- need to handle case of `char 𝕜 = 2` separately
    { exfalso, exact hg_ne hy hy' },
    { rw [h hx, pi.neg_apply, eq_comm, ←sub_eq_zero, sub_eq_add_neg, neg_neg,
       ←mul_two, hy', mul_zero], } },
end

end preconnected
