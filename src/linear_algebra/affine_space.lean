/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joseph Myers.
-/
import algebra.add_torsor
import linear_algebra.basis

noncomputable theory
open_locale big_operators

/-!
# Affine spaces

This file defines affine spaces (over modules) and subspaces, affine
maps, affine combinations of points, and the affine span of a set of
points.

## Implementation notes

This file is very minimal and many things are surely omitted. Most
results can be deduced from corresponding results for modules or
vector spaces.  The variables `k` and `V` are explicit rather than
implicit arguments to lemmas because otherwise the elaborator
sometimes has problems inferring appropriate types and type class
instances.  Definitions of affine spaces vary as to whether a space
with no points is permitted; here, we require a nonempty type of
points (via the definition of torsors requiring a nonempty type).

## References

* https://en.wikipedia.org/wiki/Affine_space
* https://en.wikipedia.org/wiki/Principal_homogeneous_space

-/

/-- `affine_space` is an abbreviation for `add_torsor` in the case
where the group is a vector space, or more generally a module, but we
omit the type classes `[ring k]` and `[module k V]` in the type
synonym itself to simplify type class search.. -/
@[nolint unused_arguments]
abbreviation affine_space (k : Type*) (V : Type*) (P : Type*) [add_comm_group V] :=
add_torsor V P

namespace affine_space

open add_action
open add_torsor

variables (k : Type*) (V : Type*) {P : Type*} [ring k] [add_comm_group V] [module k V]
variables [S : affine_space k V P]
include S

/-- The submodule spanning the differences of a (possibly empty) set
of points. -/
def vector_span (s : set P) : submodule k V := submodule.span k (vsub_set V s)

/-- The points in the affine span of a (possibly empty) set of
points. Use `affine_span` instead to get an `affine_subspace k V P`,
if the set of points is known to be nonempty. -/
def span_points (s : set P) : set P :=
{p | ∃ p1 ∈ s, ∃ v ∈ (vector_span k V s), p = v +ᵥ p1}

/-- A point in a set is in its affine span. -/
lemma mem_span_points (p : P) (s : set P) : p ∈ s → p ∈ span_points k V s
| hp := ⟨p, hp, 0, submodule.zero _, (zero_vadd V p).symm⟩

/-- The set of points in the affine span of a nonempty set of points
is nonempty. -/
lemma span_points_nonempty_of_nonempty {s : set P} :
  s.nonempty → (span_points k V s).nonempty 
| ⟨p, hp⟩ := ⟨p, mem_span_points k V p s hp⟩

/-- Adding a point in the affine span and a vector in the spanning
submodule produces a point in the affine span. -/
lemma vadd_mem_span_points_of_mem_span_points_of_mem_vector_span {s : set P} {p : P} {v : V}
    (hp : p ∈ span_points k V s) (hv : v ∈ vector_span k V s) : v +ᵥ p ∈ span_points k V s :=
begin
  rcases hp with ⟨p2, ⟨hp2, ⟨v2, ⟨hv2, hv2p⟩⟩⟩⟩,
  rw [hv2p, vadd_assoc],
  use [p2, hp2, v + v2, (vector_span k V s).add hv hv2, rfl]
end

/-- Subtracting two points in the affine span produces a vector in the
spanning submodule. -/
lemma vsub_mem_vector_span_of_mem_span_points_of_mem_span_points {s : set P} {p1 p2 : P}
    (hp1 : p1 ∈ span_points k V s) (hp2 : p2 ∈ span_points k V s) :
  p1 -ᵥ p2 ∈ vector_span k V s :=
begin
  rcases hp1 with ⟨p1a, ⟨hp1a, ⟨v1, ⟨hv1, hv1p⟩⟩⟩⟩,
  rcases hp2 with ⟨p2a, ⟨hp2a, ⟨v2, ⟨hv2, hv2p⟩⟩⟩⟩,
  rw [hv1p, hv2p, vsub_vadd_eq_vsub_sub V (v1 +ᵥ p1a), vadd_vsub_assoc, add_comm, add_sub_assoc],
  have hv1v2 : v1 - v2 ∈ vector_span k V s,
  { apply (vector_span k V s).add hv1,
    rw ←neg_one_smul k v2,
    exact (vector_span k V s).smul (-1 : k) hv2 },
  refine (vector_span k V s).add _ hv1v2,
  unfold vector_span,
  change p1a -ᵥ p2a ∈ submodule.span k (vsub_set V s),
  have hp1p2 : p1a -ᵥ p2a ∈ vsub_set V s, { use [p1a, hp1a, p2a, hp2a] },
  have hp1p2s : vsub_set V s ⊆ submodule.span k (vsub_set V s) := submodule.subset_span,
  apply set.mem_of_mem_of_subset hp1p2 hp1p2s
end

section combination

variables {k} {ι : Type*} [fintype ι]

/-- A weighted sum of the results of subtracting a base point from the
given points.  The main cases of interest are where the sum of the
weights is 0, in which case the sum is independent of the choice of
base point, and where the sum of the weights is 1, in which case the
sum added to the base point is independent of the choice of base
point. -/
def weighted_vsub_of_point (w : ι → k) (p : ι → P) (b : P) : V := ∑ i, w i • (p i -ᵥ b)

/-- The weighted sum when the weights are 0. -/
@[simp] lemma weighted_vsub_of_point_zero (p : ι → P) (b : P) :
  weighted_vsub_of_point V (0 : ι → k) p b = 0 :=
begin
  unfold weighted_vsub_of_point,
  conv_lhs {
    congr,
    skip,
    funext,
    erw zero_smul
  },
  exact finset.sum_const_zero
end

/-- The weighted sum, multiplied by a constant. -/
lemma weighted_vsub_of_point_smul (r : k) (w : ι → k) (p : ι → P) (b : P) :
  r • weighted_vsub_of_point V w p b = weighted_vsub_of_point V (r • w) p b :=
begin
  erw finset.smul_sum,
  congr,
  ext,
  rw ←mul_smul,
  refl
end

/-- The weighted sum, negated. -/
lemma weighted_vsub_of_point_neg (w : ι → k) (p : ι → P) (b : P) :
  -weighted_vsub_of_point V w p b = weighted_vsub_of_point V (-w) p b :=
begin
  erw ←finset.sum_neg_distrib,
  congr,
  ext,
  rw ←neg_smul,
  refl
end

/-- Adding two weighted sums. -/
lemma weighted_vsub_of_point_add (w₁ w₂ : ι → k) (p : ι → P) (b : P) :
  weighted_vsub_of_point V w₁ p b + weighted_vsub_of_point V w₂ p b =
    weighted_vsub_of_point V (w₁ + w₂) p b :=
begin
  erw ←finset.sum_add_distrib,
  congr,
  ext,
  rw ←add_smul,
  refl
end

/-- Subtracting two weighted sums. -/
lemma weighted_vsub_of_point_sub (w₁ w₂ : ι → k) (p : ι → P) (b : P) :
  weighted_vsub_of_point V w₁ p b - weighted_vsub_of_point V w₂ p b =
    weighted_vsub_of_point V (w₁ - w₂) p b :=
begin
  erw ←finset.sum_sub_distrib,
  congr,
  ext,
  rw ←sub_smul,
  refl
end

/-- The weighted sum is independent of the base point when the sum of
the weights is 0. -/
lemma weighted_vsub_of_point_eq_of_sum_eq_zero (w : ι → k) (p : ι → P) (h : ∑ i, w i = 0)
    (b1 b2 : P) : weighted_vsub_of_point V w p b1 = weighted_vsub_of_point V w p b2 :=
begin
  apply eq_of_sub_eq_zero,
  erw ←finset.sum_sub_distrib,
  conv_lhs {
    congr,
    skip,
    funext,
    rw [←smul_sub, vsub_sub_vsub_cancel_left]
  },
  rw [←finset.sum_smul, h, zero_smul]
end

/-- The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1. -/
lemma weighted_vsub_of_point_vadd_eq_of_sum_eq_one (w : ι → k) (p : ι → P) (h : ∑ i, w i = 1)
    (b1 b2 : P) : weighted_vsub_of_point V w p b1 +ᵥ b1 = weighted_vsub_of_point V w p b2 +ᵥ b2 :=
begin
  erw [←vsub_eq_zero_iff_eq V, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub, ←add_sub_assoc, add_comm,
       add_sub_assoc, ←finset.sum_sub_distrib],
  conv_lhs {
    congr,
    skip,
    congr,
    skip,
    funext,
    rw [←smul_sub, vsub_sub_vsub_cancel_left]
  },
  rw [←finset.sum_smul, h, one_smul, vsub_add_vsub_cancel, vsub_self]
end

/-- A weighted sum of the results of subtracting a default base point
from the given points.  This is intended to be used when the sum of
the weights is 0; that condition is specified as a hypothesis on those
lemmas that require it. -/
def weighted_vsub (w : ι → k) (p : ι → P) : V :=
weighted_vsub_of_point V w p (classical.choice S.nonempty)

/-- `weighted_vsub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
lemma weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero (w : ι → k) (p : ι → P)
    (h : ∑ i, w i = 0) (b : P) : weighted_vsub V w p = weighted_vsub_of_point V w p b :=
weighted_vsub_of_point_eq_of_sum_eq_zero V w p h _ _

/-- The weighted sum when the weights are 0. -/
@[simp] lemma weighted_vsub_zero (p : ι → P) : weighted_vsub V (0 : ι → k) p = 0 :=
weighted_vsub_of_point_zero V p _

/-- The weighted sum, multiplied by a constant. -/
lemma weighted_vsub_smul (r : k) (w : ι → k) (p : ι → P) :
  r • weighted_vsub V w p = weighted_vsub V (r • w) p :=
weighted_vsub_of_point_smul V r w p _

/-- The weighted sum, negated. -/
lemma weighted_vsub_neg (w : ι → k) (p : ι → P) :
  -weighted_vsub V w p = weighted_vsub V (-w) p :=
weighted_vsub_of_point_neg V w p _

/-- Adding two weighted sums. -/
lemma weighted_vsub_add (w₁ w₂ : ι → k) (p : ι → P) :
  weighted_vsub V w₁ p + weighted_vsub V w₂ p = weighted_vsub V (w₁ + w₂) p :=
weighted_vsub_of_point_add V w₁ w₂ p _

/-- Subtracting two weighted sums. -/
lemma weighted_vsub_sub (w₁ w₂ : ι → k) (p : ι → P) :
  weighted_vsub V w₁ p - weighted_vsub V w₂ p = weighted_vsub V (w₁ - w₂) p :=
weighted_vsub_of_point_sub V w₁ w₂ p _

/-- A weighted sum of the results of subtracting a default base point
from the given points, added to that base point.  This is intended to
be used when the sum of the weights is 1, in which case it is an
affine combination (barycenter) of the points with the given weights;
that condition is specified as a hypothesis on those lemmas that
require it. -/
def affine_combination (w : ι → k) (p : ι → P) : P :=
weighted_vsub_of_point V w p (classical.choice S.nonempty) +ᵥ (classical.choice S.nonempty)

/-- `affine_combination` gives the sum with any base point, when the
sum of the weights is 1. -/
lemma affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one (w : ι → k) (p : ι → P)
    (h : ∑ i, w i = 1) (b : P) : affine_combination V w p = weighted_vsub_of_point V w p b +ᵥ b :=
weighted_vsub_of_point_vadd_eq_of_sum_eq_one V w p h _ _

/-- Adding a `weighted_vsub` to an `affine_combination`. -/
lemma weighted_vsub_vadd_affine_combination (w₁ w₂ : ι → k) (p : ι → P) :
  weighted_vsub V w₁ p +ᵥ affine_combination V w₂ p = affine_combination V (w₁ + w₂) p :=
begin
  erw vadd_assoc,
  congr,
  exact weighted_vsub_add V w₁ w₂ p
end

/-- Subtracting two `affine_combination`s. -/
lemma affine_combination_vsub (w₁ w₂ : ι → k) (p : ι → P) :
  affine_combination V w₁ p -ᵥ affine_combination V w₂ p = weighted_vsub V (w₁ - w₂) p :=
begin
  erw vadd_vsub_vadd_cancel_right,
  exact weighted_vsub_sub V w₁ w₂ p
end

end combination

end affine_space

open add_torsor affine_space

/-- An `affine_subspace k V P` is a subset of an `affine_space k V P`
that has an affine space structure induced by a corresponding subspace
of the `module k V`. -/
structure affine_subspace (k : Type*) (V : Type*) (P : Type*) [ring k] [add_comm_group V]
    [module k V] [affine_space k V P] :=
(carrier : set P)
(direction : submodule k V)
(nonempty : carrier.nonempty)
(add : ∀ (p : P) (v : V), p ∈ carrier → v ∈ direction → v +ᵥ p ∈ carrier)
(sub : ∀ (p1 p2 : P), p1 ∈ carrier → p2 ∈ carrier → p1 -ᵥ p2 ∈ direction)

namespace affine_subspace

variables (k : Type*) (V : Type*) (P : Type*) [ring k] [add_comm_group V] [module k V]
          [S : affine_space k V P]
include S

instance : has_coe (affine_subspace k V P) (set P) := ⟨carrier⟩
instance : has_mem P (affine_subspace k V P) := ⟨λ p s, p ∈ (s : set P)⟩

/-- A point is in an affine subspace coerced to a set if and only if
it is in that affine subspace. -/
@[simp] lemma mem_coe (p : P) (s : affine_subspace k V P) :
  p ∈ (s : set P) ↔ p ∈ s :=
iff.rfl

/-- The whole affine space as a subspace of itself. -/
def univ : affine_subspace k V P :=
{ carrier := set.univ,
  direction := submodule.span k set.univ,
  nonempty := set.nonempty_iff_univ_nonempty.1 S.nonempty,
  add := λ p v hp hv, set.mem_univ _,
  sub := begin
    intros p1 p2 hp1 hp2,
    apply set.mem_bInter,
    intros x hx,
    rw set.mem_set_of_eq at hx,
    exact set.mem_of_mem_of_subset (set.mem_univ _) hx
  end }

/-- `univ`, coerced to a set, is the whole set of points. -/
@[simp] lemma univ_coe : (univ k V P : set P) = set.univ :=
rfl

/-- All points are in `univ`. -/
lemma mem_univ (p : P) : p ∈ univ k V P :=
set.mem_univ p

instance : inhabited (affine_subspace k V P) := ⟨univ k V P⟩

end affine_subspace

section affine_span

variables (k : Type*) (V : Type*) (P : Type*) [ring k] [add_comm_group V] [module k V]
          [affine_space k V P]

/-- The affine span of a nonempty set of points is the smallest affine
subspace containing those points. (Actually defined here in terms of
spans in modules.) -/
def affine_span (s : set P) (h : s.nonempty) : affine_subspace k V P :=
{ carrier := span_points k V s,
  direction := vector_span k V s,
  nonempty := span_points_nonempty_of_nonempty k V h,
  add := λ p v hp hv, vadd_mem_span_points_of_mem_span_points_of_mem_vector_span k V hp hv,
  sub := λ p1 p2 hp1 hp2, vsub_mem_vector_span_of_mem_span_points_of_mem_span_points k V hp1 hp2 }

/-- The affine span, converted to a set, is `span_points`. -/
@[simp] lemma affine_span_coe (s : set P) (h : s.nonempty) :
  (affine_span k V P s h : set P) = span_points k V s :=
rfl

/-- A point in a set is in its affine span. -/
lemma affine_span_mem (p : P) (s : set P) (hp : p ∈ s) : p ∈ affine_span k V P s ⟨p, hp⟩ :=
mem_span_points k V p s hp

end affine_span

/-- An `affine_map k V1 P1 V2 P2` is a map from `P1` to `P2` that
induces a corresponding linear map from `V1` to `V2`. -/
structure affine_map (k : Type*) (V1 : Type*) (P1 : Type*) (V2 : Type*) (P2 : Type*)
    [ring k]
    [add_comm_group V1] [module k V1] [affine_space k V1 P1]
    [add_comm_group V2] [module k V2] [affine_space k V2 P2] :=
(to_fun : P1 → P2)
(linear : linear_map k V1 V2)
(map_vadd' : ∀ (p : P1) (v : V1), to_fun (v +ᵥ p) =  linear v +ᵥ to_fun p)

namespace affine_map

variables {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*}
    {V3 : Type*} {P3 : Type*} [ring k]
    [add_comm_group V1] [module k V1] [affine_space k V1 P1]
    [add_comm_group V2] [module k V2] [affine_space k V2 P2]
    [add_comm_group V3] [module k V3] [affine_space k V3 P3]

instance: has_coe_to_fun (affine_map k V1 P1 V2 P2) := ⟨_, to_fun⟩

/-- Constructing an affine map and coercing back to a function
produces the same map. -/
@[simp] lemma coe_mk (f : P1 → P2) (linear add) :
  ((mk f linear add : affine_map k V1 P1 V2 P2) : P1 → P2) = f := rfl

/-- `to_fun` is the same as the result of coercing to a function. -/
@[simp] lemma to_fun_eq_coe (f : affine_map k V1 P1 V2 P2) : f.to_fun = ⇑f := rfl

/-- An affine map on the result of adding a vector to a point produces
the same result as the linear map applied to that vector, added to the
affine map applied to that point. -/
@[simp] lemma map_vadd (f : affine_map k V1 P1 V2 P2) (p : P1) (v : V1) :
  f (v +ᵥ p) = f.linear v +ᵥ f p := f.map_vadd' p v

/-- The linear map on the result of subtracting two points is the
result of subtracting the result of the affine map on those two
points. -/
lemma map_vsub (f : affine_map k V1 P1 V2 P2) (p1 p2 : P1) :
  f p1 -ᵥ f p2 = f.linear (p1 -ᵥ p2) :=
by conv_lhs { rw [←vsub_vadd V1 p1 p2, map_vadd, vadd_vsub] }

/-- Two affine maps are equal if they coerce to the same function. -/
@[ext] lemma ext (f g : affine_map k V1 P1 V2 P2) (h : (f : P1 → P2) = g) : f = g :=
begin
  rcases f with ⟨f, f_linear, f_add⟩,
  rcases g with ⟨g, g_linear, g_add⟩,
  change f = g at h,
  subst g,
  congr',
  ext v,
  cases (add_torsor.nonempty V1 : nonempty P1) with p,
  apply vadd_right_cancel (f p),
  erw [← f_add, ← g_add]
end

/-- Construct an affine map by verifying the relation between the map and its linear part at one
base point. Namely, this function takes a map `f : P₁ → P₂`, a linear map `f' : V₁ →ₗ[k] V₂`, and
a point `p` such that for any other point `p'` we have `f p' = f' (p' -ᵥ p) +ᵥ f p`. -/
def mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p : P1) (h : ∀ p' : P1, f p' = f' (p' -ᵥ p) +ᵥ f p) :
  affine_map k V1 P1 V2 P2 :=
{ to_fun := f,
  linear := f',
  map_vadd' := λ p' v, by rw [h, h p', vadd_vsub_assoc, f'.map_add, add_action.vadd_assoc] }

@[simp] lemma coe_mk' (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : ⇑(mk' f f' p h) = f := rfl

@[simp] lemma mk'_linear (f : P1 → P2) (f' : V1 →ₗ[k] V2) (p h) : (mk' f f' p h).linear = f' := rfl

variables (k V1 P1)

/-- Identity map as an affine map. -/
def id : affine_map k V1 P1 V1 P1 :=
{ to_fun := id,
  linear := linear_map.id,
  map_vadd' := λ p v, rfl }

/-- The identity affine map acts as the identity. -/
@[simp] lemma coe_id : ⇑(id k V1 P1) = _root_.id := rfl

variable {P1}

/-- The identity affine map acts as the identity. -/
lemma id_apply (p : P1) : id k V1 P1 p = p := rfl

variables {k V1 P1}

instance : inhabited (affine_map k V1 P1 V1 P1) := ⟨id k V1 P1⟩

/-- Composition of affine maps. -/
def comp (f : affine_map k V2 P2 V3 P3) (g : affine_map k V1 P1 V2 P2) :
  affine_map k V1 P1 V3 P3 :=
{ to_fun := f ∘ g,
  linear := f.linear.comp g.linear,
  map_vadd' := begin
    intros p v,
    rw [function.comp_app, g.map_vadd, f.map_vadd],
    refl
  end }

/-- Composition of affine maps acts as applying the two functions. -/
@[simp] lemma coe_comp (f : affine_map k V2 P2 V3 P3) (g : affine_map k V1 P1 V2 P2) :
  ⇑(f.comp g) = f ∘ g := rfl

/-- Composition of affine maps acts as applying the two functions. -/
lemma comp_apply (f : affine_map k V2 P2 V3 P3) (g : affine_map k V1 P1 V2 P2) (p : P1) :
  f.comp g p = f (g p) := rfl

end affine_map
