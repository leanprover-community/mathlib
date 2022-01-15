/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import topology.opens
import ring_theory.ideal.prod
import linear_algebra.finsupp
import algebra.punit_instances
import ring_theory.graded_algebra.homogeneous_ideal
import algebra.direct_sum.ring
import algebraic_geometry.projective_spectrum.clear_denominator

/-!
# Prime spectrum of a commutative ring

The prime spectrum of a commutative ring is the type of all prime ideals.
It is naturally endowed with a topology: the Zariski topology.

(It is also naturally endowed with a sheaf of rings,
which is constructed in `algebraic_geometry.structure_sheaf`.)

## Main definitions

* `prime_spectrum R`: The prime spectrum of a commutative ring `R`,
  i.e., the set of all prime ideals of `R`.
* `zero_locus s`: The zero locus of a subset `s` of `R`
  is the subset of `prime_spectrum R` consisting of all prime ideals that contain `s`.
* `vanishing_ideal t`: The vanishing ideal of a subset `t` of `prime_spectrum R`
  is the intersection of points in `t` (viewed as prime ideals).

## Conventions

We denote subsets of rings with `s`, `s'`, etc...
whereas we denote subsets of prime spectra with `t`, `t'`, etc...

## Inspiration/contributors

The contents of this file draw inspiration from
<https://github.com/ramonfmir/lean-scheme>
which has contributions from Ramon Fernandez Mir, Kevin Buzzard, Kenny Lau,
and Chris Hughes (on an earlier repository).

-/

noncomputable theory
open_locale direct_sum big_operators pointwise
open direct_sum set_like

variables {R A: Type}
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]


/-- `irrelavent_ideal` is the homogeneous ideal generated by homogeneous
element of positie grading-/
def irrelavent_ideal [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)] : homogeneous_ideal 𝒜 :=
{ val := { carrier := {a | graded_algebra.proj 𝒜 0 a = 0 },
  zero_mem' := begin
    change graded_algebra.proj 𝒜 0 0 = 0,
    rw linear_map.map_zero,
  end, add_mem' := λ x y hx hy, begin
    change graded_algebra.proj 𝒜 0 (x+y) = 0,
    change graded_algebra.proj 𝒜 0 x = 0 at hx,
    change graded_algebra.proj 𝒜 0 y = 0 at hy,
    rw linear_map.map_add,
    rw [hx, hy, add_zero],
  end, smul_mem' := λ c x hx, begin
    apply set_like.homogeneous_induction 𝒜 c,
    { intros, rw zero_smul,
      change graded_algebra.proj 𝒜 0 0 = 0,
      rw linear_map.map_zero, },
    { rintros ⟨a, ⟨m, hm⟩⟩,
      dsimp only,
      change graded_algebra.proj 𝒜 0 (a • x) = 0,
      rw [smul_eq_mul, ←graded_algebra.sum_support_decompose 𝒜 x, finset.mul_sum, linear_map.map_sum],
      apply finset.sum_eq_zero,
      intros i hi,
      rw ←graded_algebra.proj_apply,
      change graded_algebra.proj 𝒜 0 _ = 0 at hx,
      have mem1 : a * graded_algebra.proj 𝒜 i x ∈ 𝒜 (m + i),
      { apply set_like.graded_monoid.mul_mem hm (submodule.coe_mem _), },
      by_cases ineq : i + m = 0,
      { have : i = 0,
        { rcases nat.lt_trichotomy i 0 with LT | EQ | GT,
          { exfalso, apply nat.not_lt_zero _ LT, },
          { exact EQ, },
          { have ineq1 := nat.le_add_left i m,
            rw [nat.add_comm, ineq] at ineq1,
            exfalso, linarith only [GT, ineq1], }, },
        rw [←ineq, this, graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same,
          hx, mul_zero],
        rw [this, add_comm] at mem1,
        exact mem1, },
      { rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_ne 𝒜 mem1],
        rw [add_comm, ne.def],
        exact ineq, }, },
    { intros c1 c2 hc1 hc2,
      change graded_algebra.proj 𝒜 0 ((c1 + c2) • x) = 0,
      change graded_algebra.proj 𝒜 0 (c1 • x) = 0 at hc1,
      change graded_algebra.proj 𝒜 0 (c2 • x) = 0 at hc2,
      rw [add_smul, linear_map.map_add, hc1, hc2, add_zero], },
  end },
  property := begin
    intros i a ha,
    by_cases ineq : i = 0,
    { change graded_algebra.proj 𝒜 0 _ = 0,
      change graded_algebra.proj 𝒜 0 _ = 0 at ha,
      rw [graded_algebra.proj_apply, ineq, graded_algebra.decompose_of_mem_same],
      apply ha,
      rw ←graded_algebra.proj_apply,
      exact submodule.coe_mem _, },
    { change graded_algebra.proj 𝒜 0 _ = 0 at ha,
      change graded_algebra.proj 𝒜 0 _ = 0,
      rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_ne 𝒜 _ ineq],
      rw ←graded_algebra.proj_apply,
      exact submodule.coe_mem _, },
  end }

lemma irrelavent_ideal.mem [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)] (a : A) (ha : a ∈ irrelavent_ideal 𝒜) :
  graded_algebra.proj 𝒜 0 a = 0 :=
begin
  rw irrelavent_ideal at ha,
  exact ha,
end

@[nolint has_inhabited_instance]
def projective_spectrum  [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)] :=
  {I : homogeneous_ideal 𝒜 //
    I.1.is_prime ∧ ¬(irrelavent_ideal 𝒜 ≤ I)}

namespace projective_spectrum


variable {𝒜}
variable [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)]
/-- A method to view a point in the prime spectrum of a commutative ring
as an ideal of that ring. -/
abbreviation as_homogeneous_ideal (x : projective_spectrum 𝒜) :
  homogeneous_ideal 𝒜 := x.val

lemma as_homogeneous_ideal.explicit (x : projective_spectrum 𝒜) :
  x.as_homogeneous_ideal = x.1 := rfl

instance is_prime (x : projective_spectrum 𝒜) :
  x.as_homogeneous_ideal.1.is_prime := x.2.1

@[ext] lemma ext {x y : projective_spectrum 𝒜} :
  x = y ↔ x.as_homogeneous_ideal = y.as_homogeneous_ideal :=
subtype.ext_iff_val

/-- The zero locus of a set `s` of elements of a commutative ring `R`
is the set of all prime ideals of the ring that contain the set `s`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `zero_locus s` is exactly the subset of `prime_spectrum R`
where all "functions" in `s` vanish simultaneously.
-/

variable (𝒜)

def zero_locus (s : set A) : set (projective_spectrum 𝒜) :=
{x | s ⊆ x.as_homogeneous_ideal}

@[simp] lemma mem_zero_locus (x : projective_spectrum 𝒜) (s : set A) :
  x ∈ zero_locus 𝒜 s ↔ s ⊆ x.as_homogeneous_ideal := iff.rfl

@[simp] lemma zero_locus_span (s : set A) :
  zero_locus 𝒜 (ideal.span s) = zero_locus 𝒜 s :=
by { ext x, exact (submodule.gi _ _).gc s x.as_homogeneous_ideal }

/-- The vanishing ideal of a set `t` of points
of the prime spectrum of a commutative ring `R`
is the intersection of all the prime ideals in the set `t`.

An element `f` of `R` can be thought of as a dependent function
on the prime spectrum of `R`.
At a point `x` (a prime ideal)
the function (i.e., element) `f` takes values in the quotient ring `R` modulo the prime ideal `x`.
In this manner, `vanishing_ideal t` is exactly the ideal of `R`
consisting of all "functions" that vanish on all of `t`.
-/
def vanishing_ideal (t : set (projective_spectrum 𝒜)) : ideal A :=
⨅ (x : projective_spectrum 𝒜) (h : x ∈ t), x.as_homogeneous_ideal.1

lemma vanishing_ideal.is_prime (t : set (projective_spectrum 𝒜)) :
  ideal.is_homogeneous 𝒜 $ vanishing_ideal 𝒜 t :=
begin
  apply ideal.is_homogeneous.Inf, intros I hI,
  rw set.mem_range at hI,
  obtain ⟨y, hy⟩ := hI,
  rw ←hy,
  apply ideal.is_homogeneous.Inf, intros J HJ,
  rw set.mem_range at HJ,
  obtain ⟨hy2, rfl⟩ := HJ,
  exact y.1.2,
end

lemma coe_vanishing_ideal (t : set (projective_spectrum 𝒜)) :
  (vanishing_ideal 𝒜 t : set A) =
  {f | ∀ x : projective_spectrum 𝒜, x ∈ t → f ∈ x.as_homogeneous_ideal} :=
begin
  ext f,
  rw [vanishing_ideal, set_like.mem_coe, submodule.mem_infi],
  apply forall_congr, intro x,
  rw [submodule.mem_infi], refl,
end

lemma mem_vanishing_ideal (t : set (projective_spectrum 𝒜)) (f : A) :
  f ∈ vanishing_ideal 𝒜 t ↔
  ∀ x : projective_spectrum 𝒜, x ∈ t → f ∈ x.as_homogeneous_ideal :=
by rw [← set_like.mem_coe, coe_vanishing_ideal, set.mem_set_of_eq]

@[simp] lemma vanishing_ideal_singleton (x : projective_spectrum 𝒜) :
  vanishing_ideal 𝒜 ({x} : set (projective_spectrum 𝒜)) = x.as_homogeneous_ideal :=
by simp [vanishing_ideal]

lemma subset_zero_locus_iff_le_vanishing_ideal (t : set (projective_spectrum 𝒜))
  (I : ideal A) :
  t ⊆ zero_locus 𝒜 I ↔ I ≤ vanishing_ideal 𝒜 t :=
⟨λ h f k, (mem_vanishing_ideal _ _ _).mpr (λ x j, (mem_zero_locus _ _ _).mpr (h j) k), λ h,
  λ x j, (mem_zero_locus _ _ _).mpr (le_trans h (λ f h, ((mem_vanishing_ideal _ _ _).mp h) x j))⟩

section gc
variable (A)

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
lemma gc : @galois_connection
  (ideal A) (order_dual (set (projective_spectrum 𝒜))) _ _
  (λ I, zero_locus 𝒜 I) (λ t, vanishing_ideal 𝒜 t) :=
λ I t, subset_zero_locus_iff_le_vanishing_ideal 𝒜 t I

/-- `zero_locus` and `vanishing_ideal` form a galois connection. -/
lemma gc_set : @galois_connection
  (set A) (order_dual (set (projective_spectrum 𝒜))) _ _
  (λ s, zero_locus 𝒜 s) (λ t, vanishing_ideal 𝒜 t) :=
have ideal_gc : galois_connection (ideal.span) coe := (submodule.gi A _).gc,
by simpa [zero_locus_span, function.comp] using galois_connection.compose ideal_gc (gc _ 𝒜)

lemma subset_zero_locus_iff_subset_vanishing_ideal (t : set (projective_spectrum 𝒜))
  (s : set A) :
  t ⊆ zero_locus 𝒜 s ↔ s ⊆ vanishing_ideal 𝒜 t :=
(gc_set _ _) s t

end gc

lemma subset_vanishing_ideal_zero_locus (s : set A) :
  s ⊆ vanishing_ideal 𝒜 (zero_locus 𝒜 s) :=
(gc_set _ _).le_u_l s

lemma le_vanishing_ideal_zero_locus (I : ideal A) :
  I ≤ vanishing_ideal 𝒜 (zero_locus 𝒜 I) :=
(gc _ _).le_u_l I

lemma subset_zero_locus_vanishing_ideal (t : set (projective_spectrum 𝒜)) :
  t ⊆ zero_locus 𝒜 (vanishing_ideal 𝒜 t) :=
(gc A _).l_u_le t

lemma zero_locus_anti_mono {s t : set A} (h : s ⊆ t) : zero_locus 𝒜 t ⊆ zero_locus 𝒜 s :=
(gc_set A _).monotone_l h

lemma zero_locus_anti_mono_ideal {s t : ideal A} (h : s ≤ t) :
  zero_locus 𝒜 (t : set A) ⊆ zero_locus 𝒜 (s : set A) :=
(gc A _).monotone_l h

lemma vanishing_ideal_anti_mono {s t : set (projective_spectrum 𝒜)} (h : s ⊆ t) :
  vanishing_ideal 𝒜 t ≤ vanishing_ideal 𝒜 s :=
(gc A _).monotone_u h

lemma zero_locus_bot :
  zero_locus 𝒜 ((⊥ : ideal A) : set A) = set.univ :=
(@gc R A _ _ _ 𝒜 _ _).l_bot

@[simp] lemma zero_locus_singleton_zero :
  zero_locus 𝒜 ({0} : set A) = set.univ :=
zero_locus_bot _

@[simp] lemma zero_locus_empty :
  zero_locus 𝒜 (∅ : set A) = set.univ :=
(@gc_set R A _ _ _ 𝒜 _ _).l_bot

@[simp] lemma vanishing_ideal_univ :
  vanishing_ideal 𝒜 (∅ : set (projective_spectrum 𝒜)) = ⊤ :=
by simpa using (gc A _).u_top

lemma zero_locus_empty_of_one_mem {s : set A} (h : (1:A) ∈ s) :
  zero_locus 𝒜 s = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  intros x hx,
  rw mem_zero_locus at hx,
  have x_prime :x.as_homogeneous_ideal.1.is_prime := by apply_instance,
  have eq_top : x.as_homogeneous_ideal = ⊤,
  { rw [homogeneous_ideal.eq_top_iff, ideal.eq_top_iff_one], exact hx h },
  apply x_prime.ne_top,
  rw ←homogeneous_ideal.eq_top_iff, exact eq_top,
end

@[simp] lemma zero_locus_singleton_one :
  zero_locus 𝒜 ({1} : set A) = ∅ :=
zero_locus_empty_of_one_mem 𝒜 (set.mem_singleton (1 : A))

@[simp] lemma zero_locus_univ :
  zero_locus 𝒜 (set.univ : set A) = ∅ :=
zero_locus_empty_of_one_mem _ (set.mem_univ 1)

lemma zero_locus_sup (I J : ideal A) :
  zero_locus 𝒜 ((I ⊔ J : ideal A) : set A) = zero_locus _ I ∩ zero_locus _ J :=
(@gc R A _ _ _ 𝒜 _ _).l_sup

lemma zero_locus_union (s s' : set A) :
  zero_locus 𝒜 (s ∪ s') = zero_locus _ s ∩ zero_locus _ s' :=
(@gc_set R A _ _ _ 𝒜 _ _).l_sup

lemma vanishing_ideal_union (t t' : set (projective_spectrum 𝒜)) :
  vanishing_ideal 𝒜 (t ∪ t') = vanishing_ideal 𝒜 t ⊓ vanishing_ideal 𝒜 t' :=
(@gc R A _ _ _ 𝒜 _ _).u_inf

lemma zero_locus_supr {γ : Sort*} (I : γ → ideal A) :
  zero_locus _ ((⨆ i, I i : ideal A) : set A) = (⋂ i, zero_locus 𝒜 (I i)) :=
(@gc R A _ _ _ 𝒜 _ _).l_supr

lemma zero_locus_Union {γ : Sort*} (s : γ → set A) :
  zero_locus 𝒜 (⋃ i, s i) = (⋂ i, zero_locus 𝒜 (s i)) :=
(@gc_set R A _ _ _ 𝒜 _ _).l_supr

lemma zero_locus_bUnion (s : set (set A)) :
  zero_locus 𝒜 (⋃ s' ∈ s, s' : set A) = ⋂ s' ∈ s, zero_locus 𝒜 s' :=
by simp only [zero_locus_Union]

lemma vanishing_ideal_Union {γ : Sort*} (t : γ → set (projective_spectrum 𝒜)) :
  vanishing_ideal 𝒜 (⋃ i, t i) = (⨅ i, vanishing_ideal 𝒜 (t i)) :=
(@gc R A _ _ _ 𝒜 _ _).u_infi

lemma zero_locus_inf (I J : ideal A) :
  zero_locus 𝒜 ((I ⊓ J : ideal A) : set A) = zero_locus 𝒜 I ∪ zero_locus 𝒜 J :=
set.ext $ λ x, by simpa using x.2.1.inf_le

lemma union_zero_locus (s s' : set A) :
  zero_locus 𝒜 s ∪ zero_locus 𝒜 s' = zero_locus 𝒜 ((ideal.span s) ⊓ (ideal.span s'): ideal A) :=
by { rw zero_locus_inf, simp }

lemma zero_locus_mul (I J : ideal A) :
  zero_locus 𝒜 ((I * J : ideal A) : set A) = zero_locus 𝒜 I ∪ zero_locus 𝒜 J :=
set.ext $ λ x, by simpa using x.2.1.mul_le

lemma zero_locus_singleton_mul (f g : A) :
  zero_locus 𝒜 ({f * g} : set A) = zero_locus 𝒜 {f} ∪ zero_locus 𝒜 {g} :=
set.ext $ λ x, by simpa using x.2.1.mul_mem_iff_mem_or_mem

@[simp] lemma zero_locus_singleton_pow (f : A) (n : ℕ) (hn : 0 < n) :
  zero_locus 𝒜 ({f ^ n} : set A) = zero_locus 𝒜 {f} :=
set.ext $ λ x, by simpa using x.2.1.pow_mem_iff_mem n hn

lemma sup_vanishing_ideal_le (t t' : set (projective_spectrum 𝒜)) :
  vanishing_ideal 𝒜 t ⊔ vanishing_ideal 𝒜 t' ≤ vanishing_ideal 𝒜 (t ∩ t') :=
begin
  intros r,
  rw [submodule.mem_sup, mem_vanishing_ideal],
  rintro ⟨f, hf, g, hg, rfl⟩ x ⟨hxt, hxt'⟩,
  rw mem_vanishing_ideal at hf hg,
  apply submodule.add_mem; solve_by_elim
end

lemma mem_compl_zero_locus_iff_not_mem {f : A} {I : projective_spectrum 𝒜} :
  I ∈ (zero_locus 𝒜 {f} : set (projective_spectrum 𝒜))ᶜ ↔ f ∉ I.as_homogeneous_ideal :=
by rw [set.mem_compl_eq, mem_zero_locus, set.singleton_subset_iff]; refl

/-- The Zariski topology on the prime spectrum of a commutative ring
is defined via the closed sets of the topology:
they are exactly those sets that are the zero locus of a subset of the ring. -/
instance zariski_topology : topological_space (projective_spectrum 𝒜) :=
topological_space.of_closed (set.range (projective_spectrum.zero_locus 𝒜))
  (⟨set.univ, by simp⟩)
  begin
    intros Zs h,
    rw set.sInter_eq_Inter,
    let f : Zs → set _ := λ i, classical.some (h i.2),
    have hf : ∀ i : Zs, ↑i = zero_locus 𝒜 (f i) := λ i, (classical.some_spec (h i.2)).symm,
    simp only [hf],
    exact ⟨_, zero_locus_Union 𝒜 _⟩
  end
  (by { rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩, exact ⟨_, (union_zero_locus 𝒜 s t).symm⟩ })

lemma is_open_iff (U : set (projective_spectrum 𝒜)) :
  is_open U ↔ ∃ s, Uᶜ = zero_locus 𝒜 s :=
by simp only [@eq_comm _ Uᶜ]; refl

lemma is_closed_iff_zero_locus (Z : set (projective_spectrum 𝒜)) :
  is_closed Z ↔ ∃ s, Z = zero_locus 𝒜 s :=
by rw [← is_open_compl_iff, is_open_iff, compl_compl]

lemma is_closed_zero_locus (s : set A) :
  is_closed (zero_locus 𝒜 s) :=
by { rw [is_closed_iff_zero_locus], exact ⟨s, rfl⟩ }

lemma zero_locus_vanishing_ideal_eq_closure (t : set (projective_spectrum 𝒜)) :
  zero_locus 𝒜 (vanishing_ideal 𝒜 t : set A) = closure t :=
begin
  apply set.subset.antisymm,
  { rintro x hx t' ⟨ht', ht⟩,
    obtain ⟨fs, rfl⟩ : ∃ s, t' = zero_locus 𝒜 s,
    by rwa [is_closed_iff_zero_locus] at ht',
    rw [subset_zero_locus_iff_subset_vanishing_ideal] at ht,
    exact set.subset.trans ht hx },
  { rw (is_closed_zero_locus _ _).closure_subset_iff,
    exact subset_zero_locus_vanishing_ideal 𝒜 t }
end

lemma vanishing_ideal_closure (t : set (projective_spectrum 𝒜)) :
  vanishing_ideal 𝒜 (closure t) = vanishing_ideal 𝒜 t :=
begin
  have := (gc A 𝒜).u_l_u_eq_u t,
  dsimp only at this,
  rw zero_locus_vanishing_ideal_eq_closure 𝒜 t at this,
  exact this,
end

section basic_open

/-- `basic_open r` is the open subset containing all prime ideals not containing `r`. -/
def basic_open (r : A) : topological_space.opens (projective_spectrum 𝒜) :=
{ val := { x | r ∉ x.as_homogeneous_ideal },
  property := ⟨{r}, set.ext $ λ x, set.singleton_subset_iff.trans $ not_not.symm⟩ }

@[simp] lemma mem_basic_open (f : A) (x : projective_spectrum 𝒜) :
  x ∈ basic_open 𝒜 f ↔ f ∉ x.as_homogeneous_ideal := iff.rfl

lemma is_open_basic_open {a : A} : is_open ((basic_open 𝒜 a) :
  set (projective_spectrum 𝒜)) :=
(basic_open 𝒜 a).property

@[simp] lemma basic_open_eq_zero_locus_compl (r : A) :
  (basic_open 𝒜 r : set (projective_spectrum 𝒜)) = (zero_locus 𝒜 {r})ᶜ :=
set.ext $ λ x, by simpa only [set.mem_compl_eq, mem_zero_locus, set.singleton_subset_iff]

@[simp] lemma basic_open_one : basic_open 𝒜 (1 : A) = ⊤ :=
topological_space.opens.ext $ by simp

@[simp] lemma basic_open_zero : basic_open 𝒜 (0 : A) = ⊥ :=
topological_space.opens.ext $ by simp

lemma basic_open_mul (f g : A) : basic_open 𝒜 (f * g) = basic_open 𝒜 f ⊓ basic_open 𝒜 g :=
topological_space.opens.ext $ by {simp [zero_locus_singleton_mul]}

lemma basic_open_mul_le_left (f g : A) : basic_open 𝒜 (f * g) ≤ basic_open 𝒜 f :=
by { rw basic_open_mul 𝒜 f g, exact inf_le_left }

lemma basic_open_mul_le_right (f g : A) : basic_open 𝒜 (f * g) ≤ basic_open 𝒜 g :=
by { rw basic_open_mul 𝒜 f g, exact inf_le_right }

@[simp] lemma basic_open_pow (f : A) (n : ℕ) (hn : 0 < n) :
  basic_open 𝒜 (f ^ n) = basic_open 𝒜 f :=
topological_space.opens.ext $ by simpa using zero_locus_singleton_pow 𝒜 f n hn

lemma is_topological_basis_basic_opens : topological_space.is_topological_basis
  (set.range (λ (r : A), (basic_open 𝒜 r : set (projective_spectrum 𝒜)))) :=
begin
  apply topological_space.is_topological_basis_of_open_of_nhds,
  { rintros _ ⟨r, rfl⟩,
    exact is_open_basic_open 𝒜 },
  { rintros p U hp ⟨s, hs⟩,
    rw [← compl_compl U, set.mem_compl_eq, ← hs, mem_zero_locus, set.not_subset] at hp,
    obtain ⟨f, hfs, hfp⟩ := hp,
    refine ⟨basic_open 𝒜 f, ⟨f, rfl⟩, hfp, _⟩,
    rw [← set.compl_subset_compl, ← hs, basic_open_eq_zero_locus_compl, compl_compl],
    exact zero_locus_anti_mono 𝒜 (set.singleton_subset_iff.mpr hfs) }
end

end basic_open

section order

/-!
## The specialization order

We endow `prime_spectrum R` with a partial order,
where `x ≤ y` if and only if `y ∈ closure {x}`.

TODO: maybe define sober topological spaces, and generalise this instance to those
-/

instance : partial_order (projective_spectrum 𝒜) :=
subtype.partial_order _

@[simp] lemma as_ideal_le_as_ideal (x y : projective_spectrum 𝒜) :
  x.as_homogeneous_ideal ≤ y.as_homogeneous_ideal ↔ x ≤ y :=
subtype.coe_le_coe

@[simp] lemma as_ideal_lt_as_ideal (x y : projective_spectrum 𝒜) :
  x.as_homogeneous_ideal < y.as_homogeneous_ideal ↔ x < y :=
subtype.coe_lt_coe

lemma le_iff_mem_closure (x y : projective_spectrum 𝒜) :
  x ≤ y ↔ y ∈ closure ({x} : set (projective_spectrum 𝒜)) :=
begin
  rw [← as_ideal_le_as_ideal, ← zero_locus_vanishing_ideal_eq_closure,
    mem_zero_locus, vanishing_ideal_singleton],
  simp only [coe_subset_coe, subtype.coe_le_coe, coe_coe],
end

end order

end projective_spectrum
