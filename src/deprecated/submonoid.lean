/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard
-/
import group_theory.submonoid.basic
import algebra.big_operators.basic

/-!
# Submonoids

This file defines unbundled multiplicative and additive submonoids (deprecated). For bundled form
see `group_theory/submonoid`.

We some results about images and preimages of submonoids under monoid homomorphisms. These theorems
use unbundled monoid homomorphisms (also deprecated).

There are also theorems about the submonoids generated by an element or a subset of a monoid,
defined inductively.

## Implementation notes

Unbundled submonoids will slowly be removed from mathlib.

## Tags
submonoid, submonoids, is_submonoid
-/

open_locale big_operators

variables {M : Type*} [monoid M] {s : set M}
variables {A : Type*} [add_monoid A] {t : set A}

/-- `s` is an additive submonoid: a set containing 0 and closed under addition. -/
class is_add_submonoid (s : set A) : Prop :=
(zero_mem : (0:A) ∈ s)
(add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s)

/-- `s` is a submonoid: a set containing 1 and closed under multiplication. -/
@[to_additive]
class is_submonoid (s : set M) : Prop :=
(one_mem : (1:M) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

lemma additive.is_add_submonoid
  (s : set M) : ∀ [is_submonoid s], @is_add_submonoid (additive M) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem additive.is_add_submonoid_iff
  {s : set M} : @is_add_submonoid (additive M) _ s ↔ is_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by exactI additive.is_add_submonoid _⟩

lemma multiplicative.is_submonoid
  (s : set A) : ∀ [is_add_submonoid s], @is_submonoid (multiplicative A) _ s
| ⟨h₁, h₂⟩ := ⟨h₁, @h₂⟩

theorem multiplicative.is_submonoid_iff
  {s : set A} : @is_submonoid (multiplicative A) _ s ↔ is_add_submonoid s :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, @h₂⟩, λ h, by exactI multiplicative.is_submonoid _⟩

/-- The intersection of two submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive "The intersection of two `add_submonoid`s of an `add_monoid` `M` is
an `add_submonoid` of M."]
instance is_submonoid.inter (s₁ s₂ : set M) [is_submonoid s₁] [is_submonoid s₂] :
  is_submonoid (s₁ ∩ s₂) :=
{ one_mem := ⟨is_submonoid.one_mem, is_submonoid.one_mem⟩,
  mul_mem := λ x y hx hy,
    ⟨is_submonoid.mul_mem hx.1 hy.1, is_submonoid.mul_mem hx.2 hy.2⟩ }

/-- The intersection of an indexed set of submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive "The intersection of an indexed set of `add_submonoid`s of an `add_monoid` `M` is
an `add_submonoid` of `M`."]
instance is_submonoid.Inter {ι : Sort*} (s : ι → set M) [h : ∀ y : ι, is_submonoid (s y)] :
  is_submonoid (set.Inter s) :=
{ one_mem := set.mem_Inter.2 $ λ y, is_submonoid.one_mem,
  mul_mem := λ x₁ x₂ h₁ h₂, set.mem_Inter.2 $
    λ y, is_submonoid.mul_mem (set.mem_Inter.1 h₁ y) (set.mem_Inter.1 h₂ y) }

/-- The union of an indexed, directed, nonempty set of submonoids of a monoid `M` is a submonoid
    of `M`. -/
@[to_additive "The union of an indexed, directed, nonempty set
of `add_submonoid`s of an `add_monoid` `M` is an `add_submonoid` of `M`. "]
lemma is_submonoid_Union_of_directed {ι : Type*} [hι : nonempty ι]
  (s : ι → set M) [∀ i, is_submonoid (s i)]
  (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
  is_submonoid (⋃i, s i) :=
{ one_mem := let ⟨i⟩ := hι in set.mem_Union.2 ⟨i, is_submonoid.one_mem⟩,
  mul_mem := λ a b ha hb,
    let ⟨i, hi⟩ := set.mem_Union.1 ha in
    let ⟨j, hj⟩ := set.mem_Union.1 hb in
    let ⟨k, hk⟩ := directed i j in
    set.mem_Union.2 ⟨k, is_submonoid.mul_mem (hk.1 hi) (hk.2 hj)⟩ }

section powers

/-- The set of natural number powers `1, x, x², ...` of an element `x` of a monoid. -/
def powers (x : M) : set M := {y | ∃ n:ℕ, x^n = y}
/-- The set of natural number multiples `0, x, 2x, ...` of an element `x` of an `add_monoid`. -/
def multiples (x : A) : set A := {y | ∃ n:ℕ, n • x = y}
attribute [to_additive multiples] powers

/-- 1 is in the set of natural number powers of an element of a monoid. -/
lemma powers.one_mem {x : M} : (1 : M) ∈ powers x := ⟨0, pow_zero _⟩

/-- 0 is in the set of natural number multiples of an element of an `add_monoid`. -/
lemma multiples.zero_mem {x : A} : (0 : A) ∈ multiples x := ⟨0, zero_nsmul _⟩
attribute [to_additive] powers.one_mem

/-- An element of a monoid is in the set of that element's natural number powers. -/
lemma powers.self_mem {x : M} : x ∈ powers x := ⟨1, pow_one _⟩

/-- An element of an `add_monoid` is in the set of that element's natural number multiples. -/
lemma multiples.self_mem {x : A} : x ∈ multiples x := ⟨1, one_nsmul _⟩
attribute [to_additive] powers.self_mem

/-- The set of natural number powers of an element of a monoid is closed under multiplication. -/
lemma powers.mul_mem {x y z : M} : (y ∈ powers x) → (z ∈ powers x) → (y * z ∈ powers x) :=
λ ⟨n₁, h₁⟩ ⟨n₂, h₂⟩, ⟨n₁ + n₂, by simp only [pow_add, *]⟩

/-- The set of natural number multiples of an element of an `add_monoid` is closed under
    addition. -/
lemma multiples.add_mem {x y z : A} :
  (y ∈ multiples x) → (z ∈ multiples x) → (y + z ∈ multiples x) :=
@powers.mul_mem (multiplicative A) _ _ _ _
attribute [to_additive] powers.mul_mem

/-- The set of natural number powers of an element of a monoid `M` is a submonoid of `M`. -/
@[to_additive "The set of natural number multiples of an element of
an `add_monoid` `M` is an `add_submonoid` of `M`."]
instance powers.is_submonoid (x : M) : is_submonoid (powers x) :=
{ one_mem := powers.one_mem,
  mul_mem := λ y z, powers.mul_mem }

/-- A monoid is a submonoid of itself. -/
@[to_additive "An `add_monoid` is an `add_submonoid` of itself."]
instance univ.is_submonoid : is_submonoid (@set.univ M) := by split; simp

/-- The preimage of a submonoid under a monoid hom is a submonoid of the domain. -/
@[to_additive "The preimage of an `add_submonoid` under an `add_monoid` hom is
an `add_submonoid` of the domain."]
instance preimage.is_submonoid {N : Type*} [monoid N] (f : M → N) [is_monoid_hom f]
  (s : set N) [is_submonoid s] : is_submonoid (f ⁻¹' s) :=
{ one_mem := show f 1 ∈ s, by rw is_monoid_hom.map_one f; exact is_submonoid.one_mem,
  mul_mem := λ a b (ha : f a ∈ s) (hb : f b ∈ s),
    show f (a * b) ∈ s, by rw is_monoid_hom.map_mul f; exact is_submonoid.mul_mem ha hb }

/-- The image of a submonoid under a monoid hom is a submonoid of the codomain. -/
@[instance, to_additive "The image of an `add_submonoid` under an `add_monoid`
hom is an `add_submonoid` of the codomain."]
lemma image.is_submonoid {γ : Type*} [monoid γ] (f : M → γ) [is_monoid_hom f]
  (s : set M) [is_submonoid s] : is_submonoid (f '' s) :=
{ one_mem := ⟨1, is_submonoid.one_mem, is_monoid_hom.map_one f⟩,
  mul_mem := λ a b ⟨x, hx⟩ ⟨y, hy⟩, ⟨x * y, is_submonoid.mul_mem hx.1 hy.1,
    by rw [is_monoid_hom.map_mul f, hx.2, hy.2]⟩ }

/-- The image of a monoid hom is a submonoid of the codomain. -/
@[to_additive "The image of an `add_monoid` hom is an `add_submonoid`
of the codomain."]
instance range.is_submonoid {γ : Type*} [monoid γ] (f : M → γ) [is_monoid_hom f] :
  is_submonoid (set.range f) :=
by rw ← set.image_univ; apply_instance

/-- Submonoids are closed under natural powers. -/
lemma is_submonoid.pow_mem {a : M} [is_submonoid s] (h : a ∈ s) : ∀ {n : ℕ}, a ^ n ∈ s
| 0 := by { rw pow_zero, exact is_submonoid.one_mem }
| (n + 1) := by { rw pow_succ, exact is_submonoid.mul_mem h is_submonoid.pow_mem }

/-- An `add_submonoid` is closed under multiplication by naturals. -/
lemma is_add_submonoid.smul_mem {a : A} [is_add_submonoid t] :
  ∀ (h : a ∈ t) {n : ℕ}, n • a ∈ t :=
@is_submonoid.pow_mem (multiplicative A) _ _ _ (multiplicative.is_submonoid _)
attribute [to_additive smul_mem] is_submonoid.pow_mem

/-- The set of natural number powers of an element of a submonoid is a subset of the submonoid. -/
lemma is_submonoid.power_subset {a : M} [is_submonoid s] (h : a ∈ s) : powers a ⊆ s :=
assume x ⟨n, hx⟩, hx ▸ is_submonoid.pow_mem h

/-- The set of natural number multiples of an element of an `add_submonoid` is a subset of the
    `add_submonoid`. -/
lemma is_add_submonoid.multiple_subset {a : A} [is_add_submonoid t] :
  a ∈ t → multiples a ⊆ t :=
@is_submonoid.power_subset (multiplicative A) _ _ _ (multiplicative.is_submonoid _)
attribute [to_additive multiple_subset] is_submonoid.power_subset

end powers

namespace is_submonoid

/-- The product of a list of elements of a submonoid is an element of the submonoid. -/
@[to_additive "The sum of a list of elements of an `add_submonoid` is an element of the
`add_submonoid`."]
lemma list_prod_mem [is_submonoid s] : ∀{l : list M}, (∀x∈l, x ∈ s) → l.prod ∈ s
| []     h := one_mem
| (a::l) h :=
  suffices a * l.prod ∈ s, by simpa,
  have a ∈ s ∧ (∀x∈l, x ∈ s), by simpa using h,
  is_submonoid.mul_mem this.1 (list_prod_mem this.2)

/-- The product of a multiset of elements of a submonoid of a `comm_monoid` is an element of
the submonoid. -/
@[to_additive "The sum of a multiset of elements of an `add_submonoid` of an `add_comm_monoid`
is an element of the `add_submonoid`. "]
lemma multiset_prod_mem {M} [comm_monoid M] (s : set M) [is_submonoid s] (m : multiset M) :
  (∀a∈m, a ∈ s) → m.prod ∈ s :=
begin
  refine quotient.induction_on m (assume l hl, _),
  rw [multiset.quot_mk_to_coe, multiset.coe_prod],
  exact list_prod_mem hl
end

/-- The product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is an element
of the submonoid. -/
@[to_additive "The sum of elements of an `add_submonoid` of an `add_comm_monoid` indexed by
a `finset` is an element of the `add_submonoid`."]
lemma finset_prod_mem {M A} [comm_monoid M] (s : set M) [is_submonoid s] (f : A → M) :
  ∀(t : finset A), (∀b∈t, f b ∈ s) → ∏ b in t, f b ∈ s
| ⟨m, hm⟩ hs := multiset_prod_mem s _ (by simpa)

end is_submonoid

-- TODO: modify `subtype_instance` to produce this definition, then use it here
--  and for `subtype.group`

/-- Submonoids are themselves monoids. -/
@[to_additive "An `add_submonoid` is itself an `add_monoid`."]
def subtype.monoid {s : set M} [is_submonoid s] : monoid s :=
{ one := ⟨1, is_submonoid.one_mem⟩,
  mul := λ x y, ⟨x * y, is_submonoid.mul_mem x.2 y.2⟩,
  mul_one := λ x, subtype.eq $ mul_one x.1,
  one_mul := λ x, subtype.eq $ one_mul x.1,
  mul_assoc := λ x y z, subtype.eq $ mul_assoc x.1 y.1 z.1 }

/-- Submonoids of commutative monoids are themselves commutative monoids. -/
@[to_additive "An `add_submonoid` of a commutative `add_monoid` is itself
a commutative `add_monoid`. "]
def subtype.comm_monoid {M} [comm_monoid M] {s : set M} [is_submonoid s] : comm_monoid s :=
{ mul_comm := λ x y, subtype.eq $ mul_comm x.1 y.1,
  .. subtype.monoid }

section
local attribute [instance] subtype.monoid subtype.add_monoid

/-- Submonoids inherit the 1 of the monoid. -/
@[simp, norm_cast, to_additive "An `add_submonoid` inherits the 0 of the `add_monoid`. "]
lemma is_submonoid.coe_one [is_submonoid s] : ((1 : s) : M) = 1 := rfl
attribute [norm_cast] is_add_submonoid.coe_zero

/-- Submonoids inherit the multiplication of the monoid. -/
@[simp, norm_cast, to_additive "An `add_submonoid` inherits the addition of the `add_monoid`. "]
lemma is_submonoid.coe_mul [is_submonoid s] (a b : s) : ((a * b : s) : M) = a * b := rfl
attribute [norm_cast] is_add_submonoid.coe_add

/-- Submonoids inherit the exponentiation by naturals of the monoid. -/
@[simp, norm_cast] lemma is_submonoid.coe_pow [is_submonoid s] (a : s) (n : ℕ) :
  ((a ^ n : s) : M) = a ^ n :=
by induction n; simp [*, pow_succ]

/-- An `add_submonoid` inherits the multiplication by naturals of the `add_monoid`. -/
@[simp, norm_cast] lemma is_add_submonoid.smul_coe {A : Type*} [add_monoid A] {s : set A}
  [is_add_submonoid s] (a : s) (n : ℕ) : ((n • a : s) : A) = n • a :=
by induction n; simp [*, succ_nsmul, zero_nsmul]

attribute [to_additive smul_coe] is_submonoid.coe_pow

/-- The natural injection from a submonoid into the monoid is a monoid hom. -/
@[to_additive "The natural injection from an `add_submonoid` into
the `add_monoid` is an `add_monoid` hom. "]
instance subtype_val.is_monoid_hom [is_submonoid s] : is_monoid_hom (subtype.val : s → M) :=
{ map_one := rfl, map_mul := λ _ _, rfl }

/-- The natural injection from a submonoid into the monoid is a monoid hom. -/
@[to_additive "The natural injection from an `add_submonoid` into
the `add_monoid` is an `add_monoid` hom. "]
instance coe.is_monoid_hom [is_submonoid s] : is_monoid_hom (coe : s → M) :=
subtype_val.is_monoid_hom

/-- Given a monoid hom `f : γ → M` whose image is contained in a submonoid `s`, the induced map
    from `γ` to `s` is a monoid hom. -/
@[to_additive "Given an `add_monoid` hom `f : γ → M` whose image is contained in
an `add_submonoid` s, the induced map from `γ` to `s` is an `add_monoid` hom."]
instance subtype_mk.is_monoid_hom {γ : Type*} [monoid γ] [is_submonoid s] (f : γ → M)
  [is_monoid_hom f] (h : ∀ x, f x ∈ s) : is_monoid_hom (λ x, (⟨f x, h x⟩ : s)) :=
{ map_one := subtype.eq (is_monoid_hom.map_one f),
  map_mul := λ x y, subtype.eq (is_monoid_hom.map_mul f x y) }

/-- Given two submonoids `s` and `t` such that `s ⊆ t`, the natural injection from `s` into `t` is
    a monoid hom. -/
@[to_additive "Given two `add_submonoid`s `s` and `t` such that `s ⊆ t`, the
natural injection from `s` into `t` is an `add_monoid` hom."]
instance set_inclusion.is_monoid_hom (t : set M) [is_submonoid s] [is_submonoid t] (h : s ⊆ t) :
  is_monoid_hom (set.inclusion h) :=
subtype_mk.is_monoid_hom _ _

end

namespace add_monoid

/-- The inductively defined membership predicate for the submonoid generated by a subset of a
    monoid. -/
inductive in_closure (s : set A) : A → Prop
| basic {a : A} : a ∈ s → in_closure a
| zero : in_closure 0
| add {a b : A} : in_closure a → in_closure b → in_closure (a + b)

end add_monoid

namespace monoid

/-- The inductively defined membership predicate for the `add_submonoid` generated by a subset of an
    add_monoid. -/
inductive in_closure (s : set M) : M → Prop
| basic {a : M} : a ∈ s → in_closure a
| one : in_closure 1
| mul {a b : M} : in_closure a → in_closure b → in_closure (a * b)

attribute [to_additive] monoid.in_closure
attribute [to_additive] monoid.in_closure.one
attribute [to_additive] monoid.in_closure.mul

/-- The inductively defined submonoid generated by a subset of a monoid. -/
@[to_additive "The inductively defined `add_submonoid` genrated by a subset of an `add_monoid`."]
def closure (s : set M) : set M := {a | in_closure s a }

@[to_additive]
instance closure.is_submonoid (s : set M) : is_submonoid (closure s) :=
{ one_mem := in_closure.one, mul_mem := assume a b, in_closure.mul }

/-- A subset of a monoid is contained in the submonoid it generates. -/
@[to_additive "A subset of an `add_monoid` is contained in the `add_submonoid` it generates."]
theorem subset_closure {s : set M} : s ⊆ closure s :=
assume a, in_closure.basic

/-- The submonoid generated by a set is contained in any submonoid that contains the set. -/
@[to_additive "The `add_submonoid` generated by a set is contained in any `add_submonoid` that
contains the set."]
theorem closure_subset {s t : set M} [is_submonoid t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, is_submonoid.one_mem, is_submonoid.mul_mem]

/-- Given subsets `t` and `s` of a monoid `M`, if `s ⊆ t`, the submonoid of `M` generated by `s` is
    contained in the submonoid generated by `t`. -/
@[to_additive "Given subsets `t` and `s` of an `add_monoid M`, if `s ⊆ t`, the `add_submonoid`
of `M` generated by `s` is contained in the `add_submonoid` generated by `t`."]
theorem closure_mono {s t : set M} (h : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans h subset_closure

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
@[to_additive "The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element."]
theorem closure_singleton {x : M} : closure ({x} : set M) = powers x :=
set.eq_of_subset_of_subset (closure_subset $ set.singleton_subset_iff.2 $ powers.self_mem) $
  is_submonoid.power_subset $ set.singleton_subset_iff.1 $ subset_closure

/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set under the monoid hom. -/
@[to_additive "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals
the `add_submonoid` generated by the image of the set under the `add_monoid` hom."]
lemma image_closure {A : Type*} [monoid A] (f : M → A) [is_monoid_hom f] (s : set M) :
  f '' closure s = closure (f '' s) :=
le_antisymm
  begin
    rintros _ ⟨x, hx, rfl⟩,
    apply in_closure.rec_on hx; intros,
    { solve_by_elim [subset_closure, set.mem_image_of_mem] },
    { rw [is_monoid_hom.map_one f], apply is_submonoid.one_mem },
    { rw [is_monoid_hom.map_mul f], solve_by_elim [is_submonoid.mul_mem] }
  end
  (closure_subset $ set.image_subset _ subset_closure)

/-- Given an element `a` of the submonoid of a monoid `M` generated by a set `s`, there exists
a list of elements of `s` whose product is `a`. -/
@[to_additive "Given an element `a` of the `add_submonoid` of an `add_monoid M` generated by
a set `s`, there exists a list of elements of `s` whose sum is `a`."]
theorem exists_list_of_mem_closure {s : set M} {a : M} (h : a ∈ closure s) :
  (∃l:list M, (∀x∈l, x ∈ s) ∧ l.prod = a) :=
begin
  induction h,
  case in_closure.basic : a ha { existsi ([a]), simp [ha] },
  case in_closure.one { existsi ([]), simp },
  case in_closure.mul : a b _ _ ha hb {
    rcases ha with ⟨la, ha, eqa⟩,
    rcases hb with ⟨lb, hb, eqb⟩,
    existsi (la ++ lb),
    simp [eqa.symm, eqb.symm, or_imp_distrib],
    exact assume a, ⟨ha a, hb a⟩
  }
end

/-- Given sets `s, t` of a commutative monoid `M`, `x ∈ M` is in the submonoid of `M` generated by
    `s ∪ t` iff there exists an element of the submonoid generated by `s` and an element of the
    submonoid generated by `t` whose product is `x`. -/
@[to_additive "Given sets `s, t` of a commutative `add_monoid M`, `x ∈ M` is in the `add_submonoid`
of `M` generated by `s ∪ t` iff there exists an element of the `add_submonoid` generated by `s`
and an element of the `add_submonoid` generated by `t` whose sum is `x`."]
theorem mem_closure_union_iff {M : Type*} [comm_monoid M] {s t : set M} {x : M} :
  x ∈ closure (s ∪ t) ↔ ∃ y ∈ closure s, ∃ z ∈ closure t, y * z = x :=
⟨λ hx, let ⟨L, HL1, HL2⟩ := exists_list_of_mem_closure hx in HL2 ▸
  list.rec_on L (λ _, ⟨1, is_submonoid.one_mem, 1, is_submonoid.one_mem, mul_one _⟩)
    (λ hd tl ih HL1, let ⟨y, hy, z, hz, hyzx⟩ := ih (list.forall_mem_of_forall_mem_cons HL1) in
      or.cases_on (HL1 hd $ list.mem_cons_self _ _)
        (λ hs, ⟨hd * y, is_submonoid.mul_mem (subset_closure hs) hy, z, hz,
          by rw [mul_assoc, list.prod_cons, ← hyzx]; refl⟩)
        (λ ht, ⟨y, hy, z * hd, is_submonoid.mul_mem hz (subset_closure ht),
          by rw [← mul_assoc, list.prod_cons, ← hyzx, mul_comm hd]; refl⟩)) HL1,
λ ⟨y, hy, z, hz, hyzx⟩, hyzx ▸ is_submonoid.mul_mem (closure_mono (set.subset_union_left _ _) hy)
  (closure_mono (set.subset_union_right _ _) hz)⟩

end monoid

/-- Create a bundled submonoid from a set `s` and `[is_submonoid s]`. -/
@[to_additive "Create a bundled additive submonoid from a set `s` and `[is_add_submonoid s]`."]
def submonoid.of (s : set M) [h : is_submonoid s] : submonoid M := ⟨s, h.1, h.2⟩

@[to_additive]
instance submonoid.is_submonoid (S : submonoid M) : is_submonoid (S : set M) := ⟨S.2, S.3⟩
