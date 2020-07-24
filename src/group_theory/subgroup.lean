/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import group_theory.submonoid

/-!
# Subgroups

This file defines multiplicative and additive subgroups as an extension of submonoids, in a bundled
form (unbundled subgroups are in `deprecated/subgroups.lean`).

We prove subgroups of a group form a complete lattice, and results about images and preimages of
subgroups under group homomorphisms. The bundled subgroups use bundled monoid homomorphisms.

There are also theorems about the subgroups generated by an element or a subset of a group,
defined both inductively and as the infimum of the set of subgroups containing a given
element/subset.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are groups

- `A` is an add_group

- `H K` are subgroups of `G` or add_subgroups of `A`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `subgroup G` : the type of subgroups of a group `G`

* `add_subgroup A` : the type of subgroups of an additive group `A`

* `complete_lattice (subgroup G)` : the subgroups of `G` form a complete lattice

* `closure k` : the minimal subgroup that includes the set `k`

* `subtype` : the natural group homomorphism from a subgroup of group `G` to `G`

* `gi` : `closure` forms a Galois insertion with the coercion to set

* `comap H f` : the preimage of a subgroup `H` along the group homomorphism `f` is also a subgroup

* `map f H` : the image of a subgroup `H` along the group homomorphism `f` is also a subgroup

* `prod H K` : the product of subgroups `H`, `K` of groups `G`, `N` respectively, `H × K` is a
subgroup of `G × N`

* `monoid_hom.range f` : the range of the group homomorphism `f` is a subgroup

* `monoid_hom.ker f` : the kernel of a group homomorphism `f` is the subgroup of elements `x : G` such that
`f x = 1`

* `monoid_hom.eq_locus f g` : given group homomorphisms `f`, `g`, the elements of `G` such that `f x = g x`
form a subgroup of `G`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

open_locale big_operators

variables {G : Type*} [group G]
variables {A : Type*} [add_group A]

set_option old_structure_cmd true

/-- A subgroup of a group `G` is a subset containing 1, closed under multiplication
and closed under multiplicative inverse. -/
structure subgroup (G : Type*) [group G] extends submonoid G :=
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

/-- An additive subgroup of an additive group `G` is a subset containing 0, closed
under addition and additive inverse. -/
structure add_subgroup (G : Type*) [add_group G] extends add_submonoid G:=
(neg_mem' {x} : x ∈ carrier → -x ∈ carrier)

attribute [to_additive add_subgroup] subgroup
attribute [to_additive add_subgroup.to_add_submonoid] subgroup.to_submonoid

/-- Reinterpret a `subgroup` as a `submonoid`. -/
add_decl_doc subgroup.to_submonoid

/-- Reinterpret an `add_subgroup` as an `add_submonoid`. -/
add_decl_doc add_subgroup.to_add_submonoid

/-- Map from subgroups of group `G` to `add_subgroup`s of `additive G`. -/
def subgroup.to_add_subgroup {G : Type*} [group G] (H : subgroup G) :
  add_subgroup (additive G) :=
{ neg_mem' := H.inv_mem',
  .. submonoid.to_add_submonoid H.to_submonoid}

/-- Map from `add_subgroup`s of `additive G` to subgroups of `G`. -/
def subgroup.of_add_subgroup {G : Type*} [group G] (H : add_subgroup (additive G)) :
  subgroup G :=
{ inv_mem' := H.neg_mem',
  .. submonoid.of_add_submonoid H.to_add_submonoid}

/-- Map from `add_subgroup`s of `add_group G` to subgroups of `multiplicative G`. -/
def add_subgroup.to_subgroup {G : Type*} [add_group G] (H : add_subgroup G) :
  subgroup (multiplicative G) :=
{ inv_mem' := H.neg_mem',
  .. add_submonoid.to_submonoid H.to_add_submonoid}

/-- Map from subgroups of `multiplicative G` to `add_subgroup`s of `add_group G`. -/
def add_subgroup.of_subgroup {G : Type*} [add_group G] (H : subgroup (multiplicative G)) :
  add_subgroup G :=
{ neg_mem' := H.inv_mem',
  .. add_submonoid.of_submonoid H.to_submonoid }

/-- Subgroups of group `G` are isomorphic to additive subgroups of `additive G`. -/
def subgroup.add_subgroup_equiv (G : Type*) [group G] :
subgroup G ≃ add_subgroup (additive G) :=
{ to_fun := subgroup.to_add_subgroup,
  inv_fun := subgroup.of_add_subgroup,
  left_inv := λ x, by cases x; refl,
  right_inv := λ x, by cases x; refl }

namespace subgroup

@[to_additive]
instance : has_coe (subgroup G) (set G) := { coe := subgroup.carrier }

@[simp, to_additive]
lemma coe_to_submonoid (K : subgroup G) : (K.to_submonoid : set G) = K := rfl

@[to_additive]
instance : has_mem G (subgroup G) := ⟨λ m K, m ∈ (K : set G)⟩

@[to_additive]
instance : has_coe_to_sort (subgroup G) := ⟨_, λ G, (G : Type*)⟩

@[simp, norm_cast, to_additive]
lemma mem_coe {K : subgroup G} {g : G} : g ∈ (K : set G) ↔ g ∈ K := iff.rfl

@[simp, norm_cast, to_additive]
lemma coe_coe (K : subgroup G) : ↥(K : set G) = K := rfl

attribute [norm_cast] add_subgroup.mem_coe
attribute [norm_cast] add_subgroup.coe_coe

end subgroup

@[to_additive]
protected lemma subgroup.exists {K : subgroup G} {p : K → Prop} :
  (∃ x : K, p x) ↔ ∃ x ∈ K, p ⟨x, ‹x ∈ K›⟩ :=
set_coe.exists

@[to_additive]
protected lemma subgroup.forall {K : subgroup G} {p : K → Prop} :
  (∀ x : K, p x) ↔ ∀ x ∈ K, p ⟨x, ‹x ∈ K›⟩ :=
set_coe.forall

namespace subgroup

variables (H K : subgroup G)

/-- Copy of a subgroup with a new `carrier` equal to the old one. Useful to fix definitional
equalities.-/
@[to_additive "Copy of an additive subgroup with a new `carrier` equal to the old one.
Useful to fix definitional equalities"]
protected def copy (K : subgroup G) (s : set G) (hs : s = K) : subgroup G :=
{ carrier := s,
  one_mem' := hs.symm ▸ K.one_mem',
  mul_mem' := hs.symm ▸ K.mul_mem',
  inv_mem' := hs.symm ▸ K.inv_mem' }

/- Two subgroups are equal if the underlying set are the same. -/
@[to_additive "Two `add_group`s are equal if the underlying subsets are equal."]
theorem ext' {H K : subgroup G} (h : (H : set G) = K) : H = K :=
by { cases H, cases K, congr, exact h }

/- Two subgroups are equal if and only if the underlying subsets are equal. -/
@[to_additive "Two `add_subgroup`s are equal if and only if the underlying subsets are equal."]
protected theorem ext'_iff {H K : subgroup G} :
  H = K ↔ (H : set G) = K := ⟨λ h, h ▸ rfl, ext'⟩

/-- Two subgroups are equal if they have the same elements. -/
@[ext, to_additive "Two `add_subgroup`s are equal if they have the same elements."]
theorem ext {H K : subgroup G}
  (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := ext' $ set.ext h

attribute [ext] add_subgroup.ext

/-- A subgroup contains the group's 1. -/
@[to_additive "An `add_subgroup` contains the group's 0."]
theorem one_mem : (1 : G) ∈ H := H.one_mem'

/-- A subgroup is closed under multiplication. -/
@[to_additive "An `add_subgroup` is closed under addition."]
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := λ hx hy, H.mul_mem' hx hy

/-- A subgroup is closed under inverse. -/
@[to_additive "An `add_subgroup` is closed under inverse."]
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := λ hx, H.inv_mem' hx

@[simp, to_additive] theorem inv_mem_iff {x : G} : x⁻¹ ∈ H ↔ x ∈ H :=
⟨λ h, inv_inv x ▸ H.inv_mem h, H.inv_mem⟩

@[to_additive]
lemma mul_mem_cancel_right {x y : G} (h : x ∈ H) : y * x ∈ H ↔ y ∈ H :=
⟨λ hba, by simpa using H.mul_mem hba (H.inv_mem h), λ hb, H.mul_mem hb h⟩

@[to_additive]
lemma mul_mem_cancel_left {x y : G} (h : x ∈ H) : x * y ∈ H ↔ y ∈ H :=
⟨λ hab, by simpa using H.mul_mem (H.inv_mem h) hab, H.mul_mem h⟩

/-- Product of a list of elements in a subgroup is in the subgroup. -/
@[to_additive "Sum of a list of elements in an `add_subgroup` is in the `add_subgroup`."]
lemma list_prod_mem {l : list G} : (∀ x ∈ l, x ∈ K) → l.prod ∈ K :=
K.to_submonoid.list_prod_mem

/-- Product of a multiset of elements in a subgroup of a `comm_group` is in the subgroup. -/
@[to_additive "Sum of a multiset of elements in an `add_subgroup` of an `add_comm_group`
is in the `add_subgroup`."]
lemma multiset_prod_mem {G} [comm_group G] (K : subgroup G) (g : multiset G) :
  (∀ a ∈ g, a ∈ K) → g.prod ∈ K := K.to_submonoid.multiset_prod_mem g

/-- Product of elements of a subgroup of a `comm_group` indexed by a `finset` is in the
    subgroup. -/
@[to_additive "Sum of elements in an `add_subgroup` of an `add_comm_group` indexed by a `finset`
is in the `add_subgroup`."]
lemma prod_mem {G : Type*} [comm_group G] (K : subgroup G)
  {ι : Type*} {t : finset ι} {f : ι → G} (h : ∀ c ∈ t, f c ∈ K) :
  ∏ c in t, f c ∈ K :=
K.to_submonoid.prod_mem h

lemma pow_mem {x : G} (hx : x ∈ K) : ∀ n : ℕ, x ^ n ∈ K := K.to_submonoid.pow_mem hx

lemma gpow_mem {x : G} (hx : x ∈ K) : ∀ n : ℤ, x ^ n ∈ K
| (int.of_nat n) := pow_mem _ hx n
| -[1+ n]        := K.inv_mem $ K.pow_mem hx n.succ

/-- Construct a subgroup from a nonempty set that is closed under division. -/
@[to_additive "Construct a subgroup from a nonempty set that is closed under subtraction"]
def of_div (s : set G) (hsn : s.nonempty) (hs : ∀ x y ∈ s, x * y⁻¹ ∈ s) : subgroup G :=
have one_mem : (1 : G) ∈ s, from let ⟨x, hx⟩ := hsn in by simpa using hs x x hx hx,
have inv_mem : ∀ x, x ∈ s → x⁻¹ ∈ s, from λ x hx, by simpa using hs 1 x one_mem hx,
{ carrier := s,
  one_mem' := one_mem,
  inv_mem' := inv_mem,
  mul_mem' := λ x y hx hy, by simpa using hs x y⁻¹ hx (inv_mem y hy) }

/-- A subgroup of a group inherits a multiplication. -/
@[to_additive "An `add_subgroup` of an `add_group` inherits an addition."]
instance has_mul : has_mul H := H.to_submonoid.has_mul

/-- A subgroup of a group inherits a 1. -/
@[to_additive "An `add_subgroup` of an `add_group` inherits a zero."]
instance has_one : has_one H := H.to_submonoid.has_one

/-- A subgroup of a group inherits an inverse. -/
@[to_additive "A `add_subgroup` of a `add_group` inherits an inverse."]
instance has_inv : has_inv H := ⟨λ a, ⟨a⁻¹, H.inv_mem a.2⟩⟩

@[simp, norm_cast, to_additive] lemma coe_mul (x y : H) : (↑(x * y) : G) = ↑x * ↑y := rfl
@[simp, norm_cast, to_additive] lemma coe_one : ((1 : H) : G) = 1 := rfl
@[simp, norm_cast, to_additive] lemma coe_inv (x : H) : ↑(x⁻¹ : H) = (x⁻¹ : G) := rfl
@[simp, norm_cast, to_additive] lemma coe_mk (x : G) (hx : x ∈ H) : ((⟨x, hx⟩ : H) : G) = x := rfl

attribute [norm_cast] add_subgroup.coe_add add_subgroup.coe_zero
  add_subgroup.coe_neg add_subgroup.coe_mk

/-- A subgroup of a group inherits a group structure. -/
@[to_additive to_add_group "An `add_subgroup` of an `add_group` inherits an `add_group` structure."]
instance to_group {G : Type*} [group G] (H : subgroup G) : group H :=
{ inv := has_inv.inv,
  mul_left_inv := λ x, subtype.eq $ mul_left_inv x,
  .. H.to_submonoid.to_monoid }

/-- A subgroup of a `comm_group` is a `comm_group`. -/
@[to_additive to_add_comm_group "An `add_subgroup` of an `add_comm_group` is an `add_comm_group`."]
instance to_comm_group {G : Type*} [comm_group G] (H : subgroup G) : comm_group H :=
{ mul_comm := λ _ _, subtype.eq $ mul_comm _ _, .. H.to_group}

/-- The natural group hom from a subgroup of group `G` to `G`. -/
@[to_additive "The natural group hom from an `add_subgroup` of `add_group` `G` to `G`."]
def subtype : H →* G := ⟨coe, rfl, λ _ _, rfl⟩

@[simp, to_additive] theorem coe_subtype : ⇑H.subtype = coe := rfl

@[simp, norm_cast] lemma coe_pow (x : H) (n : ℕ) : ((x ^ n : H) : G) = x ^ n :=
coe_subtype H ▸ monoid_hom.map_pow _ _ _
@[simp, norm_cast] lemma coe_gpow (x : H) (n : ℤ) : ((x ^ n : H) : G) = x ^ n :=
coe_subtype H ▸ monoid_hom.map_gpow _ _ _

@[to_additive]
instance : has_le (subgroup G) := ⟨λ H K, ∀ ⦃x⦄, x ∈ H → x ∈ K⟩

@[to_additive]
lemma le_def {H K : subgroup G} : H ≤ K ↔ ∀ ⦃x : G⦄, x ∈ H → x ∈ K := iff.rfl

@[simp, to_additive]
lemma coe_subset_coe {H K : subgroup G} : (H : set G) ⊆ K ↔ H ≤ K := iff.rfl

@[to_additive]
instance : partial_order (subgroup G) :=
{ le := (≤),
  .. partial_order.lift (coe : subgroup G → set G) (λ a b, ext') }

/-- The subgroup `G` of the group `G`. -/
@[to_additive "The `add_subgroup G` of the `add_group G`."]
instance : has_top (subgroup G) :=
⟨{ inv_mem' := λ _ _, set.mem_univ _ , .. (⊤ : submonoid G) }⟩

/-- The trivial subgroup `{1}` of an group `G`. -/
@[to_additive "The trivial `add_subgroup` `{0}` of an `add_group` `G`."]
instance : has_bot (subgroup G) :=
⟨{ inv_mem' := λ _, by simp *, .. (⊥ : submonoid G) }⟩

@[to_additive]
instance : inhabited (subgroup G) := ⟨⊥⟩

@[simp, to_additive] lemma mem_bot {x : G} : x ∈ (⊥ : subgroup G) ↔ x = 1 := iff.rfl

@[simp, to_additive] lemma mem_top (x : G) : x ∈ (⊤ : subgroup G) := set.mem_univ x

@[simp, to_additive] lemma coe_top : ((⊤ : subgroup G) : set G) = set.univ := rfl

@[simp, to_additive] lemma coe_bot : ((⊥ : subgroup G) : set G) = {1} := rfl

/-- The inf of two subgroups is their intersection. -/
@[to_additive "The inf of two `add_subgroups`s is their intersection."]
instance : has_inf (subgroup G) :=
⟨λ H₁ H₂,
  { inv_mem' := λ _ ⟨hx, hx'⟩, ⟨H₁.inv_mem hx, H₂.inv_mem hx'⟩,
    .. H₁.to_submonoid ⊓ H₂.to_submonoid }⟩

@[simp, to_additive]
lemma coe_inf (p p' : subgroup G) : ((p ⊓ p' : subgroup G) : set G) = p ∩ p' := rfl

@[simp, to_additive]
lemma mem_inf {p p' : subgroup G} {x : G} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

@[to_additive]
instance : has_Inf (subgroup G) :=
⟨λ s,
  { inv_mem' := λ x hx, set.mem_bInter $ λ i h, i.inv_mem (by apply set.mem_bInter_iff.1 hx i h),
    .. (⨅ S ∈ s, subgroup.to_submonoid S).copy (⋂ S ∈ s, ↑S) (by simp) }⟩

@[simp, to_additive]
lemma coe_Inf (H : set (subgroup G)) : ((Inf H : subgroup G) : set G) = ⋂ s ∈ H, ↑s := rfl

attribute [norm_cast] coe_Inf add_subgroup.coe_Inf

@[simp, to_additive]
lemma mem_Inf {S : set (subgroup G)} {x : G} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_bInter_iff

/-- Subgroups of a group form a complete lattice. -/
@[to_additive "The `add_subgroup`s of an `add_group` form a complete lattice."]
instance : complete_lattice (subgroup G) :=
{ bot          := (⊥),
  bot_le       := λ S x hx, (mem_bot.1 hx).symm ▸ S.one_mem,
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (subgroup G) $ λ s, is_glb.of_image
    (λ H K, show (H : set G) ≤ K ↔ H ≤ K, from coe_subset_coe) is_glb_binfi }

/-- The `subgroup` generated by a set. -/
@[to_additive "The `add_subgroup` generated by a set"]
def closure (k : set G) : subgroup G := Inf {K | k ⊆ K}

variable {k : set G}

@[to_additive]
lemma mem_closure {x : G} : x ∈ closure k ↔ ∀ K : subgroup G, k ⊆ K → x ∈ K :=
mem_Inf

/-- The subgroup generated by a set includes the set. -/
@[simp, to_additive "The `add_subgroup` generated by a set includes the set."]
lemma subset_closure : k ⊆ closure k := λ x hx, mem_closure.2 $ λ K hK, hK hx

open set

/-- A subgroup `K` includes `closure k` if and only if it includes `k`. -/
@[simp, to_additive "An additive subgroup `K` includes `closure k` if and only if it includes `k`"]
lemma closure_le : closure k ≤ K ↔ k ⊆ K :=
⟨subset.trans subset_closure, λ h, Inf_le h⟩

@[to_additive]
lemma closure_eq_of_le (h₁ : k ⊆ K) (h₂ : K ≤ closure k) : closure k = K :=
le_antisymm ((closure_le $ K).2 h₁) h₂

/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `k`, and
is preserved under multiplication and inverse, then `p` holds for all elements of the closure
of `k`. -/
@[to_additive "An induction principle for additive closure membership. If `p` holds for `0` and all
elements of `k`, and is preserved under addition and isvers, then `p` holds for all elements
of the additive closure of `k`."]
lemma closure_induction {p : G → Prop} {x} (h : x ∈ closure k)
  (Hk : ∀ x ∈ k, p x) (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y))
  (Hinv : ∀ x, p x → p x⁻¹) : p x :=
(@closure_le _ _ ⟨p, H1, Hmul, Hinv⟩ _).2 Hk h

attribute [elab_as_eliminator] subgroup.closure_induction add_subgroup.closure_induction

variable (G)

/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : galois_insertion (@closure G _) coe :=
{ choice := λ s _, closure s,
  gc := λ s t, @closure_le _ _ t s,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variable {G}

/-- Subgroup closure of a set is monotone in its argument: if `h ⊆ k`,
then `closure h ≤ closure k`. -/
@[to_additive "Additive subgroup closure of a set is monotone in its argument: if `h ⊆ k`,
then `closure h ≤ closure k`"]
lemma closure_mono ⦃h k : set G⦄ (h' : h ⊆ k) : closure h ≤ closure k :=
(subgroup.gi G).gc.monotone_l h'

/-- Closure of a subgroup `K` equals `K`. -/
@[simp, to_additive "Additive closure of an additive subgroup `K` equals `K`"]
lemma closure_eq : closure (K : set G) = K := (subgroup.gi G).l_u_eq K

@[simp, to_additive] lemma closure_empty : closure (∅ : set G) = ⊥ :=
(subgroup.gi G).gc.l_bot

@[simp, to_additive] lemma closure_univ : closure (univ : set G) = ⊤ :=
@coe_top G _ ▸ closure_eq ⊤

@[to_additive]
lemma closure_union (s t : set G) : closure (s ∪ t) = closure s ⊔ closure t :=
(subgroup.gi G).gc.l_sup

@[to_additive]
lemma closure_Union {ι} (s : ι → set G) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
(subgroup.gi G).gc.l_supr

/-- The subgroup generated by an element of a group equals the set of integer number powers of
    the element. -/
lemma mem_closure_singleton {x y : G} : y ∈ closure ({x} : set G) ↔ ∃ n : ℤ, x ^ n = y :=
begin
  refine ⟨λ hy, closure_induction hy _ _ _ _,
    λ ⟨n, hn⟩, hn ▸ gpow_mem _ (subset_closure $ mem_singleton x) n⟩,
  { intros y hy,
    rw [eq_of_mem_singleton hy],
    exact ⟨1, gpow_one x⟩ },
  { exact ⟨0, rfl⟩ },
  { rintros _ _ ⟨n, rfl⟩ ⟨m, rfl⟩,
    exact ⟨n + m, gpow_add x n m⟩ },
    rintros _ ⟨n, rfl⟩,
    exact ⟨-n, gpow_neg x n⟩
end

@[to_additive]
lemma mem_supr_of_directed {ι} [hι : nonempty ι] {K : ι → subgroup G} (hK : directed (≤) K)
  {x : G} :
  x ∈ (supr K : subgroup G) ↔ ∃ i, x ∈ K i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (le_def.1 $ le_supr K i) hi⟩,
  suffices : x ∈ closure (⋃ i, (K i : set G)) → ∃ i, x ∈ K i,
    by simpa only [closure_Union, closure_eq (K _)] using this,
  refine (λ hx, closure_induction hx (λ _, mem_Union.1) _ _ _),
  { exact hι.elim (λ i, ⟨i, (K i).one_mem⟩) },
  { rintros x y ⟨i, hi⟩ ⟨j, hj⟩,
    rcases hK i j with ⟨k, hki, hkj⟩,
    exact ⟨k, (K k).mul_mem (hki hi) (hkj hj)⟩ },
    rintros _ ⟨i, hi⟩, exact ⟨i, inv_mem (K i) hi⟩
end

@[to_additive]
lemma mem_Sup_of_directed_on {K : set (subgroup G)} (Kne : K.nonempty)
  (hK : directed_on (≤) K) {x : G} :
  x ∈ Sup K ↔ ∃ s ∈ K, x ∈ s :=
begin
  haveI : nonempty K := Kne.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed hK.directed_coe, set_coe.exists, subtype.coe_mk]
end

variables {N : Type*} [group N] {P : Type*} [group P]

/-- The preimage of a subgroup along a monoid homomorphism is a subgroup. -/
@[to_additive "The preimage of an `add_subgroup` along an `add_monoid` homomorphism
is an `add_subgroup`."]
def comap {N : Type*} [group N] (f : G →* N)
  (H : subgroup N) : subgroup G :=
{ carrier := (f ⁻¹' H),
  inv_mem' := λ a ha,
    show f a⁻¹ ∈ H, by rw f.map_inv; exact H.inv_mem ha,
  .. H.to_submonoid.comap f }

@[simp, to_additive]
lemma coe_comap (K : subgroup N) (f : G →* N) : (K.comap f : set G) = f ⁻¹' K := rfl

@[simp, to_additive]
lemma mem_comap {K : subgroup N} {f : G →* N} {x : G} : x ∈ K.comap f ↔ f x ∈ K := iff.rfl

@[to_additive]
lemma comap_comap (K : subgroup P) (g : N →* P) (f : G →* N) :
  (K.comap g).comap f = K.comap (g.comp f) :=
rfl

/-- The image of a subgroup along a monoid homomorphism is a subgroup. -/
@[to_additive "The image of an `add_subgroup` along an `add_monoid` homomorphism
is an `add_subgroup`."]
def map (f : G →* N) (H : subgroup G) : subgroup N :=
{ carrier := (f '' H),
  inv_mem' := by { rintros _ ⟨x, hx, rfl⟩, exact ⟨x⁻¹, H.inv_mem hx, f.map_inv x⟩ },
  .. H.to_submonoid.map f }

@[simp, to_additive]
lemma coe_map (f : G →* N) (K : subgroup G) :
  (K.map f : set N) = f '' K := rfl

@[simp, to_additive]
lemma mem_map {f : G →* N} {K : subgroup G} {y : N} :
  y ∈ K.map f ↔ ∃ x ∈ K, f x = y :=
mem_image_iff_bex

@[to_additive]
lemma map_map (g : N →* P) (f : G →* N) : (K.map f).map g = K.map (g.comp f) :=
ext' $ image_image _ _ _

@[to_additive]
lemma map_le_iff_le_comap {f : G →* N} {K : subgroup G} {H : subgroup N} :
  K.map f ≤ H ↔ K ≤ H.comap f :=
image_subset_iff

@[to_additive]
lemma gc_map_comap (f : G →* N) : galois_connection (map f) (comap f) :=
λ _ _, map_le_iff_le_comap

@[to_additive]
lemma map_sup (H K : subgroup G) (f : G →* N) : (H ⊔ K).map f = H.map f ⊔ K.map f :=
(gc_map_comap f).l_sup

@[to_additive]
lemma map_supr {ι : Sort*} (f : G →* N) (s : ι → subgroup G) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

@[to_additive]
lemma comap_inf (H K : subgroup N) (f : G →* N) : (H ⊓ K).comap f = H.comap f ⊓ K.comap f :=
(gc_map_comap f).u_inf

@[to_additive]
lemma comap_infi {ι : Sort*} (f : G →* N) (s : ι → subgroup N) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp, to_additive] lemma map_bot (f : G →* N) : (⊥ : subgroup G).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp, to_additive] lemma comap_top (f : G →* N) : (⊤ : subgroup N).comap f = ⊤ :=
(gc_map_comap f).u_top

/-- Given `subgroup`s `H`, `K` of groups `G`, `N` respectively, `H × K` as a subgroup of `G × N`. -/
@[to_additive prod "Given `add_subgroup`s `H`, `K` of `add_group`s `A`, `B` respectively, `H × K`
as an `add_subgroup` of `A × B`."]
def prod (H : subgroup G) (K : subgroup N) : subgroup (G × N) :=
{ inv_mem' := λ _ hx, ⟨H.inv_mem' hx.1, K.inv_mem' hx.2⟩,
  .. submonoid.prod H.to_submonoid K.to_submonoid}

@[to_additive coe_prod]
lemma coe_prod (H : subgroup G) (K : subgroup N) :
 (H.prod K : set (G × N)) = (H : set G).prod (K : set N) := rfl

@[to_additive mem_prod]
lemma mem_prod {H : subgroup G} {K : subgroup N} {p : G × N} :
  p ∈ H.prod K ↔ p.1 ∈ H ∧ p.2 ∈ K := iff.rfl

@[to_additive prod_mono]
lemma prod_mono : ((≤) ⇒ (≤) ⇒ (≤)) (@prod G _ N _) (@prod G _ N _) :=
λ s s' hs t t' ht, set.prod_mono hs ht

@[to_additive prod_mono_right]
lemma prod_mono_right (K : subgroup G) : monotone (λ t : subgroup N, K.prod t) :=
prod_mono (le_refl K)

@[to_additive prod_mono_left]
lemma prod_mono_left (H : subgroup N) : monotone (λ K : subgroup G, K.prod H) :=
λ s₁ s₂ hs, prod_mono hs (le_refl H)

@[to_additive prod_top]
lemma prod_top (K : subgroup G) :
  K.prod (⊤ : subgroup N) = K.comap (monoid_hom.fst G N) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_fst]

@[to_additive top_prod]
lemma top_prod (H : subgroup N) :
  (⊤ : subgroup G).prod H = H.comap (monoid_hom.snd G N) :=
ext $ λ x, by simp [mem_prod, monoid_hom.coe_snd]

@[simp, to_additive top_prod_top]
lemma top_prod_top : (⊤ : subgroup G).prod (⊤ : subgroup N) = ⊤ :=
(top_prod _).trans $ comap_top _

@[to_additive] lemma bot_prod_bot : (⊥ : subgroup G).prod (⊥ : subgroup N) = ⊥ :=
ext' $ by simp [coe_prod, prod.one_eq_mk]

/-- Product of subgroups is isomorphic to their product as groups. -/
@[to_additive prod_equiv "Product of additive subgroups is isomorphic to their product
as additive groups"]
def prod_equiv (H : subgroup G) (K : subgroup N) : H.prod K ≃* H × K :=
{ map_mul' := λ x y, rfl, .. equiv.set.prod ↑H ↑K }

/-- A subgroup is normal if whenever `n ∈ H`, then `g * n * g⁻¹ ∈ H` for every `g : G` -/
structure normal : Prop :=
(conj_mem : ∀ n, n ∈ H → ∀ g : G, g * n * g⁻¹ ∈ H)

attribute [class] normal

end subgroup

namespace add_subgroup

/-- An add_subgroup is normal if whenever `n ∈ H`, then `g + n - g ∈ H` for every `g : G` -/
structure normal (H : add_subgroup A) : Prop :=
(conj_mem [] : ∀ n, n ∈ H → ∀ g : A, g + n - g ∈ H)

attribute [to_additive add_subgroup.normal] subgroup.normal
attribute [class] normal

end add_subgroup

namespace subgroup

variables {H K : subgroup G}
@[instance, priority 100, to_additive]
lemma normal_of_comm {G : Type*} [comm_group G] (H : subgroup G) : H.normal :=
⟨by simp [mul_comm, mul_left_comm]⟩

namespace normal

variable nH : H.normal

@[to_additive] lemma mem_comm {a b : G} (h : a * b ∈ H) : b * a ∈ H :=
have a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ H, from nH.conj_mem (a * b) h a⁻¹, by simpa

@[to_additive] lemma mem_comm_iff {a b : G} : a * b ∈ H ↔ b * a ∈ H :=
⟨nH.mem_comm, nH.mem_comm⟩

end normal

@[instance, priority 100, to_additive]
lemma bot_normal : normal (⊥ : subgroup G) := ⟨by simp⟩

variable (G)
/-- The center of a group `G` is the set of elements that commute with everything in `G` -/
@[to_additive "The center of a group `G` is the set of elements that commute with everything in `G`"]
def center : subgroup G :=
{ carrier := {z | ∀ g, g * z = z * g},
  one_mem' := by simp,
  mul_mem' := λ a b (ha : ∀ g, g * a = a * g) (hb : ∀ g, g * b = b * g) g,
    by assoc_rw [ha, hb g],
  inv_mem' := λ a (ha : ∀ g, g * a = a * g) g,
    by rw [← inv_inj, mul_inv_rev, inv_inv, ← ha, mul_inv_rev, inv_inv] }

variable {G}

@[to_additive] lemma mem_center_iff {z : G} : z ∈ center G ↔ ∀ g, g * z = z * g := iff.rfl

@[instance, priority 100, to_additive]
lemma center_normal : (center G).normal :=
⟨begin
  assume n hn g h,
  assoc_rw [hn (h * g), hn g],
  simp
end⟩

variables {G} (H)
/-- The `normalizer` of `H` is the smallest subgroup of `G` inside which `H` is normal. -/
@[to_additive "The `normalizer` of `H` is the smallest subgroup of `G` inside which `H` is normal."]
def normalizer : subgroup G :=
{ carrier := {g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H},
  one_mem' := by simp,
  mul_mem' := λ a b (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) (hb : ∀ n, n ∈ H ↔ b * n * b⁻¹ ∈ H) n,
    by { rw [hb, ha], simp [mul_assoc] },
  inv_mem' := λ a (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) n,
    by { rw [ha (a⁻¹ * n * a⁻¹⁻¹)], simp [mul_assoc] } }

-- variant for sets. **TODO** should this replace `normalizer`?
/-- The `set_normalizer` of `S` is the subgroup of `G` whose elements satisfy `g*S*g⁻¹=S` -/
@[to_additive "The `set_normalizer` of `S` is the subgroup of `G` whose elements satisfy `g+S-g=S`."]
def set_normalizer (S : set G) : subgroup G :=
{ carrier := {g : G | ∀ n, n ∈ S ↔ g * n * g⁻¹ ∈ S},
  one_mem' := by simp,
  mul_mem' := λ a b (ha : ∀ n, n ∈ S ↔ a * n * a⁻¹ ∈ S) (hb : ∀ n, n ∈ S ↔ b * n * b⁻¹ ∈ S) n,
    by { rw [hb, ha], simp [mul_assoc] },
  inv_mem' := λ a (ha : ∀ n, n ∈ S ↔ a * n * a⁻¹ ∈ S) n,
    by { rw [ha (a⁻¹ * n * a⁻¹⁻¹)], simp [mul_assoc] } }

variable {H}
@[to_additive] lemma mem_normalizer_iff {g : G} :
  g ∈ normalizer H ↔ ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H := iff.rfl

@[to_additive] lemma le_normalizer : H ≤ normalizer H :=
λ x xH n, by rw [H.mul_mem_cancel_right (H.inv_mem xH), H.mul_mem_cancel_left xH]

@[instance, priority 100, to_additive]
lemma normal_in_normalizer : (H.comap H.normalizer.subtype).normal :=
⟨λ x xH g, by simpa using (g.2 x).1 xH⟩

open_locale classical

@[to_additive] lemma le_normalizer_of_normal (hK : (H.comap K.subtype).normal) (HK : H ≤ K) : K ≤ H.normalizer :=
λ x hx y, ⟨λ yH, hK.conj_mem ⟨y, HK yH⟩ yH ⟨x, hx⟩,
  λ yH, by simpa [mem_comap, mul_assoc] using
             hK.conj_mem ⟨x * y * x⁻¹, HK yH⟩ yH ⟨x⁻¹, K.inv_mem hx⟩⟩

end subgroup

namespace group
variables {s : set G}

/-- Given an element `a`, `conjugates a` is the set of conjugates. -/
def conjugates (a : G) : set G := {b | is_conj a b}

lemma mem_conjugates_self {a : G} : a ∈ conjugates a := is_conj_refl _

/-- Given a set `s`, `conjugates_of_set s` is the set of all conjugates of
the elements of `s`. -/
def conjugates_of_set (s : set G) : set G := ⋃ a ∈ s, conjugates a

lemma mem_conjugates_of_set_iff {x : G} : x ∈ conjugates_of_set s ↔ ∃ a ∈ s, is_conj a x :=
set.mem_bUnion_iff

theorem subset_conjugates_of_set : s ⊆ conjugates_of_set s :=
λ (x : G) (h : x ∈ s), mem_conjugates_of_set_iff.2 ⟨x, h, is_conj_refl _⟩

theorem conjugates_of_set_mono {s t : set G} (h : s ⊆ t) :
  conjugates_of_set s ⊆ conjugates_of_set t :=
set.bUnion_subset_bUnion_left h

lemma conjugates_subset_normal {N : subgroup G} (tn : N.normal) {a : G} (h : a ∈ N) :
  conjugates a ⊆ N :=
by { rintros a ⟨c, rfl⟩, exact tn.conj_mem a h c }

theorem conjugates_of_set_subset {s : set G} {N : subgroup G} (hN : N.normal) (h : s ⊆ N) :
  conjugates_of_set s ⊆ N :=
set.bUnion_subset (λ x H, conjugates_subset_normal hN (h H))

/-- The set of conjugates of `s` is closed under conjugation. -/
lemma conj_mem_conjugates_of_set {x c : G} :
  x ∈ conjugates_of_set s → (c * x * c⁻¹ ∈ conjugates_of_set s) :=
λ H,
begin
  rcases (mem_conjugates_of_set_iff.1 H) with ⟨a,h₁,h₂⟩,
  exact mem_conjugates_of_set_iff.2 ⟨a, h₁, is_conj_trans h₂ ⟨c,rfl⟩⟩,
end

end group

namespace subgroup
open group

variable {s : set G}

/-- The normal closure of a set `s` is the subgroup closure of all the conjugates of
elements of `s`. It is the smallest normal subgroup containing `s`. -/
def normal_closure (s : set G) : subgroup G := closure (conjugates_of_set s)

theorem conjugates_of_set_subset_normal_closure : conjugates_of_set s ⊆ normal_closure s :=
subset_closure

theorem subset_normal_closure : s ⊆ normal_closure s :=
set.subset.trans subset_conjugates_of_set conjugates_of_set_subset_normal_closure

/-- The normal closure of `s` is a normal subgroup. -/
@[instance] lemma normal_closure_normal : (normal_closure s).normal :=
⟨λ n h g,
begin
  refine subgroup.closure_induction h (λ x hx, _) _ (λ x y ihx ihy, _) (λ x ihx, _),
  { exact (conjugates_of_set_subset_normal_closure (conj_mem_conjugates_of_set hx)) },
  { simpa using (normal_closure s).one_mem },
  { rw ← conj_mul,
    exact mul_mem _ ihx ihy },
  { rw ← conj_inv,
    exact inv_mem _ ihx }
end⟩

/-- The normal closure of `s` is the smallest normal subgroup containing `s`. -/
theorem normal_closure_le_normal {N : subgroup G} (hN : N.normal)
  (h : s ⊆ N) : normal_closure s ≤ N :=
begin
  assume a w,
  refine closure_induction w (λ x hx, _) _  (λ x y ihx ihy, _) (λ x ihx, _),
  { exact (conjugates_of_set_subset hN h hx) },
  { exact subgroup.one_mem _ },
  { exact subgroup.mul_mem _ ihx ihy },
  { exact subgroup.inv_mem _ ihx }
end

lemma normal_closure_subset_iff {N : subgroup G} (hN : N.normal) : s ⊆ N ↔ normal_closure s ≤ N :=
⟨normal_closure_le_normal hN, set.subset.trans (subset_normal_closure)⟩

theorem normal_closure_mono {s t : set G} (h : s ⊆ t) : normal_closure s ≤ normal_closure t :=
normal_closure_le_normal normal_closure_normal (set.subset.trans h subset_normal_closure)

theorem normal_closure_eq_infi : normal_closure s =
  ⨅ (N : subgroup G) (h : normal N) (hs : s ⊆ N), N :=
le_antisymm
  (le_infi (λ N, le_infi (λ hN, le_infi (normal_closure_le_normal hN))))
  (infi_le_of_le (normal_closure s) (infi_le_of_le (by apply_instance)
    (infi_le_of_le subset_normal_closure (le_refl _))))

end subgroup
namespace add_subgroup

open set

lemma gsmul_mem (H : add_subgroup A) {x : A} (hx : x ∈ H) :
  ∀ n : ℤ, gsmul n x ∈ H
| (int.of_nat n) := add_submonoid.nsmul_mem H.to_add_submonoid hx n
| -[1+ n]        := H.neg_mem' $ H.add_mem hx $ add_submonoid.nsmul_mem H.to_add_submonoid hx n

lemma sub_mem (H : add_subgroup A) {x y : A} (hx : x ∈ H) (hy : y ∈ H) : x - y ∈ H :=
H.add_mem hx (H.neg_mem hy)

/-- The `add_subgroup` generated by an element of an `add_group` equals the set of
natural number multiples of the element. -/
lemma mem_closure_singleton {x y : A} :
  y ∈ closure ({x} : set A) ↔ ∃ n : ℤ, gsmul n x = y :=
begin
  refine ⟨λ hy, closure_induction hy _ _ _ _,
    λ ⟨n, hn⟩, hn ▸ gsmul_mem _ (subset_closure $ mem_singleton x) n⟩,
  { intros y hy,
    rw [eq_of_mem_singleton hy],
    exact ⟨1, one_gsmul x⟩ },
  { exact ⟨0, rfl⟩ },
  { rintros _ _ ⟨n, rfl⟩ ⟨m, rfl⟩,
    exact ⟨n + m, add_gsmul x n m⟩ },
  { rintros _ ⟨n, rfl⟩,
    refine ⟨-n, neg_gsmul x n⟩ }
end

variable (H : add_subgroup A)
@[simp] lemma coe_smul (x : H) (n : ℕ) : ((nsmul n x : H) : A) = nsmul n x :=
coe_subtype H ▸ add_monoid_hom.map_nsmul _ _ _
@[simp] lemma coe_gsmul (x : H) (n : ℤ) : ((n •ℤ x : H) : A) = n •ℤ x :=
coe_subtype H ▸ add_monoid_hom.map_gsmul _ _ _

attribute [to_additive add_subgroup.coe_smul] subgroup.coe_pow
attribute [to_additive add_subgroup.coe_gsmul] subgroup.coe_gpow

end add_subgroup

namespace monoid_hom

variables {N : Type*} {P : Type*} [group N] [group P] (K : subgroup G)

open subgroup

/-- The range of a monoid homomorphism from a group is a subgroup. -/
@[to_additive "The range of an `add_monoid_hom` from an `add_group` is an `add_subgroup`."]
def range (f : G →* N) : subgroup N :=
subgroup.copy ((⊤ : subgroup G).map f) (set.range f) (by simp [set.ext_iff])

@[simp, to_additive] lemma coe_range (f : G →* N) :
  (f.range : set N) = set.range f := rfl

@[simp, to_additive] lemma mem_range {f : G →* N} {y : N} :
  y ∈ f.range ↔ ∃ x, f x = y :=
iff.rfl

@[to_additive] lemma range_eq_map (f : G →* N) : f.range = (⊤ : subgroup G).map f :=
by ext; simp

@[to_additive] def to_range (f : G →* N) : G →* f.range :=
monoid_hom.mk' (λ g, ⟨f g, ⟨g, rfl⟩⟩) $ λ a b, by {ext, exact f.map_mul' _ _}

@[to_additive]
lemma map_range (g : N →* P) (f : G →* N) : f.range.map g = (g.comp f).range :=
by rw [range_eq_map, range_eq_map]; exact (⊤ : subgroup G).map_map g f

@[to_additive]
lemma range_top_iff_surjective {N} [group N] {f : G →* N} :
  f.range = (⊤ : subgroup N) ↔ function.surjective f :=
subgroup.ext'_iff.trans $ iff.trans (by rw [coe_range, coe_top]) set.range_iff_surjective

/-- The range of a surjective monoid homomorphism is the whole of the codomain. -/
@[to_additive "The range of a surjective `add_monoid` homomorphism is the whole of the codomain."]
lemma range_top_of_surjective {N} [group N] (f : G →* N) (hf : function.surjective f) :
  f.range = (⊤ : subgroup N) :=
range_top_iff_surjective.2 hf

/-- The multiplicative kernel of a monoid homomorphism is the subgroup of elements `x : G` such that
`f x = 1` -/
@[to_additive "The additive kernel of an `add_monoid` homomorphism is the `add_subgroup` of elements
such that `f x = 0`"]
def ker (f : G →* N) := (⊥ : subgroup N).comap f

@[to_additive]
lemma mem_ker {f : G →* N} {x : G} : x ∈ f.ker ↔ f x = 1 := iff.rfl

@[to_additive]
lemma comap_ker (g : N →* P) (f : G →* N) : g.ker.comap f = (g.comp f).ker := rfl

@[to_additive] lemma to_range_ker (f : G →* N) : ker (to_range f) = ker f :=
begin
  ext,
  change (⟨f x, _⟩ : range f) = ⟨1, _⟩ ↔ f x = 1,
  simp only [],
end


/-- The subgroup of elements `x : G` such that `f x = g x` -/
@[to_additive "The additive subgroup of elements `x : G` such that `f x = g x`"]
def eq_locus (f g : G →* N) : subgroup G :=
{ inv_mem' := λ x (hx : f x = g x), show f x⁻¹ = g x⁻¹, by rw [f.map_inv, g.map_inv, hx],
  .. eq_mlocus f g}

/-- If two monoid homomorphisms are equal on a set, then they are equal on its subgroup closure. -/
@[to_additive]
lemma eq_on_closure {f g : G →* N} {s : set G} (h : set.eq_on f g s) :
  set.eq_on f g (closure s) :=
show closure s ≤ f.eq_locus g, from (closure_le _).2 h

@[to_additive]
lemma eq_of_eq_on_top {f g : G →* N} (h : set.eq_on f g (⊤ : subgroup G)) :
  f = g :=
ext $ λ x, h trivial

@[to_additive]
lemma eq_of_eq_on_dense {s : set G} (hs : closure s = ⊤) {f g : G →* N} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_top $ hs ▸ eq_on_closure h

@[to_additive]
lemma gclosure_preimage_le (f : G →* N) (s : set N) :
  closure (f ⁻¹' s) ≤ (closure s).comap f :=
(closure_le _).2 $ λ x hx, by rw [mem_coe, mem_comap]; exact subset_closure hx

/-- The image under a monoid homomorphism of the subgroup generated by a set equals the subgroup
generated by the image of the set. -/
@[to_additive "The image under an `add_monoid` hom of the `add_subgroup` generated by a set equals
the `add_subgroup` generated by the image of the set."]
lemma map_closure (f : G →* N) (s : set G) :
  (closure s).map f = closure (f '' s) :=
le_antisymm
  (map_le_iff_le_comap.2 $ le_trans (closure_mono $ set.subset_preimage_image f s)
    (gclosure_preimage_le _ _))
  ((closure_le _).2 $ set.image_subset _ subset_closure)

end monoid_hom

variables {N : Type*} [group N]

@[to_additive]
lemma subgroup.normal.comap {H : subgroup N} (hH : H.normal) (f : G →* N) :
  (H.comap f).normal :=
⟨λ _, by simp [subgroup.mem_comap, hH.conj_mem] {contextual := tt}⟩

@[instance, priority 100, to_additive] lemma subgroup.normal_comap {H : subgroup N}
  [nH : H.normal] (f : G →* N) :  (H.comap f).normal := nH.comap _

@[instance, priority 100, to_additive]
lemma monoid_hom.normal_ker (f : G →* N) : f.ker.normal :=
by rw [monoid_hom.ker]; apply_instance

namespace subgroup

/-- The subgroup generated by an element. -/
def gpowers (g : G) : subgroup G :=
subgroup.copy (gpowers_hom G g).range (set.range ((^) g : ℤ → G)) rfl

@[simp] lemma mem_gpowers (g : G) : g ∈ gpowers g := ⟨1, gpow_one _⟩

lemma gpowers_eq_closure (g : G) : gpowers g = closure {g} :=
by { ext, exact mem_closure_singleton.symm }

end subgroup

namespace add_subgroup

/-- The subgroup generated by an element. -/
def gmultiples (a : A) : add_subgroup A :=
add_subgroup.copy (gmultiples_hom A a).range (set.range ((•ℤ a) : ℤ → A)) rfl

@[simp] lemma mem_gmultiples (a : A) : a ∈ gmultiples a := ⟨1, one_gsmul _⟩

lemma gmultiples_eq_closure (a : A) : gmultiples a = closure {a} :=
by { ext, exact mem_closure_singleton.symm }

attribute [to_additive add_subgroup.gmultiples] subgroup.gpowers
attribute [to_additive add_subgroup.mem_gmultiples] subgroup.mem_gpowers
attribute [to_additive add_subgroup.gmultiples_eq_closure] subgroup.gpowers_eq_closure

end add_subgroup

namespace mul_equiv

variables {H K : subgroup G}

/-- Makes the identity isomorphism from a proof two subgroups of a multiplicative
    group are equal. -/
@[to_additive add_subgroup_congr "Makes the identity additive isomorphism from a proof
two subgroups of an additive group are equal."]
def subgroup_congr (h : H = K) : H ≃* K :=
{ map_mul' :=  λ _ _, rfl, ..equiv.set_congr $ subgroup.ext'_iff.1 h }

end mul_equiv
