/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import data.equiv.basic algebra.field

/-!
# equivs in the algebraic hierarchy

The role of this file is twofold. In the first part there are theorems of the following
form: if α has a group structure and α ≃ β then β has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and so on.

In the second part there are extensions of equiv called add_equiv,
mul_equiv, and ring_equiv, which are datatypes representing isomorphisms
of add_monoids/add_groups, monoids/groups and rings.

## Notations

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Implementation notes

Bundling structures means that many things turn into definitions, meaning that to_additive
cannot do much work for us, and conversely that we have to do a lot of naming for it.

The fields for mul_equiv and add_equiv now avoid the unbundled `is_mul_hom` and `is_add_hom`,
as these are deprecated. However ring_equiv still relies on `is_ring_hom`; this should
be rewritten in future.

## Tags

equiv, mul_equiv, add_equiv, ring_equiv
-/

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

namespace equiv

section group
variables [group α]

protected def mul_left (a : α) : α ≃ α :=
{ to_fun    := λx, a * x,
  inv_fun   := λx, a⁻¹ * x,
  left_inv  := assume x, show a⁻¹ * (a * x) = x, from inv_mul_cancel_left a x,
  right_inv := assume x, show a * (a⁻¹ * x) = x, from mul_inv_cancel_left a x }

attribute [to_additive equiv.add_left._proof_1] equiv.mul_left._proof_1
attribute [to_additive equiv.add_left._proof_2] equiv.mul_left._proof_2
attribute [to_additive equiv.add_left] equiv.mul_left

protected def mul_right (a : α) : α ≃ α :=
{ to_fun    := λx, x * a,
  inv_fun   := λx, x * a⁻¹,
  left_inv  := assume x, show (x * a) * a⁻¹ = x, from mul_inv_cancel_right x a,
  right_inv := assume x, show (x * a⁻¹) * a = x, from inv_mul_cancel_right x a }

attribute [to_additive equiv.add_right._proof_1] equiv.mul_right._proof_1
attribute [to_additive equiv.add_right._proof_2] equiv.mul_right._proof_2
attribute [to_additive equiv.add_right] equiv.mul_right

protected def inv (α) [group α] : α ≃ α :=
{ to_fun    := λa, a⁻¹,
  inv_fun   := λa, a⁻¹,
  left_inv  := assume a, inv_inv a,
  right_inv := assume a, inv_inv a }

attribute [to_additive equiv.neg._proof_1] equiv.inv._proof_1
attribute [to_additive equiv.neg._proof_2] equiv.inv._proof_2
attribute [to_additive equiv.neg] equiv.inv

def units_equiv_ne_zero (α : Type*) [field α] : units α ≃ {a : α | a ≠ 0} :=
⟨λ a, ⟨a.1, units.ne_zero _⟩, λ a, units.mk0 _ a.2, λ ⟨_, _, _, _⟩, units.ext rfl, λ ⟨_, _⟩, rfl⟩

@[simp] lemma coe_units_equiv_ne_zero [field α] (a : units α) :
  ((units_equiv_ne_zero α a) : α) = a := rfl

end group

section instances

variables (e : α ≃ β)

protected def has_zero [has_zero β] : has_zero α := ⟨e.symm 0⟩
lemma zero_def [has_zero β] : @has_zero.zero _ (equiv.has_zero e) = e.symm 0 := rfl

protected def has_one [has_one β] : has_one α := ⟨e.symm 1⟩
lemma one_def [has_one β] : @has_one.one _ (equiv.has_one e) = e.symm 1 := rfl

protected def has_mul [has_mul β] : has_mul α := ⟨λ x y, e.symm (e x * e y)⟩
lemma mul_def [has_mul β] (x y : α) :
  @has_mul.mul _ (equiv.has_mul e) x y = e.symm (e x * e y) := rfl

protected def has_add [has_add β] : has_add α := ⟨λ x y, e.symm (e x + e y)⟩
lemma add_def [has_add β] (x y : α) :
  @has_add.add _ (equiv.has_add e) x y = e.symm (e x + e y) := rfl

protected def has_inv [has_inv β] : has_inv α := ⟨λ x, e.symm (e x)⁻¹⟩
lemma inv_def [has_inv β] (x : α) : @has_inv.inv _ (equiv.has_inv e) x = e.symm (e x)⁻¹ := rfl

protected def has_neg [has_neg β] : has_neg α := ⟨λ x, e.symm (-e x)⟩
lemma neg_def [has_neg β] (x : α) : @has_neg.neg _ (equiv.has_neg e) x = e.symm (-e x) := rfl

protected def semigroup [semigroup β] : semigroup α :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..equiv.has_mul e }

protected def comm_semigroup [comm_semigroup β] : comm_semigroup α :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..equiv.semigroup e }

protected def monoid [monoid β] : monoid α :=
{ one_mul := by simp [mul_def, one_def],
  mul_one := by simp [mul_def, one_def],
  ..equiv.semigroup e,
  ..equiv.has_one e }

protected def comm_monoid [comm_monoid β] : comm_monoid α :=
{ ..equiv.comm_semigroup e,
  ..equiv.monoid e }

protected def group [group β] : group α :=
{ mul_left_inv := by simp [mul_def, inv_def, one_def],
  ..equiv.monoid e,
  ..equiv.has_inv e }

protected def comm_group [comm_group β] : comm_group α :=
{ ..equiv.group e,
  ..equiv.comm_semigroup e }

protected def add_semigroup [add_semigroup β] : add_semigroup α :=
@additive.add_semigroup _ (@equiv.semigroup _ _ e multiplicative.semigroup)

protected def add_comm_semigroup [add_comm_semigroup β] : add_comm_semigroup α :=
@additive.add_comm_semigroup _ (@equiv.comm_semigroup _ _ e multiplicative.comm_semigroup)

protected def add_monoid [add_monoid β] : add_monoid α :=
@additive.add_monoid _ (@equiv.monoid _ _ e multiplicative.monoid)

protected def add_comm_monoid [add_comm_monoid β] : add_comm_monoid α :=
@additive.add_comm_monoid _ (@equiv.comm_monoid _ _ e multiplicative.comm_monoid)

protected def add_group [add_group β] : add_group α :=
@additive.add_group _ (@equiv.group _ _ e multiplicative.group)

protected def add_comm_group [add_comm_group β] : add_comm_group α :=
@additive.add_comm_group _ (@equiv.comm_group _ _ e multiplicative.comm_group)

protected def semiring [semiring β] : semiring α :=
{ right_distrib := by simp [mul_def, add_def, add_mul],
  left_distrib := by simp [mul_def, add_def, mul_add],
  zero_mul := by simp [mul_def, zero_def],
  mul_zero := by simp [mul_def, zero_def],
  ..equiv.has_zero e,
  ..equiv.has_mul e,
  ..equiv.has_add e,
  ..equiv.monoid e,
  ..equiv.add_comm_monoid e }

protected def comm_semiring [comm_semiring β] : comm_semiring α :=
{ ..equiv.semiring e,
  ..equiv.comm_monoid e }

protected def ring [ring β] : ring α :=
{ ..equiv.semiring e,
  ..equiv.add_comm_group e }

protected def comm_ring [comm_ring β] : comm_ring α :=
{ ..equiv.comm_monoid e,
  ..equiv.ring e }

protected def zero_ne_one_class [zero_ne_one_class β] : zero_ne_one_class α :=
{ zero_ne_one := by simp [zero_def, one_def],
  ..equiv.has_zero e,
  ..equiv.has_one e }

protected def nonzero_comm_ring [nonzero_comm_ring β] : nonzero_comm_ring α :=
{ ..equiv.zero_ne_one_class e,
  ..equiv.comm_ring e }

protected def domain [domain β] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by simp [mul_def, zero_def, equiv.eq_symm_apply],
  ..equiv.has_zero e,
  ..equiv.zero_ne_one_class e,
  ..equiv.has_mul e,
  ..equiv.ring e }

protected def integral_domain [integral_domain β] : integral_domain α :=
{ ..equiv.domain e,
  ..equiv.nonzero_comm_ring e }

protected def division_ring [division_ring β] : division_ring α :=
{ inv_mul_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact inv_mul_cancel,
  mul_inv_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact mul_inv_cancel,
  ..equiv.has_zero e,
  ..equiv.has_one e,
  ..equiv.domain e,
  ..equiv.has_inv e }

protected def field [field β] : field α :=
{ ..equiv.integral_domain e,
  ..equiv.division_ring e }

protected def discrete_field [discrete_field β] : discrete_field α :=
{ has_decidable_eq := equiv.decidable_eq e,
  inv_zero := by simp [mul_def, inv_def, zero_def],
  ..equiv.has_mul e,
  ..equiv.has_inv e,
  ..equiv.has_zero e,
  ..equiv.field e }

end instances
end equiv

set_option old_structure_cmd true

/-- mul_equiv α β is the type of an equiv α ≃ β which preserves multiplication. -/
structure mul_equiv (α β : Type*) [has_mul α] [has_mul β] extends α ≃ β :=
(map_mul' : ∀ x y : α, to_fun (x * y) = to_fun x * to_fun y)

/-- add_equiv α β is the type of an equiv α ≃ β which preserves addition. -/
structure add_equiv (α β : Type*) [has_add α] [has_add β] extends α ≃ β :=
(map_add' : ∀ x y : α, to_fun (x + y) = to_fun x + to_fun y)

attribute [to_additive add_equiv] mul_equiv
attribute [to_additive add_equiv.cases_on] mul_equiv.cases_on
attribute [to_additive add_equiv.has_sizeof_inst] mul_equiv.has_sizeof_inst
attribute [to_additive add_equiv.inv_fun] mul_equiv.inv_fun
attribute [to_additive add_equiv.left_inv] mul_equiv.left_inv
attribute [to_additive add_equiv.mk] mul_equiv.mk
attribute [to_additive add_equiv.mk.inj] mul_equiv.mk.inj
attribute [to_additive add_equiv.mk.inj_arrow] mul_equiv.mk.inj_arrow
attribute [to_additive add_equiv.mk.inj_eq] mul_equiv.mk.inj_eq
attribute [to_additive add_equiv.mk.sizeof_spec] mul_equiv.mk.sizeof_spec
attribute [to_additive add_equiv.map_add'] mul_equiv.map_mul'
attribute [to_additive add_equiv.no_confusion] mul_equiv.no_confusion
attribute [to_additive add_equiv.no_confusion_type] mul_equiv.no_confusion_type
attribute [to_additive add_equiv.rec] mul_equiv.rec
attribute [to_additive add_equiv.rec_on] mul_equiv.rec_on
attribute [to_additive add_equiv.right_inv] mul_equiv.right_inv
attribute [to_additive add_equiv.sizeof] mul_equiv.sizeof
attribute [to_additive add_equiv.to_equiv] mul_equiv.to_equiv
attribute [to_additive add_equiv.to_fun] mul_equiv.to_fun

infix ` ≃* `:25 := mul_equiv
infix ` ≃+ `:25 := add_equiv

namespace mul_equiv

@[to_additive add_equiv.has_coe_to_fun]
instance {α β} [has_mul α] [has_mul β] : has_coe_to_fun (α ≃* β) := ⟨_, mul_equiv.to_fun⟩

variables [has_mul α] [has_mul β] [has_mul γ]

/-- A multiplicative isomorphism preserves multiplication (canonical form). -/
def map_mul (f : α ≃* β) :  ∀ x y : α, f (x * y) = f x * f y := f.map_mul'

/-- A multiplicative isomorphism preserves multiplication (deprecated). -/
instance (h : α ≃* β) : is_mul_hom h := ⟨h.map_mul⟩

/-- The identity map is a multiplicative isomorphism. -/
@[refl] def refl (α : Type*) [has_mul α] : α ≃* α :=
{ map_mul' := λ _ _,rfl,
..equiv.refl _}

/-- The inverse of an isomorphism is an isomorphism. -/
@[symm] def symm (h : α ≃* β) : β ≃* α :=
{ map_mul' := λ n₁ n₂, function.injective_of_left_inverse h.left_inv begin
    show h.to_equiv (h.to_equiv.symm (n₁ * n₂)) =
      h ((h.to_equiv.symm n₁) * (h.to_equiv.symm n₂)),
   rw h.map_mul,
   show _ = h.to_equiv (_) * h.to_equiv (_),
   rw [h.to_equiv.apply_symm_apply, h.to_equiv.apply_symm_apply, h.to_equiv.apply_symm_apply], end,
  ..h.to_equiv.symm}

@[simp] theorem to_equiv_symm (f : α ≃* β) : f.symm.to_equiv = f.to_equiv.symm := rfl

/-- Transitivity of multiplication-preserving isomorphisms -/
@[trans] def trans (h1 : α ≃* β) (h2 : β ≃* γ) : (α ≃* γ) :=
{ map_mul' := λ x y, show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y),
    by rw [h1.map_mul, h2.map_mul],
  ..h1.to_equiv.trans h2.to_equiv }

/-- e.right_inv in canonical form -/
@[simp] def apply_symm_apply (e : α ≃* β) : ∀ (y : β), e (e.symm y) = y :=
equiv.apply_symm_apply (e.to_equiv)

/-- e.left_inv in canonical form -/
@[simp] def symm_apply_apply (e : α ≃* β) : ∀ (x : α), e.symm (e x) = x :=
equiv.symm_apply_apply (e.to_equiv)

/-- a multiplicative equiv of monoids sends 1 to 1 (and is hence a monoid isomorphism) -/
@[simp] def map_one {α β} [monoid α] [monoid β] (h : α ≃* β) : h 1 = 1 :=
by rw [←mul_one (h 1), ←h.apply_symm_apply 1, ←h.map_mul, one_mul]

/-- A multiplicative bijection between two monoids is an isomorphism. -/
def to_monoid_hom {α β} [monoid α] [monoid β] (h : α ≃* β) : (α →* β) :=
{ to_fun := h,
  map_mul' := h.map_mul,
  map_one' := h.map_one }

/-- A multiplicative bijection between two monoids is a monoid hom
  (deprecated -- use to_monoid_hom). -/
instance is_monoid_hom {α β} [monoid α] [monoid β] (h : α ≃* β) : is_monoid_hom h :=
⟨h.map_one⟩

/-- A multiplicative bijection between two groups is a group hom
  (deprecated -- use to_monoid_hom). -/
instance is_group_hom {α β} [group α] [group β] (h : α ≃* β) :
  is_group_hom h := { map_mul := h.map_mul }

end mul_equiv

namespace add_equiv

variables [has_add α] [has_add β] [has_add γ]

/-- An additive isomorphism preserves addition (canonical form). -/
def map_add (f : α ≃+ β) :  ∀ x y : α, f (x + y) = f x + f y := f.map_add'

attribute [to_additive add_equiv.map_add] mul_equiv.map_mul
attribute [to_additive add_equiv.map_add.equations._eqn_1] mul_equiv.map_mul.equations._eqn_1

/-- A additive isomorphism preserves multiplication (deprecated). -/
instance (h : α ≃+ β) : is_add_hom h := ⟨h.map_add⟩

/-- The identity map is an additive isomorphism. -/
@[refl] def refl (α : Type*) [has_add α] : α ≃+ α :=
{ map_add' := λ _ _,rfl,
..equiv.refl _}

attribute [to_additive add_equiv.refl] mul_equiv.refl
attribute [to_additive add_equiv.refl._proof_1] mul_equiv.refl._proof_1
attribute [to_additive add_equiv.refl._proof_2] mul_equiv.refl._proof_2
attribute [to_additive add_equiv.refl._proof_3] mul_equiv.refl._proof_3
attribute [to_additive add_equiv.refl.equations._eqn_1] mul_equiv.refl.equations._eqn_1

/-- The inverse of an isomorphism is an isomorphism. -/
@[symm] def symm (h : α ≃+ β) : β ≃+ α :=
{ map_add' := λ n₁ n₂, function.injective_of_left_inverse h.left_inv begin
    show h.to_equiv (h.to_equiv.symm (n₁ + n₂)) =
      h ((h.to_equiv.symm n₁) + (h.to_equiv.symm n₂)),
   rw h.map_add,
   show _ = h.to_equiv (_) + h.to_equiv (_),
   rw [h.to_equiv.apply_symm_apply, h.to_equiv.apply_symm_apply, h.to_equiv.apply_symm_apply], end,
  ..h.to_equiv.symm}

attribute [to_additive add_equiv.symm] mul_equiv.symm
attribute [to_additive add_equiv.symm._proof_1] mul_equiv.symm._proof_1
attribute [to_additive add_equiv.symm._proof_2] mul_equiv.symm._proof_2
attribute [to_additive add_equiv.symm._proof_3] mul_equiv.symm._proof_3
attribute [to_additive add_equiv.symm.equations._eqn_1] mul_equiv.symm.equations._eqn_1

@[simp] theorem to_equiv_symm (f : α ≃+ β) : f.symm.to_equiv = f.to_equiv.symm := rfl

attribute [to_additive add_equiv.to_equiv_symm] mul_equiv.to_equiv_symm

/-- Transitivity of addition-preserving isomorphisms -/
@[trans] def trans (h1 : α ≃+ β) (h2 : β ≃+ γ) : (α ≃+ γ) :=
{ map_add' := λ x y, show h2 (h1 (x + y)) = h2 (h1 x) + h2 (h1 y),
    by rw [h1.map_add, h2.map_add],
  ..h1.to_equiv.trans h2.to_equiv }

attribute [to_additive add_equiv.trans] mul_equiv.trans
attribute [to_additive add_equiv.trans._proof_1] mul_equiv.trans._proof_1
attribute [to_additive add_equiv.trans._proof_2] mul_equiv.trans._proof_2
attribute [to_additive add_equiv.trans._proof_3] mul_equiv.trans._proof_3
attribute [to_additive add_equiv.trans.equations._eqn_1] mul_equiv.trans.equations._eqn_1

/-- e.right_inv in canonical form -/
def apply_symm_apply (e : α ≃+ β) : ∀ (y : β), e (e.symm y) = y :=
equiv.apply_symm_apply (e.to_equiv)

attribute [to_additive add_equiv.apply_symm_apply] mul_equiv.apply_symm_apply
attribute [to_additive add_equiv.apply_symm_apply.equations._eqn_1] mul_equiv.apply_symm_apply.equations._eqn_1

/-- e.left_inv in canonical form -/
def symm_apply_apply (e : α ≃+ β) : ∀ (x : α), e.symm (e x) = x :=
equiv.symm_apply_apply (e.to_equiv)

attribute [to_additive add_equiv.symm_apply_apply] mul_equiv.symm_apply_apply
attribute [to_additive add_equiv.symm_apply_apply.equations._eqn_1] mul_equiv.symm_apply_apply.equations._eqn_1

/-- an additive equiv of monoids sends 0 to 0 (and is hence an  `add_monoid` isomorphism) -/
def map_zero {α β} [add_monoid α] [add_monoid β] (h : α ≃+ β) : h 0 = 0 :=
by rw [←add_zero (h 0), ←h.apply_symm_apply 0, ←h.map_add, zero_add]

attribute [to_additive add_equiv.map_zero] mul_equiv.map_one
attribute [to_additive add_equiv.map_zero.equations._eqn_1] mul_equiv.map_one.equations._eqn_1

/-- An additive bijection between two add_monoids is an isomorphism. -/
def to_add_monoid_hom {α β} [add_monoid α] [add_monoid β] (h : α ≃+ β) : (α →+ β) :=
{ to_fun := h,
  map_add' := h.map_add,
  map_zero' := h.map_zero }

attribute [to_additive add_equiv.to_add_monoid_hom] mul_equiv.to_monoid_hom
attribute [to_additive add_equiv.to_add_monoid_hom._proof_1] mul_equiv.to_monoid_hom._proof_1
attribute [to_additive add_equiv.to_add_monoid_hom.equations._eqn_1]
  mul_equiv.to_monoid_hom.equations._eqn_1

/-- an additive bijection between two add_monoids is an add_monoid hom
(deprecated -- use to_add_monoid_hom) -/
instance is_add_monoid_hom {α β} [add_monoid α] [add_monoid β] (h : α ≃+ β) : is_add_monoid_hom h :=
⟨h.map_zero⟩

attribute [to_additive add_equiv.is_add_monoid_hom] mul_equiv.is_monoid_hom
attribute [to_additive add_equiv.is_add_monoid_hom.equations._eqn_1]
  mul_equiv.is_monoid_hom.equations._eqn_1

/-- An additive bijection between two add_groups is an add_group hom
  (deprecated -- use to_monoid_hom). -/
instance is_add_group_hom {α β} [add_group α] [add_group β] (h : α ≃+ β) :
  is_add_group_hom h := { map_add := h.map_add }

attribute [to_additive add_equiv.is_add_group_hom] mul_equiv.is_group_hom
attribute [to_additive add_equiv.is_add_group_hom.equations._eqn_1]
  mul_equiv.is_group_hom.equations._eqn_1

end add_equiv

namespace units

variables [monoid α] [monoid β] [monoid γ]
(f : α → β) (g : β → γ) [is_monoid_hom f] [is_monoid_hom g]

def map_equiv (h : α ≃* β) : units α ≃* units β :=
{ to_fun := map h,
  inv_fun := map h.symm,
  left_inv := λ u, ext $ h.left_inv u,
  right_inv := λ u, ext $ h.right_inv u,
  map_mul' := λ a b, units.ext $ h.map_mul a b}

end units

structure ring_equiv (α β : Type*) [ring α] [ring β] extends α ≃ β :=
(hom : is_ring_hom to_fun)

infix ` ≃r `:25 := ring_equiv

namespace ring_equiv

variables [ring α] [ring β] [ring γ]

instance (h : α ≃r β) : is_ring_hom h.to_equiv := h.hom
instance ring_equiv.is_ring_hom' (h : α ≃r β) : is_ring_hom h.to_fun := h.hom

def to_mul_equiv (e : α ≃r β) : α ≃* β :=
{ map_mul' := e.hom.map_mul, .. e.to_equiv }

def to_add_equiv (e : α ≃r β) : α ≃+ β :=
{ map_add' := e.hom.map_add, .. e.to_equiv }

protected def refl (α : Type*) [ring α] : α ≃r α :=
{ hom := is_ring_hom.id, .. equiv.refl α }

protected def symm {α β : Type*} [ring α] [ring β] (e : α ≃r β) : β ≃r α :=
{ hom := { map_one := e.to_mul_equiv.symm.map_one,
           map_mul := e.to_mul_equiv.symm.map_mul,
           map_add := e.to_add_equiv.symm.map_add },
  .. e.to_equiv.symm }

protected def trans {α β γ : Type*} [ring α] [ring β] [ring γ]
  (e₁ : α ≃r β) (e₂ : β ≃r γ) : α ≃r γ :=
{ hom := is_ring_hom.comp _ _, .. e₁.to_equiv.trans e₂.to_equiv  }

instance symm.is_ring_hom {e : α ≃r β} : is_ring_hom e.to_equiv.symm := hom e.symm

@[simp] lemma to_equiv_symm (e : α ≃r β) : e.symm.to_equiv = e.to_equiv.symm := rfl

@[simp] lemma to_equiv_symm_apply (e : α ≃r β) (x : β) :
  e.symm.to_equiv x = e.to_equiv.symm x := rfl

end ring_equiv
