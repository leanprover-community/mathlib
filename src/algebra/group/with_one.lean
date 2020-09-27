/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import algebra.ring.basic

universes u v
variable {α : Type u}

/-- Add an extra element `1` to a type -/
@[to_additive "Add an extra element `0` to a type"]
def with_one (α) := option α

namespace with_one

@[to_additive]
instance : monad with_one := option.monad

@[to_additive]
instance : has_one (with_one α) := ⟨none⟩

@[to_additive]
instance : inhabited (with_one α) := ⟨1⟩

@[to_additive]
instance [nonempty α] : nontrivial (with_one α) := option.nontrivial

@[to_additive]
instance : has_coe_t α (with_one α) := ⟨some⟩

@[to_additive]
lemma some_eq_coe {a : α} : (some a : with_one α) = ↑a := rfl

@[simp, to_additive]
lemma coe_ne_one {a : α} : (a : with_one α) ≠ (1 : with_one α) :=
option.some_ne_none a

@[simp, to_additive]
lemma one_ne_coe {a : α} : (1 : with_one α) ≠ a :=
coe_ne_one.symm

@[to_additive]
lemma ne_one_iff_exists {x : with_one α} : x ≠ 1 ↔ ∃ (a : α), ↑a = x :=
option.ne_none_iff_exists

@[to_additive]
lemma coe_inj {a b : α} : (a : with_one α) = b ↔ a = b :=
option.some_inj

@[elab_as_eliminator, to_additive]
protected lemma cases_on {P : with_one α → Prop} :
  ∀ (x : with_one α), P 1 → (∀ a : α, P a) → P x :=
option.cases_on

@[to_additive]
instance [has_mul α] : has_mul (with_one α) :=
{ mul := option.lift_or_get (*) }

@[to_additive]
instance [semigroup α] : monoid (with_one α) :=
{ mul_assoc := (option.lift_or_get_assoc _).1,
  one_mul   := (option.lift_or_get_is_left_id _).1,
  mul_one   := (option.lift_or_get_is_right_id _).1,
  ..with_one.has_one,
  ..with_one.has_mul }

@[to_additive]
instance [comm_semigroup α] : comm_monoid (with_one α) :=
{ mul_comm := (option.lift_or_get_comm _).1,
  ..with_one.monoid }

section lift

variables [semigroup α] {β : Type v} [monoid β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homorphism.
We have no bundled semigroup homomorphisms, so this function
takes `∀ x y, f (x * y) = f x * f y` as an explicit argument. -/
@[to_additive "Lift an add_semigroup homomorphism `f` to a bundled add_monoid homorphism.
  We have no bundled add_semigroup homomorphisms, so this function
  takes `∀ x y, f (x + y) = f x + f y` as an explicit argument."]
def lift (f : α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
  (with_one α) →* β :=
{ to_fun := λ x, option.cases_on x 1 f,
  map_one' := rfl,
  map_mul' := λ x y,
    with_one.cases_on x (by { rw one_mul, exact (one_mul _).symm }) $ λ x,
    with_one.cases_on y (by { rw mul_one, exact (mul_one _).symm }) $ λ y,
    hf x y }

variables (f : α → β) (hf : ∀ x y, f (x * y) = f x * f y)

@[simp, to_additive]
lemma lift_coe (x : α) : lift f hf x = f x := rfl

@[simp, to_additive]
lemma lift_one : lift f hf 1 = 1 := rfl

@[to_additive]
theorem lift_unique (f : with_one α →* β) : f = lift (f ∘ coe) (λ x y, f.map_mul x y) :=
monoid_hom.ext $ λ x, with_one.cases_on x f.map_one $ λ x, rfl

end lift

section map

variables {β : Type v} [semigroup α] [semigroup β]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `with_one α` to `with_one β` -/
@[to_additive "Given an additive map from `α → β` returns an add_monoid homomorphism
  from `with_zero α` to `with_zero β`"]
def map (f : α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
  with_one α →* with_one β :=
lift (coe ∘ f) (λ x y, coe_inj.2 $ hf x y)

end map

attribute [irreducible] with_one

@[simp, norm_cast, to_additive]
lemma coe_mul [has_mul α] (a b : α) : ((a * b : α) : with_one α) = a * b := rfl

end with_one

namespace with_zero

instance [one : has_one α] : has_one (with_zero α) :=
{ ..one }

lemma coe_one [has_one α] : ((1 : α) : with_zero α) = 1 := rfl

instance [has_mul α] : mul_zero_class (with_zero α) :=
{ mul       := λ o₁ o₂, o₁.bind (λ a, option.map (λ b, a * b) o₂),
  zero_mul  := λ a, rfl,
  mul_zero  := λ a, by cases a; refl,
  ..with_zero.has_zero }

@[simp, norm_cast] lemma coe_mul {α : Type u} [has_mul α]
  {a b : α} : ((a * b : α) : with_zero α) = a * b := rfl

@[simp] lemma zero_mul {α : Type u} [has_mul α]
  (a : with_zero α) : 0 * a = 0 := rfl

@[simp] lemma mul_zero {α : Type u} [has_mul α]
  (a : with_zero α) : a * 0 = 0 := by cases a; refl

instance [semigroup α] : semigroup (with_zero α) :=
{ mul_assoc := λ a b c, match a, b, c with
    | none,   _,      _      := rfl
    | some a, none,   _      := rfl
    | some a, some b, none   := rfl
    | some a, some b, some c := congr_arg some (mul_assoc _ _ _)
    end,
  ..with_zero.mul_zero_class }

instance [comm_semigroup α] : comm_semigroup (with_zero α) :=
{ mul_comm := λ a b, match a, b with
    | none,   _      := (mul_zero _).symm
    | some a, none   := rfl
    | some a, some b := congr_arg some (mul_comm _ _)
    end,
  ..with_zero.semigroup }

instance [monoid α] : monoid_with_zero (with_zero α) :=
{ one_mul := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ one_mul _
    end,
  mul_one := λ a, match a with
    | none   := rfl
    | some a := congr_arg some $ mul_one _
    end,
  ..with_zero.mul_zero_class,
  ..with_zero.has_one,
  ..with_zero.semigroup }

instance [comm_monoid α] : comm_monoid_with_zero (with_zero α) :=
{ ..with_zero.monoid_with_zero, ..with_zero.comm_semigroup }

/-- Given an inverse operation on `α` there is an inverse operation
  on `with_zero α` sending `0` to `0`-/
definition inv [has_inv α] (x : with_zero α) : with_zero α :=
do a ← x, return a⁻¹

instance [has_inv α] : has_inv (with_zero α) := ⟨with_zero.inv⟩

@[simp, norm_cast] lemma coe_inv [has_inv α] (a : α) :
  ((a⁻¹ : α) : with_zero α) = a⁻¹ := rfl

@[simp] lemma inv_zero [has_inv α] :
  (0 : with_zero α)⁻¹ = 0 := rfl

section group
variables [group α]

@[simp] lemma inv_one : (1 : with_zero α)⁻¹ = 1 :=
show ((1⁻¹ : α) : with_zero α) = 1, by simp [coe_one]

/-- A division operation on `with_zero α` when `α` has an inverse operation -/
definition div (x y : with_zero α) : with_zero α :=
x * y⁻¹

instance : has_div (with_zero α) := ⟨with_zero.div⟩

@[simp] lemma zero_div (a : with_zero α) : 0 / a = 0 := rfl
@[simp] lemma div_zero (a : with_zero α) : a / 0 = 0 := by change a * _ = _; simp

lemma div_coe (a b : α) : (a : with_zero α) / b = (a * b⁻¹ : α) := rfl

lemma one_div (x : with_zero α) : 1 / x = x⁻¹ := one_mul _

@[simp] lemma div_one : ∀ (x : with_zero α), x / 1 = x
| 0       := rfl
| (a : α) := show _ * _ = _, by simp

@[simp] lemma mul_right_inv : ∀  (x : with_zero α) (h : x ≠ 0), x * x⁻¹ = 1
| 0       h := false.elim $ h rfl
| (a : α) h := by {norm_cast, simp [coe_one]}

@[simp] lemma mul_left_inv : ∀  (x : with_zero α) (h : x ≠ 0), x⁻¹ * x = 1
| 0       h := false.elim $ h rfl
| (a : α) h := by {norm_cast, simp [coe_one]}

@[simp] lemma mul_inv_rev : ∀ (x y : with_zero α), (x * y)⁻¹ = y⁻¹ * x⁻¹
| 0       0       := rfl
| 0       (b : α) := rfl
| (a : α) 0       := rfl
| (a : α) (b : α) := by {norm_cast, exact _root_.mul_inv_rev _ _}

@[simp] lemma mul_div_cancel {a b : with_zero α} (hb : b ≠ 0) : a * b / b = a :=
show _ * _ * _ = _, by simp [mul_assoc, hb]

@[simp] lemma div_mul_cancel {a b : with_zero α} (hb : b ≠ 0) : a / b * b = a :=
show _ * _ * _ = _, by simp [mul_assoc, hb]

lemma div_eq_iff_mul_eq {a b c : with_zero α} (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
by split; intro h; simp [h.symm, hb]

lemma mul_inv_cancel : ∀ (a : with_zero α), a ≠ 0 → a * a⁻¹ = 1 :=
begin
  rintro (_ | a) h,
    {exact absurd rfl h },
    { refine option.some_inj.2 (_root_.mul_right_inv _) }
end

/-- if `G` is a group then `with_zero G` is a group with zero. -/
instance : group_with_zero (with_zero α) :=
{ inv_zero := with_zero.inv_zero,
  mul_inv_cancel := with_zero.mul_inv_cancel,
  ..with_zero.monoid_with_zero,
  ..with_zero.has_inv,
  ..with_zero.nontrivial }
end group

section comm_group
variables [comm_group α] {a b c d : with_zero α}

lemma div_eq_div (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = b * c :=
begin
  rw ne_zero_iff_exists at hb hd,
  rcases hb with ⟨b, rfl⟩,
  rcases hd with ⟨d, rfl⟩,
  induction a using with_zero.cases_on;
  induction c using with_zero.cases_on,
  { refl },
  { simp [div_coe] },
  { simp [div_coe] },
  erw [with_zero.coe_inj, with_zero.coe_inj],
  show a * b⁻¹ = c * d⁻¹ ↔ a * d = b * c,
  split; intro H,
  { rw mul_inv_eq_iff_eq_mul at H,
    rw [H, mul_right_comm, inv_mul_cancel_right, mul_comm] },
  { rw [mul_inv_eq_iff_eq_mul, mul_right_comm, mul_comm c, ← H, mul_inv_cancel_right] }
end

theorem mul_comm {α : Type u}
  [comm_group α] :
  ∀ (a b : with_zero α), a * b = b * a :=
begin
  rintro (_ | a) (_ | b),
  { refl },
  { refl },
  { refl },
  { apply option.some_inj.2,
    apply mul_comm }
end

/-- if `G` is a `comm_group` then `with_zero G` is a `comm_group_with_zero`. -/
instance : comm_group_with_zero (with_zero α) :=
{ mul_comm := mul_comm,
  ..with_zero.group_with_zero }

end comm_group

section semiring

instance [semiring α] : semiring (with_zero α) :=
{ left_distrib := λ a b c, begin
    cases a with a, {refl},
    cases b with b; cases c with c; try {refl},
    exact congr_arg some (left_distrib _ _ _)
  end,
  right_distrib := λ a b c, begin
    cases c with c,
    { change (a + b) * 0 = a * 0 + b * 0, simp },
    cases a with a; cases b with b; try {refl},
    exact congr_arg some (right_distrib _ _ _)
  end,
  ..with_zero.add_comm_monoid,
  ..with_zero.mul_zero_class,
  ..with_zero.monoid_with_zero }

end semiring

attribute [irreducible] with_zero

end with_zero
