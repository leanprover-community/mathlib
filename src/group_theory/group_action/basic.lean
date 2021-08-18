/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.defs
import group_theory.group_action.group
import group_theory.coset

/-!
# Basic properties of group actions
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open_locale big_operators
open function

namespace mul_action

variables (α) [monoid α] [mul_action α β]

/-- The orbit of an element under an action. -/
def orbit (b : β) := set.range (λ x : α, x • b)

variable {α}

lemma mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
iff.rfl

@[simp] lemma mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
⟨x, rfl⟩

@[simp] lemma mem_orbit_self (b : β) : b ∈ orbit α b :=
⟨1, by simp [mul_action.one_smul]⟩

variables (α) (β)

/-- The set of elements fixed under the whole action. -/
def fixed_points : set β := {b : β | ∀ x : α, x • b = b}

/-- `fixed_by g` is the subfield of elements fixed by `g`. -/
def fixed_by (g : α) : set β :=
{ x | g • x = x }

theorem fixed_eq_Inter_fixed_by : fixed_points α β = ⋂ g : α, fixed_by α β g :=
set.ext $ λ x, ⟨λ hx, set.mem_Inter.2 $ λ g, hx g, λ hx g, by exact (set.mem_Inter.1 hx g : _)⟩

variables {α} (β)

@[simp] lemma mem_fixed_points {b : β} :
  b ∈ fixed_points α β ↔ ∀ x : α, x • b = b := iff.rfl

@[simp] lemma mem_fixed_by {g : α} {b : β} :
  b ∈ fixed_by α β g ↔ g • b = b := iff.rfl

lemma mem_fixed_points' {b : β} : b ∈ fixed_points α β ↔
  (∀ b', b' ∈ orbit α b → b' = b) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, h _ (mem_orbit _ _)⟩

variables (α) {β}

/-- The stabilizer of a point `b` as a submonoid of `α`. -/
def stabilizer.submonoid (b : β) : submonoid α :=
{ carrier := { a | a • b = b },
  one_mem' := one_smul _ b,
  mul_mem' := λ a a' (ha : a • b = b) (hb : a' • b = b),
    show (a * a') • b = b, by rw [←smul_smul, hb, ha] }

@[simp] lemma mem_stabilizer_submonoid_iff {b : β} {a : α} :
  a ∈ stabilizer.submonoid α b ↔ a • b = b := iff.rfl

end mul_action

namespace mul_action
variable (α)
variables [group α] [mul_action α β]

/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
def stabilizer (b : β) : subgroup α :=
{ inv_mem' := λ a (ha : a • b = b), show a⁻¹ • b = b, by rw [inv_smul_eq_iff, ha]
  ..stabilizer.submonoid α b }

variables {α} {β}

@[simp] lemma mem_stabilizer_iff {b : β} {a : α} :
  a ∈ stabilizer α b ↔ a • b = b := iff.rfl

lemma orbit_eq_iff {a b : β} :
   orbit α a = orbit α b ↔ a ∈ orbit α b:=
⟨λ h, h ▸ mem_orbit_self _,
λ ⟨x, (hx : x • b = a)⟩, set.ext (λ c, ⟨λ ⟨y, (hy : y • a = c)⟩, ⟨y * x,
  show (y * x) • b = c, by rwa [mul_action.mul_smul, hx]⟩,
  λ ⟨y, (hy : y • b = c)⟩, ⟨y * x⁻¹,
    show (y * x⁻¹) • a = c, by
      conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
        mul_action.mul_smul, hx]}⟩⟩)⟩

lemma mem_fixed_points_iff_card_orbit_eq_one {a : β}
  [fintype (orbit α a)] : a ∈ fixed_points α β ↔ fintype.card (orbit α a) = 1 :=
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { exact λ h, ⟨⟨a, mem_orbit_self _⟩, λ ⟨b, ⟨x, hx⟩⟩, subtype.eq $ by simp [h x, hx.symm]⟩ },
  { assume h x,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    exact calc x • a = z : subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      ... = a : (subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm }
end

variables (α) {β}

@[simp] lemma mem_orbit_smul (g : α) (a : β) : a ∈ orbit α (g • a) :=
⟨g⁻¹, by simp⟩

@[simp] lemma smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ orbit α (h • a) :=
⟨g * h⁻¹, by simp [mul_smul]⟩

variables (α) (β)
/-- The relation "in the same orbit". -/
def orbit_rel : setoid β :=
{ r := λ a b, a ∈ orbit α b,
  iseqv := ⟨mem_orbit_self, λ a b, by simp [orbit_eq_iff.symm, eq_comm],
    λ a b, by simp [orbit_eq_iff.symm, eq_comm] {contextual := tt}⟩ }

variables {α β}

open quotient_group

/-- Action on left cosets. -/
def mul_left_cosets (H : subgroup α)
  (x : α) (y : quotient H) : quotient H :=
quotient.lift_on' y (λ y, quotient_group.mk ((x : α) * y))
  (λ a b (hab : _ ∈ H), quotient_group.eq.2
    (by rwa [mul_inv_rev, ← mul_assoc, mul_assoc (a⁻¹), inv_mul_self, mul_one]))

instance quotient (H : subgroup α) : mul_action α (quotient H) :=
{ smul := mul_left_cosets H,
  one_smul := λ a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [subgroup.one_mem])),
  mul_smul := λ x y a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [mul_inv_rev, subgroup.one_mem, mul_assoc])) }

@[simp] lemma quotient.smul_mk (H : subgroup α) (a x : α) :
  (a • quotient_group.mk x : quotient_group.quotient H) = quotient_group.mk (a * x) := rfl

@[simp] lemma quotient.smul_coe (H : subgroup α) (a x : α) :
  (a • x : quotient_group.quotient H) = ↑(a * x) := rfl

instance mul_left_cosets_comp_subtype_val (H I : subgroup α) :
  mul_action I (quotient H) :=
mul_action.comp_hom (quotient H) (subgroup.subtype I)

variables (α) {β} (x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
def of_quotient_stabilizer (g : quotient (mul_action.stabilizer α x)) : β :=
quotient.lift_on' g (•x) $ λ g1 g2 H,
calc  g1 • x
    = g1 • (g1⁻¹ * g2) • x : congr_arg _ H.symm
... = g2 • x : by rw [smul_smul, mul_inv_cancel_left]

@[simp] theorem of_quotient_stabilizer_mk (g : α) :
  of_quotient_stabilizer α x (quotient_group.mk g) = g • x :=
rfl

theorem of_quotient_stabilizer_mem_orbit (g) : of_quotient_stabilizer α x g ∈ orbit α x :=
quotient.induction_on' g $ λ g, ⟨g, rfl⟩

theorem of_quotient_stabilizer_smul (g : α) (g' : quotient (mul_action.stabilizer α x)) :
  of_quotient_stabilizer α x (g • g') = g • of_quotient_stabilizer α x g' :=
quotient.induction_on' g' $ λ _, mul_smul _ _ _

theorem injective_of_quotient_stabilizer : function.injective (of_quotient_stabilizer α x) :=
λ y₁ y₂, quotient.induction_on₂' y₁ y₂ $ λ g₁ g₂ (H : g₁ • x = g₂ • x), quotient.sound' $
show (g₁⁻¹ * g₂) • x = x, by rw [mul_smul, ← H, inv_smul_smul]

/-- Orbit-stabilizer theorem. -/
noncomputable def orbit_equiv_quotient_stabilizer (b : β) :
  orbit α b ≃ quotient (stabilizer α b) :=
equiv.symm $ equiv.of_bijective
  (λ g, ⟨of_quotient_stabilizer α b g, of_quotient_stabilizer_mem_orbit α b g⟩)
  ⟨λ x y hxy, injective_of_quotient_stabilizer α b (by convert congr_arg subtype.val hxy),
  λ ⟨b, ⟨g, hgb⟩⟩, ⟨g, subtype.eq hgb⟩⟩

@[simp] theorem orbit_equiv_quotient_stabilizer_symm_apply (b : β) (a : α) :
  ((orbit_equiv_quotient_stabilizer α b).symm a : β) = a • b :=
rfl

@[simp] lemma stabilizer_quotient {G} [group G] (H : subgroup G) :
  mul_action.stabilizer G ((1 : G) : quotient H) = H :=
by { ext, simp [quotient_group.eq] }

section draft

def equiv.sigma_assoc {α : Sort*} {β : α → Sort*} (γ : Π (a : α), β a → Sort*) :
  (Σ (ab : Σ (a : α), β a), γ ab.1 ab.2) ≃ Σ (a : α), (Σ (b : β a), γ a b) :=
{ to_fun := λ x, ⟨x.1.1, ⟨x.1.2, x.2⟩⟩,
  inv_fun := λ x, ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
  left_inv := λ ⟨⟨a, b⟩, c⟩, rfl,
  right_inv := λ ⟨a, ⟨b, c⟩⟩, rfl }

local notation `Ω` := (quotient $ orbit_rel α β)

noncomputable def goal : (Σ (a : α), (fixed_by α β a)) ≃ Ω × α :=
let
  e₀ : (Σ (a : α), fixed_by α β a) ≃ {ab : α × β // ab.1 • ab.2 = ab.2} :=
    (equiv.subtype_prod_equiv_sigma_subtype _).symm,
  e₁ : {ab : α × β // ab.1 • ab.2 = ab.2} ≃ {ba : β × α // ba.2 • ba.1 = ba.1} :=
    (equiv.prod_comm α β).subtype_equiv (λ ab, iff.rfl),
  e₂ : {ba : β × α // ba.2 • ba.1 = ba.1} ≃ Σ (b : β), stabilizer α b :=
    equiv.subtype_prod_equiv_sigma_subtype (λ (b : β) a, a ∈ stabilizer α b),
  tmp₀ : β ≃ Σ (ω : Ω), {b // quotient.mk' b = ω} :=
    (equiv.sigma_preimage_equiv quotient.mk').symm,
  e₃ : (Σ (b : β), stabilizer α b) ≃
        Σ (ωb : (Σ (ω : Ω), {b // quotient.mk' b = ω})), stabilizer α (ωb.2 : β) :=
    tmp₀.sigma_congr_left',
  e₄ : (Σ (ωb : (Σ (ω : Ω), {b // quotient.mk' b = ω})), stabilizer α (ωb.2 : β)) ≃
        Σ (ω : Ω), (Σ (b : {b // quotient.mk' b = ω}), stabilizer α (b : β)) :=
    equiv.sigma_assoc (λ (ω : Ω) (b : {b // quotient.mk' b = ω}), stabilizer α (b : β)),
  e₅ : (Σ (ω : Ω), (Σ (b : {b // quotient.mk' b = ω}), stabilizer α (b : β))) ≃
        Σ (ω : Ω), (Σ (b : {b // quotient.mk' b = ω}), stabilizer α (quotient.out' ω)) :=
    sorry,
  e₆ : (Σ (ω : Ω), (Σ (b : {b // quotient.mk' b = ω}), stabilizer α (quotient.out' ω))) ≃
        Σ (ω : Ω), {b // quotient.mk' b = ω} × stabilizer α (quotient.out' ω) :=
    sorry,
  e₇ : (Σ (ω : Ω), {b // quotient.mk' b = ω} × stabilizer α (quotient.out' ω)) ≃
        Σ (ω : Ω), orbit α (quotient.out' ω) × stabilizer α (quotient.out' ω) :=
    sorry,
  e₈ : (Σ (ω : Ω), orbit α (quotient.out' ω) × stabilizer α (quotient.out' ω)) ≃
        Σ (ω : Ω), quotient (stabilizer α $ quotient.out' ω) × stabilizer α (quotient.out' ω) :=
    equiv.sigma_congr_right
      (λ ω, equiv.prod_congr (orbit_equiv_quotient_stabilizer α _) (equiv.refl _)),
  e₉ : (Σ (ω : Ω), quotient (stabilizer α $ quotient.out' ω) × stabilizer α (quotient.out' ω)) ≃
        Σ (ω : Ω), α :=
    sorry,
  e₁₀ : (Σ (ω : Ω), α) ≃ Ω × α :=
    sorry
in e₀.trans $ e₁.trans $ e₂.trans $ e₃.trans $ e₄.trans $ e₅.trans $ e₆.trans $ e₇.trans $ e₈.trans $
  e₉.trans $ e₁₀

end draft

end mul_action

section
variables [monoid α] [add_monoid β] [distrib_mul_action α β]

lemma list.smul_sum {r : α} {l : list β} :
  r • l.sum = (l.map ((•) r)).sum :=
(const_smul_hom β r).map_list_sum l

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `is_smul_regular`.
The typeclass that restricts all terms of `M` to have this property is `no_zero_smul_divisors`. -/
lemma smul_cancel_of_non_zero_divisor {M R : Type*} [monoid M] [ring R] [distrib_mul_action M R]
  (k : M) (h : ∀ (x : R), k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) :
  a = b :=
begin
  rw ←sub_eq_zero,
  refine h _ _,
  rw [smul_sub, h', sub_self]
end

end

section
variables [monoid α] [add_comm_monoid β] [distrib_mul_action α β]

lemma multiset.smul_sum {r : α} {s : multiset β} :
  r • s.sum = (s.map ((•) r)).sum :=
(const_smul_hom β r).map_multiset_sum s

lemma finset.smul_sum {r : α} {f : γ → β} {s : finset γ} :
  r • ∑ x in s, f x = ∑ x in s, r • f x :=
(const_smul_hom β r).map_sum f s

end

/-- `G` acts pretransitively on `X` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `X` nonempty. -/
class is_pretransitive (G X) [monoid G] [mul_action G X] : Prop :=
(exists_smul_eq : ∀ x y : X, ∃ g : G, g • x = y)

lemma exists_smul_eq (M) {X} [monoid M] [mul_action M X] [is_pretransitive M X] (x y : X) :
  ∃ m : M, m • x = y := is_pretransitive.exists_smul_eq x y

instance is_pretransitive_quotient (G) [group G] (H : subgroup G) :
  is_pretransitive G (quotient_group.quotient H) :=
{ exists_smul_eq := begin
    rintros ⟨x⟩ ⟨y⟩,
    refine ⟨y * x⁻¹, quotient_group.eq.mpr _⟩,
    simp only [H.one_mem, mul_left_inv, inv_mul_cancel_right],
  end }
