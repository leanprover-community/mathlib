/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import algebra.order.group
import algebra.order.with_zero
import group_theory.subsemigroup.operations
import group_theory.order_of_element
import tactic.tfae

/-!
# Formalization of linear extensions to partially ordered semigroups

Following [PARTIALLY ORDERED ABELIAN SEMIGROUPS]
(https://eprints.lib.hokudai.ac.jp/dspace/bitstream/2115/55970/1/JFSHIU_11_N4_181-189.pdf)
-/

open function (swap)

section page181

variables (S : Type*) [has_mul S] [has_le S]

-- Definition 1
@[to_additive add_nakada_po]
abbreviation nakada_po : Prop :=
covariant_class S S (*) (≤)

variables {S}

@[to_additive add_homogeneity]
lemma homogeneity [nakada_po S] {a b : S} (h : a ≤ b) (c : S) :
  c * a ≤ c * b :=
mul_le_mul_left' h c

@[to_additive]
lemma nakada_po.comap {S S' : Type*} [has_mul S] [has_le S] [has_mul S'] [has_le S']
  [nakada_po S] (f : S' → S) (hrel : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
  (hmul : ∀ x y, f (x * y) = f x * f y):
  nakada_po S' :=
⟨λ a b c h, by { rw [←hrel, hmul, hmul], exact homogeneity (hrel.mpr h) _ }⟩

variables (S)

-- Definition 2
@[to_additive add_nakada_strong]
abbreviation nakada_strong : Prop :=
contravariant_class S S (*) (≤)

variables {S}

@[to_additive add_strong]
lemma strong [nakada_strong S] {a b c : S} (h : a * b ≤ a * c) : b ≤ c :=
le_of_mul_le_mul_left' h

@[to_additive]
lemma nakada_strong.comap {S S' : Type*} [has_mul S] [has_le S] [has_mul S'] [has_le S']
  [nakada_strong S] (f : S' → S) (hrel : ∀ {x y}, f x ≤ f y ↔ x ≤ y)
  (hmul : ∀ x y, f (x * y) = f x * f y):
  nakada_strong S' :=
⟨λ a b c h, by { rw [←hrel] at h ⊢, rw [hmul, hmul] at h, exact strong h }⟩

-- Theorem 1
@[priority 10, to_additive add_group.add_nakada_strong]
instance group.nakada_strong {G : Type*} [group G] [has_le G] [nakada_po G] :
  nakada_strong G :=
⟨λ c a b h, by simpa using homogeneity h c⁻¹⟩

end page181

section page182

variables {S : Type*} [has_mul S] [partial_order S]

-- Theorem 2.1
@[to_additive]
lemma nakada_strong.cancel_left [nakada_strong S] {a b c : S} (h : a * b = a * c) :
  b = c :=
le_antisymm (strong h.le) (strong h.ge)

-- Theorem 2.2
@[to_additive]
instance nakada_strong.contravariant_mul_lt [nakada_strong S] :
  contravariant_class S S (*) (<) :=
⟨λ a b c h, begin
  by_cases H : b = c,
  { simpa [H] using h },
  { simpa [lt_iff_le_and_ne, H] using strong h.le }
end⟩

-- Theorem 2.3
@[to_additive add_nakada_po.covariant_add_lt_of_add_nakada_strong]
instance nakada_po.covariant_mul_lt_of_nakada_strong [nakada_po S] [nakada_strong S] :
  covariant_class S S (*) (<) :=
⟨λ a b c h, begin
  by_cases H : a * b = a * c,
  { rw [nakada_strong.cancel_left H] at h,
    exact absurd h (lt_irrefl _) },
  { simpa [lt_iff_le_and_ne, H] using homogeneity h.le c }
end⟩

-- Theorem 3.1
@[to_additive add_nakada_lo.contravariant_add_lt]
instance nakada_lo.contravariant_mul_lt {S : Type*} [has_mul S] [linear_order S] [nakada_po S] :
  contravariant_class S S (*) (<) :=
⟨λ a b c h, begin
  refine (le_or_lt _ _).resolve_left (λ H, _),
  exact absurd (homogeneity H a) h.not_le
end⟩

-- extra api
attribute [to_additive nsmul_le_nsmul_of_le] pow_le_pow_of_le

-- Theorem 3.2
@[to_additive nsmul_lt_nsmul_cancel]
lemma pow_lt_pow_cancel {S : Type*} [comm_monoid S] [linear_order S] [nakada_po S] {a b : S} {n : ℕ}
  (h : a ^ n < b ^ n) : a < b :=
begin
  refine (le_or_lt _ _).resolve_left (λ H, _),
  exact absurd (pow_le_pow_of_le H) h.not_le,
end

-- Theorem 4
lemma nakada_lo.tfae {S : Type*} [has_mul S] [linear_order S] [nakada_po S] :
  tfae [∀ {a b c : S}, a * b ≤ a * c → b ≤ c,
        ∀ {a b c : S}, a * b = a * c → b = c,
        ∀ {a b : S} (h : a < b) (c : S), c * a < c * b] :=
begin
  tfae_have : 1 → 2,
  { intros H a b c h,
    haveI : nakada_strong S := ⟨λ _ _ _, H⟩,
    exact nakada_strong.cancel_left h },
  tfae_have : 2 → 3,
  { intros H a b h c,
    refine lt_of_le_of_ne (homogeneity h.le c) (λ he, _),
    simpa [H he] using h },
  tfae_have : 3 → 1,
  { intros H a b c,
    contrapose!,
    exact λ h, H h a },
  tfae_finish
end

-- Definition 3
@[ext]
structure add_order_embedding (S S' : Type*) [has_add S] [has_le S] [has_add S'] [has_le S'] extends
  add_hom S S' :=
(inj' : function.injective to_fun)
(map_rel_iff' : ∀ {a b : S}, (to_fun a) ≤ (to_fun b) ↔ a ≤ b)

@[ext, to_additive]
structure mul_order_embedding (S S' : Type*) [has_mul S] [has_le S] [has_mul S'] [has_le S'] extends
  mul_hom S S' :=
(inj' : function.injective to_fun)
(map_rel_iff' : ∀ {a b : S}, (to_fun a) ≤ (to_fun b) ↔ a ≤ b)

namespace mul_order_embedding

variables {M N F : Type*} [has_mul M] [has_le M] [has_mul N] [has_le N]

infix ` ↪*o `:25 := mul_order_embedding
infix ` ↪+o `:25 := mul_order_embedding

@[to_additive]
instance : has_coe_to_fun (M ↪*o N) (λ _, M → N) := ⟨λ e, e.to_mul_hom⟩

@[to_additive]
def to_order_embedding (e : M ↪*o N) : M ↪o N := { ..e }

@[refl, to_additive]
def refl (M : Type*) [has_mul M] [has_le M] : M ↪*o M :=
{ map_mul' := λ _ _, rfl,
  ..rel_embedding.refl _ }

@[to_additive]
instance : inhabited (M ↪*o M) := ⟨refl M⟩

@[simp, to_additive]
lemma coe_to_mul_hom (e : M ↪*o N) : (e.to_mul_hom : M → N) = e := rfl

@[simp, to_additive]
lemma coe_to_order_embedding (e : M ↪*o N) : (e.to_order_embedding : M → N) = e := rfl

@[to_additive]
lemma injective (e : M ↪*o N) : function.injective e := e.to_order_embedding.injective

@[to_additive]
instance : mul_hom_class (M ↪*o N) M N :=
{ coe := λ e, e,
  coe_injective' := λ f g h, by { ext, exact congr_fun h _ },
  map_mul := λ e, e.map_mul' }

@[to_additive]
instance {M N : Type*} [has_mul M] [preorder M] [has_mul N] [preorder N] :
  order_hom_class (M ↪*o N) M N :=
{ coe := λ e, e,
  coe_injective' := λ f g h, by { ext x, exact congr_fun h x },
  map_rel := λ e a b, (@mul_order_embedding.map_rel_iff' _ _ _ _ _ _ _ _ _).mpr }

@[simp, to_additive]
lemma map_le_iff (e : M ↪*o N) {a b : M} :
  e a ≤ e b ↔ a ≤ b :=
@mul_order_embedding.map_rel_iff' _ _ _ _ _ _ _ _ _

@[simp, to_additive]
lemma map_lt_iff {M N : Type*} [has_mul M] [preorder M] [has_mul N] [preorder N]
  (e : M ↪*o N) {a b : M} : e a < e b ↔ a < b :=
by simp [lt_iff_le_not_le]

@[to_additive]
protected def comp {M N P : Type*} [has_mul M] [has_le M] [has_mul N] [has_le N]
  [has_mul P] [has_le P] (f : N ↪*o P) (g : M ↪*o N) : M ↪*o P :=
{ inj' := f.injective.comp g.injective,
  map_rel_iff' := by simp,
  ..f.to_mul_hom.comp g.to_mul_hom, }

@[simp, to_additive]
lemma comp_apply {M N P : Type*} [has_mul M] [has_le M] [has_mul N] [has_le N]
  [has_mul P] [has_le P] (f : N ↪*o P) (g : M ↪*o N) (x : M) :
  f.comp g x = f (g x) := rfl

@[to_additive]
protected def coe (S : subsemigroup M) {hl : has_le S} (h : ∀ (x y : S), x ≤ y ↔ (x : M) ≤ y) :
  S ↪*o M :=
{ to_fun := coe,
  map_mul' := subsemigroup.coe_mul _,
  inj' := subtype.coe_injective,
  map_rel_iff' := λ _ _, (h _ _).symm }

@[simp, to_additive]
lemma coe_apply {S : subsemigroup M} {hl : has_le S}
  (h : ∀ (x y : S), x ≤ y ↔ (x : M) ≤ y) (x : S) :
  mul_order_embedding.coe S h x = coe x := rfl

end mul_order_embedding

@[ext]
structure add_order_iso (S S' : Type*) [has_add S] [has_le S] [has_add S'] [has_le S'] extends
  S ≃+ S' :=
(map_rel_iff' : ∀ {a b : S}, (to_fun a) ≤ (to_fun b) ↔ a ≤ b)

@[ext, to_additive]
structure mul_order_iso (S S' : Type*) [has_mul S] [has_le S] [has_mul S'] [has_le S'] extends
  S ≃* S' :=
(map_rel_iff' : ∀ {a b : S}, (to_fun a) ≤ (to_fun b) ↔ a ≤ b)

namespace mul_order_iso

variables {M N : Type*} [has_mul M] [has_le M] [has_mul N] [has_le N]

infix ` ≃*o `:25 := mul_order_iso
infix ` ≃+o `:25 := add_order_iso

@[to_additive]
instance : has_coe_to_fun (M ≃*o N) (λ _, M → N) := ⟨λ e, e.to_mul_equiv⟩

@[to_additive]
def to_order_iso (e : M ≃*o N) : M ≃o N := { ..e }

@[refl, to_additive]
def refl (M : Type*) [has_mul M] [has_le M] : M ≃*o M :=
{ ..mul_equiv.refl _, ..order_iso.refl _ }

@[to_additive]
instance : inhabited (M ≃*o M) := ⟨refl M⟩

@[symm, to_additive]
def symm (e : M ≃*o N) : N ≃*o M :=
{ ..e.to_mul_equiv.symm, ..e.to_order_iso.symm }

@[simp, to_additive]
lemma inv_fun_eq_symm (e : M ≃*o N) : e.inv_fun = e.symm := rfl

@[simp, to_additive]
lemma coe_to_mul_equiv (e : M ≃*o N) : (e.to_mul_equiv : M → N) = e := rfl

@[simp, to_additive]
lemma symm_apply_apply (e : M ≃*o N) (x : M) : e.symm (e x) = x :=
e.to_mul_equiv.symm_apply_apply x

@[simp, to_additive]
lemma apply_symm_apply (e : M ≃*o N) (y : N) : e (e.symm y) = y :=
e.to_mul_equiv.apply_symm_apply y

@[to_additive]
lemma injective (e : M ≃*o N) : function.injective e := e.to_mul_equiv.injective

@[to_additive]
instance : mul_equiv_class (M ≃*o N) M N :=
{ coe := λ e, e, inv := λ e, e.symm,
  left_inv := λ e, e.to_mul_equiv.left_inv,
  right_inv := λ e, e.to_mul_equiv.right_inv,
  coe_injective' := λ f g h₁ h₂, by { ext x, exact congr_fun h₁ x },
  map_mul := λ e, e.map_mul' }

@[to_additive]
instance {M N : Type*} [has_mul M] [preorder M] [has_mul N] [preorder N] :
  order_hom_class (M ≃*o N) M N :=
{ coe := λ e, e,
  coe_injective' := λ f g h, by { ext x, exact congr_fun h x },
  map_rel := λ e a b, (@mul_order_iso.map_rel_iff' _ _ _ _ _ _ _ _ _).mpr }

@[to_additive]
instance : order_iso_class (M ≃*o N) M N :=
{ map_le_map_iff := mul_order_iso.map_rel_iff' }

@[to_additive]
instance mul_order_iso.order_hom_class_rev {M N : Type*} [has_mul M] [preorder M]
  [has_mul N] [preorder N] :
  order_hom_class (M ≃*o N) N M :=
{ coe := λ e, e.symm,
  coe_injective' := λ f g h, by { ext x, have := congr_fun h (g x),
    apply f.symm.to_mul_equiv.injective,
    simp_rw coe_to_mul_equiv at this ⊢,
    simp [this] },
  map_rel := λ e a b, (@mul_order_iso.map_rel_iff' _ _ _ _ _ _ _ _ _).mpr }

@[simp, to_additive]
lemma map_lt_iff {M N : Type*} [has_mul M] [preorder M] [has_mul N] [preorder N]
  (e : M ≃*o N) {a b : M} : e a < e b ↔ a < b :=
by simp [lt_iff_le_not_le]

-- how does `simps` work?
@[to_additive]
def to_mul_order_embedding (e : M ≃*o N) : M ↪*o N :=
{ inj' := equiv_like.injective e, ..e }

@[simp, to_additive]
lemma coe_to_order_iso (e : M ≃*o N) : (e.to_order_iso : M → N) = e := rfl

@[simp, to_additive]
lemma coe_to_mul_order_embedding (e : M ≃*o N) : (e.to_mul_order_embedding : M → N) = e := rfl

@[to_additive]
def of_mul_order_embedding (f : M ↪*o N) (g : N ↪*o M) (h : function.left_inverse f g) :
  M ≃*o N :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ x, f.to_order_embedding.injective (h (f x)),
  right_inv := h,
  map_mul' := map_mul _,
  map_rel_iff' := f.map_rel_iff' }

end mul_order_iso

-- Theorem 5 (by Theorem 1, we don't need to state that `G` is a group)
@[to_additive add_strong_of_add_order_embedding]
lemma strong_of_mul_order_embedding {S G : Type*} [comm_semigroup S] [has_le S]
  [comm_semigroup G] [has_le G] [nakada_po G] [nakada_strong G] (f : S ↪*o G) : nakada_strong S :=
⟨λ a b c h, begin
  rw ←f.map_rel_iff' at h ⊢,
  simpa using h
end⟩

end page182

section page183

variables {S : Type*} [comm_semigroup S] [partial_order S] [nakada_strong S]

variables (S)
-- we twist the multiplication to simplify refl and symm proofs
-- the definition is equivalent due to the commutativity assumption
@[to_additive]
def mul_pair_setoid : setoid (S × S) :=
{ r := λ p q, p.1 * q.2 = q.1 * p.2,
  iseqv := begin
    refine ⟨λ _, rfl, λ _ _, eq.symm, _⟩,
    intros p q r h h',
    have := congr_arg ((*) p.snd) h',
    rw [mul_left_comm, ←mul_assoc, ←h, mul_comm _ q.snd, mul_comm _ q.snd, ←mul_left_comm,
        mul_assoc] at this,
    rw [nakada_strong.cancel_left this, mul_comm],
  end }

variables {S}

local attribute [instance] mul_pair_setoid

@[simp, to_additive]
lemma mul_pair_equiv_iff (p q : S × S) : p ≈ q ↔ p.1 * q.2 = q.1 * p.2 := iff.rfl

@[to_additive]
lemma mul_pair_left_eq (p : S × S) (x : S) : ⟦(x * p.1, x * p.2)⟧ = ⟦p⟧ :=
by simp only [quotient.eq, mul_pair_equiv_iff, mul_assoc, mul_comm, mul_left_comm]

@[to_additive]
lemma mul_pair_right_eq (p : S × S) (x : S) : ⟦(p.1 * x, p.2 * x)⟧ = ⟦p⟧ :=
by simp only [quotient.eq, mul_pair_equiv_iff, mul_assoc, mul_comm, mul_left_comm]

namespace pair_quotient

local notation `G` := quotient (mul_pair_setoid S)

@[to_additive]
protected def mul : G → G → G :=
quotient.map₂ (*) begin
  rintro ⟨a, a'⟩ ⟨c, c'⟩ hac ⟨b, b'⟩ ⟨d, d'⟩ hbd,
  simp only [mul_pair_equiv_iff, quotient.eq, prod.mk_mul_mk] at hac hbd ⊢,
  rw [mul_left_comm, ←mul_assoc, ←mul_assoc, mul_assoc, hbd, mul_comm c', hac],
  simp [mul_left_comm, mul_assoc, mul_comm]
end

@[to_additive]
instance : has_mul G := ⟨pair_quotient.mul⟩

-- thanks to Eric Wieser who says
-- "The elaborator can't infer the implicit arguments correctly for you
--  unless you unfold things in the right order for it, it seems"
@[simp, to_additive] lemma mk_mul : ∀ (p q : S × S), ⟦p⟧ * ⟦q⟧ = ⟦(p.1 * q.1, p.2 * q.2)⟧ :=
(quotient.map₂_mk _ _ : ∀ p q : S × S, pair_quotient.mul ⟦p⟧ ⟦q⟧ = _)

@[to_additive]
protected lemma mul_comm (x y : G) : x * y = y * x :=
quotient.induction_on₂ x y $ by { intros, simp [mul_comm, mul_assoc, mul_left_comm] }

@[to_additive]
protected lemma mul_assoc (x y z : G) : x * y * z = x * (y * z) :=
quotient.induction_on₃ x y z $ by { intros, simp [mul_comm, mul_assoc, mul_left_comm] }

@[to_additive]
instance comm_semigroup : comm_semigroup G :=
{ mul := (*),
  mul_assoc := pair_quotient.mul_assoc,
  mul_comm := pair_quotient.mul_comm }

@[to_additive]
protected def inv : G → G :=
quotient.map prod.swap $ λ _ _, by simp [mul_comm, eq_comm]

@[to_additive]
instance has_inv : has_inv G := ⟨pair_quotient.inv⟩

@[simp, to_additive] lemma inv_mk (p : S × S) : ⟦p⟧⁻¹ = ⟦p.swap⟧ := rfl

@[to_additive]
lemma mul_rev_inv_eq (x y : G) : x * x⁻¹ = y * y⁻¹ :=
quotient.induction_on₂ x y $ by { intros, simp [mul_comm] }

@[to_additive]
def one (x : S) : G := ⟦(x, x)⟧

@[to_additive]
lemma one_eq (x y : S) : one x = one y :=
by simp [one, mul_comm]

@[to_additive]
instance has_one [inhabited S] : has_one G := ⟨one (default : S)⟩

@[to_additive]
lemma one_def [inhabited S] : (1 : G) = one (default : S) := rfl

@[to_additive]
protected lemma inv_one [inhabited S] : (1 : G)⁻¹ = 1 :=
by simp [one_def, one]

@[to_additive]
instance subsingleton_mul [subsingleton S] : subsingleton G :=
⟨λ a b, quotient.induction_on₂ a b $ by simp⟩

@[to_additive]
instance nonempty_mul [h : nonempty S] : nonempty G :=
nonempty.map one h

@[to_additive]
instance [inhabited S] : comm_group G :=
{ mul := (*),
  one := 1,
  one_mul := λ a, quotient.induction_on a $ by simp [one_def, one, mul_comm, mul_left_comm],
  mul_one := λ a, quotient.induction_on a $ by simp [one_def, one, mul_comm, mul_left_comm],
  inv := pair_quotient.inv,
  mul_left_inv := λ a, begin
    induction a using quotient.induction_on,
    rw [mul_comm, mul_rev_inv_eq ⟦a⟧ 1, pair_quotient.inv_one],
    simp [one_def, one, mul_assoc]
  end,
  ..pair_quotient.comm_semigroup }

variables [nakada_po S]

@[to_additive]
protected def mul_le : G → G → Prop :=
quotient.lift₂ (λ (p q : S × S), p.1 * q.2 ≤ q.1 * p.2) begin
  rintro ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩ ⟨d, d'⟩ hac hbd,
  simp only [mul_pair_equiv_iff, eq_iff_iff] at hac hbd ⊢,
  split,
  work_on_goal 1 { rename [a x, a' x', b y, b' y', c a, c' a', d b, d' b'],
                   rename [x c, x' c', y d, y' d'],
                   rw eq_comm at hac hbd },
  all_goals { intro h,
    replace h : c' * (a * b') ≤ c' * (b * a') := homogeneity h c',
    rw [←mul_assoc, mul_comm c', hac, mul_comm b, mul_left_comm, mul_assoc, mul_left_comm] at h,
    replace h : d * (c * b') ≤ d * (c' * b) := homogeneity (strong h) d,
    rw [mul_left_comm, ←hbd, mul_left_comm, mul_comm _ b, mul_left_comm _ b] at h,
    exact strong h }
end

@[to_additive]
instance mul_has_le : has_le G := ⟨pair_quotient.mul_le⟩

@[simp, to_additive] lemma mul_le_def {p q : S × S} : ⟦p⟧ ≤ ⟦q⟧ ↔ p.1 * q.2 ≤ q.1 * p.2 := iff.rfl

@[to_additive]
instance mul_decidable_le [decidable_rel ((≤) : S → S → Prop)] :
  decidable_rel ((≤) : G → G → Prop) :=
λ a b, quotient.rec_on_subsingleton₂ a b (λ p q, decidable_of_iff' _ mul_le_def)

@[to_additive]
instance mul_partial_order : partial_order G :=
{ le := (≤),
  le_refl := λ a, quotient.induction_on a $ by simp,
  le_trans := λ a b c, quotient.induction_on₃ a b c $ begin
    rintro ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩ hab hbc,
    simp only [mul_le_def] at *,
    suffices : b' * (a * c') ≤ b' * (c * a'),
    { exact strong this },
    calc b' * (a * c') ≤ c' * (b * a') : by simpa [mul_comm, mul_left_comm] using homogeneity hab c'
    ... ≤ a' * (c * b') : by simpa [mul_comm, mul_left_comm] using homogeneity hbc a'
    ... ≤ b' * (c * a') : by simp only [mul_comm, mul_left_comm]
  end,
  le_antisymm := λ a b, begin
    induction a using quotient.induction_on,
    induction b using quotient.induction_on,
    simpa using le_antisymm
  end }

@[to_additive]
instance mul_nakada_po : nakada_po G :=
⟨λ a b c, quotient.induction_on₃ a b c begin
  rintro ⟨a, a'⟩ ⟨b, b'⟩ ⟨c, c'⟩ hbc,
  simp only [mk_mul, mul_le_def] at hbc,
  simpa only [mul_left_comm, mul_assoc, mk_mul, mul_le_def] using homogeneity (homogeneity hbc a) a'
end⟩

-- Theorem 5, corollary
@[to_additive]
instance mul_linear_order {S : Type*} [comm_semigroup S] [linear_order S]
  [nakada_po S] [nakada_strong S] : linear_order (quotient (mul_pair_setoid S)) :=
{ le_total := λ a b, quotient.induction_on₂ a b $ by
    { rintro ⟨a, a'⟩ ⟨b, b'⟩, simpa using le_total _ _ },
  decidable_le := pair_quotient.mul_decidable_le,
  ..pair_quotient.mul_partial_order }

end pair_quotient

-- Theorem 5, mpr
@[to_additive]
def to_mul_pair_quotient [nakada_po S] (x : S) : S ↪*o (quotient (mul_pair_setoid S)) :=
{ to_fun := λ a, ⟦(a * x, x)⟧,
  map_mul' := λ _ _, by simp [mul_comm, mul_left_comm],
  inj' := λ a b h, begin
    suffices : x * x * a = x * x * b,
    { exact nakada_strong.cancel_left this },
    simpa only [mul_comm, mul_left_comm, quotient.eq, mul_pair_equiv_iff] using h
  end,
  map_rel_iff' := λ _ _, by simp }

@[simp, to_additive] lemma to_mul_pair_quotient_apply [nakada_po S] (x a : S) :
  to_mul_pair_quotient x a = ⟦(a * x, x)⟧ := rfl

@[to_additive] lemma to_mul_pair_quotient_eq [nakada_po S] (x y : S) :
  to_mul_pair_quotient x = to_mul_pair_quotient y :=
by { ext, simp [mul_right_comm] }

@[to_additive]
def of_mul_pair_quotient' [nakada_po S] (x : S) :
  subsemigroup (quotient (mul_pair_setoid S)) :=
subsemigroup.closure (set.range (to_mul_pair_quotient x))

-- "Uniquely determined by S apart from its order-isomorphism"
@[to_additive]
lemma of_mul_pair_quotient'_eq [nakada_po S] (x y : S) :
  of_mul_pair_quotient' x = of_mul_pair_quotient' y :=
by rw [of_mul_pair_quotient', of_mul_pair_quotient', to_mul_pair_quotient_eq]

-- Doesn't matter which element we choose by the previous lemma
@[to_additive]
def of_mul_pair_quotient [nakada_po S] [inhabited S] :
  submonoid (quotient (mul_pair_setoid S)) :=
submonoid.closure (set.range (to_mul_pair_quotient default))

@[to_additive]
def out_mul_pair_quotient (G : Type*) [comm_group G] [partial_order G] [nakada_po G] :
  (quotient (mul_pair_setoid G)) ↪*o G :=
{ to_fun := λ p, quotient.lift_on p (λ xy, prod.fst xy * (prod.snd xy)⁻¹) $ begin
    rintro ⟨a, b⟩ ⟨c, d⟩ h,
    rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_comm, mul_inv_eq_iff_eq_mul, eq_comm],
    simpa only [mul_pair_equiv_iff, subsemigroup.mk_mul_mk, subtype.mk_eq_mk] using h
  end,
  map_mul' := λ x y, quotient.induction_on₂ x y $ by simp [mul_comm, mul_left_comm],
  inj' := λ x y, quotient.induction_on₂ x y $ λ _ _, begin
    simp only [mul_pair_equiv_iff, quotient.lift_on_mk, quotient.eq],
    rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_comm, mul_inv_eq_iff_eq_mul, eq_comm],
    exact id
  end,
  map_rel_iff' := λ x y, quotient.induction_on₂ x y $ λ a b, begin
    simp only [quotient.lift_on_mk, mul_inv_le_iff_le_mul', pair_quotient.mul_le_def],
    refine ⟨λ h, ((mul_comm _ _).le.trans (homogeneity h _)).trans (eq.le _),
            λ h, ((eq.le _).trans (homogeneity h (b.snd)⁻¹)).trans _⟩;
    simp [mul_left_comm]
  end }

@[simp, to_additive]
def out_mul_pair_quotient_apply_mk {G : Type*} [comm_group G] [partial_order G] [nakada_po G]
  (x : G × G) : out_mul_pair_quotient G ⟦x⟧ = x.fst * x.snd⁻¹ := rfl

@[to_additive]
def as_mul_pair_quotient (G : Type*) [comm_group G] [partial_order G] [nakada_po G] :
  G ≃*o (quotient (mul_pair_setoid G)) :=
mul_order_iso.of_mul_order_embedding (to_mul_pair_quotient 1) (out_mul_pair_quotient G) $
  λ x, quotient.induction_on x $ by simp only [out_mul_pair_quotient_apply_mk,
  to_mul_pair_quotient_apply, mul_one, quotient.eq, mul_pair_equiv_iff,
  inv_mul_cancel_right, eq_self_iff_true, forall_const]

@[simp, to_additive]
lemma as_mul_pair_quotient_apply {G : Type*} [comm_group G] [partial_order G] [nakada_po G]
  (x : G) :
  as_mul_pair_quotient G x = ⟦(x, 1)⟧ :=
by { nth_rewrite_rhs 0 ←mul_one x, refl }

@[simp, to_additive]
lemma as_mul_pair_quotient_symm_apply_mk {G : Type*} [comm_group G] [partial_order G] [nakada_po G]
  (x : G × G) : (as_mul_pair_quotient G).symm ⟦x⟧ = x.fst * x.snd⁻¹ := rfl

@[to_additive]
def mul_order_embedding.lift_pair_quotient {S S' : Type*}
  [comm_semigroup S] [partial_order S] [nakada_po S] [nakada_strong S]
  [comm_semigroup S'] [partial_order S'] [nakada_po S'] [nakada_strong S']
  (f : S ↪*o S') : quotient (mul_pair_setoid S) ↪*o quotient (mul_pair_setoid S') :=
{ to_fun := quotient.map (prod.map f f) $ λ _ _, by simp [←map_mul] {contextual := tt},
  map_mul' := λ x y, quotient.induction_on₂ x y $ by simp,
  inj' := λ x y, quotient.induction_on₂ x y $ by simp [←map_mul, f.injective.eq_iff],
  map_rel_iff' := λ x y, quotient.induction_on₂ x y $ by simp [←map_mul] }

-- Same `map_mk` issue as with `mk_mul`
@[simp, to_additive]
lemma mul_order_embedding.lift_pair_quotient_apply_mk {S S' : Type*}
  [comm_semigroup S] [partial_order S] [nakada_po S] [nakada_strong S]
  [comm_semigroup S'] [partial_order S'] [nakada_po S'] [nakada_strong S']
  (f : S ↪*o S') (x : S × S) : f.lift_pair_quotient ⟦x⟧ = ⟦x.map f f⟧ :=
quotient.map_mk _ (λ _, by simp [←map_mul] {contextual := tt}) _

-- how to prove minimality and uniqueness?

variables {M G M₀ : Type*} [comm_monoid M] [partial_order M] [nakada_po M] [comm_group G]
  [partial_order G] [nakada_po G] [comm_monoid_with_zero M₀] [partial_order M₀]

-- Theorem 6
@[to_additive]
lemma le_mul_left_iff :
  (∀ a b : M, a ≤ b * a) ↔ (∀ a : M, 1 ≤ a) :=
⟨λ h b, by simpa using h 1 b, λ h a b, by simpa [mul_comm] using homogeneity (h b) a⟩

lemma le_zero_of_forall_le_mul_left (h : ∀ a b : M₀, a ≤ b * a) (a : M₀) : a ≤ 0 :=
by simpa using h a 0

-- Theorem 6, corollary
@[to_additive]
lemma le_mul_left_iff_of_mul_order_embedding {S : Type*} [comm_semigroup S] [partial_order S]
  (f : S ↪*o G) :
  (∀ a b : S, a ≤ b * a) ↔ ∀ a : S, 1 ≤ f a :=
begin
  casesI is_empty_or_nonempty S with H H,
  { exact ⟨λ h a, H.elim a, λ h a, H.elim a⟩ },
  letI : inhabited S := classical.inhabited_of_nonempty H,
  split,
  { intros h a,
    have := h default a,
    rw ←f.map_rel_iff' at this,
    simpa using this },
  { intros h a b,
    have := homogeneity (h b) (f a),
    rwa [mul_one, ←map_mul, f.map_le_iff, mul_comm] at this }
end

-- Theorem 7
@[to_additive]
lemma exists_mul_of_lt_iff [nakada_po S] [nakada_strong S] [inhabited S]
  (f : S ↪*o quotient (mul_pair_setoid S)) (hf : f = to_mul_pair_quotient default) :
  (∀ a b : S, a < b → ∃ c : S, b = c * a) ↔
    ∀ a' : quotient (mul_pair_setoid S), 1 < a' → ∃ as : S, a' = f as :=
begin
  simp_rw [←f.map_lt_iff],
  split,
  { intros h x hx,
    induction H : x using quotient.induction_on with y,
    cases y with a b,
    have : x = f a * (f b)⁻¹,
    { simp [hf, H, mul_comm, mul_left_comm] },
    refine (h b a _).imp _,
    { rintro c rfl,
      simp [←H, this] },
    { rwa [←lt_mul_inv_iff_lt, ←this] } },
  { intros h a b hab,
    rw [←lt_mul_inv_iff_lt] at hab,
    refine (h _ hab).imp _,
    intros c hc,
    simp [←f.injective.eq_iff, ←hc] }
end

end page183

section page184

-- Definition 4
@[reducible, to_additive add_positive]
def positive {S : Type*} [has_mul S] [has_le S] (a : S) : Prop := a ≤ a * a
@[reducible, to_additive add_negative]
def negative {S : Type*} [has_mul S] [has_le S] (a : S) : Prop := a * a ≤ a

@[to_additive add_positive_or_add_negative]
lemma positive_or_negative {S : Type*} [has_mul S] [has_le S] [is_total S (≤)] (a : S) :
  positive a ∨ negative a :=
is_total.total _ _

section

variables {S S' M : Type*} [comm_semigroup S] [preorder S] [nakada_po S]
  [comm_semigroup S'] [preorder S'] [nakada_po S']
  [comm_monoid M] [preorder M] [nakada_po M]

@[to_additive]
lemma positive.mul {a b : S} (ha : positive a) (hb : positive b) : positive (a * b) :=
begin
  refine (homogeneity hb a).trans _,
  rw [mul_left_comm, mul_comm a, mul_assoc],
  refine homogeneity _ _,
  rw mul_left_comm,
  exact homogeneity ha _
end

@[to_additive]
lemma negative.mul {a b : S} (ha : negative a) (hb : negative b) : negative (a * b) :=
begin
  refine (le_trans _ (homogeneity hb a)),
  rw [←mul_assoc, mul_comm, mul_left_comm a],
  refine homogeneity _ _,
  rw [mul_comm _ b, mul_assoc],
  exact homogeneity ha _
end

@[to_additive add_positive_zero]
lemma positive_one : positive (1 : M) := by simp [positive]

@[to_additive add_negative_zero]
lemma negative_one : negative (1 : M) := by simp [negative]

@[to_additive add_order_embedding.add_positive]
lemma mul_order_embedding.positive (f : S ↪*o S') {a : S} (ha : positive a) : positive (f a) :=
by rwa [positive, ←map_mul, f.map_le_iff]

@[to_additive add_order_embedding.add_negative]
lemma mul_order_embedding.negative (f : S ↪*o S') {a : S} (ha : negative a) : negative (f a) :=
by rwa [negative, ←map_mul, f.map_le_iff]

variables (S M)

@[to_additive pos_add_subsemigroup]
def pos_subsemigroup : subsemigroup S :=
{ carrier := set_of positive,
  mul_mem' := λ _ _, positive.mul }

@[to_additive neg_add_subsemigroup]
def neg_subsemigroup : subsemigroup S :=
{ carrier := set_of negative,
  mul_mem' := λ _ _, negative.mul }

@[to_additive]
def pos_submonoid : submonoid M :=
{ one_mem' := positive_one,
  ..pos_subsemigroup M }

@[to_additive]
def neg_submonoid : submonoid M :=
{ one_mem' := negative_one,
  ..neg_subsemigroup M }

variables {S S'}

@[to_additive]
def mul_order_embedding.restrict_pos (f : S ↪*o S') :
  pos_subsemigroup S ↪*o pos_subsemigroup S' :=
{ to_fun := λ x, ⟨f x, f.positive x.prop⟩,
  map_mul' := λ _ _, subtype.ext $ by simp only [subsemigroup.coe_mul, map_mul, subtype.coe_mk],
  inj' := λ _ _, by simp [f.injective.eq_iff] {contextual := tt},
  map_rel_iff' := λ _ _,
    by simp only [subtype.mk_le_mk, mul_order_embedding.map_le_iff, subtype.coe_le_coe] }

@[to_additive]
def mul_order_embedding.restrict_neg (f : S ↪*o S') :
  neg_subsemigroup S ↪*o neg_subsemigroup S' :=
{ to_fun := λ x, ⟨f x, f.negative x.prop⟩,
  map_mul' := λ _ _, subtype.ext $ by simp only [subsemigroup.coe_mul, map_mul, subtype.coe_mk],
  inj' := λ _ _, by simp [f.injective.eq_iff] {contextual := tt},
  map_rel_iff' := λ _ _,
    by simp only [subtype.mk_le_mk, mul_order_embedding.map_le_iff, subtype.coe_le_coe] }

@[to_additive]
lemma mul_order_embedding.restrict_pos_apply (f : S ↪*o S') (x : pos_subsemigroup S) :
  f.restrict_pos x = ⟨f x, f.positive x.prop⟩ := rfl

@[to_additive]
lemma mul_order_embedding.restrict_neg_apply (f : S ↪*o S') (x : neg_subsemigroup S) :
  f.restrict_neg x = ⟨f x, f.negative x.prop⟩ := rfl

@[to_additive]
lemma mul_order_embedding.apply_pos_subsemigroup (f : S ↪*o S') (x : pos_subsemigroup S) :
  f x = f.restrict_pos x := rfl

@[to_additive]
lemma mul_order_embedding.apply_neg_subsemigroup (f : S ↪*o S') (x : neg_subsemigroup S) :
  f x = f.restrict_neg x := rfl

@[to_additive]
def mul_order_iso.restrict_pos (f : S ≃*o S') :
  pos_subsemigroup S ≃*o pos_subsemigroup S' :=
mul_order_iso.of_mul_order_embedding
  f.to_mul_order_embedding.restrict_pos f.symm.to_mul_order_embedding.restrict_pos $ λ _,
  by simp [mul_order_embedding.restrict_pos_apply]

@[to_additive]
def mul_order_iso.restrict_neg (f : S ≃*o S') :
  neg_subsemigroup S ≃*o neg_subsemigroup S' :=
mul_order_iso.of_mul_order_embedding
  f.to_mul_order_embedding.restrict_neg f.symm.to_mul_order_embedding.restrict_neg $ λ _,
  by simp [mul_order_embedding.restrict_neg_apply]

@[to_additive]
lemma mul_order_iso.restrict_pos_apply (f : S ≃*o S') (x : pos_subsemigroup S) :
  f.restrict_pos x = ⟨f x, f.to_mul_order_embedding.positive x.prop⟩ := rfl

@[to_additive]
lemma mul_order_iso.restrict_neg_apply (f : S ≃*o S') (x : neg_subsemigroup S) :
  f.restrict_neg x = ⟨f x, f.to_mul_order_embedding.negative x.prop⟩ := rfl

@[to_additive]
lemma mul_order_iso.apply_pos_subsemigroup (f : S ≃*o S') (x : pos_subsemigroup S) :
  f x = f.restrict_pos x := rfl

@[to_additive]
lemma mul_order_iso.apply_neg_subsemigroup (f : S ≃*o S') (x : neg_subsemigroup S) :
  f x = f.restrict_neg x := rfl

end

section

variables {S S' M : Type*} [comm_semigroup S] [comm_semigroup S'] [comm_monoid M]

@[to_additive]
instance [preorder S] [nakada_po S] : preorder (pos_subsemigroup S) :=
subtype.preorder _

@[to_additive]
instance [preorder S] [nakada_po S] : nakada_po (pos_subsemigroup S) :=
nakada_po.comap (coe : _ → S) (λ _ _, iff.rfl) (λ _ _, rfl)

@[to_additive]
instance [preorder S] [nakada_po S] [nakada_strong S] : nakada_strong (pos_subsemigroup S) :=
nakada_strong.comap (coe : _ → S) (λ _ _, iff.rfl) (λ _ _, rfl)

@[to_additive]
instance [partial_order S] [nakada_po S] : partial_order (pos_subsemigroup S) :=
subtype.partial_order _

@[to_additive]
instance [linear_order S] [nakada_po S] : linear_order (pos_subsemigroup S) :=
subtype.linear_order _

@[to_additive]
instance [preorder S] [nakada_po S] : preorder (neg_subsemigroup S) :=
subtype.preorder _

@[to_additive]
instance [preorder S] [nakada_po S] : nakada_po (neg_subsemigroup S) :=
nakada_po.comap (coe : _ → S) (λ _ _, iff.rfl) (λ _ _, rfl)

@[to_additive]
instance [preorder S] [nakada_po S] [nakada_strong S] : nakada_strong (neg_subsemigroup S) :=
nakada_strong.comap (coe : _ → S) (λ _ _, iff.rfl) (λ _ _, rfl)

@[to_additive]
instance [partial_order S] [nakada_po S] : partial_order (neg_subsemigroup S) :=
subtype.partial_order _

@[to_additive]
instance [linear_order S] [nakada_po S] : linear_order (neg_subsemigroup S) :=
subtype.linear_order _

@[to_additive]
instance [preorder M] [nakada_po M] : inhabited (pos_subsemigroup M) :=
⟨⟨1, positive_one⟩⟩

@[to_additive]
instance [preorder M] [nakada_po M] : inhabited (neg_subsemigroup M) :=
⟨⟨1, negative_one⟩⟩

@[to_additive]
instance [preorder M] [nakada_po M] : preorder (pos_submonoid M) :=
subtype.preorder _

@[to_additive]
instance [preorder M] [nakada_po M] : nakada_po (pos_submonoid M) :=
nakada_po.comap (coe : _ → M) (λ _ _, iff.rfl) (λ _ _, rfl)

@[to_additive]
instance [preorder M] [nakada_po M] [nakada_strong M] : nakada_strong (pos_submonoid M) :=
nakada_strong.comap (coe : _ → M) (λ _ _, iff.rfl) (λ _ _, rfl)

@[to_additive]
instance [partial_order M] [nakada_po M] : partial_order (pos_submonoid M) :=
subtype.partial_order _

@[to_additive]
instance [linear_order M] [nakada_po M] : linear_order (pos_submonoid M) :=
subtype.linear_order _

@[to_additive]
instance [preorder M] [nakada_po M] : preorder (neg_submonoid M) :=
subtype.preorder _

@[to_additive]
instance [preorder M] [nakada_po M] : nakada_po (neg_submonoid M) :=
nakada_po.comap (coe : _ → M) (λ _ _, iff.rfl) (λ _ _, rfl)

@[to_additive]
instance [preorder M] [nakada_po M] [nakada_strong M] : nakada_strong (neg_submonoid M) :=
nakada_strong.comap (coe : _ → M) (λ _ _, iff.rfl) (λ _ _, rfl)

@[to_additive]
instance [partial_order M] [nakada_po M] : partial_order (neg_submonoid M) :=
subtype.partial_order _

@[to_additive]
instance [linear_order M] [nakada_po M] : linear_order (neg_submonoid M) :=
subtype.linear_order _

end

@[to_additive add_positive.zero_le]
lemma positive.one_le {G : Type*} [comm_group G] [has_le G] [nakada_po G] {a : G}
  (ha : positive a) : 1 ≤ a :=
by simpa using homogeneity ha a⁻¹

@[to_additive add_negative.le_zero]
lemma negative.le_one {G : Type*} [comm_group G] [has_le G] [nakada_po G] {a : G}
  (ha : negative a) : a ≤ 1 :=
by simpa using homogeneity ha a⁻¹

@[to_additive add_positive_of_zero_le]
lemma positive_of_one_le {G : Type*} [comm_monoid G] [has_le G] [nakada_po G] {a : G}
  (ha : 1 ≤ a) : positive a :=
by simpa [positive] using homogeneity ha a

@[to_additive add_negative_of_le_zero]
lemma negative_of_le_one {G : Type*} [comm_monoid G] [has_le G] [nakada_po G] {a : G}
  (ha : a ≤ 1) : negative a :=
by simpa [negative] using homogeneity ha a

@[to_additive add_positive.add_negative_neg]
lemma positive.negative_inv {G : Type*} [comm_group G] [has_le G] [nakada_po G] {a : G}
  (ha : positive a) : negative a⁻¹ :=
by simpa only [mul_left_inv, inv_mul_cancel_comm_assoc, mul_one] using
  homogeneity (homogeneity (homogeneity ha a⁻¹) a⁻¹) a⁻¹

@[to_additive add_negative.add_positive_neg]
lemma negative.positive_inv {G : Type*} [comm_group G] [has_le G] [nakada_po G] {a : G}
  (ha : negative a) : positive a⁻¹ :=
by simpa only [mul_left_inv, inv_mul_cancel_comm_assoc, mul_one] using
  homogeneity (homogeneity (homogeneity ha a⁻¹) a⁻¹) a⁻¹

@[to_additive]
instance neg_subsemigroup.is_directed {G : Type*} [comm_group G] [preorder G] [nakada_po G] :
  is_directed (neg_subsemigroup G) (≤) :=
⟨λ ⟨a, ha⟩ ⟨b, hb⟩, ⟨⟨1, negative_one⟩, ha.le_one, hb.le_one⟩⟩

@[to_additive]
instance neg_submonoid.is_directed {G : Type*} [comm_group G] [preorder G] [nakada_po G] :
  is_directed (neg_submonoid G) (≤) :=
⟨λ ⟨a, ha⟩ ⟨b, hb⟩, ⟨1, ha.le_one, hb.le_one⟩⟩

def order_hom.is_directed {S S' : Type*} [nonempty S] [preorder S] [is_directed S (≤)]
  [preorder S'] (f : S →o S') (hf : function.surjective f) : is_directed S' (≤) :=
⟨λ x y, begin
  obtain ⟨d, hdx, hdy⟩ := directed_of (≤) ((function.inv_fun f) x) ((function.inv_fun f) y),
  exact ⟨_, (eq.ge (function.inv_fun_eq (hf _))).trans (f.monotone hdx),
    (eq.ge (function.inv_fun_eq (hf _))).trans (f.monotone hdy)⟩
end⟩

-- Theorem 8, mp, generalized
lemma is_directed_of_mul_order_iso_subsemigroup {G : Type*} [comm_group G] [partial_order G]
  [nakada_po G] {S : subsemigroup G} [is_directed S (≤)] [nakada_po S] [nakada_strong S]
  (f : G ≃*o quotient (mul_pair_setoid S)) : is_directed G (≤) :=
⟨λ x y, begin
  induction hx : (f x) using quotient.induction_on with x',
  cases x' with a c,
  induction hy : (f y) using quotient.induction_on with y',
  cases y' with b c',
  have hx' : x = f.symm (to_mul_pair_quotient a (a * c') * (to_mul_pair_quotient a (c * c'))⁻¹),
  { simp [mul_assoc, mul_comm, mul_left_comm, mul_pair_left_eq (a * (a * c'), a * (c * c')),
          mul_pair_left_eq (a * c', c * c'), mul_pair_right_eq (a, c), ←hx] },
  have hy' : y = f.symm (to_mul_pair_quotient a (b * c) * (to_mul_pair_quotient a (c * c'))⁻¹),
  { simp [mul_assoc, mul_comm, mul_left_comm, mul_pair_left_eq (a * (c * b), a * (c * c')),
          mul_pair_left_eq (c * b, c * c'), mul_pair_left_eq (b, c'), ←hy] },
  obtain ⟨d, hd, hd'⟩ := directed_of (≤) (a * c') (b * c),
  refine ⟨f.symm (to_mul_pair_quotient a d * (to_mul_pair_quotient a (c * c'))⁻¹), _, _⟩,
  { simpa [hx'] using hd },
  { simpa [hy'] using hd' }
end⟩

-- Theorem 8, mp
lemma is_directed_of_mul_order_iso {G : Type*} [comm_group G] [partial_order G] [nakada_po G]
  (f : G ≃*o quotient (mul_pair_setoid (neg_subsemigroup G))) : is_directed G (≤) :=
is_directed_of_mul_order_iso_subsemigroup f

section

variables {α β : Sort*} [setoid α]

lemma quotient.mk_eq_mk' (x : α) : ⟦x⟧ = quotient.mk' x := rfl

@[simp] lemma quotient.lift_on_mk' (x : α) (f : α → β) (h) : ⟦x⟧.lift_on' f h = f x := rfl

end

-- Theorem 8, mpr
@[to_additive neg_add_subsemigroup_iso_of_is_directed]
noncomputable def neg_subsemigroup_iso_of_is_directed (G : Type*) [comm_group G] [partial_order G]
  [nakada_po G] [is_directed G (≤)] :
  quotient (mul_pair_setoid (neg_subsemigroup G)) ≃*o G :=
{ inv_fun := λ x, begin
    set a := (directed_of (≤) x 1).some with ha,
    refine quotient.mk' (⟨a⁻¹ * x, _⟩, ⟨a⁻¹, positive.negative_inv _⟩),
    { have hxa : x ≤ a,
      { rw ha,
        generalize_proofs ha',
        exact ha'.some_spec.left },
      have hx : x = a * (a * x⁻¹)⁻¹,
      { rw [mul_inv, inv_inv, mul_inv_cancel_left] },
      have : 1 ≤ (a⁻¹ * x)⁻¹,
      { rw [hx],
        simpa only [mul_inv_rev, inv_inv, mul_inv_cancel_comm_assoc,
                    le_inv_mul_iff_mul_le, mul_one] using hxa},
      simpa only [inv_inv] using (positive_of_one_le this).negative_inv },
    { refine positive_of_one_le _,
      rw ha,
      generalize_proofs ha',
      exact ha'.some_spec.right }
  end,
  to_fun := (out_mul_pair_quotient _).comp
    (mul_order_embedding.coe (neg_subsemigroup G) (λ _ _, iff.rfl)).lift_pair_quotient,
  right_inv := λ _, by  simp [←quotient.mk_eq_mk'],
  left_inv := λ x, begin
    induction x using quotient.induction_on,
    simp [←quotient.mk_eq_mk', subtype.ext_iff, mul_comm _ (Exists.some _)⁻¹, mul_assoc]
  end,
  map_mul' := map_mul _,
  map_rel_iff' := λ _ _, mul_order_embedding.map_le_iff _ }

section pnpow

variables {S : Type*} [has_mul S] (x : S) (p : ℕ+) (n : ℕ)

-- use `x * pnpow_rec n x` and not `pnpow_rec n x * x` in the definition to make sure that
-- definitional unfolding of `pnpow_rec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `pnpow_rec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def pnpow_rec {S : Type*} [has_mul S] : ℕ+ → S → S :=
λ n, pnat.rec_on n id (λ _ f x, x * f x)

/-- The fundamental scalar multiplication in an additive monoid. `pnsmul_rec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def pnsmul_rec {S : Type*} [has_add S] : ℕ+ → S → S :=
λ n, pnat.rec_on n id (λ _ f x, x + f x)

attribute [to_additive pnsmul_rec] pnpow_rec

instance has_mul.has_pow {M : Type*} [has_mul M] : has_pow M ℕ+ := ⟨λ x n, pnpow_rec n x⟩

instance has_add.has_scalar_pnat {M : Type*} [has_add M] : has_scalar ℕ+ M :=
⟨pnsmul_rec⟩

attribute [to_additive has_add.has_scalar_pnat] has_mul.has_pow

@[simp, to_additive zero_pnsmul] lemma pnpow_one : x ^ (1 : ℕ+) = x := rfl
@[to_additive add_one_pnsmul'] lemma pnpow_add_one' : x ^ (p + 1) = x * x ^ p :=
begin
  change (pnpow_rec (p + 1) x) = x * (pnpow_rec p x),
  simp [pnpow_rec]
end

@[to_additive add_one_pnsmul]
lemma pnpow_add_one {S : Type*} [semigroup S] (x : S) (p : ℕ+) : x ^ (p + 1) = x ^ p * x :=
begin
  refine pnat.rec_on p _ _,
  { simp [pnpow_add_one'] },
  { intros n h,
    rw [pnpow_add_one', pnpow_add_one', mul_assoc, ←h, ←pnpow_add_one'] }
end

@[to_additive add_pnsmul'] lemma pnpow_add' {S : Type*} [semigroup S] (x : S) (p q : ℕ+) :
  x ^ (p + q) = x ^ q * x ^ p :=
begin
  revert q p,
  intro q,
  refine pnat.rec_on q _ _,
  { simp [pnpow_add_one'] },
  { intros q' IH p,
    simp [←add_assoc, IH, ←mul_assoc, pnpow_add_one'] }
end

@[to_additive add_pnsmul] lemma pnpow_add {S : Type*} [semigroup S] (x : S) (p q : ℕ+) :
  x ^ (p + q) = x ^ p * x ^ q :=
begin
  revert q p,
  intro q,
  refine pnat.rec_on q _ _,
  { simp [pnpow_add_one] },
  { intros q' IH p,
    simp [←add_assoc, IH, ←mul_assoc, pnpow_add_one] }
end

@[simp, to_additive pnsmul_eq_nsmul] lemma pnpow_eq_npow_coe {M : Type*} [monoid M] (x : M)
  (p : ℕ+) : x ^ p = x ^ (p : ℕ) :=
begin
  refine pnat.rec_on p _ _;
  simp [pow_succ', pnpow_add_one] {contextual := tt}
end

@[to_additive two_pnsmul] lemma pnpow_two : x ^ (2 : ℕ+) = x * x := rfl

end pnpow

@[simp] lemma nat.succ_pnat_zero : nat.succ_pnat 0 = 1 := rfl
@[simp] lemma nat.succ_pnat_succ (n : ℕ) : n.succ.succ_pnat = (n.succ_pnat + 1) := rfl

@[to_additive pnsmul_le_pnsmul_of_le]
lemma pnpow_le_pnpow_of_le {S : Type*} [has_mul S] [preorder S] [nakada_po S]
  [covariant_class S S (function.swap (*)) (≤)]
  {x y : S} (H : x ≤ y) (n : ℕ+) : x ^ n ≤ y ^ n :=
begin
  refine pnat.rec_on n _ _,
  { exact H },
  { intros n' h,
    simp only [pnpow_add_one'],
    refine (homogeneity h x).trans _,
    exact mul_le_mul_right' H _ }
end

@[to_additive add_positive.pnsmul_le_pnsmul_of_le]
lemma positive.pnpow_le_pnpow_of_le {S : Type*} [semigroup S] [preorder S] [nakada_po S]
  {x : S} (H : positive x) {n m : ℕ+} (h : n ≤ m) : x ^ n ≤ x ^ m :=
begin
  rcases h.eq_or_lt with rfl|h',
  { refl },
  obtain ⟨k, rfl⟩ : ∃ (k : ℕ+), m = n + k,
  { cases m, cases n,
    obtain ⟨k, hk⟩ := nat.exists_eq_add_of_lt h',
    refine ⟨⟨k + 1, nat.succ_pos'⟩, _⟩,
    simpa [subtype.ext_iff] using hk },
  refine pnat.rec_on n _ _,
  { refine pnat.rec_on k _ _,
    { simpa using H },
    { intros k' hk,
      refine hk.trans _,
      rw [←add_assoc, pnpow_add_one, add_comm, pnpow_add_one, mul_assoc],
      exact homogeneity H _ } },
  intros n' IH,
  rw [add_right_comm, pnpow_add_one', pnpow_add_one'],
  exact homogeneity IH _
end

@[to_additive add_negative.pnsmul_le_pnsmul_of_le]
lemma negative.pnpow_le_pnpow_of_le {S : Type*} [semigroup S] [preorder S] [nakada_po S]
  {x : S} (H : negative x) {n m : ℕ+} (h : n ≤ m) : x ^ m ≤ x ^ n :=
begin
  rcases h.eq_or_lt with rfl|h',
  { refl },
  obtain ⟨k, rfl⟩ : ∃ (k : ℕ+), m = n + k,
  { cases m, cases n,
    obtain ⟨k, hk⟩ := nat.exists_eq_add_of_lt h',
    refine ⟨⟨k + 1, nat.succ_pos'⟩, _⟩,
    simpa [subtype.ext_iff] using hk },
  refine pnat.rec_on n _ _,
  { refine pnat.rec_on k _ _,
    { simpa using H },
    { intros k' hk,
      refine le_trans _ hk,
      rw [←add_assoc, pnpow_add_one, add_comm, pnpow_add_one, mul_assoc],
      exact homogeneity H _ } },
  intros n' IH,
  rw [add_right_comm, pnpow_add_one', pnpow_add_one'],
  exact homogeneity IH _
end

section quasiidempotent

variables {M : Type*} [has_mul M]

-- TODO: in data.pnat.basic
instance pnat.decidable_div {k l : ℕ+} : decidable (k ∣ l) :=
decidable_of_iff' ((k : ℕ) ∣ (l : ℕ)) pnat.dvd_iff

lemma pnat.div_pos {k l : ℕ+} (h : k < l) : 0 < pnat.div l k :=
begin
  rw pnat.div_coe,
  split_ifs with hd hd,
  { rw ←nat.dvd_iff_mod_eq_zero at hd,
    obtain ⟨_|_|z, hz⟩ := hd,
    { simpa using hz },
    { rw [mul_one] at hz,
      rw [←pnat.coe_lt_coe, hz] at h,
      exact absurd h (lt_irrefl _) },
    rw [hz, mul_comm, nat.mul_div_cancel];
    simp },
  { exact nat.div_pos h.le (pnat.pos _) }
end

lemma pnat.add_lt_left (m n : ℕ+) : m < n + m :=
by simp [←pnat.coe_lt_coe]

lemma pnat.add_lt_right (m n : ℕ+) : m < m + n :=
by simp [←pnat.coe_lt_coe]

lemma pnat.exists_eq_add_of_lt {m n : ℕ+} (h : m < n) : ∃ k : ℕ+, n = m + k :=
begin
  obtain ⟨k, hk⟩ := nat.exists_eq_add_of_lt h,
  exact ⟨k.succ_pnat, subtype.ext hk⟩
end

@[priority 10]
instance : covariant_class ℕ+ ℕ+ ((+)) (≤) :=
⟨begin
  rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩,
  simp [←pnat.coe_le_coe]
end⟩

@[to_additive add_positive.pnsmul_eq_of_eq]
lemma positive.pnpow_eq_of_eq {S : Type*} [semigroup S] [partial_order S] [nakada_po S] {x : S}
  (h : positive x) {m n : ℕ+} (hx : x ^ m = x ^ n) (hne : m ≠ n) (k : ℕ+) (hk : m ≤ k) :
  x ^ k = x ^ m :=
begin
  rcases hk.eq_or_lt with rfl|hk',
  { refl },
  obtain ⟨k, rfl⟩ := pnat.exists_eq_add_of_lt hk',
  clear hk hk',
  refine le_antisymm _ (h.pnpow_le_pnpow_of_le (pnat.add_lt_right _ _).le),
  wlog hmn : m < n using [m n, n m],
  { exact hne.lt_or_lt },
  { obtain ⟨l, rfl⟩ := pnat.exists_eq_add_of_lt hmn,
    clear hne hmn,
    cases le_or_lt k l with hkl hkl,
    { rw hx,
      exact h.pnpow_le_pnpow_of_le (add_le_add le_rfl hkl) },
    { obtain ⟨p, r, hr, rfl⟩ : ∃ (p r : ℕ+) (hr : r ≤ l), k = p * l + r,
      { refine ⟨⟨k.div l, pnat.div_pos hkl⟩, k.mod l, (pnat.mod_le _ _).right, _⟩,
        simpa [subtype.ext_iff] using (pnat.div_add_mod' _ _).symm },
      clear hkl,
      revert p,
      intro p,
      refine pnat.rec_on p _ _,
      { rw [one_mul, ←add_assoc, pnpow_add, hx],
        nth_rewrite_lhs 0 ←hx,
        rw [←pnpow_add],
        exact (h.pnpow_le_pnpow_of_le (add_le_add le_rfl hr)) },
      { intros n IH,
        rwa [add_mul, one_mul, add_right_comm, ←add_assoc, add_right_comm, pnpow_add, ←hx,
             ←pnpow_add] } } },
  { rw [pnpow_add, hx, ←pnpow_add],
    exact this hx.symm hne.symm }
end

@[to_additive add_negative.pnsmul_eq_of_eq]
lemma negative.pnpow_eq_of_eq {S : Type*} [semigroup S] [partial_order S] [nakada_po S] {x : S}
  (h : negative x) {m n : ℕ+} (hx : x ^ m = x ^ n) (hne : m ≠ n) (k : ℕ+) (hk : m ≤ k) :
  x ^ k = x ^ m :=
begin
  rcases hk.eq_or_lt with rfl|hk',
  { refl },
  obtain ⟨k, rfl⟩ := pnat.exists_eq_add_of_lt hk',
  clear hk hk',
  refine le_antisymm (h.pnpow_le_pnpow_of_le (pnat.add_lt_right _ _).le) _,
  wlog hmn : m < n using [m n, n m],
  { exact hne.lt_or_lt },
  { obtain ⟨l, rfl⟩ := pnat.exists_eq_add_of_lt hmn,
    clear hne hmn,
    cases le_or_lt k l with hkl hkl,
    { rw hx,
      exact h.pnpow_le_pnpow_of_le (add_le_add le_rfl hkl) },
    { obtain ⟨p, r, hr, rfl⟩ : ∃ (p r : ℕ+) (hr : r ≤ l), k = p * l + r,
      { refine ⟨⟨k.div l, pnat.div_pos hkl⟩, k.mod l, (pnat.mod_le _ _).right, _⟩,
        simpa [subtype.ext_iff] using (pnat.div_add_mod' _ _).symm },
      clear hkl,
      revert p,
      intro p,
      refine pnat.rec_on p _ _,
      { rw [one_mul, ←add_assoc, pnpow_add, ←hx, ←pnpow_add, hx],
        exact (h.pnpow_le_pnpow_of_le (add_le_add le_rfl hr)), },
      { intros n IH,
        rwa [add_mul, one_mul, add_right_comm, ←add_assoc, add_right_comm, pnpow_add, ←hx,
             ←pnpow_add] } } },
  { rw [pnpow_add, hx, ←pnpow_add],
    exact this hx.symm hne.symm }
end

@[to_additive is_infinite_add_order]
def is_infinite_order (x : M) : Prop :=
∀ (i j : ℕ+) (h : i ≠ j), x ^ i ≠ x ^ j

@[to_additive is_infinite_add_order.not_is_of_fin_add_order]
lemma is_infinite_order.not_is_of_fin_order {M : Type*} [monoid M] {x : M}
  (h : is_infinite_order x) : ¬ is_of_fin_order x :=
begin
  rw [is_infinite_order] at h,
  rw [is_of_fin_order],
  rintros ⟨n, hn, H⟩,
  refine h 1 n.succ_pnat _ _,
  { simpa [subtype.ext_iff, nat.succ_inj'] using hn.lt.ne },
  { obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero (hn.lt.ne'),
    have : k.succ.iterate ((*) x) 1 = 1 := H,
    simp only [mul_one, mul_left_iterate] at this,
    simp [pow_succ', this] }
end

@[to_additive is_infinite_add_order_iff_not_is_of_fin_add_order]
lemma is_infinite_order_iff_not_is_of_fin_order {M : Type*} [monoid M] {x : M} :
  is_infinite_order x ↔ ¬ is_of_fin_order x :=
begin
  refine ⟨is_infinite_order.not_is_of_fin_order, _⟩,
  rw [is_infinite_order, is_of_fin_order],
  contrapose!,
  intro h,
  have h' : ∃ (i j : ℕ), 0 < i ∧ 0 < j ∧ i ≠ j ∧ x ^ i = x ^ j,
  { obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hne, h⟩ := h,
    refine ⟨i, j, hi, hj, _, _⟩,
    { simpa using hne },
    { simpa using h } },
  classical,
  set i : ℕ := nat.find h' with hi,
  have h'' := nat.find_spec h',
  set j : ℕ := nat.find (nat.find_spec h') with hj,
  have ipos : 0 < i := (nat.find_spec h'').left,
  have jpos : 0 < j := (nat.find_spec h'').right.left,
  have hne : i ≠ j := (nat.find_spec h'').right.right.left,
  have hx : x ^ i = x ^ j := (nat.find_spec h'').right.right.right,
  clear_value i j,
  cases hne.lt_or_lt with hij hij,
  { sorry },
  { sorry }
end

@[to_additive add_idempotent]
def idempotent (x : M) : Prop := x * x = x

@[to_additive quasi_add_idempotent]
def quasi_idempotent (x : M) : Prop :=
∃ (n' : ℕ) (n : ℕ+), n' = n ∧ set.inj_on (λ k : ℕ+, x ^ k) (set.Iic n) ∧
  ∀ (k : ℕ+), n ≤ k → x ^ k = x ^ n

namespace quasi_idempotent

variables {x : M} (h : quasi_idempotent x) [hx : decidable_pred (λ (n' : ℕ), ∃ (n : ℕ+), (n' = n ∧
  set.inj_on (λ k : ℕ+, x ^ k) (set.Iic n) ∧ ∀ (k : ℕ+), n ≤ k → x ^ k = x ^ n))]
include h hx

@[to_additive add_length_aux]
def length_aux : ℕ :=
nat.find h

@[to_additive add_length_aux_spec]
lemma length_aux_spec  : ∃ (n : ℕ+), (length_aux h = n ∧
  (set.inj_on (λ k : ℕ+, x ^ k) (set.Iic n)) ∧ ∀ (k : ℕ+), n ≤ k → x ^ k = x ^ n) :=
nat.find_spec h

@[to_additive add_length]
def length : ℕ+ :=
⟨length_aux h, begin
  obtain ⟨⟨n, hn⟩, h', -⟩ := length_aux_spec h,
  rw h',
  exact hn
end⟩

@[to_additive add_length_spec]
lemma length_spec : ∃ (n : ℕ+), length h = n ∧
  set.inj_on (λ k : ℕ+, x ^ k) (set.Iic n) ∧ ∀ (k : ℕ+), n ≤ k → x ^ k = x ^ n :=
by simpa [length, subtype.ext_iff] using length_aux_spec h

@[to_additive inj_on_pnsmul_le_length]
lemma inj_on_pnpow_le_length : set.inj_on (pow x) (set.Iic (length h)) :=
begin
  obtain ⟨_, rfl, hl, -⟩ := length_spec h,
  exact hl
end

@[to_additive pnsmul_eq_on_length_le]
lemma pnpow_eq_on_length_le (k : ℕ+) (hk : length h ≤ k) : x ^ k = x ^ length h :=
begin
  obtain ⟨_, rfl, -, hl⟩ := length_spec h,
  exact hl _ hk
end

lemma idempotent_of_length_eq_one (hl : length h = 1) :
  idempotent x :=
begin
  convert h.pnpow_eq_on_length_le 2 _,
  { simp [idempotent, hl, pnpow_two] },
  { simp [hl, ←pnat.coe_le_coe] }
end

end quasi_idempotent

lemma quasi_add_idempotent.add_idempotent_of_add_length_eq_one {A : Type*} [has_add A] {x : A}
  (h : quasi_add_idempotent x) [decidable_pred (λ (n' : ℕ), ∃ (n : ℕ+),
    n' = ↑n ∧ set.inj_on (λ (k : ℕ+), k • x) (set.Iic n) ∧ ∀ (k : ℕ+), n ≤ k → k • x = n • x)]
    (hl : h.add_length = 1) :
  add_idempotent x :=
begin
  convert h.pnsmul_eq_on_length_le 2 _,
  { simp [add_idempotent, hl, two_pnsmul] },
  { simp [hl, ←pnat.coe_le_coe] }
end

attribute [to_additive quasi_add_idempotent.add_idempotent_of_add_length_eq_one]
  quasi_idempotent.idempotent_of_length_eq_one

end quasiidempotent

-- Theorem 9
@[to_additive is_infinite_add_order_or_quasi_add_idempotent]
lemma is_infinite_order_or_quasi_idempotent {S : Type*} [semigroup S] [linear_order S] [nakada_po S]
  (x : S) : is_infinite_order x ∨ quasi_idempotent x :=
begin
  refine or_iff_not_imp_left.mpr (λ h, _),
  rw is_infinite_order at h,
  push_neg at h,
  have h' : ∃ (i : ℕ), 0 < i ∧ ∃ (j : ℕ), 0 < j ∧ i ≠ j ∧ x ^ i.to_pnat' = x ^ j.to_pnat',
  { obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hne, h⟩ := h,
    refine ⟨i, hi, j, hj, _, _⟩,
    { simpa using hne },
    { convert h;
      simp [subtype.ext_iff, hi, hj] } },
  classical,
  set i : ℕ := nat.find h' with hi,
  have h'' := nat.find_spec h',
  have hs : set.inj_on (λ (k : ℕ+), x ^ k) (set.Iic i.to_pnat'),
  { rintros ⟨m, hm'⟩ hm ⟨n, hn'⟩ hn hmn,
    obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero hm'.ne',
    obtain ⟨l, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn'.ne',
    simp only [set.mem_Iic, ←pnat.coe_le_coe, pnat.mk_coe, nat.le_find_iff, ne.def, not_exists,
               not_and, nat.to_pnat'_coe, nat.find_pos, @not_lt_zero' ℕ, false_and, exists_false,
               not_false_iff, if_true, exists_and_distrib_left] at hm hn hmn,
    rcases lt_trichotomy k l with H|rfl|H,
    { refine absurd hmn _,
      exact hn k.succ (nat.succ_lt_succ H) k.succ_pos l.succ l.succ_pos (nat.succ_lt_succ H).ne },
    { refl },
    { refine absurd hmn.symm _,
      exact hm l.succ (nat.succ_lt_succ H) l.succ_pos k.succ k.succ_pos (nat.succ_lt_succ H).ne } },
  refine ⟨i, i.to_pnat', _, hs, _⟩,
  { simp only [nat.to_pnat'_coe, nat.find_pos, @not_lt_zero' ℕ, false_and, not_false_iff,
               if_true] },
  intros k hk,
  rw ←hi at h'',
  obtain ⟨hi', j, hj, hne, hij⟩ := h'',
  cases positive_or_negative x with hx hx;
  { refine hx.pnpow_eq_of_eq hij _ _ hk,
    simp [subtype.ext_iff, hj, hne, @not_lt_zero' ℕ] }
end

end page184
