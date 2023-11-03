/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import algebra.group.pi
import algebra.group.prod
import algebra.hom.iterate
import logic.equiv.set

/-!
# The group of permutations (self-equivalences) of a type `α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `group` structure on `equiv.perm α`.
-/
universes u v

namespace equiv

variables {α : Type u} {β : Type v}

namespace perm

instance perm_group : group (perm α) :=
{ mul := λ f g, equiv.trans g f,
  one := equiv.refl α,
  inv := equiv.symm,
  mul_assoc := λ f g h, (trans_assoc _ _ _).symm,
  one_mul := trans_refl,
  mul_one := refl_trans,
  mul_left_inv := self_trans_symm,
  npow := λ n f, ⟨f^[n], f.symm^[n], f.left_inv.iterate _, f.right_inv.iterate _⟩,
  npow_succ' := λ n f, coe_fn_injective $ function.iterate_succ' _ _,
  zpow := λ n, match n with
  | int.of_nat n := λ f, ⟨f^[n], f.symm^[n], f.left_inv.iterate _, f.right_inv.iterate _⟩
  | int.neg_succ_of_nat n := λ f,
      ⟨f.symm^[n + 1], f^[n + 1], f.right_inv.iterate _, f.left_inv.iterate _⟩
  end,
  zpow_succ' := λ n f, coe_fn_injective $ function.iterate_succ' _ _ }

@[simp] lemma default_eq : (default : perm α) = 1 := rfl

/-- The permutation of a type is equivalent to the units group of the endomorphisms monoid of this
type. -/
@[simps] def equiv_units_End : perm α ≃* units (function.End α) :=
{ to_fun := λ e, ⟨e, e.symm, e.self_comp_symm, e.symm_comp_self⟩,
  inv_fun := λ u, ⟨(u : function.End α), (↑u⁻¹ : function.End α), congr_fun u.inv_val,
    congr_fun u.val_inv⟩,
  left_inv := λ e, ext $ λ x, rfl,
  right_inv := λ u, units.ext rfl,
  map_mul' := λ e₁ e₂, rfl }

/-- Lift a monoid homomorphism `f : G →* function.End α` to a monoid homomorphism
`f : G →* equiv.perm α`. -/
@[simps] def _root_.monoid_hom.to_hom_perm {G : Type*} [group G] (f : G →* function.End α) :
  G →* perm α :=
equiv_units_End.symm.to_monoid_hom.comp f.to_hom_units

theorem mul_apply (f g : perm α) (x) : (f * g) x = f (g x) :=
equiv.trans_apply _ _ _

theorem one_apply (x) : (1 : perm α) x = x := rfl

@[simp] lemma inv_apply_self (f : perm α) (x) : f⁻¹ (f x) = x := f.symm_apply_apply x

@[simp] lemma apply_inv_self (f : perm α) (x) : f (f⁻¹ x) = x := f.apply_symm_apply x

lemma one_def : (1 : perm α) = equiv.refl α := rfl

lemma mul_def (f g : perm α) : f * g = g.trans f := rfl

lemma inv_def (f : perm α) : f⁻¹ = f.symm := rfl

@[simp, norm_cast] lemma coe_one : ⇑(1 : perm α) = id := rfl
@[simp, norm_cast] lemma coe_mul (f g : perm α) : ⇑(f * g) = f ∘ g := rfl
@[norm_cast] lemma coe_pow (f : perm α) (n : ℕ) : ⇑(f ^ n) = (f^[n]) := rfl
@[simp] lemma iterate_eq_pow (f : perm α) (n : ℕ) : (f^[n]) = ⇑(f ^ n) := rfl

lemma eq_inv_iff_eq {f : perm α} {x y : α} : x = f⁻¹ y ↔ f x = y := f.eq_symm_apply

lemma inv_eq_iff_eq {f : perm α} {x y : α} : f⁻¹ x = y ↔ x = f y := f.symm_apply_eq

lemma zpow_apply_comm {α : Type*} (σ : perm α) (m n : ℤ) {x : α} :
  (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x) :=
by rw [←equiv.perm.mul_apply, ←equiv.perm.mul_apply, zpow_mul_comm]

@[simp] lemma image_inv (f : perm α) (s : set α) : ⇑f⁻¹ '' s = f ⁻¹' s := f⁻¹.image_eq_preimage _
@[simp] lemma preimage_inv (f : perm α) (s : set α) : ⇑f⁻¹ ⁻¹' s = f '' s :=
(f.image_eq_preimage _).symm

/-! Lemmas about mixing `perm` with `equiv`. Because we have multiple ways to express
`equiv.refl`, `equiv.symm`, and `equiv.trans`, we want simp lemmas for every combination.
The assumption made here is that if you're using the group structure, you want to preserve it after
simp. -/

@[simp] lemma trans_one {α : Sort*} {β : Type*} (e : α ≃ β) : e.trans (1 : perm β) = e :=
equiv.trans_refl e

@[simp] lemma mul_refl (e : perm α) : e * equiv.refl α = e := equiv.trans_refl e

@[simp] lemma one_symm : (1 : perm α).symm = 1 := equiv.refl_symm

@[simp] lemma refl_inv : (equiv.refl α : perm α)⁻¹ = 1 := equiv.refl_symm

@[simp] lemma one_trans {α : Type*} {β : Sort*} (e : α ≃ β) : (1 : perm α).trans e = e :=
equiv.refl_trans e

@[simp] lemma refl_mul (e : perm α) : equiv.refl α * e = e := equiv.refl_trans e

@[simp] lemma inv_trans_self (e : perm α) : e⁻¹.trans e = 1 := equiv.symm_trans_self e

@[simp] lemma mul_symm (e : perm α) : e * e.symm = 1 := equiv.symm_trans_self e

@[simp] lemma self_trans_inv (e : perm α) : e.trans e⁻¹ = 1 := equiv.self_trans_symm e

@[simp] lemma symm_mul (e : perm α) : e.symm * e = 1 := equiv.self_trans_symm e

/-! Lemmas about `equiv.perm.sum_congr` re-expressed via the group structure. -/

@[simp] lemma sum_congr_mul {α β : Type*} (e : perm α) (f : perm β) (g : perm α) (h : perm β) :
  sum_congr e f * sum_congr g h = sum_congr (e * g) (f * h) :=
sum_congr_trans g h e f

@[simp] lemma sum_congr_inv {α β : Type*} (e : perm α) (f : perm β) :
  (sum_congr e f)⁻¹ = sum_congr e⁻¹ f⁻¹ :=
sum_congr_symm e f

@[simp] lemma sum_congr_one {α β : Type*} :
  sum_congr (1 : perm α) (1 : perm β) = 1 :=
sum_congr_refl

/-- `equiv.perm.sum_congr` as a `monoid_hom`, with its two arguments bundled into a single `prod`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between `α` and `β`. -/
@[simps]
def sum_congr_hom (α β : Type*) :
  perm α × perm β →* perm (α ⊕ β) :=
{ to_fun := λ a, sum_congr a.1 a.2,
  map_one' := sum_congr_one,
  map_mul' := λ a b, (sum_congr_mul _ _ _ _).symm}

lemma sum_congr_hom_injective {α β : Type*} :
  function.injective (sum_congr_hom α β) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  rw prod.mk.inj_iff,
  split; ext i,
  { simpa using equiv.congr_fun h (sum.inl i), },
  { simpa using equiv.congr_fun h (sum.inr i), },
end

@[simp] lemma sum_congr_swap_one {α β : Type*} [decidable_eq α] [decidable_eq β] (i j : α) :
  sum_congr (equiv.swap i j) (1 : perm β) = equiv.swap (sum.inl i) (sum.inl j) :=
sum_congr_swap_refl i j

@[simp] lemma sum_congr_one_swap {α β : Type*} [decidable_eq α] [decidable_eq β] (i j : β) :
  sum_congr (1 : perm α) (equiv.swap i j) = equiv.swap (sum.inr i) (sum.inr j) :=
sum_congr_refl_swap i j

/-! Lemmas about `equiv.perm.sigma_congr_right` re-expressed via the group structure. -/

@[simp] lemma sigma_congr_right_mul {α : Type*} {β : α → Type*}
  (F : Π a, perm (β a)) (G : Π a, perm (β a)) :
  sigma_congr_right F * sigma_congr_right G = sigma_congr_right (F * G) :=
sigma_congr_right_trans G F

@[simp] lemma sigma_congr_right_inv {α : Type*} {β : α → Type*} (F : Π a, perm (β a)) :
  (sigma_congr_right F)⁻¹ = sigma_congr_right (λ a, (F a)⁻¹) :=
sigma_congr_right_symm F

@[simp] lemma sigma_congr_right_one {α : Type*} {β : α → Type*} :
  (sigma_congr_right (1 : Π a, equiv.perm $ β a)) = 1 :=
sigma_congr_right_refl

/-- `equiv.perm.sigma_congr_right` as a `monoid_hom`.

This is particularly useful for its `monoid_hom.range` projection, which is the subgroup of
permutations which do not exchange elements between fibers. -/
@[simps]
def sigma_congr_right_hom {α : Type*} (β : α → Type*) :
  (Π a, perm (β a)) →* perm (Σ a, β a) :=
{ to_fun := sigma_congr_right,
  map_one' := sigma_congr_right_one,
  map_mul' := λ a b, (sigma_congr_right_mul _ _).symm }

lemma sigma_congr_right_hom_injective {α : Type*} {β : α → Type*} :
  function.injective (sigma_congr_right_hom β) :=
begin
  intros x y h,
  ext a b,
  simpa using equiv.congr_fun h ⟨a, b⟩,
end

/-- `equiv.perm.subtype_congr` as a `monoid_hom`. -/
@[simps] def subtype_congr_hom (p : α → Prop) [decidable_pred p] :
  (perm {a // p a}) × (perm {a // ¬ p a}) →* perm α :=
{ to_fun := λ pair, perm.subtype_congr pair.fst pair.snd,
  map_one' := perm.subtype_congr.refl,
  map_mul' := λ _ _, (perm.subtype_congr.trans _ _ _ _).symm }

lemma subtype_congr_hom_injective (p : α → Prop) [decidable_pred p] :
  function.injective (subtype_congr_hom p) :=
begin
  rintros ⟨⟩ ⟨⟩ h,
  rw prod.mk.inj_iff,
  split;
  ext i;
  simpa using equiv.congr_fun h i
end

/-- If `e` is also a permutation, we can write `perm_congr`
completely in terms of the group structure. -/
@[simp] lemma perm_congr_eq_mul (e p : perm α) :
  e.perm_congr p = e * p * e⁻¹ := rfl

section extend_domain

/-! Lemmas about `equiv.perm.extend_domain` re-expressed via the group structure. -/

variables (e : perm α) {p : β → Prop} [decidable_pred p] (f : α ≃ subtype p)

@[simp] lemma extend_domain_one : extend_domain 1 f = 1 :=
extend_domain_refl f

@[simp] lemma extend_domain_inv : (e.extend_domain f)⁻¹ = e⁻¹.extend_domain f := rfl

@[simp] lemma extend_domain_mul (e e' : perm α) :
  (e.extend_domain f) * (e'.extend_domain f) = (e * e').extend_domain f :=
extend_domain_trans _ _ _

/-- `extend_domain` as a group homomorphism -/
@[simps] def extend_domain_hom : perm α →* perm β :=
{ to_fun := λ e, extend_domain e f,
  map_one' := extend_domain_one f,
  map_mul' := λ e e', (extend_domain_mul f e e').symm }

lemma extend_domain_hom_injective : function.injective (extend_domain_hom f) :=
(injective_iff_map_eq_one (extend_domain_hom f)).mpr (λ e he, ext (λ x, f.injective (subtype.ext
  ((extend_domain_apply_image e f x).symm.trans (ext_iff.mp he (f x))))))

@[simp] lemma extend_domain_eq_one_iff {e : perm α} {f : α ≃ subtype p} :
  e.extend_domain f = 1 ↔ e = 1 :=
(injective_iff_map_eq_one' (extend_domain_hom f)).mp (extend_domain_hom_injective f) e

@[simp] lemma extend_domain_pow (n : ℕ) : (e ^ n).extend_domain f = e.extend_domain f ^ n :=
map_pow (extend_domain_hom f) _ _

@[simp] lemma extend_domain_zpow (n : ℤ) : (e ^ n).extend_domain f = e.extend_domain f ^ n :=
map_zpow (extend_domain_hom f) _ _

end extend_domain

section subtype
variables {p : α → Prop} {f : perm α}

/-- If the permutation `f` fixes the subtype `{x // p x}`, then this returns the permutation
  on `{x // p x}` induced by `f`. -/
def subtype_perm (f : perm α) (h : ∀ x, p x ↔ p (f x)) : perm {x // p x} :=
⟨λ x, ⟨f x, (h _).1 x.2⟩, λ x, ⟨f⁻¹ x, (h (f⁻¹ x)).2 $ by simpa using x.2⟩,
  λ _, by simp only [perm.inv_apply_self, subtype.coe_eta, subtype.coe_mk],
  λ _, by simp only [perm.apply_inv_self, subtype.coe_eta, subtype.coe_mk]⟩

@[simp] lemma subtype_perm_apply (f : perm α) (h : ∀ x, p x ↔ p (f x))
  (x : {x // p x}) : subtype_perm f h x = ⟨f x, (h _).1 x.2⟩ := rfl

@[simp] lemma subtype_perm_one (p : α → Prop) (h := λ _, iff.rfl) : @subtype_perm α p 1 h = 1 :=
equiv.ext $ λ ⟨_, _⟩, rfl

@[simp] lemma subtype_perm_mul (f g : perm α) (hf hg) :
  (f.subtype_perm hf * g.subtype_perm hg : perm {x // p x}) =
    (f * g).subtype_perm (λ x, (hg _).trans $ hf _) := rfl

private lemma inv_aux : (∀ x, p x ↔ p (f x)) ↔ ∀ x, p x ↔ p (f⁻¹ x) :=
f⁻¹.surjective.forall.trans $ by simp_rw [f.apply_inv_self, iff.comm]

/-- See `equiv.perm.inv_subtype_perm`-/
lemma subtype_perm_inv (f : perm α) (hf) :
  f⁻¹.subtype_perm hf = (f.subtype_perm $ inv_aux.2 hf : perm {x // p x})⁻¹ := rfl

/-- See `equiv.perm.subtype_perm_inv`-/
@[simp] lemma inv_subtype_perm (f : perm α) (hf) :
  (f.subtype_perm hf : perm {x // p x})⁻¹ = f⁻¹.subtype_perm (inv_aux.1 hf) := rfl

private lemma pow_aux (hf : ∀ x, p x ↔ p (f x)) : ∀ {n : ℕ} x, p x ↔ p ((f ^ n) x)
| 0 x := iff.rfl
| (n + 1) x := (hf _).trans (pow_aux _)

@[simp] lemma subtype_perm_pow (f : perm α) (n : ℕ) (hf) :
  (f.subtype_perm hf : perm {x // p x}) ^ n = (f ^ n).subtype_perm (pow_aux hf) :=
begin
  induction n with n ih,
  { simp },
  { simp_rw [pow_succ', ih, subtype_perm_mul] }
end

private lemma zpow_aux (hf : ∀ x, p x ↔ p (f x)) : ∀ {n : ℤ} x, p x ↔ p ((f ^ n) x)
| (int.of_nat n) := pow_aux hf
| (int.neg_succ_of_nat n) := by { rw zpow_neg_succ_of_nat, exact inv_aux.1 (pow_aux hf) }

@[simp] lemma subtype_perm_zpow (f : perm α) (n : ℤ) (hf) :
  (f.subtype_perm hf ^ n : perm {x // p x}) = (f ^ n).subtype_perm (zpow_aux hf) :=
begin
  induction n with n ih,
  { exact subtype_perm_pow _ _ _ },
  { simp only [zpow_neg_succ_of_nat, subtype_perm_pow, subtype_perm_inv] }
end

variables [decidable_pred p] {a : α}

/-- The inclusion map of permutations on a subtype of `α` into permutations of `α`,
  fixing the other points. -/
def of_subtype : perm (subtype p) →* perm α :=
{ to_fun := λ f, extend_domain f (equiv.refl (subtype p)),
  map_one' := equiv.perm.extend_domain_one _,
  map_mul' := λ f g, (equiv.perm.extend_domain_mul _ f g).symm, }

lemma of_subtype_subtype_perm {f : perm α} (h₁ : ∀ x, p x ↔ p (f x)) (h₂ : ∀ x, f x ≠ x → p x) :
  of_subtype (subtype_perm f h₁) = f :=
equiv.ext $ λ x, begin
  by_cases hx : p x,
  { exact (subtype_perm f h₁).extend_domain_apply_subtype _ hx, },
  { rw [of_subtype, monoid_hom.coe_mk, equiv.perm.extend_domain_apply_not_subtype],
    { exact not_not.mp (λ h, hx (h₂ x (ne.symm h))),  },
    { exact hx, }, }
end

lemma of_subtype_apply_of_mem (f : perm (subtype p)) (ha : p a) : of_subtype f a = f ⟨a, ha⟩ :=
extend_domain_apply_subtype _ _ _

@[simp] lemma of_subtype_apply_coe (f : perm (subtype p)) (x : subtype p) : of_subtype f x = f x :=
subtype.cases_on x $ λ _, of_subtype_apply_of_mem f

lemma of_subtype_apply_of_not_mem (f : perm (subtype p)) (ha : ¬ p a) : of_subtype f a = a :=
extend_domain_apply_not_subtype _ _ ha

lemma mem_iff_of_subtype_apply_mem (f : perm (subtype p)) (x : α) :
  p x ↔ p ((of_subtype f : α → α) x) :=
if h : p x then
by simpa only [h, true_iff, monoid_hom.coe_mk, of_subtype_apply_of_mem f h] using (f ⟨x, h⟩).2
else by simp [h, of_subtype_apply_of_not_mem f h]

@[simp] lemma subtype_perm_of_subtype (f : perm (subtype p)) :
  subtype_perm (of_subtype f) (mem_iff_of_subtype_apply_mem f) = f :=
equiv.ext $ λ x, subtype.coe_injective (of_subtype_apply_coe f x)

/-- Permutations on a subtype are equivalent to permutations on the original type that fix pointwise
the rest. -/
@[simps] protected def subtype_equiv_subtype_perm (p : α → Prop) [decidable_pred p] :
  perm (subtype p) ≃ {f : perm α // ∀ a, ¬p a → f a = a} :=
{ to_fun := λ f, ⟨f.of_subtype, λ a, f.of_subtype_apply_of_not_mem⟩,
  inv_fun := λ f, (f : perm α).subtype_perm
    (λ a, ⟨decidable.not_imp_not.1 $ λ hfa, (f.val.injective (f.prop _ hfa) ▸ hfa),
    decidable.not_imp_not.1 $ λ ha hfa, ha $ f.prop a ha ▸ hfa⟩),
  left_inv := equiv.perm.subtype_perm_of_subtype,
  right_inv := λ f,
    subtype.ext (equiv.perm.of_subtype_subtype_perm _ $ λ a, not.decidable_imp_symm $ f.prop a) }

lemma subtype_equiv_subtype_perm_apply_of_mem (f : perm (subtype p)) (h : p a) :
  perm.subtype_equiv_subtype_perm p f a = f ⟨a, h⟩ :=
f.of_subtype_apply_of_mem h

lemma subtype_equiv_subtype_perm_apply_of_not_mem (f : perm (subtype p)) (h : ¬ p a) :
  perm.subtype_equiv_subtype_perm p f a = a :=
f.of_subtype_apply_of_not_mem h

end subtype
end perm

section swap
variables [decidable_eq α]

@[simp] lemma swap_inv (x y : α) : (swap x y)⁻¹ = swap x y := rfl

@[simp] lemma swap_mul_self (i j : α) : swap i j * swap i j = 1 := swap_swap i j

lemma swap_mul_eq_mul_swap (f : perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
equiv.ext $ λ z, begin
  simp only [perm.mul_apply, swap_apply_def],
  split_ifs;
  simp only [perm.apply_inv_self, *, perm.eq_inv_iff_eq, eq_self_iff_true, not_true] at *
end

lemma mul_swap_eq_swap_mul (f : perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f :=
by rw [swap_mul_eq_mul_swap, perm.inv_apply_self, perm.inv_apply_self]

lemma swap_apply_apply (f : perm α) (x y : α) : swap (f x) (f y) = f * swap x y * f⁻¹ :=
by rw [mul_swap_eq_swap_mul, mul_inv_cancel_right]

/-- Left-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
lemma swap_mul_self_mul (i j : α) (σ : perm α) : equiv.swap i j * (equiv.swap i j * σ) = σ :=
by rw [←mul_assoc, swap_mul_self, one_mul]

/-- Right-multiplying a permutation with `swap i j` twice gives the original permutation.

  This specialization of `swap_mul_self` is useful when using cosets of permutations.
-/
@[simp]
lemma mul_swap_mul_self (i j : α) (σ : perm α) : (σ * equiv.swap i j) * equiv.swap i j = σ :=
by rw [mul_assoc, swap_mul_self, mul_one]

/-- A stronger version of `mul_right_injective` -/
@[simp]
lemma swap_mul_involutive (i j : α) : function.involutive ((*) (equiv.swap i j)) :=
swap_mul_self_mul i j

/-- A stronger version of `mul_left_injective` -/
@[simp]
lemma mul_swap_involutive (i j : α) : function.involutive (* (equiv.swap i j)) :=
mul_swap_mul_self i j

@[simp] lemma swap_eq_one_iff {i j : α} : swap i j = (1 : perm α) ↔ i = j :=
swap_eq_refl_iff

lemma swap_mul_eq_iff {i j : α} {σ : perm α} : swap i j * σ = σ ↔ i = j :=
⟨(assume h, have swap_id : swap i j = 1 := mul_right_cancel (trans h (one_mul σ).symm),
  by {rw [←swap_apply_right i j, swap_id], refl}),
(assume h, by erw [h, swap_self, one_mul])⟩

lemma mul_swap_eq_iff {i j : α} {σ : perm α} : σ * swap i j = σ ↔ i = j :=
⟨(assume h, have swap_id : swap i j = 1 := mul_left_cancel (trans h (one_mul σ).symm),
  by {rw [←swap_apply_right i j, swap_id], refl}),
(assume h, by erw [h, swap_self, mul_one])⟩

lemma swap_mul_swap_mul_swap {x y z : α} (hwz: x ≠ y) (hxz : x ≠ z) :
  swap y z * swap x y * swap y z = swap z x :=
equiv.ext $ λ n, by { simp only [swap_apply_def, perm.mul_apply], split_ifs; cc }

end swap

section add_group
variables [add_group α] (a b : α)

@[simp] lemma add_left_zero : equiv.add_left (0 : α) = 1 := ext zero_add
@[simp] lemma add_right_zero : equiv.add_right (0 : α) = 1 := ext add_zero

@[simp] lemma add_left_add : equiv.add_left (a + b) = equiv.add_left a * equiv.add_left b :=
ext $ add_assoc _ _

@[simp] lemma add_right_add : equiv.add_right (a + b) = equiv.add_right b * equiv.add_right a :=
ext $ λ _, (add_assoc _ _ _).symm

@[simp] lemma inv_add_left : (equiv.add_left a)⁻¹ =  equiv.add_left (-a) := equiv.coe_inj.1 rfl
@[simp] lemma inv_add_right : (equiv.add_right a)⁻¹ =  equiv.add_right (-a) := equiv.coe_inj.1 rfl

@[simp] lemma pow_add_left (n : ℕ) : equiv.add_left a ^ n = equiv.add_left (n • a) :=
by { ext, simp [perm.coe_pow] }

@[simp] lemma pow_add_right (n : ℕ) : equiv.add_right a ^ n = equiv.add_right (n • a) :=
by { ext, simp [perm.coe_pow] }

@[simp] lemma zpow_add_left (n : ℤ) : equiv.add_left a ^ n = equiv.add_left (n • a) :=
(map_zsmul (⟨equiv.add_left, add_left_zero, add_left_add⟩ : α →+ additive (perm α)) _ _).symm

@[simp] lemma zpow_add_right (n : ℤ) : equiv.add_right a ^ n = equiv.add_right (n • a) :=
@zpow_add_left αᵃᵒᵖ _ _ _

end add_group

section group
variables [group α] (a b : α)

@[simp, to_additive] lemma mul_left_one : equiv.mul_left (1 : α) = 1 := ext one_mul
@[simp, to_additive] lemma mul_right_one : equiv.mul_right (1 : α) = 1 := ext mul_one

@[simp, to_additive]
lemma mul_left_mul : equiv.mul_left (a * b) = equiv.mul_left a * equiv.mul_left b :=
ext $ mul_assoc _ _

@[simp, to_additive]
lemma mul_right_mul : equiv.mul_right (a * b) = equiv.mul_right b * equiv.mul_right a :=
ext $ λ _, (mul_assoc _ _ _).symm

@[simp, to_additive inv_add_left]
lemma inv_mul_left : (equiv.mul_left a)⁻¹ = equiv.mul_left a⁻¹ := equiv.coe_inj.1 rfl
@[simp, to_additive inv_add_right]
lemma inv_mul_right : (equiv.mul_right a)⁻¹ = equiv.mul_right a⁻¹ := equiv.coe_inj.1 rfl

@[simp, to_additive pow_add_left]
lemma pow_mul_left (n : ℕ) : equiv.mul_left a ^ n = equiv.mul_left (a ^ n)  :=
by { ext, simp [perm.coe_pow] }

@[simp, to_additive pow_add_right]
lemma pow_mul_right (n : ℕ) : equiv.mul_right a ^ n = equiv.mul_right (a ^ n) :=
by { ext, simp [perm.coe_pow] }

@[simp, to_additive zpow_add_left]
lemma zpow_mul_left (n : ℤ) : equiv.mul_left a ^ n = equiv.mul_left (a ^ n) :=
(map_zpow (⟨equiv.mul_left, mul_left_one, mul_left_mul⟩ : α →* perm α) _ _).symm

@[simp, to_additive zpow_add_right]
lemma zpow_mul_right : ∀ n : ℤ, equiv.mul_right a ^ n = equiv.mul_right (a ^ n)
| (int.of_nat n) := by simp
| (int.neg_succ_of_nat n) := by simp

end group
end equiv

open equiv function

namespace set
variables {α : Type*} {f : perm α} {s t : set α}

@[simp] lemma bij_on_perm_inv : bij_on ⇑f⁻¹ t s ↔ bij_on f s t := equiv.bij_on_symm

alias bij_on_perm_inv ↔ bij_on.of_perm_inv bij_on.perm_inv

lemma maps_to.perm_pow : maps_to f s s → ∀ n : ℕ, maps_to ⇑(f ^ n) s s :=
by { simp_rw equiv.perm.coe_pow, exact maps_to.iterate }
lemma surj_on.perm_pow : surj_on f s s → ∀ n : ℕ, surj_on ⇑(f ^ n) s s :=
by { simp_rw equiv.perm.coe_pow, exact surj_on.iterate }
lemma bij_on.perm_pow : bij_on f s s → ∀ n : ℕ, bij_on ⇑(f ^ n) s s :=
by { simp_rw equiv.perm.coe_pow, exact bij_on.iterate }

lemma bij_on.perm_zpow (hf : bij_on f s s) : ∀ n : ℤ, bij_on ⇑(f ^ n) s s
| (int.of_nat n) := hf.perm_pow _
| (int.neg_succ_of_nat n) := by { rw zpow_neg_succ_of_nat, exact (hf.perm_pow _).perm_inv }

end set
