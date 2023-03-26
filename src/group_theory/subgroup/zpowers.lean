/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import group_theory.subgroup.basic

/-!
# Subgroups generated by an element

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Tags
subgroup, subgroups

-/

variables {G : Type*} [group G]
variables {A : Type*} [add_group A]
variables {N : Type*} [group N]

namespace subgroup

/-- The subgroup generated by an element. -/
def zpowers (g : G) : subgroup G :=
subgroup.copy (zpowers_hom G g).range (set.range ((^) g : ℤ → G)) rfl

@[simp] lemma mem_zpowers (g : G) : g ∈ zpowers g := ⟨1, zpow_one _⟩

lemma zpowers_eq_closure (g : G) : zpowers g = closure {g} :=
by { ext, exact mem_closure_singleton.symm }

@[simp] lemma range_zpowers_hom (g : G) : (zpowers_hom G g).range = zpowers g := rfl

lemma mem_zpowers_iff {g h : G} :
  h ∈ zpowers g ↔ ∃ (k : ℤ), g ^ k = h :=
iff.rfl

@[simp] lemma zpow_mem_zpowers (g : G) (k : ℤ) : g^k ∈ zpowers g :=
mem_zpowers_iff.mpr ⟨k, rfl⟩

@[simp] lemma npow_mem_zpowers (g : G) (k : ℕ) : g^k ∈ zpowers g :=
(zpow_coe_nat g k) ▸ zpow_mem_zpowers g k

@[simp] lemma forall_zpowers {x : G} {p : zpowers x → Prop} :
  (∀ g, p g) ↔ ∀ m : ℤ, p ⟨x ^ m, m, rfl⟩ :=
set.forall_subtype_range_iff

@[simp] lemma exists_zpowers {x : G} {p : zpowers x → Prop} :
  (∃ g, p g) ↔ ∃ m : ℤ, p ⟨x ^ m, m, rfl⟩ :=
set.exists_subtype_range_iff

lemma forall_mem_zpowers {x : G} {p : G → Prop} :
  (∀ g ∈ zpowers x, p g) ↔ ∀ m : ℤ, p (x ^ m) :=
set.forall_range_iff

lemma exists_mem_zpowers {x : G} {p : G → Prop} :
  (∃ g ∈ zpowers x, p g) ↔ ∃ m : ℤ, p (x ^ m) :=
set.exists_range_iff

instance (a : G) : countable (zpowers a) :=
((zpowers_hom G a).range_restrict_surjective.comp multiplicative.of_add.surjective).countable

end subgroup

namespace add_subgroup

/-- The subgroup generated by an element. -/
def zmultiples (a : A) : add_subgroup A :=
add_subgroup.copy (zmultiples_hom A a).range (set.range ((• a) : ℤ → A)) rfl

@[simp] lemma range_zmultiples_hom (a : A) : (zmultiples_hom A a).range = zmultiples a := rfl

attribute [to_additive add_subgroup.zmultiples] subgroup.zpowers
attribute [to_additive add_subgroup.mem_zmultiples] subgroup.mem_zpowers
attribute [to_additive add_subgroup.zmultiples_eq_closure] subgroup.zpowers_eq_closure
attribute [to_additive add_subgroup.range_zmultiples_hom] subgroup.range_zpowers_hom
attribute [to_additive add_subgroup.mem_zmultiples_iff] subgroup.mem_zpowers_iff
attribute [to_additive add_subgroup.zsmul_mem_zmultiples] subgroup.zpow_mem_zpowers
attribute [to_additive add_subgroup.nsmul_mem_zmultiples] subgroup.npow_mem_zpowers
attribute [to_additive add_subgroup.forall_zmultiples] subgroup.forall_zpowers
attribute [to_additive add_subgroup.forall_mem_zmultiples] subgroup.forall_mem_zpowers
attribute [to_additive add_subgroup.exists_zmultiples] subgroup.exists_zpowers
attribute [to_additive add_subgroup.exists_mem_zmultiples] subgroup.exists_mem_zpowers

instance (a : A) : countable (zmultiples a) :=
(zmultiples_hom A a).range_restrict_surjective.countable

section ring

variables {R : Type*} [ring R] (r : R) (k : ℤ)

@[simp] lemma int_cast_mul_mem_zmultiples :
  ↑(k : ℤ) * r ∈ zmultiples r :=
by simpa only [← zsmul_eq_mul] using zsmul_mem_zmultiples r k

@[simp] lemma int_cast_mem_zmultiples_one :
  ↑(k : ℤ) ∈ zmultiples (1 : R) :=
mem_zmultiples_iff.mp ⟨k, by simp⟩

end ring

end add_subgroup

@[simp, to_additive map_zmultiples] lemma monoid_hom.map_zpowers (f : G →* N) (x : G) :
  (subgroup.zpowers x).map f = subgroup.zpowers (f x) :=
by rw [subgroup.zpowers_eq_closure, subgroup.zpowers_eq_closure, f.map_closure, set.image_singleton]

lemma int.mem_zmultiples_iff {a b : ℤ} :
  b ∈ add_subgroup.zmultiples a ↔ a ∣ b :=
exists_congr (λ k, by rw [mul_comm, eq_comm, ← smul_eq_mul])

lemma of_mul_image_zpowers_eq_zmultiples_of_mul { x : G } :
  additive.of_mul '' ((subgroup.zpowers x) : set G) = add_subgroup.zmultiples (additive.of_mul x) :=
begin
  ext y,
  split,
  { rintro ⟨z, ⟨m, hm⟩, hz2⟩,
    use m,
    simp only,
    rwa [← of_mul_zpow, hm] },
  { rintros ⟨n, hn⟩,
    refine ⟨x ^ n, ⟨n, rfl⟩, _⟩,
    rwa of_mul_zpow }
end

lemma of_add_image_zmultiples_eq_zpowers_of_add {x : A} :
  multiplicative.of_add '' ((add_subgroup.zmultiples x) : set A) =
  subgroup.zpowers (multiplicative.of_add x) :=
begin
  symmetry,
  rw equiv.eq_image_iff_symm_image_eq,
  exact of_mul_image_zpowers_eq_zmultiples_of_mul,
end

namespace subgroup
variables {s : set G} {g : G}

@[to_additive zmultiples_is_commutative]
instance zpowers_is_commutative (g : G) : (zpowers g).is_commutative :=
⟨⟨λ ⟨_, _, h₁⟩ ⟨_, _, h₂⟩, by rw [subtype.ext_iff, coe_mul, coe_mul,
  subtype.coe_mk, subtype.coe_mk, ←h₁, ←h₂, zpow_mul_comm]⟩⟩

@[simp, to_additive zmultiples_le]
lemma zpowers_le {g : G} {H : subgroup G} : zpowers g ≤ H ↔ g ∈ H :=
by rw [zpowers_eq_closure, closure_le, set.singleton_subset_iff, set_like.mem_coe]

alias zpowers_le ↔ _ zpowers_le_of_mem
alias add_subgroup.zmultiples_le ↔ _ _root_.add_subgroup.zmultiples_le_of_mem

attribute [to_additive zmultiples_le_of_mem] zpowers_le_of_mem

@[simp, to_additive zmultiples_eq_bot] lemma zpowers_eq_bot {g : G} : zpowers g = ⊥ ↔ g = 1 :=
by rw [eq_bot_iff, zpowers_le, mem_bot]

@[to_additive zmultiples_ne_bot] lemma zpowers_ne_bot : zpowers g ≠ ⊥ ↔ g ≠ 1 :=
zpowers_eq_bot.not

@[simp, to_additive zmultiples_zero_eq_bot] lemma zpowers_one_eq_bot :
   subgroup.zpowers (1 : G) = ⊥ :=
subgroup.zpowers_eq_bot.mpr rfl

@[to_additive coe_zmultiplies_subset] lemma coe_zpowers_subset (h_one : (1 : G) ∈ s)
  (h_mul : ∀ a ∈ s, a * g ∈ s) (h_inv : ∀ a ∈ s, a * g⁻¹ ∈ s) : ↑(zpowers g) ⊆ s :=
begin
  rintro _ ⟨n, rfl⟩,
  induction n using int.induction_on with n ih n ih,
  { rwa zpow_zero },
  { rw zpow_add_one,
    exact h_mul _ ih },
  { rw zpow_sub_one,
    exact h_inv _ ih }
end

@[to_additive coe_zmultiplies_subset'] lemma coe_zpowers_subset' (h_one : (1 : G) ∈ s)
  (h_mul : ∀ a ∈ s, g * a ∈ s) (h_inv : ∀ a ∈ s, g⁻¹ * a ∈ s) : ↑(zpowers g) ⊆ s :=
begin
  rintro _ ⟨n, rfl⟩,
  induction n using int.induction_on with n ih n ih,
  { rwa zpow_zero },
  { rw [add_comm, zpow_add, zpow_one],
    exact h_mul _ ih },
  { rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one],
    exact h_inv _ ih }
end

@[to_additive] lemma centralizer_closure (S : set G) :
  (closure S).centralizer = ⨅ g ∈ S, (zpowers g).centralizer :=
le_antisymm (le_infi $ λ g, le_infi $ λ hg, centralizer_le $ zpowers_le.2 $ subset_closure hg)
  $ le_centralizer_iff.1 $ (closure_le _).2
  $ λ g, set_like.mem_coe.2 ∘ zpowers_le.1 ∘ le_centralizer_iff.1 ∘ infi_le_of_le g ∘ infi_le _

@[to_additive] lemma center_eq_infi (S : set G) (hS : closure S = ⊤) :
  center G = ⨅ g ∈ S, centralizer (zpowers g) :=
by rw [←centralizer_top, ←hS, centralizer_closure]

@[to_additive] lemma center_eq_infi' (S : set G) (hS : closure S = ⊤) :
  center G = ⨅ g : S, centralizer (zpowers g) :=
by rw [center_eq_infi S hS, ←infi_subtype'']

end subgroup
