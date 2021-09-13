/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import tactic.split_ifs
import tactic.simpa
import tactic.congr
import algebra.group.to_additive
/-!
# Instances and theorems on pi types

This file provides basic definitions and notation instances for Pi types.

Instances of more sophisticated classes are defined in `pi.lean` files elsewhere.
-/

universes u v₁ v₂ v₃
variable {I : Type u}     -- The indexing type
-- The families of types already equipped with instances
variables {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}
variables (x y : Π i, f i) (i : I)

namespace pi

/-! `1`, `0`, `+`, `*`, `-`, `⁻¹`, and `/` are defined pointwise. -/

@[to_additive] instance has_one [∀ i, has_one $ f i] :
  has_one (Π i : I, f i) :=
⟨λ _, 1⟩
@[simp, to_additive] lemma one_apply [∀ i, has_one $ f i] : (1 : Π i, f i) i = 1 := rfl

@[to_additive] lemma one_def [Π i, has_one $ f i] : (1 : Π i, f i) = λ i, 1 := rfl

@[to_additive]
instance has_mul [∀ i, has_mul $ f i] :
  has_mul (Π i : I, f i) :=
⟨λ f g i, f i * g i⟩
@[simp, to_additive] lemma mul_apply [∀ i, has_mul $ f i] : (x * y) i = x i * y i := rfl

@[to_additive] lemma mul_def [Π i, has_mul $ f i] : x * y = λ i, x i * y i := rfl

@[to_additive] instance has_inv [∀ i, has_inv $ f i] :
  has_inv (Π i : I, f i) :=
  ⟨λ f i, (f i)⁻¹⟩
@[simp, to_additive] lemma inv_apply [∀ i, has_inv $ f i] : x⁻¹ i = (x i)⁻¹ := rfl

@[to_additive] instance has_div [Π i, has_div $ f i] :
  has_div (Π i : I, f i) :=
⟨λ f g i, f i / g i⟩
@[simp, to_additive] lemma div_apply [Π i, has_div $ f i] : (x / y) i = x i / y i := rfl
@[to_additive] lemma div_def [Π i, has_div $ f i] : x / y = λ i, x i / y i := rfl

section

variables [decidable_eq I]
variables [Π i, has_zero (f i)] [Π i, has_zero (g i)] [Π i, has_zero (h i)]

/-- The function supported at `i`, with value `x` there. -/
def single (i : I) (x : f i) : Π i, f i :=
function.update 0 i x

@[simp] lemma single_eq_same (i : I) (x : f i) : single i x i = x :=
function.update_same i x _

@[simp] lemma single_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : single i x i' = 0 :=
function.update_noteq h x _

/-- Abbreviation for `single_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[simp] lemma single_eq_of_ne' {i i' : I} (h : i ≠ i') (x : f i) : single i x i' = 0 :=
single_eq_of_ne h.symm x

@[simp] lemma single_zero (i : I) : single i (0 : f i) = 0 :=
function.update_eq_self _ _

/-- On non-dependent functions, `pi.single` can be expressed as an `ite` -/
lemma single_apply {β : Sort*} [has_zero β] (i : I) (x : β) (i' : I) :
  single i x i' = if i' = i then x else 0 :=
function.update_apply 0 i x i'

/-- On non-dependent functions, `pi.single` is symmetric in the two indices. -/
lemma single_comm {β : Sort*} [has_zero β] (i : I) (x : β) (i' : I) :
  single i x i' = single i' x i :=
by simp only [single_apply, eq_comm]; congr -- deal with `decidable_eq`

lemma apply_single (f' : Π i, f i → g i) (hf' : ∀ i, f' i 0 = 0) (i : I) (x : f i) (j : I):
  f' j (single i x j) = single i (f' i x) j :=
by simpa only [pi.zero_apply, hf', single] using function.apply_update f' 0 i x j

lemma apply_single₂ (f' : Π i, f i → g i → h i) (hf' : ∀ i, f' i 0 0 = 0)
  (i : I) (x : f i) (y : g i) (j : I):
  f' j (single i x j) (single i y j) = single i (f' i x y) j :=
begin
  by_cases h : j = i,
  { subst h, simp only [single_eq_same] },
  { simp only [single_eq_of_ne h, hf'] },
end

lemma single_op {g : I → Type*} [Π i, has_zero (g i)] (op : Π i, f i → g i) (h : ∀ i, op i 0 = 0)
  (i : I) (x : f i) :
  single i (op i x) = λ j, op j (single i x j) :=
eq.symm $ funext $ apply_single op h i x

lemma single_op₂ {g₁ g₂ : I → Type*} [Π i, has_zero (g₁ i)] [Π i, has_zero (g₂ i)]
  (op : Π i, g₁ i → g₂ i → f i) (h : ∀ i, op i 0 0 = 0) (i : I) (x₁ : g₁ i) (x₂ : g₂ i) :
  single i (op i x₁ x₂) = λ j, op j (single i x₁ j) (single i x₂ j) :=
eq.symm $ funext $ apply_single₂ op h i x₁ x₂

variables (f)

lemma single_injective (i : I) : function.injective (single i : f i → Π i, f i) :=
function.update_injective _ i

section extend

variables {ι : Type u} {η : Type v₁} (R : Type v₂)

/-- For any type `R` with `1`, we extend any `f : ι → R` to `η → R` along a function
`s : ι → η`. -/
@[to_additive "For any type `R` with `0`, we extend any `f : ι → R` to `η → R`
along a function `s : ι → η`."]
noncomputable def extend_by_one [has_one R] (s : ι → η) (f : ι → R) : η → R :=
function.extend s f 1

@[simp, to_additive]
lemma extend_by_one_apply [has_one R] {s : ι → η} (f : ι → R) (hs : function.injective s) (i : ι) :
  extend_by_one R s f (s i) = f i := function.extend_apply hs _ _ _

@[to_additive]
lemma extend_by_one_apply' [has_one R] (s : ι → η) (f : ι → R) (x : η) (hi : ¬∃ i, s i = x) :
  extend_by_one R s f x = 1 :=
by { classical, simp [extend_by_one, function.extend_def, hi] }

@[to_additive]
lemma extend_by_one_injective [has_one R] {s : ι → η} (hs : function.injective s) :
  function.injective (extend_by_one R s) :=
begin
  intros f g hfg,
  ext,
  replace hfg := congr_fun hfg (s x),
  rwa [extend_by_one_apply R f hs, extend_by_one_apply R g hs] at hfg
end

end extend

end
end pi

lemma subsingleton.pi_single_eq {α : Type*} [decidable_eq I] [subsingleton I] [has_zero α]
  (i : I) (x : α) :
  pi.single i x = λ _, x :=
funext $ λ j, by rw [subsingleton.elim j i, pi.single_eq_same]
