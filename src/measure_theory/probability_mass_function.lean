/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/
import topology.instances.ennreal

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0` such that the values have (infinite) sum `1`.

This file features the monadic structure of `pmf` and the Bernoulli distribution

## Implementation Notes

This file is not yet connected to the `measure_theory` library in any way.
At some point we need to define a `measure` from a `pmf` and prove the appropriate lemmas about
that.

## Tags

probability mass function, discrete probability measure, bernoulli distribution
-/
noncomputable theory
variables {α : Type*} {β : Type*} {γ : Type*}
open_locale classical big_operators nnreal

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0` such that
  the values have (infinite) sum `1`. -/
def {u} pmf (α : Type u) : Type u := { f : α → ℝ≥0 // has_sum f 1 }

namespace pmf

instance : has_coe_to_fun (pmf α) := ⟨λ p, α → ℝ≥0, λ p a, p.1 a⟩

@[ext] protected lemma ext : ∀ {p q : pmf α}, (∀ a, p a = q a) → p = q
| ⟨f, hf⟩ ⟨g, hg⟩ eq :=  subtype.eq $ funext eq

lemma has_sum_coe_one (p : pmf α) : has_sum p 1 := p.2

lemma summable_coe (p : pmf α) : summable p := (p.has_sum_coe_one).summable

@[simp] lemma tsum_coe (p : pmf α) : (∑' a, p a) = 1 := p.has_sum_coe_one.tsum_eq

/-- The support of a `pmf` is the set where it is nonzero. -/
def support (p : pmf α) : set α := {a | p.1 a ≠ 0}

/-- The pure `pmf` is the `pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : pmf α := ⟨λ a', if a' = a then 1 else 0, has_sum_ite_eq _ _⟩

@[simp] lemma pure_apply (a a' : α) : pure a a' = (if a' = a then 1 else 0) := rfl

instance [inhabited α] : inhabited (pmf α) := ⟨pure (default α)⟩

lemma coe_le_one (p : pmf α) (a : α) : p a ≤ 1 :=
has_sum_le (by intro b; split_ifs; simp [h]; exact le_refl _) (has_sum_ite_eq a (p a)) p.2

protected lemma bind.summable (p : pmf α) (f : α → pmf β) (b : β) :
  summable (λ a : α, p a * f a b) :=
begin
  refine nnreal.summable_of_le (assume a, _) p.summable_coe,
  suffices : p a * f a b ≤ p a * 1, { simpa },
  exact mul_le_mul_of_nonneg_left ((f a).coe_le_one _) (p a).2
end

/-- The monadic bind operation for `pmf`. -/
def bind (p : pmf α) (f : α → pmf β) : pmf β :=
⟨λ b, ∑'a, p a * f a b,
  begin
    apply ennreal.has_sum_coe.1,
    simp only [ennreal.coe_tsum (bind.summable p f _)],
    rw [ennreal.summable.has_sum_iff, ennreal.tsum_comm],
    simp [ennreal.tsum_mul_left, (ennreal.coe_tsum (f _).summable_coe).symm,
      (ennreal.coe_tsum p.summable_coe).symm]
  end⟩

@[simp] lemma bind_apply (p : pmf α) (f : α → pmf β) (b : β) : p.bind f b = (∑'a, p a * f a b) :=
rfl

lemma coe_bind_apply (p : pmf α) (f : α → pmf β) (b : β) :
  (p.bind f b : ennreal) = (∑'a, p a * f a b) :=
eq.trans (ennreal.coe_tsum $ bind.summable p f b) $ by simp

@[simp] lemma pure_bind (a : α) (f : α → pmf β) : (pure a).bind f = f a :=
have ∀ b a', ite (a' = a) 1 0 * f a' b = ite (a' = a) (f a b) 0, from
  assume b a', by split_ifs; simp; subst h; simp,
by ext b; simp [this]

@[simp] lemma bind_pure (p : pmf α) : p.bind pure = p :=
have ∀ a a', (p a * ite (a' = a) 1 0) = ite (a = a') (p a') 0, from
  assume a a', begin split_ifs; try { subst a }; try { subst a' }; simp * at * end,
by ext b; simp [this]

@[simp] lemma bind_bind (p : pmf α) (f : α → pmf β) (g : β → pmf γ) :
  (p.bind f).bind g = p.bind (λ a, (f a).bind g) :=
begin
  ext1 b,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm,
             ennreal.tsum_mul_right.symm],
  rw [ennreal.tsum_comm],
  simp [mul_assoc, mul_left_comm, mul_comm]
end

lemma bind_comm (p : pmf α) (q : pmf β) (f : α → β → pmf γ) :
  p.bind (λ a, q.bind (f a)) = q.bind (λ b, p.bind (λ a, f a b)) :=
begin
  ext1 b,
  simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm,
             ennreal.tsum_mul_right.symm],
  rw [ennreal.tsum_comm],
  simp [mul_assoc, mul_left_comm, mul_comm]
end

/-- The functorial action of a function on a `pmf`. -/
def map (f : α → β) (p : pmf α) : pmf β := bind p (pure ∘ f)

lemma bind_pure_comp (f : α → β) (p : pmf α) : bind p (pure ∘ f) = map f p := rfl

lemma map_id (p : pmf α) : map id p = p := by simp [map]

lemma map_comp (p : pmf α) (f : α → β) (g : β → γ) : (p.map f).map g = p.map (g ∘ f) :=
by simp [map]

lemma pure_map (a : α) (f : α → β) : (pure a).map f = pure (f a) :=
by simp [map]

/-- The monadic sequencing operation for `pmf`. -/
def seq (f : pmf (α → β)) (p : pmf α) : pmf β := f.bind (λ m, p.bind $ λ a, pure (m a))

/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/
def of_multiset (s : multiset α) (hs : s ≠ 0) : pmf α :=
⟨λ a, s.count a / s.card,
  have ∑ a in s.to_finset, (s.count a : ℝ) / s.card = 1,
    by simp [div_eq_inv_mul, finset.mul_sum.symm, (finset.sum_nat_cast _ _).symm, hs],
  have ∑ a in s.to_finset, (s.count a : ℝ≥0) / s.card = 1,
    by rw [← nnreal.eq_iff, nnreal.coe_one, ← this, nnreal.coe_sum]; simp,
  begin
    rw ← this,
    apply has_sum_sum_of_ne_finset_zero,
    simp {contextual := tt},
  end⟩

/-- Given a finite type `α` and a function `f : α → ℝ≥0` with sum 1, we get a `pmf`. -/
def of_fintype [fintype α] (f : α → ℝ≥0) (h : ∑ x, f x = 1) : pmf α :=
⟨f, h ▸ has_sum_sum_of_ne_finset_zero (by simp)⟩

/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p : ℝ≥0) (h : p ≤ 1) : pmf bool :=
of_fintype (λ b, cond b p (1 - p)) (nnreal.eq $ by simp [h])

end pmf
