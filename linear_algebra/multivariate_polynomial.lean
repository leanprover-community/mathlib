/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Multivariate Polynomial
-/
import data.finsupp linear_algebra.basic algebra.ring

open set function finsupp lattice

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Multivariate polynomial, where `σ` is the index set of the variables and
  `α` is the coefficient ring -/
def mv_polynomial (σ : Type*) (α : Type*) [comm_semiring α] := (σ →₀ ℕ) →₀ α

namespace mv_polynomial
variables {σ : Type*} {a a' a₁ a₂ : α} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}
variables [decidable_eq σ] [decidable_eq α]

section comm_semiring
variables [comm_semiring α] {p q : mv_polynomial σ α}

instance : has_zero (mv_polynomial σ α) := finsupp.has_zero
instance : has_one (mv_polynomial σ α) := finsupp.has_one
instance : has_add (mv_polynomial σ α) := finsupp.has_add
instance : has_mul (mv_polynomial σ α) := finsupp.has_mul
instance : comm_semiring (mv_polynomial σ α) := finsupp.to_comm_semiring

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (s : σ →₀ ℕ) (a : α) : mv_polynomial σ α := single s a

/-- `C a` is the constant polynomial with value `a` -/
def C (a : α) : mv_polynomial σ α := monomial 0 a

/-- `X n` is the polynomial with value X_n -/
def X (n : σ) : mv_polynomial σ α := monomial (single n 1) 1

@[simp] lemma C_0 : C 0 = (0 : mv_polynomial σ α) := by simp [C, monomial]; refl

@[simp] lemma C_1 : C 1 = (1 : mv_polynomial σ α) := rfl

@[simp] lemma C_mul_monomial : C a * monomial s a' = monomial s (a * a') :=
by simp [C, monomial, single_mul_single]

lemma X_pow_eq_single : X n ^ e = monomial (single n e) (1 : α) :=
begin
  induction e,
  { simp [X], refl },
  { simp [pow_succ, e_ih],
    simp [X, monomial, single_mul_single, nat.succ_eq_add_one] }
end

lemma monomial_add_single : monomial (s + single n e) a = (monomial s a * X n ^ e):=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_single_add : monomial (single n e + s) a = (X n ^ e * monomial s a):=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_eq : monomial s a = C a * (s.prod $ λn e, X n ^ e : mv_polynomial σ α) :=
begin
  apply @finsupp.induction σ ℕ _ _ _ _ s,
  { simp [C, prod_zero_index]; exact (mul_one _).symm },
  { assume n e s hns he ih,
    simp [prod_add_index, prod_single_index, pow_zero, pow_add, (mul_assoc _ _ _).symm, ih.symm,
      monomial_add_single] }
end

@[recursor 7]
lemma induction_on {M : mv_polynomial σ α → Prop} (p : mv_polynomial σ α)
  (h_C : ∀a, M (C a)) (h_add : ∀p q, M p → M q → M (p + q)) (h_X : ∀p n, M p → M (p * X n)) :
  M p :=
have ∀s a, M (monomial s a),
begin
  assume s a,
  apply @finsupp.induction σ ℕ _ _ _ _ s,
  { show M (monomial 0 a), from h_C a, },
  { assume n e p hpn he ih,
    have : ∀e:ℕ, M (monomial p a * X n ^ e),
    { intro e,
      induction e,
      { simp [ih] },
      { simp [ih, pow_succ', (mul_assoc _ _ _).symm, h_X, e_ih] } },
    simp [monomial_add_single, this] }
end,
finsupp.induction p
  (by have : M (C 0) := h_C 0; rwa [C_0] at this)
  (assume s a p hsp ha hp, h_add _ _ (this s a) hp)

section eval
variables {f : σ → α}

/-- Evaluate a polynomial `p` given a valuation `f` of all the variables -/
def eval (f : σ → α) (p : mv_polynomial σ α) : α :=
p.sum (λs a, a * s.prod (λn e, f n ^ e))

@[simp] lemma eval_zero : (0 : mv_polynomial σ α).eval f = 0 :=
finsupp.sum_zero_index

lemma eval_add : (p + q).eval f = p.eval f + q.eval f :=
finsupp.sum_add_index (by simp) (by simp [add_mul])

lemma eval_monomial : (monomial s a).eval f = a * s.prod (λn e, f n ^ e) :=
finsupp.sum_single_index (zero_mul _)

@[simp] lemma eval_C : (C a).eval f = a :=
by simp [eval_monomial, C, prod_zero_index]

@[simp] lemma eval_X : (X n).eval f = f n :=
by simp [eval_monomial, X, prod_single_index, pow_one]

lemma eval_mul_monomial :
  ∀{s a}, (p * monomial s a).eval f = p.eval f * a * s.prod (λn e, f n ^ e) :=
begin
  apply mv_polynomial.induction_on p,
  { assume a' s a, by simp [C_mul_monomial, eval_monomial] },
  { assume p q ih_p ih_q, simp [add_mul, eval_add, ih_p, ih_q] },
  { assume p n ih s a,
    from calc (p * X n * monomial s a).eval f = (p * monomial (single n 1 + s) a).eval f :
        by simp [monomial_single_add, -add_comm, pow_one, mul_assoc]
      ... = (p * monomial (single n 1) 1).eval f * a * s.prod (λn e, f n ^ e) :
        by simp [ih, prod_single_index, prod_add_index, pow_one, pow_add, mul_assoc, mul_left_comm,
          -add_comm] }
end

lemma eval_mul : ∀{p}, (p * q).eval f = p.eval f * q.eval f :=
begin
  apply mv_polynomial.induction_on q,
  { simp [C, eval_monomial, eval_mul_monomial, prod_zero_index] },
  { simp [mul_add, eval_add] {contextual := tt} },
  { simp [X, eval_monomial, eval_mul_monomial, (mul_assoc _ _ _).symm] { contextual := tt} }
end

end eval

section vars

/-- `vars p` is the set of variables appearing in the polynomial `p` -/
def vars (p : mv_polynomial σ α) : finset σ := p.support.bind finsupp.support

@[simp] lemma vars_0 : (0 : mv_polynomial σ α).vars = ∅ :=
show (0 : (σ →₀ ℕ) →₀ α).support.bind finsupp.support = ∅, by simp

@[simp] lemma vars_monomial (h : a ≠ 0) : (monomial s a).vars = s.support :=
show (single s a : (σ →₀ ℕ) →₀ α).support.bind finsupp.support = s.support,
  by simp [support_single_ne_zero, h]

@[simp] lemma vars_C : (C a : mv_polynomial σ α).vars = ∅ :=
decidable.by_cases
  (assume h : a = 0, by simp [h])
  (assume h : a ≠ 0, by simp [C, h])

@[simp] lemma vars_X (h : 0 ≠ (1 : α)) : (X n : mv_polynomial σ α).vars = {n} :=
calc (X n : mv_polynomial σ α).vars = (single n 1).support : vars_monomial h.symm
  ... = {n} : by rw [support_single_ne_zero nat.zero_ne_one.symm]

end vars

section degree_of
/-- `degree_of n p` gives the highest power of X_n that appears in `p` -/
def degree_of (n : σ) (p : mv_polynomial σ α) : ℕ := p.support.sup (λs, s n)

end degree_of

section total_degree
/-- `total_degree p` gives the maximum |s| over the monomials X^s in `p` -/
def total_degree (p : mv_polynomial σ α) : ℕ := p.support.sup (λs, s.sum $ λn e, e)

end total_degree

end comm_semiring

section comm_ring
variable [comm_ring α]
instance : ring (mv_polynomial σ α) := finsupp.to_ring
instance : has_scalar α (mv_polynomial σ α) := finsupp.to_has_scalar
instance : module α (mv_polynomial σ α) := finsupp.to_module

instance {f : σ → α} : is_ring_hom (eval f) := ⟨λ x y, eval_add, λ x y, eval_mul, eval_C⟩

-- `mv_polynomial σ` is a functor (incomplete)
definition functorial [decidable_eq β] [comm_ring β] (i : α → β) [is_ring_hom i] :
  mv_polynomial σ α → mv_polynomial σ β :=
map_range i (is_ring_hom.map_zero i)

end comm_ring

end mv_polynomial
