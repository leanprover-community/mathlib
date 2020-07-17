/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import tactic.ring_exp
import tactic.chain
import data.monoid_algebra
import data.finset.sort

/-!
# Theory of univariate polynomials

Polynomials are represented as `add_monoid_algebra R ℕ`, where `R` is a commutative semiring.
In this file, we define `polynomial`, provide basic instances, and prove an `ext` lemma.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable


/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
def polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℕ

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u
variables {R : Type u} {a : R} {m n : ℕ}

section semiring
variables [semiring R] {p q : polynomial R}

instance : inhabited (polynomial R) := finsupp.inhabited
instance : semiring (polynomial R) := add_monoid_algebra.semiring
instance : has_scalar R (polynomial R) := add_monoid_algebra.has_scalar
instance : semimodule R (polynomial R) := add_monoid_algebra.semimodule

instance subsingleton [subsingleton R] : subsingleton (polynomial R) :=
⟨λ _ _, ext (λ _, subsingleton.elim _ _)⟩

/-- The coercion turning a `polynomial` into the function which reports the coefficient of a given
monomial `X^n` -/
def coeff_coe_to_fun : has_coe_to_fun (polynomial R) :=
finsupp.has_coe_to_fun

local attribute [instance] coeff_coe_to_fun


@[simp] lemma support_zero : (0 : polynomial R).support = ∅ := rfl

/-- `monomial s a` is the monomial `a * X^s` -/
@[reducible]
def monomial (n : ℕ) (a : R) : polynomial R := finsupp.single n a

@[simp] lemma monomial_zero_right (n : ℕ) :
  monomial n (0 : R) = 0 :=
by simp [monomial]

lemma monomial_add (n : ℕ) (r s : R) :
  monomial n (r + s) = monomial n r + monomial n s :=
by simp [monomial]

/-- `X` is the polynomial variable (aka indeterminant). -/
def X : polynomial R := monomial 1 1

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
lemma X_mul : X * p = p * X :=
begin
  ext,
  simp [X, monomial, add_monoid_algebra.mul_apply, sum_single_index, add_comm],
end

lemma X_pow_mul {n : ℕ} : X^n * p = p * X^n :=
begin
  induction n with n ih,
  { simp, },
  { conv_lhs { rw pow_succ', },
    rw [mul_assoc, X_mul, ←mul_assoc, ih, mul_assoc, ←pow_succ'], }
end

lemma X_pow_mul_assoc {n : ℕ} : (p * X^n) * q = (p * q) * X^n :=
by rw [mul_assoc, X_pow_mul, ←mul_assoc]

/-- coeff p n is the coefficient of X^n in p -/
def coeff (p : polynomial R) := p.to_fun

lemma apply_eq_coeff : p n = coeff p n := rfl


@[simp] lemma coeff_mk (s) (f) (h) : coeff (finsupp.mk s f h : polynomial R) = f := rfl

lemma coeff_single : coeff (single n a) m = if n = m then a else 0 :=
by { dsimp [single, finsupp.single], congr, }

@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : polynomial R) n = 0 := rfl

@[simp] lemma coeff_one_zero : coeff (1 : polynomial R) 0 = 1 := coeff_single


instance [has_repr R] : has_repr (polynomial R) :=
⟨λ p, if p = 0 then "0"
  else (p.support.sort (≤)).foldr
    (λ n a, a ++ (if a = "" then "" else " + ") ++
      if n = 0
        then "C (" ++ repr (coeff p n) ++ ")"
        else if n = 1
          then if (coeff p n) = 1 then "X" else "C (" ++ repr (coeff p n) ++ ") * X"
          else if (coeff p n) = 1 then "X ^ " ++ repr n
            else "C (" ++ repr (coeff p n) ++ ") * X ^ " ++ repr n) ""⟩

theorem ext_iff {p q : polynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n :=
⟨λ h n, h ▸ rfl, finsupp.ext⟩

@[ext] lemma ext {p q : polynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
(@ext_iff _ _ p q).2

-- this has the same content as the subsingleton
lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : polynomial R) : p = 0 :=
by rw [←one_smul R p, ←h, zero_smul]


end semiring


section ring
variables [ring R]

instance : ring (polynomial R) := add_monoid_algebra.ring

@[simp] lemma coeff_neg (p : polynomial R) (n : ℕ) : coeff (-p) n = -coeff p n := rfl

@[simp]
lemma coeff_sub (p q : polynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n := rfl

end ring


section comm_semiring
variables [comm_semiring R]

instance : comm_semiring (polynomial R) := add_monoid_algebra.comm_semiring

end comm_semiring

section nonzero_semiring

variables [semiring R] [nontrivial R] {p q : polynomial R}
instance : nontrivial (polynomial R) :=
begin
  refine nontrivial_of_ne 0 1 _, intro h,
  have := coeff_zero 0, revert this, rw h, simp,
end

end nonzero_semiring

end polynomial
