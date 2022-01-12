/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import algebra.ring.basic
import algebra.lie.of_associative
import data.real.basic
import linear_algebra.basic

/-!
# Jordan algebras

Let `A` be a non-associative algebra (i.e. a module equipped with a bilinear multiplication
operation). Then `A` is said to be a (commutative) Jordan algebra if the multiplication is
commutative and satisfies a weak associativity law known as the Jordan Identity: for all `a` and `b`
in `A`,
```
(a * b) * a^2 = a * (b * a^2)
```
i.e. the operators of multiplication by `a` and `a^2` commute. Every associative algebra can be
equipped with a second  multiplication making it into a commutative Jordan algebra.
Jordan algebras arising this way are said to be special. There are also exceptional Jordan algebras
which can be shown not to be the symmetrisation of any associative algebra. The 3x3
matrices of octonions is the canonical example.

Commutative Jordan algebras were introduced by Jordan, von Neumann and Wigner
([jordanvonneumannwigner1934]) as a mathematical model for the observables of a quantum mechanical
physical system (for a C*-algebra the self-adjoint part is closed under the symmetrised Jordan
multiplication). Jordan algebras have subsequently been studied from the points of view of abstract
algebra and functional analysis. They have connections to Lie algebras and differential geometry.

A more general concept of a (non-commutative) Jordan algebra can also be defined, as a
(non-commutative, non-associative) algebra `A` where, for each `a` in `A`, the operators of left and
right multiplication by `a` and `a^2` commute. Such algebras have connected to the Vidav-Palmer
theorem [cabreragarciarodriguezpalacios2014].

A comprehensive overview of the algebraic theory can be found in [mccrimmon2004].

A real Jordan algebra `A` can be introduced by
```
variables {A : Type*} [non_unital_non_assoc_ring A] [module ℝ A] [smul_comm_class ℝ A A]
  [is_scalar_tower ℝ A A] [is_comm_jordan A]
```

## Main results

- `lin_jordan` : Linearisation of the commutative Jordan axiom

## Implementation notes

We shall primarily be interested in linear Jordan algebras (i.e. over rings of characteristic not
two) leaving quadratic algebras to those better versed in that theory.

The conventional way to linearise the Jordan axiom is to equate coefficients (more formally, assume
that the axiom holds in all field extensions). For simplicity we use brute force algebraic expansion
and substitution instead.

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
* [Jordan, von Neumann and Wigner, 1934][jordanvonneumannwigner1934]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

-/

/--
A (non-commutative) Jordan multiplication.
-/
class is_jordan (A : Type*) [has_mul A] :=
(lmul_comm_rmul : ∀ a b : A, (a * b) * a = a * (b * a))
(lmul_lmul_comm_lmul: ∀ a b : A, (a * a) * (a * b) = a * ((a * a) * b))
(lmul_lmul_comm_rmul: ∀ a b : A, (a * a) * (b * a) = ((a * a) * b) * a)
(lmul_comm_rmul_rmul: ∀ a b : A, (a * b) * (a * a) = a * (b * (a * a)))
(rmul_comm_rmul_rmul: ∀ a b : A, (b * a) * (a * a) = (b * (a * a)) * a)

/--
A commutative Jordan multipication
-/
class is_comm_jordan (A : Type*) [has_mul A]:=
(mul_comm: ∀ a b : A, a * b = b * a)
(jordan: ∀ a b : A, (a * b) * (a * a) = a * (b * (a *a)))

-- A (commutative) Jordan multiplication is also a Jordan multipication
@[priority 100] -- see Note [lower instance priority]
instance jordan_of_comm_jordan (A : Type*) [has_mul A] [is_comm_jordan A] : is_jordan A :=
{ lmul_comm_rmul := λ a b, by rw [is_comm_jordan.mul_comm, is_comm_jordan.mul_comm a b],
  lmul_lmul_comm_lmul := λ a b, by rw [is_comm_jordan.mul_comm (a * a) (a * b),
  is_comm_jordan.jordan, is_comm_jordan.mul_comm b (a * a)],
  lmul_comm_rmul_rmul := λ a b, by rw [is_comm_jordan.mul_comm, ←is_comm_jordan.jordan,
    is_comm_jordan.mul_comm],
  lmul_lmul_comm_rmul :=  λ a b, by rw [is_comm_jordan.mul_comm (a * a) (b * a),
    is_comm_jordan.mul_comm b a, is_comm_jordan.jordan, is_comm_jordan.mul_comm,
    is_comm_jordan.mul_comm b (a * a)],
  rmul_comm_rmul_rmul := λ a b, by rw [is_comm_jordan.mul_comm b a, is_comm_jordan.jordan,
    is_comm_jordan.mul_comm], }

universe u

/- A (unital, associative) ring satisfies the (non-commutative) Jordan axioms-/
@[priority 100] -- see Note [lower instance priority]
instance ring.to_jordan_ring (B : Type u) [ring B] : is_jordan B :=
{ lmul_comm_rmul := by { intros, rw mul_assoc },
  lmul_lmul_comm_lmul := by { intros, rw [mul_assoc, mul_assoc] },
  lmul_comm_rmul_rmul := by { intros, rw [mul_assoc] },
  lmul_lmul_comm_rmul := by { intros, rw [←mul_assoc] },
  rmul_comm_rmul_rmul := by { intros, rw [← mul_assoc, ← mul_assoc] } }

variables {A : Type*} [non_unital_non_assoc_ring A]

/--
Left multiplication operator
-/
@[simps] def function.End.L : A →+ add_monoid.End A := add_monoid_hom.mul
local notation `L` := function.End.L

/--
Right multiplication operator
-/
@[simps] def function.End.R : A→+(add_monoid.End A) :=
  add_monoid_hom.flip (L  : A →+ add_monoid.End A)
local notation `R` := function.End.R

-- The Jordan axioms can be expressed in terms of commuting multiplication operators

lemma lmul_rmul_comm [is_jordan A] (a : A) : ⁅L a, R a⁆ = 0 :=
begin
  ext b,
  rw ring.lie_def,
  simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
      function.End.L_apply_apply, add_monoid.coe_mul, function.End.R_apply_apply],
    rw is_jordan.lmul_comm_rmul, rw sub_self,
end

lemma lmul_lmul_sq_comm [is_jordan A] (a : A) : ⁅L a, L (a * a)⁆ = 0 :=
begin
  ext b,
  rw ring.lie_def,
  simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
    function.End.L_apply_apply, add_monoid.coe_mul],
  rw is_jordan.lmul_lmul_comm_lmul, rw sub_self,
end

lemma lmul_rmul_sq_comm [is_jordan A] (a : A) : ⁅L a, R (a * a)⁆ = 0 :=
begin
  ext b,
  rw ring.lie_def,
  simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
    function.End.L_apply_apply, add_monoid.coe_mul, function.End.R_apply_apply],
  rw is_jordan.lmul_comm_rmul_rmul, rw sub_self,
end

lemma lmul_sq_rmul_comm [is_jordan A] (a : A) : ⁅L (a * a), R a⁆ = 0 :=
begin
  ext b,
  rw ring.lie_def,
  simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
    function.End.L_apply_apply, add_monoid.coe_mul, function.End.R_apply_apply],
  rw is_jordan.lmul_lmul_comm_rmul, rw sub_self,
end

lemma rmul_rmul_sq_comm [is_jordan A] (a : A) : ⁅R a, R (a * a)⁆ = 0 :=
begin
  ext b,
  rw ring.lie_def,
  simp only [add_monoid_hom.zero_apply, add_monoid_hom.sub_apply, function.comp_app,
    add_monoid.coe_mul, function.End.R_apply_apply],
  rw is_jordan.rmul_comm_rmul_rmul, rw sub_self,
end

variable [is_comm_jordan A]

/-
instance : comm_monoid A :=
{ mul_comm := λ a b, is_comm_jordan.mul_comm a b,
  .. (show non_unital_non_assoc_ring A, by apply_instance) }
-/

/- Linearise the Jordan axiom with two variables-/
lemma mul_op_com1 (a b : A) :
  ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆  = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b), L ((a+b)*(a+b))⁆ : by rw (lmul_lmul_sq_comm (a + b))
    ... = ⁅L a + L b, L (a*a+a*b+(b*a+b*b))⁆ : by rw [add_mul, mul_add, mul_add, map_add]
    ... = ⁅L a + L b, L (a*a) + L(a*b) + (L(a*b) + L(b*b))⁆ :
      by rw [map_add, map_add, map_add, is_comm_jordan.mul_comm b a]
    ... = ⁅L a + L b, L (a*a) + (2:ℤ)•L(a*b) + L(b*b)⁆ : by abel
    ... = ⁅L a, L (a*a)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, L(b*b)⁆
      + (⁅L b, L (a*a)⁆ + ⁅L b,(2:ℤ)•L(a*b)⁆ + ⁅L b,L(b*b)⁆) :
        by rw [add_lie, lie_add, lie_add, lie_add, lie_add]
    ... = (2:ℤ)•⁅L a, L(a*b)⁆ + ⁅L a, L(b*b)⁆ + (⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L b,L(a*b)⁆) :
      by rw [lmul_lmul_sq_comm a, lmul_lmul_sq_comm b, lie_smul, lie_smul,
        zero_add, add_zero]
    ... = ⁅L a, L (b*b)⁆ + ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L (a*b)⁆ + (2:ℤ)•⁅L b, L (a*b)⁆: by abel
end

/- Linearise the Jordan axiom with three variables-/
lemma lin_jordan (a b c : A) : (2:ℤ)•(⁅L a, L (b*c)⁆ + ⁅L b, L (a*c)⁆ + ⁅L c, L (a*b)⁆) = 0 :=
begin
  symmetry,
  calc 0 = ⁅L (a+b+c), L ((a+b+c)*(a+b+c))⁆ : by rw (lmul_lmul_sq_comm (a + b + c))
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(b*a) + L(b*b) + L(b*c)) + (L(c*a) + L(c*b) + L(c*c))⁆ :
    by rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add,
      map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add, map_add]
  ... = ⁅L a + L b + L c,
    L (a*a) + L(a*b) + L (a*c) + (L(a*b) + L(b*b) + L(b*c)) + (L(a*c) + L(b*c) + L(c*c))⁆ :
    by rw [is_comm_jordan.mul_comm b a, is_comm_jordan.mul_comm c a,
      is_comm_jordan.mul_comm c b]
  ... = ⁅L a + L b + L c, L (a*a) + L(b*b) + L(c*c) + (2:ℤ)•L(a*b) + (2:ℤ)•L(a*c) + (2:ℤ)•L(b*c) ⁆ :
    by abel
  ... = ⁅L a, L (a*a)⁆ + ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, (2:ℤ)•L(a*c)⁆
          + ⁅L a, (2:ℤ)•L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + ⁅L b, L(b*b)⁆ + ⁅L b, L(c*c)⁆ + ⁅L b, (2:ℤ)•L(a*b)⁆
          + ⁅L b, (2:ℤ)•L(a*c)⁆ + ⁅L b, (2:ℤ)•L(b*c)⁆)
        + (⁅L c, L (a*a)⁆ + ⁅L c, L(b*b)⁆ + ⁅L c, L(c*c)⁆ + ⁅L c, (2:ℤ)•L(a*b)⁆
          + ⁅L c, (2:ℤ)•L(a*c)⁆ + ⁅L c, (2:ℤ)•L(b*c)⁆) :
    by rw [add_lie, add_lie, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add,
     lie_add, lie_add, lie_add, lie_add, lie_add, lie_add, lie_add]
  ... = ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + ⁅L a, (2:ℤ)•L(a*b)⁆ + ⁅L a, (2:ℤ)•L(a*c)⁆
          + ⁅L a, (2:ℤ)•L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + ⁅L b, L(c*c)⁆ + ⁅L b, (2:ℤ)•L(a*b)⁆ + ⁅L b, (2:ℤ)•L(a*c)⁆
          + ⁅L b, (2:ℤ)•L(b*c)⁆)
        + (⁅L c, L (a*a)⁆ + ⁅L c, L(b*b)⁆ + ⁅L c, (2:ℤ)•L(a*b)⁆ + ⁅L c, (2:ℤ)•L(a*c)⁆
          + ⁅L c, (2:ℤ)•L(b*c)⁆) :
    by rw [lmul_lmul_sq_comm a, lmul_lmul_sq_comm b,
      lmul_lmul_sq_comm c, zero_add, add_zero, add_zero]
  ... = ⁅L a, L(b*b)⁆ + ⁅L a, L(c*c)⁆ + (2:ℤ)•⁅L a, L(a*b)⁆ + (2:ℤ)•⁅L a, L(a*c)⁆
          + (2:ℤ)•⁅L a, L(b*c)⁆
        + (⁅L b, L (a*a)⁆ + ⁅L b, L(c*c)⁆ + (2:ℤ)•⁅L b, L(a*b)⁆ + (2:ℤ)•⁅L b, L(a*c)⁆
          + (2:ℤ)•⁅L b, L(b*c)⁆)
        + (⁅L c, L (a*a)⁆ + ⁅L c, L(b*b)⁆ + (2:ℤ)•⁅L c, L(a*b)⁆ + (2:ℤ)•⁅L c, L(a*c)⁆
          + (2:ℤ)•⁅L c, L(b*c)⁆) :
    by rw [lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul, lie_smul]
  ... = (⁅L a, L(b*b)⁆+ ⁅L b, L (a*a)⁆ + (2:ℤ)•⁅L a, L(a*b)⁆ + (2:ℤ)•⁅L b, L(a*b)⁆)
        + (⁅L a, L(c*c)⁆ + ⁅L c, L (a*a)⁆ + (2:ℤ)•⁅L a, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*c)⁆)
        + (⁅L b, L(c*c)⁆ + ⁅L c, L(b*b)⁆ + (2:ℤ)•⁅L b, L(b*c)⁆ + (2:ℤ)•⁅L c, L(b*c)⁆)
        + ((2:ℤ)•⁅L a, L(b*c)⁆ + (2:ℤ)•⁅L b, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*b)⁆) : by abel
  ... = (2:ℤ)•⁅L a, L(b*c)⁆ + (2:ℤ)•⁅L b, L(a*c)⁆ + (2:ℤ)•⁅L c, L(a*b)⁆ :
    by rw [mul_op_com1,mul_op_com1, mul_op_com1, zero_add, zero_add, zero_add]
  ... = (2:ℤ)•(⁅L a, L (b*c)⁆ + ⁅L b, L (a*c)⁆ + ⁅L c, L (a*b)⁆) : by rw [smul_add, smul_add]
end
