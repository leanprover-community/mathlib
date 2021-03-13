/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import group_theory.group_action.defs
/-!
# Introduce `smul_with_zero`

In analogy with the usual monoid action on a Type `M`, we introduce an action of a
`monoid_with_zero` on a Type with `0`.

In particular, for Types `R` and `M`, both containing `0`, we define `smul_with_zero R M` to
be the typeclass where the products `r • 0` and `0 • m` vanish for all `r : R` and all `m : M`.

Moreover, in the case in which `R` is a `monoid_with_zero`, we introduce the typeclass
`mul_action_with_zero R M`, mimicking group actions and having an absorbing `0` in `R`.
Thus, the action is required to be compatible with

* the unit of the monoid, acting as the identity;
* the zero of the monoid_with_zero, acting as zero;
* associativity of the monoid.

We also add `instances`:

* any `monoid_with_zero` has a `mul_action_with_zero R R` acting on itself;
-/

variables (R M : Type*)

section has_zero

variable [has_zero M]

/--  `smul_with_zero` is a class consisting of a Type `R` with `0 : R` and a scalar multiplication
of `R` on a Type `M` with `0`, such that the equality `r • m = 0` holds if at least one among `r`
or `m` equals `0`. -/
class smul_with_zero [has_zero R] extends has_scalar R M :=
(smul_zero : ∀ r : R, r • (0 : M) = 0)
(zero_smul : ∀ m : M, (0 : R) • m = 0)

variables {M}

@[simp] lemma zero_smul [has_zero R] [smul_with_zero R M] (m : M) :
  (0 : R) • m = 0 :=
smul_with_zero.zero_smul m

variables (M)

section monoid_with_zero

variable [monoid_with_zero R]

/--  An action of a monoid with zero `R` on a Type `M`, also with `0`, compatible with `0`
(both in `R` and in `M`), with `1 ∈ R`, and with associativity of multiplication on the
monoid `M`. -/
class mul_action_with_zero extends mul_action R M :=
-- these fields are copied from `smul_with_zero`, as `extends` behaves poorly
(smul_zero : ∀ r : R, r • (0 : M) = 0)
(zero_smul : ∀ m : M, (0 : R) • m = 0)

@[priority 100] -- see Note [lower instance priority]
instance mul_action_with_zero.to_smul_with_zero [m : mul_action_with_zero R M] :
  smul_with_zero R M :=
{..m}

instance monoid_with_zero.to_mul_action_with_zero : mul_action_with_zero R R :=
{ smul_zero := mul_zero,
  zero_smul := zero_mul,
  ..monoid.to_mul_action R }

end monoid_with_zero

end has_zero
