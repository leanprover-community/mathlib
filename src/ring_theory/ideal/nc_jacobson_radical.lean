/-
Copyright (c) 2022 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
import ring_theory.jacobson_ideal
import ring_theory.inverses
/-!
# Jacobson radical of a noncommutative ring

In this file, we define the Jacobson radical of a ring and prove its basic properties.

Let `R` be a (possibly noncommutative) ring. The *Jacobson radical* of `R` is defined
to be the intersection of all maximal *left* ideals of `R`, which coincides with that of
all maximal *right* ideals, so it is a two-sided ideal.

## Main definitions

* `ring.jacobson R : ideal R`: the Jacobson radical of a ring `R`, that is,
  the intersection of all maximal *left* ideals.

## Main statements

* `ring.mem_jacobson_tfae`: some equivalent conditions for an element in a ring
  to be contained in the Jacobson radical.

* `ring.jacobson_op`: the Jacobson radical of a ring coincides with that of its opposite ring.
  This essentially says that the definition of the Jacobson radical is left-right symmetric:
  the intersection of all maximal left ideals coincides with that of all maximal right ideals.

## Implementation notes

In `ring_theory/jacobson_ideal`, `ideal.jacobson I` is defined for `I : ideal R`. This is
the intersection of all maximal left ideals containing `I`.
This should not be confused with `ring.jacobson R` (which is actually defined by
`ideal.jacobson ⊥` in this file).

## TODO

* Define the Jacobson radical of a module, and make it compatible with `ideal.jacobson`
and `ring.jacobson`, and prove Nakayama's lemma.

* State and prove more direct statement saying that the intersection of maximal left ideals
coincides with that of maximal right ideals.

* State that `ring.jacobson R` is a two-sided ideal.
-/

universe u
variables {R : Type u} [ring R]

namespace ideal

lemma one_add_mul_self_mem_maximal_of_not_mem_maximal {x : R} {I : ideal R}
  (h₁ : I.is_maximal) (h₂ : x ∉ I) : ∃ a : R, 1 + a * x ∈ I :=
begin
  have : (1 : R) ∈ I ⊔ span {x},
  { rw is_maximal_iff at h₁,
    apply h₁.2 _ _ le_sup_left h₂,
    apply mem_sup_right,
    apply submodule.mem_span_singleton_self },
  rw submodule.mem_sup at this,
  obtain ⟨m, hmI, y, hy, hmy⟩ := this,
  rw mem_span_singleton' at hy,
  obtain ⟨a, rfl⟩ := hy,
  existsi -a,
  rwa [←hmy, neg_mul, add_neg_cancel_right],
end

end ideal

/-! ### Jacobson radical of a ring -/

namespace ring
open ideal

/--
For a ring `R`, `jacobson R` is the Jacobson radical of `R`, that is,
the intersection of all maximal left ideals of of `R`. Note that we use left ideals.
-/
def jacobson (R : Type u) [ring R] : ideal R := ideal.jacobson ⊥

lemma jacobson_def : jacobson R = Inf {I : ideal R | I.is_maximal } :=
congr_arg Inf $ by simp

lemma has_left_inv_one_add_of_mem_jacobson {x : R} :
  x ∈ jacobson R → has_left_inv (1 + x):=
begin
  contrapose,
  rw not_has_left_inv_iff_mem_maximal,
  rintro ⟨I, hImax, hxxI⟩ hx,
  refine hImax.ne_top _,
  rw eq_top_iff_one,
  have hxI : x ∈ I := by { rw [jacobson_def, mem_Inf] at hx, apply hx hImax },
  exact (add_mem_cancel_right hxI).mp hxxI,
end

/-- Characterizations of the Jacobson radical of a ring.

The following are equivalent for an element `x` in a ring `R`.
* 0: `x` is in the Jacobson radical of `R`, that is, contained in every maximal left ideal.
* 1: `1 + a * x` has a left inverse for any `a : R`.
* 2: `1 + a * x` is a unit for any `a : R`.
* 3: `1 + x * b` is a unit for any `b : R`.
* 4: `1 + a * x * b` is a unit for any `a b : R`.
-/
theorem mem_jacobson_tfae {R : Type u} [ring R] (x : R) : tfae [
  x ∈ jacobson R,
  ∀ a : R, has_left_inv (1 + a * x),
  ∀ a : R, is_unit (1 + a * x),
  ∀ b : R, is_unit (1 + x * b),
  ∀ a b : R, is_unit (1 + a * x * b)] :=
begin
  tfae_have : 1 → 2,
  { exact λ hx a, has_left_inv_one_add_of_mem_jacobson $
    (jacobson R).smul_mem' a hx },
  tfae_have : 2 → 3,
  { intros hx a,
    obtain ⟨c, hc⟩ := hx a,
    apply is_unit_of_left_inv_of_has_left_inv hc,
    suffices : c = 1 + ( -c * a * x),
    { rw this, apply hx },
    { calc c = c * (1 + a * x) + ( -c * a * x) : by noncomm_ring
        ...  = 1 + ( -c * a * x) : by rw hc } },
  tfae_have : 3 → 5,
  { intros hx _ _,
    apply is_unit.one_add_mul_swap,
    rw ←mul_assoc,
    apply hx },
  tfae_have : 5 → 1,
  { intro h,
    by_contra hx,
    rw [jacobson_def, submodule.mem_Inf] at hx,
    simp only [not_forall] at hx,
    rcases hx with ⟨I, hImax, hxI⟩,
    refine hImax.ne_top _,
    obtain ⟨a, ha⟩ := ideal.one_add_mul_self_mem_maximal_of_not_mem_maximal hImax hxI,
    apply eq_top_of_is_unit_mem _ ha,
    specialize h a 1,
    rwa [mul_assoc, mul_one] at h },
  tfae_have : 3 ↔ 4,
  { split; exact λ h b, (h b).one_add_mul_swap },
  tfae_finish,
end

open mul_opposite
/-- The Jacobson radical of `R` coincides with that of its opposite ring `Rᵐᵒᵖ`. -/
theorem jacobson_op {x : R} :
  x ∈ jacobson R ↔ op x ∈ jacobson Rᵐᵒᵖ :=
begin
  split,
  { intro hx,
    rw (mem_jacobson_tfae $ op x).out 0 3,
    intro a,
    rw [←is_unit_unop_iff_is_unit, unop_add, unop_one, unop_mul, unop_op],
    apply ((mem_jacobson_tfae x).out 0 2).mp hx },
  { intro hx,
    rw (mem_jacobson_tfae x).out 0 3,
    intro a,
    rw [←is_unit_op_iff_is_unit, op_add, op_one, op_mul],
    apply ((mem_jacobson_tfae $ op x).out 0 2).mp hx },
end

end ring
