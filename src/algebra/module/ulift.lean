/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import algebra.module.basic
import algebra.ring.ulift

/-!
# Pi instances for module and multiplicative actions

This file defines instances for module, mul_action and related structures on Pi Types
-/

namespace ulift
universes u v w
variable {R : Type u}
variable {M : Type v}

instance has_scalar [has_scalar R M] :
  has_scalar (ulift R) M :=
⟨λ s x, s.down • x⟩

@[simp] lemma smul_apply [has_scalar R M] (s : ulift R) (x : M) : (s • x) = s.down • x := rfl

instance has_scalar' [has_scalar R M] :
  has_scalar R (ulift M) :=
⟨λ s x, ⟨s • x.down⟩⟩

@[simp]
lemma smul_apply' [has_scalar R M] (s : R) (x : ulift M) :
  (s • x).down = s • x.down :=
rfl

instance mul_action [monoid R] [mul_action R M] :
  mul_action (ulift R) M :=
{ smul := (•),
  mul_smul := λ r s f, by { cases r, cases s, simp [mul_smul], },
  one_smul := λ f, by { simp [one_smul], } }

instance mul_action' [monoid R] [mul_action R M] :
  mul_action R (ulift M) :=
{ smul := (•),
  mul_smul := λ r s f, by { cases f, ext, simp [mul_smul], },
  one_smul := λ f, by { ext, simp [one_smul], } }

instance distrib_mul_action [monoid R] [add_monoid M] [distrib_mul_action R M] :
  distrib_mul_action (ulift R) M :=
{ smul_zero := λ c, by { cases c, simp [smul_zero], },
  smul_add := λ c f g, by { cases c, simp [smul_add], },
  ..ulift.mul_action }

instance distrib_mul_action' [monoid R] [add_monoid M] [distrib_mul_action R M] :
  distrib_mul_action R (ulift M) :=
{ smul_zero := λ c, by { ext, simp [smul_zero], },
  smul_add := λ c f g, by { ext, simp [smul_add], },
  ..ulift.mul_action' }

instance semimodule [semiring R] [add_comm_monoid M] [semimodule R M] :
  semimodule (ulift R) M :=
{ add_smul := λ c f g, by { cases c, simp [add_smul], },
  zero_smul := λ f, by { simp [zero_smul], },
  ..ulift.distrib_mul_action }

instance semimodule' [semiring R] [add_comm_monoid M] [semimodule R M] :
  semimodule R (ulift M) :=
{ add_smul := by { intros, ext1, apply add_smul },
  zero_smul := by { intros, ext1, apply zero_smul } }

end ulift
