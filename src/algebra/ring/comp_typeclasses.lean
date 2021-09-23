/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/

import algebra.ring.basic

/-!
# Propositional typeclasses on several ring homs

This file contains three typeclasses used in the definition of (semi)linear maps:
* `ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃`, which expresses the fact that `σ₂₃.comp σ₁₂ = σ₁₃`
* `ring_hom_inv_pair σ₁₂ σ₂₁`, which states that `σ₁₂` and `σ₂₁` are inverses of each other
* `ring_hom_surjective σ`, which states that `σ` is surjective

Instances of these typeclasses mostly involving `ring_hom.id` are also provided:
* `ring_hom_inv_pair (ring_hom.id R) (ring_hom.id R)`
* `[ring_hom_inv_pair σ₁₂ σ₂₁] ring_hom_comp_triple σ₁₂ σ₂₁ (ring_hom.id R₁)`
* `ring_hom_comp_triple (ring_hom.id R₁) σ₁₂ σ₁₂`
* `ring_hom_comp_triple σ₁₂ (ring_hom.id R₂) σ₁₂`
* `ring_hom_surjective (ring_hom.id R)`
* `[ring_hom_inv_pair σ₁ σ₂] : ring_hom_surjective σ₁`

## Implementation notes

* For the typeclass `ring_hom_inv_pair σ₁₂ σ₂₁`, `σ₂₁` is marked as an `out_param`,
  as it must typically be found via the typeclass inference system.

* Likewise, for `ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃`, `σ₁₃` is marked as an `out_param`,
  for the same reason.

## Tags

`ring_hom_comp_triple`, `ring_hom_inv_pair`, `ring_hom_surjective`
-/

variables {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variables [semiring R₁] [semiring R₂] [semiring R₃]

/-- Class that expresses the fact that three ring equivs form a composition triple. This is
used to handle composition of semilinear maps. -/
class ring_hom_comp_triple (σ₁₂ : R₁ →+* R₂) (σ₂₃ : R₂ →+* R₃)
  (σ₁₃ : out_param (R₁ →+* R₃)) : Prop :=
(is_comp_triple : σ₁₃ = σ₂₃.comp σ₁₂)

variables {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}

namespace ring_hom_comp_triple

@[simp] lemma comp_eq [t : ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] : σ₂₃.comp σ₁₂ = σ₁₃ :=
t.is_comp_triple.symm

@[simp] lemma comp_apply [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] {x : R₁} :
  σ₂₃ (σ₁₂ x) = σ₁₃ x :=
show (σ₂₃.comp σ₁₂) x = σ₁₃ x, by rw [comp_eq]

end ring_hom_comp_triple

/-- Class that expresses the fact that two ring equivs are inverses of each other. This is used
to handle `symm` for semilinear equivalences. -/
class ring_hom_inv_pair (σ : R₁ →+* R₂) (σ' : out_param (R₂ →+* R₁)) : Prop :=
(is_inv_pair₁ : σ'.comp σ = ring_hom.id R₁)
(is_inv_pair₂ : σ.comp σ' = ring_hom.id R₂)

variables {σ : R₁ →+* R₂} {σ' : R₂ →+* R₁}

namespace ring_hom_inv_pair

variables [ring_hom_inv_pair σ σ']

@[simp] lemma trans_eq : σ.comp σ' = (ring_hom.id R₂) :=
by { rw ring_hom_inv_pair.is_inv_pair₂ }

@[simp] lemma trans_eq₂ : σ'.comp σ = (ring_hom.id R₁) :=
by { rw ring_hom_inv_pair.is_inv_pair₁ }

@[simp] lemma inv_pair_apply {x : R₁} : σ' (σ x) = x :=
by { rw [← ring_hom.comp_apply, trans_eq₂], simp }

@[simp] lemma inv_pair_apply₂ {x : R₂} : σ (σ' x) = x :=
by { rw [← ring_hom.comp_apply, trans_eq], simp }

instance ids : ring_hom_inv_pair (ring_hom.id R₁) (ring_hom.id R₁) := ⟨rfl, rfl⟩
instance triples {σ₂₁ : R₂ →+* R₁} [ring_hom_inv_pair σ₁₂ σ₂₁] :
  ring_hom_comp_triple σ₁₂ σ₂₁ (ring_hom.id R₁) :=
⟨by simp only [trans_eq₂]⟩

end ring_hom_inv_pair

namespace ring_hom_comp_triple

instance ids : ring_hom_comp_triple (ring_hom.id R₁) σ₁₂ σ₁₂ := ⟨by { ext, simp }⟩
instance right_ids : ring_hom_comp_triple σ₁₂ (ring_hom.id R₂) σ₁₂ := ⟨by { ext, simp }⟩

end ring_hom_comp_triple

/-- Class expressing the fact that a `ring_hom` is surjective. This is needed in the context
of semilinear maps, where some lemmas require this. -/
class ring_hom_surjective (σ : R₁ →+* R₂) : Prop :=
(is_surjective : function.surjective σ)

lemma ring_hom.is_surjective (σ : R₁ →+* R₂) [t : ring_hom_surjective σ] : function.surjective σ :=
t.is_surjective

namespace ring_hom_surjective

-- The linter gives a false positive, since `σ₂` is an out_param
@[priority 100, nolint dangerous_instance] instance inv_pair {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}
  [ring_hom_inv_pair σ₁ σ₂] : ring_hom_surjective σ₁ :=
⟨λ x, ⟨σ₂ x, ring_hom_inv_pair.inv_pair_apply₂⟩⟩

instance ids : ring_hom_surjective (ring_hom.id R₁) := ⟨is_surjective⟩

-- if this is an instance, it causes typeclass inference to loop
lemma comp [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [ring_hom_surjective σ₁₂] [ring_hom_surjective σ₂₃] :
  ring_hom_surjective σ₁₃ :=
{ is_surjective := begin
    have := σ₂₃.is_surjective.comp σ₁₂.is_surjective,
    rwa [← ring_hom.coe_comp, ring_hom_comp_triple.comp_eq] at this,
  end }

end ring_hom_surjective
