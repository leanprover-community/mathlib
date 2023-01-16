/-
Copyright (c) 2022 Paul A. Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul A. Reichert
-/
import analysis.convex.basic
import data.real.nnreal
import topology.algebra.module.basic
import topology.instances.real

/-!
# convex bodies

This file contains the definition of the type `convex_body V`
consisting of
convex, compact, nonempty subsets of a real normed space `V`.

`convex_body V` is a module over the nonnegative reals (`nnreal`).

TODOs:
- endow it with the Hausdorff metric
- define positive convex bodies, requiring the interior to be nonempty
- introduce support sets

## Tags

convex, convex body
-/

open_locale pointwise
open_locale nnreal

variables (V : Type*) [topological_space V] [add_comm_group V] [has_continuous_add V]
  [module ℝ V] [has_continuous_smul ℝ V]

/--
Let `V` be a normed space. A subset of `V` is a convex body if and only if
it is convex, compact, and nonempty.
-/
structure convex_body :=
(carrier : set V)
(convex' : convex ℝ carrier)
(is_compact' : is_compact carrier)
(nonempty' : carrier.nonempty)

namespace convex_body

variables {V}

instance : set_like (convex_body V) V :=
{ coe := convex_body.carrier,
  coe_injective' := λ K L h, by { cases K, cases L, congr' } }

lemma convex (K : convex_body V) : convex ℝ (K : set V) := K.convex'
lemma is_compact (K : convex_body V) : is_compact (K : set V) := K.is_compact'
lemma nonempty (K : convex_body V) : (K : set V).nonempty := K.nonempty'

@[ext]
protected lemma ext {K L : convex_body V} (h : (K : set V) = L) : K = L := set_like.ext' h

@[simp]
lemma coe_mk (s : set V) (h₁ h₂ h₃) : (mk s h₁ h₂ h₃ : set V) = s := rfl

instance : add_monoid (convex_body V) :=
-- we cannot write K + L to avoid reducibility issues with the set.has_add instance
{ add := λ K L, ⟨set.image2 (+) K L,
                 K.convex.add L.convex,
                 K.is_compact.add L.is_compact,
                 K.nonempty.add L.nonempty⟩,
  add_assoc := λ K L M, by { ext, simp only [coe_mk, set.image2_add, add_assoc] },
  zero := ⟨0, convex_singleton 0, is_compact_singleton, set.singleton_nonempty 0⟩,
  zero_add := λ K, by { ext, simp only [coe_mk, set.image2_add, zero_add] },
  add_zero := λ K, by { ext, simp only [coe_mk, set.image2_add, add_zero] } }

@[simp]
lemma coe_add (K L : convex_body V) : (↑(K + L) : set V) = (K : set V) + L := rfl

@[simp]
lemma coe_zero : (↑(0 : convex_body V) : set V) = 0 := rfl

instance : inhabited (convex_body V) := ⟨0⟩

instance : add_comm_monoid (convex_body V) :=
{ add_comm := λ K L, by { ext, simp only [coe_add, add_comm] },
  .. convex_body.add_monoid }

instance : has_smul ℝ (convex_body V) :=
{ smul := λ c K, ⟨c • (K : set V), K.convex.smul _, K.is_compact.smul _, K.nonempty.smul_set⟩ }

@[simp]
lemma coe_smul (c : ℝ) (K : convex_body V) : (↑(c • K) : set V) = c • (K : set V) := rfl

instance : distrib_mul_action ℝ (convex_body V) :=
{ to_has_smul := convex_body.has_smul,
  one_smul := λ K, by { ext, simp only [coe_smul, one_smul] },
  mul_smul := λ c d K, by { ext, simp only [coe_smul, mul_smul] },
  smul_add := λ c K L, by { ext, simp only [coe_smul, coe_add, smul_add] },
  smul_zero := λ c, by { ext, simp only [coe_smul, coe_zero, smul_zero] } }

@[simp]
lemma coe_smul' (c : ℝ≥0) (K : convex_body V) : (↑(c • K) : set V) = c • (K : set V) := rfl

/--
The convex bodies in a fixed space $V$ form a module over the nonnegative reals.
-/
instance : module ℝ≥0 (convex_body V) :=
{ add_smul := λ c d K,
  begin
    ext1,
    simp only [coe_smul, coe_add],
    exact convex.add_smul K.convex (nnreal.coe_nonneg _) (nnreal.coe_nonneg _),
  end,
  zero_smul := λ K, by { ext1, exact set.zero_smul_set K.nonempty } }

end convex_body
