/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/

import ring_theory.subring

variables {F : Type*} [field F] (s : set F)

class is_subfield extends is_subring s :=
(inv_mem : ∀ {x : F}, x ∈ s → x⁻¹ ∈ s)

open is_subfield

instance subset.field [is_subfield s] : field s :=
begin
  refine_struct { inv := λ (a : s), ⟨a.val⁻¹, inv_mem a.property⟩,
                .. subset.comm_ring };
  have_field; simp [subtype.ext]; intros; apply field; assumption
end

instance subtype.field [is_subfield s] : field (subtype s) := subset.field s
