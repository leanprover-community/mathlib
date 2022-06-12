/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import ring_theory.trace
import field_theory.finite.basic
import field_theory.finite.galois_field

/-!
# The trace map for finite fields

We define `trace_to_zmod F` for a finite field `F` as the trace map
from `F` to its prime field `zmod p` (where `p = ring_char F`),
and we state the fact that this trace map is nondegenerate.

## Tags
finite field, trace
-/

namespace finite_field

/-- The trace map from a finite field to its prime field is nongedenerate. -/
lemma trace_to_zmod_nondegenerate (F : Type*) [field F] [fintype F] {a : F}
 (ha : a ≠ 0) : ∃ b : F, algebra.trace (zmod (ring_char F)) F (a * b) ≠ 0 :=
begin
  haveI : fact (ring_char F).prime := ⟨char_p.char_is_prime F _⟩,
  have htr := trace_form_nondegenerate (zmod (ring_char F)) F a,
  simp_rw [algebra.trace_form_apply] at htr,
  by_contra' hf,
  exact ha (htr hf),
end

end finite_field
