/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.matrix.basic
import algebra.char_p
/-!
# Matrices in prime characteristic
-/

open matrix
variables {n : Type*} [fintype n] {R : Type*} [ring R]

instance matrix.char_p [decidable_eq n] [nonempty n] (p : ℕ) [char_p R p] :
  char_p (matrix n n R) p :=
{ cast_eq_zero_iff :=
  begin
    intro k, rw ← char_p.cast_eq_zero_iff R p k,
    rw ← nat.cast_zero, rw ← (scalar n).map_nat_cast,
    convert scalar_inj, simp, assumption,
  end }
