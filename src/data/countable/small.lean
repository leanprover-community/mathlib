/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import logic.small.basic
import data.countable.defs
import tactic.apply_fun
import tactic.assert_exists
import tactic.by_contra
import tactic.monotonicity.basic
import tactic.monotonicity.default
import tactic.monotonicity.interactive
import tactic.monotonicity.lemmas
import tactic.nontriviality

/-!
# All countable types are small.

That is, any countable type is equivalent to a type in any universe.
-/

universes w v

@[priority 100]
instance small_of_countable (α : Type v) [countable α] : small.{w} α :=
let ⟨f, hf⟩ := exists_injective_nat α in small_of_injective hf
