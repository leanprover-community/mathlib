/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.core
import tactic.tauto

namespace tactic

/-- Run a tactic, returning the goals as they were before running the tactic. -/
meta def capture_terms {α : Type} (t : tactic α) : tactic (list expr × α) :=
do
  gs ← get_goals,
  a ← t,
  return (gs, a)

/-- Run a tactic, and then return the pretty printed original goal. -/
meta def pp_term {α : Type} (t : tactic α) : tactic string :=
do
  g :: _ ← get_goals,
  t,
  to_string <$> pp g

namespace interactive

declare_trace show_term

/--
`show_term { tac }` runs the tactic `tac`,
and then prints the term that was constructed.

This is useful for understanding what tactics are doing,
and how metavariables are handled.

As an example, if the goal is `ℕ × ℕ`, `show_term { split, exact 0 }` will
print `(0, ?m_1)`, indicating that the original goal has been partially filled in.
-/
meta def show_term (t : itactic) : itactic :=
pp_term t >>= (λ s, when_tracing `show_term (trace s))

end interactive
end tactic

set_option trace.show_term true
