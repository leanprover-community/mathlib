import tactic.tidy
import tactic.basic

namespace tactic

meta def sorry_if_contains_sorry : tactic unit :=
do
  g ← target,
  lock_tactic_state -- so the metavariable type in `sorry : _` doesn't become a goal
    (to_expr ``(sorry : _) >>= kdepends_on g >>= guardb) <|> fail "goal does not contain `sorrry`",
  tactic.admit

end tactic

/-
The propositional fields of `category` are annotated with the auto_param `obviously`,
which is defined here as a
[`replacer` tactic](https://leanprover-community.github.io/mathlib_docs/commands.html#def_replacer).
We then immediately set up `obviously` to call `tidy`. Later, this can be replaced with more
powerful tactics.
-/
def_replacer obviously
@[obviously] meta def obviously' :=
tactic.sorry_if_contains_sorry <|>
tactic.tidy <|>
tactic.fail (
"`obviously` failed to solve a subgoal.\n" ++
"You may need to explicitly provide a proof of the corresponding structure field.")
