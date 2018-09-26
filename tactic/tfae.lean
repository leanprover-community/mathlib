/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Simon Hudon

"The Following Are Equivalent" (tfae):
Tactic for proving the equivalence of a set of proposition
using various implications between them.
-/

import tactic.basic tactic.interactive data.list.basic
import tactic.scc

open expr tactic lean lean.parser

namespace tactic
open interactive interactive.types expr

export list (tfae)

namespace tfae

@[derive has_reflect] inductive arrow : Type
| right      : arrow
| left_right : arrow
| left       : arrow

meta def mk_implication : Π (re : arrow) (e₁ e₂ : expr), pexpr
| arrow.right      e₁ e₂ := ``(%%e₁ → %%e₂)
| arrow.left_right e₁ e₂ := ``(%%e₁ ↔ %%e₂)
| arrow.left       e₁ e₂ := ``(%%e₂ → %%e₁)

meta def mk_name : Π (re : arrow) (i₁ i₂ : nat), name
| arrow.right      i₁ i₂ := ("tfae_" ++ to_string i₁ ++ "_to_"  ++ to_string i₂ : string)
| arrow.left_right i₁ i₂ := ("tfae_" ++ to_string i₁ ++ "_iff_" ++ to_string i₂ : string)
| arrow.left       i₁ i₂ := ("tfae_" ++ to_string i₂ ++ "_to_"  ++ to_string i₁ : string)

end tfae

namespace interactive

open tactic.tfae list

meta def parse_list : expr → option (list expr )
| `([]) := pure []
| `(%%e :: %%es) := (::) e <$> parse_list es
| _ := none

/-- in a goal of the form `tfae [a₀,a₁,a₂]`,
`tfae_have : i → j` creates the assertion `aᵢ → aⱼ`. The other possible
notations are `tfae_have : i ← j` and `tfae_have : i ↔ j`. The user can
also provide a label for the assertion, as with `have`: `tfae_have h : i ↔ j`
-/
meta def tfae_have
  (h : parse $ optional ident <* tk ":")
  (i₁ : parse small_nat)
  (re : parse (((tk "→" <|> tk "->")  *> return arrow.right)      <|>
               ((tk "↔" <|> tk "<->") *> return arrow.left_right) <|>
               ((tk "←" <|> tk "<-")  *> return arrow.left)))
  (i₂ : parse small_nat)
  (discharger : tactic unit := (solve_by_elim)) :
  tactic unit := do
    `(tfae %%l) <- target,
    l ← parse_list l,
    e₁ ← list.nth l (i₁ - 1) <|> fail format!"index {i₁} is not between 1 and {l.length}",
    e₂ ← list.nth l (i₂ - 1) <|> fail format!"index {i₂} is not between 1 and {l.length}",
    type ← to_expr (tfae.mk_implication re e₁ e₂),
    let h := h.get_or_else (mk_name re i₁ i₂),
    tactic.assert h type,
    return ()

/-- find all implications and equivalences in to prove a goal of
the form `tfae [...]`
-/
meta def tfae_finish : tactic unit :=
applyc ``tfae_nil <|>
closure.mk_closure (λ cl,
do impl_graph.mk_scc cl,
   tfae_cons ← mk_const ``tfae_cons_cons,
   repeat $ do {
     rewrite_target tfae_cons, split,
     prove_eqv_target cl },
   applyc ``tfae_singleton,
   pure ())

end interactive
end tactic
