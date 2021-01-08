/-
Copyright (c) 2021 Yakov Pechersky All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.equiv.basic
import tactic.norm_num

/-!
# `norm_swap`

Evaluating swapping expressions of numerals, of the form `swap x y z`,
for numerals `x y z : ℕ`.
-/

open equiv tactic expr

/--
If `e : expr` is of the form `app (⇑f) x`, get back the `expr`s for type of `f`,
the `has_coe_to_fun` instance, the expr for `f` itself, and `x`.
-/
meta def expr.get_of_coe_fn (e : expr) (f : name) : tactic (expr × expr × expr × expr) :=
do
  if e.is_app_of ``coe_fn
  then do
    [α, inst, fexpr, x] ← pure e.get_app_args,
    let fname : name := fexpr.get_app_fn.const_name,
    if fname = f then pure (α, inst, fexpr, x)
    else
      fail!"retrieved function name {fname} is not the expected {f}"
  else fail "not of coe_fn form with a single argument"

/--
Produce the `expr` which is the application of the term represented by `n` with the
`expr`s in `l`, while constructing the proper typeclass context.
Differs from `mk_app` because `mk_app` assumes that `n` is over `Type*`,
while here, `mk_sorted_app` assumed that `n` is over `Sort*`.
-/
meta def tactic.instance_cache.mk_sorted_app (c : instance_cache) (n : name) (l : list expr) :
  tactic (instance_cache × expr) :=
do d ← get_decl n,
   (c, l) ← instance_cache.append_typeclasses d.type.binding_body c l,
   return (c, (const n [c.univ.succ]).mk_app (c.α :: l))

open norm_num

namespace norm_swap

/--
A tactic for normalizing swaps of the form `equiv.swap a b c` where
`a, b, c` are numerals.

```
example : equiv.swap 1 2 1 = 2 := by norm_num
```
-/
@[norm_num] meta def eval : expr → tactic (expr × expr) := λ e, do
  (swapt, coe_fn_inst, f, c) ← expr.get_of_coe_fn e ``equiv.swap,
  [α, deceq_inst, a, b] ← pure f.get_app_args, -- the swap should have exactly two arguments applied
  unify α `(ℕ) <|> (fail "currently, norm_swap supports only ℕ"),
  dic ← mk_instance_cache α,
  na ← a.to_nat,
  nb ← b.to_nat,
  nc ← c.to_nat,
  if ha : nc = na
    then do
      (dic, p) ← dic.mk_sorted_app ``swap_apply_left [a, b],
      pure (b, p)
  else if hb : nc = nb
    then do
      (dic, p) ← dic.mk_sorted_app ``swap_apply_right [a, b],
      pure (a, p)
  else do
    nic ← mk_instance_cache `(ℕ), -- our `na, nb, nc` are now in Nat
    (_, hca) ← (prove_ne nic c a nc na),
    (_, hcb) ← (prove_ne nic c b nc nb),
    (dic, p) ← dic.mk_sorted_app ``swap_apply_of_ne_of_ne [a, b, c, hca, hcb],
    pure (c, p)

end norm_swap
