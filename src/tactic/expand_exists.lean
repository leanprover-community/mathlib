/-
Copyright (c) 2022 Ian Wood. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ian Wood
-/
import init.meta.declaration
import meta.expr
import init.meta.lean.parser

/-!
# `expand_exists`

`expand_exists` is an attribute which takes a proof that something exists with some property, and
outputs a value using `classical.some`, and a proof that it has that property using
`classical.some_spec`.
-/

namespace tactic

open expr

private meta structure parse_ctx :=
(original_decl : declaration)
-- is theorem, name, type, value
(decl : bool → name → expr → pexpr → tactic unit)
(names : list name)
(pis_depth : ℕ := 0)

private meta structure parse_ctx_exists extends parse_ctx :=
-- Applies pi arguments to a term (eg `id` -> `id #2 #1 #0`).
(with_args : expr → expr)
-- Takes the form of `classical.some_spec^n (it_exists ...)`, with `n` the depth of `∃` parsed.
(spec_chain : pexpr)
-- List of declarations containing the value(s) of witnesses.
(exists_decls : list name := [])

private meta structure parse_ctx_props extends parse_ctx_exists :=
-- Projects a proof of the full proposition (eg `A ∧ B ∧ C`) to a specific proof (eg `B`).
(project_proof : pexpr → pexpr := id)

-- Converts `#0` in `∃ n, #0 = #0` to `n_value = n_value`.
private meta def instantiate_exists_decls (ctx : parse_ctx_exists) (p : expr) : expr :=
p.instantiate_vars $ ctx.exists_decls.reverse.map (λname,
  ctx.with_args (const name ctx.original_decl.univ_levels))

private meta def parse_one_prop (ctx : parse_ctx_props) (p : expr) : tactic unit :=
do
  let p : expr := instantiate_exists_decls { ..ctx } p,
  let val : pexpr := ctx.project_proof ctx.spec_chain,
  n <- match ctx.names with
  | [n] := return n
  | [] := fail "missing name for proposition"
  | _ := fail "too many names for propositions (are you missing an and?)"
  end,
  ctx.decl true n p val

private meta def parse_props : parse_ctx_props → expr → tactic unit
| ctx (app (app (const "and" []) p) q) := do
  match ctx.names with
  | [n] := parse_one_prop ctx (app (app (const `and []) p) q)
  | (n :: tail) :=
    parse_one_prop { names := [n],
      project_proof := (λ p, (const `and.left []) p) ∘ ctx.project_proof,
      ..ctx } p
    >> parse_props { names := tail,
      project_proof := (λ p, (const `and.right []) p) ∘ ctx.project_proof,
      ..ctx } q
  | [] := fail "missing name for proposition"
  end
| ctx p := parse_one_prop ctx p

private meta def parse_exists : parse_ctx_exists → expr → tactic unit
| ctx (app (app (const "Exists" [lvl]) type) (lam var_name bi var_type body)) := do
  /- TODO: Is this needed, and/or does this create issues? -/
  (if type = var_type then tactic.skip else tactic.fail "exists types should be equal"),
  ⟨n, names⟩ <- match ctx.names with
  | (n :: tail) := return (n, tail)
  | [] := fail "missing name for exists"
  end,
  -- Type may be dependant on earlier arguments.
  let type := instantiate_exists_decls ctx type,
  let value : pexpr := (const `classical.some [lvl]) ctx.spec_chain,
  ctx.decl false n type value,

  let exists_decls := ctx.exists_decls.concat n,
  let some_spec : pexpr := (const `classical.some_spec [lvl]) ctx.spec_chain,
  let ctx : parse_ctx_exists := { names := names,
    spec_chain := some_spec,
    exists_decls := exists_decls,
    ..ctx },
  parse_exists ctx body
| ctx e := parse_props { ..ctx } e

private meta def parse_pis : parse_ctx → expr → tactic unit
| ctx (pi n bi ty body) :=
  -- When making a declaration, wrap in an equivalent pi expression.
  let decl := (λ is_theorem name type val,
    ctx.decl is_theorem name (pi n bi ty type) (lam n bi (to_pexpr ty) val)) in
  parse_pis { decl := decl, pis_depth := ctx.pis_depth + 1, ..ctx } body
| ctx (app (app (const "Exists" [lvl]) type) p) :=
  let with_args := (λ (e : expr),
    (list.range ctx.pis_depth).foldr (λ n (e : expr), e (var n)) e) in
  parse_exists { with_args := with_args,
    spec_chain := to_pexpr (
      with_args $ const ctx.original_decl.to_name ctx.original_decl.univ_levels),
    ..ctx } (app (app (const "Exists" [lvl]) type) p)
| ctx e := fail ("unexpected expression " ++ to_string e)

/--
From a proof that (a) value(s) exist(s) with certain properties, constructs (an) instance(s)
satisfying those properties. For instance:

```lean
@[expand_exists nat_greater nat_greater_spec]
lemma nat_greater_exists (n : ℕ) : ∃ m : ℕ, n < m := ...

#check nat_greater      -- nat_greater : ℕ → ℕ
#check nat_greater_spec -- nat_greater_spec : ∀ (n : ℕ), n < nat_greater n
```

It supports multiple witnesses:

```lean
@[expand_exists nat_greater_m nat_greater_l nat_greater_spec]
lemma nat_greater_exists (n : ℕ) : ∃ (m l : ℕ), n < m ∧ m < l := ...

#check nat_greater_m      -- nat_greater : ℕ → ℕ
#check nat_greater_l      -- nat_greater : ℕ → ℕ
#check nat_greater_spec-- nat_greater_spec : ∀ (n : ℕ),
  n < nat_greater_m n ∧ nat_greater_m n < nat_greater_l n
```

It also supports logical conjunctions:
```lean
@[expand_exists nat_greater nat_greater_lt nat_greater_nonzero]
lemma nat_greater_exists (n : ℕ) : ∃ m : ℕ, n < m ∧ m ≠ 0 := ...

#check nat_greater         -- nat_greater : ℕ → ℕ
#check nat_greater_lt      -- nat_greater_lt : ∀ (n : ℕ), n < nat_greater n
#check nat_greater_nonzero -- nat_greater_nonzero : ∀ (n : ℕ), nat_greater n ≠ 0
```
Note that without the last argument `nat_greater_nonzero`, `nat_greater_lt` would be:
```lean
#check nat_greater_lt -- nat_greater_lt : ∀ (n : ℕ), n < nat_greater n ∧ nat_greater n ≠ 0
```
-/
@[user_attribute]
meta def expand_exists_attr : user_attribute unit (list name) :=
{ name := "expand_exists",
  descr := "From a proof that (a) value(s) exist(s) with certain properties, "
  ++ "constructs (an) instance(s) satisfying those properties.",
  parser := lean.parser.many lean.parser.ident,
  after_set := some (λ decl prio persistent, do
    d <- get_decl decl,
    names <- expand_exists_attr.get_param decl,
    parse_pis
    { original_decl := d,
      decl := λ is_t n ty val, (tactic.to_expr val >>= λ val,
        tactic.add_decl (if is_t then declaration.thm n d.univ_params ty (pure val)
          else declaration.defn n d.univ_params ty val default tt)),
      names := names } d.type) }

add_tactic_doc
{ name := "expand_exists",
  category := doc_category.attr,
  decl_names := [`tactic.expand_exists_attr],
  tags := [] }

end tactic
