/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

/-!
# Documentation commands

We generate html documentation from mathlib. It is convenient to collect lists of tactics, commands,
notes, etc. To facilitate this, we declare these documentation entries in the library
using special commands.

* `library_note` adds a note describing a certain feature or design decision. These can be
  referenced in doc strings with the text `note [name of note]`.
* `add_tactic_doc` adds an entry documenting an interactive tactic, command, hole command, or
  attribute.

Since these commands are used in files imported by `tactic.core`, this file has no imports.

## Implementation details

`library_note note_id note_msg` creates a declaration `` `library_note.i `` for some `i`.
This declaration is a pair of strings `note_id` and `note_msg`, and it gets tagged with the
`library_note` attribute.

Similarly, `add_tactic_doc` creates a declaration `` `tactic_doc.i `` that stores the provided
information.
-/

/-- A rudimentary hash function on strings. -/
def string.hash (s : string) : ℕ :=
s.fold 1 (λ h c, (33*h + c.val) % unsigned_sz)

/-- `mk_hashed_name nspace id` hashes the string `id` to a value `i` and returns the name
`nspace._i` -/
meta def string.mk_hashed_name (nspace : name) (id : string) : name :=
nspace <.> ("_" ++ to_string id.hash)

/-! ### The `library_note` command -/

/-- A user attribute `library_note` for tagging decls of type `string × string` for use in note
output. -/
@[user_attribute] meta def library_note_attr : user_attribute :=
{ name := `library_note,
  descr := "Notes about library features to be included in documentation" }

open tactic

/-- If `note_name` and `note` are `pexpr`s representing strings,
`add_library_note note_name note` adds a declaration of type `string × string` and tags it with
the `library_note` attribute. -/
meta def tactic.add_library_note (note_name note : pexpr) : tactic unit :=
do note_name ← to_expr note_name,
   let decl_name := (to_string note_name).mk_hashed_name `library_note,
   body ← to_expr ``((%%note_name, %%note) : string × string),
   add_decl $ mk_definition decl_name [] `(string × string) body,
   library_note_attr.set decl_name () tt none

open lean lean.parser interactive
/--
A command to add library notes. Syntax:
```
library_note "note id" "note content"
```

---

At various places in mathlib, we leave implementation notes that are referenced from many other
files. To keep track of these notes, we use the command `library_note`. This makes it easy to
retrieve a list of all notes, e.g. for documentation output.

These notes can be referenced in mathlib with the syntax `Note [note id]`.
Often, these references will be made in code comments (`--`) that won't be displayed in docs.
If such a reference is made in a doc string or module doc, it will be linked to the corresponding
note in the doc display.

Syntax:
```
library_note "note id" "note message"
```

An example from `meta.expr`:

```
library_note "open expressions"
"Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x)."
```

This note can be referenced near a usage of `pi_binders`:


```
-- See Note [open expressions]
/-- behavior of f -/
def f := pi_binders ...
```

-/
@[user_command] meta def library_note (_ : parse (tk "library_note")) : parser unit :=
do name ← parser.pexpr,
   note ← parser.pexpr,
   of_tactic $ tactic.add_library_note name note

/-- Collects all notes in the current environment.
Returns a list of pairs `(note_id, note_content)` -/
meta def tactic.get_library_notes : tactic (list (string × string)) :=
attribute.get_instances `library_note >>=
  list.mmap (λ dcl, mk_const dcl >>= eval_expr (string × string))

/-! ### The `add_tactic_doc_entry` command -/

/-- The categories of tactic doc entry. -/
@[derive [decidable_eq, has_reflect]]
inductive doc_category
| tactic | cmd | hole_cmd | attr

/-- Format a `doc_category` -/
meta def doc_category.to_string : doc_category → string
| doc_category.tactic := "tactic"
| doc_category.cmd := "command"
| doc_category.hole_cmd := "hole_command"
| doc_category.attr := "attribute"

meta instance : has_to_format doc_category := ⟨↑doc_category.to_string⟩

/-- The information used to generate a tactic doc entry -/
@[derive has_reflect]
structure tactic_doc_entry :=
(name : string)
(category : doc_category)
(decl_names : list _root_.name)
(tags : list string := [])
(description : string := "")
(inherit_description_from : option _root_.name := none)

/-- format a `tactic_doc_entry` -/
meta def tactic_doc_entry.to_string : tactic_doc_entry → string
| ⟨name, category, decl_names, tags, description, _⟩ :=
let decl_names := decl_names.map (repr ∘ to_string),
    tags := tags.map repr in
"{" ++ to_string (format!"\"name\": {repr name}, \"category\": \"{category}\", \"decl_names\":{decl_names}, \"tags\": {tags}, \"description\": {repr description}") ++ "}"

meta instance : has_to_string tactic_doc_entry :=
⟨tactic_doc_entry.to_string⟩

/-- `update_description_from tde inh_id` replaces the `description` field of `tde` with the
    doc string of the declaration named `inh_id`. -/
meta def tactic_doc_entry.update_description_from (tde : tactic_doc_entry) (inh_id : name) :
  tactic tactic_doc_entry :=
do ds ← doc_string inh_id <|> fail (to_string inh_id ++ " has no doc string"),
   return { description := ds .. tde }

/--
`update_description tde` replaces the `description` field of `tde` with:

* the doc string of `tde.inherit_description_from`, if this field has a value
* the doc string of the entry in `tde.decl_names`, if this field has length 1

If neither of these conditions are met, it returns `tde`. -/
meta def tactic_doc_entry.update_description (tde : tactic_doc_entry) : tactic tactic_doc_entry :=
match tde.inherit_description_from, tde.decl_names with
| some inh_id, _ := tde.update_description_from inh_id
| none, [inh_id] := tde.update_description_from inh_id
| none, _ := return tde
end

/-- A user attribute `tactic_doc` for tagging decls of type `tactic_doc_entry`
for use in doc output -/
@[user_attribute] meta def tactic_doc_entry_attr : user_attribute :=
{ name := `tactic_doc,
  descr := "Information about a tactic to be included in documentation" }

/-- Collects everything in the environment tagged with the attribute `tactic_doc`. -/
meta def tactic.get_tactic_doc_entries : tactic (list tactic_doc_entry) :=
attribute.get_instances `tactic_doc >>=
  list.mmap (λ dcl, mk_const dcl >>= eval_expr tactic_doc_entry)

/-- `add_tactic_doc tde` assumes `tde : pexpr` represents a term of type `tactic_doc_entry`.
It adds a declaration to the environment with `tde` as its body and tags it with the `tactic_doc`
attribute. If `tde.decl_names` has exactly one entry, and the referenced declaration is missing a
doc string, it adds `tde.description` as the doc string. -/
meta def tactic.add_tactic_doc (tde : expr) : tactic unit :=
do tde ← eval_expr tactic_doc_entry tde,
   when (tde.description = "" ∧ tde.inherit_description_from.is_none ∧ tde.decl_names.length ≠ 1) $
     fail "A tactic doc entry must contain either a description or a declaration to inherit a description from",
   tde ← if tde.description = "" then tde.update_description else return tde,
   let decl_name := (tde.name ++ tde.category.to_string).mk_hashed_name `tactic_doc,
   add_decl $ mk_definition decl_name [] `(tactic_doc_entry) (reflect tde),
   tactic_doc_entry_attr.set decl_name () tt none

/-- Given a `pexpr`, attempt to elaborate it and return either the error message or the result. -/
private meta def elab_as_tde_or_error_msg (pe : pexpr) : tactic (expr ⊕ string) :=
λ s, match to_expr ``(%%pe : tactic_doc_entry) ff ff s with
| interaction_monad.result.success e s := interaction_monad.result.success (sum.inl e) s
| interaction_monad.result.exception (some msg) _ _ := interaction_monad.result.success (sum.inr (msg ()).to_string) s
| interaction_monad.result.exception none _ _ := interaction_monad.result.success (sum.inr (format!"{pe} is not a valid tactic doc entry").to_string) s
end

/--
A command used to add documentation for a tactic, command, hole command, or attribute.

Usage: after defining an interactive tactic, command, or attribute,
add its documentation as follows.
```lean
add_tactic_doc
{ name := "display name of the tactic",
  category := cat,
  decl_names := [`dcl_1, dcl_2],
  tags := ["tag_1", "tag_2"],
  description := "describe what the command does here"
}
```

The argument to `add_tactic_doc` is a structure of type `tactic_doc_entry`.
* `name` refers to the display name of the tactic; it is used as the header of the doc entry.
* `cat` refers to the category of doc entry.
  Options: `doc_category.tactic`, `doc_category.cmd`, `doc_category.hole_cmd`, `doc_category.attr`
* `decl_names` is a list of the declarations associated with this doc. For instance,
  the entry for `linarith` would set ``decl_names := [`tactic.interactive.linarith]``.
  Some entries may cover multiple declarations.
  It is only necessary to list the interactive versions of tactics.
* `tags` is an optional list of strings used to categorize entries.
* `description` is the body of the entry. Like doc strings, it can be formatted with markdown.
  What you are reading now is the description of `add_tactic_doc`.

If only one related declaration is listed in `decl_names` and it does not have a doc string,
`description` will be automatically added as its doc string. If there are multiple declarations, you
can select the one to be used by passing a name to the `inherit_description_from` field.

If you prefer a tactic to have a doc string that is different then the doc entry, then between
the `/--` `-/` markers, write the desired doc string first, then `---`, then the doc entry.

Note that providing a badly formed `tactic_doc_entry` to the command can result in strange error
messages.

-/
@[user_command] meta def add_tactic_doc_command (_ : parse $ tk "add_tactic_doc") : parser unit :=
do pe ← parser.pexpr,
   elab ← of_tactic (elab_as_tde_or_error_msg pe),
   match elab with
   | sum.inl e := tactic.add_tactic_doc e
   | sum.inr msg := interaction_monad.fail msg
   end .

add_tactic_doc
{ name                     := "library_note",
  category                 := doc_category.cmd,
  decl_names               := [`library_note, `tactic.add_library_note],
  tags                     := ["documentation"],
  inherit_description_from := `library_note }

add_tactic_doc
{ name                     := "add_tactic_doc",
  category                 := doc_category.cmd,
  decl_names               := [`add_tactic_doc_command, `tactic.add_tactic_doc],
  tags                     := ["documentation"],
  inherit_description_from := `add_tactic_doc_command }

-- add docs to core tactics

add_tactic_doc
{ name := "cc (congruence closure)",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.cc],
  tags := ["core", "finishing"],
  description :=
"The congruence closure tactic `cc` tries to solve the goal by chaining
equalities from context and applying congruence (i.e. if `a = b`, then `f a = f b`).
It is a finishing tactic, i.e. it is meant to close
the current goal, not to make some inconclusive progress.
A mostly trivial example would be:

```lean
example (a b c : ℕ) (f : ℕ → ℕ) (h: a = b) (h' : b = c) : f a = f c := by cc
```

As an example requiring some thinking to do by hand, consider:

```lean
example (f : ℕ → ℕ) (x : ℕ)
  (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
  f x = x :=
by cc
```

The tactic works by building an equality matching graph. It's a graph where
the vertices are terms and they are linked by edges if they are known to
be equal. Once you've added all the equalities in your context, you take
the transitive closure of the graph and, for each connected component
(i.e. equivalence class) you can elect a term that will represent the
whole class and store proofs that the other elements are equal to it.
You then take the transitive closure of these equalities under the
congruence lemmas.

The `cc` implementation in Lean does a few more tricks: for example it
derives `a=b` from `nat.succ a = nat.succ b`, and `nat.succ a !=
nat.zero` for any `a`.

* The starting reference point is Nelson, Oppen, [Fast decision procedures based on congruence
closure](http://www.cs.colorado.edu/~bec/courses/csci5535-s09/reading/nelson-oppen-congruence.pdf),
Journal of the ACM (1980)

* The congruence lemmas for dependent type theory as used in Lean are described in
[Congruence closure in intensional type theory](https://leanprover.github.io/papers/congr.pdf)
(de Moura, Selsam IJCAR 2016).
" }

add_tactic_doc
{ name := "conv",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.conv],
  tags := ["core"],
  description :=
"`conv {...}` allows the user to perform targeted rewriting on a goal or hypothesis,
by focusing on particular subexpressions.

See <https://leanprover-community.github.io/mathlib_docs/conv.html> for more details.

Inside `conv` blocks, mathlib currently additionally provides
* `erw`,
* `ring` and `ring2`,
* `norm_num`,
* `norm_cast`, and
* `conv` (within another `conv`).

Using `conv` inside a `conv` block allows the user to return to the previous
state of the outer `conv` block after it is finished. Thus you can continue
editing an expression without having to start a new `conv` block and re-scoping
everything. For example:
```lean
example (a b c d : ℕ) (h₁ : b = c) (h₂ : a + c = a + d) : a + b = a + d :=
by conv {
  to_lhs,
  conv {
    congr, skip,
    rw h₁,
  },
  rw h₂,
}
```
Without `conv`, the above example would need to be proved using two successive
`conv` blocks, each beginning with `to_lhs`.

Also, as a shorthand, `conv_lhs` and `conv_rhs` are provided, so that
```lean
example : 0 + 0 = 0 :=
begin
  conv_lhs { simp }
end
```
just means
```lean
example : 0 + 0 = 0 :=
begin
  conv { to_lhs, simp }
end
```
and likewise for `to_rhs`.
" }

add_tactic_doc
{ name := "simp",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.simp],
  tags := ["core", "simplification"],
  description :=
"
The `simp` tactic works by applying a conditional term rewriting system to try and prove, or at
least simplify, your goal. What this basically means is that `simp` is equipped with a list of
lemmas (those tagged with the `simp` attribute), many of which are of the form `X = Y` or `X iff Y`,
and attempts to match subterms of the goal with the left hand side of a rule, and then replaces the
subterm with the right hand side. The system is conditional in the sense that lemmas are allowed to
have preconditions (`P -> (X = Y)`) and in these cases it will try and prove the precondition using
its simp lemmas before applying `X = Y`.

You can watch `simp` in action by using `set_option trace.simplify true` in your code. For example

```lean
namespace hidden

definition cong (a b m : ℤ) : Prop := ∃ n : ℤ, b - a = m * n

notation a ` ≡ ` b ` mod ` m  := cong a b m
set_option trace.simplify true
theorem cong_refl (m : ℤ) : ∀ a : ℤ, a ≡ a mod m :=
begin
intro a,
unfold cong,
existsi (0:ℤ),
simp
end

end hidden
```

If you do this exercise you will discover firstly that `simp` spends a lot of its time trying random
lemmas and then giving up very shortly afterwards, and also that the `unfold` command is also
underlined in green -- Lean seems to apply `simp` when you do an `unfold` as well (apparently
`unfold` just asks `simp` to do its dirty work for it -- `unfold X` is close to `simp only [X]`).

If you only want to see what worked rather than all the things that didn't, you could try
`set_option trace.simplify.rewrite true`.

## Simp lemmas

In case you want to train `simp` to use certain extra lemmas (for example because they're coming up
again and again in your work) you can add new lemmas for yourself. For example in mathlib in
`algebra/ring.lean` we find the line

```lean
@[simp] theorem ne_zero (u : units α) : (u : α) ≠ 0
```

This lemma is then added to `simp`'s armoury. Note several things however.

1) It might not be wise to make a random theorem into a simp lemma. Ideally the result has to be of
a certain kind, the most important kinds being those of the form `A=B` and `A↔B`. Note however that
if you want to add `fact` to `simp`'s weaponry, you can prove

```lean
@[simp] lemma my_lemma : fact ↔ true
```

(and in fact more recent versions of Lean do this automatically when you try to add random theorems
to the simp dataset).

2) If you are not careful you can add a bad simp lemma of the form
`foo x y = [something mentioning foo]` and then `simp` will attempt to rewrite `foo` and then end up
with another one, and attempt to rewrite that, and so on. This can be fixed by using `rw` instead of
`simp`, or using the config option `{single_pass := tt}`.


## When it is unadvisable to use simp

Using `simp` in the middle of proofs is a `simp` anti-pattern, which will produce brittle code. In
other words, don't use `simp` in the middle of proofs. Use it to finish proofs. If you really need
to simplify a goal in the middle of a proof, then use `simp`, but afterwards cut and paste the goal
into your code and write `suffices : (simplified thing), by simpa using this`. This is really
important because the behaviour of `simp` changes sometimes, and if you put `simp` in the middle of
proofs then your code might randomly stop compiling and it will be hard to figure out why if you
didn't write down the exact thing which `simp` used to be reducing your goal to.

## How to use simp better

Conversely, if you ever manage to close a goal with `simp`, then take a look at the line before you
ran `simp`. Could you have run `simp` one line earlier? How far back did `simp` start working? Even
for goals where you didn't use `simp` at all -- could you have used `simp` for your last line? What
about the last-but one? And so on.

Recall that `simp` lemmas are almost all of the form `X = Y` or `X ↔ Y`. Hence `simp` might work
well for such goals. However what about goals of the form `X → Y`? You could try assuming `h : X`
and then running either `simpa using h` or `simp {contextual := tt}` to see if Lean can deduce `Y`.

## Simp options

The behaviour of `simp` can be tweaked by `simp` variants and also by passing options to the
algorithm. A good place to start is to look at the docstring for `simp` (write `simp` in VS Code and
hover your mouse over it to see the docstring). Here are some examples, some of which are covered by
the docstring and some of which are not.

1) `simp only [H1, H2, H3]` uses only lemmas `H1`, `H2`, and `H3` rather than `simp`s full
collection of lemmas. Whyever might one want to do this in practice? Because sometimes `simp`
simplifies things too much -- it might unfold things that you wanted to keep folded, for example.
Another reason is that using `simp only` can speed up slow `simp` calls significantly.

2) `simp [-X]` stops `simp` from using lemma `X`. One could imagine using this as another solution
when one finds `simp` doing more than you would like. Recall from above that
`set_option trace.simplify.rewrite true` shows you exactly which lemmas `simp` is using.

3) `simp * at *`. This simplifies everything in sight. Use if life is getting complicated.

4) `simp {single_pass := tt}` -- this `single_pass` is a config option, one of around 16 at the
time of writing. One can use `single_pass` to avoid loops which would otherwise occur; for example
`nat.gcd_def` is an equality with `gcd` on both the left and right hand side, so
`simp [nat.gcd_def]` is risky behaviour whereas `simp [nat.gcd_def] {single_pass := tt}` is not.
As you can imagine, `simp only [h] {single_pass := tt}` here makes simp behave pretty much like
`rw h`.

5) Search for `structure simp_config` in the file `init/meta/simp_tactic.lean` in core Lean to see
the full list of config options. Others, many undocumented, are:
```
(max_steps : nat           := simp.default_max_steps)
(contextual : bool         := ff)
(lift_eq : bool            := tt)
(canonize_instances : bool := tt)
(canonize_proofs : bool    := ff)
(use_axioms : bool         := tt)
(zeta : bool               := tt)
(beta : bool               := tt)
(eta  : bool               := tt)
(proj : bool               := tt) -- reduce projections
(iota : bool               := tt)
(iota_eqn : bool           := ff) -- reduce using all equation lemmas generated by equation/pattern-matching compiler
(constructor_eq : bool     := tt)
(single_pass : bool        := ff)
(fail_if_unchanged         := tt)
(memoize                   := tt)
```

We see from the changelog that setting `constructor_eq` to true will reduce equations of the form
`X a1 a2... = Y b1 b2...` to false if `X` and `Y` are distinct constructors for the same type, and
to `a1 = b1 and a2 = b2 and...` if `X = Y` are the same constructor. Another interesting example is
`iota_eqn` : `simp!` is shorthand for `simp {iota_eqn := tt}`. This adds non-trivial equation lemmas
generated by the equation/pattern-matching compiler to `simp`'s weaponry. See the changelog for more
details.

## Cutting edge `simp` facts

If you want to find out the most recent tweaks to `simp`, a very good place to look is
[the changelog](https://github.com/leanprover/lean/blob/master/doc/changes.md).

## Something that could be added later on

\"Re: documentation. If you mention congruence, you could show off `simp`'s support for congruence
relations. If you show reflexivity and transitivity for cong, and have congruence lemmas for +,
etc., then you can rewrite with congruences as if they were equations.\"
" }
