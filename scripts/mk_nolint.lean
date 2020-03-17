/-
Copyright (c) 2019 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robert Y. Lewis
-/

import tactic.lint system.io  -- these are required
import all   -- then import everything, to parse the library for failing linters

/-!
# mk_nolint

Defines a function that writes a file containing the names of all declarations
that fail the linting tests in `mathlib_linters`.

This is mainly used in the Travis check for mathlib.

It assumes that files generated by `mk_all.sh` are present.

Usage: `lean --run mk_nolint.lean` writes a file `nolints.txt` in the current directory.
-/

open io io.fs

open native

/-- Runs when called with `lean --run` -/
meta def main : io unit := do
e ← run_tactic get_env,
decls ← run_tactic lint_mathlib_decls,
let non_auto_decls := decls.filter (λ d, ¬ d.to_name.is_internal ∧ ¬ d.is_auto_generated e),
linters ← run_tactic $ get_linters mathlib_linters,
results ← run_tactic $ lint_core decls non_auto_decls linters,
env ← run_tactic tactic.get_env,
mathlib_path_len ← string.length <$> run_tactic tactic.get_mathlib_dir,
let failed_decls_by_file := rb_lmap.of_list (do
  (linter_name, _, decls) ← results,
  (decl_name, _) ← decls.to_list,
  let file_name := (env.decl_olean decl_name).get_or_else "",
  pure (file_name.popn mathlib_path_len, decl_name.to_string, linter_name.last)),
handle ← mk_file_handle "nolints.txt" mode.write,
put_str_ln handle "import .all",
put_str_ln handle "run_cmd tactic.skip",
failed_decls_by_file.to_list.reverse.mmap' (λ ⟨file_name, decls⟩, do
  put_str_ln handle $ "\n-- " ++ file_name,
  (rb_lmap.of_list decls).to_list.reverse.mmap $ λ ⟨decl, linters⟩,
    put_str_ln handle $ "apply_nolint " ++ decl ++ " " ++ " ".intercalate linters),
close handle
