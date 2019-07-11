/-
This consists of two user-commands which allow you to declare notation localized to a namespace.

* Declare notation which is localized to a namespace using:
```
localized "infix ` ⊹ `:60 := my_add" in my.add
```
* After this command it will be available in the same section/namespace/file, just as if you wrote `local infix ` ⊹ `:60 := my_add`
* You can open it in other places. The following command will declare the notation again as local notation in that section/namespace/files:
```
open_notation my.add
```
* More generally, the following will declare all localized notation in the specified namespaces.
```
open_notation namespace1 namespace2 ...
```
* You can also declare other localized commands, like local attributes
```
localized "attribute [simp] le_refl" in le
```
The code is based on code from Gabriel Ebner from the hott3 repository.
-/
import tactic.core
open lean lean.parser interactive tactic

reserve notation `localized`

meta def localized_attr_maker (nm : name) : user_attribute unit (list string) := {
    name := "_localized" ++ nm,
    descr := "(interal) attribute that flags localized commands in namespace " ++ nm.to_string,
    parser := return list.nil
}

/-- Get all commands in the given notation namespace and return them as a list of strings -/
meta def get_localized (ns : list name) : tactic (list string) :=
do env ← get_env,
   let ns := ns.filter $ λ nm, env.contains $ "_localized_decl" ++ nm,
   decls : list (list string) ← ns.mmap $ λ nm,
    (do attr ← mk_const $ "_localized_attr" ++ nm,
        attr ← eval_expr (user_attribute unit (list string)) attr,
        attr.get_param $ "_localized_decl" ++ nm),
   return decls.join

/-- Execute all commands in the given notation namespace -/
@[user_command] meta def open_notation_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "open_notation") : parser unit :=
do ns ← many ident,
   cmds ← get_localized ns,
   cmds.mmap' emit_code_here

/-- Add a new command to a notation namespace. The information in a notation namespace is stored
  into a declaration `_localized_decl.<namespace>` which has attribute `_localized_attr.<namespace>`
  which has as argument the list of commands. -/
@[user_command] meta def localized_cmd (meta_info : decl_meta_info)
  (_ : parse $ tk "localized") : parser unit :=
do cmd ← parser.pexpr, cmd ← i_to_expr cmd, cmd ← eval_expr string cmd,
   let cmd := "local " ++ cmd,
   emit_code_here cmd,
   tk "in",
   nm ← ident,
   env ← get_env,
   let attr_nm : name := "_localized_attr" ++ nm,
   let decl_nm : name := "_localized_decl" ++ nm,
   if env.contains decl_nm then
    (do attr ← mk_const attr_nm >>= λ e, eval_expr (user_attribute unit (list string)) e,
      l ← attr.get_param decl_nm,
      attr.set decl_nm (cmd::l) tt)
   else
    (do let attr_expr := `(localized_attr_maker nm),
        let attr_decl := declaration.defn attr_nm [] `(user_attribute unit (list string))
          attr_expr (reducibility_hints.regular 1 tt) ff,
        add_decl $ attr_decl,
        attribute.register attr_nm,
        attr ← eval_expr (user_attribute unit (list string)) attr_expr,
        let decl := mk_definition decl_nm [] `(unit) `(unit.star),
        add_decl $ decl,
        attr.set decl_nm [cmd] tt)

/-- Print all commands in a given notation namespace -/
meta def print_localized_commands (ns : list name) : tactic unit :=
do cmds ← get_localized ns, cmds.mmap' trace
