# How to use calc

[NB: KB wrote this because he always struggles to find the relevant
part of TPIL because naive search fails; the TPIL link is [section 4.3](https://leanprover.github.io/theorem_proving_in_lean/quantifiers_and_equality.html#calculational-proofs)]

`calc` appears to be something called an `environment`. I don't really
know what an environment is. 

calc will work with any relation tagged [refl], and if they're also tagged
[trans] then calc is a bit more powerful.

Here's an example of a proof which uses `calc`. When I type calc I almost
always immediately follow it with something that looks similar to the
set-up below. In fact I wish I could just type `calc` and then press
one keyboard shortcut and the below set-up would just appear. Patrick
says I should learn about [snippets](https://code.visualstudio.com/docs/editor/userdefinedsnippets).

```lean
open nat
theorem zero_add_induction_step (d : ℕ) (H : 0 + d = d) : 0 + succ d = succ d :=
calc 0 + succ d = _      : _
--- ABOVE HERE write more ... lines
...             = succ d : _
```

I type it out, I fill in the holes, and occasionally I get annoyed by red
ines under ...s because the error messages are hard for me to follow sometimes.

When I've finished it might look something like this.

```lean
open nat
theorem zero_add_induction_step (d : ℕ) (H : 0 + d = d) : 0 + succ d = succ d :=
calc 0 + succ d = succ (0 + d) : rfl
...             = succ d : by rw [H]
```

