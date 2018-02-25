# mathlib

[![Build Status](https://travis-ci.org/leanprover/mathlib.svg?branch=master)](https://travis-ci.org/leanprover/mathlib)

Lean standard library

Besides [Lean's general documentation](https://leanprover.github.io/documentation/), the documentation of mathlib consists of:
* a description of [currently covered theories](docs/theories.md)
* an explanation of [naming conventions](docs/naming.md) that is useful
  to find or contribute definitions and lemmas
* a description of [tactics](docs/tactics.md) introduced in mathlib
* a [style guide](docs/style.md) for contributors
* a tentative list of [work in progress](docs/wip.md) to make sure
  efforts are not duplicated without collaboration

Development of this library very closely follows the development of Lean
itself. Hence this library will almost never be usable with stable
releases of Lean. On the other hand, there can be some short delay
between nightly releases of Lean and adaptations of mathlib. In such
cases, mathlib works with no release available from the main
[download page](https://leanprover.github.io/download/). However, the
[nightlies directory](nightlies/) should always contain releases working
with current mathlib.
