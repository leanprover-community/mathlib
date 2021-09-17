/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import linear_algebra.free_module
import linear_algebra.char_poly.coeff

/-!

# Characteristic polynomial

We define the characteristic polynomial of `f : M →ₗ[R] N`, where `M` and `N` are free `R`-modules.

## Main definition

* `charpoly f` : the characteristic polynomial of `f`.

-/

universes u v

variables {R : Type u} {M : Type v} [comm_ring R] [nontrivial R]
variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M]

open_locale classical

noncomputable theory

open module.free

section basic

def charpoly (f : M →ₗ[R] M) : polynomial R :=
(linear_map.to_matrix (choose_basis R M) (choose_basis R M) f).charpoly

end basic
