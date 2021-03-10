/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_topology.simplicial_object
import category_theory.yoneda

/-!
A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to all these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

We define the standard simplices `Δ[n]` as simplicial sets,
and their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `open_locale sSet`.)

## Future work

There isn't yet a complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order preserving function `fin n → fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.
-/

universes v u

open category_theory

/-- The category of simplicial sets.
This is the category of contravariant functors from
`simplex_category` to `Type u`. -/
@[derive large_category]
def sSet : Type (u+1) := simplicial_object (Type u)

namespace sSet

/-- The `n`-th standard simplex `Δ[n]` associated with a nonempty finite linear order `n`
is the Yoneda embedding of `n`. -/
def standard_simplex : simplex_category ⥤ sSet := yoneda

localized "notation `Δ[`n`]` := standard_simplex.obj n" in sSet

instance : inhabited sSet := ⟨standard_simplex.obj (0 : ℕ)⟩

/-- The `m`-simplices of the `n`-th standard simplex are
the monotone maps from `fin (m+1)` to `fin (n+1)`. -/
def as_preorder_hom {n} {m} (α : Δ[n].obj m) :
  preorder_hom (fin (m.unop+1)) (fin (n+1)) := α

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex consists of
all `m`-simplices of `standard_simplex n` that are not surjective
(when viewed as monotone function `m → n`). -/
def boundary (n : ℕ) : sSet :=
{ obj := λ m, {α : Δ[n].obj m // ¬ function.surjective (as_preorder_hom α)},
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : Δ[n].obj m₁),
  by { intro h, apply α.property, exact function.surjective.of_comp h }⟩ }

localized "notation `∂Δ[`n`]` := boundary n" in sSet

/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/
def boundary_inclusion (n : ℕ) :
  ∂Δ[n] ⟶ Δ[n] :=
{ app := λ m (α : {α : Δ[n].obj m // _}), α }

/-- `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex, where `i : n`.
It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
def horn (n : ℕ) (i : fin (n+1)) : sSet :=
{ obj := λ m,
  { α : Δ[n].obj m // set.range (as_preorder_hom α) ∪ {i} ≠ set.univ },
  map := λ m₁ m₂ f α, ⟨f.unop ≫ (α : Δ[n].obj m₁),
  begin
    intro h, apply α.property,
    rw set.eq_univ_iff_forall at h ⊢, intro j,
    apply or.imp _ id (h j),
    intro hj,
    exact set.range_comp_subset_range _ _ hj,
  end⟩ }

localized "notation `Λ[`n`, `i`]` := horn n i" in sSet

/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/
def horn_inclusion (n : ℕ) (i : fin (n+1)) :
  Λ[n, i] ⟶ Δ[n] :=
{ app := λ m (α : {α : Δ[n].obj m // _}), α }

end sSet
