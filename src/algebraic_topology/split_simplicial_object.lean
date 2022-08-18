/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.simplicial_object
import category_theory.limits.shapes.finite_products

/-!

# Split simplicial objects

In this file, we introduce the notion of split simplicial object.
If `C` is a category that has finite coproducts, a splitting
`s : splitting X` of a simplical object `X` in `C` consists
of the datum of a sequence of objects `s.N : ℕ → C` and a
sequence of morphisms `s.ι n : s.N n → X _[n]` that have
the property that a certain canonical map identifies `X _[n]`
with the coproduct of objects `s.N i` indexed by all possible
epimorphisms `[n] ⟶ [i]` in `simplex_category`. (We do not
assume that the morphisms `s.ι n` are monomorphisms: in the
most common categories, this would be a consequence of the
axioms.)

## References
* [Stacks: Splitting simplicial objects] https://stacks.math.columbia.edu/tag/017O

-/

noncomputable theory

open category_theory
open category_theory.category
open category_theory.limits
open opposite
open_locale simplicial

universe u

variables {C : Type*} [category C]

namespace simplicial_object

namespace splitting

/-- The index set which appears in the definition of split simplicial objects. -/
def index_set (Δ : simplex_categoryᵒᵖ) :=
Σ (Δ' : simplex_categoryᵒᵖ), { α : Δ.unop ⟶ Δ'.unop // epi α }

namespace index_set

/-- The element in `splitting.index_set Δ` attached to an epimorphism `f : Δ ⟶ Δ'`. -/
@[simps]
def mk {Δ Δ' : simplex_category} (f : Δ ⟶ Δ') [epi f] : index_set (op Δ) :=
⟨op Δ', f, infer_instance⟩

variables {Δ' Δ : simplex_categoryᵒᵖ} (A : index_set Δ)

/-- The epimorphism in `simplex_category` associated to `A : splitting.index_set Δ` -/
def e := A.2.1

instance : epi A.e := A.2.2

lemma ext' : A = ⟨A.1, ⟨A.e, A.2.2⟩⟩ := by tidy

lemma ext (A₁ A₂ : index_set Δ) (h₁ : A₁.1 = A₂.1)
  (h₂ : A₁.e ≫ eq_to_hom (by rw h₁) = A₂.e) : A₁ = A₂ :=
begin
  rcases A₁ with ⟨Δ₁, ⟨α₁, hα₁⟩⟩,
  rcases A₂ with ⟨Δ₂, ⟨α₂, hα₂⟩⟩,
  simp only at h₁,
  subst h₁,
  simp only [eq_to_hom_refl, comp_id, index_set.e] at h₂,
  simp only [h₂],
end

instance : fintype (index_set Δ) :=
fintype.of_injective
  ((λ A, ⟨⟨A.1.unop.len, nat.lt_succ_iff.mpr
    (simplex_category.len_le_of_epi (infer_instance : epi A.e))⟩, A.e.to_order_hom⟩) :
    index_set Δ → (sigma (λ (k : fin (Δ.unop.len+1)), (fin (Δ.unop.len+1) → fin (k+1)))))
begin
  rintros ⟨Δ₁, α₁⟩ ⟨Δ₂, α₂⟩ h₁,
  induction Δ₁ using opposite.rec,
  induction Δ₂ using opposite.rec,
  simp only at h₁,
  have h₂ : Δ₁ = Δ₂ := by { ext1, simpa only [subtype.mk_eq_mk] using h₁.1, },
  subst h₂,
  refine ext _ _ rfl _,
  ext : 2,
  exact eq_of_heq h₁.2,
end

variable (Δ)

/-- The distinguished element in `splitting.index_set Δ` which corresponds to the
identity of `Δ`. -/
def id : index_set Δ := ⟨Δ, ⟨𝟙 _, by apply_instance,⟩⟩

instance : inhabited (index_set Δ) := ⟨id Δ⟩

end index_set

variables (N : ℕ → C) (Δ : simplex_categoryᵒᵖ)
  (X : simplicial_object C) (φ : Π n, N n ⟶ X _[n])

/-- Given a sequences of objects `N : ℕ → C` in a category `C`, this is
a family of objects indexed by the elements `A : splitting.index_set Δ`.
The `Δ`-simplices of a split simplicial objects shall identify to the
coproduct of objects in such a family. -/
@[simp, nolint unused_arguments]
def summand (A : index_set Δ) : C := N A.1.unop.len

variable [has_finite_coproducts C]

/-- The coproduct of the family `summand N Δ` -/
@[simp]
def coprod := ∐ summand N Δ

variable {Δ}

/-- The inclusion of a summand in the coproduct. -/
@[simp]
def ι_coprod (A : index_set Δ) : N A.1.unop.len ⟶ coprod N Δ := sigma.ι _ A

variables {N}

/-- The canonical morphism `coprod N Δ ⟶ X.obj Δ` attached to a sequence
of objects `N` and a sequence of morphisms `N n ⟶ X _[n]`. -/
@[simp]
def map (Δ : simplex_categoryᵒᵖ) : coprod N Δ ⟶ X.obj Δ :=
sigma.desc (λ A, φ A.1.unop.len ≫ X.map A.e.op)

end splitting

variable [has_finite_coproducts C]

/-- A splitting of a simplicial object `X` consists of the datum of a sequence
of objects `N`, a sequence of morphisms `ι : N n ⟶ X _[n]` such that
for all `Δ : simplex_categoryhᵒᵖ`, the canonical map `splitting.map X ι Δ`
is an isomorphism. -/
@[nolint has_nonempty_instance]
structure splitting (X : simplicial_object C) :=
(N : ℕ → C)
(ι : Π n, N n ⟶ X _[n])
(map_is_iso' : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (splitting.map X ι Δ))

namespace splitting

variables {X Y : simplicial_object C} (s : splitting X)

instance map_is_iso (Δ : simplex_categoryᵒᵖ) : is_iso (splitting.map X s.ι Δ) :=
s.map_is_iso' Δ

/-- The isomorphism on simplices given by the axiom `splitting.map_is_iso'` -/
@[simps]
def iso (Δ : simplex_categoryᵒᵖ) : coprod s.N Δ ≅ X.obj Δ :=
as_iso (splitting.map X s.ι Δ)

/-- Via the isomorphism `s.iso Δ`, this is the inclusion of a summand
in the direct sum decomposition given by the splitting `s : splitting X`. -/
def ι_summand {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.N A.1.unop.len ⟶ X.obj Δ :=
splitting.ι_coprod s.N A ≫ (s.iso Δ).hom

@[reassoc]
lemma ι_summand_eq {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.ι_summand A = s.ι A.1.unop.len ≫ X.map A.e.op :=
begin
  dsimp only [ι_summand, iso.hom],
  erw [colimit.ι_desc, cofan.mk_ι_app],
end

lemma ι_summand_id (n : ℕ) : s.ι_summand (index_set.id (op [n])) = s.ι n :=
by { erw [ι_summand_eq, X.map_id, comp_id], refl, }

/-- As it is stated in `splitting.hom_ext`, a morphism `f : X ⟶ Y` from a split
simplicial object to any simplicial object is determined by its restrictions
`s.φ f n : s.N n ⟶ Y _[n]` to the distinguished summands in each degree `n`. -/
@[simp]
def φ (f : X ⟶ Y) (n : ℕ) : s.N n ⟶ Y _[n] := s.ι n ≫ f.app (op [n])

@[simp, reassoc]
lemma ι_summand_comp_app (f : X ⟶ Y) {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.ι_summand A ≫ f.app Δ = s.φ f A.1.unop.len ≫ Y.map A.e.op :=
by simp only [ι_summand_eq_assoc, φ, nat_trans.naturality, assoc]

lemma hom_ext' {Z : C} {Δ : simplex_categoryᵒᵖ} (f g : X.obj Δ ⟶ Z)
  (h : ∀ (A : index_set Δ), s.ι_summand A ≫ f = s.ι_summand A ≫ g) :
    f = g :=
begin
  rw ← cancel_epi (s.iso Δ).hom,
  ext A,
  discrete_cases,
  simpa only [ι_summand_eq, iso_hom, colimit.ι_desc_assoc, cofan.mk_ι_app, assoc] using h A,
end

lemma hom_ext (f g : X ⟶ Y) (h : ∀ n : ℕ, s.φ f n = s.φ g n) : f = g :=
begin
  ext Δ,
  apply s.hom_ext',
  intro A,
  induction Δ using opposite.rec,
  induction Δ using simplex_category.rec with n,
  dsimp,
  simp only [s.ι_summand_comp_app, h],
end

/-- The map `X.obj Δ ⟶ Z` obtained by providing a family of morphisms on all the
terms of decomposition given by a splitting `s : splitting X`  -/
def desc {Z : C} (Δ : simplex_categoryᵒᵖ)
  (F : Π (A : index_set Δ), s.N A.1.unop.len ⟶ Z) : X.obj Δ ⟶ Z :=
(s.iso Δ).inv ≫ sigma.desc F

@[simp, reassoc]
lemma ι_desc {Z : C} (Δ : simplex_categoryᵒᵖ)
  (F : Π (A : index_set Δ), s.N A.1.unop.len ⟶ Z) (A : index_set Δ) :
  s.ι_summand A ≫ s.desc Δ F = F A :=
begin
  dsimp only [ι_summand, desc],
  simp only [assoc, iso.hom_inv_id_assoc, ι_coprod],
  erw [colimit.ι_desc, cofan.mk_ι_app],
end

end splitting

end simplicial_object
