/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.sites.grothendieck
import category_theory.sites.pretopology
import category_theory.sites.sheaf
import category_theory.full_subcategory
import category_theory.types

universes v u
namespace category_theory

open category_theory category limits sieve classical

variables {C : Type u} [category.{v} C]

namespace sheaf

variables {P : Cᵒᵖ ⥤ Type v}
variables {X Y : C} {S : sieve X} {R : presieve X}
variables (J J₂ : grothendieck_topology C)

/--
To show `P` is a sheaf for the binding of `U` with `B`, it suffices to show that `P` is a sheaf for
`U`, that `P` is a sheaf for each sieve in `B`, and that it is separated for any pullback of any
sieve in `B`.

This is mostly an auxiliary lemma to show `is_sheaf_for_trans`.
-/
lemma is_sheaf_for_bind (P : Cᵒᵖ ⥤ Type v) (U : sieve X)
  (B : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f → sieve Y)
  (hU : presieve.is_sheaf_for P U)
  (hB : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), presieve.is_sheaf_for P (B hf))
  (hB' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (h : U f) ⦃Z⦄ (g : Z ⟶ Y), presieve.is_separated_for P ((B h).pullback g)) :
  presieve.is_sheaf_for P (sieve.bind U B) :=
begin
  intros s hs,
  let y : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), presieve.family_of_elements P (B hf) :=
    λ Y f hf Z g hg, s _ (presieve.bind_comp _ _ hg),
  have hy : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).compatible,
  { intros Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm,
    apply hs,
    apply reassoc_of comm },
  let t : presieve.family_of_elements P U,
  { intros Y f hf,
    apply (hB hf).amalgamate (y hf) (hy hf) },
  have ht : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).is_amalgamation (t f hf),
  { intros Y f hf,
    apply (hB hf).is_amalgamation _ },
  have hT : t.compatible,
  { rw presieve.compatible_iff_sieve_compatible,
    intros Z W f h hf,
    apply (hB (U.downward_closed hf h)).is_separated_for.ext,
    intros Y l hl,
    apply (hB' hf (l ≫ h)).ext,
    intros M m hm,
    have : (bind ⇑U B) (m ≫ l ≫ h ≫ f),
    { have : bind U B _ := presieve.bind_comp f hf hm,
      simpa using this },
    transitivity s (m ≫ l ≫ h ≫ f) this,
    { have := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m),
      rw [op_comp, functor_to_types.map_comp_apply] at this,
      rw this,
      change s _ _ = s _ _,
      simp },
    { have : s _ _ = _ := (ht hf _ hm).symm,
      simp only [assoc] at this,
      rw this,
      simp } },
  refine ⟨hU.amalgamate t hT, _, _⟩,
  { rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩,
    rw [op_comp, functor_to_types.map_comp_apply, presieve.is_sheaf_for.valid_glue _ _ _ hg],
    apply ht hg _ hf },
  { intros y hy,
    apply hU.is_separated_for.ext,
    intros Y f hf,
    apply (hB hf).is_separated_for.ext,
    intros Z g hg,
    rw [←functor_to_types.map_comp_apply, ←op_comp, hy _ (presieve.bind_comp _ _ hg),
        hU.valid_glue _ _ hf, ht hf _ hg] }
end

/--
Given two sieves `R` and `S`, to show that `P` is a sheaf for `S`, we can show:
* `P` is a sheaf for `R`
* `P` is a sheaf for the pullback of `S` along any arrow in `R`
* `P` is separated for the pullback of `R` along any arrow in `S`.

This is mostly an auxiliary lemma to construct `finest_topology`.
-/
lemma is_sheaf_for_trans (P : Cᵒᵖ ⥤ Type v) (R S : sieve X)
  (hR : presieve.is_sheaf_for P R)
  (hR' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : S f), presieve.is_separated_for P (R.pullback f))
  (hS : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : R f), presieve.is_sheaf_for P (S.pullback f)) :
  presieve.is_sheaf_for P S :=
begin
  have : (bind ⇑R (λ (Y : C) (f : Y ⟶ X) (hf : R f), pullback f S) : presieve X) ≤ S,
  { rintros Z f ⟨W, f, g, hg, (hf : S _), rfl⟩,
    apply hf },
  apply presieve.is_sheaf_for_subsieve_aux P this,
  apply is_sheaf_for_bind _ _ _ hR hS,
  { intros Y f hf Z g,
    dsimp,
    rw ← pullback_comp,
    apply (hS (R.downward_closed hf _)).is_separated_for },
  { intros Y f hf,
    have : (sieve.pullback f (bind R (λ T (k : T ⟶ X) (hf : R k), pullback k S))) = R.pullback f,
    { ext Z g,
      split,
      { rintro ⟨W, k, l, hl, _, comm⟩,
        rw [mem_pullback, ← comm],
        simp [hl] },
      { intro a,
        refine ⟨Z, 𝟙 Z, _, a, _⟩,
        simp [hf] } },
    rw this,
    apply hR' hf },
end

/-- Construct the finest (largest) Grothendieck topology for which the given presheaf is a sheaf. -/
def finest_topology_single (P : Cᵒᵖ ⥤ Type v) : grothendieck_topology C :=
{ sieves := λ X S, ∀ Y (f : Y ⟶ X), presieve.is_sheaf_for P (S.pullback f),
  top_mem' := λ X Y f,
  begin
    rw sieve.pullback_top,
    exact presieve.is_sheaf_for_top_sieve P,
  end,
  pullback_stable' := λ X Y S f hS Z g,
  begin
    rw ← pullback_comp,
    apply hS,
  end,
  transitive' := λ X S hS R hR Z g,
  begin
    -- This is the hard part of the construction, showing that the given set of sieves satisfies
    -- the transitivity axiom.
    refine is_sheaf_for_trans P (pullback g S) _ (hS Z g) _ _,
    { intros Y f hf,
      rw ← pullback_comp,
      apply (hS _ _).is_separated_for },
    { intros Y f hf,
      have := hR hf _ (𝟙 _),
      rw [pullback_id, pullback_comp] at this,
      apply this },
  end }

/--
Construct the finest (largest) Grothendieck topology for which all the given presheaves are sheaves.
-/
def finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) : grothendieck_topology C :=
Inf (finest_topology_single '' Ps)

/-- Check that if `P ∈ Ps`, then `P` is indeed a sheaf for the finest topology on `Ps`. -/
lemma sheaf_for_finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) :
  P ∈ Ps → presieve.is_sheaf (finest_topology Ps) P :=
begin
  intros h X S hS,
  simpa using hS _ ⟨⟨_, _, ⟨_, h, rfl⟩, rfl⟩, rfl⟩ _ (𝟙 _),
end

/--
Check that if each `P ∈ Ps` is a sheaf for `J`, then `J` is a subtopology of `finest_topology Ps`.
-/
lemma is_finest_topology (Ps : set (Cᵒᵖ ⥤ Type v)) (J : grothendieck_topology C)
  (hJ : ∀ P ∈ Ps, presieve.is_sheaf J P) : J ≤ finest_topology Ps :=
begin
  intros X S hS,
  rintro _ ⟨⟨_, _, ⟨P, hP, rfl⟩, rfl⟩, rfl⟩,
  intros Y f,
  exact hJ P hP (S.pullback f) (J.pullback_stable f hS),
end

/--
The `canonical_topology` on a category is the finest (largest) topology for which every
representable presheaf is a sheaf.
-/
-- TODO: Show that if `P` is a sheaf for this topology, then `P` is representable
def canonical_topology (C : Type u) [category.{v} C] : grothendieck_topology C :=
finest_topology (set.range yoneda.obj)

/-- `yoneda.obj X` is a sheaf for the canonical topology. -/
lemma yoneda_obj_is_sheaf (X : C) : presieve.is_sheaf (canonical_topology C) (yoneda.obj X) :=
λ Y S hS, sheaf_for_finest_topology _ (set.mem_range_self _) _ hS

/-- A representable functor is a sheaf for the canonical topology. -/
lemma representable_is_sheaf (P : Cᵒᵖ ⥤ Type v) [representable P] :
  presieve.is_sheaf (canonical_topology C) P :=
presieve.is_sheaf_iso (canonical_topology C) representable.w (yoneda_obj_is_sheaf _)

/--
A subcanonical topology is a topology which is smaller than the canonical topology.
Equivalently, a topology is subcanonical iff every representable is a sheaf.
-/
def subcanonical (J : grothendieck_topology C) : Prop :=
J ≤ canonical_topology C

namespace subcanonical

/-- If every functor `yoneda.obj X` is a `J`-sheaf, then `J` is subcanonical. -/
lemma of_yoneda_is_sheaf (J : grothendieck_topology C)
  (h : ∀ X, presieve.is_sheaf J (yoneda.obj X)) :
  subcanonical J :=
begin
  apply is_finest_topology,
  rintro P ⟨X, rfl⟩,
  apply h,
end

/-- If `J` is subcanonical, then any representable is a `J`-sheaf. -/
lemma representable_is_sheaf {J : grothendieck_topology C} (hJ : subcanonical J)
  (P : Cᵒᵖ ⥤ Type v) [representable P] :
  presieve.is_sheaf J P :=
presieve.is_sheaf_for_coarser_topology _ hJ (representable_is_sheaf P)

end subcanonical

end sheaf

end category_theory
