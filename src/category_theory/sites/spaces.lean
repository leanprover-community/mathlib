import topology.opens
import category_theory.sites.grothendieck
import category_theory.sites.pretopology
import category_theory.limits.lattice

universe u

variables (T : Type u) [topological_space T]

namespace category_theory
open topological_space limits

/-- The Grothendieck topology associated to a topological space. -/
def associated : grothendieck_topology (opens T) :=
{ sieves := λ X S, ∀ x ∈ X, ∃ U (f : U ⟶ X), S f ∧ x ∈ U,
  top_mem' := λ X x hx, ⟨_, 𝟙 _, trivial, hx⟩,
  pullback_stable' := λ X Y S f hf y hy,
  begin
    rcases hf y (le_of_hom f hy) with ⟨U, g, hg, hU⟩,
    refine ⟨U ⊓ Y, hom_of_le inf_le_right, _, hU, hy⟩,
    apply S.downward_closed hg (hom_of_le inf_le_left),
  end,
  transitive' := λ X S hS R hR x hx,
  begin
    rcases hS x hx with ⟨U, f, hf, hU⟩,
    rcases hR hf _ hU with ⟨V, g, hg, hV⟩,
    exact ⟨_, g ≫ f, hg, hV⟩,
  end }

/-- The Grothendieck pretopology associated to a topological space. -/
def associated_p : pretopology (opens T) :=
{ coverings := λ X R, ∀ x ∈ X, ∃ U (f : U ⟶ X), R f ∧ x ∈ U,
  has_isos := λ X Y f i x hx,
        by exactI ⟨_, _, arrows_with_codomain.singleton_arrow_self _, le_of_hom (inv f) hx⟩,
  pullbacks := λ X Y f S hS x hx,
  begin
    rcases hS _ (le_of_hom f hx) with ⟨U, g, hg, hU⟩,
    refine ⟨_, _, ⟨_, _, hg, rfl, rfl⟩, _⟩,
    have : U ⊓ Y ≤ pullback g f,
      refine le_of_hom (pullback.lift (hom_of_le inf_le_left) (hom_of_le inf_le_right) rfl),
    apply this ⟨hU, hx⟩,
  end,
  transitive := λ X S Ti hS hTi x hx,
  begin
    rcases hS x hx with ⟨U, f, hf, hU⟩,
    rcases hTi f hf x hU with ⟨V, g, hg, hV⟩,
    exact ⟨_, _, ⟨_, g, f, hf, hg, rfl⟩, hV⟩,
  end }

/--
The pretopology associated to a space induces the Grothdendieck topology associated to the space.
-/
lemma same_topology : pretopology.to_grothendieck _ (associated_p T) = associated T :=
begin
  apply le_antisymm,
  { rintro X S ⟨R, hR, RS⟩ x hx,
    rcases hR x hx with ⟨U, f, hf, hU⟩,
    exact ⟨_, f, RS _ hf, hU⟩ },
  { intros X S hS,
    exact ⟨S, hS, le_refl _⟩ }
end

end category_theory
