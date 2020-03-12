/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.equalizers

/-!
# Kernels and cokernels

In a category with zero morphisms, the kernel of a morphism `f : X ⟶ Y` is just the equalizer of `f`
and `0 : X ⟶ Y`. (Similarly the cokernel is the coequalizer.)

We don't yet prove much here, just provide
* `kernel : (X ⟶ Y) → C`
* `kernel.ι : kernel f ⟶ X`
* `kernel.condition : kernel.ι f ≫ f = 0` and
* `kernel.lift (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f` (as well as the dual versions)

## Main statements

Besides the definition and lifts,
* `kernel.ι_zero_is_iso`: a kernel map of a zero morphism is an isomorphism
* `kernel.is_limit_cone_zero_cone`: if our category has a zero object, then the map from the zero
  obect is a kernel map of any monomorphism

## Future work
* TODO: images and coimages, and then abelian categories.
* TODO: connect this with existing working in the group theory and ring theory libraries.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

universes v u

open category_theory
open category_theory.limits.walking_parallel_pair

namespace category_theory.limits

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables {X Y : C} (f : X ⟶ Y)

section
variables [has_zero_morphisms.{v} C] [has_limit (parallel_pair f 0)]

/-- The kernel of a morphism, expressed as the equalizer with the 0 morphism. -/
abbreviation kernel : C := equalizer f 0

/-- The map from `kernel f` into the source of `f`. -/
abbreviation kernel.ι : kernel f ⟶ X := equalizer.ι f 0

@[simp, reassoc] lemma kernel.condition : kernel.ι f ≫ f = 0 :=
by simp [equalizer.condition]

/-- Given any morphism `k` so `k ≫ f = 0`, `k` factors through `kernel f`. -/
abbreviation kernel.lift {W : C} (k : W ⟶ X) (h : k ≫ f = 0) : W ⟶ kernel f :=
limit.lift (parallel_pair f 0) (fork.of_ι k (by simpa))

/-- Every kernel of the zero morphism is an isomorphism -/
def kernel.ι_zero_is_iso [has_limit (parallel_pair (0 : X ⟶ Y) 0)] :
  is_iso (kernel.ι (0 : X ⟶ Y)) :=
by { apply limit_cone_parallel_pair_self_is_iso, apply limit.is_limit }

end

section has_zero_object
variables [has_zero_object.{v} C]

local attribute [instance] zero_of_zero_object
local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

/-- The morphism from the zero object determines a cone on a kernel diagram -/
def kernel.zero_cone : cone (parallel_pair f 0) :=
{ X := 0,
  π := { app := λ j, 0 }}

/-- The map from the zero object is a kernel of a monomorphism -/
def kernel.is_limit_cone_zero_cone [mono f] : is_limit (kernel.zero_cone f) :=
{ lift := λ s, 0,
  fac' := λ s j,
  begin
    cases j,
    { erw has_zero_morphisms.zero_comp,
      convert (@zero_of_comp_mono _ _ _ _ _ _ _ f _ _).symm,
      erw fork.condition,
      convert has_zero_morphisms.comp_zero.{v} _ (s.π.app zero) _ },
    { rw ←cone_parallel_pair_right s,
      simp only [has_zero_morphisms.zero_comp],
      convert (has_zero_morphisms.comp_zero.{v} _ (s.π.app zero) _).symm },
  end,
  uniq' := λ _ m _, has_zero_object.zero_of_to_zero m }

/-- The kernel of a monomorphism is isomorphic to the zero object -/
def kernel.of_mono [has_limit (parallel_pair f 0)] [mono f] : kernel f ≅ 0 :=
functor.map_iso (cones.forget _) $ is_limit.unique_up_to_iso
  (limit.is_limit (parallel_pair f 0)) (kernel.is_limit_cone_zero_cone f)

/-- The kernel morphism of a monomorphism is a zero morphism -/
lemma kernel.ι_of_mono [has_limit (parallel_pair f 0)] [mono f] : kernel.ι f = 0 :=
by rw [←category.id_comp _ (kernel.ι f), ←iso.hom_inv_id (kernel.of_mono f), category.assoc,
  has_zero_object.zero_of_to_zero (kernel.of_mono f).hom, has_zero_morphisms.zero_comp]

section
variables (X) (Y)

/-- The kernel morphism of a zero morphism is an isomorphism -/
def kernel.ι_of_zero [has_limit (parallel_pair (0 : X ⟶ Y) 0)] : is_iso (kernel.ι (0 : X ⟶ Y)) :=
equalizer.ι_of_self _

end

end has_zero_object

section
variables [has_zero_morphisms.{v} C] [has_colimit (parallel_pair f 0)]

/-- The cokernel of a morphism, expressed as the coequalizer with the 0 morphism. -/
abbreviation cokernel : C := coequalizer f 0

/-- The map from the target of `f` to `cokernel f`. -/
abbreviation cokernel.π : Y ⟶ cokernel f := coequalizer.π f 0

@[simp, reassoc] lemma cokernel.condition : f ≫ cokernel.π f = 0 :=
by simp [coequalizer.condition]

/-- Given any morphism `k` so `f ≫ k = 0`, `k` factors through `cokernel f`. -/
abbreviation cokernel.desc {W : C} (k : Y ⟶ W) (h : f ≫ k = 0) : cokernel f ⟶ W :=
colimit.desc (parallel_pair f 0) (cofork.of_π k (by simpa))
end

section has_zero_object
variables [has_zero_object.{v} C]

local attribute [instance] zero_of_zero_object
local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

/-- The morphism to the zero object determines a cocone on a cokernel diagram -/
def cokernel.zero_cocone : cocone (parallel_pair f 0) :=
{ X := 0,
  ι := { app := λ j, 0 } }

/-- The morphism to the zero object is a cokernel of an epimorphism -/
def cokernel.is_colimit_cocone_zero_cocone [epi f] : is_colimit (cokernel.zero_cocone f) :=
{ desc := λ s, 0,
  fac' := λ s j,
  begin
    cases j,
    { erw [←cocone_parallel_pair_left s,
        has_zero_morphisms.comp_zero _ ((cokernel.zero_cocone f).ι.app zero) _, cofork.condition,
        has_zero_morphisms.zero_comp],
      refl },
    { erw has_zero_morphisms.zero_comp,
      convert (@zero_of_comp_epi _ _ _ _ _ _ f _ _ _).symm,
      erw [cofork.condition, has_zero_morphisms.zero_comp],
      refl },
  end,
  uniq' := λ _ m _, has_zero_object.zero_of_from_zero m }

/-- The cokernel of an epimorphism is isomorphic to the zero object -/
def cokernel.of_epi [has_colimit (parallel_pair f 0)] [epi f] : cokernel f ≅ 0 :=
functor.map_iso (cocones.forget _) $ is_colimit.unique_up_to_iso
  (colimit.is_colimit (parallel_pair f 0)) (cokernel.is_colimit_cocone_zero_cocone f)

/-- The cokernel morphism if an epimorphism is a zero morphism -/
lemma cokernel.π_of_epi [has_colimit (parallel_pair f 0)] [epi f] : cokernel.π f = 0 :=
by rw [←category.comp_id _ (cokernel.π f), ←iso.hom_inv_id (cokernel.of_epi f), ←category.assoc,
  has_zero_object.zero_of_from_zero (cokernel.of_epi f).inv, has_zero_morphisms.comp_zero]

section
variables (X) (Y)

/-- The cokernel of a zero morphism is an isomorphism -/
def cokernel.π_of_zero [has_colimit (parallel_pair (0 : X ⟶ Y) 0)] :
  is_iso (cokernel.π (0 : X ⟶ Y)) :=
coequalizer.π_of_self _

end

end has_zero_object

section has_zero_object
variables [has_zero_object.{v} C]

local attribute [instance] zero_of_zero_object
local attribute [instance] has_zero_object.zero_morphisms_of_zero_object

/-- The kernel of the cokernel of an epimorphism is an isomorphism -/
instance kernel.of_cokernel_of_epi [has_colimit (parallel_pair f 0)]
  [has_limit (parallel_pair (cokernel.π f) 0)] [epi f] : is_iso (kernel.ι (cokernel.π f)) :=
equalizer.ι_of_self' _ _ $ cokernel.π_of_epi f

/-- The cokernel of the kernel of a monomorphism is an isomorphism -/
instance cokernel.of_kernel_of_mono [has_limit (parallel_pair f 0)]
  [has_colimit (parallel_pair (kernel.ι f) 0)] [mono f] : is_iso (cokernel.π (kernel.ι f)) :=
coequalizer.π_of_self' _ _ $ kernel.ι_of_mono f

end has_zero_object

end category_theory.limits
namespace category_theory.limits
variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

variables [has_zero_morphisms.{v} C]

/-- `has_kernels` represents a choice of kernel for every morphism -/
class has_kernels :=
(has_limit : Π {X Y : C} (f : X ⟶ Y), has_limit (parallel_pair f 0))

/-- `has_cokernels` represents a choice of cokernel for every morphism -/
class has_cokernels :=
(has_colimit : Π {X Y : C} (f : X ⟶ Y), has_colimit (parallel_pair f 0))

attribute [instance] has_kernels.has_limit has_cokernels.has_colimit

/-- Kernels are finite limits, so if `C` has all finite limits, it also has all kernels -/
def has_kernels_of_has_finite_limits [has_finite_limits.{v} C] : has_kernels.{v} C :=
{ has_limit := infer_instance }

/-- Cokernels are finite limits, so if `C` has all finite colimits, it also has all cokernels -/
def has_cokernels_of_has_finite_colimits [has_finite_colimits.{v} C] : has_cokernels.{v} C :=
{ has_colimit := infer_instance }

end category_theory.limits
