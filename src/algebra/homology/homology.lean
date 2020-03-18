import algebra.homology.chain_complex
import category_theory.limits.shapes.images
import category_theory.limits.shapes.kernels

universes v u

namespace chain_complex

open category_theory
open category_theory.limits

variables {V : Type u} [𝒱 : category.{v} V] [has_zero_morphisms.{v} V]
include 𝒱

section
variable [has_kernels.{v} V]
/-- The map induceed by a chain map between the kernels of the differentials. -/
def induced_map_on_cycles {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
  kernel (C.d i) ⟶ kernel (C'.d i) :=
kernel.lift _ (kernel.ι _ ≫ f.f i)
begin
  rw [category.assoc, f.comm_at, ←category.assoc, kernel.condition, has_zero_morphisms.zero_comp],
end
end

/-!
At this point we assume that we have all images, and all equalizers.
We need to assume all equalizers, not just kernels, so that
`factor_thru_image` is an epimorphism.
-/
variables [has_images.{v} V] [has_equalizers.{v} V]

/-- The connecting morphism from the image of `d i` to the kernel of `d (i+1)`. -/
def image_to_kernel_map (C : chain_complex.{v} V) (i : ℤ) :
  image (C.d i) ⟶ kernel (C.d (i+1)) :=
kernel.lift _ (image.ι (C.d i))
begin
  apply @epi.left_cancellation _ _ _ _ (factor_thru_image (C.d i)) _ _ _ _ _,
  simp,
  refl,
end

-- PROJECT:
-- At this level of generality, it's just not true that a chain map
-- induces maps on boundaries
--
-- Let's add these later, with appropriate (but hopefully fairly minimal)
-- assumptions: perhaps that the category is regular?
-- I think in that case we can compute `image` as the regular coimage,
-- i.e. the coequalizer of the kernel pair,
-- and that image has the appropriate mapping property.

-- def induced_map_on_boundaries {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
--   image (C.d i) ⟶ image (C'.d i) :=
-- sorry

-- I'm not certain what the minimal assumptions required to prove the following
-- lemma are:

-- lemma induced_maps_commute {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
-- image_to_kernel_map C i ≫ induced_map_on_cycles f (i+1) =
--   induced_map_on_boundaries f i ≫ image_to_kernel_map C' i :=
-- sorry

variables [has_cokernels.{v} V]

/-- The `i`-th homology group of the chain complex `C`. -/
def homology_group (C : chain_complex.{v} V) (i : ℤ) : V :=
cokernel (image_to_kernel_map C i)

-- PROJECT:

-- As noted above, as we don't get induced maps on boundaries with this generality,
-- we can't assemble the homology groups into a functor. Hopefully, however,
-- the commented out code below will work
-- (with whatever added assumptions are needed above.)

-- def induced_map_on_homology {C C' : chain_complex.{v} V} (f : C ⟶ C') (i : ℤ) :
--   C.homology_group i ⟶ C'.homology_group i :=
-- cokernel.desc _ (induced_map_on_cycles f (i+1) ≫ cokernel.π _)
-- begin
--   rw [←category.assoc, induced_maps_commute, category.assoc, cokernel.condition],
--   erw [has_zero_morphisms.comp_zero],
-- end

-- /-- The homology functor from chain complexes to `ℤ` graded objects in `V`. -/
-- def homology : chain_complex.{v} V ⥤ graded_object ℤ V :=
-- { obj := λ C i, homology_group C i,
--   map := λ C C' f i, induced_map_on_homology f i,
--   map_id' := sorry,
--   map_comp' := sorry, }

end chain_complex
