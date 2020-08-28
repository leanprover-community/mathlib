import algebraic_geometry.locally_ringed_space
import algebraic_geometry.Spec

open topological_space
open category_theory

namespace algebraic_geometry

structure Scheme extends X : LocallyRingedSpace :=
(local_affine : ∀ x : carrier, ∃ (U : opens carrier) (m : x ∈ U) (R : CommRing)
  (i : X.to_SheafedSpace.restrict _ _ (opens.inclusion_open_embedding U) ≅ Spec.SheafedSpace R), true)

-- PROJECT
-- In fact, we can construct `Spec.LocallyRingedSpace R`,
-- and the isomorphism `i` above is an isomorphism in `LocallyRingedSpace`.
-- However this is a consequence of the above definition, and not necessary for defining schemes.
-- We haven't done this yet because:
-- 1. We haven't proved that the stalk of the structure sheaf is isomorphic to the localisation
--    **as a ring**, only at the level of `Type`.
--    To do this, we need to know that `forget CommRing` preserves filtered colimits.
-- 2. We haven't shown that you can restrict a `LocallyRingedSpace` along an open embedding.
--    We can do this already for `SheafedSpace` (as above), but we need to know that
--    the stalks of the restriction are still local rings, which we follow if we knew that
--    the stalks didn't change.
--    This will follow if we define cofinal functors, and show precomposing with a cofinal functor
--    doesn't change colimits, because open neighbourhoods of `x` within `U` are cofinal in
--    all open neighbourhoods of `x`.

namespace Scheme

def to_LocallyRingedSpace (S : Scheme) : LocallyRingedSpace := { ..S }

/--
Schemes are a full subcategory of locally ringed spaces.
-/
instance : category Scheme :=
induced_category.category Scheme.to_LocallyRingedSpace

end Scheme

end algebraic_geometry
