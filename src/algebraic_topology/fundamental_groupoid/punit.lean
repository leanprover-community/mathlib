/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import algebraic_topology.fundamental_groupoid.induced_maps
import category_theory.punit

/-!
# Fundamental groupoid of punit

The fundamental groupoid of punit is naturally isomorphic to `category_theory.discrete punit`
-/

noncomputable theory

open category_theory

namespace path

instance : subsingleton (path punit.star punit.star) := ⟨λ x y, by ext⟩

end path

namespace fundamental_groupoid

instance {x y : fundamental_groupoid punit} : subsingleton (x ⟶ y) :=
begin
  convert_to subsingleton (path.homotopic.quotient punit.star punit.star),
  { congr; apply punit_eq_star, },
  apply quotient.subsingleton,
end

/-- Equivalence of groupoids between fundamental groupoid of punit and punit -/
def fundamental_groupoid_punit_iso_punit : fundamental_groupoid punit ≌ discrete punit :=
equivalence.mk (functor.star _) ((category_theory.functor.const _).obj punit.star)
  (nat_iso.of_components (λ _, eq_to_iso dec_trivial) (λ _ _ _, dec_trivial))
  (functor.punit_ext _ _)

end fundamental_groupoid
