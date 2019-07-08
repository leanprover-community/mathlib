import category_theory.category category_theory.isomorphism category_theory.groupoid
import algebra.group.units data.equiv.algebra

universes v u

namespace category_theory

/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with `function.comp`, not with `category.comp`. -/
def End {C : Type u} [𝒞_struct : category_struct.{v+1} C] (X : C) := X ⟶ X

namespace End

section struct

variables {C : Type u} [𝒞_struct : category_struct.{v+1} C] (X : C)
include 𝒞_struct

instance has_one : has_one (End X) := ⟨𝟙 X⟩

/-- Multiplication of endomorphisms agrees with `function.comp`, not `category_struct.comp`. -/
instance has_mul : has_mul (End X) := ⟨λ x y, y ≫ x⟩

variable {X}

@[simp] lemma one_def : (1 : End X) = 𝟙 X := rfl

@[simp] lemma mul_def (xs ys : End X) : xs * ys = ys ≫ xs := rfl

end struct

/-- Endomorphisms of an object form a monoid -/
instance monoid {C : Type u} [category.{v+1} C] {X : C} : monoid (End X) :=
{ mul_one := category.id_comp C,
  one_mul := category.comp_id C,
  mul_assoc := λ x y z, (category.assoc C z y x).symm,
  ..End.has_mul X, ..End.has_one X }

/-- In a groupoid, endomorphisms form a group -/
instance group {C : Type u} [groupoid.{v+1} C] (X : C) : group (End X) :=
{ mul_left_inv := groupoid.comp_inv C, inv := groupoid.inv, ..End.monoid }

end End

def Aut {C : Type u} [𝒞 : category.{v+1} C] (X : C) := X ≅ X

attribute [extensionality Aut] iso.ext

namespace Aut

variables {C : Type u} [𝒞 : category.{v+1} C] (X : C)
include 𝒞

instance: group (Aut X) :=
by refine { one := iso.refl X,
            inv := iso.symm,
            mul := flip iso.trans, .. } ; dunfold flip; obviously

def units_End_eqv_Aut : (units (End X)) ≃* Aut X :=
{ to_fun := λ f, ⟨f.1, f.2, f.4, f.3⟩,
  inv_fun := λ f, ⟨f.1, f.2, f.4, f.3⟩,
  left_inv := λ ⟨f₁, f₂, f₃, f₄⟩, rfl,
  right_inv := λ ⟨f₁, f₂, f₃, f₄⟩, rfl,
  hom := ⟨λ f g, by rcases f; rcases g; refl⟩ }

end Aut

end category_theory
