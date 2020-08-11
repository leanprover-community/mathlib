/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Module.kernels
import algebra.category.Module.limits
import category_theory.abelian.basic

/-!
# The category of left R-modules is abelian.
-/

open category_theory
open category_theory.limits

noncomputable theory

universe u

namespace Module
variables {R : Type u} [ring R] {M N : Module R} (f : M ⟶ N)

/-- In the category of modules, every monomorphism is normal. -/
def normal_mono (hf : mono f) : normal_mono f :=
{ Z := of R f.range.quotient,
  g := f.range.mkq,
  w := linear_map.range_mkq_comp _,
  is_limit :=
    is_kernel.iso_kernel _ _ (kernel_is_limit _)
      /- The following [invalid Lean code](https://github.com/leanprover-community/lean/issues/341)
        might help you understand what's going on here:
        ```
        calc
        M   ≃ₗ[R] f.ker.quotient  : (submodule.quot_equiv_of_eq_bot _ (ker_eq_bot_of_mono _)).symm
        ... ≃ₗ[R] f.range         : linear_map.quot_ker_equiv_range f
        ... ≃ₗ[R] r.range.mkq.ker : linear_equiv.of_eq _ _ (submodule.ker_mkq _).symm
        ```
      -/
      (linear_equiv.to_Module_iso'
        (linear_equiv.trans (submodule.quot_equiv_of_eq_bot _ (ker_eq_bot_of_mono _)).symm
          (linear_equiv.trans (linear_map.quot_ker_equiv_range f)
            (linear_equiv.of_eq _ _ (submodule.ker_mkq _).symm)))) $
      by { ext, refl } }

/-- In the category of modules, every epimorphism is normal. -/
def normal_epi (hf : epi f) : normal_epi f :=
{ W := of R f.ker,
  g := f.ker.subtype,
  w := linear_map.comp_ker_subtype _,
  is_colimit :=
    is_cokernel.cokernel_iso _ _ (cokernel_is_colimit _)
      (linear_equiv.to_Module_iso'
      /- The following invalid Lean code might help you understand what's going on here:
        ```
        calc f.ker.subtype.range.quotient
            ≃ₗ[R] f.ker.quotient : submodule.quot_equiv_of_eq _ _ (submodule.range_subtype _)
        ... ≃ₗ[R] f.range        : linear_map.quot_ker_equiv_range f
        ... ≃ₗ[R] N              : linear_equiv.of_top _ (range_eq_top_of_epi _)
        ```
      -/
        (linear_equiv.trans
          (linear_equiv.trans (submodule.quot_equiv_of_eq _ _ (submodule.range_subtype _))
            (linear_map.quot_ker_equiv_range f)) (linear_equiv.of_top _ (range_eq_top_of_epi _)))) $
      by { ext, refl } }

/-- The category of R-modules is abelian. -/
instance : abelian (Module R) :=
{ has_finite_products := by { dsimp [has_finite_products], apply_instance },
  has_kernels := by apply_instance,
  has_cokernels := has_cokernels_Module,
  normal_mono := λ X Y, normal_mono,
  normal_epi := λ X Y, normal_epi }

end Module
