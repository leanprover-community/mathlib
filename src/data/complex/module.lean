/-
Copyright (c) 2020 Alexander Bentkamp, Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Sébastien Gouëzel
-/
import data.complex.basic
import algebra.algebra.ordered
import data.matrix.notation
import field_theory.tower
import linear_algebra.finite_dimensional

/-!
# Complex number as a vector space over `ℝ`

This file contains the following instances:
* Any `•`-structure (`has_scalar`, `mul_action`, `distrib_mul_action`, `semimodule`, `algebra`) on
  `ℝ` imbues a corresponding structure on `ℂ`. This includes the statement that `ℂ` is an `ℝ`
  algebra.
* any complex vector space is a real vector space;
* any finite dimensional complex vector space is a finite dimensional real vector space;
* the space of `ℝ`-linear maps from a real vector space to a complex vector space is a complex
  vector space.

It also defines three linear maps:

* `complex.linear_map.re`;
* `complex.linear_map.im`;
* `complex.linear_map.of_real`.

They are bundled versions of the real part, the imaginary part, and the embedding of `ℝ` in `ℂ`,
as `ℝ`-linear maps.
-/
noncomputable theory

namespace complex

variables {R : Type*} {S : Type*}

section

variables [has_scalar R ℝ]

instance : has_scalar R ℂ :=
{ smul := λ r x, ⟨r • x.re, r • x.im⟩ }

lemma smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := rfl
lemma smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := rfl

@[simp] lemma smul_coe {x : ℝ} {z : ℂ} : x • z = x * z :=
by ext; simp [smul_re, smul_im]

end

instance [has_scalar R ℝ] [has_scalar S ℝ] [smul_comm_class R S ℝ] : smul_comm_class R S ℂ :=
{ smul_comm := λ r s x, ext (smul_comm _ _ _) (smul_comm _ _ _) }

instance [has_scalar R S] [has_scalar R ℝ] [has_scalar S ℝ] [is_scalar_tower R S ℝ] :
  is_scalar_tower R S ℂ :=
{ smul_assoc := λ r s x, ext (smul_assoc _ _ _) (smul_assoc _ _ _) }

instance [monoid R] [mul_action R ℝ] : mul_action R ℂ :=
{ one_smul := λ x, ext (one_smul _ _) (one_smul _ _),
  mul_smul := λ r s x, ext (mul_smul _ _ _) (mul_smul _ _ _) }

instance [semiring R] [distrib_mul_action R ℝ] : distrib_mul_action R ℂ :=
{ smul_add := λ r x y, ext (smul_add _ _ _) (smul_add _ _ _),
  smul_zero := λ r, ext (smul_zero _) (smul_zero _) }

instance [semiring R] [semimodule R ℝ] : semimodule R ℂ :=
{ add_smul := λ r s x, ext (add_smul _ _ _) (add_smul _ _ _),
  zero_smul := λ r, ext (zero_smul _ _) (zero_smul _ _) }

instance [comm_semiring R] [algebra R ℝ] : algebra R ℂ :=
{ smul := (•),
  smul_def' := λ r x, by ext; simp [smul_re, smul_im, algebra.smul_def],
  commutes' := λ r ⟨xr, xi⟩, by ext; simp [smul_re, smul_im, algebra.commutes],
  ..complex.of_real.comp (algebra_map R ℝ) }

section
open_locale complex_order

lemma complex_ordered_semimodule : ordered_semimodule ℝ ℂ :=
{ smul_lt_smul_of_pos := λ z w x h₁ h₂,
  begin
    obtain ⟨y, l, rfl⟩ := lt_def.mp h₁,
    refine lt_def.mpr ⟨x * y, _, _⟩,
    exact mul_pos h₂ l,
    ext; simp [mul_add],
  end,
  lt_of_smul_lt_smul_of_pos := λ z w x h₁ h₂,
  begin
    obtain ⟨y, l, e⟩ := lt_def.mp h₁,
    by_cases h : x = 0,
    { subst h, exfalso, apply lt_irrefl 0 h₂, },
    { refine lt_def.mpr ⟨y / x, div_pos l h₂, _⟩,
      replace e := congr_arg (λ z, (x⁻¹ : ℂ) * z) e,
      simp only [mul_add, ←mul_assoc, h, one_mul, of_real_eq_zero, smul_coe, ne.def,
        not_false_iff, inv_mul_cancel] at e,
      convert e,
      simp only [div_eq_iff_mul_eq, h, of_real_eq_zero, of_real_div, ne.def, not_false_iff],
      norm_cast,
      simp [mul_comm _ y, mul_assoc, h],
    },
  end }

localized "attribute [instance] complex_ordered_semimodule" in complex_order

end


@[simp] lemma coe_algebra_map : ⇑(algebra_map ℝ ℂ) = complex.of_real := rfl

open submodule finite_dimensional

lemma is_basis_one_I : is_basis ℝ ![1, I] :=
begin
  refine ⟨linear_independent_fin2.2 ⟨I_ne_zero, λ a, mt (congr_arg re) $ by simp⟩,
    eq_top_iff'.2 $ λ z, _⟩,
  suffices : ∃ a b : ℝ, z = a • I + b • 1,
    by simpa [mem_span_insert, mem_span_singleton, -set.singleton_one],
  use [z.im, z.re],
  simp [algebra.smul_def, add_comm]
end

instance : finite_dimensional ℝ ℂ := of_fintype_basis is_basis_one_I

@[simp] lemma findim_real_complex : finite_dimensional.findim ℝ ℂ = 2 :=
by rw [findim_eq_card_basis is_basis_one_I, fintype.card_fin]

@[simp] lemma dim_real_complex : vector_space.dim ℝ ℂ = 2 :=
by simp [← findim_eq_dim, findim_real_complex]

lemma {u} dim_real_complex' : cardinal.lift.{0 u} (vector_space.dim ℝ ℂ) = 2 :=
by simp [← findim_eq_dim, findim_real_complex, bit0]

end complex

/- Register as an instance (with low priority) the fact that a complex vector space is also a real
vector space. -/
@[priority 900]
instance module.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E] : module ℝ E :=
restrict_scalars.semimodule ℝ ℂ E

instance module.real_complex_tower (E : Type*) [add_comm_group E] [module ℂ E] :
  is_scalar_tower ℝ ℂ E :=
restrict_scalars.is_scalar_tower ℝ ℂ E

@[priority 100]
instance finite_dimensional.complex_to_real (E : Type*) [add_comm_group E] [module ℂ E]
  [finite_dimensional ℂ E] : finite_dimensional ℝ E :=
finite_dimensional.trans ℝ ℂ E

lemma dim_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  vector_space.dim ℝ E = 2 * vector_space.dim ℂ E :=
cardinal.lift_inj.1 $
  by { rw [← dim_mul_dim' ℝ ℂ E, complex.dim_real_complex], simp [bit0] }

lemma findim_real_of_complex (E : Type*) [add_comm_group E] [module ℂ E] :
  finite_dimensional.findim ℝ E = 2 * finite_dimensional.findim ℂ E :=
by rw [← finite_dimensional.findim_mul_findim ℝ ℂ E, complex.findim_real_complex]

namespace complex

/-- Linear map version of the real part function, from `ℂ` to `ℝ`. -/
def linear_map.re : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.re,
  map_add' := add_re,
  map_smul' := by simp, }

@[simp] lemma linear_map.coe_re : ⇑linear_map.re = re := rfl

/-- Linear map version of the imaginary part function, from `ℂ` to `ℝ`. -/
def linear_map.im : ℂ →ₗ[ℝ] ℝ :=
{ to_fun := λx, x.im,
  map_add' := add_im,
  map_smul' := by simp, }

@[simp] lemma linear_map.coe_im : ⇑linear_map.im = im := rfl

/-- Linear map version of the canonical embedding of `ℝ` in `ℂ`. -/
def linear_map.of_real : ℝ →ₗ[ℝ] ℂ :=
{ to_fun := coe,
  map_add' := of_real_add,
  map_smul' := λc x, by simp [algebra.smul_def] }

@[simp] lemma linear_map.coe_of_real : ⇑linear_map.of_real = coe := rfl

/-- `ℝ`-linear map version of the complex conjugation function from `ℂ` to `ℂ`. -/
def linear_map.conj : ℂ →ₗ[ℝ] ℂ :=
{ map_smul' := by simp [restrict_scalars_smul_def],
  ..conj }

@[simp] lemma linear_map.coe_conj : ⇑linear_map.conj = conj := rfl

end complex
