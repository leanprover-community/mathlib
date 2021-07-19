/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yourong Zang.
-/
import tactic
import geometry.euclidean.basic
import geometry.manifold.charted_space
import analysis.normed_space.inner_product

/-!
# Conformal Maps on Inner Product Spaces

A map between real inner product spaces `X`, `Y` is `conformal_at` some point `x` in `X` if it is real differentiable
and its differential at that point is a nonzero constant multiple of a linear isometry equivalence.

## Main results

* `conformal_at`: the main defintion
* The conformality of the composition of two conformal maps, the identity map and multiplications by a constant
* `conformal_at_iff`: an equivalent definition of the conformality at some point
* `conformal_at_preserves_angle`: if a map is `conformal_at` some point, then its differential preserves all angles at that point
* `conformal_groupoid`: the groupoid of conformal local homeomorphisms

## Tags

conformal

## Warning

The definition of `conformal_at` in this file does NOT require the maps to be orientation-preserving. Maps such as
the conjugate function on the complex plane is considered as a conformal map in this file.
-/

noncomputable theory

section conformality

/-- A continuous linear map `f'` is said to be conformal if it is a nonzero multiple of a bijective linear isometry. -/
def is_conformal_map {X Y : Type*}
[inner_product_space ℝ X] [inner_product_space ℝ Y] (f' : X →L[ℝ] Y) :=
∃ (c : ℝ) (hc : c ≠ 0) (lie : X ≃ₗᵢ[ℝ] Y), (f' : X → Y) = (λ y, c • y) ∘ lie

/-- A map `f` is said to be conformal if it has a conformal differential `f'`. -/
def conformal_at
{X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y]
(f : X → Y) (x : X) :=
∃ (f' : X →L[ℝ] Y), has_fderiv_at f f' x ∧ is_conformal_map f'


namespace conformal_at

variables {X Y Z : Type*}
  [inner_product_space ℝ X] [inner_product_space ℝ Y] [inner_product_space ℝ Z]

open linear_isometry_equiv continuous_linear_map

theorem differentiable_at {f : X → Y} {x : X} (h : conformal_at f x) :
differentiable_at ℝ f x := let ⟨_, h₁, _, _, _, _⟩ := h in h₁.differentiable_at

theorem id (x : X) : conformal_at id x :=
⟨id ℝ X, has_fderiv_at_id _, 1, one_ne_zero, refl ℝ X, by ext; simp⟩

theorem const_smul {c : ℝ} (h : c ≠ 0) (x : X) : conformal_at (λ (x': X), c • x') x :=
⟨c • continuous_linear_map.id ℝ X, has_fderiv_at.const_smul (has_fderiv_at_id x) c, c, h, refl ℝ X, by ext; simp⟩

theorem comp {f : X → Y} {g : Y → Z} {x : X} :
  conformal_at f x → conformal_at g (f x) → conformal_at (g ∘ f) x :=
begin
  rintro ⟨f', hf₁, cf, hcf, lief, hf₂⟩ ⟨g', hg₁, cg, hcg, lieg, hg₂⟩,
  exact ⟨g'.comp f', has_fderiv_at.comp x hg₁ hf₁, cg * cf, mul_ne_zero hcg hcf, lief.trans lieg,
    by { ext, simp [coe_comp' f' g', hf₂, hg₂, smul_smul cg cf] }⟩,
end

/-- A real differentiable map `f` is conformal at point `x` if and only if 
    its differential `f'` at that point scales any inner product by a positive scalar. -/
theorem _root_.conformal_at_iff {f : X → Y} {x : X} {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) :
conformal_at f x ↔ ∃ (c : ℝ) (hc : c > 0), ∀ (u v : X), inner (f' u) (f' v) = (c : ℝ) * (inner u v) :=
begin
  split,
  { rintros ⟨f₁, h₁, c₁, hc₁, lie, h₂⟩,
    refine ⟨c₁ * c₁, mul_self_pos hc₁, λ u v, _⟩,
    simp [← f'.coe_coe, ← f'.coe_def_rev, has_fderiv_at.unique h h₁, h₂, inner_map_map, real_inner_smul_left,
      real_inner_smul_right, mul_assoc] },
  { rintro ⟨c₁, hc₁, huv⟩,
    let c := real.sqrt c₁⁻¹,
    have hc : c ≠ 0 := λ w, by {simp only [c] at w;
      exact (real.sqrt_ne_zero'.mpr $ inv_pos.mpr hc₁) w},
    let c_map := linear_equiv.smul_of_ne_zero ℝ Y c hc,
    let f₁ := f'.to_linear_equiv.trans c_map,
    have minor : (f₁ : X → Y) = (λ (y : Y), c • y) ∘ f' := rfl,
    have minor' : (f' : X → Y) = (λ (y : Y), c⁻¹ • y) ∘ f₁ := by ext;
      rw [minor, function.comp_apply, function.comp_apply,
          smul_smul, inv_mul_cancel hc, one_smul],
    have key : ∀ (u v : X), inner (f₁ u) (f₁ v) = inner u v := λ u v, by
      rw [minor, function.comp_app, function.comp_app, real_inner_smul_left,
          real_inner_smul_right, huv u v, ← mul_assoc, ← mul_assoc,
          real.mul_self_sqrt $ le_of_lt $ inv_pos.mpr hc₁,
          inv_mul_cancel $ ne_of_gt hc₁, one_mul],
    exact ⟨f'.to_continuous_linear_map, h, c⁻¹, inv_ne_zero hc, f₁.isometry_of_inner key, minor'⟩, },
end

def char_fun_at {f : X → Y} (x : X) {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at f x) : ℝ :=
by choose c hc huv using (conformal_at_iff h).mp H; exact c

/-- If a real differentiable map `f` is conformal at a point `x`, then it preserves the angles at that point. -/
theorem _root_.conformal_at_preserves_angle {f : X → Y} {x : X} {f' : X ≃L[ℝ] Y}
(h : has_fderiv_at f f'.to_continuous_linear_map x) (H : conformal_at f x) (u v : X) :
  inner_product_geometry.angle (f' u) (f' v) = inner_product_geometry.angle u v :=
begin
  repeat { rw inner_product_geometry.angle },
  suffices new : inner (f' u) (f' v) / (∥f' u∥ * ∥f' v∥) = inner u v / (∥u∥ * ∥v∥),
  { rw new, },
  { rcases H with ⟨f₁, h₁, c₁, hc₁, lie, h₂⟩,
    have minor : ∥c₁∥ ≠ 0 := λ w, hc₁ (norm_eq_zero.mp w),
    have : f'.to_continuous_linear_map = f₁ := has_fderiv_at.unique h h₁,
    rw [← continuous_linear_equiv.coe_coe f', ← continuous_linear_equiv.coe_def_rev f'],
    repeat { rw inner_product_angle.def },
    rw [this, h₂],
    repeat { rw function.comp_apply },
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, linear_isometry_equiv.inner_map_map],
    repeat { rw [norm_smul, linear_isometry_equiv.norm_map] },
    rw [← mul_assoc],
    exact calc c₁ * c₁ * inner u v / (∥c₁∥ * ∥u∥ * ∥c₁∥ * ∥v∥)
            = c₁ * c₁ * inner u v / (∥c₁∥ * ∥c₁∥ * ∥u∥ * ∥v∥) : by simp only [mul_comm, mul_assoc]
        ... = c₁ * c₁ * inner u v / (abs c₁ * abs c₁ * ∥u∥ * ∥v∥) : by rw [real.norm_eq_abs]
        ... = c₁ * c₁ * inner u v / (c₁ * c₁ * ∥u∥ * ∥v∥) : by rw [← pow_two, ← sq_abs, pow_two]
        ... = c₁ * (c₁ * inner u v) / (c₁ * (c₁ * (∥u∥ * ∥v∥))) : by simp only [mul_assoc]
        ... = (c₁ * inner u v) / (c₁ * (∥u∥ * ∥v∥)) : by rw mul_div_mul_left _ _ hc₁
        ... = inner u v / (∥u∥ * ∥v∥) : by rw mul_div_mul_left _ _ hc₁, },
end

end conformal_at


/-- A map `f` is conformal on a set `s` if it's conformal at every point in that set. -/
def conformal_on {X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y] 
(f : X → Y) (s : set X) := ∀ (x : X), x ∈ s → conformal_at f x

namespace conformal_on

variables {X Y Z: Type*} 
  [inner_product_space ℝ X] [inner_product_space ℝ Y] [inner_product_space ℝ Z]

theorem conformal_at {f : X → Y} {u : set X} (h : conformal_on f u) {x : X} (hx : x ∈ u) :
conformal_at f x := h x hx

theorem comp {f : X → Y} {g : Y → Z}
{u : set X} {v : set Y} (hf : conformal_on f u) (hg : conformal_on g v) :
conformal_on (g ∘ f) (u ∩ f⁻¹' v) := λ x hx, (hf x hx.1).comp (hg (f x) $ set.mem_preimage.mp hx.2)

theorem congr {f : X → X} {g : X → X}
{u : set X} (hu : is_open u) (h : ∀ (x : X), x ∈ u → g x = f x) (hf : conformal_on f u) :
conformal_on g u := λ x hx, let ⟨f', h₁, c, hc, lie, h₂⟩ := hf x hx in
begin
  have : has_fderiv_at g f' x :=
    by apply h₁.congr_of_eventually_eq; rw filter.eventually_eq_iff_exists_mem; exact ⟨u, hu.mem_nhds hx, h⟩,
  exact ⟨f', this, c, hc, lie, h₂⟩,
end

end conformal_on

/-- A map `f` is conformal if it's conformal at every point. -/
def conformal
{X Y : Type*} [inner_product_space ℝ X] [inner_product_space ℝ Y]
(f : X → Y) := ∀ (x : X), conformal_at f x

namespace conformal

variables {X Y Z : Type*} 
  [inner_product_space ℝ X] [inner_product_space ℝ Y] [inner_product_space ℝ Z]

theorem conformal_at {f : X → Y} (h : conformal f) (x : X) :
conformal_at f x := h x

theorem conformal_on {f : X → Y} (h : conformal f) :
conformal_on f set.univ := λ x hx, h x

theorem differentiable {f : X → Y} (h : conformal f) :
differentiable ℝ f := λ x, (h x).differentiable_at

theorem id : conformal (id : X → X) := λ x, conformal_at.id x

theorem const_smul {c : ℝ} (h : c ≠ 0) :
conformal (λ (x : X), c • x) := λ x, conformal_at.const_smul h x

theorem comp {f : X → Y} {g : Y → Z} (hf : conformal f) (hg : conformal g) :
conformal (g ∘ f) := λ x, conformal_at.comp (hf x) (hg (f x))

end conformal

variables {X : Type*} [inner_product_space ℝ X]

def conformal_pregroupoid : pregroupoid X :=
{ property := λ f u, conformal_on f u,
  comp := λ f g u v hf hg hu hv huv, hf.comp hg,
  id_mem := conformal.conformal_on conformal.id,
  locality := λ f u hu h x hx, let ⟨v, h₁, h₂, h₃⟩ := h x hx in h₃ x ⟨hx, h₂⟩,
  congr := λ f g u hu h hf, conformal_on.congr hu h hf, }

def conformal_groupoid : structure_groupoid X := conformal_pregroupoid.groupoid

end conformality