/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel
-/

import topology.topological_fiber_bundle
import topology.algebra.module
import topology.continuous_function.algebra
import linear_algebra.dual
import topology.continuous_function.continuous_section


/-!
# Topological vector bundles

In this file we define topological vector bundles.

Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a topological vector bundle structure on `bundle.total_space E`,
one should addtionally have the following data:

* `F` should be a topological space and a module over a semiring `R`;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `R`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* The most important condition: around each point, there should be a bundle trivialization which
is a continuous linear equiv in the fibers.

If all these conditions are satisfied, we register the typeclass
`topological_vector_bundle R F E`. We emphasize that the data is provided by other classes, and
that the `topological_vector_bundle` class is `Prop`-valued.

The point of this formalism is that it is unbundled in the sense that the total space of the bundle
is a type with a topology, with which one can work or put further structure, and still one can
perform operations on topological vector bundles (which are yet to be formalized). For instance,
assume that `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `R`
with fiber models `F₁` and `F₂` which are normed spaces. Then one can construct the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber `E x := (E₁ x →L[R] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[R] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces). Let
`vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂ (x : B)` be a type synonym for `E₁ x →L[R] E₂ x`.
Then one can endow
`bundle.total_space (vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂)`
with a topology and a topological vector bundle structure.

Similar constructions can be done for tensor products of topological vector bundles, exterior
algebras, and so on, where the topology can be defined using a norm on the fiber model if this
helps.
-/

noncomputable theory

open bundle set

variables (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
  [topological_space F] [topological_space (total_space E)] [topological_space B]
section

variables [semiring R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [add_comm_monoid F] [module R F]

section

/-- Local trivialization for vector bundles. -/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.trivialization extends bundle_trivialization F (proj E) :=
(linear : ∀ x ∈ base_set, is_linear_map R (λ y : (E x), (to_fun y).2))

instance : has_coe_to_fun (topological_vector_bundle.trivialization R F E) :=
⟨λ _, (total_space E → B × F), λ e, e.to_bundle_trivialization⟩

instance : has_coe (topological_vector_bundle.trivialization R F E)
  (bundle_trivialization F (proj E)) :=
⟨topological_vector_bundle.trivialization.to_bundle_trivialization⟩

namespace topological_vector_bundle

variables {R F E}

lemma trivialization.mem_source (e : trivialization R F E)
  {x : total_space E} : x ∈ e.source ↔ proj E x ∈ e.base_set := bundle_trivialization.mem_source e

@[simp, mfld_simps] lemma trivialization.coe_coe (e : trivialization R F E) :
  ⇑e.to_local_homeomorph = e := rfl

end topological_vector_bundle

end

variables [∀ x, topological_space (E x)]

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class topological_vector_bundle : Prop :=
(inducing [] : ∀ (b : B), inducing (λ x : (E b), (id ⟨b, x⟩ : total_space E)))
(locally_trivial [] : ∀ b : B, ∃ e : topological_vector_bundle.trivialization R F E, b ∈ e.base_set)

variable [topological_vector_bundle R F E]

namespace topological_vector_bundle

/-- `trivialization_at R F E b` is some choice of trivialization of a vector bundle whose base set
contains a given point `b`. -/
def trivialization_at : Π b : B, trivialization R F E :=
λ b, classical.some (topological_vector_bundle.locally_trivial R F E b)

@[simp, mfld_simps] lemma mem_base_set_trivialization_at (b : B) :
  b ∈ (trivialization_at R F E b).base_set :=
classical.some_spec (topological_vector_bundle.locally_trivial R F E b)

@[simp, mfld_simps] lemma base_set_trivialization_at_mem_nhds (b : B) :
  (trivialization_at R F E b).base_set ∈ nhds b :=
is_open.mem_nhds (trivialization_at R F E b).open_base_set (mem_base_set_trivialization_at R F E b)

@[simp, mfld_simps] lemma mem_source_trivialization_at (z : total_space E) :
  z ∈ (trivialization_at R F E z.1).source :=
by { rw bundle_trivialization.mem_source, apply mem_base_set_trivialization_at }

variables {R F E}

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
def trivialization.continuous_linear_equiv_at (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) : E b ≃L[R] F :=
{ to_fun := λ y, (e ⟨b, y⟩).2,
  inv_fun := λ z, begin
    have : ((e.to_local_homeomorph.symm) (b, z)).fst = b :=
      bundle_trivialization.proj_symm_apply' _ hb,
    have C : E ((e.to_local_homeomorph.symm) (b, z)).fst = E b, by rw this,
    exact cast C (e.to_local_homeomorph.symm (b, z)).2
  end,
  left_inv := begin
    assume v,
    rw [← heq_iff_eq],
    apply (cast_heq _ _).trans,
    have A : (b, (e ⟨b, v⟩).snd) = e ⟨b, v⟩,
    { refine prod.ext _ rfl,
      symmetry,
      exact bundle_trivialization.coe_fst' _ hb },
    have B : e.to_local_homeomorph.symm (e ⟨b, v⟩) = ⟨b, v⟩,
    { apply local_homeomorph.left_inv_on,
      rw bundle_trivialization.mem_source,
      exact hb },
    rw [A, B],
  end,
  right_inv := begin
    assume v,
    have B : e (e.to_local_homeomorph.symm (b, v)) = (b, v),
    { apply local_homeomorph.right_inv_on,
      rw bundle_trivialization.mem_target,
      exact hb },
    have C : (e (e.to_local_homeomorph.symm (b, v))).2 = v, by rw [B],
    conv_rhs { rw ← C },
    dsimp,
    congr,
    ext,
    { exact (bundle_trivialization.proj_symm_apply' _ hb).symm },
    { exact (cast_heq _ _).trans (by refl) },
  end,
  map_add' := λ v w, (e.linear _ hb).map_add v w,
  map_smul' := λ c v, (e.linear _ hb).map_smul c v,
  continuous_to_fun := begin
    refine continuous_snd.comp _,
    apply continuous_on.comp_continuous e.to_local_homeomorph.continuous_on
      (topological_vector_bundle.inducing R F E b).continuous (λ x, _),
    rw bundle_trivialization.mem_source,
    exact hb,
  end,
  continuous_inv_fun := begin
    rw (topological_vector_bundle.inducing R F E b).continuous_iff,
    dsimp,
    have : continuous (λ (z : F), (e.to_bundle_trivialization.to_local_homeomorph.symm) (b, z)),
    { apply e.to_local_homeomorph.symm.continuous_on.comp_continuous
        (continuous_const.prod_mk continuous_id') (λ z, _),
      simp only [bundle_trivialization.mem_target, hb, local_equiv.symm_source,
        local_homeomorph.symm_to_local_equiv] },
    convert this,
    ext z,
    { exact (bundle_trivialization.proj_symm_apply' _ hb).symm },
    { exact cast_heq _ _ },
  end }

@[simp] lemma trivialization.continuous_linear_equiv_at_apply (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) (y : E b) : e.continuous_linear_equiv_at b hb y = (e ⟨b, y⟩).2 := rfl

@[simp] lemma trivialization.continuous_linear_equiv_at_apply' (e : trivialization R F E)
  (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at (proj E x) (e.mem_source.1 hx) x.2 = (e x).2 :=
by { cases x, refl }

section
local attribute [reducible] bundle.trivial

instance {B : Type*} {F : Type*} [add_comm_monoid F] (b : B) :
  add_comm_monoid (bundle.trivial B F b) := ‹add_comm_monoid F›

instance {B : Type*} {F : Type*} [add_comm_group F] (b : B) :
  add_comm_group (bundle.trivial B F b) := ‹add_comm_group F›

instance {B : Type*} {F : Type*} [add_comm_monoid F] [module R F] (b : B) :
  module R (bundle.trivial B F b) := ‹module R F›

end

variables (R B F)

/-- Local trivialization for trivial bundle. -/
def trivial_bundle_trivialization : trivialization R F (bundle.trivial B F) :=
{ to_fun := λ x, (x.fst, x.snd),
  inv_fun := λ y, ⟨y.fst, y.snd⟩,
  source := univ,
  target := univ,
  map_source' := λ x h, mem_univ (x.fst, x.snd),
  map_target' :=λ y h,  mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_refl _, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_refl _, },
  base_set := univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [univ_prod_univ],
  proj_to_fun := λ y hy, rfl,
  linear := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

instance trivial_bundle.topological_vector_bundle :
  topological_vector_bundle R F (bundle.trivial B F) :=
{ locally_trivial := λ x, ⟨trivial_bundle_trivialization R B F, mem_univ x⟩,
  inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp, proj,
      induced_const, top_inf_eq, trivial.proj_snd, id.def, trivial.topological_space, this,
      induced_id],
  end⟩ }

variables {R B F}

/- Not registered as an instance because of a metavariable. -/
lemma is_topological_vector_bundle_is_topological_fiber_bundle :
  is_topological_fiber_bundle F (proj E) :=
λ x, ⟨(trivialization_at R F E x).to_bundle_trivialization, mem_base_set_trivialization_at R F E x⟩

end topological_vector_bundle

section sections

open topological_vector_bundle

variables {R B E F}

lemma right_inv.preimage_source_eq_base_set (f : right_inv (proj E)) (b : B) :
  f ⁻¹' (trivialization_at R F E b).source = (trivialization_at R F E b).base_set :=
by rw [bundle_trivialization.source_eq, ←preimage_comp, f.right_inv]; refl

lemma right_inv.image_mem_trivialization_at_source (f : right_inv (proj E)) (b : B) :
  f b ∈ (trivialization_at R F E b).source :=
begin
  rw [mem_preimage.symm, right_inv.preimage_source_eq_base_set],
  exact mem_base_set_trivialization_at R F E b
end

lemma right_inv.mem_base_set_image_mem_source (f : right_inv (proj E)) {b : B} {x : B}
  (h : x ∈ (trivialization_at R F E b).base_set) :
  f x ∈ (trivialization_at R F E b).source :=
begin
  rw [mem_preimage.symm, right_inv.preimage_source_eq_base_set],
  exact h
end

@[simp, mfld_simps] lemma topological_vector_bundle.trivialization.coe_fst
  (e : trivialization R F E) {x : total_space E} (ex : x ∈ e.source) :
  (e x).1 = (proj E) x :=
e.proj_to_fun x ex

lemma right_inv.trivialization_at_fst (f : right_inv (proj E)) {b : B} :
  ∀ x ∈ (trivialization_at R F E b).base_set,
  ((trivialization_at R F E b) (f x)).fst = x :=
begin
  intros x h,
  rw [(trivialization_at R F E b).coe_fst (f.mem_base_set_image_mem_source h)],
  exact congr_fun f.right_inv x,
end

variables (R F E)

lemma right_inv.continuous_at_iff_continuous_within_at (f : right_inv (proj E)) (b : B) :
  continuous_at f b ↔
  continuous_within_at (λ x, ((trivialization_at R F E b) (f x)).snd)
  (trivialization_at R F E b).base_set b :=
⟨λ h, begin
  have h2 := (trivialization_at R F E b).to_bundle_trivialization.to_local_homeomorph.continuous_at
    (right_inv.image_mem_trivialization_at_source f b),
  exact (h2.comp h).continuous_within_at.snd,
end,
λ h, begin
  refine continuous_within_at.continuous_at _ (base_set_trivialization_at_mem_nhds R F E b),
  rw local_homeomorph.continuous_within_at_iff_continuous_within_at_comp_left
    ((trivialization_at R F E b).to_bundle_trivialization.to_local_homeomorph),
  { rw continuous_within_at_prod_iff,
    exact ⟨continuous_within_at.congr continuous_within_at_id (f.trivialization_at_fst)
      (f.trivialization_at_fst b (mem_base_set_trivialization_at R F E b)), h⟩ },
  { exact right_inv.image_mem_trivialization_at_source f b },
  { rw right_inv.preimage_source_eq_base_set, exact self_mem_nhds_within }
end ⟩

variables {R F E}

lemma mem_base_set_right_inv_fst {g : right_inv (proj E)} {b : B} {e : trivialization R F E}
  (hb : b ∈ e.base_set) : (g b).fst ∈ e.base_set := by { rw right_inv.fst_eq_id, exact hb }

lemma triv_snd_eq_cont_lin_equiv_at_snd {g : right_inv (proj E)} {b : B} {e : trivialization R F E}
  (hb : b ∈ e.base_set) :
  (e (g b)).snd =
  (e.continuous_linear_equiv_at ((g b).fst) (mem_base_set_right_inv_fst hb)) (g b).snd :=
by simp only [trivialization.continuous_linear_equiv_at_apply, sigma.eta]

lemma trivialization_at_snd_map_add (g h : right_inv (proj E)) (b : B) :
  ∀ x ∈ (trivialization_at R F E b).base_set,
  ((trivialization_at R F E b) ((g + h) x)).snd = ((trivialization_at R F E b) (g x)).snd +
  ((trivialization_at R F E b) (h x)).snd :=
begin
  intros x hx,
  repeat {rw triv_snd_eq_cont_lin_equiv_at_snd hx},
  simp only [linear_map.map_add],
  have H : ∀ f, ((trivialization_at R F E b).continuous_linear_equiv_at ((g + h) x).fst
    (mem_base_set_right_inv_fst hx)) ((right_inv.to_pi R f) ((g + h) x).fst) =
    ((trivialization_at R F E b).continuous_linear_equiv_at (f x).fst
    (mem_base_set_right_inv_fst hx)) (f x).snd := λ f,
  begin
    simp only [trivialization.continuous_linear_equiv_at_apply],
    have : (((g + h) x).fst : B) = (f x).fst := by { simp only [right_inv.fst_eq_id], },
    rw [this, right_inv.snd_eq_to_pi_fst R], end,
  rw [right_inv.snd_eq_to_pi_fst R, linear_equiv.map_add, pi.add_apply,
   continuous_linear_equiv.map_add, H g, H h],
end

variables {B E} (R F)

instance [has_continuous_add F] [topological_vector_bundle R F E] :
has_add (continuous_section (proj E)) :=
⟨λ g h, { continuous_to_fun := by begin
  refine continuous_iff_continuous_at.2 (λ b, _),
  rw [right_inv.to_fun_eq_coe,
    (((g : right_inv (proj E)) + h).continuous_at_iff_continuous_within_at R F E b)],
  refine continuous_within_at.congr _ (trivialization_at_snd_map_add ↑g ↑h b)
        ((trivialization_at_snd_map_add g h b) b (mem_base_set_trivialization_at R F E b)),
  have hg : continuous_at g.to_fun b := g.continuous_to_fun.continuous_at,
  have hh : continuous_at h.to_fun b := h.continuous_to_fun.continuous_at,
  rw [continuous_section.to_fun_eq_coe, ←continuous_section.coe_fn_coe] at hg hh,
  rw right_inv.continuous_at_iff_continuous_within_at R F E ↑g b at hg,
  rw right_inv.continuous_at_iff_continuous_within_at R F E ↑h b at hh,
  simp only [continuous_section.coe_fn_coe] at *,
  exact continuous_add.continuous_within_at.comp_univ (hg.prod hh),
  end,
..((g : right_inv (proj E)) + h) } ⟩

variables {R F}

lemma trivialization.map_zero {e : trivialization R F E} (b : B) (hb : b ∈ e.base_set) :
  (e ((0 : right_inv (proj E)) b)).snd = 0 :=
by { rw [triv_snd_eq_cont_lin_equiv_at_snd hb, right_inv.snd_eq_to_pi_fst R, linear_equiv.map_zero,
  pi.zero_apply, continuous_linear_equiv.map_zero], assumption }
--                  What the heck it's going on here!?  ↑

variables (R F)

instance [topological_vector_bundle R F E] : has_zero (continuous_section (proj E)) :=
⟨ { continuous_to_fun := begin
  refine continuous_iff_continuous_at.2 (λ b, _),
  rw [right_inv.to_fun_eq_coe,
    ((0 : right_inv (proj E)).continuous_at_iff_continuous_within_at R F E b)],
  refine continuous_within_at.congr _ trivialization.map_zero
    (trivialization.map_zero b (mem_base_set_trivialization_at R F E b)),
  exact continuous_within_at_const
end,
  ..(0 : right_inv (proj E))} ⟩

instance [topological_vector_bundle R F E] : inhabited (continuous_section (proj E)) := ⟨0⟩

variables {R F}

lemma trivialization.map_smul {g : right_inv (proj E)} {e : trivialization R F E} {r : R} (b : B)
  (hb : b ∈ e.base_set) :
  (e ((r • (g : right_inv (proj E))) b)).snd = r • (e ((g : right_inv (proj E)) b)).snd :=
begin
  rw [triv_snd_eq_cont_lin_equiv_at_snd hb, right_inv.snd_eq_to_pi_fst R, linear_equiv.map_smul,
    pi.smul_apply, continuous_linear_equiv.map_smul],
  simp only [trivialization.continuous_linear_equiv_at_apply],
  congr,
  have h : ((r • g) b).fst = (g b).fst := by simp only [right_inv.fst_eq_id],
  rw [h, (right_inv.snd_eq_to_pi_fst R).symm],
  exact sigma.eq rfl rfl,
end

variables (R F)

instance [has_continuous_add F] [topological_vector_bundle R F E] :
add_comm_monoid (continuous_section (proj E)) :=
{ add_assoc := λ f g h, by { apply continuous_section.ext_right_inv, exact add_assoc _ _ _ },
  zero_add := λ f, by { apply continuous_section.ext_right_inv, exact zero_add _ },
  add_zero := λ f, by { apply continuous_section.ext_right_inv, exact add_zero _ },
  add_comm := λ f g, by { apply continuous_section.ext_right_inv, exact add_comm _ _ },
  ..continuous_section.has_zero R F,
  ..continuous_section.has_add R F, }

instance [topological_space R] [has_continuous_smul R F] [topological_vector_bundle R F E] :
has_scalar R (continuous_section (proj E)) :=
⟨λ r g, { continuous_to_fun := by begin
  refine continuous_iff_continuous_at.2 (λ b, _),
  rw [right_inv.to_fun_eq_coe,
    ((r • (g : right_inv (proj E))).continuous_at_iff_continuous_within_at R F E b)],
  refine continuous_within_at.congr _ trivialization.map_smul
    (trivialization.map_smul b (mem_base_set_trivialization_at R F E b)),
  have hg : continuous_at g.to_fun b := g.continuous_to_fun.continuous_at,
  rw [continuous_section.to_fun_eq_coe, ←continuous_section.coe_fn_coe] at hg,
  rw right_inv.continuous_at_iff_continuous_within_at R F E ↑g b at hg,
  simp only [continuous_section.coe_fn_coe] at *,
  exact continuous_within_at.const_smul hg r,
  end,
..(r • (g : right_inv (proj E))) } ⟩

instance [has_continuous_add F] [topological_space R] [has_continuous_smul R F]
  [topological_vector_bundle R F E] : module R (continuous_section (proj E)) :=
{ zero_smul := λ f, by { apply continuous_section.ext_right_inv, exact zero_smul R _ },
  smul_zero := λ r, by { apply continuous_section.ext_right_inv, exact smul_zero r },
  add_smul := λ r s f, by { apply continuous_section.ext_right_inv,
                exact add_smul r s (f : right_inv (proj E)) },
  smul_add := λ r f g, by { apply continuous_section.ext_right_inv, exact smul_add r _ _ },
  add_smul := λ r s g, by { apply continuous_section.ext_right_inv, exact add_smul r s _ },
  mul_smul := λ r s g, by { apply continuous_section.ext_right_inv, exact mul_smul r s _ },
  one_smul := λ f, by { apply continuous_section.ext_right_inv, exact one_smul R _ },
  ..continuous_section.has_scalar R F }

end sections

end

section sections

open topological_vector_bundle

variables {E R F}
  [ring R] [∀ x, add_comm_group (E x)] [∀ x, module R (E x)]
  [add_comm_group F] [module R F] [topological_add_group F]
  [∀ x, topological_space (E x)]

lemma trivialization.map_neg [topological_vector_bundle R F E] {g : right_inv (proj E)}
  {e : trivialization R F E} (b : B) (hb : b ∈ e.base_set) :
  (e ((- (g : right_inv (proj E))) b)).snd = - (e ((g : right_inv (proj E)) b)).snd :=
begin
  rw [triv_snd_eq_cont_lin_equiv_at_snd hb, right_inv.snd_eq_to_pi_fst R],
  rw [((right_inv.to_pi R) : (right_inv (proj E)) ≃ₗ[R] (Π x, E x)).map_neg],
  /- What is going on here!?   ↑   ↑   ↑   ↑   ↑    ↑    ↑  -/
  rw [pi.neg_apply, continuous_linear_equiv.map_neg],
  simp only [trivialization.continuous_linear_equiv_at_apply],
  congr,
  have h : ((-g) b).fst = (g b).fst := by simp only [right_inv.fst_eq_id],
  rw [h, (right_inv.snd_eq_to_pi_fst R).symm],
  exact sigma.eq rfl rfl,
end

variables (R F)

instance [topological_vector_bundle R F E] :
has_neg (continuous_section (proj E)) :=
⟨λ g, { continuous_to_fun := by begin
  refine continuous_iff_continuous_at.2 (λ b, _),
  rw [right_inv.to_fun_eq_coe,
    ((-(g : right_inv (proj E))).continuous_at_iff_continuous_within_at R F E b)],
    refine continuous_within_at.congr _ trivialization.map_neg
    (trivialization.map_neg b (mem_base_set_trivialization_at R F E b)),
  have hg : continuous_at g.to_fun b := g.continuous_to_fun.continuous_at,
  rw [continuous_section.to_fun_eq_coe, ←continuous_section.coe_fn_coe] at hg,
  rw right_inv.continuous_at_iff_continuous_within_at R F E ↑g b at hg,
  simp only [continuous_section.coe_fn_coe] at *,
  exact continuous_within_at.neg hg,
  end,
..(-(g : right_inv (proj E))) } ⟩

instance [topological_vector_bundle R F E]:
add_comm_group (continuous_section (proj E)) :=
{ add_left_neg :=  λ f, by { apply continuous_section.ext_right_inv,
                            exact add_left_neg (f : right_inv (proj E)) },
  ..continuous_section.has_neg R F,
  ..continuous_section.add_comm_monoid R F, }

end sections
