/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/

import topology.vector_bundle.basic

/-!
# Fiberwise product of two vector bundles

If `E₁ : B → Type*` and `E₂ : B → Type*` define two fiber bundles over `R` with fiber
models `F₁` and `F₂`, we define the bundle of fibrewise products `E₁ ×ᵇ E₂ := λ x, E₁ x × E₂ x`.

If moreover `E₁` and `E₂` are vector bundles over `R`, we can endow `E₁ ×ᵇ E₂` with a vector bundle
structure: `bundle.prod.vector_bundle`, the direct sum of the two vector bundles.

A similar construction (which is yet to be formalized) can be done for the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber a type synonym
`vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂ x := (E₁ x →L[R] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[R] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces).  Likewise for tensor
products of topological vector bundles, exterior algebras, and so on, where the topology can be
defined using a norm on the fiber model if this helps.

## Tags
Vector bundle, fiberwise product, direct sum
-/

noncomputable theory

open bundle set
open_locale classical bundle

variables (R 𝕜 : Type*) {B : Type*} (F : Type*) (E : B → Type*)

section defs
variables (E₁ : B → Type*) (E₂ : B → Type*)
variables [topological_space (total_space E₁)] [topological_space (total_space E₂)]

/-- Equip the total space of the fibrewise product of two fiber bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `total_space E₁ × total_space E₂`. -/
instance fiber_bundle.prod.topological_space :
  topological_space (total_space (E₁ ×ᵇ E₂)) :=
topological_space.induced
  (λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)))
  (by apply_instance : topological_space (total_space E₁ × total_space E₂))

/-- The diagonal map from the total space of the fibrewise product of two fiber bundles
`E₁`, `E₂` into `total_space E₁ × total_space E₂` is `inducing`. -/
lemma fiber_bundle.prod.inducing_diag : inducing
  (λ p, (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
    total_space (E₁ ×ᵇ E₂) → total_space E₁ × total_space E₂) :=
⟨rfl⟩

end defs

open fiber_bundle

variables [nontrivially_normed_field R] [topological_space B]

variables (F₁' : Type*) [topological_space F₁']
  (F₁ : Type*) [normed_add_comm_group F₁] [normed_space R F₁]
  (E₁ : B → Type*) [topological_space (total_space E₁)]

variables (F₂' : Type*) [topological_space F₂']
  (F₂ : Type*) [normed_add_comm_group F₂] [normed_space R F₂]
  (E₂ : B → Type*) [topological_space (total_space E₂)]

namespace trivialization
variables (ε₁ : trivialization F₁' (π E₁)) (ε₂ : trivialization F₂' (π E₂))
variables (e₁ : trivialization F₁ (π E₁)) (e₂ : trivialization F₂ (π E₂))
include ε₁ ε₂
variables {R F₁' F₁ E₁ F₂' F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `trivialization.prod`, the induced
trivialization for the fibrewise product of `E₁` and `E₂`. -/
def prod.to_fun' : total_space (E₁ ×ᵇ E₂) → B × (F₁' × F₂') :=
λ p, ⟨p.1, (ε₁ ⟨p.1, p.2.1⟩).2, (ε₂ ⟨p.1, p.2.2⟩).2⟩

variables {ε₁ ε₂}

lemma prod.continuous_to_fun : continuous_on (prod.to_fun' ε₁ ε₂)
  (@total_space.proj B (E₁ ×ᵇ E₂) ⁻¹' (ε₁.base_set ∩ ε₂.base_set)) :=
begin
  let f₁ : total_space (E₁ ×ᵇ E₂) → total_space E₁ × total_space E₂ :=
    λ p, ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂)),
  let f₂ : total_space E₁ × total_space E₂ → (B × F₁') × (B × F₂') := λ p, ⟨ε₁ p.1, ε₂ p.2⟩,
  let f₃ : (B × F₁') × (B × F₂') → B × F₁' × F₂' := λ p, ⟨p.1.1, p.1.2, p.2.2⟩,
  have hf₁ : continuous f₁ := (prod.inducing_diag E₁ E₂).continuous,
  have hf₂ : continuous_on f₂ (ε₁.source ×ˢ ε₂.source) :=
    ε₁.to_local_homeomorph.continuous_on.prod_map ε₂.to_local_homeomorph.continuous_on,
  have hf₃ : continuous f₃ :=
    (continuous_fst.comp continuous_fst).prod_mk (continuous_snd.prod_map continuous_snd),
  refine ((hf₃.comp_continuous_on hf₂).comp hf₁.continuous_on _).congr _,
  { rw [ε₁.source_eq, ε₂.source_eq],
    exact maps_to_preimage _ _ },
  rintros ⟨b, v₁, v₂⟩ ⟨hb₁, hb₂⟩,
  simp only [prod.to_fun', prod.mk.inj_iff, eq_self_iff_true, and_true],
  rw ε₁.coe_fst,
  rw [ε₁.source_eq, mem_preimage],
  exact hb₁,
end

variables (ε₁ ε₂) [nz₁ : Π x, has_zero (E₁ x)] [nz₂ : ∀ x, has_zero (E₂ x)]
  [mnd₁ : Π x, add_comm_monoid (E₁ x)] [mdl₁ : Π x, module R (E₁ x)]
  [mnd₂ : Π x, add_comm_monoid (E₂ x)] [mdl₂ : Π x, module R (E₂ x)]

include nz₁ nz₂

/-- Given trivializations `ε₁`, `ε₂` for fiber bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `trivialization.prod`, the induced
trivialization for the fibrewise product of `E₁` and `E₂`. -/
def prod.inv_fun' (p : B × (F₁' × F₂')) : total_space (E₁ ×ᵇ E₂) :=
⟨p.1, ε₁.symm p.1 p.2.1, ε₂.symm p.1 p.2.2⟩

variables {ε₁ ε₂}

lemma prod.left_inv {x : total_space (E₁ ×ᵇ E₂)}
  (h : x ∈ @total_space.proj B (E₁ ×ᵇ E₂) ⁻¹' (ε₁.base_set ∩ ε₂.base_set)) :
  prod.inv_fun' ε₁ ε₂ (prod.to_fun' ε₁ ε₂ x) = x :=
begin
  obtain ⟨x, v₁, v₂⟩ := x,
  obtain ⟨h₁ : x ∈ ε₁.base_set, h₂ : x ∈ ε₂.base_set⟩ := h,
  simp only [prod.to_fun', prod.inv_fun', symm_apply_apply_mk, h₁, h₂]
end

lemma prod.right_inv {x : B × F₁' × F₂'}
  (h : x ∈ (ε₁.base_set ∩ ε₂.base_set) ×ˢ (univ : set (F₁' × F₂'))) :
  prod.to_fun' ε₁ ε₂ (prod.inv_fun' ε₁ ε₂ x) = x :=
begin
  obtain ⟨x, w₁, w₂⟩ := x,
  obtain ⟨⟨h₁ : x ∈ ε₁.base_set, h₂ : x ∈ ε₂.base_set⟩, -⟩ := h,
  simp only [prod.to_fun', prod.inv_fun', apply_mk_symm, h₁, h₂]
end

lemma prod.continuous_inv_fun :
  continuous_on (prod.inv_fun' ε₁ ε₂) ((ε₁.base_set ∩ ε₂.base_set) ×ˢ univ) :=
begin
  rw (prod.inducing_diag E₁ E₂).continuous_on_iff,
  have H₁ : continuous (λ p : B × F₁' × F₂', ((p.1, p.2.1), (p.1, p.2.2))) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd),
  refine (ε₁.continuous_on_symm.prod_map ε₂.continuous_on_symm).comp H₁.continuous_on _,
  exact λ x h, ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩
end

variables (e₁ e₂ ε₁ ε₂ R)
variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁' E₁] [fiber_bundle F₂' E₂] [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]

/-- Given trivializations `ε₁`, `ε₂` for fiber bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the fibrewise product of `E₁` and `E₂`, whose base set is
`ε₁.base_set ∩ ε₂.base_set`. -/
@[nolint unused_arguments]
def prod : trivialization (F₁' × F₂') (π (E₁ ×ᵇ E₂)) :=
{ to_fun := prod.to_fun' ε₁ ε₂,
  inv_fun := prod.inv_fun' ε₁ ε₂,
  source := (@total_space.proj B (E₁ ×ᵇ E₂)) ⁻¹' (ε₁.base_set ∩ ε₂.base_set),
  target := (ε₁.base_set ∩ ε₂.base_set) ×ˢ set.univ,
  map_source' := λ x h, ⟨h, set.mem_univ _⟩,
  map_target' := λ x h, h.1,
  left_inv' := λ x, prod.left_inv,
  right_inv' := λ x, prod.right_inv,
  open_source := begin
    refine (ε₁.open_base_set.inter ε₂.open_base_set).preimage _,
    have : continuous (@total_space.proj B E₁) := continuous_proj F₁' E₁,
    exact this.comp (prod.inducing_diag E₁ E₂).continuous.fst,
  end,
  open_target := (ε₁.open_base_set.inter ε₂.open_base_set).prod is_open_univ,
  continuous_to_fun := prod.continuous_to_fun,
  continuous_inv_fun := prod.continuous_inv_fun,
  base_set := ε₁.base_set ∩ ε₂.base_set,
  open_base_set := ε₁.open_base_set.inter ε₂.open_base_set,
  source_eq := rfl,
  target_eq := rfl,
  proj_to_fun := λ x h, rfl }

omit nz₁ nz₂ ε₁ ε₂
include mnd₁ mdl₁ mnd₂ mdl₂

instance prod.is_linear [e₁.is_linear R] [e₂.is_linear R] : (e₁.prod e₂).is_linear R :=
{ linear := λ x ⟨h₁, h₂⟩, (((e₁.linear R h₁).mk' _).prod_map ((e₂.linear R h₂).mk' _)).is_linear }

omit mnd₁ mdl₁ mnd₂ mdl₂
include nz₁ nz₂

@[simp] lemma base_set_prod : (prod ε₁ ε₂).base_set = ε₁.base_set ∩ ε₂.base_set :=
rfl

omit nz₁ nz₂
include mnd₁ mdl₁ mnd₂ mdl₂

variables {e₁ e₂ ε₁ ε₂}

variables (R)

lemma prod_apply
  [e₁.is_linear R] [e₂.is_linear R] {x : B} (hx₁ : x ∈ e₁.base_set)
  (hx₂ : x ∈ e₂.base_set) (v₁ : E₁ x) (v₂ : E₂ x) :
  prod e₁ e₂ ⟨x, (v₁, v₂)⟩
  = ⟨x, e₁.continuous_linear_equiv_at R x hx₁ v₁, e₂.continuous_linear_equiv_at R x hx₂ v₂⟩ :=
rfl

omit mnd₁ mdl₁ mnd₂ mdl₂
include nz₁ nz₂

lemma prod_symm_apply (x : B) (w₁ : F₁') (w₂ : F₂') : (prod ε₁ ε₂).to_local_equiv.symm (x, w₁, w₂)
  = ⟨x, ε₁.symm x w₁, ε₂.symm x w₂⟩ :=
rfl

end trivialization

open trivialization

variables [nz₁ : Π x, has_zero (E₁ x)] [nz₂ : ∀ x, has_zero (E₂ x)]
  [mnd₁ : Π x, add_comm_monoid (E₁ x)] [mdl₁ : Π x, module R (E₁ x)]
  [mnd₂ : Π x, add_comm_monoid (E₂ x)] [mdl₂ : Π x, module R (E₂ x)]

variables [Π x : B, topological_space (E₁ x)] [Π x : B, topological_space (E₂ x)]
  [fiber_bundle F₁' E₁] [fiber_bundle F₂' E₂]
  [fiber_bundle F₁ E₁] [fiber_bundle F₂ E₂]

include nz₁ nz₂

/-- The product of two fiber bundles is a fiber bundle. -/
instance _root_.bundle.prod.fiber_bundle : fiber_bundle (F₁' × F₂') (E₁ ×ᵇ E₂) :=
{ total_space_mk_inducing := λ b,
  begin
    rw (prod.inducing_diag E₁ E₂).inducing_iff,
    exact (total_space_mk_inducing F₁' E₁ b).prod_mk (total_space_mk_inducing F₂' E₂ b),
  end,
  trivialization_atlas :=
    {e |  ∃ (e₁ : trivialization F₁' (π E₁)) (e₂ : trivialization F₂' (π E₂))
    [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₂], by exactI
    e = trivialization.prod e₁ e₂},
  trivialization_at := λ b, (trivialization_at F₁' E₁ b).prod (trivialization_at F₂' E₂ b),
  mem_base_set_trivialization_at :=
    λ b, ⟨mem_base_set_trivialization_at F₁' E₁ b, mem_base_set_trivialization_at F₂' E₂ b⟩,
  trivialization_mem_atlas := λ b, ⟨trivialization_at F₁' E₁ b, trivialization_at F₂' E₂ b,
    by apply_instance, by apply_instance, rfl⟩ }

omit nz₁ nz₂
include mnd₁ mdl₁ mnd₂ mdl₂

/-- The product of two vector bundles is a vector bundle. -/
instance _root_.bundle.prod.vector_bundle  [vector_bundle R F₁ E₁] [vector_bundle R F₂ E₂] :
  vector_bundle R (F₁ × F₂) (E₁ ×ᵇ E₂) :=
{ trivialization_linear' := begin
    rintros _ ⟨e₁, e₂, he₁, he₂, rfl⟩, resetI,
    apply_instance
  end,
  continuous_on_coord_change' := begin
    rintros _ _ ⟨e₁, e₂, he₁, he₂, rfl⟩ ⟨e₁', e₂', he₁', he₂', rfl⟩, resetI,
    refine (((continuous_on_coord_change R e₁ e₁').mono _).prod_mapL R
      ((continuous_on_coord_change R e₂ e₂').mono _)).congr _;
    dsimp only [base_set_prod] with mfld_simps,
    { mfld_set_tac },
    { mfld_set_tac },
    { rintro b hb,
      rw [continuous_linear_map.ext_iff],
      rintro ⟨v₁, v₂⟩,
      show (e₁.prod e₂).coord_changeL R (e₁'.prod e₂') b (v₁, v₂) =
        (e₁.coord_changeL R e₁' b v₁, e₂.coord_changeL R e₂' b v₂),
      rw [e₁.coord_changeL_apply e₁', e₂.coord_changeL_apply e₂',
        (e₁.prod e₂).coord_changeL_apply'],
      exacts [rfl, hb, ⟨hb.1.2, hb.2.2⟩, ⟨hb.1.1, hb.2.1⟩] }
  end }

omit mnd₁ mdl₁ mnd₂ mdl₂
include nz₁ nz₂

instance _root_.bundle.prod.mem_trivialization_atlas {e₁ : trivialization F₁' (π E₁)}
  {e₂ : trivialization F₂' (π E₂)} [mem_trivialization_atlas e₁] [mem_trivialization_atlas e₂] :
  mem_trivialization_atlas (e₁.prod e₂ : trivialization (F₁' × F₂') (π (E₁ ×ᵇ E₂))) :=
{ out := ⟨e₁, e₂, by apply_instance, by apply_instance, rfl⟩ }

variables {R F₁ E₁ F₂ E₂}

omit nz₁ nz₂
include mnd₁ mdl₁ mnd₂ mdl₂

@[simp] lemma trivialization.continuous_linear_equiv_at_prod {e₁ : trivialization F₁ (π E₁)}
  {e₂ : trivialization F₂ (π E₂)} [e₁.is_linear R] [e₂.is_linear R] {x : B} (hx₁ : x ∈ e₁.base_set)
  (hx₂ : x ∈ e₂.base_set) :
  (e₁.prod e₂).continuous_linear_equiv_at R x ⟨hx₁, hx₂⟩
  = (e₁.continuous_linear_equiv_at R x hx₁).prod (e₂.continuous_linear_equiv_at R x hx₂) :=
begin
  ext1,
  funext v,
  obtain ⟨v₁, v₂⟩ := v,
  rw [(e₁.prod e₂).continuous_linear_equiv_at_apply R, trivialization.prod],
  exact (congr_arg prod.snd (prod_apply R hx₁ hx₂ v₁ v₂) : _)
end
