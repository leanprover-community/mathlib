/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import topology.subset_properties
import topology.connected
import topology.algebra.monoid
import tactic.tfae

/-!
# Locally constant functions

This file sets up the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `is_locally_constant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if every set in `Y` has an open preimage.
* `locally_constant X Y` : the type of locally constant maps from `X` to `Y`
* `locally_constant.map` : push-forward of locally constant maps
* `locally_constant.comap` : pull-back of locally constant maps

-/

variables {X Y Z α : Type*} [topological_space X]

open set filter
open_locale topological_space

/-- A function between topological spaces is locally constant if the preimage of any set is open. -/
def is_locally_constant (f : X → Y) : Prop := ∀ s : set Y, is_open (f ⁻¹' s)

namespace is_locally_constant

protected lemma tfae (f : X → Y) :
  tfae [is_locally_constant f,
    ∀ x, ∀ᶠ x' in 𝓝 x, f x' = f x,
    ∀ x, is_open {x' | f x' = f x},
    ∀ y, is_open (f ⁻¹' {y}),
    ∀ x, ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x] :=
begin
  tfae_have : 1 → 4, from λ h y, h {y},
  tfae_have : 4 → 3, from λ h x, h (f x),
  tfae_have : 3 → 2, from λ h x, mem_nhds_sets (h x) rfl,
  tfae_have : 2 → 5,
  { intros h x,
    rcases mem_nhds_sets_iff.1 (h x) with ⟨U, eq, hU, hx⟩,
    exact ⟨U, hU, hx, eq⟩ },
  tfae_have : 5 → 1,
  { intros h s,
    refine is_open_iff_forall_mem_open.2 (λ x hx, _),
    rcases h x with ⟨U, hU, hxU, eq⟩,
    exact ⟨U, λ x' hx', mem_preimage.2 $ (eq x' hx').symm ▸ hx, hU, hxU⟩ },
  tfae_finish
end

@[nontriviality] lemma of_discrete [discrete_topology X] (f : X → Y) :
  is_locally_constant f :=
λ s, is_open_discrete _

lemma is_open_fiber {f : X → Y} (hf : is_locally_constant f) (y : Y) :
  is_open {x | f x = y} :=
hf {y}

lemma iff_exists_open (f : X → Y) :
  is_locally_constant f ↔ ∀ x, ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
(is_locally_constant.tfae f).out 0 4

lemma iff_eventually_eq (f : X → Y) :
  is_locally_constant f ↔ ∀ x, ∀ᶠ y in 𝓝 x, f y = f x :=
(is_locally_constant.tfae f).out 0 1

lemma exists_open {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
(iff_exists_open f).1 hf x

protected lemma eventually_eq {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∀ᶠ y in 𝓝 x, f y = f x :=
(iff_eventually_eq f).1 hf x

protected lemma continuous [topological_space Y] {f : X → Y} (hf : is_locally_constant f) :
  continuous f :=
⟨λ U hU, hf _⟩

lemma iff_continuous {_ : topological_space Y} [discrete_topology Y] (f : X → Y) :
  is_locally_constant f ↔ continuous f :=
⟨is_locally_constant.continuous, λ h s, h.is_open_preimage s (is_open_discrete _)⟩

lemma iff_continuous_bot (f : X → Y) :
  is_locally_constant f ↔ @continuous X Y _ ⊥ f :=
iff_continuous f

lemma of_constant (f : X → Y) (h : ∀ x y, f x = f y) :
  is_locally_constant f :=
(iff_eventually_eq f).2 $ λ x, eventually_of_forall $ λ x', h _ _

lemma const (y : Y) : is_locally_constant (function.const X y) :=
of_constant _ $ λ _ _, rfl

lemma comp {f : X → Y} (hf : is_locally_constant f) (g : Y → Z) :
  is_locally_constant (g ∘ f) :=
λ s, by { rw set.preimage_comp, exact hf _ }

lemma prod_mk {Y'} {f : X → Y} {f' : X → Y'} (hf : is_locally_constant f)
  (hf' : is_locally_constant f') :
  is_locally_constant (λ x, (f x, f' x)) :=
(iff_eventually_eq _).2 $ λ x, (hf.eventually_eq x).mp $ (hf'.eventually_eq x).mono $
  λ x' hf' hf, prod.ext hf hf'

lemma comp₂ {Y₁ Y₂ Z : Type*} {f : X → Y₁} {g : X → Y₂}
  (hf : is_locally_constant f) (hg : is_locally_constant g) (h : Y₁ → Y₂ → Z) :
  is_locally_constant (λ x, h (f x) (g x)) :=
(hf.prod_mk hg).comp (λ x : Y₁ × Y₂, h x.1 x.2)

lemma comp_continuous [topological_space Y] {g : Y → Z} {f : X → Y}
  (hg : is_locally_constant g) (hf : continuous f) :
  is_locally_constant (g ∘ f) :=
λ s, by { rw set.preimage_comp, exact hf.is_open_preimage _ (hg _) }

/-- A locally constant function is constant on any preconnected set. -/
lemma apply_eq_of_is_preconnected {f : X → Y} (hf : is_locally_constant f)
  {s : set X} (hs : is_preconnected s) {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
  f x = f y :=
begin
  let U := f ⁻¹' {f y},
  suffices : x ∉ Uᶜ, from not_not.1 this,
  intro hxV,
  specialize hs U Uᶜ (hf {f y}) (hf {f y}ᶜ) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩,
  { simpa only [inter_empty, not_nonempty_empty, inter_compl_self] using hs },
  { simp only [union_compl_self, subset_univ] }
end

lemma iff_is_const [preconnected_space X] {f : X → Y} :
  is_locally_constant f ↔ ∀ x y, f x = f y :=
⟨λ h x y, h.apply_eq_of_is_preconnected is_preconnected_univ trivial trivial, of_constant _⟩

lemma range_finite [compact_space X] {f : X → Y} (hf : is_locally_constant f) :
  (set.range f).finite :=
begin
  letI : topological_space Y := ⊥,
  haveI : discrete_topology Y := ⟨rfl⟩,
  rw @iff_continuous X Y ‹_› ‹_› at hf,
  exact finite_of_is_compact_of_discrete _ (compact_range hf)
end

@[to_additive] lemma one [has_one Y] : is_locally_constant (1 : X → Y) := const 1

@[to_additive] lemma inv [has_inv Y] ⦃f : X → Y⦄ (hf : is_locally_constant f) :
  is_locally_constant f⁻¹ :=
hf.comp (λ x, x⁻¹)

@[to_additive]
lemma mul [has_mul Y] ⦃f g : X → Y⦄ (hf : is_locally_constant f) (hg : is_locally_constant g) :
  is_locally_constant (f * g) :=
hf.comp₂ hg (*)

@[to_additive]
lemma div [has_div Y] ⦃f g : X → Y⦄ (hf : is_locally_constant f) (hg : is_locally_constant g) :
  is_locally_constant (f / g) :=
hf.comp₂ hg (/)

end is_locally_constant

/-- A (bundled) locally constant function from a topological space `X` to a type `Y`. -/
structure locally_constant (X Y : Type*) [topological_space X] :=
(to_fun : X → Y)
(is_locally_constant : is_locally_constant to_fun)

namespace locally_constant

instance [inhabited Y] : inhabited (locally_constant X Y) :=
⟨⟨_, is_locally_constant.const (default Y)⟩⟩

instance : has_coe_to_fun (locally_constant X Y) := ⟨_, locally_constant.to_fun⟩

initialize_simps_projections locally_constant (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : locally_constant X Y) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : X → Y) (h) : ⇑(⟨f, h⟩ : locally_constant X Y) = f := rfl

theorem congr_fun {f g : locally_constant X Y} (h : f = g) (x : X) : f x = g x :=
congr_arg (λ h : locally_constant X Y, h x) h

theorem congr_arg (f : locally_constant X Y) {x y : X} (h : x = y) : f x = f y :=
congr_arg (λ x : X, f x) h

theorem coe_injective : function.injective (λ (f : locally_constant X Y) (x : X), f x)
| ⟨f, hf⟩ ⟨g, hg⟩ h := have f = g, from h, by subst f

@[simp, norm_cast] theorem coe_inj {f g : locally_constant X Y} : (f : X → Y) = g ↔ f = g :=
coe_injective.eq_iff

@[ext] theorem ext ⦃f g : locally_constant X Y⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

theorem ext_iff {f g : locally_constant X Y} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

protected lemma continuous [topological_space Y] (f : locally_constant X Y) : continuous f :=
f.is_locally_constant.continuous

/-- The constant locally constant function on `X` with value `y : Y`. -/
def const (X : Type*) {Y : Type*} [topological_space X] (y : Y) :
  locally_constant X Y :=
⟨function.const X y, is_locally_constant.const _⟩

lemma range_finite [compact_space X] (f : locally_constant X Y) :
  (set.range f).finite :=
f.is_locally_constant.range_finite

lemma apply_eq_of_is_preconnected (f : locally_constant X Y) {s : set X} (hs : is_preconnected s)
  {x y : X} (hx : x ∈ s) (hy : y ∈ s) :
  f x = f y :=
f.is_locally_constant.apply_eq_of_is_preconnected hs hx hy

lemma apply_eq_of_preconnected_space [preconnected_space X] (f : locally_constant X Y) (x y : X) :
  f x = f y :=
f.is_locally_constant.apply_eq_of_is_preconnected is_preconnected_univ trivial trivial

lemma eq_const [preconnected_space X] (f : locally_constant X Y) (x : X) :
  f = const X (f x) :=
ext $ λ y, apply_eq_of_preconnected_space f _ _

lemma exists_eq_const [preconnected_space X] [nonempty Y] (f : locally_constant X Y) :
  ∃ y, f = const X y :=
begin
  rcases classical.em (nonempty X) with ⟨⟨x⟩⟩|hX,
  { exact ⟨f x, f.eq_const x⟩ },
  { exact ⟨classical.arbitrary Y, ext $ λ x, (hX ⟨x⟩).elim⟩ }
end

/-- Push forward of locally constant maps under any map, by post-composition. -/
def map (f : Y → Z) : locally_constant X Y → locally_constant X Z :=
λ g, ⟨f ∘ g, λ s, by { rw set.preimage_comp, apply g.is_locally_constant }⟩

@[simp] lemma map_apply (f : Y → Z) (g : locally_constant X Y) : ⇑(map f g) = f ∘ g := rfl

@[simp] lemma map_id : @map X Y Y _ id = id := by { ext, refl }

@[simp] lemma map_comp {Y₁ Y₂ Y₃ : Type*} (g : Y₂ → Y₃) (f : Y₁ → Y₂) :
  @map X _ _ _ g ∘ map f = map (g ∘ f) := by { ext, refl }

section comap

open_locale classical

variables [topological_space Y]

/-- Pull back of locally constant maps under any map, by pre-composition.

This definition only makes sense if `f` is continuous,
in which case it sends locally constant functions to their precomposition with `f`.
See also `locally_constant.coe_comap`. -/
noncomputable
def comap (f : X → Y) :
  locally_constant Y Z → locally_constant X Z :=
if hf : continuous f
then λ g, ⟨g ∘ f, g.is_locally_constant.comp_continuous hf⟩
else
begin
  by_cases H : nonempty X,
  { introsI g, exact const X (g $ f $ classical.arbitrary X) },
  { intro g, refine ⟨λ x, (H ⟨x⟩).elim, _⟩,
    intro s, rw is_open_iff_nhds, intro x, exact (H ⟨x⟩).elim }
end

@[simp] lemma coe_comap (f : X → Y) (g : locally_constant Y Z) (hf : continuous f) :
  ⇑(comap f g) = g ∘ f :=
by { rw [comap, dif_pos hf], refl }

@[simp] lemma comap_id : @comap X X Z _ _ id = id :=
by { ext, simp only [continuous_id, id.def, function.comp.right_id, coe_comap] }

lemma comap_comp [topological_space Z]
  (f : X → Y) (g : Y → Z) (hf : continuous f) (hg : continuous g) :
  @comap _ _ α _ _ f ∘ comap g = comap (g ∘ f) :=
by { ext, simp only [hf, hg, hg.comp hf, coe_comap] }

lemma comap_const (f : X → Y) (y : Y) (h : ∀ x, f x = y) :
  (comap f : locally_constant Y Z → locally_constant X Z) =
  λ g, ⟨λ x, g y, is_locally_constant.const _⟩ :=
begin
  ext, rw coe_comap,
  { simp only [h, coe_mk, function.comp_app] },
  { rw show f = λ x, y, by ext; apply h,
    exact continuous_const }
end

end comap

end locally_constant
