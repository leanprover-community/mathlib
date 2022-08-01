/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.balanced
import category_theory.limits.opposites
import category_theory.limits.shapes.zero_morphisms
import category_theory.subobject.lattice
import category_theory.subobject.well_powered
import data.set.opposite

/-!
# Separating and detecting sets

There are several non-equivalent notions of a generator of a category. Here, we consider two of
them:

* We say that `𝒢` is a separating set if the functors `C(G, -)` for `G ∈ 𝒢` are collectively
    faithful, i.e., if `h ≫ f = h ≫ g` for all `h` with domain in `𝒢` implies `f = g`.
* We say that `𝒢` is a detecting set if the functors `C(G, -)` collectively reflect isomorphisms,
    i.e., if any `h` with domain in `𝒢` uniquely factors through `f`, then `f` is an isomorphism.

There are, of course, also the dual notions of coseparating and codetecting sets.

## Main results

We
* define predicates `is_separating`, `is_coseparating`, `is_detecting` and `is_codetecting` on
  sets of objects;
* show that separating and coseparating are dual notions;
* show that detecting and codetecting are dual notions;
* show that if `C` has equalizers, then detecting implies separating;
* show that if `C` has coequalizers, then codetecting implies separating;
* show that if `C` is balanced, then separating implies detecting and coseparating implies
  codetecting;
* show that `∅` is separating if and only if `∅` is coseparating if and only if `C` is thin;
* show that `∅` is detecting if and only if `∅` is codetecting if and only if `C` is a groupoid;
* define predicates `is_separator`, `is_coseparator`, `is_detector` and `is_codetector` as the
  singleton counterparts to the definitions for sets above and restate the above results in this
  situation;
* show that `G` is a separator if and only if `coyoneda.obj (op G)` is faithful (and the dual);
* show that `G` is a detector if and only if `coyoneda.obj (op G)` reflects isomorphisms (and the
  dual).

## Future work

* We currently don't have any examples yet.
* We will want typeclasses `has_separator C` and similar.
* To state the Special Adjoint Functor Theorem, we will need to be able to talk about *small*
  separating sets.

-/

universes w v u

open category_theory.limits opposite

namespace category_theory
variables {C : Type u} [category.{v} C]

/-- We say that `𝒢` is a separating set if the functors `C(G, -)` for `G ∈ 𝒢` are collectively
    faithful, i.e., if `h ≫ f = h ≫ g` for all `h` with domain in `𝒢` implies `f = g`. -/
def is_separating (𝒢 : set C) : Prop :=
∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ (G ∈ 𝒢) (h : G ⟶ X), h ≫ f = h ≫ g) → f = g

/-- We say that `𝒢` is a coseparating set if the functors `C(-, G)` for `G ∈ 𝒢` are collectively
    faithful, i.e., if `f ≫ h = g ≫ h` for all `h` with codomain in `𝒢` implies `f = g`. -/
def is_coseparating (𝒢 : set C) : Prop :=
∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ (G ∈ 𝒢) (h : Y ⟶ G), f ≫ h = g ≫ h) → f = g

/-- We say that `𝒢` is a detecting set if the functors `C(G, -)` collectively reflect isomorphisms,
    i.e., if any `h` with domain in `𝒢` uniquely factors through `f`, then `f` is an isomorphism. -/
def is_detecting (𝒢 : set C) : Prop :=
∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G ∈ 𝒢) (h : G ⟶ Y), ∃! (h' : G ⟶ X), h' ≫ f = h) → is_iso f

/-- We say that `𝒢` is a codetecting set if the functors `C(-, G)` collectively reflect
    isomorphisms, i.e., if any `h` with codomain in `G` uniquely factors through `f`, then `f` is
    an isomorphism. -/
def is_codetecting (𝒢 : set C) : Prop :=
∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ (G ∈ 𝒢) (h : X ⟶ G), ∃! (h' : Y ⟶ G), f ≫ h' = h) → is_iso f

section dual

lemma is_separating_op_iff (𝒢 : set C) : is_separating 𝒢.op ↔ is_coseparating 𝒢 :=
begin
  refine ⟨λ h𝒢 X Y f g hfg, _, λ h𝒢 X Y f g hfg, _⟩,
  { refine quiver.hom.op_inj (h𝒢 _ _ (λ G hG h, quiver.hom.unop_inj _)),
    simpa only [unop_comp, quiver.hom.unop_op] using hfg _ (set.mem_op.1 hG) _ },
  { refine quiver.hom.unop_inj (h𝒢 _ _ (λ G hG h, quiver.hom.op_inj _)),
    simpa only [op_comp, quiver.hom.op_unop] using hfg _ (set.op_mem_op.2 hG) _ }
end

lemma is_coseparating_op_iff (𝒢 : set C) : is_coseparating 𝒢.op ↔ is_separating 𝒢 :=
begin
  refine ⟨λ h𝒢 X Y f g hfg, _, λ h𝒢 X Y f g hfg, _⟩,
  { refine quiver.hom.op_inj (h𝒢 _ _ (λ G hG h, quiver.hom.unop_inj _)),
    simpa only [unop_comp, quiver.hom.unop_op] using hfg _ (set.mem_op.1 hG) _ },
  { refine quiver.hom.unop_inj (h𝒢 _ _ (λ G hG h, quiver.hom.op_inj _)),
    simpa only [op_comp, quiver.hom.op_unop] using hfg _ (set.op_mem_op.2 hG) _ }
end

lemma is_coseparating_unop_iff (𝒢 : set Cᵒᵖ) : is_coseparating 𝒢.unop ↔ is_separating 𝒢 :=
by rw [← is_separating_op_iff, set.unop_op]

lemma is_separating_unop_iff (𝒢 : set Cᵒᵖ) : is_separating 𝒢.unop ↔ is_coseparating 𝒢 :=
by rw [← is_coseparating_op_iff, set.unop_op]

lemma is_detecting_op_iff (𝒢 : set C) : is_detecting 𝒢.op ↔ is_codetecting 𝒢 :=
begin
  refine ⟨λ h𝒢 X Y f hf, _, λ h𝒢 X Y f hf, _⟩,
  { refine (is_iso_op_iff _).1 (h𝒢 _ (λ G hG h, _)),
    obtain ⟨t, ht, ht'⟩ := hf (unop G) (set.mem_op.1 hG) h.unop,
    exact ⟨t.op, quiver.hom.unop_inj ht, λ y hy,
      quiver.hom.unop_inj (ht' _ (quiver.hom.op_inj hy))⟩ },
  { refine (is_iso_unop_iff _).1 (h𝒢 _ (λ G hG h, _)),
    obtain ⟨t, ht, ht'⟩ := hf (op G) (set.op_mem_op.2 hG) h.op,
    refine ⟨t.unop, quiver.hom.op_inj ht, λ y hy, quiver.hom.op_inj (ht' _ _)⟩,
    exact quiver.hom.unop_inj (by simpa only using hy) }
end

lemma is_codetecting_op_iff (𝒢 : set C) : is_codetecting 𝒢.op ↔ is_detecting 𝒢 :=
begin
  refine ⟨λ h𝒢 X Y f hf, _, λ h𝒢 X Y f hf, _⟩,
  { refine (is_iso_op_iff _).1 (h𝒢 _ (λ G hG h, _)),
    obtain ⟨t, ht, ht'⟩ := hf (unop G) (set.mem_op.1 hG) h.unop,
    exact ⟨t.op, quiver.hom.unop_inj ht, λ y hy,
      quiver.hom.unop_inj (ht' _ (quiver.hom.op_inj hy))⟩ },
  { refine (is_iso_unop_iff _).1 (h𝒢 _ (λ G hG h, _)),
    obtain ⟨t, ht, ht'⟩ := hf (op G) (set.op_mem_op.2 hG) h.op,
    refine ⟨t.unop, quiver.hom.op_inj ht, λ y hy, quiver.hom.op_inj (ht' _ _)⟩,
    exact quiver.hom.unop_inj (by simpa only using hy) }
end

lemma is_detecting_unop_iff (𝒢 : set Cᵒᵖ) : is_detecting 𝒢.unop ↔ is_codetecting 𝒢 :=
by rw [← is_codetecting_op_iff, set.unop_op]

lemma is_codetecting_unop_iff {𝒢 : set Cᵒᵖ} : is_codetecting 𝒢.unop ↔ is_detecting 𝒢 :=
by rw [← is_detecting_op_iff, set.unop_op]

end dual

lemma is_detecting.is_separating [has_equalizers C] {𝒢 : set C} (h𝒢 : is_detecting 𝒢) :
  is_separating 𝒢 :=
λ X Y f g hfg,
  have is_iso (equalizer.ι f g), from h𝒢 _ (λ G hG h, equalizer.exists_unique _ (hfg _ hG _)),
  by exactI eq_of_epi_equalizer

section
local attribute [instance] has_equalizers_opposite

lemma is_codetecting.is_coseparating [has_coequalizers C] {𝒢 : set C} :
  is_codetecting 𝒢 → is_coseparating 𝒢 :=
by simpa only [← is_separating_op_iff, ← is_detecting_op_iff] using is_detecting.is_separating

end

lemma is_separating.is_detecting [balanced C] {𝒢 : set C} (h𝒢 : is_separating 𝒢) :
  is_detecting 𝒢 :=
begin
  intros X Y f hf,
  refine (is_iso_iff_mono_and_epi _).2 ⟨⟨λ Z g h hgh, h𝒢 _ _ (λ G hG i, _)⟩, ⟨λ Z g h hgh, _⟩⟩,
  { obtain ⟨t, -, ht⟩ := hf G hG (i ≫ g ≫ f),
    rw [ht (i ≫ g) (category.assoc _ _ _), ht (i ≫ h) (hgh.symm ▸ category.assoc _ _ _)] },
  { refine h𝒢 _ _ (λ G hG i, _),
    obtain ⟨t, rfl, -⟩ := hf G hG i,
    rw [category.assoc, hgh, category.assoc] }
end

section
local attribute [instance] balanced_opposite

lemma is_coseparating.is_codetecting [balanced C] {𝒢 : set C} :
  is_coseparating 𝒢 → is_codetecting 𝒢 :=
by simpa only [← is_detecting_op_iff, ← is_separating_op_iff] using is_separating.is_detecting

end

lemma is_detecting_iff_is_separating [has_equalizers C] [balanced C] (𝒢 : set C) :
  is_detecting 𝒢 ↔ is_separating 𝒢 :=
⟨is_detecting.is_separating, is_separating.is_detecting⟩

lemma is_codetecting_iff_is_coseparating [has_coequalizers C] [balanced C] {𝒢 : set C} :
  is_codetecting 𝒢 ↔ is_coseparating 𝒢 :=
⟨is_codetecting.is_coseparating, is_coseparating.is_codetecting⟩

section mono

lemma is_separating.mono {𝒢 : set C} (h𝒢 : is_separating 𝒢) {ℋ : set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) :
  is_separating ℋ :=
λ X Y f g hfg, h𝒢 _ _ $ λ G hG h, hfg _ (h𝒢ℋ hG) _

lemma is_coseparating.mono {𝒢 : set C} (h𝒢 : is_coseparating 𝒢) {ℋ : set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) :
  is_coseparating ℋ :=
λ X Y f g hfg, h𝒢 _ _ $ λ G hG h, hfg _ (h𝒢ℋ hG) _

lemma is_detecting.mono {𝒢 : set C} (h𝒢 : is_detecting 𝒢) {ℋ : set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) :
  is_detecting ℋ :=
λ X Y f hf, h𝒢 _ $ λ G hG h, hf _ (h𝒢ℋ hG) _

lemma is_codetecting.mono {𝒢 : set C} (h𝒢 : is_codetecting 𝒢) {ℋ : set C} (h𝒢ℋ : 𝒢 ⊆ ℋ) :
  is_codetecting ℋ :=
λ X Y f hf, h𝒢 _ $ λ G hG h, hf _ (h𝒢ℋ hG) _

end mono

section empty

lemma thin_of_is_separating_empty (h : is_separating (∅ : set C)) (X Y : C) :
  subsingleton (X ⟶ Y) :=
⟨λ f g, h _ _ $ λ G, false.elim⟩

lemma is_separating_empty_of_thin [∀ X Y : C, subsingleton (X ⟶ Y)] : is_separating (∅ : set C) :=
λ X Y f g hfg, subsingleton.elim _ _

lemma thin_of_is_coseparating_empty (h : is_coseparating (∅ : set C)) (X Y : C) :
  subsingleton (X ⟶ Y) :=
⟨λ f g, h _ _ $ λ G, false.elim⟩

lemma is_coseparating_empty_of_thin [∀ X Y : C, subsingleton (X ⟶ Y)] :
  is_coseparating (∅ : set C) :=
λ X Y f g hfg, subsingleton.elim _ _

lemma groupoid_of_is_detecting_empty (h : is_detecting (∅ : set C)) {X Y : C} (f : X ⟶ Y) :
  is_iso f :=
h _ $ λ G, false.elim

lemma is_detecting_empty_of_groupoid [∀ {X Y : C} (f : X ⟶ Y), is_iso f] :
  is_detecting (∅ : set C) :=
λ X Y f hf, infer_instance

lemma groupoid_of_is_codetecting_empty (h : is_codetecting (∅ : set C)) {X Y : C} (f : X ⟶ Y) :
  is_iso f :=
h _ $ λ G, false.elim

lemma is_codetecting_empty_of_groupoid [∀ {X Y : C} (f : X ⟶ Y), is_iso f] :
  is_codetecting (∅ : set C) :=
λ X Y f hf, infer_instance

end empty

lemma is_separating_iff_epi (𝒢 : set C)
  [Π (A : C), has_coproduct (λ f : Σ G : 𝒢, (G : C) ⟶ A, (f.1 : C))] :
  is_separating 𝒢 ↔ ∀ A : C, epi (sigma.desc (@sigma.snd 𝒢 (λ G, (G : C) ⟶ A))) :=
begin
  refine ⟨λ h A, ⟨λ Z u v huv, h _ _ (λ G hG f, _)⟩, λ h X Y f g hh, _⟩,
  { simpa using (sigma.ι (λ f : Σ G : 𝒢, (G : C) ⟶ A, (f.1 : C)) ⟨⟨G, hG⟩, f⟩) ≫= huv },
  { haveI := h X,
    refine (cancel_epi (sigma.desc (@sigma.snd 𝒢 (λ G, (G : C) ⟶ X)))).1 (colimit.hom_ext (λ j, _)),
    simpa using hh j.as.1.1 j.as.1.2 j.as.2 }
end

lemma is_coseparating_iff_mono (𝒢 : set C)
  [Π (A : C), has_product (λ f : Σ G : 𝒢, A ⟶ (G : C), (f.1 : C))] :
  is_coseparating 𝒢 ↔ ∀ A : C, mono (pi.lift (@sigma.snd 𝒢 (λ G, A ⟶ (G : C)))) :=
begin
  refine ⟨λ h A, ⟨λ Z u v huv, h _ _ (λ G hG f, _)⟩, λ h X Y f g hh, _⟩,
  { simpa using huv =≫ (pi.π (λ f : Σ G : 𝒢, A ⟶ (G : C), (f.1 : C)) ⟨⟨G, hG⟩, f⟩) },
  { haveI := h Y,
    refine (cancel_mono (pi.lift (@sigma.snd 𝒢 (λ G, Y ⟶ (G : C))))).1 (limit.hom_ext (λ j, _)),
    simpa using hh j.as.1.1 j.as.1.2 j.as.2 }
end

section well_powered

namespace subobject

lemma eq_of_le_of_is_detecting {𝒢 : set C} (h𝒢 : is_detecting 𝒢) {X : C} (P Q : subobject X)
  (h₁ : P ≤ Q) (h₂ : ∀ (G ∈ 𝒢) {f : G ⟶ X}, Q.factors f → P.factors f) : P = Q :=
begin
  suffices : is_iso (of_le _ _ h₁),
  { exactI le_antisymm h₁ (le_of_comm (inv (of_le _ _ h₁)) (by simp)) },
  refine h𝒢 _ (λ G hG f, _),
  have : P.factors (f ≫ Q.arrow) := h₂ _ hG ((factors_iff _ _).2 ⟨_, rfl⟩),
  refine ⟨factor_thru _ _ this, _, λ g (hg : g ≫ _ = f), _⟩,
  { simp only [← cancel_mono Q.arrow, category.assoc, of_le_arrow, factor_thru_arrow] },
  { simp only [← cancel_mono (subobject.of_le _ _ h₁), ← cancel_mono Q.arrow, hg,
      category.assoc, of_le_arrow, factor_thru_arrow] }
end

lemma inf_eq_of_is_detecting [has_pullbacks C] {𝒢 : set C} (h𝒢 : is_detecting 𝒢) {X : C}
  (P Q : subobject X) (h : ∀ (G ∈ 𝒢) {f : G ⟶ X}, P.factors f → Q.factors f) : P ⊓ Q = P :=
eq_of_le_of_is_detecting h𝒢 _ _ _root_.inf_le_left (λ G hG f hf, (inf_factors _).2 ⟨hf, h _ hG hf⟩)

lemma eq_of_is_detecting [has_pullbacks C] {𝒢 : set C} (h𝒢 : is_detecting 𝒢) {X : C}
  (P Q : subobject X) (h : ∀ (G ∈ 𝒢) {f : G ⟶ X}, P.factors f ↔ Q.factors f) : P = Q :=
calc P = P ⊓ Q : eq.symm $ inf_eq_of_is_detecting h𝒢 _ _ $ λ G hG f hf, (h G hG).1 hf
   ... = Q ⊓ P : inf_comm
   ... = Q     : inf_eq_of_is_detecting h𝒢 _ _ $ λ G hG f hf, (h G hG).2 hf

end subobject

/-- A category with pullbacks and a small detecting set is well-powered. -/
lemma well_powered_of_is_detecting [has_pullbacks C] {𝒢 : set C} [small.{v} 𝒢]
  (h𝒢 : is_detecting 𝒢) : well_powered C :=
⟨λ X, @small_of_injective _ _ _ (λ P : subobject X, { f : Σ G : 𝒢, G.1 ⟶ X | P.factors f.2 }) $
  λ P Q h, subobject.eq_of_is_detecting h𝒢 _ _ (by simpa [set.ext_iff] using h)⟩

end well_powered

/-- We say that `G` is a separator if the functor `C(G, -)` is faithful. -/
def is_separator (G : C) : Prop :=
is_separating ({G} : set C)

/-- We say that `G` is a coseparator if the functor `C(-, G)` is faithful. -/
def is_coseparator (G : C) : Prop :=
is_coseparating ({G} : set C)

/-- We say that `G` is a detector if the functor `C(G, -)` reflects isomorphisms. -/
def is_detector (G : C) : Prop :=
is_detecting ({G} : set C)

/-- We say that `G` is a codetector if the functor `C(-, G)` reflects isomorphisms. -/
def is_codetector (G : C) : Prop :=
is_codetecting ({G} : set C)

section dual

lemma is_separator_op_iff (G : C) : is_separator (op G) ↔ is_coseparator G :=
by rw [is_separator, is_coseparator, ← is_separating_op_iff, set.singleton_op]

lemma is_coseparator_op_iff (G : C) : is_coseparator (op G) ↔ is_separator G :=
by rw [is_separator, is_coseparator, ← is_coseparating_op_iff, set.singleton_op]

lemma is_coseparator_unop_iff (G : Cᵒᵖ) : is_coseparator (unop G) ↔ is_separator G :=
by rw [is_separator, is_coseparator, ← is_coseparating_unop_iff, set.singleton_unop]

lemma is_separator_unop_iff (G : Cᵒᵖ) : is_separator (unop G) ↔ is_coseparator G :=
by rw [is_separator, is_coseparator, ← is_separating_unop_iff, set.singleton_unop]

lemma is_detector_op_iff (G : C) : is_detector (op G) ↔ is_codetector G :=
by rw [is_detector, is_codetector, ← is_detecting_op_iff, set.singleton_op]

lemma is_codetector_op_iff (G : C) : is_codetector (op G) ↔ is_detector G :=
by rw [is_detector, is_codetector, ← is_codetecting_op_iff, set.singleton_op]

lemma is_codetector_unop_iff (G : Cᵒᵖ) : is_codetector (unop G) ↔ is_detector G :=
by rw [is_detector, is_codetector, ← is_codetecting_unop_iff, set.singleton_unop]

lemma is_detector_unop_iff (G : Cᵒᵖ) : is_detector (unop G) ↔ is_codetector G :=
by rw [is_detector, is_codetector, ← is_detecting_unop_iff, set.singleton_unop]

end dual

lemma is_detector.is_separator [has_equalizers C] {G : C} : is_detector G → is_separator G :=
is_detecting.is_separating

lemma is_codetector.is_coseparator [has_coequalizers C] {G : C} :
  is_codetector G → is_coseparator G :=
is_codetecting.is_coseparating

lemma is_separator.is_detector [balanced C] {G : C} : is_separator G → is_detector G :=
is_separating.is_detecting

lemma is_cospearator.is_codetector [balanced C] {G : C} : is_coseparator G → is_codetector G :=
is_coseparating.is_codetecting

lemma is_separator_def (G : C) :
  is_separator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
⟨λ hG X Y f g hfg, hG _ _ $ λ H hH h, by { obtain rfl := set.mem_singleton_iff.1 hH, exact hfg h },
 λ hG X Y f g hfg, hG _ _ $ λ h, hfg _ (set.mem_singleton _) _⟩

lemma is_separator.def {G : C} :
  is_separator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : G ⟶ X, h ≫ f = h ≫ g) → f = g :=
(is_separator_def _).1

lemma is_coseparator_def (G : C) :
  is_coseparator G ↔ ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
⟨λ hG X Y f g hfg, hG _ _ $ λ H hH h, by { obtain rfl := set.mem_singleton_iff.1 hH, exact hfg h },
 λ hG X Y f g hfg, hG _ _ $ λ h, hfg _ (set.mem_singleton _) _⟩

lemma is_coseparator.def {G : C} :
  is_coseparator G → ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : Y ⟶ G, f ≫ h = g ≫ h) → f = g :=
(is_coseparator_def _).1

lemma is_detector_def (G : C) :
  is_detector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → is_iso f :=
⟨λ hG X Y f hf, hG _ $ λ H hH h, by { obtain rfl := set.mem_singleton_iff.1 hH, exact hf h },
 λ hG X Y f hf, hG _ $ λ h, hf _ (set.mem_singleton _) _⟩

lemma is_detector.def {G : C} :
  is_detector G → ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : G ⟶ Y, ∃! h', h' ≫ f = h) → is_iso f :=
(is_detector_def _).1

lemma is_codetector_def (G : C) :
  is_codetector G ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : X ⟶ G, ∃! h', f ≫ h' = h) → is_iso f :=
⟨λ hG X Y f hf, hG _ $ λ H hH h, by { obtain rfl := set.mem_singleton_iff.1 hH, exact hf h },
 λ hG X Y f hf, hG _ $ λ h, hf _ (set.mem_singleton _) _⟩

lemma is_codetector.def {G : C} :
  is_codetector G → ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ h : X ⟶ G, ∃! h', f ≫ h' = h) → is_iso f :=
(is_codetector_def _).1

lemma is_separator_iff_faithful_coyoneda_obj (G : C) :
  is_separator G ↔ faithful (coyoneda.obj (op G)) :=
⟨λ hG, ⟨λ X Y f g hfg, hG.def _ _ (congr_fun hfg)⟩,
 λ h, (is_separator_def _).2 $ λ X Y f g hfg,
  by exactI (coyoneda.obj (op G)).map_injective (funext hfg)⟩

lemma is_coseparator_iff_faithful_yoneda_obj (G : C) :
  is_coseparator G ↔ faithful (yoneda.obj G) :=
⟨λ hG, ⟨λ X Y f g hfg, quiver.hom.unop_inj (hG.def _ _ (congr_fun hfg))⟩,
 λ h, (is_coseparator_def _).2 $ λ X Y f g hfg, quiver.hom.op_inj $
  by exactI (yoneda.obj G).map_injective (funext hfg)⟩

lemma is_separator_iff_epi (G : C) [Π A : C, has_coproduct (λ (f : G ⟶ A), G)] :
  is_separator G ↔ ∀ (A : C), epi (sigma.desc (λ (f : G ⟶ A), f)) :=
begin
  rw is_separator_def,
  refine ⟨λ h A, ⟨λ Z u v huv, h _ _ (λ i, _)⟩, λ h X Y f g hh, _⟩,
  { simpa using (sigma.ι _ i) ≫= huv },
  { haveI := h X,
    refine (cancel_epi (sigma.desc (λ (f : G ⟶ X), f))).1 (colimit.hom_ext (λ j, _)),
    simpa using hh j.as }
end

lemma is_coseparator_iff_mono (G : C) [Π A : C, has_product (λ (f : A ⟶ G), G)] :
  is_coseparator G ↔ ∀ (A : C), mono (pi.lift (λ (f : A ⟶ G), f)) :=
begin
  rw is_coseparator_def,
  refine ⟨λ h A, ⟨λ Z u v huv, h _ _ (λ i, _)⟩, λ h X Y f g hh, _⟩,
  { simpa using huv =≫ (pi.π _ i) },
  { haveI := h Y,
    refine (cancel_mono (pi.lift (λ (f : Y ⟶ G), f))).1 (limit.hom_ext (λ j, _)),
    simpa using hh j.as }
end

section zero_morphisms
variables [has_zero_morphisms C]

lemma is_separator_coprod (G H : C) [has_binary_coproduct G H] :
  is_separator (G ⨿ H) ↔ is_separating ({G, H} : set C) :=
begin
  refine ⟨λ h X Y u v huv, _, λ h, (is_separator_def _).2 (λ X Y u v huv, h _ _ (λ Z hZ g, _))⟩,
  { refine h.def _ _ (λ g, coprod.hom_ext _ _),
    { simpa using huv G (by simp) (coprod.inl ≫ g) },
    { simpa using huv H (by simp) (coprod.inr ≫ g) } },
  { simp only [set.mem_insert_iff, set.mem_singleton_iff] at hZ,
    unfreezingI { rcases hZ with rfl|rfl },
    { simpa using coprod.inl ≫= huv (coprod.desc g 0) },
    { simpa using coprod.inr ≫= huv (coprod.desc 0 g) } }
end

lemma is_separator_coprod_of_is_separator_left (G H : C) [has_binary_coproduct G H]
  (hG : is_separator G) : is_separator (G ⨿ H) :=
(is_separator_coprod _ _).2 $ is_separating.mono hG $ by simp

lemma is_separator_coprod_of_is_separator_right (G H : C) [has_binary_coproduct G H]
  (hH : is_separator H) : is_separator (G ⨿ H) :=
(is_separator_coprod _ _).2 $ is_separating.mono hH $ by simp

lemma is_separator_sigma {β : Type w} (f : β → C) [has_coproduct f] :
  is_separator (∐ f) ↔ is_separating (set.range f) :=
begin
  refine ⟨λ h X Y u v huv, _, λ h, (is_separator_def _).2 (λ X Y u v huv, h _ _ (λ Z hZ g, _))⟩,
  { refine h.def _ _ (λ g, colimit.hom_ext (λ b, _)),
    simpa using huv (f b.as) (by simp) (colimit.ι (discrete.functor f) _ ≫ g) },
  { obtain ⟨b, rfl⟩ := set.mem_range.1 hZ,
    classical,
    simpa using sigma.ι f b ≫= huv (sigma.desc (pi.single b g)) }
end

lemma is_separator_sigma_of_is_separator {β : Type w} (f : β → C) [has_coproduct f]
  (b : β) (hb : is_separator (f b)) : is_separator (∐ f) :=
(is_separator_sigma _).2 $ is_separating.mono hb $ by simp

lemma is_coseparator_prod (G H : C) [has_binary_product G H] :
  is_coseparator (G ⨯ H) ↔ is_coseparating ({G, H} : set C) :=
begin
  refine ⟨λ h X Y u v huv, _, λ h, (is_coseparator_def _).2 (λ X Y u v huv, h _ _ (λ Z hZ g, _))⟩,
  { refine h.def _ _ (λ g, prod.hom_ext _ _),
    { simpa using huv G (by simp) (g ≫ limits.prod.fst) },
    { simpa using huv H (by simp) (g ≫ limits.prod.snd) } },
  { simp only [set.mem_insert_iff, set.mem_singleton_iff] at hZ,
    unfreezingI { rcases hZ with rfl|rfl },
    { simpa using huv (prod.lift g 0) =≫ limits.prod.fst },
    { simpa using huv (prod.lift 0 g) =≫ limits.prod.snd } }
end

lemma is_coseparator_prod_of_is_coseparator_left (G H : C) [has_binary_product G H]
  (hG : is_coseparator G) : is_coseparator (G ⨯ H) :=
(is_coseparator_prod _ _).2 $ is_coseparating.mono hG $ by simp

lemma is_coseparator_prod_of_is_coseparator_right (G H : C) [has_binary_product G H]
  (hH : is_coseparator H) : is_coseparator (G ⨯ H) :=
(is_coseparator_prod _ _).2 $ is_coseparating.mono hH $ by simp

lemma is_coseparator_pi {β : Type w} (f : β → C) [has_product f] :
  is_coseparator (∏ f) ↔ is_coseparating (set.range f) :=
begin
  refine ⟨λ h X Y u v huv, _, λ h, (is_coseparator_def _).2 (λ X Y u v huv, h _ _ (λ Z hZ g, _))⟩,
  { refine h.def _ _ (λ g, limit.hom_ext (λ b, _)),
    simpa using huv (f b.as) (by simp) (g ≫ limit.π (discrete.functor f) _ ) },
  { obtain ⟨b, rfl⟩ := set.mem_range.1 hZ,
    classical,
    simpa using huv (pi.lift (pi.single b g)) =≫ pi.π f b }
end

lemma is_coseparator_pi_of_is_coseparator {β : Type w} (f : β → C) [has_product f]
  (b : β) (hb : is_coseparator (f b)) : is_coseparator (∏ f) :=
(is_coseparator_pi _).2 $ is_coseparating.mono hb $ by simp

end zero_morphisms

lemma is_detector_iff_reflects_isomorphisms_coyoneda_obj (G : C) :
  is_detector G ↔ reflects_isomorphisms (coyoneda.obj (op G)) :=
begin
  refine ⟨λ hG, ⟨λ X Y f hf, hG.def _ (λ h, _)⟩, λ h, (is_detector_def _).2 (λ X Y f hf, _)⟩,
  { rw [is_iso_iff_bijective, function.bijective_iff_exists_unique] at hf,
    exact hf h },
  { suffices : is_iso ((coyoneda.obj (op G)).map f),
    { exactI @is_iso_of_reflects_iso _ _ _ _ _ _ _ (coyoneda.obj (op G)) _ h },
    rwa [is_iso_iff_bijective, function.bijective_iff_exists_unique] }
end

lemma is_codetector_iff_reflects_isomorphisms_yoneda_obj (G : C) :
  is_codetector G ↔ reflects_isomorphisms (yoneda.obj G) :=
begin
  refine ⟨λ hG, ⟨λ X Y f hf, _ ⟩, λ h, (is_codetector_def _).2 (λ X Y f hf, _)⟩,
  { refine (is_iso_unop_iff _).1 (hG.def _ _),
    rwa [is_iso_iff_bijective, function.bijective_iff_exists_unique] at hf },
  { rw ← is_iso_op_iff,
    suffices : is_iso ((yoneda.obj G).map f.op),
    { exactI @is_iso_of_reflects_iso _ _ _ _ _ _ _ (yoneda.obj G) _ h },
    rwa [is_iso_iff_bijective, function.bijective_iff_exists_unique] }
end

lemma well_powered_of_is_detector [has_pullbacks C] (G : C) (hG : is_detector G) :
  well_powered C :=
well_powered_of_is_detecting hG

end category_theory
