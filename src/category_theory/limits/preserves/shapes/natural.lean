/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes
import category_theory.is_connected
import category_theory.connected_components
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.preserves.shapes.products
import category_theory.limits.preserves.shapes.terminal
import category_theory.conj
import category_theory.adjunction.opposites

/-!
# Preserving limits from naturality

The definition of `G : C ⥤ D` preserving limits of shape `J` can equivalently be stated as:
for any `F : J ⥤ C`, the canonical morphism `G.obj (limit F) ⟶ limit (G ⋙ F)` is an isomorphism.
Note that this morphism is natural in `F`.
However in certain cases, to show `G` preserves limits of shape `J`, it suffices to show there are
natural isomorphisms `G.obj (limit F) ⟶ limit (G ⋙ F)`: in particular these might not be the
canonical isomorphisms.
For instance, there are cases where the natural isomorphisms are not unique, but their mere
existence is enough to establish that the canonical morphism is isomorphic.

At the moment, this file shows only a special case (Theorem 3.3 of [Winskel]):
If `G` preserves the terminal object and there are natural isomorphisms `G (X ⨯ Y) ≅ G X ⨯ G Y`,
then `G` preserves binary products.

## References

* [Winskel] https://www.cl.cam.ac.uk/~gw104/preservation.pdf
-/

noncomputable theory

universes v u₁ u₂

namespace category_theory
open category limits

variables {C : Type u₁} [category.{v} C]
variables {D : Type u₂} [category.{v} D]
variables (G : C ⥤ D)

namespace preserves_connected

variables {J : Type v} [small_category J] [is_connected J]

@[simps {rhs_md := semireducible}]
def same_cones {c : C} : yoneda.obj c ≅ ((functor.const J).obj c).cones :=
nat_iso.of_components
  (λ d, (equiv_of_fully_faithful (functor.const J : C ⥤ _)).to_iso)
  (λ d d' f, rfl)

instance constant_has_limit {c : C} : has_limit ((functor.const J).obj c) :=
has_limit.mk ⟨_, is_limit.of_nat_iso same_cones⟩

def limit_constant_iso (c : C) : limit ((functor.const J).obj c) ≅ c :=
limit.iso_limit_cone ⟨_, is_limit.of_nat_iso same_cones⟩

-- Note the LHS does not depend on `j`, so this shouldn't be a simp lemma
lemma limit_constant_iso_hom {c : C} (j : J) :
  (limit_constant_iso c).hom = limit.π ((functor.const J).obj c) j :=
nat_trans_from_is_connected _ (classical.arbitrary J) j

@[reassoc, simp]
lemma limit_constant_iso_inv (c : C) (j : J) :
  (limit_constant_iso c).inv ≫ limit.π ((functor.const J).obj c) j = 𝟙 c :=
limit.lift_π _ _

variables [has_limits_of_shape J C] [has_limits_of_shape J D]

def preserves_of_shape_of_natural_iso (θ : Π (K : J ⥤ C), G.obj (limit K) ≅ limit (K ⋙ G))
  (hθ : ∀ {K K'} α, (θ K).hom ≫ lim_map (whisker_right α G) = G.map (lim_map α) ≫ (θ K').hom) :
  preserves_limits_of_shape J G :=
{ preserves_limit := λ K,
  { preserves := λ c t,
    begin
      apply (limit.is_limit (K ⋙ G)).of_point_iso,
      let i₂ : limit ((functor.const J).obj c.X) ≅ limit K :=
        limit_constant_iso c.X ≪≫ t.cone_point_unique_up_to_iso (limit.is_limit _),
      have q : i₂.hom = lim_map c.π,
      { ext j,
        simp [limit_constant_iso_hom j] },
      let i₁ : (functor.const J).obj (G.obj c.X) ≅ (functor.const J).obj c.X ⋙ G :=
        nat_iso.of_components (λ _, iso.refl _) (by tidy),
      let i := (limit_constant_iso (G.obj c.X)).symm ≪≫ has_limit.iso_of_nat_iso i₁,
      have z : limit.lift (K ⋙ G) (G.map_cone c) = i.hom ≫ lim_map (whisker_right c.π G : _),
      { ext1,
        simp [limit_constant_iso_inv_assoc (G.obj c.X)] },
      specialize hθ c.π,
      rw ← iso.eq_inv_comp at hθ,
      dsimp,
      rw [z, hθ, ← q],
      apply_instance,
    end } }

end preserves_connected

namespace preserves_product

variables {K : Type v}
variables [has_products_of_shape K C]
variables [preserves_limit (functor.empty _) G]

open_locale classical

def fixed (k : K) (X : C) {T : C} (hT : is_terminal T) :
  ∏ (λ (k' : K), if k' = k then X else T) ≅ X :=
{ hom :=
  begin
    apply pi.π (λ (k' : K), if k' = k then X else T) k ≫ _,
    apply eq_to_hom,
    simp,
  end,
  inv := pi.lift (λ k', if h : k' = k then eq_to_hom (by simp [h]) else hT.from X ≫ eq_to_hom (by simp [h])),
  hom_inv_id' :=
  begin
    ext,
    simp only [limit.lift_π, assoc, id_comp, fan.mk_π_app],
    by_cases (j = k),
    { cases h,
      simp },
    { simp only [h, if_true, eq_self_iff_true, if_false, dif_neg, not_false_iff],
      rw [← assoc, ← assoc, ← is_iso.eq_comp_inv],
      apply hT.hom_ext }
  end }

variables [has_products_of_shape K D] [has_terminal C] [has_terminal D]

def preserves_pair_of_natural_isomorphism {X Y : C} (s : Π (f : K → C), G.obj (∏ f) ≅ ∏ (G.obj ∘ f))
  (w : ∀ {f g : K → C} (α : Π k, f k ⟶ g k), (s f).hom ≫ pi.map (λ k, G.map (α k) : _) = G.map (pi.map α) ≫ (s g).hom)
  (f : K → C) :
  preserves_limit (discrete.functor f) G :=
begin
  refine preserves_limit_of_preserves_limit_cone (product_is_product _) _,
  apply (is_limit_map_cone_fan_mk_equiv _ _ _).symm _,
  -- This isomorphism is the main idea of the proof: we use an isomorphism which is (in general)
  -- not the identity isomorphism, but it gives nice naturality
  let s_ : Π (k : K), G.obj (f k) ≅ G.obj (f k),
  { intro k,
    apply G.map_iso (fixed k (f k) terminal_is_terminal).symm ≪≫ s _ ≪≫ _,
    apply _ ≪≫ fixed k (G.obj (f k)) (is_limit_of_has_terminal_of_preserves_limit G),
    apply pi.map_iso,
    intro k',
    apply eq_to_iso (apply_ite G.obj _ _ _) },
  have hs₁ : ∀ (k : K), (s f).hom ≫ pi.π _ k = G.map (pi.π _ k) ≫ (s_ k).hom,
  { intro k,
    let α : Π k', f k' ⟶ (if k' = k then f k else ⊤_ C),
    { intro k',
      refine (if h : k' = k then _ else _),
      { apply eq_to_hom,
        simp [h] },
      { apply terminal.from (f k') ≫ eq_to_hom _,
        simp [h] } },
    have q : α k = eq_to_hom _ := dif_pos rfl,
    have := w α =≫ pi.π _ k,
    simp only [discrete.nat_trans_app, lim_map_π, assoc] at this,
    conv at this {to_lhs, congr, skip, congr, skip, rw [q, eq_to_hom_map] },
    rw [← assoc, ← is_iso.eq_comp_inv] at this,
    rw this,
    clear this,
    rw [assoc, assoc],
    change _ = G.map _ ≫ G.map _ ≫ _ ≫ lim_map _ ≫ _,
    rw ← G.map_comp_assoc,
    congr' 2,
    { change _ = _ ≫ (fixed _ _ _).inv,
      rw iso.eq_comp_inv,
      change lim_map _ ≫ limit.π _ _ ≫ _ = _,
      rw lim_map_π_assoc,
      change pi.π f k ≫ α k ≫ _ = _,
      rw [q, eq_to_hom_trans, eq_to_hom_refl, comp_id] },
    { change pi.π _ _ ≫ _ = lim_map _ ≫ _ ≫ _,
      rw lim_map_π_assoc,
      simpa } },
  dsimp,
  refine is_limit.of_iso_limit
            ((is_limit.postcompose_inv_equiv _ _).symm
              (product_is_product (G.obj ∘ f))) _,
  { apply discrete.nat_iso,
    apply s_ },
  { symmetry,
    refine cones.ext (s f) _,
    intro k,
    change G.map _ = (s f).hom ≫ pi.π _ _ ≫ (s_ k).inv,
    rw [← assoc, iso.eq_comp_inv],
    apply (hs₁ k).symm }
end

end preserves_product

namespace preserves_pair

variables [has_finite_products C] [has_finite_products D]
variables [preserves_limit (functor.empty _) G]

@[simps]
def left_unit (X : C) {T : C} (hT : is_terminal T) : T ⨯ X ≅ X :=
{ hom := limits.prod.snd,
  inv := prod.lift (hT.from X) (𝟙 X),
  hom_inv_id' := prod.hom_ext (hT.hom_ext _ _) (by simp) }

@[simps]
def right_unit (X : C) {T : C} (hT : is_terminal T) : X ⨯ T ≅ X :=
{ hom := limits.prod.fst,
  inv := prod.lift (𝟙 X) (hT.from X),
  hom_inv_id' := prod.hom_ext (by simp) (hT.hom_ext _ _) }

/--
If we have natural isomorphisms `G (X ⨯ Y) ≅ G X ⨯ G Y` and `G` preserves the terminal objects,
then `G` preserves binary products. In particular, the isomorphisms do not need to be the canonical
isomorphisms, but using the terminal object we can show binary products are preserved.

Proof is taken from Theorem 3.3 of [Winskel].
-/
def preserves_pair_of_natural_isomorphism {X Y : C} (s : Π X Y, G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y)
  (w : ∀ {X X' Y Y'} (f) (g), (s X Y).hom ≫ limits.prod.map (G.map f) (G.map g) = G.map (limits.prod.map f g) ≫ (s X' Y').hom) :
  preserves_limit (pair X Y) G :=
begin
  refine preserves_limit_of_preserves_limit_cone (prod_is_prod _ _) _,
  apply (is_limit_map_cone_binary_fan_equiv _ _ _).symm _,
  -- This isomorphism is the main idea of the proof: we use an isomorphism which is (in general)
  -- not the identity isomorphism, but it gives nice naturality
  let s₁ : G.obj X ≅ G.obj X,
  { apply _ ≪≫ s X (⊤_ C) ≪≫ _,
    { apply G.map_iso (right_unit _ terminal_is_terminal).symm },
    { apply right_unit _ (is_limit_of_has_terminal_of_preserves_limit G) } },
  let s₂ : G.obj Y ≅ G.obj Y,
  { apply _ ≪≫ s (⊤_ C) Y ≪≫ _,
    { apply G.map_iso (left_unit _ terminal_is_terminal).symm },
    { apply left_unit _ (is_limit_of_has_terminal_of_preserves_limit G) } },
  have hs₁ : (s X Y).hom ≫ limits.prod.fst = G.map limits.prod.fst ≫ s₁.hom,
  { have := w (𝟙 X) (terminal.from Y) =≫ limits.prod.fst,
    simp only [functor.map_id, assoc, comp_id, limits.prod.map_fst] at this,
    change _ = _ ≫ G.map (right_unit X terminal_is_terminal).inv ≫ _ ≫ _,
    rw [this, ← G.map_comp_assoc],
    congr' 2,
    rw iso.eq_comp_inv,
    simp },
  have hs₂ : (s X Y).hom ≫ limits.prod.snd = G.map limits.prod.snd ≫ s₂.hom,
  { have := w (terminal.from X) (𝟙 Y) =≫ limits.prod.snd,
    simp only [functor.map_id, assoc, limits.prod.map_snd, comp_id] at this,
    change _ = _ ≫ G.map (left_unit _ terminal_is_terminal).inv ≫ _ ≫ _,
    rw [this, ← G.map_comp_assoc],
    congr' 2,
    rw iso.eq_comp_inv,
    simp },
  refine is_limit.of_iso_limit
            ((is_limit.postcompose_inv_equiv _ _).symm
              (prod_is_prod (G.obj X) (G.obj Y))) _,
  { apply discrete.nat_iso _,
    intro j,
    cases j,
    { apply s₁ },
    { apply s₂ } },
  { symmetry,
    refine cones.ext (s _ _) _,
    rintro (_ | _),
    { change G.map _ = (s X Y).hom ≫ limits.prod.fst ≫ s₁.inv,
      rw [reassoc_of hs₁, iso.hom_inv_id, comp_id] },
    { change G.map _ = _ ≫ limits.prod.snd ≫ s₂.inv,
      rw [reassoc_of hs₂, iso.hom_inv_id, comp_id] } }
end

end preserves_pair

section general

variables {J : Type v} [small_category J]
variables (K : decomposed J ⥤ C)
-- open_locale classical

@[simps]
def assemble_cone
  (γ : Π (j : connected_components J), cone (inclusion j ⋙ K : component j ⥤ C))
  (c : fan (λ j, (γ j).X)) :
  cone K :=
{ X := c.X,
  π :=
  { app :=
    begin
      rintro ⟨j₁, j₂⟩,
      apply c.π.app j₁ ≫ (γ j₁).π.app j₂,
    end,
    naturality' :=
    begin
      rintro ⟨j₁, X⟩ ⟨_, _⟩ ⟨_, _, Y, f⟩,
      change 𝟙 c.X ≫ c.π.app _ ≫ _ = (c.π.app _ ≫ _) ≫ _,
      rw [id_comp, assoc, ← (γ j₁).w f],
      refl,
    end } }

-- Prop 4.2 of the paper
-- I used a different proof since this one seemed more direct to do: it proves the exact same thing.
def assemble_limit
  (γ : Π (j : connected_components J), cone (inclusion j ⋙ K : component j ⥤ C))
  (hγ : Π (j : connected_components J), is_limit (γ j))
  (c : fan (λ j, (γ j).X))
  (hc : is_limit c) :
  is_limit (assemble_cone K γ c) :=
{ lift := λ s,
  begin
    apply hc.lift (fan.mk _ (λ j, _)),
    apply (hγ j).lift ⟨_, λ X, _, _⟩,
    apply s.π.app ⟨j, X⟩,
    rintro X Y f,
    change 𝟙 s.X ≫ _ = _ ≫ K.map _,
    rw [id_comp, s.w],
  end,
  fac' :=
  begin
    rintro s ⟨j, X⟩,
    change _ ≫ _ ≫ _ = _,
    rw [hc.fac_assoc, fan.mk_π_app, (hγ j).fac],
  end,
  uniq' :=
  begin
    intros s m w,
    apply hc.hom_ext,
    intro j,
    rw [hc.fac, fan.mk_π_app],
    apply (hγ j).hom_ext,
    intro X,
    rw (hγ j).fac,
    change (_ ≫ _) ≫ _ = s.π.app _,
    rw [assoc],
    apply w ⟨j, X⟩,
  end }

open_locale classical

def right (j) : (decomposed J ⥤ C) ⥤ component j ⥤ C :=
(whiskering_left _ _ _).obj (inclusion _)

def plus_obj' {T : C} (hT : is_terminal T) (j : connected_components J) :
  (component j ⥤ C) → decomposed J ⥤ C :=
λ H, sigma.desc (λ k,
{ obj := λ X,
  begin
    refine dite (j = k) _ _,
    { intro h,
      refine H.obj _,
      subst h,
      apply X },
    { intro h,
      apply T }
  end,
  map := λ X Y f,
  begin
    refine dite (j = k) _ _,
    { intro h,
      subst h,
      exact eq_to_hom (by simp) ≫ H.map f ≫ eq_to_hom (by simp) },
    { intro h,
      refine eq_to_hom (by simp [h]) }
  end,
  map_id' := λ X,
  begin
    by_cases (j = k),
    { subst h,
      simp },
    { simp [h] }
  end,
  map_comp' := λ X Y Z f g,
  begin
    by_cases (j = k),
    { subst h,
      simp },
    { simp [h] }
  end })

def plus_hom_equiv {T : C} (hT : is_terminal T) (j : connected_components J)
  (G : decomposed J ⥤ C) (H : component j ⥤ C) :
  ((right j).obj G ⟶ H) ≃ (G ⟶ (plus_obj' hT j) H) :=
begin
  apply equiv.trans _ (thingy G _).symm.to_equiv,
  refine ⟨_, _, _, _⟩,
  { intros f i,
    apply _ ≫ (sigma.incl_desc _ _).inv,
    refine dite (j = i) _ _,
    { intro h,
      subst h,
      apply f ≫ _,
      refine ⟨_, _⟩,
      { intro Z,
        exact eq_to_hom (by simp) },
      { intros Z₁ Z₂ g,
        simp } },
    { intro h,
      refine ⟨_, _⟩,
      { intro Z,
        apply hT.from (G.obj ⟨_, Z⟩) ≫ eq_to_hom _,
        simp [h] },
      { intros X Y f,
        dsimp,
        simp only [h, eq_self_iff_true, eq_to_hom_trans, dif_neg, assoc, not_false_iff],
        rw ← assoc,
        congr' 1,
        apply hT.hom_ext } } },
  { intro f,
    apply f j ≫ (sigma.incl_desc _ _).hom ≫ _,
    refine ⟨_, _⟩,
    { intro X,
      apply eq_to_hom _,
      simp },
    { intros X Y g,
      simp } },
  { intros f,
    ext i,
    simp },
  { intro f,
    ext i X,
    by_cases (j = i),
    { subst h,
      rw dif_pos rfl,
      dsimp,
      simp,
      apply comp_id },
    { rw dif_neg h,
      change (_ ≫ _) ≫ _ = _,
      rw ← is_iso.eq_comp_inv,
      rw ← is_iso.eq_comp_inv,
      apply hT.hom_ext } }
end.

lemma plus_symm_natural {T : C} (hT : is_terminal T) (j : connected_components J)
  (G G' : decomposed J ⥤ C) (H : component j ⥤ C)
  (f : G' ⟶ G) (g : G ⟶ (plus_obj' hT j) H) :
  (right j).map f ≫ (plus_hom_equiv hT j _ _).symm g = (plus_hom_equiv hT j _ _).symm (f ≫ g) :=
begin
  ext X,
  symmetry,
  apply assoc,
end

def plus' {T : C} (hT : is_terminal T) (j : connected_components J) :
  (component j ⥤ C) ⥤ decomposed J ⥤ C :=
begin
  refine adjunction.right_adjoint_of_equiv (plus_hom_equiv hT j) _,
  intros G' G H f g,
  rw ← equiv.eq_symm_apply,
  ext X,
  rw ← plus_symm_natural,
  simp,
end

def plus_adjunction {T : C} (hT : is_terminal T) (j : connected_components J) :
  right j ⊣ plus' hT j :=
adjunction.adjunction_of_equiv_right _ _

/--
The isomorphism of cones between H and H+.
This shows that if `C` has limits of shape `J` and a terminal object, it has limits of shape of
any connected component of `J`.
-/
def plus_cones {T : C} (hT : is_terminal T) (j : connected_components J) (H : component j ⥤ C) :
  H.cones ≅ ((plus' hT j).obj H).cones :=
begin
  apply nat_iso.of_components _ _,
  { intro X,
    refine equiv.to_iso _,
    refine equiv.trans _ ((plus_adjunction hT j).hom_equiv _ _),
    exact equiv.refl _ },
  { intros X Y f,
    ext Z W,
    sorry }
end

-- def extra_plus_adjunction
def extra_plus_cones [preserves_limit (functor.empty C) G] {T : C} (hT : is_terminal T)
  (j : connected_components J) (H : component j ⥤ C) :
  (H ⋙ G).cones ≅ ((plus' hT j).obj H ⋙ G).cones :=
begin
  have i : (plus' hT j).obj H ⋙ G ≅ (plus' (is_terminal_obj_of_is_terminal G T hT) _).obj (H ⋙ G),
  { apply sigma.nat_iso,
    intro k,
    apply _ ≪≫ (sigma.incl_desc _ _).symm,
    apply (functor.associator _ _ _).symm ≪≫ _,
    refine (iso_whisker_right (sigma.incl_desc _ _) _) ≪≫ _,
    apply nat_iso.of_components _ _,
    { intro X,
      apply eq_to_iso,
      dsimp,
      rw apply_dite G.obj },
    { intros X Y f,
      dsimp,
      split_ifs,
      { subst h,
        simpa },
      { simp } } },
  refine nat_iso.of_components _ _,
  intro X,
  apply equiv.to_iso,
  change (_ ⟶ _) ≃ (_ ⟶ _),
  apply equiv.trans _ (iso.hom_congr (iso.refl _) i.symm),

end

def diag : (discrete (connected_components J) ⥤ C) ⥤ (decomposed J ⥤ C) :=
{ obj := λ F, sigma.desc $ λ j, (functor.const _).obj (F.obj j),
  map := λ F₁ F₂ α,
  { app := λ X, α.app X.1,
    naturality' :=
    begin
      rintro _ _ ⟨i, X, Y, f⟩,
      dsimp,
      simp,
    end } }

end general

end category_theory
