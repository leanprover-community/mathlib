/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Junyan Xu
-/
import algebraic_geometry.sheafed_space
import topology.sheaves.punit
import topology.sheaves.stalks
import category_theory.preadditive.injective

/-!
# Skyscraper (pre)sheaves

A skyscraper (pre)sheaf `𝓕 : (pre)sheaf C X` is the (pre)sheaf with value `A` at point `p₀` that is
supported only at open sets contain `p₀`, i.e. `𝓕(U) = A` if `p₀ ∈ U` and `𝓕(U) = *` if `p₀ ∉ U`
where `*` is a terminal object of `C`. In terms of stalks, `𝓕` is supported at all specializations
of `p₀`, i.e. if `p₀ ⤳ x` then `𝓕ₓ ≅ A` and if `¬ p₀ ⤳ x` then `𝓕ₓ ≅ *`.

## Main definitions

* `skyscraper_presheaf`: `skyscraper_presheaf p₀ A` is the skyscraper presheaf at point `p₀` with
  value `A`.
* `skyscraper_sheaf`: the skyscraper presheaf satisfies the sheaf condition.

## Main statements

* `skyscraper_presheaf_stalk_of_specializes`: if `y ∈ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `A`.
* `skyscraper_presheaf_stalk_of_not_specializes`: if `y ∉ closure {p₀}` then the stalk of
  `skyscraper_presheaf p₀ A` at `y` is `*` the terminal object.

TODO: generalize universe level when calculating stalks, after generalizing universe level of stalk.
-/

noncomputable theory

open topological_space Top category_theory category_theory.limits opposite

universes u v w

variables {X : Top.{u}} (p₀ : X) [Π (U : opens X), decidable (p₀ ∈ U)]

section

variables {C : Type v} [category.{w} C] [has_terminal C] (A : C)

/--
A skyscraper presheaf is a presheaf supported at a single point: if `p₀ ∈ X` is a specified
point, then the skyscraper presheaf `𝓕` with value `A` is defined by `U ↦ A` if `p₀ ∈ U` and
`U ↦ *` if `p₀ ∉ A` where `*` is some terminal object.
-/
@[simps] def skyscraper_presheaf : presheaf C X :=
{ obj := λ U, if p₀ ∈ unop U then A else terminal C,
  map := λ U V i, if h : p₀ ∈ unop V
    then eq_to_hom $ by erw [if_pos h, if_pos (le_of_hom i.unop h)]
    else ((if_neg h).symm.rec terminal_is_terminal).from _,
  map_id' := λ U, (em (p₀ ∈ U.unop)).elim (λ h, dif_pos h)
    (λ h, ((if_neg h).symm.rec terminal_is_terminal).hom_ext _ _),
  map_comp' := λ U V W iVU iWV,
  begin
    by_cases hW : p₀ ∈ unop W,
    { have hV : p₀ ∈ unop V := le_of_hom iWV.unop hW,
      simp only [dif_pos hW, dif_pos hV, eq_to_hom_trans] },
    { rw [dif_neg hW], apply ((if_neg hW).symm.rec terminal_is_terminal).hom_ext }
  end }

lemma skyscraper_presheaf_eq_pushforward
  [hd : Π (U : opens (Top.of punit.{u+1})), decidable (punit.star ∈ U)] :
  skyscraper_presheaf p₀ A =
  continuous_map.const (Top.of punit) p₀ _* skyscraper_presheaf punit.star A :=
by convert_to @skyscraper_presheaf X p₀
  (λ U, hd $ (opens.map $ continuous_map.const _ p₀).obj U) C _ A _ = _; congr <|> refl

/--
Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps] def skyscraper_presheaf_functor.map' {a b : C} (f : a ⟶ b) :
  skyscraper_presheaf p₀ a ⟶ skyscraper_presheaf p₀ b :=
{ app := λ U, if h : p₀ ∈ U.unop
    then eq_to_hom (if_pos h) ≫ f ≫ eq_to_hom (if_pos h).symm
    else ((if_neg h).symm.rec terminal_is_terminal).from _,
  naturality' := λ U V i,
  begin
    simp only [skyscraper_presheaf_map], by_cases hV : p₀ ∈ V.unop,
    { have hU : p₀ ∈ U.unop := le_of_hom i.unop hV, split_ifs,
      simpa only [eq_to_hom_trans_assoc, category.assoc, eq_to_hom_trans], },
    { apply ((if_neg hV).symm.rec terminal_is_terminal).hom_ext, },
  end }

lemma skyscraper_presheaf_functor.map'_id {a : C} :
  skyscraper_presheaf_functor.map' p₀ (𝟙 a) = 𝟙 _ :=
begin
  ext1, ext1, simp only [skyscraper_presheaf_functor.map'_app, nat_trans.id_app], split_ifs,
  { simp only [category.id_comp, category.comp_id, eq_to_hom_trans, eq_to_hom_refl], },
  { apply ((if_neg h).symm.rec terminal_is_terminal).hom_ext, },
end

lemma skyscraper_presheaf_functor.map'_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
  skyscraper_presheaf_functor.map' p₀ (f ≫ g) =
  skyscraper_presheaf_functor.map' p₀ f ≫ skyscraper_presheaf_functor.map' p₀ g :=
begin
  ext1, ext1, simp only [skyscraper_presheaf_functor.map'_app, nat_trans.comp_app], split_ifs,
  { simp only [category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp], },
  { apply ((if_neg h).symm.rec terminal_is_terminal).hom_ext, },
end

/--
Taking skyscraper presheaf at a point is functorial: `c ↦ skyscraper p₀ c` defines a functor by
sending every `f : a ⟶ b` to the natural transformation `α` defined as: `α(U) = f : a ⟶ b` if
`p₀ ∈ U` and the unique morphism to a terminal object in `C` if `p₀ ∉ U`.
-/
@[simps] def skyscraper_presheaf_functor : C ⥤ presheaf C X :=
{ obj := skyscraper_presheaf p₀,
  map := λ _ _, skyscraper_presheaf_functor.map' p₀,
  map_id' := λ _, skyscraper_presheaf_functor.map'_id p₀,
  map_comp' := λ _ _ _, skyscraper_presheaf_functor.map'_comp p₀ }

end

section

-- In this section, we calculate the stalks for skyscraper presheaves.
-- We need to restrict universe level.

variables {C : Type v} [category.{u} C] (A : C) [has_terminal C]

/--
The cocone at `A` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∈ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone_of_specializes {y : X} (h : p₀ ⤳ y) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ A) :=
{ X := A,
  ι := { app := λ U, eq_to_hom $ if_pos $ h.mem_open U.unop.1.2 U.unop.2,
    naturality' := λ U V inc, begin
      change dite _ _ _ ≫ _ = _, rw dif_pos,
      { erw [category.comp_id, eq_to_hom_trans], refl },
      { exact h.mem_open V.unop.1.2 V.unop.2 },
    end } }

/--
The cocone at `A` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∈ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_is_colimit_of_specializes
  {y : X} (h : p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone_of_specializes p₀ A h) :=
{ desc := λ c, eq_to_hom (if_pos trivial).symm ≫ c.ι.app (op ⊤),
  fac' := λ c U, begin
    rw ← c.w (hom_of_le $ (le_top : unop U ≤ _)).op,
    change _ ≫ _ ≫ dite _ _ _ ≫ _ = _,
    rw dif_pos,
    { simpa only [skyscraper_presheaf_cocone_of_specializes_ι_app,
        eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp] },
    { exact h.mem_open U.unop.1.2 U.unop.2 },
  end,
  uniq' := λ c f h, by rw [← h, skyscraper_presheaf_cocone_of_specializes_ι_app,
    eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp] }

/--
If `y ∈ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is `A`.
-/
noncomputable def skyscraper_presheaf_stalk_of_specializes [has_colimits C]
  {y : X} (h : p₀ ⤳ y) : (skyscraper_presheaf p₀ A).stalk y ≅ A :=
colimit.iso_colimit_cocone ⟨_, skyscraper_presheaf_cocone_is_colimit_of_specializes p₀ A h⟩

/--
The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∉ closure {p₀}`
-/
@[simps] def skyscraper_presheaf_cocone (y : X) :
  cocone ((open_nhds.inclusion y).op ⋙ skyscraper_presheaf p₀ A) :=
{ X := terminal C,
  ι :=
  { app := λ U, terminal.from _,
    naturality' := λ U V inc, terminal_is_terminal.hom_ext _ _ } }

/--
The cocone at `*` for the stalk functor of `skyscraper_presheaf p₀ A` when `y ∉ closure {p₀}` is a
colimit
-/
noncomputable def skyscraper_presheaf_cocone_is_colimit_of_not_specializes
  {y : X} (h : ¬p₀ ⤳ y) : is_colimit (skyscraper_presheaf_cocone p₀ A y) :=
let h1 : ∃ (U : open_nhds y), p₀ ∉ U.1 :=
  let ⟨U, ho, h₀, hy⟩ := not_specializes_iff_exists_open.mp h in ⟨⟨⟨U, ho⟩, h₀⟩, hy⟩ in
{ desc := λ c, eq_to_hom (if_neg h1.some_spec).symm ≫ c.ι.app (op h1.some),
  fac' := λ c U, begin
    change _ = c.ι.app (op U.unop),
    simp only [← c.w (hom_of_le $ @inf_le_left _ _ h1.some U.unop).op,
      ← c.w (hom_of_le $ @inf_le_right _ _ h1.some U.unop).op, ← category.assoc],
    congr' 1,
    refine ((if_neg _).symm.rec terminal_is_terminal).hom_ext _ _,
    exact λ h, h1.some_spec h.1,
  end,
  uniq' := λ c f H, begin
    rw [← category.id_comp f, ← H, ← category.assoc],
    congr' 1, apply terminal_is_terminal.hom_ext,
  end }

/--
If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is isomorphic to a
terminal object.
-/
noncomputable def skyscraper_presheaf_stalk_of_not_specializes [has_colimits C]
  {y : X} (h : ¬p₀ ⤳ y) : (skyscraper_presheaf p₀ A).stalk y ≅ terminal C :=
colimit.iso_colimit_cocone ⟨_, skyscraper_presheaf_cocone_is_colimit_of_not_specializes _ A h⟩

/--
If `y ∉ closure {p₀}`, then the stalk of `skyscraper_presheaf p₀ A` at `y` is a terminal object
-/
def skyscraper_presheaf_stalk_of_not_specializes_is_terminal
  [has_colimits C] {y : X} (h : ¬p₀ ⤳ y) : is_terminal ((skyscraper_presheaf p₀ A).stalk y) :=
is_terminal.of_iso terminal_is_terminal $ (skyscraper_presheaf_stalk_of_not_specializes _ _ h).symm

lemma skyscraper_presheaf_is_sheaf [has_products.{u} C] : (skyscraper_presheaf p₀ A).is_sheaf :=
by classical; exact (presheaf.is_sheaf_iso_iff
  (eq_to_iso $ skyscraper_presheaf_eq_pushforward p₀ A)).mpr
  (sheaf.pushforward_sheaf_of_sheaf _ (presheaf.is_sheaf_on_punit_of_is_terminal _
  (by { dsimp, rw if_neg, exact terminal_is_terminal, exact set.not_mem_empty punit.star })))

/--
The skyscraper presheaf supported at `p₀` with value `A` is the sheaf that assigns `A` to all opens
`U` that contain `p₀` and assigns `*` otherwise.
-/
def skyscraper_sheaf [has_products.{u} C] : sheaf C X :=
⟨skyscraper_presheaf p₀ A, skyscraper_presheaf_is_sheaf _ _⟩

end
