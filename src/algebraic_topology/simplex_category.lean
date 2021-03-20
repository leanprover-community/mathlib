/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/

import order.category.NonemptyFinLinOrd
import category_theory.skeletal
import data.finset.sort
import tactic.linarith

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `fin (n+1)` to `fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `simplex_category` and `simplex_category.hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `simplex_category.mk` creates an object of `simplex_category` out of a natural number.
  Use the notation `[n]` in the `simplicial` locale.
2. `simplex_category.len` gives the "length" of an object of `simplex_category`, as a natural.
3. `simplex_category.hom.mk` makes a morphism out of a monotone map between `fin`'s.
4. `simplex_category.hom.to_preorder_hom` gives the underlying monotone map associated to a
  term of `simplex_category.hom`.

-/

universe variables u

open category_theory

/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `fin (n+1) → fin (m+1)`
-/
@[derive inhabited, irreducible]
def simplex_category := ulift.{u} ℕ

namespace simplex_category

section
local attribute [semireducible] simplex_category

-- TODO: Make `mk` irreducible.
/-- Interpet a natural number as an object of the simplex category. -/
def mk (n : ℕ) : simplex_category := ulift.up n

localized "notation `[`n`]` := simplex_category.mk n" in simplicial

-- TODO: Make `len` irreducible.
/-- The length of an object of `simplex_category`. -/
def len (n : simplex_category) : ℕ := n.down

@[ext] lemma ext (a b : simplex_category) : a.len = b.len → a = b := ulift.ext a b
@[simp] lemma len_mk (n : ℕ) : [n].len = n := rfl
@[simp] lemma mk_len (n : simplex_category) : [n.len] = n := by {cases n, refl}

/-- Morphisms in the simplex_category. -/
@[irreducible, nolint has_inhabited_instance]
protected def hom (a b : simplex_category.{u}) : Type u :=
ulift (fin (a.len + 1) →ₘ fin (b.len + 1))

namespace hom

local attribute [semireducible] simplex_category.hom

/-- Make a moprhism in `simplex_category` from a monotone map of fin's. -/
def mk {a b : simplex_category.{u}} (f : fin (a.len + 1) →ₘ fin (b.len + 1)) :
  simplex_category.hom a b :=
ulift.up f

/-- Recover the monotone map from a morphism in the simplex category. -/
def to_preorder_hom {a b : simplex_category.{u}} (f : simplex_category.hom a b) :
  fin (a.len + 1) →ₘ fin (b.len + 1) :=
ulift.down f

@[ext] lemma ext {a b : simplex_category.{u}} (f g : simplex_category.hom a b) :
  f.to_preorder_hom = g.to_preorder_hom → f = g := ulift.ext _ _

@[simp] lemma mk_to_preorder_hom {a b : simplex_category.{u}}
  (f : simplex_category.hom a b) : mk (f.to_preorder_hom) = f :=
by {cases f, refl}

@[simp] lemma to_preorder_hom_mk {a b : simplex_category.{u}}
  (f : fin (a.len + 1) →ₘ fin (b.len + 1)) : (mk f).to_preorder_hom = f :=
by simp [to_preorder_hom, mk]

lemma mk_to_preorder_hom_apply {a b : simplex_category.{u}}
  (f : fin (a.len + 1) →ₘ fin (b.len + 1)) (i : fin (a.len + 1)) :
  (mk f).to_preorder_hom i = f i := rfl

/-- Identity morphisms of `simplex_category`. -/
@[simp]
def id (a : simplex_category.{u}) :
  simplex_category.hom a a :=
mk preorder_hom.id

/-- Composition of morphisms of `simplex_category`. -/
@[simp]
def comp {a b c : simplex_category.{u}} (f : simplex_category.hom b c)
  (g : simplex_category.hom a b) : simplex_category.hom a c :=
mk $ f.to_preorder_hom.comp g.to_preorder_hom

end hom

@[simps]
instance small_category : small_category.{u} simplex_category :=
{ hom := λ n m, simplex_category.hom n m,
  id := λ m, simplex_category.hom.id _,
  comp := λ _ _ _ f g, simplex_category.hom.comp g f, }

/--
Make a morphism `[n] ⟶ [m]` from a monotone map between fin's.
This is useful for constructing morphisms beetween `[n]` directly
without identifying `n` with `[n].len`.
-/
@[simp]
def mk_hom {n m : ℕ} (f : (fin (n+1)) →ₘ (fin (m+1))) : [n] ⟶ [m] :=
simplex_category.hom.mk f

end

open_locale simplicial

section generators
/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/

/-- The `i`-th face map from `[n]` to `[n+1]` -/
def δ {n} (i : fin (n+2)) : [n] ⟶ [n+1] :=
mk_hom (fin.succ_above i).to_preorder_hom

/-- The `i`-th degeneracy map from `[n+1]` to `[n]` -/
def σ {n} (i : fin (n+1)) : [n+1] ⟶ [n] := mk_hom
{ to_fun := fin.pred_above i,
  monotone' := fin.pred_above_right_monotone i }

/-- The generic case of the first simplicial identity -/
lemma δ_comp_δ {n} {i j : fin (n+2)} (H : i ≤ j) :
  δ i ≫ δ j.succ = δ j ≫ δ i.cast_succ :=
begin
  ext k,
  dsimp [δ, fin.succ_above],
  simp only [order_embedding.to_preorder_hom_coe,
    order_embedding.coe_of_strict_mono,
    function.comp_app,
    simplex_category.hom.to_preorder_hom_mk,
    preorder_hom.comp_to_fun],
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  split_ifs; { simp at *; linarith },
end

/-- The special case of the first simplicial identity -/
lemma δ_comp_δ_self {n} {i : fin (n+2)} : δ i ≫ δ i.cast_succ = δ i ≫ δ i.succ :=
begin
  ext j,
  dsimp [δ, fin.succ_above],
  simp only [order_embedding.to_preorder_hom_coe,
    order_embedding.coe_of_strict_mono,
    function.comp_app,
    simplex_category.hom.to_preorder_hom_mk,
    preorder_hom.comp_to_fun],
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  split_ifs; { simp at *; linarith },
end

/-- The second simplicial identity -/
lemma δ_comp_σ_of_le {n} {i : fin (n+2)} {j : fin (n+1)} (H : i ≤ j.cast_succ) :
  δ i.cast_succ ≫ σ j.succ = σ j ≫ δ i :=
begin
  ext k,
  suffices : ite (j.succ.cast_succ < ite (k < i) k.cast_succ k.succ)
    (ite (k < i) (k:ℕ) (k + 1) - 1) (ite (k < i) k (k + 1)) =
      ite ((if h : (j:ℕ) < k
        then k.pred (by { rintro rfl, exact nat.not_lt_zero _ h })
        else k.cast_lt (by { cases j, cases k, simp only [len_mk], linarith })).cast_succ < i)
          (ite (j.cast_succ < k) (k - 1) k) (ite (j.cast_succ < k) (k - 1) k + 1),
  { dsimp [δ, σ, fin.succ_above, fin.pred_above],
    simpa [fin.pred_above] with push_cast },
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  simp only [subtype.mk_le_mk, fin.cast_succ_mk] at H,
  dsimp, simp only [if_congr, subtype.mk_lt_mk, dif_ctx_congr],
  split_ifs,
  -- Most of the goals can now be handled by `linarith`,
  -- but we have to deal with two of them by hand.
  swap 8,
  { exact (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) ‹_›)).symm, },
  swap 7,
  { have : k ≤ i := nat.le_of_pred_lt ‹_›, linarith, },
  -- Hope for the best from `linarith`:
  all_goals { try { refl <|> simp at * }; linarith, },
end

/-- The first part of the third simplicial identity -/
lemma δ_comp_σ_self {n} {i : fin (n+1)} :
  δ i.cast_succ ≫ σ i = 𝟙 [n] :=
begin
  ext j,
  suffices : ite (fin.cast_succ i < ite (j < i) (fin.cast_succ j) j.succ)
    (ite (j < i) (j:ℕ) (j + 1) - 1) (ite (j < i) j (j + 1)) = j,
  { dsimp [δ, σ, fin.succ_above, fin.pred_above], simpa [fin.pred_above] with push_cast },
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  dsimp, simp only [if_congr, subtype.mk_lt_mk],
  split_ifs; { simp at *; linarith, },
end

/-- The second part of the third simplicial identity -/
lemma δ_comp_σ_succ {n} {i : fin (n+1)} :
  δ i.succ ≫ σ i = 𝟙 [n] :=
begin
  ext j,
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  dsimp [δ, σ, fin.succ_above, fin.pred_above],
  simp [fin.pred_above] with push_cast,
  split_ifs; { simp at *; linarith, },
end

/-- The fourth simplicial identity -/
lemma δ_comp_σ_of_gt {n} {i : fin (n+2)} {j : fin (n+1)} (H : j.cast_succ < i) :
  δ i.succ ≫ σ j.cast_succ = σ j ≫ δ i :=
begin
  ext k,
  dsimp [δ, σ, fin.succ_above, fin.pred_above],
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  simp only [subtype.mk_lt_mk, fin.cast_succ_mk] at H,
  suffices : ite (_ < ite (k < i + 1) _ _) _ _ =
    ite _ (ite (j < k) (k - 1) k) (ite (j < k) (k - 1) k + 1),
  { simpa [apply_dite fin.cast_succ, fin.pred_above] with push_cast, },
  split_ifs,
  -- Most of the goals can now be handled by `linarith`,
  -- but we have to deal with three of them by hand.
  swap 2,
  { simp only [subtype.mk_lt_mk] at h_1,
    simp only [not_lt] at h_2,
    simp only [self_eq_add_right, one_ne_zero],
    exact lt_irrefl (k - 1) (lt_of_lt_of_le
      (nat.pred_lt (ne_of_lt (lt_of_le_of_lt (zero_le _) h_1)).symm)
      (le_trans (nat.le_of_lt_succ h) h_2)) },
  swap 4,
  { simp only [subtype.mk_lt_mk] at h_1,
    simp only [not_lt] at h,
    simp only [nat.add_succ_sub_one, add_zero],
    exfalso,
    exact lt_irrefl _ (lt_of_le_of_lt (nat.le_pred_of_lt (nat.lt_of_succ_le h)) h_3), },
  swap 4,
  { simp only [subtype.mk_lt_mk] at h_1,
    simp only [not_lt] at h_3,
    simp only [nat.add_succ_sub_one, add_zero],
    exact (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) h_2)).symm, },
  -- Hope for the best from `linarith`:
  all_goals { simp at h_1 h_2 ⊢; linarith, },
end

local attribute [simp] fin.pred_mk

/-- The fifth simplicial identity -/
lemma σ_comp_σ {n} {i j : fin (n+1)} (H : i ≤ j) :
  σ i.cast_succ ≫ σ j = σ j.succ ≫ σ i :=
begin
  ext k,
  dsimp [σ, fin.pred_above],
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  simp only [subtype.mk_le_mk] at H,
  -- At this point `simp with push_cast` makes good progress, but neither `simp?` nor `squeeze_simp`
  -- return usable sets of lemmas.
  -- To avoid using a non-terminal simp, we make a `suffices` statement indicating the shape
  -- of the goal we're looking for, and then use `simpa with push_cast`.
  -- I'm not sure this is actually much more robust that a non-terminal simp.
  suffices : ite (_ < dite (i < k) _ _) _ _ =
    ite (_ < dite (j + 1 < k) _ _) _ _,
  { simpa [fin.pred_above] with push_cast, },
  split_ifs,
  -- `split_ifs` created 12 goals.
  -- Most of them are dealt with `by simp at *; linarith`,
  -- but we pull out two harder ones to do by hand.
  swap 3,
  { simp only [not_lt] at h_2,
    exact false.elim
    (lt_irrefl (k - 1)
      (lt_of_lt_of_le (nat.pred_lt (id (ne_of_lt (lt_of_le_of_lt (zero_le i) h)).symm))
        (le_trans h_2 (nat.succ_le_of_lt h_1)))) },
  swap 3,
  { simp only [subtype.mk_lt_mk, not_lt] at h_1,
    exact false.elim
    (lt_irrefl j (lt_of_lt_of_le (nat.pred_lt_pred (nat.succ_ne_zero j) h_2) h_1)) },
  -- Deal with the rest automatically.
  all_goals { simp at *; linarith, },
end

end generators

section skeleton


/-- The functor that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
def skeletal_functor : simplex_category ⥤ NonemptyFinLinOrd :=
{ obj := λ a, NonemptyFinLinOrd.of $ ulift (fin (a.len + 1)),
  map := λ a b f,
    ⟨λ i, ulift.up (f.to_preorder_hom i.down), λ i j h, f.to_preorder_hom.monotone h⟩ }

lemma skeletal : skeletal simplex_category :=
λ X Y ⟨I⟩,
begin
  suffices : fintype.card (fin (X.len+1)) = fintype.card (fin (Y.len+1)),
  { ext, simpa },
  { apply fintype.card_congr,
    refine equiv.ulift.symm.trans (((skeletal_functor ⋙ forget _).map_iso I).to_equiv.trans _),
    apply equiv.ulift }
end

namespace skeletal_functor

instance : full skeletal_functor :=
{ preimage := λ a b f, simplex_category.hom.mk ⟨λ i, (f (ulift.up i)).down, λ i j h, f.monotone h⟩,
  witness' := by { intros m n f, dsimp at *, ext1 ⟨i⟩, ext1, refl } }

instance : faithful skeletal_functor :=
{ map_injective' := λ m n f g h,
  begin
    ext1, ext1 i, apply ulift.up.inj,
    change (skeletal_functor.map f) ⟨i⟩ = (skeletal_functor.map g) ⟨i⟩,
    rw h,
  end }

instance : ess_surj skeletal_functor :=
{ mem_ess_image := λ X, ⟨mk (fintype.card X - 1 : ℕ), ⟨begin
    have aux : fintype.card X = fintype.card X - 1 + 1,
    { exact (nat.succ_pred_eq_of_pos $ fintype.card_pos_iff.mpr ⟨⊥⟩).symm, },
    let f := mono_equiv_of_fin X aux,
    have hf := (finset.univ.order_emb_of_fin aux).strict_mono,
    refine
    { hom := ⟨λ i, f i.down, _⟩,
      inv := ⟨λ i, ⟨f.symm i⟩, _⟩,
      hom_inv_id' := _,
      inv_hom_id' := _ },
    { rintro ⟨i⟩ ⟨j⟩ h, show f i ≤ f j, exact hf.monotone h, },
    { intros i j h, show f.symm i ≤ f.symm j, rw ← hf.le_iff_le,
      show f (f.symm i) ≤ f (f.symm j), simpa only [order_iso.apply_symm_apply], },
    { ext1 ⟨i⟩, ext1, exact f.symm_apply_apply i },
    { ext1 i, exact f.apply_symm_apply i },
  end⟩⟩,}

noncomputable instance is_equivalence : is_equivalence skeletal_functor :=
equivalence.equivalence_of_fully_faithfully_ess_surj skeletal_functor

end skeletal_functor

/-- The equivalence that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletal_equivalence : simplex_category ≌ NonemptyFinLinOrd :=
functor.as_equivalence skeletal_functor

end skeleton

/--
`simplex_category` is a skeleton of `NonemptyFinLinOrd`.
-/
noncomputable
def is_skeleton_of : is_skeleton_of NonemptyFinLinOrd simplex_category skeletal_functor :=
{ skel := skeletal,
  eqv := skeletal_functor.is_equivalence }

/-- The truncated simplex category. -/
@[derive small_category]
def truncated (n : ℕ) := {a : simplex_category // a.len ≤ n}

namespace truncated

instance {n} : inhabited (truncated n) := ⟨⟨[0],by simp⟩⟩

/--
The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
@[derive [full, faithful]]
def inclusion {n : ℕ} : simplex_category.truncated n ⥤ simplex_category :=
full_subcategory_inclusion _

end truncated

end simplex_category
