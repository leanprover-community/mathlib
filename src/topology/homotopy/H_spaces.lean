/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

-- import analysis.complex.circle
import topology.compact_open
import topology.homotopy.basic
import topology.homotopy.path

universes u v w

noncomputable theory

open_locale unit_interval

namespace continuous_map

lemma continuous_to_C_iff_uncurry (X : Type u) (Y : Type v) (Z : Type w) [topological_space X]
  [topological_space Y] [locally_compact_space Y] [topological_space Z] (g : X → C(Y, Z)) :
  continuous g ↔ continuous (λ p : X × Y, g p.1 p.2) :=  iff.intro
(λ h, continuous_uncurry_of_continuous ⟨_, h⟩) (λ h, continuous_of_continuous_uncurry _ h)

-- lemma continuous_to_C_iff_curry (X Y Z : Type u) [topological_space X] [topological_space Y]
-- [locally_compact_space X] [locally_compact_space Y] [topological_space Z] (g : X → C(Y, Z)) :
--   continuous g ↔ continuous (λ x y, g x y) :=  --iff.intro
-- -- (λ h, continuous_uncurry_of_continuous ⟨_, h⟩) (λ h, continuous_of_continuous_uncurry _ h)
-- begin
--   sorry;
--   {
--   split,
--   { intro h,
--     -- have := function.curry_uncurry (λ x y, g x y),
--     -- rw ← this,
--     apply continuous_pi _,
--     have φ  := (@homeomorph.curry X Y Z _ _ _ _ _).symm,
--     let G : C(X, C(Y,Z)) := ⟨g, h⟩,
--     let F := φ.1.1 G,

--     intro y,
--     -- exact h,
--     -- have := continuous_uncurry,
--     -- apply continuous_pi (λ (i : Y), _),

--   },
--   },
-- end

end continuous_map

namespace path

open continuous_map

variables (X : Type u) [topological_space X]

instance (x y : X) : has_coe (path x y) C(I, X) := ⟨λ γ, γ.1⟩

instance (x y : X) : topological_space (path x y) := topological_space.induced (coe : _ → C(↥I, X))
  continuous_map.compact_open

end path

namespace H_space

open path continuous_map

class H_space (X : Type u) [topological_space X]  :=
(Hmul : X × X → X)
(e : X)
(cont' : continuous Hmul)
(Hmul_e_e : Hmul (e, e) = e)
(left_Hmul_e : ∀ x : X,
  continuous_map.homotopy_rel
  ⟨(λ a : X, Hmul (e, a)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  ⟨id, continuous_id'⟩
  {e})
(right_Hmul_e : ∀ x : X,
  continuous_map.homotopy_rel
  ⟨(λ x : X, Hmul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  ⟨id, continuous_id'⟩
  {e})


notation ` ∨ `:65 := H_space.Hmul

instance topological_group_H_space (G : Type u) [topological_space G] [group G]
  [topological_group G] : H_space G :=
{ Hmul := function.uncurry has_mul.mul,
  e := 1,
  cont' := continuous_mul,
  Hmul_e_e := by {simp only [function.uncurry_apply_pair, mul_one]},
  left_Hmul_e := λ _, by {simp only [function.uncurry_apply_pair, one_mul],
    exact continuous_map.homotopy_rel.refl _ _ },
  right_Hmul_e := λ _, by {simp only [function.uncurry_apply_pair, mul_one],
    exact continuous_map.homotopy_rel.refl _ _ },
}

@[simp]
lemma Hmul_e {G : Type u} [topological_space G] [group G] [topological_group G] :
  (1 : G) = H_space.e := rfl

-- open circle

-- instance S0_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := infer_instance
-- instance S1_H_space : H_space circle := infer_instance
-- instance S3_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry
-- instance S7_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry

variables {X : Type u} [topological_space X]

-- def loop_space (x : X) : Type u := {f : C(I, X) // f 0 = x ∧ f 1 = x}

-- instance (x : X) : topological_space (loop_space x) := by {exact subtype.topological_space}

-- instance (x : X) : has_coe (loop_space x) C(I, X) := {coe := λ g, ⟨g.1⟩}

-- example (Y Z : Type) [topological_space Y] [topological_space Z] [locally_compact_space Y]
-- [locally_compact_space Z] (g : Y → C(Z, X)) (hg : continuous g) : continuous (λ p : Y × Z, g p.fst p.snd) :=
-- begin
--   let f:= continuous_map.uncurry ⟨g, hg⟩,
--   exact f.2,
-- end

def loop_space (x : X) := path x x


notation ` Ω(` x `)` := path x x

@[simp]
lemma continuous_coe (x : X) : continuous (coe : Ω(x) → C(↥I, X)) := continuous_induced_dom

@[ext]
lemma ext_loop (x : X) (γ γ' : Ω(x) ) : γ = γ' ↔ (∀ t, γ t = γ' t) :=
begin
  split;
  intro h,
  { simp only [h, eq_self_iff_true, forall_const] },
  { rw [← function.funext_iff] at h, exact path.ext h }
end

example (x : X) : has_coe_to_fun Ω(x) (λ _, I → X) := infer_instance


variable {x : X}

@[simp]
lemma continuous_to_Ω_iff_to_C {Y : Type u} [topological_space Y] {g : Y → Ω(x) } :
 continuous g ↔ continuous (↑g : Y → C(I,X)) :=
 ⟨λ h, continuous.comp (continuous_coe x) h, λ h, continuous_induced_rng h⟩
--begin
  --  split;
--   intro h,
--   { exact continuous.comp (continuous_coe x) h },
--   { exact continuous_induced_rng h, },
-- end

lemma continuous_to_Ω_iff_uncurry {Y : Type u} [topological_space Y]
[locally_compact_space Y] {g : Y → Ω(x)} : continuous g ↔ continuous (λ p : Y × I, g p.1 p.2) :=
  iff.intro ((λ h, (continuous_to_C_iff_uncurry Y I X ↑g).mp (continuous_to_Ω_iff_to_C.mp h)))
  (λ h, continuous_to_Ω_iff_to_C.mpr ((continuous_to_C_iff_uncurry Y I X ↑g).mpr h))

-- lemma continuous_to_loop_space_iff_uncurry (Y : Type u) [topological_space Y] (g : Y → Ω x) :
--   continuous g ↔ continuous (λ y : Y, λ t : I, g y t) :=
-- begin
  -- have := @continuous_map.continuous_uncurry_of_continuous Y I X _ _ _ _,
  -- split,
  -- sorry,
  -- intro h,
  -- apply this,
  -- have := this h,
-- sorry;{
--   let g₁ : Y → C(I,X) := λ y, g y,
--   split,
--   { intro h,
--     have hg₁ : continuous g₁, sorry,
--     -- { convert h.subtype_coe,
--     --   ext t,
--     --   refl },
--     have H := continuous_uncurry_of_continuous ⟨g₁, hg₁⟩,
--     exact continuous_pi (λ _, continuous.comp H (continuous_id'.prod_mk continuous_const)), },
--   { intro h,

--     suffices hg₁ : continuous g₁,
--     sorry,
--     apply continuous_of_continuous_uncurry,
--     dsimp [function.uncurry],
--     -- exact continuous_pi (λ (t : I), continuous.comp h (continuous_id'.prod_mk continuous_const)),
--     -- suggest,
--     -- library_search,
--     -- continuity,
--     -- simp,
--     -- convert h using 0,
--   },
-- }
-- end


-- lemma continuous_to_loop_space_iff_curry {Y : Type u} [topological_space Y]
--   {g : Y → Ω x} : continuous g ↔ continuous (λ p : Y × I, g p.1 p.2) :=
--   begin
--     sorry
--   end

-- example (Y Z : Type u) [topological_space Y] [topological_space Z] (f : Y → X) (hf : continuous f)
-- : continuous (λ p : Y × Z, f p.1) := continuous.fst' hf

-- example (Y Z : Type u) [topological_space Y] [topological_space Z] :
--   (X × Y) × Z ≃ₜ X × (Y × Z) := homeomorph.prod_assoc X Y Z

def I₀ := {t : I | t.1 ≤ 1/2}

lemma univ_eq_union_halves' (α : Type u) : (set.univ : set (α × I)) =
  ((set.univ : set α) ×ˢ I₀) ∪ ((set.univ : set α) ×ˢ I₀ᶜ) :=  by {ext, simp only [set.mem_union_eq,
   set.mem_prod, set.mem_univ, true_and, set.mem_compl_eq], tauto}

lemma univ_eq_union_halves (α : Type u) : ((set.univ : set α) ×ˢ I₀) ∪ ((set.univ : set α) ×ˢ I₀ᶜ)
  = (set.univ : set (α × I)) :=  by {ext, simp only [set.mem_union_eq, set.mem_prod, set.mem_univ,
    true_and, set.mem_compl_eq], tauto}

lemma continuous_of_restricts_union {α β : Type u} [topological_space α] [topological_space β]
  {s t : set α} {f : α → β} (H : s ∪ t = set.univ) (hs : continuous (s.restrict f))
  (ht : continuous (t.restrict f)) : continuous f := sorry --it should be a iff if it lands in `mathlib`

lemma continuous_triple_prod_assoc {α β γ δ : Type u} [topological_space α] [topological_space β]
  [topological_space γ] [topological_space δ] (f : (α × β) × γ → δ) : continuous f ↔
    continuous (f ∘ (homeomorph.prod_assoc α β γ).symm.1) :=
begin
  split,
  {refine λ (h : continuous f), h.comp _,
    simp only [homeomorph.coe_to_equiv, homeomorph.comp_continuous_iff],
    exact continuous_id},
  { refine λ (h : continuous (f ∘ ⇑((homeomorph.prod_assoc α β γ).symm.to_equiv))), _,
    simp only [*, homeomorph.coe_to_equiv, homeomorph.comp_continuous_iff'] at * },
end

lemma continuous_triple_prod_swap {α β γ δ : Type u} [topological_space α] [topological_space β]
  [topological_space γ] [topological_space δ] (f : (α × β) × γ → δ) : continuous f ↔
    continuous (f ∘ (homeomorph.prod_comm _ _).symm.1) :=
begin
  sorry,
end

example (α β : Type u) [inhabited α] (f : α → β) : (∃ b, f = (function.const α b)) ↔
  (∀ x y : α, f x = f y) :=
begin
  split,
  { rintro ⟨b, hb⟩,
    intros x y,
    rw hb },
  { intro h,
    use f (default : α),
    ext,
    rw h }
end


-- #help options

-- set_option trace.simp_lemmas true

lemma Hmul_Ω_cont (x : X) (γ γ' : Ω(x)) : continuous (λ t, γ.trans γ' t) :=
begin
  exact (trans γ γ').continuous,
end

lemma Hmul_Ω_cont' (x : X) : continuous (λ t, λ φ : Ω(x) × Ω(x), φ.1.trans φ.2 t) :=
begin
  exact continuous_pi (λ (i : path x x × path x x), (i.fst.trans i.snd).continuous),
end

-- lemma Hmul_Ω_cont'' (x : X) : continuous (λ φ : Ω(x) × Ω(x), λ t, φ.1.trans φ.2 t) :=
-- begin
--   continuity,
-- end

lemma senza_due_con_swap (x : X) : continuous (λ x : (I × Ω(x)) × Ω(x), x.1.2 x.1.1) :=
begin
  have h : continuous (λ x : (I × Ω(x)) × Ω(x), x.1), exact continuous_fst,
  set π := (λ p : I × Ω(x), p.1 p.2) with hπ,
  { have hπ : continuous π,
    have := @continuous_eval' I X _ _ _,
    sorry,
    sorry,
    -- convert this,
    -- have π':= function.uncurry_curry π,
    -- rw ← π',
    -- have := continuous_uncurry_of_continuous,
    -- have := continuous_to_Ω_iff_uncurry.mpr _,
    -- have := continuous.comp continuous_swap _,
    -- apply continuous.comp continuous_swap,

    }
  have := hπ.comp h,
  exact this,
end

lemma Hmul_Ω_cont₁ (x : X) : continuous (λ x : I × Ω(x) × Ω(x), x.2.1.trans x.2.2 x.1) :=
begin
  apply continuous.piecewise,
  sorry,
  -- sorry,
  { --let φ₁ := prod.swap,
    set f := λ (i : ↥I × path x x × path x x), i.snd.fst.extend (2 * ↑(i.fst)) with hf,
    set g := λ (i : (↥I × Ω(x)) × Ω(x)), i.fst.snd.extend (2 * ↑(i.fst.fst)) with hg,
    -- have : continuous f, sorry,
    let φ₁ := (@homeomorph.prod_assoc I Ω(x) Ω(x) _ _ _),
    apply (φ₁.comp_continuous_iff').mp,
    set ψ₁ := f ∘ φ₁ with hψ₁,
    have heq : ψ₁ = g, refl,
    rw ← hψ₁,
    rw heq,
    apply continuous.prod,
    -- continuity,
    -- simp,
    -- ext ⟨⟨t, γ⟩, γ'⟩,
    -- refl,
    -- let := φ₁.1.1,-- = (λ p : I × Ω(X) × Ω(x), ⟨p.1, ⟨p.2.1, p.2.2⟩⟩),
    -- squeeze_simp [φ₁.1.1],
    -- simp only,


  },
end

instance loop_space_is_H_space (x : X) : H_space Ω(x) :=
{ Hmul := λ ρ, ρ.1.trans ρ.2,
  e := refl _,
  cont' := --sorry,
  begin
    sorry;
    -- apply continuous_to_Ω_iff_uncu/rry.mpr,
    -- dsimp [path.trans],
    -- apply continuous_to_Ω_iff_to_C.mpr,
    -- have h₁ : continuous (λ p : Ω(x) × Ω(x),
    -- have h₂ : continuous (coe : I → ℝ), sorry,
    -- refine continuous.comp _ h,
    -- simp only [one_div],
    -- unfold_coes,
    -- simp only,
    -- convert continuous.comp _ _,

    -- continuity,
    -- apply conti/inuous_of_const _,
    -- rintros ⟨γ₁, γ₂, h⟩ k,--, h₃, h₄, h₅, h₆⟩,
    -- funext,
    -- apply continuous.piecewise,
    -- {sorry},
    -- { apply continuous.path_extend,
    --  {
    --   apply continuous_to_Ω_iff_uncurry.mp,
    --     exact continuous_fst.comp continuous_fst,
    --     refine locally_compact_space.prod _ _,

    --  },
    -- refine continuous_uncurry_left (λ (i : (path x x × path x x) × ↥I), i.fst.fst) _,
      -- continuity,
      -- apply continuous.path_extend,
    --  simp only,
      -- have : continuous (λ (t : (path x x × path x x) × ↥I), t.fst.fst),
      -- refine continuous_fst.comp continuous_fst,
      -- refine _,
      -- apply continuous_uncurry_extend_of_continuous_family,
      -- have := continuous_of_continuous_uncurry,
    --  apply continuous.path_extend,
    --  convert this,
    --   refine _,
    --   sorry,
      -- simp only,

    -- },
    -- {sorry},
--  sorry;
 {
  --   apply (continuous_to_loop_space_iff_curry x).mpr,
  apply continuous_of_restricts_union (univ_eq_union_halves _),
  { dsimp [set.restrict],
    dsimp [path.trans],
    -- dsimp [I₀],
    -- have lemma_dopo : ∀ x : (set.univ: (set I₀)), (x.1 : ℝ) ≤ 1/2, sorry,
    -- have lemma_dopo : ∀ x : I₀, ((x : I) : ℝ) ≤ 1/2, sorry,
    have := @continuous.if_const,-- ((set.univ: (set I)) ×ˢ I₀) _ _ ,
    -- simp_rw lemma_dopo,
    },
  sorry,
  -- simp only,
  --   { let φ := (λ p : (Ω x × Ω x) × I₀, p.fst.snd p.snd),
  --     have hφ: continuous φ, sorry,
  --     sorry,
  --     -- convert hφ,
  --     -- refl,

  --   },
    -- sorry,

    -- rw continuous_iff_continuous_at,
    -- intro w,
    -- rw ← continuous_within_at_univ,
    -- rw univ_eq_union_halves' ((Ω x) × (Ω x)),
    -- -- rw h,
    -- apply continuous_within_at_union.mpr,
    -- split,
    -- {


      -- have H := @continuous_within_at_snd ((new_loop_space x) × (new_loop_space x)) I _ _
      --   (set.univ ×ˢ I₀) w,
      -- have := @continuous_within_at.comp ((new_loop_space x × new_loop_space x) × I) _ X _ _ _,
      -- let ψ := (λ p : ((new_loop_space x × new_loop_space x) × I), ((path.trans p.fst.fst p.fst.snd).1).1),
    -- { have := continuous_within_at.comp' continuous_within_at_snd _,
    --simp [path.trans],
      -- by_cases hw : w.2.1 ≤ 2⁻¹,
      -- simp_rw if_pos,

      -- apply

    -- },
  -- sorry,
    -- },
 },
  end,
  Hmul_e_e := sorry,
  left_Hmul_e := sorry,
  right_Hmul_e := sorry}


end H_space
