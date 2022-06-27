/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import measure_theory.function.lp_space
import analysis.normed_space.lattice_ordered_group

/-!
# Order related properties of Lp spaces

### Results

- `Lp E p μ` is an `ordered_add_comm_group` when `E` is a `normed_lattice_add_comm_group`.

### TODO

- move definitions of `Lp.pos_part` and `Lp.neg_part` to this file, and define them as
  `has_pos_part.pos` and `has_pos_part.neg` given by the lattice structure.

-/

open topological_space measure_theory lattice_ordered_comm_group
open_locale ennreal

variables {α E : Type*} {m : measurable_space α} {μ : measure α} {p : ℝ≥0∞}

namespace measure_theory
namespace Lp

section order
variables [normed_lattice_add_comm_group E]

lemma coe_fn_le (f g : Lp E p μ) : f ≤ᵐ[μ] g ↔ f ≤ g :=
by rw [← subtype.coe_le_coe, ← ae_eq_fun.coe_fn_le, ← coe_fn_coe_base, ← coe_fn_coe_base]

lemma coe_fn_nonneg (f : Lp E p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f :=
begin
  rw ← coe_fn_le,
  have h0 := Lp.coe_fn_zero E p μ,
  split; intro h; filter_upwards [h, h0] with _ _ h2,
  { rwa h2, },
  { rwa ← h2, },
end

instance : covariant_class (Lp E p μ) (Lp E p μ) (+) (≤) :=
begin
  refine ⟨λ f g₁ g₂ hg₁₂, _⟩,
  rw ← coe_fn_le at hg₁₂ ⊢,
  filter_upwards [coe_fn_add f g₁, coe_fn_add f g₂, hg₁₂] with _ h1 h2 h3,
  rw [h1, h2, pi.add_apply, pi.add_apply],
  exact add_le_add le_rfl h3,
end

instance : ordered_add_comm_group (Lp E p μ) :=
{ add_le_add_left := λ f g, add_le_add_left,
  ..subtype.partial_order _, ..add_subgroup.to_add_comm_group _}

instance [second_countable_topology E] [measurable_space E] [borel_space E]
  [has_measurable_sup₂ E] [has_measurable_inf₂ E] :
  lattice (Lp E p μ) :=
subtype.lattice (λ f g hf hg, by { rw mem_Lp_iff_mem_ℒp at *,
    exact (mem_ℒp_congr_ae (ae_eq_fun.coe_fn_sup _ _)).mpr (hf.sup hg), })
  (λ f g hf hg, by { rw mem_Lp_iff_mem_ℒp at *,
    exact (mem_ℒp_congr_ae (ae_eq_fun.coe_fn_inf _ _)).mpr (hf.inf hg),})

lemma ae_eq_fun.coe_fn_abs [second_countable_topology E] [measurable_space E] [borel_space E]
  [has_measurable_sup₂ E]
  (f : α →ₘ[μ] E) :
    ⇑|f| =ᵐ[μ] λ x, |f x| :=
begin
  simp_rw abs_eq_sup_neg,
  refine (ae_eq_fun.coe_fn_sup _ _).trans _,
  filter_upwards [ae_eq_fun.coe_fn_neg f] with x hx,
  rw [hx, pi.neg_apply],
end

lemma coe_fn_sup [measurable_space E] [second_countable_topology E]
  [borel_space E] [has_measurable_sup₂ E] (f g : Lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g :=
ae_eq_fun.coe_fn_sup _ _

lemma coe_fn_inf [measurable_space E] [second_countable_topology E]
  [borel_space E] [has_measurable_sup₂ E] (f g : Lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g :=
ae_eq_fun.coe_fn_inf _ _

lemma coe_fn_abs [measurable_space E] [second_countable_topology E]
  [borel_space E] [has_measurable_sup₂ E] (f : Lp E p μ) : ⇑|f| =ᵐ[μ] λ x, |f x| :=
ae_eq_fun.coe_fn_abs _

noncomputable
instance [second_countable_topology E] [measurable_space E] [borel_space E]
  [has_measurable_sup₂ E] [has_measurable_inf₂ E] [fact (1 ≤ p)] :
  normed_lattice_add_comm_group (Lp E p μ) :=
{ add_le_add_left := λ f g, add_le_add_left,
  solid := λ f g hfg, by { rw ← coe_fn_le at hfg, simp_rw Lp.norm_def,
    rw ennreal.to_real_le_to_real (Lp.snorm_ne_top f) (Lp.snorm_ne_top g),
    refine snorm_mono_ae _,
    filter_upwards [hfg, Lp.coe_fn_abs f, Lp.coe_fn_abs g] with x hx hxf hxg,
    rw [hxf, hxg] at hx,
    exact solid hx, },
  ..Lp.lattice, ..Lp.normed_group, }

end order

end Lp
end measure_theory
