/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.function.simple_func_dense_lp
import measure_theory.function.strongly_measurable

/-!
# Finitely strongly measurable functions in `Lp`

Functions in `Lp` for `0 < p < ∞` are finitely strongly measurable.

## Main statements

* `mem_ℒp.ae_fin_strongly_measurable`: if `mem_ℒp f p μ` with `0 < p < ∞`, then
  `ae_fin_strongly_measurable f μ`.
* `Lp.fin_strongly_measurable`: for `0 < p < ∞`, `Lp` functions are finitely strongly measurable.

## References

* Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
Springer, 2016.
-/

open measure_theory filter topological_space function
open_locale ennreal topological_space measure_theory

namespace measure_theory

local infixr ` →ₛ `:25 := simple_func

variables {α G : Type*} {p : ℝ≥0∞} {m m0 : measurable_space α} {μ : measure α}
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  {f : α → G}

lemma mem_ℒp.fin_strongly_measurable_of_measurable (hf : mem_ℒp f p μ) (hf_meas : measurable f)
  (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  fin_strongly_measurable f μ :=
begin
  let fs := simple_func.approx_on f hf_meas set.univ 0 (set.mem_univ _),
  refine ⟨fs, _, _⟩,
  { have h_fs_Lp : ∀ n, mem_ℒp (fs n) p μ, from simple_func.mem_ℒp_approx_on_univ hf_meas hf,
    exact λ n, (fs n).measure_support_lt_top_of_mem_ℒp (h_fs_Lp n) hp_ne_zero hp_ne_top, },
  { exact λ x, simple_func.tendsto_approx_on hf_meas (set.mem_univ 0) (by simp), },
end

lemma mem_ℒp.ae_fin_strongly_measurable (hf : mem_ℒp f p μ) (hp_ne_zero : p ≠ 0)
  (hp_ne_top : p ≠ ∞) :
  ae_fin_strongly_measurable f μ :=
⟨hf.ae_measurable.mk f,
  ((mem_ℒp_congr_ae hf.ae_measurable.ae_eq_mk).mp hf).fin_strongly_measurable_of_measurable
    hf.ae_measurable.measurable_mk hp_ne_zero hp_ne_top,
  hf.ae_measurable.ae_eq_mk⟩

lemma integrable.ae_fin_strongly_measurable (hf : integrable f μ) :
  ae_fin_strongly_measurable f μ :=
(mem_ℒp_one_iff_integrable.mpr hf).ae_fin_strongly_measurable one_ne_zero ennreal.coe_ne_top

lemma Lp.fin_strongly_measurable (f : Lp G p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
  fin_strongly_measurable f μ :=
(Lp.mem_ℒp f).fin_strongly_measurable_of_measurable (Lp.measurable f) hp_ne_zero hp_ne_top

end measure_theory
