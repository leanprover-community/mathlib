/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Winston Yin
-/
import analysis.special_functions.integrals
import topology.metric_space.contracting

/-!
# Picard-Lindelöf (Cauchy-Lipschitz) Theorem

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that an ordinary differential equation $\dot x=v(t, x)$ such that $v$ is
Lipschitz continuous in $x$ and continuous in $t$ has a local solution, see
`exists_forall_deriv_within_Icc_eq_of_is_picard_lindelof`.

As a corollary, we prove that a time-independent locally continuously differentiable ODE has a
local solution.

## Implementation notes

In order to split the proof into small lemmas, we introduce a structure `picard_lindelof` that holds
all assumptions of the main theorem. This structure and lemmas in the `picard_lindelof` namespace
should be treated as private implementation details. This is not to be confused with the `Prop`-
valued structure `is_picard_lindelof`, which holds the long hypotheses of the Picard-Lindelöf
theorem for actual use as part of the public API.

We only prove existence of a solution in this file. For uniqueness see `ODE_solution_unique` and
related theorems in `analysis.ODE.gronwall`.

## Tags

differential equation
-/

open filter function set metric topological_space interval_integral measure_theory
open measure_theory.measure_space (volume)
open_locale filter topology nnreal ennreal nat interval

noncomputable theory

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]

/-- `Prop` structure holding the hypotheses of the Picard-Lindelöf theorem.

The similarly named `picard_lindelof` structure is part of the internal API for convenience, so as
not to constantly invoke choice, but is not intended for public use. -/
structure is_picard_lindelof
  {E : Type*} [normed_add_comm_group E] (v : ℝ → E → E) (t_min t₀ t_max : ℝ) (x₀ : E)
  (L : ℝ≥0) (R C : ℝ) : Prop :=
(ht₀ : t₀ ∈ Icc t_min t_max)
(hR : 0 ≤ R)
(lipschitz : ∀ t ∈ Icc t_min t_max, lipschitz_on_with L (v t) (closed_ball x₀ R))
(cont : ∀ x ∈ closed_ball x₀ R, continuous_on (λ (t : ℝ), v t x) (Icc t_min t_max))
(norm_le : ∀ (t ∈ Icc t_min t_max) (x ∈ closed_ball x₀ R), ‖v t x‖ ≤ C)
(C_mul_le_R : (C : ℝ) * linear_order.max (t_max - t₀) (t₀ - t_min) ≤ R)

/-- This structure holds arguments of the Picard-Lipschitz (Cauchy-Lipschitz) theorem. It is part of
the internal API for convenience, so as not to constantly invoke choice. Unless you want to use one
of the auxiliary lemmas, use `exists_forall_deriv_within_Icc_eq_of_lipschitz_of_continuous` instead
of using this structure.

The similarly named `is_picard_lindelof` is a bundled `Prop` holding the long hypotheses of the
Picard-Lindelöf theorem as named arguments. It is used as part of the public API.
-/
structure picard_lindelof (E : Type*) [normed_add_comm_group E] [normed_space ℝ E] :=
(to_fun : ℝ → E → E)
(t_min t_max : ℝ)
(t₀ : Icc t_min t_max)
(x₀ : E)
(C R L : ℝ≥0)
(is_pl : is_picard_lindelof to_fun t_min t₀ t_max x₀ L R C)

namespace picard_lindelof

variables (v : picard_lindelof E)

instance : has_coe_to_fun (picard_lindelof E) (λ _, ℝ → E → E) := ⟨to_fun⟩

instance : inhabited (picard_lindelof E) :=
⟨⟨0, 0, 0, ⟨0, le_rfl, le_rfl⟩, 0, 0, 0, 0,
  { ht₀ := by { rw [subtype.coe_mk, Icc_self], exact mem_singleton _ },
    hR := by refl,
    lipschitz := λ t ht, (lipschitz_with.const 0).lipschitz_on_with _,
    cont := λ _ _, by simpa only [pi.zero_apply] using continuous_on_const,
    norm_le := λ t ht x hx, norm_zero.le,
    C_mul_le_R := (zero_mul _).le }⟩⟩

lemma t_min_le_t_max : v.t_min ≤ v.t_max := v.t₀.2.1.trans v.t₀.2.2

protected lemma nonempty_Icc : (Icc v.t_min v.t_max).nonempty := nonempty_Icc.2 v.t_min_le_t_max

protected lemma lipschitz_on_with {t} (ht : t ∈ Icc v.t_min v.t_max) :
  lipschitz_on_with v.L (v t) (closed_ball v.x₀ v.R) :=
v.is_pl.lipschitz t ht

protected lemma continuous_on :
  continuous_on (uncurry v) (Icc v.t_min v.t_max ×ˢ closed_ball v.x₀ v.R) :=
have continuous_on (uncurry (flip v)) (closed_ball v.x₀ v.R ×ˢ Icc v.t_min v.t_max),
  from continuous_on_prod_of_continuous_on_lipschitz_on _ v.L v.is_pl.cont v.is_pl.lipschitz,
this.comp continuous_swap.continuous_on (preimage_swap_prod _ _).symm.subset

lemma norm_le {t : ℝ} (ht : t ∈ Icc v.t_min v.t_max) {x : E} (hx : x ∈ closed_ball v.x₀ v.R) :
  ‖v t x‖ ≤ v.C :=
v.is_pl.norm_le _ ht _ hx

/-- The maximum of distances from `t₀` to the endpoints of `[t_min, t_max]`. -/
def t_dist : ℝ := max (v.t_max - v.t₀) (v.t₀ - v.t_min)

lemma t_dist_nonneg : 0 ≤ v.t_dist := le_max_iff.2 $ or.inl $ sub_nonneg.2 v.t₀.2.2

lemma dist_t₀_le (t : Icc v.t_min v.t_max) : dist t v.t₀ ≤ v.t_dist :=
begin
  rw [subtype.dist_eq, real.dist_eq],
  cases le_total t v.t₀ with ht ht,
  { rw [abs_of_nonpos (sub_nonpos.2 $ subtype.coe_le_coe.2 ht), neg_sub],
    exact (sub_le_sub_left t.2.1 _).trans (le_max_right _ _) },
  { rw [abs_of_nonneg (sub_nonneg.2 $ subtype.coe_le_coe.2 ht)],
    exact (sub_le_sub_right t.2.2 _).trans (le_max_left _ _) }
end

/-- Projection $ℝ → [t_{\min}, t_{\max}]$ sending $(-∞, t_{\min}]$ to $t_{\min}$ and $[t_{\max}, ∞)$
to $t_{\max}$. -/
def proj : ℝ → Icc v.t_min v.t_max := proj_Icc v.t_min v.t_max v.t_min_le_t_max

lemma proj_coe (t : Icc v.t_min v.t_max) : v.proj t = t := proj_Icc_coe _ _

lemma proj_of_mem {t : ℝ} (ht : t ∈ Icc v.t_min v.t_max) : ↑(v.proj t) = t :=
by simp only [proj, proj_Icc_of_mem _ ht, subtype.coe_mk]

@[continuity] lemma continuous_proj : continuous v.proj := continuous_proj_Icc

/-- The space of curves $γ \colon [t_{\min}, t_{\max}] \to E$ such that $γ(t₀) = x₀$ and $γ$ is
Lipschitz continuous with constant $C$. The map sending $γ$ to
$\mathbf Pγ(t)=x₀ + ∫_{t₀}^{t} v(τ, γ(τ))\,dτ$ is a contracting map on this space, and its fixed
point is a solution of the ODE $\dot x=v(t, x)$. -/
structure fun_space :=
(to_fun : Icc v.t_min v.t_max → E)
(map_t₀' : to_fun v.t₀ = v.x₀)
(lipschitz' : lipschitz_with v.C to_fun)

namespace fun_space

variables {v} (f : fun_space v)

instance : has_coe_to_fun (fun_space v) (λ _, Icc v.t_min v.t_max → E) := ⟨to_fun⟩

instance : inhabited v.fun_space :=
⟨⟨λ _, v.x₀, rfl, (lipschitz_with.const _).weaken (zero_le _)⟩⟩

protected lemma lipschitz : lipschitz_with v.C f := f.lipschitz'

protected lemma continuous : continuous f := f.lipschitz.continuous

/-- Each curve in `picard_lindelof.fun_space` is continuous. -/
def to_continuous_map : v.fun_space ↪ C(Icc v.t_min v.t_max, E) :=
⟨λ f, ⟨f, f.continuous⟩, λ f g h, by { cases f, cases g, simpa using h }⟩

instance : metric_space v.fun_space :=
metric_space.induced to_continuous_map to_continuous_map.injective infer_instance

lemma uniform_inducing_to_continuous_map : uniform_inducing (@to_continuous_map _ _ _ v) := ⟨rfl⟩

lemma range_to_continuous_map :
  range to_continuous_map =
    {f : C(Icc v.t_min v.t_max, E) | f v.t₀ = v.x₀ ∧ lipschitz_with v.C f} :=
begin
  ext f, split,
  { rintro ⟨⟨f, hf₀, hf_lip⟩, rfl⟩, exact ⟨hf₀, hf_lip⟩ },
  { rcases f with ⟨f, hf⟩, rintro ⟨hf₀, hf_lip⟩, exact ⟨⟨f, hf₀, hf_lip⟩, rfl⟩ }
end

lemma map_t₀ : f v.t₀ = v.x₀ := f.map_t₀'

protected lemma mem_closed_ball (t : Icc v.t_min v.t_max) : f t ∈ closed_ball v.x₀ v.R :=
calc dist (f t) v.x₀ = dist (f t) (f.to_fun v.t₀) : by rw f.map_t₀'
                 ... ≤ v.C * dist t v.t₀          : f.lipschitz.dist_le_mul _ _
                 ... ≤ v.C * v.t_dist             : mul_le_mul_of_nonneg_left (v.dist_t₀_le _) v.C.2
                 ... ≤ v.R                        : v.is_pl.C_mul_le_R

/-- Given a curve $γ \colon [t_{\min}, t_{\max}] → E$, `v_comp` is the function
$F(t)=v(π t, γ(π t))$, where `π` is the projection $ℝ → [t_{\min}, t_{\max}]$. The integral of this
function is the image of `γ` under the contracting map we are going to define below. -/
def v_comp (t : ℝ) : E := v (v.proj t) (f (v.proj t))

lemma v_comp_apply_coe (t : Icc v.t_min v.t_max) : f.v_comp t = v t (f t) :=
by simp only [v_comp, proj_coe]

lemma continuous_v_comp : continuous f.v_comp :=
begin
  have := (continuous_subtype_coe.prod_mk f.continuous).comp v.continuous_proj,
  refine continuous_on.comp_continuous v.continuous_on this (λ x, _),
  exact ⟨(v.proj x).2, f.mem_closed_ball _⟩
end

lemma norm_v_comp_le (t : ℝ) : ‖f.v_comp t‖ ≤ v.C :=
v.norm_le (v.proj t).2 $ f.mem_closed_ball _

lemma dist_apply_le_dist (f₁ f₂ : fun_space v) (t : Icc v.t_min v.t_max) :
  dist (f₁ t) (f₂ t) ≤ dist f₁ f₂ :=
@continuous_map.dist_apply_le_dist _ _ _ _ _ f₁.to_continuous_map f₂.to_continuous_map _

lemma dist_le_of_forall {f₁ f₂ : fun_space v} {d : ℝ} (h : ∀ t, dist (f₁ t) (f₂ t) ≤ d) :
  dist f₁ f₂ ≤ d :=
(@continuous_map.dist_le_iff_of_nonempty _ _ _ _ _ f₁.to_continuous_map f₂.to_continuous_map _
  v.nonempty_Icc.to_subtype).2 h

instance [complete_space E] : complete_space v.fun_space :=
begin
  refine (complete_space_iff_is_complete_range
    uniform_inducing_to_continuous_map).2 (is_closed.is_complete _),
  rw [range_to_continuous_map, set_of_and],
  refine (is_closed_eq (continuous_map.continuous_eval_const _) continuous_const).inter _,
  have : is_closed {f : Icc v.t_min v.t_max → E | lipschitz_with v.C f} :=
    is_closed_set_of_lipschitz_with v.C,
  exact this.preimage continuous_map.continuous_coe
end

lemma interval_integrable_v_comp (t₁ t₂ : ℝ) :
  interval_integrable f.v_comp volume t₁ t₂ :=
(f.continuous_v_comp).interval_integrable _ _

variables [complete_space E]

/-- The Picard-Lindelöf operator. This is a contracting map on `picard_lindelof.fun_space v` such
that the fixed point of this map is the solution of the corresponding ODE.

More precisely, some iteration of this map is a contracting map. -/
def next (f : fun_space v) : fun_space v :=
{ to_fun := λ t, v.x₀ + ∫_{v.t₀}^{t} τ, f.v_comp τ,
  map_t₀' := by rw [integral_same, add_zero],
  lipschitz' := lipschitz_with.of_dist_le_mul $ λ t₁ t₂,
    begin
      rw [dist_add_left, dist_eq_norm,
        integral_interval_sub_left (f.interval_integrable_v_comp _ _)
          (f.interval_integrable_v_comp _ _)],
      exact norm_integral_le_of_norm_le_const (λ t ht, f.norm_v_comp_le _),
    end }

lemma next_apply (t : Icc v.t_min v.t_max) : f.next t = v.x₀ + ∫_{v.t₀}^{t} τ, f.v_comp τ := rfl

lemma has_deriv_within_at_next (t : Icc v.t_min v.t_max) :
  has_deriv_within_at (f.next ∘ v.proj) (v t (f t)) (Icc v.t_min v.t_max) t :=
begin
  haveI : fact ((t : ℝ) ∈ Icc v.t_min v.t_max) := ⟨t.2⟩,
  simp only [(∘), next_apply],
  refine has_deriv_within_at.const_add _ _,
  have : has_deriv_within_at (λ t : ℝ, ∫_{v.t₀}^{t} τ, f.v_comp τ) (f.v_comp t)
    (Icc v.t_min v.t_max) t,
    from integral_has_deriv_within_at_right (f.interval_integrable_v_comp _ _)
      (f.continuous_v_comp.strongly_measurable_at_filter _ _)
      f.continuous_v_comp.continuous_within_at,
  rw v_comp_apply_coe at this,
  refine this.congr_of_eventually_eq_of_mem _ t.coe_prop,
  filter_upwards [self_mem_nhds_within] with _ ht',
  rw v.proj_of_mem ht'
end

lemma dist_next_apply_le_of_le {f₁ f₂ : fun_space v} {n : ℕ} {d : ℝ}
  (h : ∀ t, dist (f₁ t) (f₂ t) ≤ (v.L * |t - v.t₀|) ^ n / n! * d) (t : Icc v.t_min v.t_max) :
  dist (next f₁ t) (next f₂ t) ≤ (v.L * |t - v.t₀|) ^ (n + 1) / (n + 1)! * d :=
begin
  simp only [dist_eq_norm, next_apply, add_sub_add_left_eq_sub,
    ← interval_integral.integral_sub (interval_integrable_v_comp _ _ _)
      (interval_integrable_v_comp _ _ _), norm_integral_eq_norm_integral_Ioc] at *,
  calc ‖∫ τ in Ι (v.t₀ : ℝ) t, f₁.v_comp τ - f₂.v_comp τ‖
      ≤ ∫ τ in Ι (v.t₀ : ℝ) t, v.L * ((v.L * |τ - v.t₀|) ^ n / n! * d) :
    begin
      refine norm_integral_le_of_norm_le (continuous.integrable_on_uIoc _) _,
      { continuity },
      { refine (ae_restrict_mem measurable_set_Ioc).mono (λ τ hτ, _),
        refine (v.lipschitz_on_with (v.proj τ).2).norm_sub_le_of_le
          (f₁.mem_closed_ball _) (f₂.mem_closed_ball _) ((h _).trans_eq _),
        rw v.proj_of_mem,
        exact (uIcc_subset_Icc v.t₀.2 t.2 $ Ioc_subset_Icc_self hτ) }
    end
  ... = (v.L * |t - v.t₀|) ^ (n + 1) / (n + 1)! * d : _,
  simp_rw [mul_pow, div_eq_mul_inv, mul_assoc, measure_theory.integral_mul_left,
    measure_theory.integral_mul_right, integral_pow_abs_sub_uIoc, div_eq_mul_inv,
    pow_succ (v.L : ℝ), nat.factorial_succ, nat.cast_mul, nat.cast_succ, mul_inv, mul_assoc]
end

lemma dist_iterate_next_apply_le (f₁ f₂ : fun_space v) (n : ℕ) (t : Icc v.t_min v.t_max) :
  dist (next^[n] f₁ t) (next^[n] f₂ t) ≤ (v.L * |t - v.t₀|) ^ n / n! * dist f₁ f₂ :=
begin
  induction n with n ihn generalizing t,
  { rw [pow_zero, nat.factorial_zero, nat.cast_one, div_one, one_mul],
    exact dist_apply_le_dist f₁ f₂ t },
  { rw [iterate_succ_apply', iterate_succ_apply'],
    exact dist_next_apply_le_of_le ihn _ }
end

lemma dist_iterate_next_le (f₁ f₂ : fun_space v) (n : ℕ) :
  dist (next^[n] f₁) (next^[n] f₂) ≤ (v.L * v.t_dist) ^ n / n! * dist f₁ f₂ :=
begin
  refine dist_le_of_forall (λ t, (dist_iterate_next_apply_le _ _ _ _).trans _),
  have : 0 ≤ dist f₁ f₂ := dist_nonneg,
  have : |(t - v.t₀ : ℝ)| ≤ v.t_dist := v.dist_t₀_le t,
  mono*; simp only [nat.cast_nonneg, mul_nonneg, nnreal.coe_nonneg, abs_nonneg, *]
end

end fun_space

variables [complete_space E]

section

lemma exists_contracting_iterate :
  ∃ (N : ℕ) K, contracting_with K ((fun_space.next : v.fun_space → v.fun_space)^[N]) :=
begin
  rcases ((real.tendsto_pow_div_factorial_at_top (v.L * v.t_dist)).eventually
    (gt_mem_nhds zero_lt_one)).exists with ⟨N, hN⟩,
  have : (0 : ℝ) ≤ (v.L * v.t_dist) ^ N / N!,
    from div_nonneg (pow_nonneg (mul_nonneg v.L.2 v.t_dist_nonneg) _) (nat.cast_nonneg _),
  exact ⟨N, ⟨_, this⟩, hN,
    lipschitz_with.of_dist_le_mul (λ f g, fun_space.dist_iterate_next_le f g N)⟩
end

lemma exists_fixed : ∃ f : v.fun_space, f.next = f :=
let ⟨N, K, hK⟩ := exists_contracting_iterate v in ⟨_, hK.is_fixed_pt_fixed_point_iterate⟩

end

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. Use
`exists_forall_deriv_within_Icc_eq_of_is_picard_lindelof` instead for the public API. -/
lemma exists_solution :
  ∃ f : ℝ → E, f v.t₀ = v.x₀ ∧ ∀ t ∈ Icc v.t_min v.t_max,
    has_deriv_within_at f (v t (f t)) (Icc v.t_min v.t_max) t :=
begin
  rcases v.exists_fixed with ⟨f, hf⟩,
  refine ⟨f ∘ v.proj, _, λ t ht, _⟩,
  { simp only [(∘), proj_coe, f.map_t₀] },
  { simp only [(∘), v.proj_of_mem ht],
    lift t to Icc v.t_min v.t_max using ht,
    simpa only [hf, v.proj_coe] using f.has_deriv_within_at_next t }
end

end picard_lindelof

lemma is_picard_lindelof.norm_le₀ {E : Type*} [normed_add_comm_group E]
  {v : ℝ → E → E} {t_min t₀ t_max : ℝ} {x₀ : E} {C R : ℝ} {L : ℝ≥0}
  (hpl : is_picard_lindelof v t_min t₀ t_max x₀ L R C) : ‖v t₀ x₀‖ ≤ C :=
hpl.norm_le t₀ hpl.ht₀ x₀ $ mem_closed_ball_self hpl.hR

/-- Picard-Lindelöf (Cauchy-Lipschitz) theorem. -/
theorem exists_forall_deriv_within_Icc_eq_of_is_picard_lindelof
  [complete_space E] {v : ℝ → E → E} {t_min t₀ t_max : ℝ} (x₀ : E) {C R : ℝ} {L : ℝ≥0}
  (hpl : is_picard_lindelof v t_min t₀ t_max x₀ L R C) :
  ∃ f : ℝ → E, f t₀ = x₀ ∧ ∀ t ∈ Icc t_min t_max,
    has_deriv_within_at f (v t (f t)) (Icc t_min t_max) t :=
begin
  lift C to ℝ≥0 using (norm_nonneg _).trans hpl.norm_le₀,
  lift t₀ to Icc t_min t_max using hpl.ht₀,
  exact picard_lindelof.exists_solution
    ⟨v, t_min, t_max, t₀, x₀, C, ⟨R, hpl.hR⟩, L, { ht₀ := t₀.property, ..hpl }⟩
end

variables [proper_space E] {v : E → E} (t₀ : ℝ) (x₀ : E)

/-- A time-independent, locally continuously differentiable ODE satisfies the hypotheses of the
  Picard-Lindelöf theorem. -/
lemma exists_is_picard_lindelof_const_of_cont_diff_on_nhds
  {s : set E} (hv : cont_diff_on ℝ 1 v s) (hs : s ∈ 𝓝 x₀) :
  ∃ (ε > (0 : ℝ)) L R C, is_picard_lindelof (λ t, v) (t₀ - ε) t₀ (t₀ + ε) x₀ L R C :=
begin
  -- extract Lipschitz constant
  obtain ⟨L, s', hs', hlip⟩ := cont_diff_at.exists_lipschitz_on_with
    ((hv.cont_diff_within_at (mem_of_mem_nhds hs)).cont_diff_at hs),
  -- radius of closed ball in which v is bounded
  obtain ⟨r, hr : 0 < r, hball⟩ := metric.mem_nhds_iff.mp (inter_sets (𝓝 x₀) hs hs'),
  have hr' := (half_pos hr).le,
  obtain ⟨C, hC⟩ := (is_compact_closed_ball x₀ (r / 2)).bdd_above_image -- uses proper_space E
    (hv.continuous_on.norm.mono (subset_inter_iff.mp
        ((closed_ball_subset_ball (half_lt_self hr)).trans hball)).left),
  have hC' : 0 ≤ C,
  { apply (norm_nonneg (v x₀)).trans,
    apply hC,
    exact ⟨x₀, ⟨mem_closed_ball_self hr', rfl⟩⟩ },
  set ε := if C = 0 then 1 else (r / 2 / C) with hε,
  have hε0 : 0 < ε,
  { rw hε,
    split_ifs,
    { exact zero_lt_one },
    { exact div_pos (half_pos hr) (lt_of_le_of_ne hC' (ne.symm h)) } },
  refine ⟨ε, hε0, L, r / 2, C, _⟩,
  exact { ht₀ := by {rw ←real.closed_ball_eq_Icc, exact mem_closed_ball_self hε0.le},
    hR := (half_pos hr).le,
    lipschitz := λ t ht, hlip.mono (subset_inter_iff.mp
      (subset_trans (closed_ball_subset_ball (half_lt_self hr)) hball)).2,
    cont := λ x hx, continuous_on_const,
    norm_le := λ t ht x hx, hC ⟨x, hx, rfl⟩,
    C_mul_le_R := begin
      rw [add_sub_cancel', sub_sub_cancel, max_self, mul_ite, mul_one],
      split_ifs,
      { rwa ← h at hr' },
      { exact (mul_div_cancel' (r / 2) h).le }
    end }
end

/-- A time-independent, locally continuously differentiable ODE admits a solution in some open
interval. -/
theorem exists_forall_deriv_at_Ioo_eq_of_cont_diff_on_nhds
  {s : set E} (hv : cont_diff_on ℝ 1 v s) (hs : s ∈ 𝓝 x₀) :
  ∃ (ε > (0 : ℝ)) (f : ℝ → E), f t₀ = x₀ ∧
    ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), f t ∈ s ∧ has_deriv_at f (v (f t)) t :=
begin
  obtain ⟨ε, hε, L, R, C, hpl⟩ := exists_is_picard_lindelof_const_of_cont_diff_on_nhds t₀ x₀ hv hs,
  obtain ⟨f, hf1, hf2⟩ := exists_forall_deriv_within_Icc_eq_of_is_picard_lindelof x₀ hpl,
  have hf2' : ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), has_deriv_at f (v (f t)) t :=
    λ t ht, (hf2 t (Ioo_subset_Icc_self ht)).has_deriv_at (Icc_mem_nhds ht.1 ht.2),
  have h : (f ⁻¹' s) ∈ 𝓝 t₀,
  { have := (hf2' t₀ (mem_Ioo.mpr ⟨sub_lt_self _ hε, lt_add_of_pos_right _ hε⟩)),
    apply continuous_at.preimage_mem_nhds this.continuous_at,
    rw hf1,
    exact hs },
  rw metric.mem_nhds_iff at h,
  obtain ⟨r, hr1, hr2⟩ := h,
  refine ⟨min r ε, lt_min hr1 hε, f, hf1, λ t ht,
    ⟨_, hf2' t (mem_of_mem_of_subset ht (Ioo_subset_Ioo
      (sub_le_sub_left (min_le_right _ _) _) (add_le_add_left (min_le_right _ _) _)))⟩⟩,
  rw ←set.mem_preimage,
  apply set.mem_of_mem_of_subset _ hr2,
  apply set.mem_of_mem_of_subset ht,
  rw ←real.ball_eq_Ioo,
  exact (metric.ball_subset_ball (min_le_left _ _))
end

/-- A time-independent, continuously differentiable ODE admits a solution in some open interval. -/
theorem exists_forall_deriv_at_Ioo_eq_of_cont_diff
  (hv : cont_diff ℝ 1 v) : ∃ (ε > (0 : ℝ)) (f : ℝ → E), f t₀ = x₀ ∧
    ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), has_deriv_at f (v (f t)) t :=
let ⟨ε, hε, f, hf1, hf2⟩ := exists_forall_deriv_at_Ioo_eq_of_cont_diff_on_nhds t₀ x₀ hv.cont_diff_on
  (is_open.mem_nhds is_open_univ (mem_univ _)) in ⟨ε, hε, f, hf1, λ t ht, (hf2 t ht).2⟩
