import analysis.complex.basic
import analysis.calculus.deriv
import tactic.pi_instances
import ring_theory.subring.basic
import analysis.normed_space.basic
import analysis.calculus.deriv
import analysis.analytic.basic



local attribute [instance] classical.prop_decidable
noncomputable theory

universes u v
open_locale classical topological_space big_operators filter
open filter complex asymptotics

section
variables {α : Type*} {β : Type*} {s : set α}

def extend_by_zero [has_zero β] (f : s → β) : α → β :=
λ z, if h : z ∈ s then f ⟨z, h⟩ else 0

lemma extend_by_zero_zero [has_zero β] :
extend_by_zero (λ s, 0 : s → β) = (λ h, 0) :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_zero' [has_zero β] :
extend_by_zero (0 : s → β) = 0 :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_add [add_group β] (f g : s → β) :
extend_by_zero (f + g) = extend_by_zero f + extend_by_zero g :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_sum [add_comm_monoid β] (ι  : finset α) (F : ι →  s → β) :
extend_by_zero (λ (x : s), ∑ (i : ι ), F i x) = ∑ (i : ι), extend_by_zero (F i) :=
begin
ext z,
by_cases h : z ∈ s,
simp only [extend_by_zero, h, finset.sum_apply, dif_pos],
simp only [extend_by_zero, h, finset.sum_apply, dif_neg, not_false_iff, finset.sum_const_zero],
end

lemma extend_by_zero_mul [semiring β] (f g : s → β) :
extend_by_zero (f * g) = extend_by_zero f * extend_by_zero g :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_neg [add_group β] (f : s → β) :
extend_by_zero (-f) = -extend_by_zero f :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_smul [ring β] (c : β) (f : s → β) :
  extend_by_zero (c • f) = c • extend_by_zero f :=
  by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

end



def open_subs:=topological_space.opens ℂ

/--A function is Holomorphic on an open subset of the complex numbers, if for every point in the domain
there is a neibourhood around the point containing the derivative of the function. In order to make it work
with has_deriv_within_at, we first extend the function by zero to the entire complex plane. -/


def is_holomorphic_on {D : open_subs} (f : D.1 → ℂ) : Prop :=
  ∀ z : D.1, ∃ f', has_deriv_within_at (extend_by_zero f) (f') D.1 z


lemma is_holomorphic_on_iff_differentiable_on  (D : open_subs) (f : D.1 → ℂ):
  differentiable_on ℂ  (extend_by_zero f) D.1 ↔ is_holomorphic_on f:=
begin
  rw is_holomorphic_on,
  split,
  rw differentiable_on,
  intros hd z,
  have h1:= hd z.1 z.2,
  have h2:=  differentiable_within_at.has_fderiv_within_at h1,
  simp_rw has_deriv_within_at,
  simp_rw has_deriv_at_filter,
  simp_rw has_fderiv_within_at at h2,
  simp at *,
  dunfold fderiv_within at h2,
  dunfold differentiable_within_at at h1,
  rw dif_pos h1 at h2,
  use classical.some h1 1,
  simp,
  exact h2,
  intro hz,
  rw differentiable_on,
  intros x hx,
  have h1:= hz ⟨x, hx⟩,
  have h2:= classical.some_spec h1,
  apply has_deriv_within_at.differentiable_within_at  h2,
end

variable {D : open_subs}

lemma ext_by_zero_eq (D: open_subs) (c : ℂ):
∀ (y : ℂ), (y ∈ (D.1 : set ℂ)) → extend_by_zero (λ z : D.1, (c : ℂ)) y = c :=
begin
  intros y hy,
  rw extend_by_zero,
  simp only [dite_eq_ite],
  cases D,
  dsimp at *,
  simp only [ite_eq_left_iff] at *,
  intros A,
  solve_by_elim,
end

lemma ext_by_zero_eq' (D: open_subs) (f : D.1 → ℂ) (y : ℂ) (h: y ∈ (D.1 : set ℂ)):
  extend_by_zero (f ) y = (f ⟨ y, h⟩) :=
begin
 rw extend_by_zero,
 simp,
 cases D,
 dsimp at *,
 exact dif_pos h,
end

lemma ext_by_zero_apply (D: open_subs) (f : D.1 → ℂ) (y : D.1) :
  extend_by_zero (f ) y = (f y) :=
begin
  have:= ext_by_zero_eq' D f y y.2,
  rw this,
  simp,
end

lemma const_hol  (c : ℂ) : is_holomorphic_on (λ z : D.1, (c : ℂ)) :=
begin
  rw is_holomorphic_on,
  intro z,
  use (0: ℂ),
  have h1:=has_deriv_within_at_const  z.1 D.1 c,
  have H:= has_deriv_within_at.congr_of_eventually_eq_of_mem h1 _ z.property ,
  convert H,
  rw  eventually_eq,
  rw eventually_iff_exists_mem,
  use D.1,
  have H2:= ext_by_zero_eq D c,
  split,
  have h3:= D.2,
  simp at h3,
  have h4:=is_open.mem_nhds h3 z.2,
  simp only [subtype.val_eq_coe],
  convert h4,
  simp,
  rw nhds_within,
  simp only [inf_eq_left, le_principal_iff],
  exact h4,
  exact H2,
end

lemma zero_hol (D: open_subs) : is_holomorphic_on (λ z : D.1, (0 : ℂ)) :=
begin
  apply const_hol (0:ℂ ),
end

lemma one_hol (D: open_subs) : is_holomorphic_on (λ z : D.1, (1 : ℂ)) :=
begin
apply const_hol (1: ℂ),

end
lemma add_hol (f g : D.1 → ℂ) (f_hol : is_holomorphic_on f) (g_hol : is_holomorphic_on g) :
  is_holomorphic_on (f + g) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  cases g_hol z₀ with g'z₀ Hg,
  existsi (f'z₀ + g'z₀),
  rw extend_by_zero_add,
  have:=has_deriv_within_at.add Hf Hg,
  exact this,
end

lemma mul_hol (f g : D.1 → ℂ) (f_hol : is_holomorphic_on f) (g_hol : is_holomorphic_on g) :
  is_holomorphic_on (f * g) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  cases g_hol z₀ with g'z₀ Hg,
  existsi f'z₀*(extend_by_zero g z₀) + (extend_by_zero f z₀)*g'z₀,
  rw extend_by_zero_mul,
 have:=has_deriv_within_at.mul Hf Hg,
 exact this,
end

lemma neg_hol (f : D.1 → ℂ) (f_hol : is_holomorphic_on f) : is_holomorphic_on (-f) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ H,
  existsi -f'z₀,
  rw extend_by_zero_neg,
  have h3:=has_deriv_within_at.neg H,
  exact h3,
end

/--The ring of holomorphic functions-/
def hol_ring (D: open_subs) : subring (D.1 → ℂ) :=
{ carrier := {f : D.1 → ℂ | is_holomorphic_on f},
  zero_mem' := zero_hol D,
 add_mem'  := add_hol,
 neg_mem'  := neg_hol,
 mul_mem'  := mul_hol,
 one_mem'  := one_hol D
}

lemma smul_hol (c : ℂ) (f : D.1 → ℂ) (f_hol : is_holomorphic_on f) : is_holomorphic_on (c • f) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  existsi c * f'z₀,
  rw extend_by_zero_smul,
  have h2:= has_deriv_within_at.const_smul c Hf,
  exact h2,

end

def hol_submodule (D: open_subs) : submodule (ℂ)  (D.1 → ℂ) :=
{ carrier := {f : D.1 → ℂ | is_holomorphic_on f},
  zero_mem' := zero_hol D,
  add_mem' := add_hol,
  smul_mem' := smul_hol}

lemma aux (s t d : set ℂ) (h :  s ⊆ t) : s ∩ d ⊆ t :=
begin
  intros x hx,
  apply h,
  simp at *,
  apply hx.1,
end

lemma aux2 (x : ℂ) (a b : ℝ) : metric.ball x a ∩ metric.ball x b = metric.ball x (min a b) :=
begin
  ext,
  split,
  simp only [and_imp, metric.mem_ball, set.mem_inter_eq, lt_min_iff],
  intros ha hb,
  simp only [ha, hb, and_self],
  simp only [and_imp, metric.mem_ball, set.mem_inter_eq, lt_min_iff],
  intros ha hb,
  simp only [ha, hb, and_self],
end


lemma diff_on_diff (f : D.1 → ℂ) (h : ∀ x : D.1, ∃ (ε: ℝ), 0 < ε ∧ (metric.ball x.1 ε ⊆ D.val ) ∧
  differentiable_on ℂ (extend_by_zero f) (metric.ball x ε)) :
  differentiable_on ℂ (extend_by_zero f) D.1 :=
begin
  simp_rw differentiable_on at *,
  simp_rw differentiable_within_at at *,
  intros x hx,
  have hh := h ⟨x, hx⟩,
  obtain ⟨ε, hε, hb, H⟩:= hh,
  have HH:= H x,
  simp only [metric.mem_ball, subtype.coe_mk, dist_self] at HH,
  have HHH:= HH hε,
  obtain ⟨f', hf'⟩:= HHH,
  use f',
  simp_rw has_fderiv_within_at_iff_tendsto at *,
  rw metric.tendsto_nhds at *,
  intros δ hδ,
  have hf2 := hf'  δ hδ,
  rw filter.eventually_iff_exists_mem at *,
  simp only [exists_prop, metric.mem_ball, gt_iff_lt, topological_space.opens.mem_coe,
    dist_zero_right, continuous_linear_map.map_sub, set_coe.forall, subtype.coe_mk,
    subtype.val_eq_coe,norm_eq_abs, norm_mul, norm_inv] at *,
  obtain ⟨S, hS, HD⟩ := hf2,
  simp_rw metric.mem_nhds_within_iff at *,
  obtain ⟨e, he, HE⟩:= hS,
  use S,
  split,
  use min e ε,
  simp only [gt_iff_lt, topological_space.opens.mem_coe, lt_min_iff, subtype.val_eq_coe] at *,
  simp only [he, hε, and_self],
  simp only [true_and],
  have : metric.ball x e ∩ metric.ball x ε = metric.ball x (min e ε), by {apply aux2,},
  rw this at HE,
  apply aux _ _ _ HE,
  apply HD,
end

lemma tendsto_unif_extend_by_zero (F : ℕ → D.1 → ℂ) (f : D.1 → ℂ)
(h: tendsto_uniformly F f filter.at_top ) :
  tendsto_uniformly_on (λ (n : ℕ), extend_by_zero (F n)) (extend_by_zero f) filter.at_top D.1 :=
begin
  simp_rw metric.tendsto_uniformly_on_iff,
  rw metric.tendsto_uniformly_iff at h,
  intros ε hε,
  have h2:= h ε hε,
  simp only [gt_iff_lt, topological_space.opens.mem_coe, ge_iff_le, nonempty_of_inhabited,
  set_coe.forall, eventually_at_top, subtype.val_eq_coe] at *,
  obtain ⟨a, ha⟩:= h2,
  use a,
  intros b hb x hx,
  have hf:= ext_by_zero_apply D f ⟨x, hx⟩,
  have hFb:= ext_by_zero_apply D (F b) ⟨x, hx⟩,
  simp only [topological_space.opens.mem_coe, subtype.coe_mk, subtype.val_eq_coe] at *,
  rw hf,
  rw hFb,
  apply ha b hb x hx,
end
