import number_theory.mod_forms.Eisenstein_series
import measure_theory.integral.unform_limits_of_holomorphic
import .mod_forms2


universes u v w

open complex modular_forms

open_locale big_operators nnreal classical filter topological_space manifold

local notation `ℍ` := upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space, upper_half_plane_is_open⟩: open_subs)
noncomputable theory

namespace Eisenstein_series

lemma eisen_square_diff_on (k : ℤ)  (hkn : k ≠ 0) (n : ℕ) :
  is_holomorphic_on (λ (z : ℍ'), eisen_square k n z) :=
begin
  rw ←  is_holomorphic_on_iff_differentiable_on,
  have h1 : extend_by_zero (λ (z : ℍ'), eisen_square k n z) =
  λ x : ℂ,  ∑ y in (Square n), (extend_by_zero (λ z : ℍ', Eise k z y)) x,
  by {simp_rw eisen_square,
  funext z,
  by_cases h : z ∈ ℍ'.1,
  simp only [extend_by_zero, finset.sum_dite_irrel, finset.sum_const_zero] at *,
  simp only [extend_by_zero, finset.sum_dite_irrel, finset.sum_const_zero] at *,},
  simp only [ne.def] at *,
  rw h1,
  apply differentiable_on.sum,
  intros i hi,
  apply Eise'_has_diff_within_at k i hkn,
end

def eisen_square' (k : ℤ) (n: ℕ) : ℍ' → ℂ:=
λ (z : ℍ'), ∑ x in (finset.range n), eisen_square k x z

lemma eisen_square'_diff_on (k : ℤ)  (hkn : k ≠ 0) (n : ℕ) :
  is_holomorphic_on (eisen_square' k n ) :=
begin
  rw ←  is_holomorphic_on_iff_differentiable_on,
  have h1 : extend_by_zero ( eisen_square' k n) =
  λ x : ℂ,  ∑ y in (finset.range n), (extend_by_zero (λ z : ℍ', eisen_square k y z)) x,
  by{simp_rw eisen_square',
  funext z,
  by_cases h : z ∈ ℍ'.1,
  simp only [extend_by_zero, finset.sum_dite_irrel, finset.sum_const_zero] at *,
  simp only [extend_by_zero, finset.sum_dite_irrel, finset.sum_const_zero] at *},
  rw h1,
  apply differentiable_on.sum,
  intros i hi,
  have := eisen_square_diff_on k hkn i,
  rw ←  is_holomorphic_on_iff_differentiable_on at this,
  apply this,
end

lemma Eisen_partial_tends_to_uniformly_on_ball (k: ℕ) (h : 3 ≤ k) (z : ℍ') : ∃ (A B ε : ℝ),
  0 < ε ∧ metric.closed_ball z ε ⊆ (upper_half_space_slice A B)  ∧  0 < B ∧ ε < B ∧
  (tendsto_uniformly_on (eisen_square' k) (Eisenstein_series_of_weight_ k)
  filter.at_top (metric.closed_ball z ε)   ) :=
begin
  have h1:= closed_ball_in_slice z,
  obtain ⟨A, B, ε, hε, hB, hball, hA, hεB⟩ := h1,
  use A,
  use B,
  use ε,
  simp only [hε, hB, hball, hεB, true_and],
  have hz: z ∈ (upper_half_space_slice A B), by {apply hball, simp  [hε .le],},
  have hu:= (Eisen_partial_tends_to_uniformly k h A B hA hB),
  have hu2:
    tendsto_uniformly_on (Eisen_par_sum_slice k A B ) (Eisenstein_series_restrict k A B)
    filter.at_top (metric.closed_ball ⟨z, hz⟩ ε), by {apply hu.tendsto_uniformly_on},
  clear hu,
  simp_rw Eisenstein_series_restrict at *,
  simp_rw metric.tendsto_uniformly_on_iff at *,
  simp_rw Eisen_par_sum_slice at *,
  simp_rw Eisen_square_slice at *,
  simp_rw eisen_square',
  simp only [filter.eventually_at_top, abs_of_real, gt_iff_lt, ge_iff_le, nonempty_of_inhabited,
  metric.mem_closed_ball, subtype.forall, set_coe.forall, upper_half_plane.coe_im,
  subtype.coe_mk, subtype.val_eq_coe, coe_coe, upper_half_plane.coe_re] at *,
  intros δ hδ,
  have hu3:= hu2 δ hδ,
  clear hu2,
  obtain ⟨a, ha⟩:=hu3,
  use a,
  intros b hb x hx,
  have hxx: x ∈ upper_half_space_slice A B,
  by {apply hball, simp only [hx, metric.mem_closed_ball],},
  have hxu := upper_half_plane.im_pos x,
  have ha2:= ha b hb x hxu,
  apply ha2,
  apply hx,
  simp only [slice_mem],
  apply hxx,
end

lemma Eisen_partial_tends_to_uniformly_on_ball' (k: ℕ) (h : 3 ≤ k) (z : ℍ') : ∃ (A B ε : ℝ),
  0 < ε ∧ metric.closed_ball z ε ⊆ (upper_half_space_slice A B)  ∧  0 < B ∧ ε < B ∧
  (tendsto_uniformly_on ( λ n, extend_by_zero ( eisen_square' k n))
  (extend_by_zero (Eisenstein_series_of_weight_ k))
  filter.at_top (metric.closed_ball z ε)   ) :=
begin
  have H := Eisen_partial_tends_to_uniformly_on_ball k h z,
  obtain ⟨A, B, ε, hε, hball, hB, hεB, hunif⟩ :=H,
  use A,
  use B,
  use ε,
  simp only [hε, hball, hB, hεB, true_and],
  simp_rw metric.tendsto_uniformly_on_iff at *,
  intros ε' hε',
  have h2:= hunif ε' hε',
  simp only [filter.eventually_at_top, gt_iff_lt, ge_iff_le, metric.mem_closed_ball] at *,
  obtain ⟨a, ha⟩:= h2,
  use a,
  have Hba:= ball_in_upper_half z A B ε hB hε hεB hball,
  intros b hb x hx,
  have hxx : x ∈ ℍ'.1, by {apply Hba, simp [hx],},
  have hf:= ext_by_zero_apply ℍ' (Eisenstein_series_of_weight_ k) ⟨x, hxx⟩,
  let F: ℕ → ℍ' → ℂ := λ n,  eisen_square' k n,
  have hFb:= ext_by_zero_apply ℍ' (F b) ⟨x, hxx⟩,
  simp only [topological_space.opens.mem_coe, subtype.coe_mk, subtype.val_eq_coe] at *,
  rw hf,
  rw hFb,
  apply ha b hb ⟨x, hxx⟩ hx,
end


lemma Eisenstein_is_holomorphic (k: ℕ) (hk : 3 ≤ k):
  is_holomorphic_on (modular_forms.hol_extn (Eisenstein_series_of_weight_ k)):=
begin
  rw ←  is_holomorphic_on_iff_differentiable_on,
  apply diff_on_diff,
  intro x,
  have H:= Eisen_partial_tends_to_uniformly_on_ball' k hk x,
  obtain ⟨A, B, ε, hε, hball, hB, hεB, hunif⟩ :=H,
  use 2⁻¹*ε,
  have hball2: metric.closed_ball ↑x ε ⊆ ℍ'.1,
  by {apply ball_in_upper_half x A B ε hB hε hεB hball,},
  split,
  ring_nf,
  nlinarith,
  split,
  intros w hw,
  have hwa : w ∈ ℍ'.1,
  by { apply hball2, simp, simp at hw, apply le_trans hw.le, field_simp, linarith,},
  apply hwa,
  have hkn : (k : ℤ) ≠ 0, by {norm_cast, linarith,},
  let F: ℕ → ℂ → ℂ := λ n, extend_by_zero ( eisen_square' k n),
  have hdiff : ∀ (n : ℕ), differentiable_on ℂ (F n) (metric.closed_ball x ε),
  by {intro n,
  have := eisen_square'_diff_on k hkn n,
  rw ← is_holomorphic_on_iff_differentiable_on at this,
  simp_rw F,
  apply this.mono,
  apply hball2,},
  apply uniform_of_diff_circle_int_is_diff F (extend_by_zero (Eisenstein_series_of_weight_ k)) x ε (2⁻¹*ε) hε _ _
  hdiff hunif,
  ring_nf,
  linarith,
  simp [hε.le],
end

lemma Eisenstein_is_mdiff (k : ℕ) (hk : 3 ≤ k):
  mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (↑(Eisenstein_series_of_weight_ k) : ℍ' → ℂ):=
begin
rw mdiff_iff_holo,
apply Eisenstein_is_holomorphic,
apply hk,
end

def my_vadd : ℤ → ℍ → ℍ :=
λ n, λ (z : ℍ), ⟨z.1+n, by {simp, apply z.2},⟩

instance : has_vadd ℤ ℍ := {
vadd:= my_vadd
}

lemma my_add_im (n : ℤ) (z : ℍ) : (my_vadd n z).im = z.im :=
begin
  simp_rw my_vadd,
  simp only [subtype.val_eq_coe],
  simp_rw upper_half_plane.im,
  simp only [add_zero, int_cast_im, add_im, subtype.coe_mk],
end

lemma my_add_re (n : ℤ) (z : ℍ) : (my_vadd n z).re = z.re + n :=
begin
  simp_rw my_vadd,
  simp only [subtype.val_eq_coe],
  simp_rw upper_half_plane.re,
  simp only [int_cast_re, add_re, subtype.coe_mk],
end


lemma zero_vadd' (z : ℍ) : my_vadd (0: ℤ) z = z :=
begin
  simp_rw my_vadd,
  simp only [add_zero, int.cast_zero, subtype.coe_eta, subtype.val_eq_coe],
end

lemma add_vadd'  (n m : ℤ) (z : ℍ): my_vadd (n+m) z = my_vadd n (my_vadd m z)   :=
begin
  simp_rw my_vadd,
  simp only [int.cast_add, subtype.val_eq_coe],
  abel,
end

instance : add_action ℤ ℍ :={
  zero_vadd := by {apply zero_vadd',},
  add_vadd := by {apply add_vadd',},
}

def Tn (n : ℤ) : matrix  (fin 2) (fin 2 ) ℤ := ![![1, n], ![0, 1]]

lemma Tndet (n : ℤ) : matrix.det (Tn(n)) = 1 :=
begin
  simp_rw Tn,
  rw matrix.det_fin_two,
  simp only [matrix.head_cons, mul_one, sub_zero, matrix.cons_val_one, mul_zero,
  matrix.cons_val_zero],
end

lemma coe_aux (γ : SL2Z) :
 ∀ i j, ((γ : matrix.GL_pos (fin 2) ℝ) i j : ℝ) = ((γ i j : ℤ) : ℝ) :=
begin
  intros i j,
  have :=SL2Z.mat_vals  γ i j,
  simp only [of_real_int_cast, subtype.val_eq_coe, matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at *,
  simp,
end

def TN (n : ℤ) : SL2Z := ⟨Tn (n), Tndet n⟩

lemma TN00 (n : ℤ) : ((TN n) : matrix.GL_pos (fin 2) ℝ) 0 0 = 1 :=
begin
  simp_rw TN,
  simp_rw Tn,
  simp_rw coe_aux,
  dsimp at *,
  simp only [int.cast_one] at *,
end


lemma TN01 (n : ℤ) : ((TN n) : matrix.GL_pos (fin 2) ℝ) 0 1 = n :=
begin
  simp_rw TN,
  simp_rw Tn,
  simp_rw coe_aux,
  dsimp at *,
  simp only [matrix.head_cons, matrix.cons_val_one] at *,
end

lemma TN10 (n : ℤ) : ((TN n) : matrix.GL_pos (fin 2) ℝ) 1 0 = 0 :=
begin
  simp_rw TN,
  simp_rw Tn,
  simp_rw coe_aux,
  dsimp at *,
  simp only [int.cast_zero, matrix.cons_val_one, matrix.cons_val_zero, matrix.head_cons] at *,
end

lemma TN11 (n : ℤ) : ((TN n) : matrix.GL_pos (fin 2) ℝ) 1 1 = 1 :=
begin
  simp_rw TN,
  simp_rw Tn,
  simp_rw coe_aux,
  dsimp at *,
  simp only [matrix.head_cons, int.cast_one, matrix.cons_val_one] at *,
end

lemma mod_form_periodic (k : ℤ) (f : ℍ → ℂ)
  (h: f ∈ (modular_forms.weakly_modular_submodule k (⊤ : subgroup SL2Z))) : ∀ (z : ℍ) (n : ℤ),
  f( ((TN n) : matrix.GL_pos (fin 2) ℝ)  • z ) = f(z) :=
begin
  simp only [modular_forms.wmodular_mem', coe_coe] at h,
  intros z n,
  have htop : (TN n) ∈ (⊤ : subgroup SL2Z), by {simp,},
  have H:= h ⟨(TN n), htop⟩ z,
  simp only [subgroup.coe_mk] at H,
  have hoo' : (⟨(TN n), htop⟩ : ( (⊤ : subgroup SL2Z)) )  1 0 = 0, by {refl,},
  have h11' : (⟨(TN n), htop⟩ : ( (⊤ : subgroup SL2Z)) )  1 1 = 1, by {refl,},
  simp_rw hoo' at H,
  simp_rw h11' at H,
  simp [int.cast_zero, one_mul, zero_mul, int.cast_one, zero_add, one_zpow₀] at H,
  simp,
  apply H,
end

lemma smul_expl (n : ℤ) (z : ℍ) : (((TN n) : matrix.GL_pos (fin 2) ℝ)  • z ) = n +ᵥ z :=
begin
  simp [coe_coe],
  have := upper_half_plane.coe_smul ((TN n) : matrix.GL_pos (fin 2) ℝ) z,
  have h1:= (TN00 n),
  have h2:= (TN01 n),
  have h3:= (TN10 n),
  have h4:= (TN11 n),
  ext,
  simp only [upper_half_plane.num, upper_half_plane.denom, eq_self_iff_true, coe_coe,
  upper_half_plane.coe_smul, upper_half_plane.coe_re] at *,
  simp_rw [h1, h2, h3,h4],
  simp only [int_cast_re, one_mul, of_real_zero, zero_mul, add_re, of_real_int_cast, zero_add,
  of_real_one, div_one, upper_half_plane.coe_re],
  convert (my_add_re n z).symm,
  simp only [upper_half_plane.num, upper_half_plane.denom, eq_self_iff_true,
  upper_half_plane.coe_im, coe_coe, upper_half_plane.coe_smul] at *,
  simp_rw [h1, h2, h3,h4],
  simp only [add_zero, one_mul, of_real_zero, int_cast_im, zero_mul, add_im, of_real_int_cast,
  zero_add, upper_half_plane.coe_im, of_real_one, div_one],
  convert (my_add_im n z).symm,
end

lemma abs_floor_sub (r : ℝ) :  |(r - (int.floor r))| < 1 :=
begin
simp only [int.self_sub_floor],
rw _root_.abs_of_nonneg (int.fract_nonneg r),
apply (int.fract_lt_one r),
end

lemma upp_half_translation (z : ℍ) : ∃ (n : ℤ),
  (((TN n) : matrix.GL_pos (fin 2) ℝ)  • z) ∈ (upper_half_space_slice 1 z.1.2) :=
begin
  let n:= (int.floor z.1.1),
  use -n,
  have:= smul_expl (-n) z,
  simp_rw this,
  simp only [abs_of_real, ge_iff_le, slice_mem, upper_half_plane.coe_im, subtype.val_eq_coe,
  upper_half_plane.coe_re],
  have him := my_add_im (-n) z,
  have hre := my_add_re (-n) z,
  split,
  have h1: (-n +ᵥ z).re = (my_vadd (-n) z).re, by {refl,},
  rw h1,
  rw hre,
  simp,
  apply (abs_floor_sub z.1.1).le,
  have h2: (-n +ᵥ z).im = (my_vadd (-n) z).im, by {refl,},
  rw h2,
  rw him,
  apply le_abs_self,
end

lemma eis_bound_by_real_eis (k : ℕ) (z : ℍ) (hk : 3 ≤ k) :
  complex.abs (Eisenstein_series_of_weight_ k z) ≤ (real_Eisenstein_series_of_weight_ k z) :=
begin
  simp_rw Eisenstein_series_of_weight_,
  simp_rw real_Eisenstein_series_of_weight_,
  simp_rw real_Eise,
  simp_rw Eise,
  apply abs_tsum',
  have := real_eise_is_summable k z hk,
  simp_rw real_Eise at this,
  simp only [one_div, complex.abs_pow, complex.abs_inv, norm_eq_abs, zpow_coe_nat] at *,
  apply this,
end

lemma Eisenstein_is_bounded (k: ℕ) (hk : 3 ≤ k) :
   Eisenstein_series_of_weight_ k  ∈  is_bound_at_infinity  :=
begin
simp only [modular_forms.bound_mem, subtype.forall, upper_half_plane.coe_im],
have h2: 0 < (2 : ℝ), by {linarith,},
set M : ℝ :=(8/(rfunct (lbpoint 1 2 h2) )^k)*Riemann_zeta (k-1),
use M,
use 2,
intros z hz hz2,
have trans := upp_half_translation ⟨z,hz⟩,
obtain ⟨n, hn⟩:= trans,
have mod_period := mod_form_periodic k (λ z : ℍ, Eisenstein_series_of_weight_ k z)
  (Eisenstein_is_wmodular (⊤ : subgroup SL2Z) k) ⟨z, hz⟩ n,
simp only [coe_coe] at mod_period,
simp_rw ← mod_period,
set Z : ℍ := (((TN n) : matrix.GL_pos (fin 2) ℝ)  • ⟨z,hz⟩),
have H := eis_bound_by_real_eis k Z hk,
simp_rw  Z at H,
apply le_trans H,
simp_rw M,
have HR:=Real_Eisenstein_bound_unifomly_on_stip k hk 1 2 h2,
have hZ : Z ∈ upper_half_space_slice 1 2,
by {have:= smul_expl n ⟨z, hz⟩,
simp_rw Z at *,
rw this,
rw this at hn,
simp only [abs_of_real, ge_iff_le, slice_mem, upper_half_plane.coe_im, subtype.val_eq_coe,
upper_half_plane.coe_re] at hn,
simp only [abs_of_real, ge_iff_le, slice_mem, upper_half_plane.coe_im, subtype.val_eq_coe,
upper_half_plane.coe_re],
split,
apply hn.1,
have hadd: (n +ᵥ (⟨z,hz⟩ : ℍ) ).1.im = (my_vadd (n) ⟨z,hz⟩).im, by {refl,},
simp only [upper_half_plane.coe_im, subtype.val_eq_coe] at hadd,
simp_rw hadd,
rw my_add_im n ⟨z, hz⟩,
apply le_trans hz2,
apply le_abs_self,},
apply HR ⟨Z, hZ⟩,
end

lemma Eisenstein_series_is_modular_form  (k : ℕ) (hk : 3 ≤ k) :
 is_modular_form_of_lvl_and_weight (⊤ : subgroup SL2Z) k (Eisenstein_series_of_weight_ k) :=
 {hol:= by {apply Eisenstein_is_mdiff k hk},
 transf := by {apply Eisenstein_is_wmodular (⊤ : subgroup SL2Z) k},
 infinity := by {intros A,
 rw (wmodular_mem k (⊤ : subgroup SL2Z) (Eisenstein_series_of_weight_ k )).1
 (Eisenstein_is_wmodular (⊤ : subgroup SL2Z) k) A,
 apply Eisenstein_is_bounded k hk}}

end Eisenstein_series
