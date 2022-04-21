import analysis.complex.cauchy_integral
import analysis.analytic.basic
import analysis.calculus.parametric_interval_integral
import data.complex.basic

open topological_space set measure_theory interval_integral metric filter function complex
open_locale interval real nnreal ennreal topological_space big_operators

noncomputable theory

universes u v

variables {E : Type u} [normed_group E] [normed_space ℂ E] [measurable_space E] [borel_space E]
  [second_countable_topology E] [complete_space E]

namespace complex

lemma has_cauchy_integral_form {R : ℝ} {z w : ℂ} (hw : w ∈ ball z R)
  {f : ℂ → E} (hd : differentiable_on ℂ f (closed_ball z R)) :
  f w  = (1/(2 • π • I)) •  ∮ z in C(z, R), (z - w)⁻¹ • f z  :=
begin
  have := circle_integral_sub_inv_smul_of_continuous_on_of_differentiable_on hw hd.continuous_on
  (hd.mono ball_subset_closed_ball),
  rw this,
  simp only [real_smul, nsmul_eq_mul, nat.cast_bit0, nat.cast_one, one_div, ←mul_assoc],
  have hc : (2 * ↑π * I) ≠ 0,
  by {simp only [of_real_eq_zero, false_or, ne.def, bit0_eq_zero, one_ne_zero, mul_eq_zero],
  simp only [real.pi_ne_zero, I_ne_zero, not_false_iff, or_self],},
  apply (inv_smul_smul₀ hc (f w)).symm,
  end

def circle_integral_function (R : ℝ) (z : ℂ) (f : ℂ → E) (w : ℂ) : (ℝ → E) := λ θ,
(1/(2 • π • I)) • deriv (circle_map z R) θ • ((circle_map z R θ) - w)⁻¹ • f  (circle_map z R θ)

def circle_integral_function_deriv (R : ℝ) (z : ℂ) (f : ℂ → E) (w : ℂ) : (ℝ → E) := λ θ,
  (1/(2 • π • I)) • deriv (circle_map z R) θ •
  (((circle_map z R θ) - w)^(2))⁻¹ • f  (circle_map z R θ)

def circle_integral_function_deriv_alt (R : ℝ) (z : ℂ) (f : ℂ → E) (w : ℂ) : (ℝ → E) := λ θ,
   (((circle_map z R θ) - w)⁻¹ )^(2) • (1/(2 • π • I)) •
   deriv (circle_map z R) θ • f  (circle_map z R θ)

lemma circle_integral_function_deriv_eq_alt (R : ℝ) (z : ℂ) (f : ℂ → E) (w : ℂ) :
circle_integral_function_deriv  R z f w = circle_integral_function_deriv_alt  R z f w :=
begin
simp_rw [circle_integral_function_deriv, circle_integral_function_deriv_alt],
ext,
simp_rw ←mul_smul,
simp_rw ←mul_assoc,
field_simp,
simp_rw mul_comm,
end

lemma circle_integral_function_deriv_eq (R : ℝ) (z : ℂ) (f : ℂ → E) (w : ℂ) :
  circle_integral_function_deriv  R z f w = (λ θ,
  ((circle_map z R θ) - w)⁻¹ • (circle_integral_function R z f w θ)) :=
begin
simp_rw [circle_integral_function_deriv, circle_integral_function, pow_two],
ext,
field_simp,
simp_rw [←one_div_mul_one_div,←mul_smul, ←mul_assoc],
field_simp,
have H : ∀ a b c d e : ℂ, a/(e * d * b * c) = a/ (c * e * d * b) ,
 by {intros a b c d e, have: (e * d * b * c) = (c * e * d * b) , by {ring,}, rw this, },
simp_rw H,
end

lemma circle_integral_function_circle_int (R : ℝ) (z : ℂ) (f : ℂ → E) (w : ℂ) :
∫ (θ : ℝ) in 0..2 * π, circle_integral_function R z f w θ =
(1/(2 • π • I)) •  ∮ z in C(z, R), (z - w)⁻¹ • f z :=
begin
  simp_rw [circle_integral_function,circle_integral,deriv_circle_map, circle_map],
  simp only [real_smul, nsmul_eq_mul, nat.cast_bit0, nat.cast_one, one_div,
  interval_integral.integral_smul, zero_add],
end

lemma circle_map_ne_on_ball (R : ℝ) (hR: 0 < R) (z w : ℂ) (hw : w ∈ ball z R) :
∀  x : ℝ, circle_map z R x - w ≠ 0 :=
begin
intros x hx,
by_contra,
have h1 : circle_map z R x = w, by {exact sub_eq_zero.mp hx,},
rw ←h1 at hw,
simp only [mem_ball] at hw,
have  h2 := circle_map_mem_sphere z hR.le x,
rw mem_sphere at h2,
rw h2 at hw,
simp at hw,
apply hw,
end

lemma circle_map_inv_continuous_on (R : ℝ) (hR: 0 < R) (z w : ℂ) (hw : w ∈ ball z R) :
 continuous_on (λ θ,  (circle_map z R θ - w)⁻¹) [0, 2*π] :=
begin
simp_rw ←one_div,
apply continuous_on.div,
apply continuous_const.continuous_on,
apply continuous_on.sub,
apply (continuous_circle_map z R).continuous_on,
apply continuous_const.continuous_on,
intros x hx,
apply circle_map_ne_on_ball R hR z w hw,
end

lemma circle_integral_function_cont_on_ICC (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z w : ℂ)
  (hf : continuous_on f (sphere z R)  )
  (hw : w ∈ ball z R):
  continuous_on (circle_integral_function R z f w) [0, 2*π] :=
begin
rw circle_integral_function,
apply continuous_on.smul,
exact continuous_const.continuous_on,
apply continuous_on.smul,
simp_rw deriv_circle_map,
have:= (continuous_circle_map 0 R).continuous_on,
apply continuous_on.mul,
apply this,
exact continuous_const.continuous_on,
apply continuous_on.smul,
apply circle_map_inv_continuous_on R hR z w hw,
apply continuous_on.comp,
apply hf,
apply (continuous_circle_map z R).continuous_on,
rw maps_to,
intros v hv,
apply circle_map_mem_sphere,
apply hR.le,
end

lemma circle_integral_function_deriv_cont_on_ICC (R : ℝ) (hR: 0 < R) (f : ℂ → E) (z w : ℂ)
  (hf : continuous_on f (sphere z R)  )
  (hw : w ∈ ball z R):
  continuous_on (circle_integral_function_deriv R z f w) [0, 2*π] :=
begin
rw circle_integral_function_deriv_eq,
apply continuous_on.smul,
apply circle_map_inv_continuous_on R hR z w hw,
apply circle_integral_function_cont_on_ICC R hR f z w hf hw,
end

lemma circle_integral_function_cont_on (R : ℝ) (hR: 0 < R) (f : ℂ → E) (z w : ℂ)
  (hf : continuous_on f (sphere z R))
  (hw : w ∈ ball z R):
  continuous_on (circle_integral_function R z f w) (Ι 0 (2 * π)) :=
begin
 have := circle_integral_function_cont_on_ICC R hR f z w hf hw,
 apply this.mono,
 rw interval_oc_of_le (real.two_pi_pos.le),
 rw interval_of_le (real.two_pi_pos.le),
 exact Ioc_subset_Icc_self,
end

def fbound3 (R : ℝ) (z : ℂ): (ℂ × ℝ → ℂ) :=
  λ w, circle_integral_function_deriv R z (λ x, 1) w.1 w.2

def fbound3_rest (R : ℝ) (z : ℂ): ℝ → (ℂ → ℂ) :=
 λ θ, λ w, circle_integral_function_deriv R z (λ x, 1) w θ

lemma cont_on_prod_sub (s : set ℝ) (f : ℝ → ℂ) (g : ℂ → ℂ) (v : set ℂ) (hf : continuous_on f s)
(hg : continuous_on g v) :
continuous_on (λ (t : ℂ × ℝ), f(t.2)-g (t.1)) (v ×ˢ s):=
begin
apply continuous_on.sub,
rw metric.continuous_on_iff at *,
simp only [mem_prod, gt_iff_lt, and_imp, prod.forall, exists_prop] at *,
simp_rw prod.dist_eq,
intros a b ha hb ε hε,
have HF:= hf  b hb ε hε,
obtain ⟨d, hd, hdd⟩:=HF,
refine ⟨d, hd, _⟩,
intros x y hx hy hdist,
simp only [max_lt_iff] at hdist,
apply hdd y hy hdist.2,
rw metric.continuous_on_iff at *,
simp only [mem_prod, gt_iff_lt, and_imp, prod.forall, exists_prop] at *,
simp_rw prod.dist_eq,
intros a b ha hb ε hε,
have HG:= hg a ha ε hε,
obtain ⟨d, hd, hdd⟩:=HG,
refine ⟨d, hd, _⟩,
intros x y hx hy hdist,
simp only [max_lt_iff] at hdist,
apply hdd x hx hdist.1,
end


lemma circle_int_funct_cont_on_prod  (R r : ℝ) (hR: 0 < R) (hr : r < R) (z : ℂ) :
 continuous_on (λ (w : ℂ × ℝ), ((circle_map z R w.snd - w.fst)⁻¹)^2)
  ( ((closed_ball z r) ×ˢ (interval 0 (2*π))) : set (ℂ × ℝ)) :=
begin
apply continuous_on.pow,
simp_rw ←one_div,
apply continuous_on.div,
apply continuous_const.continuous_on,
have:= cont_on_prod_sub (interval 0 (2*π)) (circle_map z R) (λ x, x) (closed_ball z r),
simp only at this,
apply this,
apply (continuous_circle_map z R).continuous_on,
apply continuous_on_id,
simp only [mem_prod, mem_closed_ball, ne.def, and_imp, prod.forall],
intros a b ha hb,
apply circle_map_ne_on_ball,
apply hR,
simp only [mem_ball],
linarith,
end

lemma cont_on_prod (s : set ℝ) (f : ℝ → ℂ) (hf : continuous_on f s) (v : set ℂ) :
continuous_on (λ (t : ℂ × ℝ), f(t.2)) (v ×ˢ s):=
begin
rw metric.continuous_on_iff at *,
simp only [mem_prod, gt_iff_lt, and_imp, prod.forall, exists_prop],
intros a b ha hb ε hε,
have HF:= hf  b hb ε hε,
obtain ⟨d, hd, hdd⟩:=HF,
refine ⟨d, hd, _⟩,
intros x y hx hy hdist,
rw prod.dist_eq at hdist,
simp only [max_lt_iff] at hdist,
apply hdd y hy hdist.2,
end


lemma fbound3_continuous_on (R r : ℝ) (hR: 0 < R) (hr : r < R) (z : ℂ) :
continuous_on  (complex.abs ∘ (fbound3 R z ))
  ( ((closed_ball z r) ×ˢ   (interval 0 (2*π))) : set (ℂ × ℝ)) :=
begin
  have c1:= continuous_abs,
  have c2: continuous_on abs ⊤, by {apply continuous.continuous_on c1},
  apply continuous_on.comp c2,
  rw fbound3,
  simp_rw circle_integral_function_deriv_eq_alt,
  simp_rw circle_integral_function_deriv_alt,
  apply continuous_on.smul,
  apply circle_int_funct_cont_on_prod R r hR hr,
  apply continuous_on.smul,
  apply continuous_const.continuous_on,
  simp,
  have c1:=(continuous_circle_map 0 R).continuous_on ,
  apply continuous_on.mul,
  apply cont_on_prod _ _ c1 _,
  apply continuous_const.continuous_on,
  rw maps_to,
  simp,
end

instance : has_set_prod (set  ℂ) (set ℝ) (set (ℂ × ℝ )) := infer_instance

lemma fbounded3 (R r : ℝ) (hR: 0 < R) (hr : r < R) (hr' : 0 ≤  r)  (z : ℂ) :
 ∃ (x :  ((closed_ball z r) ×ˢ  (interval 0 (2*π)) : set (ℂ × ℝ)) ),
 ∀ (y :  ((closed_ball z r) ×ˢ  (interval 0 (2*π)) : set (ℂ × ℝ)) ),
 complex.abs (fbound3 R  z  y) ≤ complex.abs(fbound3 R z x):=
begin
have cts:= fbound3_continuous_on R r hR hr z,
  have comp : is_compact   ( ((closed_ball z r) ×ˢ (interval 0 (2*π))) : set (ℂ × ℝ)),
  by {apply is_compact.prod,
  exact proper_space.is_compact_closed_ball z r,
  apply is_compact_interval,},
  have none : (((closed_ball z r) ×ˢ (interval 0 (2*π))) : set (ℂ × ℝ)).nonempty ,
  by {apply nonempty.prod,
  simp only [hr', zero_le_mul_left, nonempty_closed_ball, zero_lt_bit0, zero_lt_one, inv_pos],
  simp only [nonempty_interval], },
  have := is_compact.exists_forall_ge comp none cts,
  simp at *,
  apply this,
end

lemma circle_integral_function_deriv_cont_on (R : ℝ) (hR: 0 < R)  (f : ℂ → E) (z w : ℂ)
  (hf : continuous_on f (sphere z R)  )  (hw : w ∈ ball z R):
  continuous_on (circle_integral_function_deriv R z f w) (Ι 0 (2*π)) :=
begin
 apply (circle_integral_function_deriv_cont_on_ICC R hR f z w hf hw).mono,
 rw [interval_oc_of_le (real.two_pi_pos.le), interval_of_le (real.two_pi_pos.le)],
 exact Ioc_subset_Icc_self,
end

/--Cauchy integral from of a function at `z` in a disk of radius `R`-/
def circle_integral_form (R : ℝ) (z : ℂ) (f : ℂ → E) : (ℂ → E) := λ w,
(1/(2 • π • I)) • (∮ z in C(z, R), (z - w)⁻¹ • f z)

lemma circle_intgral_form_eq_int (R : ℝ) (z : ℂ) (f : ℂ → E) :
circle_integral_form R z f =  λ w,
 ∫ (θ : ℝ) in 0..2 * π, (circle_integral_function R z f w) θ :=
begin
simp_rw [circle_integral_form,circle_integral_function, circle_integral],
ext,
simp,
end

lemma bound3_cts (R : ℝ)  (hR: 0 < R) (z a: ℂ) (b : ℝ) (f : ℂ → ℂ)
  (hf : continuous_on f (sphere z R)) :
  continuous_on (λ (r : ℝ),
  (complex.abs ( fbound3_rest R z b a)) * complex.abs (f(circle_map z R r))) [0, 2*π] :=
begin
  apply continuous_on.mul,
  apply continuous_const.continuous_on,
  apply continuous_on.comp,
   have cabs: continuous_on abs ⊤, by {apply continuous_abs.continuous_on,},
  apply cabs,
  apply continuous_on.comp,
  apply hf,
  apply (continuous_circle_map z R).continuous_on,
  all_goals {rw maps_to, intros x hx,},
  apply circle_map_mem_sphere,
  apply hR.le,
  simp,
end

lemma circle_integral_function_deriv_bound3 (R r : ℝ)  (hR: 0 < R) (hr : r < R) (hr' : 0 ≤  r)
  (z : ℂ) (f : ℂ → ℂ) (x : ℂ) (hx : x ∈ ball z r) (hf : continuous_on f (sphere z R)) :
  ∃ (boun : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ ball x ε ⊆ ball z R ∧
  (∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε,
  ∥circle_integral_function_deriv R z f y t∥ ≤  boun t) ∧ continuous_on boun [0, 2*π]:=
 begin
  have HBB:= ball_subset_ball hr.le,
  have h2R: 0 < 2*R, by {linarith,},
  have fbb := fbounded3 R r hR hr hr' z,
  have ball:=exists_ball_subset_ball hx,
  obtain ⟨ε', hε', H⟩:= ball,
  simp at fbb,
  obtain ⟨ a, b, hab⟩ := fbb,
  set bound : ℝ → ℝ := λ r, (complex.abs ( fbound3_rest R z b a)) *
  complex.abs (f(circle_map z R r)) ,
  use bound,
  use ε',
  simp only [gt_iff_lt] at hε',
  simp only [hε', true_and, mem_ball, norm_eq_abs],
  have h_ball : ball x ε' ⊆ ball z R,
  by {apply subset.trans H HBB, },
  simp only [h_ball, true_and],
  split,
  rw filter.eventually_iff_exists_mem,
  use ⊤,
  simp,
  intros y hy v hv,
  have hvv: v ∈ ball x ε', by {simp, apply hv},
  have hvz : v ∈ ball z r, by {apply H, apply hvv,},
  simp only [bound, fbound3, circle_integral_function_deriv, fbound3_rest, one_div, abs_of_real,
  abs_exp_of_real_mul_I, mem_ball, mul_one, algebra.id.smul_eq_mul, abs_I, nat.cast_bit0, real_smul,
  abs_mul, nsmul_eq_mul, abs_div, zero_lt_bit0, abs_inv, zero_lt_mul_left, nat.cast_one, abs_two,
  abs_pow,zero_lt_one] at *,
  have hyy : y ∈ [0,2*π ], by {apply Ioc_subset_Icc_self, apply hy,},
  have hab2:= hab.2 v y hvz.le hyy,
  have abp : 0 ≤ complex.abs (f(circle_map z R y)), by {apply abs_nonneg},
  have := mul_le_mul_of_nonneg_right hab2 abp,
  simp at *,
  simp_rw ←mul_assoc at *,
  apply this,
  apply bound3_cts R hR z a b f hf,
 end

 lemma circle_integral_function_has_deriv_at  (R : ℝ) (hR : 0 < R) (z : ℂ) (f : ℂ → ℂ) :
  ∀ t : ℝ, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball z R,
   has_deriv_at (λ y, (circle_integral_function R z f) y t)
  ((circle_integral_function_deriv R z f) y t) y :=
begin
  simp only [true_and, mem_ball, top_eq_univ, univ_mem, mem_univ, forall_true_left],
  intros y hy x hx,
  simp_rw [circle_integral_function, circle_integral_function_deriv],
  simp only [one_div, algebra.id.smul_eq_mul, nat.cast_bit0, real_smul, nsmul_eq_mul, nat.cast_one],
  simp_rw ← mul_assoc,
  apply has_deriv_at.mul_const,
  apply has_deriv_at.const_mul,
  have H : has_deriv_at (λ (y_1 : ℂ), (circle_map z R y - y_1)) (-1 ) x,
  by {apply has_deriv_at.const_sub, apply has_deriv_at_id,},
  have := circle_map_ne_on_ball R hR z x hx y,
  have hfin:= has_deriv_at.inv H this,
  simp only [one_div, neg_neg] at hfin,
  apply hfin,
end

lemma ae_circle_integral_function_has_deriv_at (R : ℝ) (z : ℂ) (hR : 0 < R) (f : ℂ → ℂ) :
  ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball z R,
  has_deriv_at (λ y, (circle_integral_function R z f) y t)
  ((circle_integral_function_deriv R z f) y t) y :=
begin
  rw filter.eventually_iff_exists_mem,
  use ⊤,
  simp only [true_and, top_eq_univ, univ_mem, mem_univ, forall_true_left],
  apply circle_integral_function_has_deriv_at,
  apply hR,
end

lemma circle_integral_function_ae_measurable  (R r: ℝ) (hR: 0 < R) (hr : r < R)
  (z x : ℂ) (hx : x ∈ ball z r ) (f : ℂ → ℂ) (hf : continuous_on f (sphere z R)) :
  ∀ᶠ y in 𝓝 x, ae_measurable (( λ w, (λ θ, (circle_integral_function R z f w θ))) y)
  (volume.restrict (Ι 0 (2 * π))):=
  begin
   have HBB:= ball_subset_ball hr.le,
  rw filter.eventually_iff_exists_mem,
  have BALL := exists_ball_subset_ball hx,
  obtain ⟨ε', He, HB⟩ := BALL,
  use (ball x ε'),
  have hm := metric.ball_mem_nhds x He,
  simp only [hm, true_and, mem_ball],
  intros y hy,
  have hmea : measurable_set (Ι 0 (2 * π)), by {exact measurable_set_interval_oc,},
  have := continuous_on.ae_measurable (circle_integral_function_cont_on R hR f z y hf _) hmea,
  apply this,
  apply HBB,
  apply HB,
  simp only [hy, mem_ball],
  end

lemma circle_integral_function_Interval_integrable (R r: ℝ) (hR: 0 < R) (hr : r < R)
(z x : ℂ) (hx : x ∈ ball z r ) (f : ℂ → ℂ) (hf : continuous_on f (sphere z R)) :
 interval_integrable ((λ w, (λ θ, (circle_integral_function R z f w θ))) x) volume 0  (2 * π) :=
begin
   have HBB:= ball_subset_ball hr.le,
  have cts := circle_integral_function_cont_on_ICC R hR f z x hf,
  have hxx: x ∈ ball z R, by {apply HBB, apply hx,},
  have ctss:= cts hxx,
  have := continuous_on.interval_integrable ctss,
  apply this,
  apply_instance,
end

lemma circle_integral_function_deriv_ae_measurable  (R r: ℝ) (hR: 0 < R) (hr : r < R)
  (z x : ℂ) (hx : x ∈ ball z r ) (f : ℂ → ℂ) (hf : continuous_on f (sphere z R)) :
   ae_measurable (( λ w, (λ θ, (circle_integral_function_deriv R z f w θ))) x)
  (volume.restrict (Ι 0 (2 * π))):=
  begin
  have HBB:= ball_subset_ball hr.le,
  have hmea : measurable_set (Ι 0 (2 * π)), by {exact measurable_set_interval_oc,},
  have := continuous_on.ae_measurable (circle_integral_function_deriv_cont_on R hR f z x hf _) hmea,
  apply this,
  apply HBB,
  apply hx,
  end

lemma circle_integral_differentiable_on (R r: ℝ) (hR: 0 < R) (hr : r < R) (hr' : 0 ≤  r) (z : ℂ)
  (f : ℂ → ℂ) (hf : continuous_on f (sphere z R)) :
  differentiable_on ℂ (circle_integral_form R z f) (ball z r) :=
begin
  rw circle_integral_form,
  simp_rw ←circle_integral_function_circle_int R z f,
  simp_rw circle_integral_function,
  rw differentiable_on,
  simp_rw differentiable_within_at,
  intros x hx,
  have h4R: 0 < (4⁻¹*R), by {apply mul_pos, rw inv_pos, linarith, apply hR,},
  set F : ℂ → ℝ → ℂ  := λ w, (λ θ, (circle_integral_function R z f w θ)),
  set F' : ℂ → ℝ → ℂ := circle_integral_function_deriv R z f,
  have hF_meas : ∀ᶠ y in 𝓝 x, ae_measurable (F y) (volume.restrict (Ι 0 (2 * π))) ,
  by {simp_rw F,  apply circle_integral_function_ae_measurable R r hR hr  z x hx f hf},
  have hF_int : interval_integrable (F x) volume 0  (2 * π),
  by {simp_rw F, apply  circle_integral_function_Interval_integrable  R r hR hr z x hx f hf},
  have  hF'_meas : ae_measurable (F' x) (volume.restrict (Ι 0 (2 * π))) ,
  by {simp_rw F',apply circle_integral_function_deriv_ae_measurable R r hR hr  z x hx f hf},
  have BOU := circle_integral_function_deriv_bound3 R r hR hr hr' z f x hx hf,
  obtain ⟨bound, ε, hε ,h_ball, h_boun, hcts⟩:= BOU,
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε , ∥F' y t∥ ≤  bound t,
  by {simp_rw F',
  apply h_boun,},
  have  bound_integrable : interval_integrable bound volume 0 (2 * π) ,
  by {apply continuous_on.interval_integrable, apply hcts,},
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι 0 (2 * π) → ∀ y ∈ ball x ε,
    has_deriv_at (λ y, F y t) (F' y t) y,
  by {simp_rw [F, F', circle_integral_function, circle_integral_function_deriv],
  have := ae_circle_integral_function_has_deriv_at R z hR f,
  simp_rw [circle_integral_function, circle_integral_function_deriv] at this,
  rw filter.eventually_iff_exists_mem at *,
  obtain ⟨ S , hS, HH⟩ := this,
  refine ⟨S , hS, _ ⟩,
  intros y hSy hy x hx,
  have hxz: x ∈ ball z R, by {apply h_ball, apply hx},
  apply HH y hSy hy x hxz,},
  have := interval_integral.has_deriv_at_integral_of_dominated_loc_of_deriv_le
    hε hF_meas hF_int hF'_meas h_bound bound_integrable h_diff,
  simp_rw [F, circle_integral_function,has_deriv_at, has_deriv_at_filter] at this,
  simp_rw has_fderiv_within_at,
  simp only [real_smul, nsmul_eq_mul, nat.cast_bit0, nat.cast_one, one_div, algebra.id.smul_eq_mul,
    integral_const_mul, mem_ball, zero_lt_mul_left, inv_pos, zero_lt_bit0, zero_lt_one,
    norm_eq_abs] at *,
  have h3:= this.2,
  let der := (interval_integral (F' x) 0 (2 * π) volume),
  let DER := continuous_linear_map.smul_right (1 : ℂ →L[ℂ] ℂ) der,
  use DER,
  simp_rw [DER, der],
  have this2:= (has_fderiv_at_filter.mono h3),
  apply this2,
  rw nhds_within,
  simp only [inf_le_left],
end

lemma circle_integral_function_sub  (R : ℝ) (f g : ℂ → ℂ) (z w : ℂ) : ∀ θ : ℝ,
   complex.abs (((circle_integral_function R z f w ) θ)-((circle_integral_function R z g w) θ)) =
   complex.abs (circle_integral_function R z (f -g) w θ) :=
begin
  intro θ,
  simp [circle_integral_function],
  ring_nf,
  simp,
end

lemma circle_integral_function_sub_bound  (R : ℝ) (hR: 0 < R)  (f : ℂ → ℂ) (z w : ℂ) (r : ℝ)
    (h:  ∀ (x : sphere z R), (complex.abs (f x) ≤ abs r)) : ∀ θ : ℝ,
    complex.abs (circle_integral_function R z f w θ) ≤
    complex.abs (circle_integral_function R z (λ x, r) w θ) :=
begin
  intro θ,
  simp [circle_integral_function, one_div, abs_of_real, abs_exp_of_real_mul_I, mul_one,
  algebra.id.smul_eq_mul, abs_I, nat.cast_bit0, real_smul, abs_mul, nsmul_eq_mul, abs_div, abs_inv,
  nat.cast_one, abs_two, ←mul_assoc],
  apply monotone_mul_left_of_nonneg,
  apply mul_nonneg,
  apply mul_nonneg,
  simp_rw inv_nonneg,
  apply mul_nonneg,
  linarith,
  apply _root_.abs_nonneg,
  apply _root_.abs_nonneg,
  simp_rw ←one_div,
  apply div_nonneg,
  linarith,
  apply complex.abs_nonneg,
  simp only [abs_of_real, set_coe.forall, subtype.coe_mk] at h,
  apply h,
  apply circle_map_mem_sphere z hR.le θ,
end

lemma circle_integral_function_int (R : ℝ) (hR: 0 < R) (F : ℂ → ℂ) (z : ℂ)
  (F_cts :  continuous_on (F ) (sphere z R))
  (w : ball z R): integrable (circle_integral_function R z F w) (volume.restrict (Ioc 0  (2*π))) :=
begin
  apply integrable_on.integrable,
  rw ← interval_integrable_iff_integrable_Ioc_of_le,
  apply continuous_on.interval_integrable,
  have hw := w.property,
  simp only [mem_ball, subtype.val_eq_coe] at hw,
  have := circle_integral_function_cont_on_ICC R hR F z w F_cts,
  simp only [mem_ball] at this,
  have hc:= this hw,
  apply hc,
  simp only [zero_le_mul_left, zero_lt_bit0, zero_lt_one],
  linarith [real.pi_pos],
end

lemma circle_integral_function_int_abs (R : ℝ) (hR: 0 < R) (F : ℂ → ℂ) (z : ℂ)
  (F_cts :  continuous_on (F ) (sphere z R))
  (w : ball z R) :
  integrable (complex.abs ∘ (circle_integral_function R z F w)) (volume.restrict (Ioc 0  (2*π))) :=
begin
  apply integrable_on.integrable,
  rw ← interval_integrable_iff_integrable_Ioc_of_le,
  apply continuous_on.interval_integrable,
  apply continuous_on.comp,
  have cabs: continuous_on abs ⊤, by {apply continuous_abs.continuous_on,},
  apply cabs,
  have hw := w.property,
  simp only [mem_ball, subtype.val_eq_coe] at hw,
  have := circle_integral_function_cont_on_ICC R hR F z w F_cts,
  simp only [mem_ball] at this,
  have hc:= this hw,
  apply hc,
  simp only [preimage_univ, top_eq_univ, subset_univ, maps_to_univ],
  linarith [real.pi_pos],
end

lemma abs_aux (x : ℂ) (r : ℝ) (h : ∃ (b : ℂ), complex.abs (x-b)+ complex.abs(b) ≤  r) :
  complex.abs(x) ≤  r :=
begin
  obtain ⟨b, hb⟩ := h,
  have hs: (x -b) + b = x , by {simp only [sub_add_cancel],},
  rw ← hs,
  apply le_trans _ hb,
  exact (x - b).abs_add b,
end

lemma circle_integral_function_of_unifom_limit (R : ℝ) (hR: 0 < R) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
  (z : ℂ) (hlim : tendsto_uniformly_on F f filter.at_top (sphere z R)) (w : ball z R) :
  ∀ (a : ℝ), tendsto (λ n, ((circle_integral_function R z (F n) w)) a)
  at_top (𝓝 (((circle_integral_function R z f w)) a)) :=
begin
  rw metric.tendsto_uniformly_on_iff at hlim,
  simp only [metric.tendsto_nhds, dist_comm, circle_integral_function],
  simp only [one_div, algebra.id.smul_eq_mul, gt_iff_lt, mem_closed_ball, nat.cast_bit0, real_smul,
  ge_iff_le, nsmul_eq_mul, nat.cast_one, eventually_at_top] at *,
  intros y ε hε,
  set r : ℂ :=  (2 * (↑π * I))⁻¹ * circle_map 0 R y * I * ((circle_map z R y - ↑w)⁻¹),
  have hr: 0 < ∥ r ∥,
  by {simp_rw r,
  simp,
  apply mul_pos,
  apply mul_pos,
  rw inv_eq_one_div,
  rw one_div_pos,
  apply mul_pos,
  linarith,
  simp only [_root_.abs_pos, ne.def],
  apply real.pi_ne_zero,
  rw _root_.abs_pos,
  linarith,
  rw inv_pos,
  rw abs_pos,
  apply circle_map_ne_on_ball R hR z w w.2,},
  have hr':  ∥ r ∥ ≠ 0, by {linarith,},
  let e:= (∥ r ∥)⁻¹ * (ε/2),
  have he: 0 < e, by {simp_rw e, apply mul_pos,
  apply inv_pos.2 hr, apply div_pos, apply hε, linarith,},
  have h_lim2:= hlim e he,
  obtain ⟨a, ha⟩ := h_lim2,
  use a,
  intros b hb,
  simp,
  simp_rw dist_eq_norm at *,
  simp_rw ← mul_sub,
  have hg: ∥(2 * (↑π * I))⁻¹ * (circle_map 0 R y * I *
  ((circle_map z R y - ↑w)⁻¹ * (f (circle_map z R y) - F b (circle_map z R y))))∥ =
  ∥(2 * (↑π * I))⁻¹ * circle_map 0 R y * I * ((circle_map z R y - ↑w)⁻¹) ∥ *
  ∥ (f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I)))∥,
  by {simp only [abs_of_real, abs_exp_of_real_mul_I, mul_one, abs_I,
  abs_mul, abs_div, abs_inv, abs_two, norm_eq_abs], ring_nf,},
  rw hg,
  simp_rw ← r,
  have haa := ha b hb,
  have hab := haa (z + ↑R * exp (↑y * I)) (circle_map_mem_sphere z hR.le y),
  simp only [abs_of_real, abs_exp_of_real_mul_I, add_sub_cancel',
  mul_one, abs_mul, norm_eq_abs] at hab,
  have triv : |R| ≤ R, by {rw abs_of_pos hR,},
  have haav : ∥ r ∥ * ∥f (z + ↑R * exp (↑y * I)) - F b (z + ↑R * exp (↑y * I))∥ < ∥ r ∥ * e,
  by {apply mul_lt_mul_of_pos_left hab hr,},
  simp_rw e at haav,
  apply lt_trans haav,
  rw div_eq_inv_mul,
  simp_rw ← mul_assoc,
  simp_rw [mul_inv_cancel hr'],
  simp only [one_mul],
  rw mul_lt_iff_lt_one_left,
  rw inv_eq_one_div,
  linarith,
  apply hε,
end

lemma sum_ite_eq_extract {α : Type*} [decidable_eq α] (s : finset α) (b : s) (f : s → ℂ) :
  ∑ n, f n = f b + ∑ n, ite (n = b) 0 (f n) :=
begin
  simp_rw ← tsum_fintype,
  apply tsum_ite_eq_extract,
  simp only at *,
  apply (has_sum_fintype f).summable,
end

def circle_int_bound2 (R : ℝ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (w : ball z R) (a : ℕ) : ℝ → ℝ :=
  λ θ, (∑ (i : finset.range (a+1) ),complex.abs ((circle_integral_function R z (F i) w) θ))  +
  complex.abs ((circle_integral_function R z (λ x, 1) w) θ)  +
  complex.abs ((circle_integral_function R z f w) θ)

lemma circle_int_bound2_int (R : ℝ) (hR: 0 < R) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (w : ball z R) (a : ℕ)
  (F_cts : ∀ n, continuous_on (F n) (sphere z R)) (hf : continuous_on f (sphere z R)) :
  integrable (circle_int_bound2 R F f z w a) (volume.restrict (Ioc 0  (2*π))) :=
begin
 rw circle_int_bound2,
  apply integrable.add,
  apply  integrable.add,
  apply integrable_finset_sum,
  simp only [finset.mem_attach, forall_true_left, finset.univ_eq_attach],
  intro i,
  apply circle_integral_function_int_abs R hR (F i) z (F_cts i),
  apply circle_integral_function_int_abs R hR _ z continuous_const.continuous_on,
  apply circle_integral_function_int_abs R hR f z hf,
end

lemma circle_int_uniform_lim_eq_lim_of_int (R : ℝ) (hR: 0 < R) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ)
  (w : ball z R) (F_cts : ∀ n, continuous_on (F n) (sphere z R))
  (hlim : tendsto_uniformly_on F f filter.at_top (sphere z R) )  :
  tendsto (λn, ∫ (θ : ℝ) in 0..2 * π, (circle_integral_function R z (F n) w) θ)
  at_top (𝓝 $  ∫ (θ : ℝ) in 0..2 * π, (circle_integral_function R z f w) θ) :=
begin
have f_cont: continuous_on f (sphere z R) ,
  by {apply tendsto_uniformly_on.continuous_on hlim, simp only [ge_iff_le, eventually_at_top],
  use 1,
  intros b hb, apply F_cts,},
  have F_measurable : ∀ n,
  ae_measurable (circle_integral_function R z (F n) w) (volume.restrict (Ioc 0  (2*π))),
  by {intro n,
  have:= circle_integral_function_int R hR  (F n) z (F_cts n) w,
  apply this.ae_measurable, },
  have h_lim'' : ∀ (a : ℝ), tendsto (λ n, ((circle_integral_function R z (F n) w)) a)
  at_top (𝓝 (((circle_integral_function R  z f w)) a)),
  by {apply circle_integral_function_of_unifom_limit R hR F f z hlim},
  have h_lim' : ∀ᵐ a ∂(volume.restrict (Ioc 0  (2*π))),
  tendsto (λ n, ((circle_integral_function R z (F n)  w)) a)
  at_top (𝓝 (((circle_integral_function R z f w)) a)),
  by {simp only [h_lim'', eventually_true],},
  rw metric.tendsto_uniformly_on_iff at hlim,
  simp only [gt_iff_lt, ge_iff_le, eventually_at_top] at hlim,
  have hlimb:= hlim 1 (zero_lt_one),
  obtain ⟨ a, ha⟩ :=hlimb,
  set bound : ℝ → ℝ :=λ θ, (∑ (i : finset.range (a+1) ),
  complex.abs ((circle_integral_function R z (F i) w) θ))
  + complex.abs ((circle_integral_function R z (λ x, 1) w) θ)  +
  complex.abs ((circle_integral_function R z f  w) θ),
  have h_bound : ∀ n, ∀ᵐ a ∂(volume.restrict (Ioc 0  (2*π))),
  ∥(circle_integral_function R z (F n) w) a∥ ≤ bound a,
  by {intro n,
  rw  ae_restrict_iff' at *,
  rw eventually_iff_exists_mem,
  use ⊤,
  simp only [true_and, and_imp, mem_Ioc,
  top_eq_univ, univ_mem, mem_univ, forall_true_left, norm_eq_abs],
  intros y hyl hyu,
  by_cases (n ≤ a),
  simp_rw bound,
  have:= sum_ite_eq_extract (finset.range (a+1)) ⟨n, by {simp [h],linarith}⟩
  (λ (i : finset.range (a+1) ),complex.abs ((circle_integral_function R z (F i) w) y)),
  simp only [and_imp, mem_Ioc, add_zero,mem_closed_ball,int.coe_nat_add,ge_iff_le,int.coe_nat_one,
  zero_add,finset.univ_eq_attach,finset.mem_range,subtype.coe_mk,zero_lt_one,neg_zero] at *,
  norm_cast at *,
  simp_rw this,
  rw add_assoc,
  rw add_assoc,
  simp only [le_add_iff_nonneg_right],
  apply add_nonneg,
  apply finset.sum_nonneg,
  intros i hi,
  simp only,
  rw ← dite_eq_ite,
  by_cases H : i = ⟨n, by {simp only [finset.mem_range],linarith}⟩,
  simp only [H, dite_eq_ite, if_true, eq_self_iff_true],
  simp only [dif_neg H],
  apply abs_nonneg,
  simp only [add_nonneg, abs_nonneg],
  simp only [not_le] at h,
  apply abs_aux ((circle_integral_function R z (F n) w) y) (bound y),
  use circle_integral_function R z f ↑w y,
  rw circle_integral_function_sub,
  simp_rw bound,
  simp only [add_le_add_iff_right, finset.univ_eq_attach],
  have := circle_integral_function_sub_bound R hR ((F n) - f) z w 1,
  have haan:= ha n h.le,
  simp only [of_real_one, abs_one, pi.sub_apply] at this,
  simp_rw dist_eq_norm at *,
  simp only [norm_eq_abs] at haan,
  have haf:  ∀ (x : sphere z R), abs (F n x - f x) ≤  1,
  by {intro x, rw abs_sub_comm, apply (haan x.1 x.property).le,},
  have h5:= this haf,
  have h6:= h5 y,
  refine le_add_of_nonneg_of_le _ h6,
  apply finset.sum_nonneg,
  intros i hi,
  apply abs_nonneg,
  all_goals {simp only [measurable_set_Ioc]},},
  have bound_integrable : integrable bound (volume.restrict (Ioc 0  (2*π))),
  by {have := circle_int_bound2_int R hR F f z w a F_cts f_cont,
  simp_rw bound,
  rw circle_int_bound2 at this,
  apply this,},
  have := tendsto_integral_of_dominated_convergence bound F_measurable bound_integrable
  h_bound h_lim',
  have pi: 0 ≤ 2*π , by {apply real.two_pi_pos.le},
  simp_rw  integral_of_le pi,
  apply this,
end

lemma abs_norm (x : ℂ) : norm( abs x)= abs x :=
begin
  rw real.norm_eq_abs,
  apply abs_abs,
end

lemma auxlefind {a b c r s t : ℝ} (ha :  a < r ) (hb : b < s) (hc : c < t) :
a + b + c< r + s + t :=
begin
  linarith,
end

lemma auxff (a b r : ℝ) (hr : 0  < r) :   a < b*r →  r⁻¹ *a <  b :=
begin
  exact (inv_mul_lt_iff' hr).mpr,
end

lemma auxfals (a : ℂ) : abs a < 0 → false :=
begin
  have := abs_nonneg a,
  intro ha,
  linarith,
end

lemma aux2 (a b c d e f r: ℂ) (ε : ℝ) (hε: 0 < ε) (h1: abs (a- b) < 8⁻¹*abs(r)*ε)
(h2 :abs (c- d) < 8⁻¹*abs(r)*ε ) (h3 :(abs r)⁻¹ * abs ((b- d)- (e-f)) < (2/3)*ε) :
(abs r)⁻¹ * abs ((a-b) - (c-d) + (b-d) - (e-f) ) < ε :=
begin
  have h4: abs (((a-b) - (c-d)) + (b-d) - (e-f) ) ≤ abs ((a-b) - (c-d)) + abs ((b-d) - (e-f)),
  by {set x : ℂ := (a-b) - (c-d),
  set y: ℂ :=((b-d) - (e-f)),
  have := abs_add x y,
  convert this,
  simp_rw y,
  ring_nf,},
  have h5: abs (a - b - (c - d)) ≤ abs (a -b)+ abs (c-d),
  by {have:= complex.abs_sub_le (a-b) 0 (c-d),
  simp only [zero_sub, sub_zero, neg_sub] at this,
  have hcd :abs (c-d)= abs (d-c), by {apply complex.abs_sub_comm,},
  rw hcd,
  apply this,},
  have h6 :(abs r)⁻¹ * abs (((a-b) - (c-d)) + (b-d) - (e-f) ) ≤
  (abs r)⁻¹ *abs (a -b)+ (abs r)⁻¹* abs (c-d)+  (abs r)⁻¹ * abs ((b-d) - (e-f)),
  by {ring_nf, apply mul_mono_nonneg, rw inv_nonneg, apply abs_nonneg,
  apply le_trans h4, simp_rw ← add_assoc, simp only [h5, add_le_add_iff_right],},
  have hr : 0 < abs r,
  by {by_contradiction h,
  simp only [abs_pos, not_not] at h,
  rw h at h1,
  simp only [zero_mul, abs_zero, mul_zero] at h1,
  apply auxfals (a-b) h1,},
  have h11: (abs(r))⁻¹* abs (a-b) < (8⁻¹*ε ),
  by {have:= auxff (abs (a-b)) (8⁻¹*ε) (abs r) hr,
  apply this, have e1: 8⁻¹* (abs r) *ε = 8⁻¹* ε* (abs r),
  by {ring_nf,},
  rw ← e1,
  apply h1,},
  have h22: (abs(r))⁻¹* abs (c-d) < (8⁻¹*ε), by {
  have:= auxff (abs (c-d)) (8⁻¹*ε) (abs r) hr,
  apply this,
  have e1: 8⁻¹* (abs r) *ε = 8⁻¹* ε* (abs r),
  by {ring_nf,},
  rw ← e1,
  apply h2,},
  have h7 :=  auxlefind h11 h22 h3,
  have h8 := lt_of_le_of_lt h6  h7,
  apply lt_trans h8,
  ring_exp,
  linarith,
end

lemma aux3 (a b c d r: ℂ) (ε : ℝ) (hε : 0 < ε )
 (h : ∃ (x y : ℂ), abs ( a- y) < 8⁻¹*abs(r)*ε ∧ abs (b -x) < 8⁻¹*abs(r)*ε ∧
 (abs r)⁻¹ *abs ((y -x)- (c -d) ) < 8⁻¹*ε) :
 (abs r)⁻¹ *abs ((a-b )- (c-d)) < (2/3)*ε :=
begin
  obtain ⟨x, y , h1,h2, h3⟩:= h,
  have hr : 0 < abs r,
  by {by_contradiction h,
  simp only [abs_pos, not_not] at h,
  rw h at h1,
  simp only [zero_mul, abs_zero, mul_zero] at h1,
  apply auxfals (a-y) h1, },
  have h33: (abs r)⁻¹ * abs ((c -d) - (y -x)) < 8⁻¹*ε,
  by {have : abs ((c -d) - (y -x)) = abs ((y -x)- (c -d) ),
  by  { rw abs_sub_comm,},
  rw this,
  apply h3,},
  have h5 : abs ((a-b )- (c-d)) = abs (( (a-y) -(b-x) )- ((c-d)-(y-x))) ,
  by {ring_nf,},
  rw h5,
  have h6: (abs r)⁻¹ *abs (( (a-y) -(b-x) )- ((c-d)-(y-x))) ≤ (abs r)⁻¹ * abs (a-y) +
  (abs r)⁻¹ * abs(b-x)+ (abs r)⁻¹ * abs ((c-d) -(y-x)),
  by {ring_nf,
  apply mul_mono_nonneg,
  rw inv_nonneg,
  apply abs_nonneg,
  have h4: abs (((a-y) - (b-x)) + -((c-d) - (y-x)) ) ≤ abs ((a-y) - (b-x)) + abs ((c-d) - (y-x)),
  by {set X : ℂ := (a-y) - (b-x),
  set Y : ℂ :=-((c-d) - (y-x)),
  have := complex.abs_add X Y,
  have ho : abs (c - d - (y - x)) = abs Y, by {simp_rw Y, rw abs_neg,},
  rw ho,
  convert this,},
  have h44 : abs ((a-y) - (b-x)) ≤ abs (a-y) + abs (b-x),
  by {have := complex.abs_sub_le (a-y) 0 (b-x),
  simp only [zero_sub, sub_zero, neg_sub] at this,
  have hcd : abs (b-x)= abs (x-b), by {apply complex.abs_sub_comm,},
  rw hcd,
  apply this,},
  apply le_trans h4,
  simp_rw ← add_assoc,
  simp only [h44, add_le_add_iff_right],},
  have h11 : (abs r)⁻¹ * abs ( a- y) < 8⁻¹*ε, by {
  have:= auxff (abs (a-y)) (8⁻¹*ε) (abs r) hr,
  apply this,
  have e1 : 8⁻¹* (abs r) *ε = 8⁻¹* ε* (abs r),
  by {ring_nf,},
  rw ← e1,
  apply h1,},
  have h22: (abs r)⁻¹ * abs ( b- x) < 8⁻¹*ε, by {
  have:= auxff (abs (b-x)) (8⁻¹*ε) (abs r) hr,
  apply this,
  have e1: 8⁻¹* (abs r) *ε = 8⁻¹* ε* (abs r),
  by {ring_nf,},
  rw ← e1,
  apply h2,},
  have h7 := auxlefind h11 h22 h33,
  have h8 := lt_of_le_of_lt h6  h7,
  apply lt_trans h8,
  field_simp,
  linarith,
end

lemma auxfin (a b c d e f r: ℂ) (ε : ℝ) (hε: 0 < ε) (h1: abs (a- b) < 8⁻¹*abs(r)*ε)
  (h2 :abs (c- d) < 8⁻¹*abs(r)*ε )
  (h : ∃ (x y : ℂ), abs ( b- y) < 8⁻¹*abs(r)*ε ∧ abs (d-x) < 8⁻¹*abs(r)*ε ∧
  (abs r)⁻¹ *abs ((y -x)- (e -f) ) < 8⁻¹*ε) :
  (abs r)⁻¹ * abs ((a-b) - (c-d) + (b-d) - (e-f) ) < ε :=
begin
  apply aux2 ,
  apply hε,
  apply h1,
  apply h2,
  apply aux3,
  apply hε,
  obtain ⟨x,y,hxy⟩:= h,
  use x,
  use y,
  apply hxy,
end

lemma unif_lim_of_diff_is_cts_sphere (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (R : ℝ)
  (hdiff : ∀ (n : ℕ), differentiable_on ℂ (F n) (sphere z R))
  (hlim : tendsto_uniformly_on F f filter.at_top (sphere z R)) :
  continuous_on f (sphere z R) :=
begin
  have F_cts : ∀ n, continuous_on (F n) (sphere z R),
  by {intro n, apply (hdiff n).continuous_on,},
  apply tendsto_uniformly_on.continuous_on hlim,
  simp only [ge_iff_le, eventually_at_top],
  use 1,
  intros b hb,
  apply F_cts,
end

lemma unif_lim_of_diff_is_cts (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (R : ℝ)
  (hdiff : ∀ (n : ℕ), differentiable_on ℂ (F n) (closed_ball z R))
  (hlim : tendsto_uniformly_on F f filter.at_top (closed_ball z R)) :
  continuous_on f (closed_ball z R) :=
begin
  have F_cts : ∀ n, continuous_on (F n) (closed_ball z R),
  by {intro n, apply (hdiff n).continuous_on,},
  apply tendsto_uniformly_on.continuous_on hlim,
  simp only [ge_iff_le, eventually_at_top],
  use 1,
  intros b hb,
  apply F_cts,
end

lemma circle_integral_unif_of_diff_has_fderiv (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (R r: ℝ)
  (hr : r < R) (hlim : tendsto_uniformly_on F f filter.at_top (closed_ball z R))
  (F_alt : ∀ (n : ℕ) (c : ball z r ), F n c = (circle_integral_form R z (F n)) c)
  (x : ℂ)
  (hx : x ∈  ball z r)
  (keyb : ∀ (w : ↥(ball z R)),
  tendsto (λ (n : ℕ), ∫ (θ : ℝ) in 0..2 * π, circle_integral_function R z (F n) ↑w θ) at_top
  (𝓝 (∫ (θ : ℝ) in 0..2 * π, circle_integral_function R z f ↑w θ))  )
  (D : ℂ →L[ℂ] ℂ )
  (hD : has_fderiv_within_at (circle_integral_form R z f) D (ball z r) x ) :
  ∃ (f' : ℂ →L[ℂ] ℂ), has_fderiv_within_at f f' (ball z r) x :=
begin
  have hxx : x ∈ ball z R, by {apply ball_subset_ball hr.le, apply hx},
  use D,
  simp_rw [has_fderiv_within_at_iff_tendsto, metric.tendsto_nhds, tendsto_uniformly_on_iff,
  dist_eq_norm]  at *,
  intros ε hε,
  have h8 : 0 < 8⁻¹*ε,
  by {simp only [zero_lt_bit0, zero_lt_mul_left, zero_lt_one, inv_pos], apply hε,},
  have hDε := hD (8⁻¹*ε) h8,
  clear hD,
  simp only [mem_ball, gt_iff_lt, mem_closed_ball, norm_mul, ge_iff_le,
  nonempty_of_inhabited, sub_zero, zero_lt_bit0, zero_lt_mul_left, continuous_linear_map.map_sub,
  set_coe.forall, subtype.coe_mk, eventually_at_top, zero_lt_one, inv_pos, norm_eq_abs,
  norm_inv] at *,
  rw filter.eventually_iff_exists_mem at *,
  obtain ⟨S1, hS1, HS1⟩:= hDε,
  let U:= S1 ⊓ ball z r,
  use U,
  have hU: U ∈ 𝓝[ball z r] x ,
  by {simp only [U, metric.mem_nhds_within_iff, exists_prop, mem_ball, and_true, gt_iff_lt,
  inf_eq_inter, inter_subset_right, subset_inter_iff] at *, exact hS1,},
  simp only [hU, true_and],
  clear hU hS1,
  intros y hy,
  simp_rw U at hy,
  let t := abs (y -x),
  by_cases ht: t ≠ 0,
  simp only [mem_ball, mem_inter_eq, inf_eq_inter] at hy,
  simp_rw abs_norm,
  have hyz: y ∈ ball z R, by {apply ball_subset_ball hr.le, exact (mem_ball.2 hy.2),},
  have keyy:= keyb y hyz,
  have keyy2:= keyb x hxx,
  have h8': 0 < 8⁻¹*t*ε, by {apply mul_pos, apply mul_pos,
  simp only [zero_lt_bit0, zero_lt_one, inv_pos],
  rw abs_pos,
  simp only [abs_eq_zero, ne.def] at ht,
  apply ht,
  apply hε,},
  have key2:= keyy2 (8⁻¹*t*ε) h8',
  have hlim2:= hlim (8⁻¹*t*ε) h8',
  clear hlim,
  obtain ⟨a'', ha''⟩ := keyy (8⁻¹*t*ε) h8',
  obtain ⟨a, ha⟩ := hlim2,
  obtain ⟨a', ha'⟩ := key2,
  set A' : ℕ := max a a',
  simp only [mem_ball, abs_eq_zero, ne.def, subtype.coe_mk] at *,
  set A : ℕ := max A' a'',
  have haA: a ≤ A, by {simp only [le_refl, true_or, le_max_iff],},
  have ha'A: a' ≤ A, by {simp only [le_refl, true_or, or_true, le_max_iff],},
  have ha''A : a'' ≤ A, by {simp only [le_refl, or_true, le_max_iff],},
  have HH: ∀ (y : ℂ), f y - f x - (D y - D x) =
  (f y - F A y) - ((f x)- (F A x)) + ((F A y)- (F A x))  - (D y - D x),
  by {intro y,simp only [sub_left_inj], ring_nf,},
  simp_rw HH,
  apply' auxfin _ _ _ _ _ _ _ _ hε (ha A haA y hyz.le) (ha A haA x (mem_ball.1 hxx).le),
  clear keyb keyy keyy2 HH hε h8 h8',
  refine ⟨(circle_integral_form R  z f x), (circle_integral_form R z f y),_⟩,
  simp_rw circle_intgral_form_eq_int,
  have hyy := mem_ball.2 hy.2,
  have hxz := mem_ball.2 hx,
  split,
  have:= F_alt A ⟨y,hyy⟩,
  simp only [subtype.coe_mk] at this,
  rw this,
  simp_rw circle_intgral_form_eq_int,
  apply ha'' A ha''A,
  split,
  have:= F_alt A ⟨x,hxz⟩,
  simp only [subtype.coe_mk] at this,
  rw this,
  simp_rw circle_intgral_form_eq_int,
  apply ha' A ha'A,
  simp_rw abs_norm at HS1,
  simp_rw circle_intgral_form_eq_int at HS1,
  apply HS1,
  apply hy.1,
  simp only [abs_eq_zero, not_not] at ht,
  rw ht,
  simp only [norm_zero, zero_mul, abs_zero, inv_zero],
  apply hε,
end

lemma uniform_of_diff_circle_int_is_diff (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) (R r: ℝ)
  (hR: 0 < R) (hr : r < R)
  (hr' : 0 ≤ r) (hdiff : ∀ (n : ℕ), differentiable_on ℂ (F n) (closed_ball z R))
  (hlim : tendsto_uniformly_on F f filter.at_top (closed_ball z R)) :
  differentiable_on ℂ f (ball z r) :=
begin
  have F_alt : ∀ (n : ℕ) (c : ball z r), F n c = (circle_integral_form R z (F n)) c,
  by {intros n c,
  have hc : c.1 ∈ ball z R, by { apply ball_subset_ball hr.le, apply c.property,},
  have ht := has_cauchy_integral_form hc (hdiff n),
  simp only [one_div, mem_ball, algebra.id.smul_eq_mul,
  nat.cast_bit0, real_smul, nsmul_eq_mul, nat.cast_one, subtype.val_eq_coe] at *,
  rw ht,
  simp only [circle_integral_form, circle_integral_function,  one_div, algebra.id.smul_eq_mul,
  nat.cast_bit0, real_smul,integral_const_mul, nsmul_eq_mul, nat.cast_one],},
  have F_cts : ∀ n, continuous_on (F n) (sphere z R),
  by {intro n, have:= (hdiff n).continuous_on, apply this.mono sphere_subset_closed_ball, },
  rw differentiable_on,
  intros x hx,
  have keyb :=λ ww, circle_int_uniform_lim_eq_lim_of_int R hR F f z ww F_cts
  (hlim.mono sphere_subset_closed_ball),
  rw differentiable_within_at,
  have hf := unif_lim_of_diff_is_cts F f z R  hdiff hlim,
  have HF :=circle_integral_differentiable_on R r hR hr hr' z f (hf.mono sphere_subset_closed_ball),
  clear hf F_cts hdiff,
  rw differentiable_on at HF,
  have HF2 := HF x,
  clear HF,
  simp only [hx, forall_true_left, differentiable_within_at] at HF2,
  obtain ⟨D, hD⟩:= HF2,
  apply circle_integral_unif_of_diff_has_fderiv F f z R r hr hlim F_alt x hx keyb D hD,
end

end complex
