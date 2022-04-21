import .Eisenstein_series_index_lemmas


universes u v w

open complex

open_locale big_operators nnreal classical filter

local notation `ℍ` := upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space, upper_half_plane_is_open⟩: open_subs)
noncomputable theory


/-! ### Eisenstein series -/

namespace Eisenstein_series

/-- The function on `ℤ × ℤ` whose sum defines an Eisenstein series.-/

def Eise (k: ℤ) (z : ℍ) : ℤ × ℤ →  ℂ:=
λ x, 1/(x.1*z+x.2)^k

/-
def Eisen (k : ℤ) (x : ℤ × ℤ) : C(ℍ, ℂ) :=
⟨λ z, 1/(x.1*z+x.2)^k, by {simp,  sorry}⟩
-/

instance : topological_space C(ℍ, ℂ) :=infer_instance



def Eise' (k: ℤ) (z : ℂ) : ℤ × ℤ →  ℂ:=
λ x, 1/(x.1*z+x.2)^k

def real_Eise (k: ℤ) (z : ℍ) : ℤ × ℤ →  ℝ:=
λ x, complex.abs(1/(x.1*z+x.2)^k)


def Eise_deriv (k: ℤ) (z : ℂ) : ℤ × ℤ →  ℂ:=
λ x, (-k*x.1)/(x.1*z+x.2)^(k+1)


/--The Eisenstein series of weight `k : ℤ` -/
def Eisenstein_series_of_weight_ (k: ℤ) : ℍ → ℂ:=
 λ z, ∑' (x : ℤ × ℤ), (Eise k z x)

def real_Eisenstein_series_of_weight_ (k: ℤ) : ℍ → ℝ:=
 λ z, ∑' (x : ℤ × ℤ), (real_Eise k z x)

def Eisenstein_deriv_weight (k: ℤ) : ℍ → ℂ:=
 λ z, ∑' (x : ℤ × ℤ), (Eise_deriv k z x)


/-
lemma summable2 (k : ℤ) (h: 3 ≤ k) : summable (Eisen k):=
begin
  sorry,
end


def Eisenstein_series_of_weight_' (k: ℤ) : C(ℍ, ℂ):=
 ∑' (x : ℤ × ℤ), Eisen k x
-/

lemma Eise_is_nonneg (k: ℤ) (z : ℍ) (y : ℤ × ℤ): 0 ≤ abs (Eise k z y):=
begin
 apply complex.abs_nonneg,
end

lemma calc_lem (k: ℤ) (a b c d i1 i2: ℂ) (z : ℍ) (h: c*z+d ≠ 0) :
((i1* ((a*z+b)/(c*z+d))+i2)^k)⁻¹=(c*z+d)^k* (((i1 * a + i2 * c) * z + (i1 * b + i2 * d))^k)⁻¹:=
begin
  have h1: i1*((a*z+b)/(c*z+d))+i2=(i1*(a*z+b)/(c*z+d)+i2), by {ring  }, rw h1,
  have h2:  (i1*(a*z+b)/(c*z+d)+i2)=((i1*(a*z+b))/(c*z+d)+i2), by {ring}, rw h2,
  have h3:=div_add' (i1*(a*z+b)) i2 (c*z+d) h, rw h3, simp [inv_pow], rw div_eq_inv_mul,
  have h4 : (((c * ↑z + d) ^ k)⁻¹ * (i1 * (a * ↑z + b) + i2 * (c * ↑z + d)) ^ k)⁻¹ =
  (c * ↑z + d) ^ k * ((i1 * (a * ↑z + b) + i2 * (c * ↑z + d)) ^ k)⁻¹,
  by {rw ← div_eq_inv_mul, rw inv_div, rw div_eq_inv_mul, ring,},
  rw h4,
  have h5: (c*z+d)^k ≠ 0,
  by {apply zpow_ne_zero _ h,  },
  apply congr_arg (λ (b : ℂ), (c*z+d)^k * b⁻¹),
  ring_nf,
end

lemma coe_chain (A: SL2Z) (i j : fin (2)):
  (A.1 i j : ℂ)= ((A.1 : (matrix (fin 2) (fin 2) ℝ) ) i j : ℂ):=
begin
  simp,
  rw ← coe_coe,
  fin_cases i;
  fin_cases j,
  simp only [coe_coe],
  work_on_goal 0 { cases A, dsimp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { dsimp at *, simp only [int_cast_re] at *, refl }, dsimp at *,
  simp only [int_cast_im] at *},
  work_on_goal 0 { cases A, dsimp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { dsimp at *, simp only [int_cast_re] at *, refl }, dsimp at *,
  simp only [int_cast_im] at *},
  work_on_goal 0 { cases A, dsimp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { dsimp at *, simp only [int_cast_re] at *, refl }, dsimp at *,
  simp only [int_cast_im] at *},
  cases A, dsimp at *, tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { dsimp at *,simp only [int_cast_re] at *, refl }, dsimp at *,
  simp only [int_cast_im] at *,
end


/- How the Eise function changes under the Moebius action-/
lemma Eise_moeb (k: ℤ) (z : ℍ) (A : SL2Z) (i : ℤ × ℤ ) :
  Eise k ( (A : matrix.GL_pos (fin 2) ℝ) • z) i =
  ((A.1 1 0*z+A.1 1 1)^k)*(Eise k z (Ind_equiv A i ) ) :=
begin
  rw Eise,
  rw Eise,
  simp [coe_fn_coe_base'],
  dsimp,
  rw calc_lem,
  have := upper_half_plane.denom_ne_zero A z,
  rw upper_half_plane.denom at this,
  simp at this,
  apply this,
end

lemma Eisenstein_is_wmodular (Γ : subgroup SL2Z) (k: ℤ)  :
 (Eisenstein_series_of_weight_ k) ∈ (modular_forms.weakly_modular_submodule k Γ) :=
begin
rw modular_forms.wmodular_mem',
rw Eisenstein_series_of_weight_,
simp only [set.mem_set_of_eq],
intros A z,
have h1:= Eise_moeb k z A,
have h2:=tsum_congr h1,
convert h2,
simp only [subtype.val_eq_coe],
have h3:=equiv.tsum_eq (Ind_equiv A) (Eise k z),
rw tsum_mul_left,
rw h3,
refl,
end

lemma Eise_on_square_is_bounded ( k : ℕ) (z : ℍ) (n : ℕ) (x: ℤ × ℤ) (h: x ∈ Square n) (hn: 1 ≤ n):
  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* n^k))⁻¹ :=
begin
  by_cases C1: complex.abs (x.1: ℂ)=n,
  rw inv_le_inv,
  have h0: (x.1:ℂ) ≠ 0,
  by {norm_cast,
  intro hx,
  rw hx at C1,
  simp only [int.cast_zero, complex.abs_zero] at C1,
  norm_cast at C1,
  rw ← C1 at hn,
  simp only [nat.one_ne_zero, le_zero_iff] at hn,
  exact hn,},
  have h1:(↑(x.fst) * ↑z + ↑(x.snd)) ^ k =  (↑(x.fst))^k* ((z: ℂ)+(x.2: ℂ)/(↑(x.fst)))^k,
  by { rw ← mul_pow,
  rw div_eq_mul_inv,
  have: (x.fst: ℂ) * ((z: ℂ)  + (x.snd: ℂ) * ((x.fst: ℂ))⁻¹)=(x.fst: ℂ) * (z: ℂ) + (x.snd: ℂ),
  by {have p1: (x.fst: ℂ) * ((z: ℂ)  + (x.snd: ℂ) * ((x.fst: ℂ))⁻¹)=
  ((x.fst: ℂ) * (z: ℂ)  + (x.fst : ℂ) * ((x.fst: ℂ))⁻¹ * (x.snd: ℂ)),
  ring_nf,
  rw mul_inv_cancel at p1,
  simp only [one_mul] at p1,
  rw p1,
  exact h0,},
  rw this,},
  rw h1,
  rw complex.abs_mul,
  rw complex.abs_mul,
  have h3: complex.abs (↑(x.fst) ^ k)= (complex.abs (↑(x.fst)))^k , by {apply complex.abs_pow, },
  rw h3,
  rw C1,
  have h4: complex.abs (↑n ^ k)=↑n ^ k, by {norm_cast, },
  rw h4,
  rw mul_comm,
  apply mul_le_mul_of_nonneg_left,
  have:=auxlem2 z n  x h k ,
  apply this, norm_cast,
  simp only [zero_le'],
  simp only [complex.abs_pos, ne.def],
  have hh : ((x.fst): ℂ) * (z: ℂ) + (x.snd: ℂ) ≠ 0, by {
  intro H,
  have H1 : x.1 = 0 ∨ (z: ℂ).im = 0, by simpa using congr_arg complex.im H,
  cases H1, {rw H1 at C1, simp only [int.cast_zero, complex.abs_zero] at C1,
  norm_cast at C1,
  rw ← C1 at hn,
  simp only [nat.one_ne_zero, square_mem, le_zero_iff] at *,
  exact hn,},
  have HH:= z.property,
  simp only [subtype.val_eq_coe] at HH,
  rw H1 at HH,
  simp at HH,
  exact HH,},
  apply pow_ne_zero,
  exact hh,
  simp only [complex.abs_mul],
  apply mul_pos,
  rw complex.abs_pos,
  apply pow_ne_zero,
  have:= rfunct_pos z,
  norm_cast,
  intro np,
  rw np at this,
  simp only [lt_self_iff_false] at this,
  exact this,
  simp only [complex.abs_pos],
  apply pow_ne_zero,
  norm_cast,
  intro Hn,
  rw Hn at hn,
  simp only [nat.one_ne_zero, le_zero_iff] at hn,
  exact hn,
  have C2: complex.abs (x.2: ℂ)=n, by {simp only [square_mem] at h,
  have:=max_aux'' x.1.nat_abs x.2.nat_abs n h,
  norm_cast,
  cases this,
  by_contra,
  norm_cast at C1,
  rw ← this at C1,
  rw int.abs_eq_nat_abs at C1,
  simp only [eq_self_iff_true, not_true] at C1,
  exact C1,
  rw ← this,
  rw int.abs_eq_nat_abs,},
  rw inv_le_inv,
  have h0: (x.2: ℂ ) ≠ 0, by {norm_cast,
  intro hx,
  rw hx at C2,
  simp only [int.cast_zero, complex.abs_zero] at C2,
  norm_cast at C2,
  rw ← C2 at hn,
  simp only [nat.one_ne_zero, le_zero_iff] at hn,
  exact hn,},
  have h1:(↑(x.fst) * ↑z + ↑(x.snd)) ^ k =  (↑(x.snd))^k* (((x.1:ℂ)/(x.2: ℂ))*(z: ℂ)+1)^k,
  by {rw ← mul_pow,simp only,
  rw div_eq_mul_inv,
  have: (x.snd: ℂ) * ((x.fst: ℂ) * ((x.snd: ℂ))⁻¹ * (z:ℂ) + 1)=
  ((x.snd: ℂ ) * ((x.snd : ℂ))⁻¹ * (x.fst : ℂ )* (z: ℂ) + (x.snd: ℂ)), by {ring,},
  rw this,
  rw mul_inv_cancel,
  simp only [one_mul],
  exact h0,},
  rw h1,
  rw complex.abs_mul,
  rw complex.abs_mul,
  have h3: complex.abs (↑(x.2) ^ k)= (complex.abs (↑(x.2)))^k ,
  by {apply complex.abs_pow,},
  rw h3,
  rw C2,
  have h4: complex.abs (↑n ^ k)=↑n ^ k, by {norm_cast, },
  rw h4,
  rw mul_comm,
  apply mul_le_mul_of_nonneg_left,
  have:=auxlem3 z n  x h k ,
  apply this,
  norm_cast,
  simp only [zero_le'],
  have hh : ((x.fst): ℂ) * (z: ℂ) + (x.snd: ℂ) ≠ 0,
  by {intro H,
  have H1 : x.1 = 0 ∨ (z: ℂ).im = 0,
  by simpa using congr_arg complex.im H,
  cases H1,
  {rw H1 at H,
  simp only [int.cast_eq_zero, int.cast_zero, zero_mul, zero_add] at H,
  rw H at C2,
  simp only [int.cast_zero, complex.abs_zero] at C2,
  norm_cast at C2,
  rw ← C2 at hn,
  simp only [nat.one_ne_zero, square_mem, le_zero_iff] at *,
  exact hn},
  have HH:= z.property, simp only [subtype.val_eq_coe] at HH,
  rw H1 at HH, simp only [lt_self_iff_false] at HH,
  exact HH,},
  rw complex.abs_pos,
  apply pow_ne_zero,
  exact hh,simp only [complex.abs_mul],
  apply mul_pos,
  rw complex.abs_pos,
  apply pow_ne_zero,
  have:= rfunct_pos z,
  norm_cast,
  intro np,
  rw np at this,
  simp only [lt_self_iff_false] at this,
  exact this,
  simp only [complex.abs_pos],
  apply pow_ne_zero,
  norm_cast,
  intro Hn,
  rw Hn at hn,
  simp only [nat.one_ne_zero, le_zero_iff] at hn,
  exact hn,
end

lemma Eise_on_square_is_bounded' ( k : ℕ) (z : ℍ) (n : ℕ) (hn: 1 ≤ n): ∀ (x: ℤ × ℤ),
x ∈ (Square n) →  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* n^k))⁻¹ :=
begin
intros x hx,
apply Eise_on_square_is_bounded k z n x hx hn,
end

lemma Eise_on_zero_Square (k : ℕ) (z : ℍ) (h: 1 ≤ k) :∀ (x: ℤ × ℤ),
x ∈ (Square 0) →  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* 0^k))⁻¹ :=
begin
  intros x hx,
  rw Square_zero at hx,
  simp only [finset.mem_singleton] at hx,
  simp_rw hx,
  simp only [add_zero, int.cast_zero, zero_mul, complex.abs_mul],
  have h1: (0: ℂ)^k=0, by {rw zero_pow_eq_zero, linarith,},
  rw h1,
  rw complex.abs_zero,
  simp only [mul_zero],
end

lemma Eise_on_square_is_bounded'' ( k : ℕ) (z : ℍ) (n : ℕ) (hn: 1 ≤ k): ∀ (x: ℤ × ℤ),
x ∈ (Square n) →  (complex.abs(((x.1: ℂ)*z+(x.2: ℂ))^k))⁻¹ ≤ (complex.abs ((rfunct z)^k* n^k))⁻¹ :=
begin
by_cases h0: n=0,
{rw h0, apply Eise_on_zero_Square k z hn, },
have Hn: 1 ≤ n,
by {have:=nat.pos_of_ne_zero,
simp at this,
work_on_goal 0 { cases z, solve_by_elim },},
intros x hx,
apply Eise_on_square_is_bounded k z n x hx Hn,
end

lemma natpowsinv (x : ℝ) (n : ℤ)  (h2: x ≠ 0): (x^(n-1))⁻¹=(x^n)⁻¹*x:=
begin
have:=zpow_sub_one₀ h2 n,
rw this,
have h3:=mul_zpow₀ (x^n) (x⁻¹) (-1),
simp at *,
exact h3,
end

/-Sum over squares is bounded -/
lemma BigClaim (k : ℕ) (z : ℍ) (h : 3 ≤ k):
  ∀ (n: ℕ), ∑ (y: ℤ × ℤ) in (Square n),
  ((real_Eise k z) y)  ≤ (8/((rfunct z)^k))*(n^((k: ℤ)-1))⁻¹:=
begin
  intro n,
  rw real_Eise,
  simp only [one_div, complex.abs_pow, complex.abs_inv, zpow_coe_nat],
  have k0: 1 ≤ k, by {linarith,},
  have BO :=  Eise_on_square_is_bounded'' ( k : ℕ) (z : ℍ) (n : ℕ) k0,
  by_cases n0 : n=0,
  { rw n0,
  rw Square_zero,
  simp only [add_zero, int.cast_zero, nat.cast_zero, zero_mul, finset.sum_singleton],
  have H0: (0: ℂ)^k=0, by {rw zero_pow_eq_zero, linarith,},
  simp only [complex.abs_zero, inv_zero],
  have H00: (0: ℝ)^((k: ℤ)-1)=0,
  by { rw zero_zpow, linarith,},
  rw H00,
  simp [inv_zero, mul_zero], norm_cast at *, rw H0,},
  have := finset.sum_le_sum BO,
  simp only [finset.sum_const, complex.abs_mul, nsmul_eq_mul] at this,
  rw Square_size n at this,
  norm_cast at this,
  have ne:( (8 * n) * (complex.abs (rfunct z ^ k) * ((n ^ k): ℝ))⁻¹ : ℝ)=
  (8/((rfunct z)^k))*(n^((k: ℤ)-1))⁻¹,
  by {rw complex.abs_pow,
  rw complex.abs_of_nonneg,
  rw ← mul_pow,
  rw div_eq_inv_mul,
  have : 8* ↑n * ((rfunct z * ↑n) ^ k)⁻¹= 8*((rfunct z)^k)⁻¹ * (↑n^((k: ℤ)-1))⁻¹,
  by {have dis: ((rfunct z * ↑n) ^ k)⁻¹ = ((rfunct z)^k)⁻¹* (↑n^k)⁻¹,
  by {rw mul_pow,
  simp_rw [← zpow_neg_one],
  simp_rw [← mul_zpow₀], },
  simp [dis],
  rw natpowsinv,
  ring,
  norm_cast,
  intro hN,
  rw hN at n0,
  simp only [eq_self_iff_true, not_true] at n0,
  exact n0,},
  rw this,
  ring,
  have rpos := rfunct_pos z,
  apply le_of_lt rpos,},
  norm_cast at ne,
  rw ne at this,
  norm_cast,
  simp at *,
  apply this,
  have hhh := nat.pos_of_ne_zero n0,
  linarith,
end


lemma SmallClaim (k : ℕ) (z : ℍ) (h : 3 ≤ k):
 ∀ (n : ℕ), (λ (x: ℕ), ∑ (y : ℤ × ℤ) in (Square x),  (real_Eise k z) y) n ≤  (8/(rfunct z)^k) * ((rie (k-1)) n):=
begin
have BIGCLAIM:= BigClaim k z h,
simp only at BIGCLAIM,
rw rie,
simp only [one_div],
intro n,
have tr :((↑n ^ ((k: ℤ) - 1))⁻¹: ℝ)=((↑n ^ ((k: ℝ) - 1))⁻¹: ℝ), by {simp [inv_inj],
have:= realpow n k,
rw ← this,
simp [int.cast_coe_nat, int.cast_one, int.cast_sub],},
rw ← tr,
apply BIGCLAIM n,
end


lemma real_eise_is_summable (k : ℕ) (z : ℍ) (h : 3 ≤ k): summable (real_Eise k z):=
begin
  let In:=Square,
  have HI:=Squares_cover_all,
  let g:= λ (y : ℤ × ℤ), (real_Eise k z) y,
  have gpos: ∀ (y : ℤ × ℤ), 0 ≤ g y,
  by {simp_rw g, intro y, rw real_Eise, simp, simp [complex.abs_nonneg],},
  have index_lem:= sum_lemma g  gpos In HI,
  rw index_lem,
  let e:=λ (x: ℕ), ∑ (y : ℤ × ℤ) in (In x), g y,
  have BIGCLAIM: ∀ (n : ℕ), ∑ (y : ℤ × ℤ) in (In n), g y ≤(8/((rfunct z)^k))*(n^((k: ℤ)-1))⁻¹,
  by {simp_rw g,
  apply BigClaim k z h,},
  have smallerclaim:  ∀ (n : ℕ), e n ≤  (8/(rfunct z)^k) * ((rie (k-1)) n),
  by {simp_rw e,
  apply SmallClaim k z h,},
  have epos: ∀ (x : ℕ), 0 ≤ e x, by {simp_rw e, simp_rw g, intro x,
  apply finset.sum_nonneg,  intros i hi, apply complex.abs_nonneg, },
  have hk: 1 < ((k-1): ℤ), by { linarith, },
  have nze: ((8/((rfunct z)^k)): ℝ)  ≠ 0,
  by {apply div_ne_zero,
  simp only [ne.def, not_false_iff, bit0_eq_zero, one_ne_zero],
  apply pow_ne_zero,
  simp only [ne.def],
  by_contra HR,
  have := rfunct_pos z,
  rw HR at this,
  simp only [lt_self_iff_false] at this,
    exact this, },
  have riesum:=int_Riemann_zeta_is_summmable (k-1) hk,
  have riesum': summable (λ (n : ℕ), (8 / (rfunct z)^k) * rie (↑k - 1) n),
  by {rw (summable_mul_left_iff nze).symm,
  simp only [int.cast_coe_nat, int.cast_one, int.cast_sub] at riesum,
  apply riesum,},
  have:=summable_of_nonneg_of_le epos smallerclaim,
  apply this,
  apply riesum',
end


lemma Real_Eisenstein_bound (k : ℕ) (z : ℍ) (h : 3 ≤ k):
    (real_Eisenstein_series_of_weight_ k z) ≤ (8/(rfunct z)^k)*Riemann_zeta (k-1):=
begin
  rw [real_Eisenstein_series_of_weight_, Riemann_zeta, ← tsum_mul_left],
  let In:=Square,
  have HI:=Squares_cover_all,
  let g:= λ (y : ℤ × ℤ), (real_Eise k z) y,
  have gpos: ∀ (y : ℤ × ℤ), 0 ≤ g y,
  by {simp_rw g, intro y, rw real_Eise, simp, simp  [complex.abs_nonneg],},
  have hgsumm: summable g,
  by {simp_rw g, apply real_eise_is_summable k z h, },
  have index_lem:= tsum_lemma g In HI hgsumm,
  simp_rw g at index_lem,
  simp,
  rw index_lem,
  have ind_lem2:=sum_lemma g gpos In HI,
  have smallclaim:= SmallClaim k z h,
  have hk: 1 < ((k-1): ℤ), by { linarith, },
  have nze: ((8/((rfunct z)^k)): ℝ)  ≠ 0,
  by {apply div_ne_zero, simp, apply pow_ne_zero,
  simp, by_contra HR,
  have:=rfunct_pos z,
  rw HR at this,
  simp at this,
  exact this, },
  have riesum:=int_Riemann_zeta_is_summmable (k-1) hk,
  have riesum': summable (λ (n : ℕ), (8 / (rfunct z)^k) * rie (↑k - 1) n),
  by {rw (summable_mul_left_iff nze).symm,
  simp at riesum,
  apply riesum,},
  apply tsum_le_tsum,
  apply smallclaim,
  simp_rw g at ind_lem2,
  rw ← ind_lem2,
  simp_rw g at hgsumm,
  apply hgsumm,
  apply riesum',
end

lemma Eisenstein_series_is_summable (k : ℕ) (z : ℍ) (h : 3 ≤ k) : summable (Eise k z) :=
begin
let f:=(Eise k z),
have sum_Eq:  summable (λ x, abs (f x)) → summable f, by {apply summable_if_complex_abs_summable,},
apply sum_Eq,
simp_rw f,
have:=real_eise_is_summable k z h,
rw real_Eise at this,
exact this,
end

/--The sum of Eise over the `Square`'s-/
def eisen_square (k : ℤ) (n: ℕ): ℍ → ℂ:=
λ z, ∑ x in Square n, Eise k z x


lemma Eisenstein_series_is_sum_eisen_squares (k: ℕ) (z: ℍ) (h : 3 ≤ k) :
(Eisenstein_series_of_weight_ k z) = ∑' (n : ℕ), eisen_square k n z:=
begin
rw Eisenstein_series_of_weight_, simp_rw eisen_square,

have HI:=Squares_cover_all,
let g:= λ (y : ℤ × ℤ),  (Eise k z ) y,
have hgsumm: summable g, by {simp_rw g, apply Eisenstein_series_is_summable k z h, },
have index_lem:= tsum_lemma' g Square HI hgsumm, simp_rw g at index_lem, exact index_lem,

end

def Eisen_partial_sums (k: ℤ) (n : ℕ): ℍ → ℂ:=
λ z, ∑ x in (finset.range n), (eisen_square k x z)

def upper_half_space_slice (A B : ℝ) :=
  {z : ℍ | complex.abs(z.1.1) ≤ A ∧ complex.abs(z.1.2) ≥ B  }

instance upper_half_space_slice_to_uhs (A B : ℝ) :
  has_coe (upper_half_space_slice A B) ℍ := ⟨λ z, z.1⟩

@[simp]lemma slice_mem (A B : ℝ) (z: ℍ): z ∈ (upper_half_space_slice A B) ↔
(complex.abs(z.1.1) ≤ A ∧ complex.abs(z.1.2) ≥ B) :=iff.rfl

lemma slice_in_upper_half (A B : ℝ) (x : (upper_half_space_slice A B) ) :
  x.1.1 ∈ ℍ'.1:=
begin
have hx : 0 < (x.1).im, by {apply upper_half_plane.im_pos,},
simp at hx,
simp,
apply hx,
end

lemma ball_coe (z w : ℍ) (ε : ℝ) (hε : 0 < ε) :
  w ∈ metric.closed_ball z ε ↔ w.1 ∈ metric.closed_ball z.1 ε :=
begin
simp,
split,
intro hzw,
exact hzw,
intro hzw,
exact hzw,
end

lemma ball_in_upper_half (z : ℍ) (A B ε : ℝ)(hB : 0 < B) ( hε : 0 < ε) (hBε : ε < B)
  (h : metric.closed_ball z ε ⊆ upper_half_space_slice A B) :
    metric.closed_ball z.1 ε ⊆ ℍ'.1 :=
begin
intros x hx,
simp at *,
have hg : 0 < (x.2), by {
  rw metric.closed_ball at h,
    have hz : z ∈ upper_half_space_slice A B, by {apply h, simp [hε.le]},
    simp at hz,
    have hz2:= z.2,
    have hzB: B ≤ complex.abs z.1.2, by {simp [hz.2],},
    rw dist_eq_norm at hx,
    simp at hx,
    have h3:= le_trans (abs_im_le_abs (x-z.1)) hx,
    have h4:= _root_.abs_sub_le z.1.2 x.2 0,
    rw sub_im at h3,
    rw _root_.abs_sub_comm at h3,
    have h33: -ε ≤ - |z.im - x.im|, by {simp, apply h3, },
    simp at h4,
    have h5 : |z.im| - |z.im - x.im| ≤ |x.im|, by {linarith,},
    simp at hzB,
    have h6 : B - ε ≤ |z.im| - |z.im - x.im|, by {linarith, },
    by_contradiction hc,
    simp at hc,
    have hcc: 0 ≤ -x.im, by {linarith, },
    have hzc :|z.im - x.im| = z.im - x.im, by {apply _root_.abs_of_nonneg, apply add_nonneg,
    apply z.2.le, apply hcc,},
    have hzp : |z.im| = z.im, by {apply _root_.abs_of_nonneg z.2.le,},
    simp_rw [hzc, hzp] at h6,
    simp only [sub_sub_cancel] at h6,
    linarith,},
apply hg,
end

lemma closed_ball_in_slice (z : ℍ) : ∃ (A B ε : ℝ), 0 < ε ∧ 0 < B ∧
  metric.closed_ball z ε ⊆ upper_half_space_slice A B ∧  0 ≤ A ∧ ε < B:=
begin
  let e := 3⁻¹ * complex.abs(z.1.2),
  let a := complex.abs(z.1.2) +  complex.abs(z),
  let b := complex.abs(z.1.2) - e,
  use a,
  use b,
  use e,
  split,
  simp_rw e,
  simp,
  apply mul_pos,
  rw inv_pos,
  linarith,
  simp,
  apply upper_half_plane.im_ne_zero z,
  split,
  simp_rw b,
  simp_rw e,
  ring_nf,
  simp only [abs_of_real, upper_half_plane.coe_im, subtype.val_eq_coe],
  apply mul_pos,
  nlinarith,
  simp,
  apply upper_half_plane.im_ne_zero z,
  split,
  intro x,
  simp only [abs_of_real, tsub_le_iff_right, ge_iff_le, metric.mem_closed_ball, slice_mem,
  upper_half_plane.coe_im, subtype.val_eq_coe, upper_half_plane.coe_re],
  intro hxz,
  have d1 : dist x z = dist (x : ℂ) (z :ℂ), by {exact subtype.dist_eq x z,},
  rw d1 at  hxz,
  rw dist_eq_norm at hxz,
  simp only [norm_eq_abs] at hxz,
  have:= abs_sub_le x.1 z.1 0,
  simp only [sub_zero, subtype.val_eq_coe] at this,
  split,
  simp_rw a,
  have hre := le_trans (abs_re_le_abs x.1) this,
  rw upper_half_plane.re,
  simp only [abs_of_real, upper_half_plane.coe_im, subtype.val_eq_coe, upper_half_plane.coe_re] at *,
  apply le_trans hre,
  simp only [add_le_add_iff_right],
  apply le_trans hxz,
  simp_rw e,
  rw upper_half_plane.im,
  simp only [abs_of_real, upper_half_plane.coe_im, subtype.val_eq_coe],
  have hxim : 0 ≤ |z.im|, by {apply _root_.abs_nonneg,},
  ring_nf,
  linarith,
  have ineq1:= _root_.abs_sub_le z.1.2 x.1.2 0,
  simp only [sub_zero, upper_half_plane.coe_im, subtype.val_eq_coe] at ineq1,
  apply le_trans ineq1,
  rw add_comm,
  simp only [add_le_add_iff_left],
  have ki:= le_trans (abs_im_le_abs (x.1-z.1)) hxz,
  rw sub_im at ki,
  rw _root_.abs_sub_comm at ki,
  convert ki,
  simp_rw a,
  split,
  apply add_nonneg,
  apply complex.abs_nonneg,
  apply complex.abs_nonneg,
  simp_rw b,
  simp_rw e,
  ring_nf,
  rw ← sub_pos,
  have hr : 0 < complex.abs (z.1.im), by {simp, apply upper_half_plane.im_ne_zero z,},
  linarith,
end

/--Canonical point in the `A B` slice-/
def lbpoint (A B : ℝ) (h: 0 < B): ℍ := ⟨⟨A,B⟩, by { simp, exact h,},⟩

lemma aux55 (a b : ℝ ) (h : a ≠ 0 ) : a/(a+b)=1/(b/a+1) :=
begin
  have : b/a+1=(b+a)/a, by {ring_nf, simp [h],},
  rw this,
  simp,
  rw add_comm,
end

lemma aux4 (a b : ℝ) (h: 0 < b): (b^4+(a*b)^2)/(a^2+b^2)^2=1/((a/b)^2 +1 ):=
begin
  have h1 : (a^2+b^2)^2=(a^2+b^2)*(a^2+b^2), by {ring,},
  rw h1,
  have h2: (b^4+(a*b)^2)=b^2*(a^2+b^2) , by {ring},
  rw h2,
  rw mul_div_assoc,
  simp only [one_div, div_pow, div_self_mul_self'],
  field_simp,
  have hb : b^2 ≠ 0 , by {simp [h], intro h3, linarith,},
  have:= (aux55  (b^2) (a^2) hb),
  rw add_comm,
  exact this,
end

lemma aux5 (a b : ℝ): 0 < a^2/b^2+1:=
begin
  have h1: 0 ≤a^2/b^2, by  {apply div_nonneg, nlinarith, nlinarith, },
  linarith,
end

lemma aux6 (a b : ℝ) (h: 0 ≤  a) (h2: 0 ≤ b) : a ≤ b → a^2 ≤ b^2 :=
begin
  intro hab,
  nlinarith,
end

lemma rfunct_lower_bound_on_slice (A B : ℝ) (h: 0 < B) (z : upper_half_space_slice A B) :
rfunct (lbpoint A B h) ≤  rfunct(z.1) :=
begin
  simp at *,
  simp_rw rfunct,
  simp_rw lbpoint,
  simp only [ min_le_iff, le_min_iff,subtype.val_eq_coe],
  cases z,
  cases z_property,
  cases z_val,
  dsimp at *,
  simp at *,
  fsplit,
  simp_rw lb,
  rw real.sqrt_le_sqrt_iff,
  have h1: B^2 ≤ complex.abs (z_val_val.im)^2, by {norm_cast, nlinarith, },
  norm_cast at h1,
  rw _root_.sq_abs at h1,
  simp [h1],
  nlinarith,
  simp_rw lb,
  rw real.sqrt_le_sqrt_iff,
  rw real.sqrt_le_sqrt_iff,
  rw aux4,
  rw aux4,
  simp,
  rw inv_le_inv,
  simp,
  have i1: (((z_val_val.im)^2)⁻¹ : ℝ)≤ ((B^2)⁻¹ : ℝ) ,
    by {rw inv_le_inv,
    have h' : 0 ≤ B , by {linarith,},
    have z_prop' : 0 ≤ z_val_val.im, by {linarith,},
    apply aux6 _ _ h' z_prop',
    have : z_val_val.im = complex.abs (z_val_val.im),
    by  {norm_cast, have:= abs_of_pos z_val_property, exact this.symm,},
    norm_cast at this,
    rw this,
    exact z_property_right,
    apply pow_two_pos_of_ne_zero,
    linarith,
    apply pow_two_pos_of_ne_zero, linarith,},
  have i2: ((z_val_val.re)^2 : ℝ )≤ (A^2 : ℝ),
    by {have : (complex.abs (z_val_val.re))^2 = z_val_val.re^2,
    by {norm_cast,
    simp,},
    norm_cast at this,
    rw ← this,
    have v2: 0 ≤ complex.abs (z_val_val.re), by {apply complex.abs_nonneg,},
    norm_cast at v2,
    have v1: 0 ≤ A, by {apply le_trans v2 z_property_left,},
    apply aux6 _ _ v2 v1,
    exact z_property_left,},
  ring_nf, simp at *,
  have i3:= mul_le_mul i1 i2,
  have i4: 0 ≤ (z_val_val.re)^2, by {nlinarith,},
  have i5: 0 ≤ (B ^ 2)⁻¹ , by { simp, nlinarith,},
  have i6:= i3 i4 i5,
  simp_rw i6,
  simp,
  apply aux5,
  apply aux5,
  exact h,
  exact z_val_property,
  apply div_nonneg,
  apply right.add_nonneg,
  have he : even (4 : ℤ), by {simp,},
  have := even.zpow_nonneg he (z_val_val.im) ,
  apply this,
  simp,
  nlinarith,
  nlinarith,
  apply div_nonneg,
  apply right.add_nonneg,
  have he : even (4 : ℤ), by {simp,},
  have := even.zpow_nonneg he (z_val_val.im) ,
  apply this,
  simp only,
  nlinarith,
  nlinarith,
end


lemma rfunctbound (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B) (z : upper_half_space_slice A B) :
(8/(rfunct z)^k)*Riemann_zeta (k-1)  ≤ (8/(rfunct (lbpoint A B hb) )^k)*Riemann_zeta (k-1) :=
begin
  have h1:= rfunct_lower_bound_on_slice A B hb z,
  simp only [subtype.val_eq_coe] at h1,
  have v1: 0 ≤ rfunct z, by {have:= rfunct_pos z, linarith, },
  have v2: 0 ≤ rfunct (lbpoint A B hb), by {have:= rfunct_pos (lbpoint A B hb), linarith, },
  have h2 := pow_le_pow_of_le_left v2 h1 k,
  ring_nf,
  rw ← inv_le_inv at h2,
  have h3: 0 ≤  Riemann_zeta (k-1), by {have hk: 1 < (k-1 : ℤ), by { linarith,},
  have hkk: 1 < ((k-1 : ℤ) : ℝ), by {norm_cast, exact hk,},
  simp only [int.cast_coe_nat, int.cast_one, int.cast_sub] at hkk,
  have:= Riemann_zeta_pos (k-1) hkk, linarith,},
  nlinarith,
  apply pow_pos,
  apply rfunct_pos,
  apply pow_pos,
  apply rfunct_pos,
end


lemma rfunctbound' (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B) (z : upper_half_space_slice A B) (n : ℕ) :
(8/(rfunct z)^k)* (rie (k-1) n)  ≤ (8/(rfunct (lbpoint A B hb) )^k)* (rie  (k-1) n) :=
begin
  have h1:= rfunct_lower_bound_on_slice A B hb z,
  simp only [subtype.val_eq_coe] at h1,
  have v1: 0 ≤ rfunct z, by {have:= rfunct_pos z, linarith, },
  have v2: 0 ≤ rfunct (lbpoint A B hb), by {have:= rfunct_pos (lbpoint A B hb), linarith, },
  have h2 := pow_le_pow_of_le_left v2 h1 k,
  ring_nf,
  rw ← inv_le_inv at h2,
  have h3: 0 ≤  rie (k-1) n,
  by {rw rie,
  simp only [one_div, inv_nonneg],
  apply real.rpow_nonneg_of_nonneg,
  simp only [nat.cast_nonneg],},
  nlinarith,
  apply pow_pos,
  apply rfunct_pos,
  apply pow_pos,
  apply rfunct_pos,
end

lemma Real_Eisenstein_bound_unifomly_on_stip (k : ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B)
  (z : upper_half_space_slice A B) :
    (real_Eisenstein_series_of_weight_ k z.1) ≤ (8/(rfunct (lbpoint A B hb) )^k)*Riemann_zeta (k-1):=
begin
have : (8/(rfunct z)^k)*Riemann_zeta (k-1)  ≤ (8/(rfunct (lbpoint A B hb) )^k)*Riemann_zeta (k-1),
by {apply rfunctbound, exact h},
apply le_trans (Real_Eisenstein_bound k z h) this,
end

def Eisen_square_slice (k : ℤ) (A B : ℝ)  (n : ℕ) :
  (upper_half_space_slice A B) → ℂ := λ x, (eisen_square k n x)

def Eisen_par_sum_slice (k : ℤ) (A B : ℝ) (n : ℕ) :
  (upper_half_space_slice A B) → ℂ :=
  λ z, ∑ x in (finset.range n), (Eisen_square_slice k A B  x z)

instance : has_coe ℍ ℍ' :=
⟨ λ z, ⟨ z.1, by {simp, cases z, assumption,}, ⟩ ⟩

instance slice_coe (A B : ℝ) (hb : 0 < B) : has_coe (upper_half_space_slice A B) ℍ' :=
⟨λ (x : (upper_half_space_slice A B)), (x : ℍ')  ⟩

def Eisenstein_series_restrict (k : ℤ) (A B : ℝ) : (upper_half_space_slice A B) → ℂ :=
λ x, Eisenstein_series_of_weight_ k x

instance  nonemp (A B : ℝ) (ha : 0 ≤  A) (hb : 0 < B) : nonempty (upper_half_space_slice A B):=
begin
  let z:= (⟨  A, B⟩ : ℂ),
  rw ← exists_true_iff_nonempty,
  simp,
  use z,
  have zim: z.im = B, by {refl,},
  use hb,
  simp_rw z,
  simp_rw [upper_half_plane.re, upper_half_plane.im],
  simp,
  split,
  have:= abs_eq_self.2 ha,
  rw this,
  apply le_abs_self,
end

lemma Eisenstein_series_is_sum_eisen_squares_slice (k: ℕ) (h : 3 ≤ k) (A B : ℝ) (hb : 0 < B)
 (z: (upper_half_space_slice A B)) :
  (Eisenstein_series_restrict k A B z) = ∑' (n : ℕ), (Eisen_square_slice k A B n z):=
begin
  rw Eisenstein_series_restrict, simp_rw Eisen_square_slice,
  have HI:=Squares_cover_all,
  let g:= λ (y : ℤ × ℤ),  (Eise k z ) y,
  have hgsumm: summable g,
  by {simp_rw g, apply Eisenstein_series_is_summable k z h, },
  have index_lem:= tsum_lemma' g Square HI hgsumm,
  simp_rw g at index_lem,
  exact index_lem,
end

lemma Eisen_partial_tends_to_uniformly (k: ℕ) (h : 3 ≤ k) (A B : ℝ) (ha : 0 ≤ A) (hb : 0 < B) :
tendsto_uniformly (Eisen_par_sum_slice k A B ) (Eisenstein_series_restrict k A B) filter.at_top:=
begin
  let M : ℕ → ℝ := λ x,   (8/(rfunct (lbpoint A B hb) )^k)* (rie  (k-1) x),
  have:= M_test_uniform _ (Eisen_square_slice k A B ) M,
  simp_rw  ← (Eisenstein_series_is_sum_eisen_squares_slice k h A B hb _) at this,
  apply this,
  simp_rw Eisen_square_slice,
  simp_rw eisen_square,
  simp_rw M,
  simp_rw Eise,
  intros n a,
  have SC:= SmallClaim k a h n,
  rw real_Eise at SC,
  simp at SC,
  simp,
  have ineq1:
  complex.abs (∑ (x : ℤ × ℤ) in Square n, ((↑(x.fst) * ↑↑a + ↑(x.snd)) ^ k)⁻¹) ≤
  ∑ (x : ℤ × ℤ) in Square n, (complex.abs ((↑(x.fst) * ↑↑a + ↑(x.snd)) ^ k))⁻¹,
  by {simp,
  have := complex_abs_sum_le  (Square n)
  (λ  (x : ℤ × ℤ),  (((x.1 : ℂ) * (a : ℂ) + (x.2 : ℂ)) ^ k)⁻¹),
  simp at this,
  exact this, },
  simp at *,
  have SC2:= le_trans ineq1 SC,
  have rb := rfunctbound' k h A B hb a n,
  apply le_trans SC2 rb,
  apply_instance,
  apply_instance,
  simp_rw M,
  have hk: 1 < ((k-1): ℤ), by { linarith, },
  have nze: ((8/((rfunct (lbpoint A B hb))^k)): ℝ)  ≠ 0,
  by {apply div_ne_zero, simp, apply pow_ne_zero,
  simp, by_contra HR,
  have:=rfunct_pos (lbpoint A B hb),
  rw HR at this,
  simp at this,
  exact this, },
  have riesum:=int_Riemann_zeta_is_summmable (k-1) hk,
  rw (summable_mul_left_iff nze).symm,
  simp at riesum,
  apply riesum,
  apply Eisenstein_series.nonemp A B ha hb,
end

def powfun  (k : ℤ) : ℂ → ℂ :=
λ x, x^k

def trans (a b : ℤ) : ℂ → ℂ :=
λ x, a*x+b

def ein (a b k : ℤ): ℂ → ℂ :=
λ x, (a*x+b)^k

lemma com (a b k : ℤ): (ein a b k) = (powfun k) ∘ trans a b :=
begin
refl,
end

lemma d1 (k: ℤ) (x : ℂ): deriv (λ x, x^k) x = k*x^(k-1) :=
by {simp only [deriv_zpow'], }

lemma d2 (a b k: ℤ) (x : ℂ) (h : (a: ℂ)*x+b ≠ 0) : deriv (ein a b k) x = k*a*(a*x+b)^(k-1):=
begin
  rw com,
  rw deriv.comp,
  rw powfun,
  rw trans,
  simp,
  ring,
  rw powfun,
  rw trans, simp, simp_rw differentiable_at_zpow ,
  simp [h],
  rw trans,
  simp only [differentiable_at_const,
  differentiable_at_add_const_iff,
  differentiable_at_id',
  differentiable_at.mul],
end


lemma aux8 (a b k: ℤ ) (x : ℂ): (((a : ℂ)*x+b)^k)⁻¹ =  ((a : ℂ)*x+b)^-k:=
begin
refine (zpow_neg₀ _ k).symm,
end

lemma dd2 (a b k: ℤ) (x : ℂ) (h : (a: ℂ)*x+b ≠ 0) :
  has_deriv_at (ein a b k) (k*(a*x+b)^(k-1)*(a) : ℂ) x:=
begin
  rw com,
  apply has_deriv_at.comp,
  rw powfun,
  rw trans,
  simp,
  apply has_deriv_at_zpow,
  simp [h],
  rw trans,
  apply has_deriv_at.add_const,
  have:= has_deriv_at.const_mul (a: ℂ) (has_deriv_at_id x) ,
  simp at *,
  exact this,
end

lemma H_member (z : ℂ) : z ∈ upper_half_space ↔ 0 < z.im:=iff.rfl

lemma Eise'_has_deriv_within_at (k : ℤ) (y: ℤ × ℤ) (hkn: k ≠ 0) :
  is_holomorphic_on (λ (z : ℍ'), Eise k z y):=
begin
  rw is_holomorphic_on,
  intro z,
  by_cases hy: (y.1 : ℂ)*z.1 + y.2 ≠ 0,
  simp_rw Eise, ring_nf,
  have:= aux8 y.1 y.2 k z.1,
  simp only [subtype.val_eq_coe] at this,
  have nz: (y.1 : ℂ)*z.1 + y.2 ≠ 0 , by {apply hy,},
  have hdd:= dd2 y.1 y.2 (-k) z nz,
  rw ein at hdd,
  have H' := has_deriv_at.has_deriv_within_at hdd,
  have H : has_deriv_within_at (λ (x : ℂ), (↑(y.fst) * x + ↑(y.snd)) ^ -k)
  (↑-k * (↑(y.fst) * ↑z + ↑(y.snd)) ^ (-k - 1) * ↑(y.fst)) upper_half_space ↑z, by {apply H'},
  simp at H,
  let fx:=(-k*((y.1:ℂ)*z.1+y.2)^(-k-1)*(y.1) : ℂ),
  use fx,
  rw has_deriv_within_at_iff_tendsto at *,
  simp  [ zpow_neg₀, algebra.id.smul_eq_mul, eq_self_iff_true,
   ne.def, int.cast_neg, subtype.val_eq_coe, norm_eq_abs, sub_neg_eq_add] at *,
  rw metric.tendsto_nhds_within_nhds at *,
  intros ε hε,
  have HH:= H ε hε,
  use classical.some HH,
  have:= classical.some_spec HH,
  simp only [exists_prop, gt_iff_lt, norm_mul, dist_zero_right,
    norm_inv] at this,
  have hg:= this.1,
  simp only [hg, true_and, exists_prop, gt_iff_lt, norm_mul, dist_zero_right, norm_inv] at *,
  intros x hx hd,
  dsimp at *,
  simp_rw extend_by_zero,
  simp only [dite_eq_ite, if_true, subtype.coe_prop, subtype.coe_eta, subtype.coe_mk],
  rw ← dite_eq_ite, rw dif_pos hx,
  have H3:= this_1 hx hd,
  simp_rw fx,
  convert H3,
  ring,
  simp only [not_not, subtype.val_eq_coe] at hy,
  have hz: y.1 =0 ∧ y.2 = 0,
  by {by_contra,
  simp only [not_and] at h,
  cases z,
  cases y,
  dsimp at *,
  injections_and_clear,
  dsimp at *,
  simp only [int_cast_re, int.cast_eq_zero, add_zero, int_cast_im, zero_mul, sub_zero,
  mul_eq_zero] at *,
  cases h_2,
  rw h_2 at h_1,
  simp only [int.cast_eq_zero, int.cast_zero, zero_mul, zero_add] at *,
  have:= h h_2,
  rw h_1 at this,
  simp only [eq_self_iff_true, not_true] at this,
  exact this,
  simp only [H_member] at z_property,
  rw h_2 at z_property,
  simp only [lt_self_iff_false] at z_property,
  exact z_property,},
  simp_rw Eise, rw [hz.1, hz.2],
  simp only [one_div, add_zero, int.cast_zero, zero_mul],
  have zhol:= zero_hol ℍ' ,
  rw is_holomorphic_on at zhol,
  have zhol':= zhol z,
  simp only at zhol',
  have zk: ((0: ℂ)^k)⁻¹ =0,
  by {simp only [inv_eq_zero],
  apply zero_zpow,
  apply hkn,},
  rw zk,
  exact zhol',
end

lemma Eise'_has_diff_within_at (k : ℤ) (y: ℤ × ℤ) (hkn: k ≠ 0) :
  differentiable_on ℂ (extend_by_zero (λ (z : ℍ'), Eise k z y)) ℍ':=
begin
  have:= is_holomorphic_on_iff_differentiable_on ℍ' (λ (z : ℍ'), Eise k z y),
  simp only [subtype.coe_mk],
  rw this,
  apply Eise'_has_deriv_within_at,
  apply hkn,
end

lemma Eis_diff_on_ball {R : ℝ} {z w : ℂ} (hw : w ∈ metric.ball z R) (k : ℤ) (y: ℤ × ℤ) (hkn: k ≠ 0)
  (h : metric.closed_ball z R ⊆ ℍ' ):
  differentiable_on ℂ (extend_by_zero (λ (z : ℍ'), Eise k z y)) (metric.closed_ball z R) :=
begin
  apply differentiable_on.mono (Eise'_has_diff_within_at k y hkn),
  simp only [metric.mem_ball, ne.def, subtype.coe_mk] at *,
  apply h,
end

end Eisenstein_series
