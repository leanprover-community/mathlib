import tactic.ring
import tactic.pi_instances
import analysis.complex.basic
import ring_theory.coprime.basic
import ring_theory.int.basic
import data.complex.basic
import analysis.p_series
import data.real.nnreal
import analysis.special_functions.pow

universes u v

open complex

open_locale big_operators

noncomputable theory


/-! ### Riemann zeta function -/


def rie (k : ℝ): ℕ → ℝ :=
λ x, 1/((x: ℝ)^k)


/--The `Riemann zeta function` defined on the real numbers.
It is defined as the infinite sum of the reciprocals of the naturals to the power `k`. We check it is summable at the end for real `k` greater than 1.-/

def Riemann_zeta (k : ℝ): ℝ :=
 ∑' (x : ℕ), (rie k x)


lemma Riemann_zeta_is_summmable (k: ℝ) (h: 1 < k): summable (rie k):=
begin
rw rie,

have h2:=nnreal.summable_one_div_rpow.2 h, simp only [one_div, real.summable_nat_rpow_inv], exact h,
end

lemma int_Riemann_zeta_is_summmable (k: ℤ) (h: 1 < k): summable (rie k):=
begin
apply Riemann_zeta_is_summmable, norm_cast, exact h,
end

lemma Riemann_zeta_pos (k : ℝ) (h: 1 < k) : 0 < Riemann_zeta k :=
begin
  rw Riemann_zeta,
  apply tsum_pos (Riemann_zeta_is_summmable k h) _ 1,
  rw rie,
  simp,
  intro b,
  simp_rw rie,
  simp,
  apply real.rpow_nonneg_of_nonneg,
  norm_cast,
  linarith,
end
