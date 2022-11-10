/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
import algebra.euclidean_domain.defs
import algebra.ring.divisibility
import algebra.ring.regular
import algebra.field.defs
import algebra.group_with_zero.divisibility

/-!
# Lemmas about Euclidean domains

## Main statements

* `gcd_eq_gcd_ab`: states Bézout's lemma for Euclidean domains.

-/

universe u

namespace euclidean_domain
variable {R : Type u}
variables [euclidean_domain R]

local infix ` ≺ `:50 := euclidean_domain.r

lemma mul_div_cancel_left {a : R} (b) (a0 : a ≠ 0) : a * b / a = b :=
eq.symm $ eq_of_sub_eq_zero $ classical.by_contradiction $ λ h,
begin
  have := mul_left_not_lt a h,
  rw [mul_sub, sub_eq_iff_eq_add'.2 (div_add_mod (a*b) a).symm] at this,
  exact this (mod_lt _ a0)
end

lemma mul_div_cancel (a) {b : R} (b0 : b ≠ 0) : a * b / b = a :=
by { rw mul_comm, exact mul_div_cancel_left a b0 }

@[simp] lemma mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a :=
⟨λ h, by { rw [← div_add_mod a b, h, add_zero], exact dvd_mul_right _ _ },
 λ ⟨c, e⟩, begin
  rw [e, ← add_left_cancel_iff, div_add_mod, add_zero],
  haveI := classical.dec,
  by_cases b0 : b = 0,
  { simp only [b0, zero_mul] },
  { rw [mul_div_cancel_left _ b0] }
 end⟩

@[simp] lemma mod_self (a : R) : a % a = 0 :=
mod_eq_zero.2 dvd_rfl

lemma dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a :=
by rw [dvd_add_iff_right (h.mul_right _), div_add_mod]

@[simp] lemma mod_one (a : R) : a % 1 = 0 :=
mod_eq_zero.2 (one_dvd _)

@[simp] lemma zero_mod (b : R) : 0 % b = 0 :=
mod_eq_zero.2 (dvd_zero _)

@[simp, priority 900] lemma zero_div {a : R} : 0 / a = 0 :=
classical.by_cases
  (λ a0 : a = 0, a0.symm ▸ div_zero 0)
  (λ a0, by simpa only [zero_mul] using mul_div_cancel 0 a0)

@[simp, priority 900] lemma div_self {a : R} (a0 : a ≠ 0) : a / a = 1 :=
by simpa only [one_mul] using mul_div_cancel 1 a0

lemma eq_div_of_mul_eq_left {a b c : R} (hb : b ≠ 0) (h : a * b = c) : a = c / b :=
by rw [← h, mul_div_cancel _ hb]

lemma eq_div_of_mul_eq_right {a b c : R} (ha : a ≠ 0) (h : a * b = c) : b = c / a :=
by rw [← h, mul_div_cancel_left _ ha]

theorem mul_div_assoc (x : R) {y z : R} (h : z ∣ y) : x * y / z = x * (y / z) :=
begin
  classical, by_cases hz : z = 0,
  { subst hz, rw [div_zero, div_zero, mul_zero] },
  rcases h with ⟨p, rfl⟩,
  rw [mul_div_cancel_left _ hz, mul_left_comm, mul_div_cancel_left _ hz]
end

@[simp, priority 900] -- This generalizes `int.div_one`, see note [simp-normal form]
lemma div_one (p : R) : p / 1 = p :=
(euclidean_domain.eq_div_of_mul_eq_left (one_ne_zero' R) (mul_one p)).symm

lemma div_dvd_of_dvd {p q : R} (hpq : q ∣ p) :
  p / q ∣ p :=
begin
  by_cases hq : q = 0,
  { rw [hq, zero_dvd_iff] at hpq,
    rw hpq,
    exact dvd_zero _ },
  use q,
  rw [mul_comm, ← euclidean_domain.mul_div_assoc _ hpq, mul_comm,
      euclidean_domain.mul_div_cancel _ hq]
end

lemma dvd_div_of_mul_dvd {a b c : R} (h : a * b ∣ c) : b ∣ c / a :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp only [div_zero, dvd_zero] },
  rcases h with ⟨d, rfl⟩,
  refine ⟨d, _⟩,
  rw [mul_assoc, mul_div_cancel_left _ ha]
end

section gcd
variable [decidable_eq R]

@[simp] theorem gcd_zero_right (a : R) : gcd a 0 = a :=
by { rw gcd, split_ifs; simp only [h, zero_mod, gcd_zero_left] }

theorem gcd_val (a b : R) : gcd a b = gcd (b % a) a :=
by { rw gcd, split_ifs; [simp only [h, mod_zero, gcd_zero_right], refl]}

theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b :=
gcd.induction a b
  (λ b, by { rw gcd_zero_left, exact ⟨dvd_zero _, dvd_rfl⟩ })
  (λ a b aneq ⟨IH₁, IH₂⟩, by { rw gcd_val,
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩ })

theorem gcd_dvd_left (a b : R) : gcd a b ∣ a := (gcd_dvd a b).left

theorem gcd_dvd_right (a b : R) : gcd a b ∣ b := (gcd_dvd a b).right

protected theorem gcd_eq_zero_iff {a b : R} :
  gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
⟨λ h, by simpa [h] using gcd_dvd a b,
 by { rintro ⟨rfl, rfl⟩, exact gcd_zero_right _ }⟩

theorem dvd_gcd {a b c : R} : c ∣ a → c ∣ b → c ∣ gcd a b :=
gcd.induction a b
  (λ _ _ H, by simpa only [gcd_zero_left] using H)
  (λ a b a0 IH ca cb, by { rw gcd_val,
    exact IH ((dvd_mod_iff ca).2 cb) ca })

theorem gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b :=
⟨λ h, by {rw ← h, apply gcd_dvd_right },
 λ h, by rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩

@[simp] theorem gcd_one_left (a : R) : gcd 1 a = 1 :=
gcd_eq_left.2 (one_dvd _)

@[simp] theorem gcd_self (a : R) : gcd a a = a :=
gcd_eq_left.2 dvd_rfl

@[simp] theorem xgcd_aux_fst (x y : R) : ∀ s t s' t',
  (xgcd_aux x s t y s' t').1 = gcd x y :=
gcd.induction x y (by { intros, rw [xgcd_zero_left, gcd_zero_left] })
(λ x y h IH s t s' t', by { simp only [xgcd_aux_rec h, if_neg h, IH], rw ← gcd_val })

theorem xgcd_aux_val (x y : R) : xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) :=
by rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1, prod.mk.eta]

private def P (a b : R) : R × R × R → Prop | (r, s, t) := (r : R) = a * s + b * t

theorem xgcd_aux_P (a b : R) {r r' : R} : ∀ {s t s' t'}, P a b (r, s, t) →
  P a b (r', s', t') → P a b (xgcd_aux r s t r' s' t') :=
gcd.induction r r' (by { intros, simpa only [xgcd_zero_left] }) $ λ x y h IH s t s' t' p p', begin
  rw [xgcd_aux_rec h], refine IH _ p, unfold P at p p' ⊢,
  rw [mul_sub, mul_sub, add_sub, sub_add_eq_add_sub, ← p', sub_sub,
    mul_comm _ s, ← mul_assoc, mul_comm _ t, ← mul_assoc, ← add_mul, ← p,
    mod_eq_sub_mul_div]
end

/-- An explicit version of **Bézout's lemma** for Euclidean domains. -/
theorem gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcd_a a b + b * gcd_b a b :=
by { have := @xgcd_aux_P _ _ _ a b a b 1 0 0 1
  (by rw [P, mul_one, mul_zero, add_zero]) (by rw [P, mul_one, mul_zero, zero_add]),
rwa [xgcd_aux_val, xgcd_val] at this }

@[priority 70] -- see Note [lower instance priority]
instance (R : Type*) [e : euclidean_domain R] : is_domain R :=
by { haveI := classical.dec_eq R, exact
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    λ a b h, (or_iff_not_and_not.2 $ λ h0,
      h0.1 $ by rw [← mul_div_cancel a h0.2, h, zero_div]),
  ..e }}

end gcd

section lcm
variables [decidable_eq R]

theorem dvd_lcm_left (x y : R) : x ∣ lcm x y :=
classical.by_cases
  (assume hxy : gcd x y = 0, by { rw [lcm, hxy, div_zero], exact dvd_zero _ })
  (λ hxy, let ⟨z, hz⟩ := (gcd_dvd x y).2 in ⟨z, eq.symm $ eq_div_of_mul_eq_left hxy $
    by rw [mul_right_comm, mul_assoc, ← hz]⟩)

theorem dvd_lcm_right (x y : R) : y ∣ lcm x y :=
classical.by_cases
  (assume hxy : gcd x y = 0, by { rw [lcm, hxy, div_zero], exact dvd_zero _ })
  (λ hxy, let ⟨z, hz⟩ := (gcd_dvd x y).1 in ⟨z, eq.symm $ eq_div_of_mul_eq_right hxy $
    by rw [← mul_assoc, mul_right_comm, ← hz]⟩)

theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z :=
begin
  rw lcm, by_cases hxy : gcd x y = 0,
  { rw [hxy, div_zero], rw euclidean_domain.gcd_eq_zero_iff at hxy, rwa hxy.1 at hxz },
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩,
  suffices : x * y ∣ z * gcd x y,
  { cases this with p hp, use p,
    generalize_hyp : gcd x y = g at hxy hs hp ⊢, subst hs,
    rw [mul_left_comm, mul_div_cancel_left _ hxy, ← mul_left_inj' hxy, hp],
    rw [← mul_assoc], simp only [mul_right_comm] },
  rw [gcd_eq_gcd_ab, mul_add], apply dvd_add,
  { rw mul_left_comm, exact mul_dvd_mul_left _ (hyz.mul_right _) },
  { rw [mul_left_comm, mul_comm], exact mul_dvd_mul_left _ (hxz.mul_right _) }
end

@[simp] lemma lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z :=
⟨λ hz, ⟨(dvd_lcm_left _ _).trans hz, (dvd_lcm_right _ _).trans hz⟩,
λ ⟨hxz, hyz⟩, lcm_dvd hxz hyz⟩

@[simp] lemma lcm_zero_left (x : R) : lcm 0 x = 0 :=
by rw [lcm, zero_mul, zero_div]

@[simp] lemma lcm_zero_right (x : R) : lcm x 0 = 0 :=
by rw [lcm, mul_zero, zero_div]

@[simp] lemma lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0 :=
begin
  split,
  { intro hxy, rw [lcm, mul_div_assoc _ (gcd_dvd_right _ _), mul_eq_zero] at hxy,
    apply or_of_or_of_imp_right hxy, intro hy,
    by_cases hgxy : gcd x y = 0,
    { rw euclidean_domain.gcd_eq_zero_iff at hgxy, exact hgxy.2 },
    { rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩,
      generalize_hyp : gcd x y = g at hr hs hy hgxy ⊢, subst hs,
      rw [mul_div_cancel_left _ hgxy] at hy, rw [hy, mul_zero] } },
  rintro (hx | hy),
  { rw [hx, lcm_zero_left] },
  { rw [hy, lcm_zero_right] }
end

@[simp] lemma gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y :=
begin
  rw lcm, by_cases h : gcd x y = 0,
  { rw [h, zero_mul], rw euclidean_domain.gcd_eq_zero_iff at h, rw [h.1, zero_mul] },
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩,
  generalize_hyp : gcd x y = g at h hr ⊢, subst hr,
  rw [mul_assoc, mul_div_cancel_left _ h]
end

end lcm

section div

lemma mul_div_mul_cancel {a b c : R} (ha : a ≠ 0) (hcb : c ∣ b) :
  a * b / (a * c) = b / c :=
begin
  by_cases hc : c = 0, { simp [hc] },
  refine eq_div_of_mul_eq_right hc (mul_left_cancel₀ ha _),
  rw [← mul_assoc, ← mul_div_assoc _ (mul_dvd_mul_left a hcb),
         mul_div_cancel_left _ (mul_ne_zero ha hc)]
end

lemma mul_div_mul_comm_of_dvd_dvd {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b) :
  a * b / (c * d) = a / c * (b / d) :=
begin
  rcases eq_or_ne c 0 with rfl | hc0, { simp },
  rcases eq_or_ne d 0 with rfl | hd0, { simp },
  obtain ⟨k1, rfl⟩ := hac,
  obtain ⟨k2, rfl⟩ := hbd,
  rw [mul_div_cancel_left _ hc0, mul_div_cancel_left _ hd0, mul_mul_mul_comm,
    mul_div_cancel_left _ (mul_ne_zero hc0 hd0)],
end

end div

end euclidean_domain
