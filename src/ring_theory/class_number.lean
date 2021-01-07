import algebra.big_operators.finsupp
import algebra.floor
import group_theory.quotient_group
import linear_algebra.determinant
import linear_algebra.free_module
import linear_algebra.matrix
import ring_theory.dedekind_domain
import ring_theory.fractional_ideal

-- These results are in separate files for faster re-compiling.
-- They should be merged with the appropriate lower-level file when development is finished.
import ring_theory.class_number.det
import ring_theory.class_number.euclidean_absolute_value
import ring_theory.class_number.ideal
import ring_theory.class_number.integral_closure
import ring_theory.class_number.subalgebra

open ring

open_locale big_operators

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [field K] [field L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L] [is_separable f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]
variables (abs : euclidean_absolute_value R ℤ)

noncomputable def abs_norm [decidable_eq L] (x : integral_closure R L) : ℤ :=
abs (@algebra.norm R (integral_closure R L) _ _ _ _ _ _ _ (integral_closure.is_basis L f) x)

noncomputable def abs_frac_norm [decidable_eq L] (x : L) : ℚ :=
abs.to_frac f (algebra.norm (is_basis_coe f (integral_closure.is_basis L f)) x)

lemma abs_frac_norm_coe [decidable_eq L] (x : integral_closure R L) :
  abs_frac_norm f abs (x : L) = abs_norm f abs x :=
begin
  unfold abs_frac_norm abs_norm algebra.norm,
  rw [monoid_hom.coe_mk,
      to_matrix_is_basis_coe f (integral_closure.is_basis L f)
        (algebra.lmul (f.codomain) L x) (algebra.lmul R (integral_closure R L) x),
      det_map, monoid_hom.coe_mk],
  { exact abs.to_frac_to_map f _ },
  intro y,
  simp
end

/-- If `L` is a finite dimensional extension of the field of fractions of a Euclidean domain `R`,
there is a function mapping each `x : L` to the "closest" value that is integral over `R`. -/
noncomputable def integral_part (x : L) : integral_closure R L :=
∑ i, f.integral_part ((is_basis_coe f (integral_closure.is_basis L f)).repr x i) • i

variables [decidable_eq L]

section

variables (L)

include L f abs

def finset_approx : finset R := sorry

end

-- Theorem 4.1
lemma finset_approx.zero_not_mem : (0 : R) ∉ finset_approx L f abs := sorry

theorem exists_mem_finset_approx (g : L) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
    abs_frac_norm f abs (r • g - q) < 1 :=
sorry

-- Corollary 4.2
theorem exists_mem_finset_approx' (a : integral_closure R L) {b}
  (hb : b ≠ (0 : integral_closure R L)) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
    abs_norm f abs (r • a - q * b) < abs_norm f abs b :=
begin
  obtain ⟨q, r, hr, hrgq⟩ := exists_mem_finset_approx f abs (a / b : L),
  use [q, r, hr],
  unfold abs_frac_norm abs_norm at hrgq,
  have h_coe_b : (b : L) ≠ 0,
  { rwa [ne.def, submodule.coe_eq_zero] },
  have hb' : 0 < abs_frac_norm f abs (b : L),
  { exact (abs.to_frac f).pos ((algebra.norm_ne_zero _).mpr h_coe_b) },
  rw [← mul_lt_mul_right hb', one_mul] at hrgq,
  unfold abs_frac_norm at hrgq,
  rw [← (abs.to_frac f).map_mul, ← (algebra.norm _).map_mul, sub_mul, mul_comm, ← smul_eq_mul,
      smul_comm, smul_eq_mul, ← mul_div_assoc, mul_div_cancel_left _ h_coe_b] at hrgq,
  rw [← @int.cast_lt ℚ, ← abs_frac_norm_coe, ← abs_frac_norm_coe],
  unfold abs_frac_norm,
  exact_mod_cast hrgq
end

end euclidean_domain


section class_group

section integral_domain

variables {R K L : Type*} [integral_domain R]
variables [field K] [field L] [decidable_eq L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]

open ring.fractional_ideal units

section
/-- `to_principal_ideal x` sends `x ≠ 0 : K` to the fractional ideal generated by `x` -/
@[irreducible]
def to_principal_ideal : units f.codomain →* units (fractional_ideal f) :=
{ to_fun := λ x,
  ⟨ span_singleton x,
    span_singleton x⁻¹,
    by simp only [span_singleton_one, units.mul_inv', span_singleton_mul_span_singleton],
    by simp only [span_singleton_one, units.inv_mul', span_singleton_mul_span_singleton]⟩,
  map_mul' := λ x y, ext (by simp only [units.coe_mk, units.coe_mul, span_singleton_mul_span_singleton]),
  map_one' := ext (by simp only [span_singleton_one, units.coe_mk, units.coe_one]) }

local attribute [semireducible] to_principal_ideal

variables {f}

@[simp] lemma coe_to_principal_ideal (x : units f.codomain) :
  (to_principal_ideal f x : fractional_ideal f) = span_singleton x :=
rfl

@[simp] lemma to_principal_ideal_eq_iff {I : units (fractional_ideal f)} {x : units f.codomain} :
  to_principal_ideal f x = I ↔ span_singleton (x : f.codomain) = I :=
units.ext_iff

end

instance principal_ideals.normal : (to_principal_ideal f).range.normal :=
subgroup.normal_of_comm _

section
/-- The class group with respect to `f : fraction_map R K`
is the group of invertible fractional ideals modulo the principal ideals. -/
@[derive(comm_group)]
def class_group := quotient_group.quotient (to_principal_ideal f).range

@[simp] lemma fractional_ideal.coe_to_fractional_ideal_top :
  ((⊤ : ideal R) : fractional_ideal f) = 1 :=
by { rw [← ideal.one_eq_top], refl }

@[simp] lemma units.mk0_one {M : Type*} [group_with_zero M] (h) :
  units.mk0 (1 : M) h = 1 :=
by { ext, refl }

@[simp] lemma units.mk0_map {M : Type*} [group_with_zero M] (x y : M) (hxy) :
  mk0 (x * y) hxy = mk0 x (mul_ne_zero_iff.mp hxy).1 * mk0 y (mul_ne_zero_iff.mp hxy).2 :=
by { ext, refl }

/-- The monoid of nonzero ideals. -/
def nonzero_ideal (R : Type*) [integral_domain R] : submonoid (ideal R) :=
{ carrier := {I | I ≠ ⊥},
  one_mem' := show (1 : ideal R) ≠ ⊥, by { rw ideal.one_eq_top, exact submodule.bot_ne_top.symm },
  mul_mem' := λ I J (hI : I ≠ ⊥) (hJ : J ≠ ⊥), show I * J ≠ ⊥,
    by { obtain ⟨x, x_mem, x_ne⟩ := I.ne_bot_iff.mp hI,
         obtain ⟨y, y_mem, y_ne⟩ := J.ne_bot_iff.mp hJ,
         exact (submodule.ne_bot_iff _).mpr
           ⟨x * y, ideal.mul_mem_mul x_mem y_mem, mul_ne_zero x_ne y_ne⟩ } }

/-- Send a nonzero ideal to the corresponding class in the class group. -/
noncomputable def class_group.mk [is_dedekind_domain R] :
  nonzero_ideal R →* class_group f :=
(quotient_group.mk' _).comp
  { to_fun := λ I, units.mk0 I
      ((fractional_ideal.coe_to_fractional_ideal_ne_zero (le_refl (non_zero_divisors R))).mpr I.2),
    map_one' := by simp,
    map_mul' := λ x y, by simp }

lemma quotient_group.mk'_eq_mk' {G : Type*} [group G] {N : subgroup G} [hN : N.normal] {x y : G} :
  quotient_group.mk' N x = quotient_group.mk' N y ↔ ∃ z ∈ N, x * z = y :=
(@quotient.eq _ (quotient_group.left_rel _) _ _).trans
  ⟨λ (h : x⁻¹ * y ∈ N), ⟨_, h, by rw [← mul_assoc, mul_right_inv, one_mul]⟩,
   λ ⟨z, z_mem, eq_y⟩,
     by { rw ← eq_y, show x⁻¹ * (x * z) ∈ N, rwa [← mul_assoc, mul_left_inv, one_mul] }⟩

lemma ideal.mem_mul_span_singleton {x y : R} {I : ideal R} :
  x ∈ I * ideal.span {y} ↔ ∃ z ∈ I, z * y = x :=
submodule.mem_smul_span_singleton

lemma ideal.mem_span_singleton_mul {x y : R} {I : ideal R} :
  x ∈ ideal.span {y} * I ↔ ∃ z ∈ I, y * z = x :=
by simp only [mul_comm, ideal.mem_mul_span_singleton]

lemma ideal.le_span_singleton_mul_iff {x : R} {I J : ideal R} :
  I ≤ ideal.span {x} * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI :=
show (∀ {zI} (hzI : zI ∈ I), zI ∈ ideal.span {x} * J) ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI,
by simp only [ideal.mem_span_singleton_mul]

lemma ideal.span_singleton_mul_le_iff {x : R} {I J : ideal R} :
  ideal.span {x} * I ≤ J ↔ ∀ z ∈ I, x * z ∈ J :=
begin
  simp only [ideal.mul_le, ideal.mem_span_singleton_mul, ideal.mem_span_singleton],
  split,
  { intros h zI hzI,
    exact h x (dvd_refl x) zI hzI },
  { rintros h _ ⟨z, rfl⟩ zI hzI,
    rw [mul_comm x z, mul_assoc],
    exact J.mul_mem_left (h zI hzI) },
end

lemma ideal.span_singleton_mul_le_span_singleton_mul {x y : R} {I J : ideal R} :
  ideal.span {x} * I ≤ ideal.span {y} * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zI = y * zJ :=
by simp only [ideal.span_singleton_mul_le_iff, ideal.mem_span_singleton_mul, eq_comm]

lemma ideal.eq_singleton_mul {x : R} (I J : ideal R) :
  I = ideal.span {x} * J ↔ ((∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI) ∧ (∀ z ∈ J, x * z ∈ I)) :=
by simp only [le_antisymm_iff, ideal.le_span_singleton_mul_iff, ideal.span_singleton_mul_le_iff]

lemma ideal.singleton_mul_eq_singleton_mul {x y : R} (I J : ideal R) :
  ideal.span {x} * I = ideal.span {y} * J ↔
    ((∀ zI ∈ I, ∃ zJ ∈ J, x * zI = y * zJ) ∧
     (∀ zJ ∈ J, ∃ zI ∈ I, x * zI = y * zJ)) :=
by simp only [le_antisymm_iff, ideal.span_singleton_mul_le_span_singleton_mul, eq_comm]

lemma fractional_ideal.le_span_singleton_mul_iff {x : f.codomain} {I J : fractional_ideal f} :
  I ≤ span_singleton x * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI :=
show (∀ {zI} (hzI : zI ∈ I), zI ∈ span_singleton x * J) ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI,
by { simp only [fractional_ideal.mem_singleton_mul, eq_comm], refl }

lemma fractional_ideal.span_singleton_mul_le_iff {x : f.codomain} {I J : fractional_ideal f} :
  span_singleton x * I ≤ J ↔ ∀ z ∈ I, x * z ∈ J :=
begin
  simp only [fractional_ideal.mul_le, fractional_ideal.mem_singleton_mul,
             fractional_ideal.mem_span_singleton],
  split,
  { intros h zI hzI,
    exact h x ⟨1, one_smul _ _⟩ zI hzI },
  { rintros h _ ⟨z, rfl⟩ zI hzI,
    rw [algebra.smul_mul_assoc],
    exact submodule.smul_mem J.1 _ (h zI hzI) },
end

lemma fractional_ideal.eq_span_singleton_mul {x : f.codomain} {I J : fractional_ideal f} :
  I = span_singleton x * J ↔ (∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI) ∧ ∀ z ∈ J, x * z ∈ I :=
by simp only [le_antisymm_iff, fractional_ideal.le_span_singleton_mul_iff,
              fractional_ideal.span_singleton_mul_le_iff]

lemma class_group.mk_eq_mk_iff [is_dedekind_domain R]
  (I J : nonzero_ideal R) :
  class_group.mk f I = class_group.mk f J ↔
    ∃ (x y : R) (hx : x ≠ 0) (hy : y ≠ 0), ideal.span {x} * (I : ideal R) = ideal.span {y} * J :=
begin
  simp only [class_group.mk, monoid_hom.comp_apply, monoid_hom.coe_mk, quotient_group.mk'_eq_mk',
    exists_prop, monoid_hom.mem_range, ideal.singleton_mul_eq_singleton_mul],
  split,
  { rintros ⟨z, ⟨xy, hxy, rfl⟩, eq_J⟩,
    have hx : (f.to_localization_map.sec (xy : f.codomain)).1 ≠ 0,
    { suffices : f.to_map (f.to_localization_map.sec (xy : f.codomain)).1 ≠ 0,
      { refine mt (λ h, _) this,
        rw [h, ring_hom.map_zero] },
      rw [ne.def, ← localization_map.sec_spec (xy : f.codomain), mul_eq_zero],
      push_neg,
      use xy.ne_zero,
      exact f.to_map_ne_zero_of_mem_non_zero_divisors _ },
    use [(f.to_localization_map.sec (xy : f.codomain)).1,
         (f.to_localization_map.sec (xy : f.codomain)).2,
         hx,
         ne_zero_of_mem_non_zero_divisors (f.to_localization_map.sec (xy : f.codomain)).2.2],
    apply fractional_ideal.coe_to_fractional_ideal_injective (le_refl (non_zero_divisors R)),
    rw [fractional_ideal.coe_to_fractional_ideal_mul (ideal.span _),
        fractional_ideal.coe_to_fractional_ideal_mul (ideal.span _)],
    all_goals { sorry } },
  { rintros ⟨x, y, hx, hy, h⟩,
    refine ⟨_, ⟨units.mk0 (f.mk' x ⟨y, mem_non_zero_divisors_iff_ne_zero.mpr hy⟩) _, rfl⟩, _⟩,
    { rw [ne.def, f.mk'_eq_iff_eq_mul, zero_mul],
      exact mt (f.to_map.injective_iff.mp f.injective _) hx },
    { ext, sorry } },
end

lemma class_group.mk_surjective [is_dedekind_domain R] : function.surjective (class_group.mk f) :=
begin
  rintros ⟨I⟩,
  obtain ⟨a, a_ne_zero, ha⟩ := I.1.2,
  refine ⟨⟨{ carrier := { x | f.to_map (a * x) ∈ I.1 }, .. }, _⟩, _⟩,
  { simp only [ring_hom.map_zero, set.mem_set_of_eq, mul_zero, ring_hom.map_mul],
    exact submodule.zero_mem I },
  { simp only [ring_hom.map_add, set.mem_set_of_eq, mul_zero, ring_hom.map_mul, mul_add],
    exact λ _ _ ha hb, submodule.add_mem I ha hb },
  { simp only [smul_eq_mul, set.mem_set_of_eq, mul_zero, ring_hom.map_mul, mul_add,
               mul_left_comm (f.to_map a)],
    exact λ c _ hb, submodule.smul_mem I c hb },
  { apply (submodule.ne_bot_iff _).mpr,
    obtain ⟨x, x_ne, x_mem⟩ := exists_ne_zero_mem_is_integer I.ne_zero,
    refine ⟨x, show f.to_map (a * x) ∈ I.1, from _, x_ne⟩,
    rw [ring_hom.map_mul, ← f.algebra_map_eq, ← algebra.smul_def a (algebra_map _ f.codomain x)],
    exact submodule.smul_mem _ _ x_mem },
  { symmetry,
    apply quotient.sound,
    refine ⟨units.mk0 (f.to_map a) (f.to_map_ne_zero_of_mem_non_zero_divisors ⟨a, a_ne_zero⟩), _⟩,
    apply @mul_left_cancel _ _ I,
    rw [← mul_assoc, mul_right_inv, one_mul],
    ext x,
    simp [localization_map.coe_submodule],
    sorry }
end

variables {K' : Type*} [field K'] (f) (f' : fraction_map R K')

lemma monoid_hom.range_eq_top {G H : Type*} [group G] [group H] (f : G →* H) :
  f.range = ⊤ ↔ function.surjective f :=
⟨ λ h y, show y ∈ f.range, from h.symm ▸ subgroup.mem_top y,
  λ h, subgroup.ext (λ x, by simp [h x]) ⟩
end

end integral_domain

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [is_dedekind_domain R]
variables [field K] [field L] [decidable_eq L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L] [is_separable f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]
variables (abs : euclidean_absolute_value R ℤ)

-- Lemma 5.1
lemma exists_min (I : nonzero_ideal (integral_closure R L)) :
  ∃ b ∈ I.1, b ≠ 0 ∧ ∀ c ∈ I.1, abs_norm f abs c < abs_norm f abs b → c = 0 :=
begin
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ :=
    @int.exists_least_of_bdd (λ a, ∃ b ∈ I.1, b ≠ 0 ∧ abs_norm f abs b = a) _ _,
  { use [b, b_mem, b_ne_zero],
    intros c hc lt,
    by_contra c_ne_zero,
    exact not_le_of_gt lt (min _ ⟨c, hc, c_ne_zero, rfl⟩) },
  { use 0,
    rintros _ ⟨b, b_mem, b_ne_zero, rfl⟩,
    apply abs.nonneg },
  { obtain ⟨b, b_mem, b_ne_zero⟩ := I.1.ne_bot_iff.mp I.2,
    exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩ }
end

lemma is_scalar_tower.algebra_map_injective {R S T : Type*}
  [comm_semiring R] [comm_semiring S] [comm_semiring T]
  [algebra R S] [algebra S T] [algebra R T]
  [is_scalar_tower R S T]
  (hRS : function.injective (algebra_map R S)) (hST : function.injective (algebra_map S T)) :
  function.injective (algebra_map R T) :=
by { rw is_scalar_tower.algebra_map_eq R S T, exact hST.comp hRS }

lemma subalgebra.algebra_map_injective {R S : Type*} [comm_semiring R] [comm_semiring S]
  [algebra R S] (A : subalgebra R S) (h : function.injective (algebra_map R S)) :
  function.injective (algebra_map R A) :=
begin
  intros x y hxy,
  apply h,
  simp only [is_scalar_tower.algebra_map_apply R A S],
  exact congr_arg (coe : A → S) hxy
end

lemma integral_closure.algebra_map_injective :
  function.injective (algebra_map R (integral_closure R L)) :=
(subalgebra.algebra_map_injective _
  (is_scalar_tower.algebra_map_injective
    (show function.injective (algebra_map R f.codomain), from f.injective)
    (algebra_map f.codomain L).injective))

lemma cancel_monoid_with_zero.dvd_of_mul_dvd_mul_left {G₀ : Type*} [cancel_monoid_with_zero G₀]
  {a b c : G₀} (ha : a ≠ 0) (h : a * b ∣ a * c) :
  b ∣ c :=
begin
  obtain ⟨d, hd⟩ := h,
  refine ⟨d, mul_left_cancel' ha _⟩,
  rwa mul_assoc at hd
end

lemma ideal.dvd_of_mul_dvd_mul_left {R : Type*} [integral_domain R] [is_dedekind_domain R]
  {I J K : ideal R} (hI : I ≠ ⊥)
  (h : I * J ∣ I * K) :
  J ∣ K :=
cancel_monoid_with_zero.dvd_of_mul_dvd_mul_left hI h

lemma ideal.span_singleton_ne_bot {R : Type*} [comm_ring R] {a : R} (ha : a ≠ 0) :
  ideal.span ({a} : set R) ≠ ⊥ :=
begin
  rw [ne.def, ideal.span_eq_bot],
  push_neg,
  exact ⟨a, set.mem_singleton a, ha⟩
end

lemma finset.dvd_prod {ι M : Type*} [comm_monoid M] {x : ι} {s : finset ι}
  (hx : x ∈ s) (f : ι → M) :
  f x ∣ ∏ i in s, f i :=
multiset.dvd_prod (multiset.mem_map.mpr ⟨x, hx, rfl⟩)

-- Theorem 5.2
theorem exists_mul_eq_mul (I : nonzero_ideal (integral_closure R L)) :
  ∃ (J : nonzero_ideal (integral_closure R L)),
  class_group.mk (integral_closure.fraction_map_of_finite_extension L f) I =
    class_group.mk (integral_closure.fraction_map_of_finite_extension L f) J ∧
    J.1 ∣ ideal.span {algebra_map _ _ (∏ m in finset_approx L f abs, m)} :=
begin
  set m := ∏ m in finset_approx L f abs, m with m_eq,
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min f abs I,
  suffices : ideal.span {b} ∣ ideal.span {algebra_map _ _ m} * I.1,
  { obtain ⟨J, hJ⟩ := this,
    refine ⟨⟨J, _⟩, _, _⟩,
    { sorry },
    { rw class_group.mk_eq_mk_iff,
      refine ⟨algebra_map _ _ m, b, _, b_ne_zero, hJ⟩,
      refine mt ((algebra_map R _).injective_iff.mp (integral_closure.algebra_map_injective f) _) _,
      rw finset.prod_eq_zero_iff,
      push_neg,
      intros a ha a_eq,
      rw a_eq at ha,
      exact finset_approx.zero_not_mem f abs ha },
    apply ideal.dvd_of_mul_dvd_mul_left (ideal.span_singleton_ne_bot b_ne_zero),
    rw [ideal.dvd_iff_le, ← hJ, mul_comm, m_eq],
    apply ideal.mul_mono,
    rw [ideal.span_le, set.singleton_subset_iff],
    exact b_mem },
  rw [ideal.dvd_iff_le, ideal.mul_le],
  intros r' hr' a ha,
  rw ideal.mem_span_singleton at ⊢ hr',
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' f abs a b_ne_zero,
  apply @dvd_of_mul_left_dvd _ _ q,
  rw algebra.smul_def at lt,
  rw ← sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left ha) (I.1.mul_mem_left b_mem)) lt),
  refine mul_dvd_mul_right (dvd_trans (ring_hom.map_dvd _ _) hr') _,
  exact finset.dvd_prod r_mem (λ x, x)
end

-- Theorem 5.3
instance : fintype (class_group f) :=
_

end euclidean_domain

end class_group

#lint
