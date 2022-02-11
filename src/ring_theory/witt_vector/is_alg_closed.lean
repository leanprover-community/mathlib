/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth
-/

import field_theory.is_alg_closed.basic
import field_theory.perfect_closure
import ring_theory.witt_vector.domain
import ring_theory.witt_vector.truncated
import data.mv_polynomial.supported


/-!
# "Eigenvectors" of the Frobenius map

The goal of this file is to prove `witt_vector.exists_frobenius_solution_fraction_ring`,
which says that for an algebraically closed field `k` of characteristic `p` and `a, b` in the
field of fractions of Witt vectors over `k`,
there is a solution `b` to the equation `φ b * a = p ^ m * b`, where `φ` is the Frobenius map.

Most of this file builds up the equivalent theorem over `𝕎 k` directly,
moving to the field of fractions at the end.
See `witt_vector.frobenius_rotation` and its specification.

The construction proceeds by recursively defining a sequence of coefficients as solutions to a
polynomial equation in `k`. We must define these as generic polynomials using Witt vector API
(`witt_vector.witt_mul`, `witt_polynomial`) to show that they satisfy the desired equation.
-/

noncomputable theory

section move_elsewhere

section

variables (p : ℕ) [fact p.prime]

/-- A field is perfect if Frobenius is surjective -/
def perfect_ring.of_surjective (k : Type*) [field k] [char_p k p]
  (h : function.surjective $ frobenius k p) :
  perfect_ring k p :=
{ pth_root' := function.surj_inv h,
  frobenius_pth_root' := function.surj_inv_eq h,
  pth_root_frobenius' := λ x, (frobenius k p).injective $ function.surj_inv_eq h _ }

-- an algebraically closed field is perfect, many google hits, maybe somewhere in mathlib?
@[priority 100]
instance is_alg_closed.perfect_ring (k : Type*) [field k] [char_p k p] [is_alg_closed k] :
  perfect_ring k p :=
perfect_ring.of_surjective p k $ λ x, is_alg_closed.exists_pow_nat_eq _ $ fact.out _

end

end move_elsewhere

namespace witt_vector

variables (p : ℕ) [hp : fact p.prime]
variables {k : Type*} [field k]
include hp
local notation `𝕎` := witt_vector p

section recursive_case_poly

/-!

## The recursive case of the vector coefficients

The first coefficient of our solution vector is easy to define below.
In this section we focus on the recursive case.
The goal is to turn `witt_poly_prod n` into a univariate polynomial
whose variable represents the `n`th coefficient of `x` in `x * a`.
-/

open witt_vector finset
open_locale big_operators


section
open mv_polynomial

omit hp

/--
(∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val)*(∑ i in range n, (y.coeff i)^(p^(n-i)) * p^i.val)
-/
def witt_poly_prod (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ n) *
  rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ n)

include hp

lemma witt_poly_prod_vars (n : ℕ) :
  (witt_poly_prod p n).vars ⊆ finset.univ.product (finset.range (n + 1)) :=
begin
  rw [witt_poly_prod],
  apply subset.trans (vars_mul _ _),
  apply union_subset;
  { apply subset.trans (vars_rename _ _),
    simp [witt_polynomial_vars,image_subset_iff] }
end

private lemma sum_ident_1 (n : ℕ) :
  (∑ i in range (n+1), p^i * (witt_mul p i)^(p^(n-i)) : mv_polynomial (fin 2 × ℕ) ℤ) =
    witt_poly_prod p n :=
begin
  simp only [witt_poly_prod],
  convert witt_structure_int_prop p (X (0 : fin 2) * X 1) n using 1,
  { simp only [witt_polynomial, witt_mul, int.nat_cast_eq_coe_nat],
    rw alg_hom.map_sum,
    congr' 1 with i,
    congr' 1,
    have hsupp : (finsupp.single i (p ^ (n - i))).support = {i},
    { rw finsupp.support_eq_singleton,
      simp only [and_true, finsupp.single_eq_same, eq_self_iff_true, ne.def],
      exact pow_ne_zero _ hp.out.ne_zero, },
    simp only [bind₁_monomial, hsupp, int.cast_coe_nat, prod_singleton, ring_hom.eq_int_cast,
      finsupp.single_eq_same, C_pow, mul_eq_mul_left_iff, true_or, eq_self_iff_true], },
  { simp only [map_mul, bind₁_X_right] }
end

/-- The "remainder term" of `witt_poly_prod`. See `sum_ident_2`. -/
def extra_poly (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
∑ i in range n, p^i * (witt_mul p i)^(p^(n-i))

lemma extra_poly_vars (n : ℕ) : (extra_poly p n).vars ⊆ finset.univ.product (finset.range n) :=
begin
  rw [extra_poly],
  apply subset.trans (vars_sum_subset _ _),
  rw bUnion_subset,
  intros x hx,
  apply subset.trans (vars_mul _ _),
  apply union_subset,
  { apply subset.trans (vars_pow _ _),
    have : (p : mv_polynomial (fin 2 × ℕ) ℤ) = (C (p : ℤ)),
    { simp only [int.cast_coe_nat, ring_hom.eq_int_cast] },
    rw [this, vars_C],
    apply empty_subset },
  { apply subset.trans (vars_pow _ _),
    apply subset.trans (witt_mul_vars _ _),
    apply product_subset_product (subset.refl _),
    simp only [mem_range, range_subset] at hx ⊢,
    exact hx }
end

private lemma sum_ident_2 (n : ℕ) :
  (p ^ n * witt_mul p n : mv_polynomial (fin 2 × ℕ) ℤ) + extra_poly p n = witt_poly_prod p n :=
begin
  convert sum_ident_1 p n,
  rw [sum_range_succ, add_comm, nat.sub_self, pow_zero, pow_one],
  refl
end

omit hp

/--
`diff p n` represents the remainder term from `sum_ident_3`.
`witt_poly_prod p (n+1)` will have variables up to `n+1`,
but `diff` will only have variables up to `n`.
-/
def diff (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
(∑ (x : ℕ) in
     range (n + 1),
     (rename (prod.mk 0)) ((monomial (finsupp.single x (p ^ (n + 1 - x)))) (↑p ^ x))) *
  ∑ (x : ℕ) in
    range (n + 1),
    (rename (prod.mk 1)) ((monomial (finsupp.single x (p ^ (n + 1 - x)))) (↑p ^ x))

private lemma sum_ident_3 (n : ℕ) :
  witt_poly_prod p (n+1) =
  - (p^(n+1) * X (0, n+1)) * (p^(n+1) * X (1, n+1)) +
  (p^(n+1) * X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ (n + 1)) +
  (p^(n+1) * X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ (n + 1)) +
  diff p n :=
begin
  -- a useful auxiliary fact
  have mvpz : (p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) = mv_polynomial.C (↑p ^ (n + 1)),
  { simp only [int.cast_coe_nat, ring_hom.eq_int_cast, C_pow, eq_self_iff_true] },

  -- unfold definitions and peel off the last entries of the sums.
  rw [witt_poly_prod, witt_polynomial, alg_hom.map_sum, alg_hom.map_sum,
      sum_range_succ],
  -- these are sums up to `n+2`, so be careful to only unfold to `n+1`.
  conv_lhs {congr, skip, rw [sum_range_succ] },
  simp only [add_mul, mul_add, tsub_self, int.nat_cast_eq_coe_nat, pow_zero, alg_hom.map_sum],

  -- rearrange so that the first summand on rhs and lhs is `diff`, and peel off
  conv_rhs { rw add_comm },
  simp only [add_assoc],
  apply congr_arg (has_add.add _),
  conv_rhs { rw sum_range_succ },

  -- the rest is equal with proper unfolding and `ring`
  simp only [rename_monomial, monomial_eq_C_mul_X, map_mul, rename_C, pow_one, rename_X, mvpz],
  simp only [int.cast_coe_nat, map_pow, ring_hom.eq_int_cast, rename_X, pow_one, tsub_self,
    pow_zero],
  ring,
end

include hp

lemma diff_vars (n : ℕ) : (diff p n).vars ⊆ univ.product (range (n+1)) :=
begin
  rw [diff],
  apply subset.trans (vars_mul _ _),
  apply union_subset;
  { apply subset.trans (vars_sum_subset _ _),
    rw bUnion_subset,
    intros x hx,
    rw [rename_monomial, vars_monomial, finsupp.map_domain_single],
    { apply subset.trans (finsupp.support_single_subset),
      simp [hx], },
    { apply pow_ne_zero,
      exact_mod_cast hp.out.ne_zero } }
end

private lemma sum_ident_4 (n : ℕ) :
  (p ^ (n + 1) * witt_mul p (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) =
  - (p^(n+1) * X (0, n+1)) * (p^(n+1) * X (1, n+1)) +
  (p^(n+1) * X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ (n + 1)) +
  (p^(n+1) * X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ (n + 1)) +
  (diff p n - extra_poly p (n + 1)) :=
begin
  rw [← add_sub_assoc, eq_sub_iff_add_eq, sum_ident_2],
  exact sum_ident_3 _ _
end

/-- This is the polynomial whose dimension we want to get a handle on. Appears in `sum_ident_4`. -/
def poly_of_interest (n : ℕ) : mv_polynomial (fin 2 × ℕ) ℤ :=
witt_mul p (n + 1) + p^(n+1) * X (0, n+1) * X (1, n+1) -
  (X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ (n + 1)) -
  (X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ (n + 1))

private lemma sum_ident_5 (n : ℕ) :
  (p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) *
    poly_of_interest p n =
  (diff p n - extra_poly p (n + 1)) :=
begin
  simp only [poly_of_interest, mul_sub, mul_add, sub_eq_iff_eq_add'],
  rw sum_ident_4 p n,
  ring,
end

lemma prod_vars_subset (n : ℕ) :
  ((p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) * poly_of_interest p n).vars ⊆
  univ.product (range (n+1)) :=
begin
  rw sum_ident_5,
  apply subset.trans (vars_sub_subset _ _),
  apply union_subset,
  { apply diff_vars },
  { apply extra_poly_vars }
end

lemma poly_of_interest_vars_eq (n : ℕ) :
  (poly_of_interest p n).vars =
    ((p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) * (witt_mul p (n + 1) +
    p^(n+1) * X (0, n+1) * X (1, n+1) -
    (X (0, n+1)) * rename (prod.mk (1 : fin 2)) (witt_polynomial p ℤ (n + 1)) -
    (X (1, n+1)) * rename (prod.mk (0 : fin 2)) (witt_polynomial p ℤ (n + 1)))).vars :=
begin
  have : (p ^ (n + 1) : mv_polynomial (fin 2 × ℕ) ℤ) = C (p ^ (n + 1) : ℤ),
  { simp only [int.cast_coe_nat, ring_hom.eq_int_cast, C_pow, eq_self_iff_true] },
  rw [poly_of_interest, this, vars_C_mul],
  apply pow_ne_zero,
  exact_mod_cast hp.out.ne_zero
end

lemma poly_of_interest_vars (n : ℕ) : (poly_of_interest p n).vars ⊆ univ.product (range (n+1)) :=
by rw poly_of_interest_vars_eq; apply prod_vars_subset

lemma peval_poly_of_interest (n : ℕ) (x y : 𝕎 k) :
  peval (poly_of_interest p n) ![λ i, x.coeff i, λ i, y.coeff i] =
  (x * y).coeff (n + 1) + p^(n+1) * x.coeff (n+1) * y.coeff (n+1)
    - y.coeff (n+1) * ∑ i in range (n+1+1), p^i * x.coeff i ^ (p^(n+1-i))
    - x.coeff (n+1) * ∑ i in range (n+1+1), p^i * y.coeff i ^ (p^(n+1-i)) :=
begin
  simp only [poly_of_interest, peval, map_nat_cast, matrix.head_cons, map_pow,
    function.uncurry_apply_pair, aeval_X,
  matrix.cons_val_one, map_mul, matrix.cons_val_zero, map_sub],
  rw [sub_sub, add_comm (_ * _), ← sub_sub],
  have mvpz : (p : mv_polynomial ℕ ℤ) = mv_polynomial.C ↑p,
  { rw [ring_hom.eq_int_cast, int.cast_coe_nat] },
  congr' 3,
  { simp only [mul_coeff, peval, map_nat_cast, map_add, matrix.head_cons, map_pow,
      function.uncurry_apply_pair, aeval_X, matrix.cons_val_one, map_mul, matrix.cons_val_zero], },
  all_goals
  { simp only [witt_polynomial_eq_sum_C_mul_X_pow, aeval, eval₂_rename, int.cast_coe_nat,
      ring_hom.eq_int_cast, eval₂_mul, function.uncurry_apply_pair, function.comp_app, eval₂_sum,
      eval₂_X, matrix.cons_val_zero, eval₂_pow, int.cast_pow, ring_hom.to_fun_eq_coe, coe_eval₂_hom,
      int.nat_cast_eq_coe_nat, alg_hom.coe_mk],
  congr' 1 with z,
  rw [mvpz, mv_polynomial.eval₂_C],
  refl }
end

/- characteristic `p` version -/
lemma peval_poly_of_interest' [char_p k p] (n : ℕ) (x y : 𝕎 k) :
  peval (poly_of_interest p n) ![λ i, x.coeff i, λ i, y.coeff i] =
  (x * y).coeff (n + 1) - y.coeff (n+1) * x.coeff 0 ^ (p^(n+1))
    - x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) :=
begin
  rw peval_poly_of_interest,
  have : (p : k) = 0 := char_p.cast_eq_zero (k) p,
  simp only [this, add_zero, zero_mul, nat.succ_ne_zero, ne.def, not_false_iff, zero_pow'],
  congr; -- same proof both times, factor it out
  { rw finset.sum_eq_single_of_mem 0,
    { simp },
    { simp },
    { intros j _ hj,
      simp [zero_pow (zero_lt_iff.mpr hj)] } },
end

omit hp

lemma restrict_to_vars {σ : Type*} {s : set σ} (R : Type*) [comm_ring R] {F : mv_polynomial σ ℤ}
  (hF : ↑F.vars ⊆ s) :
  ∃ f : (s → R) → R, ∀ x : σ → R, f (x ∘ coe : s → R) = aeval x F :=
begin
  classical,
  rw [← mem_supported, supported_eq_range_rename, alg_hom.mem_range] at hF,
  cases hF with F' hF',
  use λ z, aeval z F',
  intro x,
  simp only [←hF', aeval_rename],
end

include hp

variable [char_p k p]

lemma nth_mul_coeff' (n : ℕ) :
  ∃ f : (truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k),
  ∀ (x y : 𝕎 k),
  f (truncate_fun (n+1) x) (truncate_fun (n+1) y)
  = (x * y).coeff (n+1) - y.coeff (n+1) * x.coeff 0 ^ (p^(n+1))
    - x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) :=
begin
  simp only [←peval_poly_of_interest'],
  obtain ⟨f₀, hf₀⟩ := restrict_to_vars k (poly_of_interest_vars p n),
  let f : truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k,
  { intros x y,
    apply f₀,
    rintros ⟨a, ha⟩,
    apply function.uncurry (![x, y]),
    simp only [true_and, multiset.mem_cons, range_coe, product_val, multiset.mem_range,
       multiset.mem_product, multiset.range_succ, mem_univ_val] at ha,
    refine ⟨a.fst, ⟨a.snd, _⟩⟩,
    cases ha with ha ha; linarith only [ha] },
  use f,
  intros x y,
  dsimp [peval],
  rw ← hf₀,
  simp only [f, function.uncurry_apply_pair],
  congr,
  ext a,
  cases a with a ha,
  cases a with i m,
  simp only [true_and, multiset.mem_cons, range_coe, product_val, multiset.mem_range,
    multiset.mem_product, multiset.range_succ, mem_univ_val] at ha,
  have ha' : m < n + 1 := by cases ha with ha ha; linarith only [ha],
  fin_cases i;  -- surely this case split is not necessary
  { simpa only using x.coeff_truncate_fun ⟨m, ha'⟩ }
end

end

variable [char_p k p]

lemma nth_mul_coeff (n : ℕ) :
  ∃ f : (truncated_witt_vector p (n+1) k → truncated_witt_vector p (n+1) k → k), ∀ (x y : 𝕎 k),
    (x * y).coeff (n+1) =
      x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) + y.coeff (n+1) * x.coeff 0 ^ (p^(n+1)) +
      f (truncate_fun (n+1) x) (truncate_fun (n+1) y) :=
begin
  obtain ⟨f, hf⟩ := nth_mul_coeff' p n,
  { use f,
    intros x y,
    rw hf x y,
    ring },
  all_goals { apply_instance },
end

/--
Produces the "remainder function" of the `n+1`st coefficient, which does not depend on the `n+1`st
coefficients of the inputs. -/
def nth_remainder (n : ℕ) : (fin (n+1) → k) → (fin (n+1) → k) → k :=
classical.some (nth_mul_coeff p n)

lemma nth_remainder_spec (n : ℕ) (x y : 𝕎 k) :
  (x * y).coeff (n+1) =
    x.coeff (n+1) * y.coeff 0 ^ (p^(n+1)) + y.coeff (n+1) * x.coeff 0 ^ (p^(n+1)) +
    nth_remainder p n (truncate_fun (n+1) x) (truncate_fun (n+1) y) :=
classical.some_spec (nth_mul_coeff p n) _ _


open polynomial

/-- The root of this polynomial determines the `n+1`st coefficient of our solution. -/
def succ_nth_defining_poly (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k) : polynomial k :=
X^p * C (a₁.coeff 0 ^ (p^(n+1))) - X * C (a₂.coeff 0 ^ (p^(n+1)))
  + C (a₁.coeff (n+1) * ((bs 0)^p)^(p^(n+1)) +
      nth_remainder p n (λ v, (bs v)^p) (truncate_fun (n+1) a₁) -
      a₂.coeff (n+1) * (bs 0)^p^(n+1) - nth_remainder p n bs (truncate_fun (n+1) a₂))

lemma succ_nth_defining_poly_degree (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_defining_poly p n a₁ a₂ bs).degree = p :=
begin
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n+1))).degree = p,
  { rw [degree_mul, degree_C],
    { simp only [nat.cast_with_bot, add_zero, degree_X, degree_pow, nat.smul_one_eq_coe] },
    { exact pow_ne_zero _ ha₁ } },
  have : (X ^ p * C (a₁.coeff 0 ^ p ^ (n+1)) - X * C (a₂.coeff 0 ^ p ^ (n+1))).degree = p,
  { rw [degree_sub_eq_left_of_degree_lt, this],
    rw [this, degree_mul, degree_C, degree_X, add_zero],
    { exact_mod_cast hp.out.one_lt },
    { exact pow_ne_zero _ ha₂ } },
  rw [succ_nth_defining_poly, degree_add_eq_left_of_degree_lt, this],
  apply lt_of_le_of_lt (degree_C_le),
  rw [this],
  exact_mod_cast hp.out.pos
end

variable [is_alg_closed k]

lemma root_exists (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  ∃ b : k, (succ_nth_defining_poly p n a₁ a₂ bs).is_root b :=
is_alg_closed.exists_root _ $
  by simp [(succ_nth_defining_poly_degree p n a₁ a₂ bs ha₁ ha₂), hp.out.ne_zero]

/-- This is the `n+1`st coefficient of our solution, projected from `root_exists`. -/
def succ_nth_val (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : k :=
classical.some (root_exists p n a₁ a₂ bs ha₁ ha₂)

lemma succ_nth_val_spec (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_defining_poly p n a₁ a₂ bs).is_root (succ_nth_val p n a₁ a₂ bs ha₁ ha₂) :=
classical.some_spec (root_exists p n a₁ a₂ bs ha₁ ha₂)

lemma succ_nth_val_spec' (n : ℕ) (a₁ a₂ : 𝕎 k) (bs : fin (n+1) → k)
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  (succ_nth_val p n a₁ a₂ bs ha₁ ha₂)^p * a₁.coeff 0 ^ (p^(n+1)) +
    a₁.coeff (n+1) * ((bs 0)^p)^(p^(n+1)) +
    nth_remainder p n (λ v, (bs v)^p) (truncate_fun (n+1) a₁)
   = (succ_nth_val p n a₁ a₂ bs ha₁ ha₂) * a₂.coeff 0 ^ (p^(n+1)) +
     a₂.coeff (n+1) * (bs 0)^(p^(n+1)) + nth_remainder p n bs (truncate_fun (n+1) a₂) :=
begin
  rw ← sub_eq_zero,
  have := succ_nth_val_spec p n a₁ a₂ bs ha₁ ha₂,
  simp only [polynomial.map_add, polynomial.eval_X, polynomial.map_pow, polynomial.eval_C,
    polynomial.eval_pow, succ_nth_defining_poly, polynomial.eval_mul, polynomial.eval_add,
    polynomial.eval_sub, polynomial.map_mul, polynomial.map_sub, polynomial.is_root.def] at this,
  convert this using 1,
  ring
end

end recursive_case_poly

section base_case

variable [is_alg_closed k]

lemma solution_pow (a₁ a₂ : 𝕎 k) :
  ∃ x : k, x^(p-1) = a₂.coeff 0 / a₁.coeff 0 :=
is_alg_closed.exists_pow_nat_eq _ $ by linarith [hp.out.one_lt, le_of_lt hp.out.one_lt]

/-- The base case (0th coefficient) of our solution vector. -/
def solution (a₁ a₂ : 𝕎 k) : k :=
classical.some $ solution_pow p a₁ a₂

lemma solution_spec (a₁ a₂ : 𝕎 k) :
  (solution p a₁ a₂)^(p-1) = a₂.coeff 0 / a₁.coeff 0 :=
classical.some_spec $ solution_pow p a₁ a₂

lemma solution_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  solution p a₁ a₂ ≠ 0 :=
begin
  intro h,
  have := solution_spec p a₁ a₂,
  rw [h, zero_pow] at this,
  { simpa [ha₁, ha₂] using _root_.div_eq_zero_iff.mp this.symm },
  { linarith [hp.out.one_lt, le_of_lt hp.out.one_lt] }
end

lemma solution_spec' {a₁ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (a₂ : 𝕎 k) :
  (solution p a₁ a₂)^p * a₁.coeff 0 = (solution p a₁ a₂) * a₂.coeff 0 :=
begin
  have := solution_spec p a₁ a₂,
  cases nat.exists_eq_succ_of_ne_zero hp.out.ne_zero with q hq,
  have hq' : q = p - 1 := by simp only [hq, tsub_zero, nat.succ_sub_succ_eq_sub],
  conv_lhs {congr, congr, skip, rw hq},
  rw [pow_succ', hq', this],
  field_simp [ha₁, mul_comm],
end


end base_case

section frobenius_rotation

variables [is_alg_closed k] [char_p k p]

/--
Recursively defines the sequence of coefficients for `witt_vector.frobenius_rotation`.
-/
noncomputable def frobenius_rotation_coeff {a₁ a₂ : 𝕎 k}
  (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : ℕ → k
| 0       := solution p a₁ a₂
| (n + 1) := succ_nth_val p n a₁ a₂ (λ i, frobenius_rotation_coeff i.val) ha₁ ha₂
using_well_founded { dec_tac := `[apply fin.is_lt] }

/--
For nonzero `a₁` and `a₂`, `frobenius_rotation a₁ a₂` is a Witt vector that satisfies the
equation `frobenius (frobenius_rotation a₁ a₂) * a₁ = (frobenius_rotation a₁ a₂) * a₂`.
-/
def frobenius_rotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) : 𝕎 k :=
witt_vector.mk p (frobenius_rotation_coeff p ha₁ ha₂)

lemma frobenius_rotation_nonzero {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  frobenius_rotation p ha₁ ha₂ ≠ 0 :=
begin
  intro h,
  apply solution_nonzero p ha₁ ha₂,
  simpa [← h, frobenius_rotation, frobenius_rotation_coeff] using witt_vector.zero_coeff p k 0
end

lemma frobenius_frobenius_rotation {a₁ a₂ : 𝕎 k} (ha₁ : a₁.coeff 0 ≠ 0) (ha₂ : a₂.coeff 0 ≠ 0) :
  frobenius (frobenius_rotation p ha₁ ha₂) * a₁ = (frobenius_rotation p ha₁ ha₂) * a₂ :=
begin
  ext n,
  induction n with n ih,
  { simp only [witt_vector.mul_coeff_zero, witt_vector.coeff_frobenius_char_p,
      frobenius_rotation, frobenius_rotation_coeff],
    apply solution_spec' _ ha₁ },
  { simp only [nth_remainder_spec, witt_vector.coeff_frobenius_char_p, frobenius_rotation_coeff,
      frobenius_rotation, fin.val_eq_coe],
    have := succ_nth_val_spec' p n a₁ a₂
      (λ (i : fin (n + 1)), frobenius_rotation_coeff p ha₁ ha₂ i.val) ha₁ ha₂,
    simp only [frobenius_rotation_coeff, fin.val_eq_coe, fin.val_zero] at this,
    convert this using 4,
    apply truncated_witt_vector.ext,
    intro i,
    simp only [fin.val_eq_coe, witt_vector.coeff_truncate_fun, witt_vector.coeff_frobenius_char_p],
    refl }
end

lemma p_nonzero (k : Type*) [comm_ring k] [char_p k p] [nontrivial k] : (p : 𝕎 k) ≠ 0 :=
begin
  have : (p : 𝕎 k).coeff 1 = 1 := by simpa using witt_vector.coeff_p_pow 1,
  intros h,
  simpa [h] using this
end

lemma p_nonzero' (k : Type*) [comm_ring k] [char_p k p] [nontrivial k] :
  (p : fraction_ring (𝕎 k)) ≠ 0 :=
by simpa using (is_fraction_ring.injective (𝕎 k) (fraction_ring (𝕎 k))).ne (p_nonzero p k)

local notation `K` := fraction_ring (𝕎 k)

lemma frobenius_bijective (R : Type*) [comm_ring R] [char_p R p] [perfect_ring R p] :
  function.bijective (@witt_vector.frobenius p R _ _) :=
begin
  rw witt_vector.frobenius_eq_map_frobenius,
  exact ⟨witt_vector.map_injective _ (frobenius_equiv R p).injective,
    witt_vector.map_surjective _ (frobenius_equiv R p).surjective⟩,
end

/-- This is basically the same as `𝕎 k` being a DVR. -/
lemma split (a : 𝕎 k) (ha : a ≠ 0) :
  ∃ (m : ℕ) (b : 𝕎 k), b.coeff 0 ≠ 0 ∧ a = p ^ m * b :=
begin
  obtain ⟨m, c, hc, hcm⟩ := witt_vector.verschiebung_nonzero ha,
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).surjective.iterate m c,
  rw witt_vector.iterate_frobenius_coeff at hc,
  have := congr_fun (witt_vector.verschiebung_frobenius_comm.comp_iterate m) b,
  simp only [function.comp_app] at this,
  rw ← this at hcm,
  refine ⟨m, b, _, _⟩,
  { contrapose! hc,
    have : 0 < p ^ m := pow_pos (nat.prime.pos (fact.out _)) _,
    simp [hc, this] },
  { rw ← mul_left_iterate (p : 𝕎 k) m,
    convert hcm,
    ext1 x,
    rw [mul_comm, ← witt_vector.verschiebung_frobenius x] },
end

local notation `φ` := is_fraction_ring.field_equiv_of_ring_equiv
  (ring_equiv.of_bijective _ (frobenius_bijective p k))

lemma exists_frobenius_solution_fraction_ring {a : fraction_ring (𝕎 k)} (ha : a ≠ 0) :
  ∃ (b : fraction_ring (𝕎 k)) (hb : b ≠ 0) (m : ℤ), φ b * a = p ^ m * b :=
begin
  revert ha,
  refine localization.induction_on a _,
  rintros ⟨r, q, hq⟩ hrq,
  rw mem_non_zero_divisors_iff_ne_zero at hq,
  have : r ≠ 0 := λ h, hrq (by simp [h]),
  obtain ⟨m, r', hr', rfl⟩ := split p r this,
  obtain ⟨n, q', hq', rfl⟩ := split p q hq,
  let b := frobenius_rotation p hr' hq',
  refine ⟨algebra_map (𝕎 k) _ b, _, m - n, _⟩,
  { simpa only [map_zero] using
      (is_fraction_ring.injective (witt_vector p k) (fraction_ring (witt_vector p k))).ne
        (frobenius_rotation_nonzero p hr' hq')},
  have key : witt_vector.frobenius b * p ^ m * r' * p ^ n = p ^ m * b * (p ^ n * q'),
  { have H := congr_arg (λ x : 𝕎 k, x * p ^ m * p ^ n) (frobenius_frobenius_rotation p hr' hq'),
    dsimp at H,
    refine (eq.trans _ H).trans _; ring },
  have hq'' : algebra_map (𝕎 k) (fraction_ring (𝕎 k)) q' ≠ 0,
  { have hq''' : q' ≠ 0 := λ h, hq' (by simp [h]),
    simpa only [ne.def, map_zero] using
      (is_fraction_ring.injective (𝕎 k) (fraction_ring (𝕎 k))).ne hq''' },
  rw zpow_sub₀ (p_nonzero' p k),
  field_simp [p_nonzero' p k],
  simp only [is_fraction_ring.field_equiv_of_ring_equiv,
    is_localization.ring_equiv_of_ring_equiv_eq, ring_equiv.coe_of_bijective],
  convert congr_arg (λ x, algebra_map (𝕎 k) (fraction_ring (𝕎 k)) x) key using 1,
  { simp only [ring_hom.map_mul, ring_hom.map_pow, map_nat_cast],
    ring },
  { simp only [ring_hom.map_mul, ring_hom.map_pow, map_nat_cast] }
end

end frobenius_rotation

end witt_vector
