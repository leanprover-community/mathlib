/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.direct_limit
import field_theory.splitting_field

/-!
# Algebraic Closure

In this file we define the typeclass for algebraically closed fields and algebraic closures.
We also construct an algebraic closure for any field.

## Main Definitions

- `is_alg_closed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
polynomial in `k` splits.

- `is_alg_closure k K` is the typeclass saying `K` is an algebraic closure of `k`.

- `algebraic_closure k` is an algebraic closure of `k` (in the same universe).
  It is constructed by taking the polynomial ring generated by indeterminates `x_f`
  corresponding to monic irreducible polynomials `f` with coefficients in `k`, and quotienting
  out by a maximal ideal containing every `f(x_f)`, and then repeating this step countably
  many times. See Exercise 1.13 in Atiyah--Macdonald.

## TODO

Show that any algebraic extension embeds into any algebraically closed extension (via Zorn's lemma).

## Tags

algebraic closure, algebraically closed

-/

universes u v w
noncomputable theory
open_locale classical big_operators
open polynomial

variables (k : Type u) [field k]

/-- Typeclass for algebraically closed fields.

To show `polynomial.splits p f` for an arbitrary ring homomorphism `f`,
see `is_alg_closed.splits_codomain` and `is_alg_closed.splits_domain`.
-/
class is_alg_closed : Prop :=
(splits : ∀ p : polynomial k, p.splits $ ring_hom.id k)

/-- Every polynomial splits in the field extension `f : K →+* k` if `k` is algebraically closed.

See also `is_alg_closed.splits_domain` for the case where `K` is algebraically closed.
-/
theorem is_alg_closed.splits_codomain {k K : Type*} [field k] [is_alg_closed k] [field K]
  {f : K →+* k} (p : polynomial K) : p.splits f :=
by { convert is_alg_closed.splits (p.map f), simp [splits_map_iff] }

/-- Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed.

See also `is_alg_closed.splits_codomain` for the case where `k` is algebraically closed.
-/
theorem is_alg_closed.splits_domain {k K : Type*} [field k] [is_alg_closed k] [field K]
  {f : k →+* K} (p : polynomial k) : p.splits f :=
polynomial.splits_of_splits_id _ $ is_alg_closed.splits _

namespace is_alg_closed

theorem of_exists_root (H : ∀ p : polynomial k, p.monic → irreducible p → ∃ x, p.eval x = 0) :
  is_alg_closed k :=
⟨λ p, or.inr $ λ q hq hqp,
 have irreducible (q * C (leading_coeff q)⁻¹),
   by { rw ← coe_norm_unit_of_ne_zero hq.ne_zero,
        exact irreducible_of_associated associated_normalize hq },
 let ⟨x, hx⟩ := H (q * C (leading_coeff q)⁻¹) (monic_mul_leading_coeff_inv hq.ne_zero) this in
 degree_mul_leading_coeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root this hx⟩

lemma degree_eq_one_of_irreducible [is_alg_closed k] {p : polynomial k} (h_nz : p ≠ 0)
  (hp : irreducible p) :
  p.degree = 1 :=
degree_eq_one_of_irreducible_of_splits h_nz hp (is_alg_closed.splits_codomain _)

lemma algebra_map_surjective_of_is_integral {k K : Type*} [field k] [domain K]
  [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_integral k K) :
  function.surjective (algebra_map k K) :=
begin
  refine λ x, ⟨-((minpoly k x).coeff 0), _⟩,
  have hq : (minpoly k x).leading_coeff = 1 := minpoly.monic (hf x),
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k
    (minpoly.ne_zero (hf x)) (minpoly.irreducible (hf x)),
  have : (aeval x (minpoly k x)) = 0 := minpoly.aeval k x,
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul,
    aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at this,
  exact (ring_hom.map_neg (algebra_map k K) ((minpoly k x).coeff 0)).symm ▸ this.symm,
end

lemma algebra_map_surjective_of_is_integral' {k K : Type*} [field k] [integral_domain K]
  [hk : is_alg_closed k] (f : k →+* K) (hf : f.is_integral) : function.surjective f :=
@algebra_map_surjective_of_is_integral k K _ _ _ f.to_algebra hf

lemma algebra_map_surjective_of_is_algebraic {k K : Type*} [field k] [domain K]
  [hk : is_alg_closed k] [algebra k K] (hf : algebra.is_algebraic k K) :
  function.surjective (algebra_map k K) :=
algebra_map_surjective_of_is_integral ((is_algebraic_iff_is_integral' k).mp hf)

end is_alg_closed

/-- Typeclass for an extension being an algebraic closure. -/
class is_alg_closure (K : Type v) [field K] [algebra k K] : Prop :=
(alg_closed : is_alg_closed K)
(algebraic : algebra.is_algebraic k K)

theorem is_alg_closure_iff (K : Type v) [field K] [algebra k K] :
  is_alg_closure k K ↔ is_alg_closed K ∧ algebra.is_algebraic k K :=
⟨λ h, ⟨h.1, h.2⟩, λ h, ⟨h.1, h.2⟩⟩

namespace algebraic_closure

open mv_polynomial

/-- The subtype of monic irreducible polynomials -/
@[reducible] def monic_irreducible : Type u :=
{ f : polynomial k // monic f ∧ irreducible f }

/-- Sends a monic irreducible polynomial `f` to `f(x_f)` where `x_f` is a formal indeterminate. -/
def eval_X_self (f : monic_irreducible k) : mv_polynomial (monic_irreducible k) k :=
polynomial.eval₂ mv_polynomial.C (X f) f

/-- The span of `f(x_f)` across monic irreducible polynomials `f` where `x_f` is an
indeterminate. -/
def span_eval : ideal (mv_polynomial (monic_irreducible k) k) :=
ideal.span $ set.range $ eval_X_self k

/-- Given a finset of monic irreducible polynomials, construct an algebra homomorphism to the
splitting field of the product of the polynomials sending each indeterminate `x_f` represented by
the polynomial `f` in the finset to a root of `f`. -/
def to_splitting_field (s : finset (monic_irreducible k)) :
  mv_polynomial (monic_irreducible k) k →ₐ[k] splitting_field (∏ x in s, x : polynomial k) :=
mv_polynomial.aeval $ λ f,
  if hf : f ∈ s
  then root_of_splits _
    ((splits_prod_iff _ $ λ (j : monic_irreducible k) _, j.2.2.ne_zero).1
      (splitting_field.splits _) f hf)
    (mt is_unit_iff_degree_eq_zero.2 f.2.2.not_unit)
  else 37

theorem to_splitting_field_eval_X_self {s : finset (monic_irreducible k)} {f} (hf : f ∈ s) :
  to_splitting_field k s (eval_X_self k f) = 0 :=
by { rw [to_splitting_field, eval_X_self, ← alg_hom.coe_to_ring_hom, hom_eval₂,
         alg_hom.coe_to_ring_hom, mv_polynomial.aeval_X, dif_pos hf,
         ← algebra_map_eq, alg_hom.comp_algebra_map],
  exact map_root_of_splits _ _ _ }

theorem span_eval_ne_top : span_eval k ≠ ⊤ :=
begin
  rw [ideal.ne_top_iff_one, span_eval, ideal.span, ← set.image_univ, finsupp.mem_span_iff_total],
  rintros ⟨v, _, hv⟩,
  replace hv := congr_arg (to_splitting_field k v.support) hv,
  rw [alg_hom.map_one, finsupp.total_apply, finsupp.sum, alg_hom.map_sum, finset.sum_eq_zero] at hv,
  { exact zero_ne_one hv },
  intros j hj,
  rw [smul_eq_mul, alg_hom.map_mul, to_splitting_field_eval_X_self k hj, mul_zero]
end

/-- A random maximal ideal that contains `span_eval k` -/
def max_ideal : ideal (mv_polynomial (monic_irreducible k) k) :=
classical.some $ ideal.exists_le_maximal _ $ span_eval_ne_top k

instance max_ideal.is_maximal : (max_ideal k).is_maximal :=
(classical.some_spec $ ideal.exists_le_maximal _ $ span_eval_ne_top k).1

theorem le_max_ideal : span_eval k ≤ max_ideal k :=
(classical.some_spec $ ideal.exists_le_maximal _ $ span_eval_ne_top k).2

/-- The first step of constructing `algebraic_closure`: adjoin a root of all monic polynomials -/
def adjoin_monic : Type u :=
(max_ideal k).quotient

instance adjoin_monic.field : field (adjoin_monic k) :=
ideal.quotient.field _

instance adjoin_monic.inhabited : inhabited (adjoin_monic k) := ⟨37⟩

/-- The canonical ring homomorphism to `adjoin_monic k`. -/
def to_adjoin_monic : k →+* adjoin_monic k :=
(ideal.quotient.mk _).comp C

instance adjoin_monic.algebra : algebra k (adjoin_monic k) :=
(to_adjoin_monic k).to_algebra

theorem adjoin_monic.algebra_map : algebra_map k (adjoin_monic k) = (ideal.quotient.mk _).comp C :=
rfl

theorem adjoin_monic.is_integral (z : adjoin_monic k) : is_integral k z :=
let ⟨p, hp⟩ := ideal.quotient.mk_surjective z in hp ▸
mv_polynomial.induction_on p (λ x, is_integral_algebra_map) (λ p q, is_integral_add)
  (λ p f ih, @is_integral_mul _ _ _ _ _ _ (ideal.quotient.mk _ _) ih ⟨f, f.2.1,
    by { erw [adjoin_monic.algebra_map, ← hom_eval₂,
              ideal.quotient.eq_zero_iff_mem],
      exact le_max_ideal k (ideal.subset_span ⟨f, rfl⟩) }⟩)

theorem adjoin_monic.exists_root {f : polynomial k} (hfm : f.monic) (hfi : irreducible f) :
  ∃ x : adjoin_monic k, f.eval₂ (to_adjoin_monic k) x = 0 :=
⟨ideal.quotient.mk _ $ X (⟨f, hfm, hfi⟩ : monic_irreducible k),
 by { rw [to_adjoin_monic, ← hom_eval₂, ideal.quotient.eq_zero_iff_mem],
      exact le_max_ideal k (ideal.subset_span $ ⟨_, rfl⟩) }⟩

/-- The `n`th step of constructing `algebraic_closure`, together with its `field` instance. -/
def step_aux (n : ℕ) : Σ α : Type u, field α :=
nat.rec_on n ⟨k, infer_instance⟩ $ λ n ih, ⟨@adjoin_monic ih.1 ih.2, @adjoin_monic.field ih.1 ih.2⟩

/-- The `n`th step of constructing `algebraic_closure`. -/
def step (n : ℕ) : Type u :=
(step_aux k n).1

instance step.field (n : ℕ) : field (step k n) :=
(step_aux k n).2

instance step.inhabited (n) : inhabited (step k n) := ⟨37⟩

/-- The canonical inclusion to the `0`th step. -/
def to_step_zero : k →+* step k 0 :=
ring_hom.id k

/-- The canonical ring homomorphism to the next step. -/
def to_step_succ (n : ℕ) : step k n →+* step k (n + 1) :=
@to_adjoin_monic (step k n) (step.field k n)

instance step.algebra_succ (n) : algebra (step k n) (step k (n + 1)) :=
(to_step_succ k n).to_algebra

theorem to_step_succ.exists_root {n} {f : polynomial (step k n)}
  (hfm : f.monic) (hfi : irreducible f) :
  ∃ x : step k (n + 1), f.eval₂ (to_step_succ k n) x = 0 :=
@adjoin_monic.exists_root _ (step.field k n) _ hfm hfi

/-- The canonical ring homomorphism to a step with a greater index. -/
def to_step_of_le (m n : ℕ) (h : m ≤ n) : step k m →+* step k n :=
{ to_fun := nat.le_rec_on h (λ n, to_step_succ k n),
  map_one' := begin
    induction h with n h ih, { exact nat.le_rec_on_self 1 },
    rw [nat.le_rec_on_succ h, ih, ring_hom.map_one]
  end,
  map_mul' := λ x y, begin
    induction h with n h ih, { simp_rw nat.le_rec_on_self },
    simp_rw [nat.le_rec_on_succ h, ih, ring_hom.map_mul]
  end,
  map_zero' := begin
    induction h with n h ih, { exact nat.le_rec_on_self 0 },
    rw [nat.le_rec_on_succ h, ih, ring_hom.map_zero]
  end,
  map_add' := λ x y, begin
    induction h with n h ih, { simp_rw nat.le_rec_on_self },
    simp_rw [nat.le_rec_on_succ h, ih, ring_hom.map_add]
  end }

@[simp] lemma coe_to_step_of_le (m n : ℕ) (h : m ≤ n) :
  (to_step_of_le k m n h : step k m → step k n) = nat.le_rec_on h (λ n, to_step_succ k n) :=
rfl

instance step.algebra (n) : algebra k (step k n) :=
(to_step_of_le k 0 n n.zero_le).to_algebra

instance step.scalar_tower (n) : is_scalar_tower k (step k n) (step k (n + 1)) :=
is_scalar_tower.of_algebra_map_eq $ λ z,
  @nat.le_rec_on_succ (step k) 0 n n.zero_le (n + 1).zero_le (λ n, to_step_succ k n) z

theorem step.is_integral (n) : ∀ z : step k n, is_integral k z :=
nat.rec_on n (λ z, is_integral_algebra_map) $ λ n ih z,
  is_integral_trans ih _ (adjoin_monic.is_integral (step k n) z : _)

instance to_step_of_le.directed_system :
  directed_system (step k) (λ i j h, to_step_of_le k i j h) :=
⟨λ i x h, nat.le_rec_on_self x, λ i₁ i₂ i₃ h₁₂ h₂₃ x, (nat.le_rec_on_trans h₁₂ h₂₃ x).symm⟩

end algebraic_closure

/-- The canonical algebraic closure of a field, the direct limit of adding roots to the field for
each polynomial over the field. -/
def algebraic_closure : Type u :=
ring.direct_limit (algebraic_closure.step k) (λ i j h, algebraic_closure.to_step_of_le k i j h)

namespace algebraic_closure

instance : field (algebraic_closure k) :=
field.direct_limit.field _ _

instance : inhabited (algebraic_closure k) := ⟨37⟩

/-- The canonical ring embedding from the `n`th step to the algebraic closure. -/
def of_step (n : ℕ) : step k n →+* algebraic_closure k :=
ring_hom.of $ ring.direct_limit.of _ _ _

instance algebra_of_step (n) : algebra (step k n) (algebraic_closure k) :=
(of_step k n).to_algebra

theorem of_step_succ (n : ℕ) : (of_step k (n + 1)).comp (to_step_succ k n) = of_step k n :=
ring_hom.ext $ λ x, show ring.direct_limit.of (step k) (λ i j h, to_step_of_le k i j h) _ _ = _,
  by { convert ring.direct_limit.of_f n.le_succ x, ext x, exact (nat.le_rec_on_succ' x).symm }

theorem exists_of_step (z : algebraic_closure k) : ∃ n x, of_step k n x = z :=
ring.direct_limit.exists_of z

-- slow
theorem exists_root {f : polynomial (algebraic_closure k)}
  (hfm : f.monic) (hfi : irreducible f) :
  ∃ x : algebraic_closure k, f.eval x = 0 :=
begin
  have : ∃ n p, polynomial.map (of_step k n) p = f,
  { convert ring.direct_limit.polynomial.exists_of f },
  unfreezingI { obtain ⟨n, p, rfl⟩ := this },
  rw monic_map_iff at hfm,
  have := hfm.irreducible_of_irreducible_map (of_step k n) p hfi,
  obtain ⟨x, hx⟩ := to_step_succ.exists_root k hfm this,
  refine ⟨of_step k (n + 1) x, _⟩,
  rw [← of_step_succ k n, eval_map, ← hom_eval₂, hx, ring_hom.map_zero]
end

instance : is_alg_closed (algebraic_closure k) :=
is_alg_closed.of_exists_root _ $ λ f, exists_root k

instance : algebra k (algebraic_closure k) :=
(of_step k 0).to_algebra

/-- Canonical algebra embedding from the `n`th step to the algebraic closure. -/
def of_step_hom (n) : step k n →ₐ[k] algebraic_closure k :=
{ commutes' := λ x, ring.direct_limit.of_f n.zero_le x,
  .. of_step k n }

theorem is_algebraic : algebra.is_algebraic k (algebraic_closure k) :=
λ z, (is_algebraic_iff_is_integral _).2 $ let ⟨n, x, hx⟩ := exists_of_step k z in
hx ▸ is_integral_alg_hom (of_step_hom k n) (step.is_integral k n x)

instance : is_alg_closure k (algebraic_closure k) :=
⟨algebraic_closure.is_alg_closed k, is_algebraic k⟩

end algebraic_closure

/--
Every element `f` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `K`
has non-empty spectrum:
that is, there is some `c : K` so `f - c • 1` is not invertible.
-/
-- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
lemma exists_spectrum_of_is_alg_closed_of_finite_dimensional (𝕜 : Type*) [field 𝕜] [is_alg_closed 𝕜]
  {A : Type*} [nontrivial A] [ring A] [algebra 𝕜 A] [I : finite_dimensional 𝕜 A] (f : A) :
  ∃ c : 𝕜, ¬ is_unit (f - algebra_map 𝕜 A c) :=
begin
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := is_integral_of_noetherian I f,
  have nu : ¬ is_unit (aeval f p), { rw [←aeval_def] at h_eval_p, rw h_eval_p, simp, },
  rw [eq_prod_roots_of_monic_of_splits_id h_mon (is_alg_closed.splits p),
    ←multiset.prod_to_list, alg_hom.map_list_prod] at nu,
  replace nu := mt list.prod_is_unit nu,
  simp only [not_forall, exists_prop, aeval_C, multiset.mem_to_list,
    list.mem_map, aeval_X, exists_exists_and_eq_and, multiset.mem_map, alg_hom.map_sub] at nu,
  exact ⟨nu.some, nu.some_spec.2⟩,
end
