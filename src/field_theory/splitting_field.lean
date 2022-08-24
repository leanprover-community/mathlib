/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import field_theory.intermediate_field
import ring_theory.adjoin_root

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : polynomial K` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : polynomial K` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `polynomial.splits i f`: A predicate on a field homomorphism `i : K → L` and a polynomial `f`
  saying that `f` is zero or all of its irreducible factors over `L` have degree `1`.
* `polynomial.splitting_field f`: A fixed splitting field of the polynomial `f`.
* `polynomial.is_splitting_field`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.
* `lift_of_splits`: If `K` and `L` are field extensions of a field `F` and for some finite subset
  `S` of `K`, the minimal polynomial of every `x ∈ K` splits as a polynomial with coefficients in
  `L`, then `algebra.adjoin F S` embeds into `L`.
* `polynomial.is_splitting_field.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.
* `polynomial.is_splitting_field.alg_equiv`: Every splitting field of a polynomial `f` is isomorphic
  to `splitting_field f` and thus, being a splitting field is unique up to isomorphism.

-/

noncomputable theory
open_locale classical big_operators polynomial

universes u v w

variables {F : Type u} {K : Type v} {L : Type w}

namespace polynomial

variables [field K] [field L] [field F]
open polynomial

section splits

variables (i : K →+* L)

/-- A polynomial `splits` iff it is zero or all of its irreducible factors have `degree` 1. -/
def splits (f : K[X]) : Prop :=
f = 0 ∨ ∀ {g : L[X]}, irreducible g → g ∣ f.map i → degree g = 1

@[simp] lemma splits_zero : splits i (0 : K[X]) := or.inl rfl

@[simp] lemma splits_C (a : K) : splits i (C a) :=
if ha : a = 0 then ha.symm ▸ (@C_0 K _).symm ▸ splits_zero i
else
have hia : i a ≠ 0, from mt ((injective_iff_map_eq_zero i).1 i.injective _) ha,
or.inr $ λ g hg ⟨p, hp⟩, absurd hg.1 (not_not.2 (is_unit_iff_degree_eq_zero.2 $
  by have := congr_arg degree hp;
    simp [degree_C hia, @eq_comm (with_bot ℕ) 0,
      nat.with_bot.add_eq_zero_iff] at this; clear _fun_match; tauto))

lemma splits_of_degree_eq_one {f : K[X]} (hf : degree f = 1) : splits i f :=
or.inr $ λ g hg ⟨p, hp⟩,
  by have := congr_arg degree hp;
  simp [nat.with_bot.add_eq_one_iff, hf, @eq_comm (with_bot ℕ) 1,
    mt is_unit_iff_degree_eq_zero.2 hg.1] at this;
  clear _fun_match; tauto

lemma splits_of_degree_le_one {f : K[X]} (hf : degree f ≤ 1) : splits i f :=
begin
  cases h : degree f with n,
  { rw [degree_eq_bot.1 h]; exact splits_zero i },
  { cases n with n,
    { rw [eq_C_of_degree_le_zero (trans_rel_right (≤) h le_rfl)];
      exact splits_C _ _ },
    { have hn : n = 0,
      { rw h at hf,
        cases n, { refl }, { exact absurd hf dec_trivial } },
      exact splits_of_degree_eq_one _ (by rw [h, hn]; refl) } }
end

lemma splits_of_nat_degree_le_one {f : K[X]} (hf : nat_degree f ≤ 1) : splits i f :=
splits_of_degree_le_one i (degree_le_of_nat_degree_le hf)

lemma splits_of_nat_degree_eq_one {f : K[X]} (hf : nat_degree f = 1) : splits i f :=
splits_of_nat_degree_le_one i (le_of_eq hf)

lemma splits_mul {f g : K[X]} (hf : splits i f) (hg : splits i g) : splits i (f * g) :=
if h : f * g = 0 then by simp [h]
else or.inr $ λ p hp hpf, ((principal_ideal_ring.irreducible_iff_prime.1 hp).2.2 _ _
    (show p ∣ map i f * map i g, by convert hpf; rw polynomial.map_mul)).elim
  (hf.resolve_left (λ hf, by simpa [hf] using h) hp)
  (hg.resolve_left (λ hg, by simpa [hg] using h) hp)

lemma splits_of_splits_mul {f g : K[X]} (hfg : f * g ≠ 0) (h : splits i (f * g)) :
  splits i f ∧ splits i g :=
⟨or.inr $ λ g hgi hg, or.resolve_left h hfg hgi
   (by rw polynomial.map_mul; exact hg.trans (dvd_mul_right _ _)),
 or.inr $ λ g hgi hg, or.resolve_left h hfg hgi
   (by rw polynomial.map_mul; exact hg.trans (dvd_mul_left _ _))⟩

lemma splits_of_splits_of_dvd {f g : K[X]} (hf0 : f ≠ 0) (hf : splits i f) (hgf : g ∣ f) :
  splits i g :=
by { obtain ⟨f, rfl⟩ := hgf, exact (splits_of_splits_mul i hf0 hf).1 }

lemma splits_of_splits_gcd_left {f g : K[X]} (hf0 : f ≠ 0) (hf : splits i f) :
  splits i (euclidean_domain.gcd f g) :=
polynomial.splits_of_splits_of_dvd i hf0 hf (euclidean_domain.gcd_dvd_left f g)

lemma splits_of_splits_gcd_right {f g : K[X]} (hg0 : g ≠ 0) (hg : splits i g) :
  splits i (euclidean_domain.gcd f g) :=
polynomial.splits_of_splits_of_dvd i hg0 hg (euclidean_domain.gcd_dvd_right f g)

lemma splits_map_iff (j : L →+* F) {f : K[X]} :
  splits j (f.map i) ↔ splits (j.comp i) f :=
by simp [splits, polynomial.map_map]

theorem splits_one : splits i 1 :=
splits_C i 1

theorem splits_of_is_unit {u : K[X]} (hu : is_unit u) : u.splits i :=
splits_of_splits_of_dvd i one_ne_zero (splits_one _) $ is_unit_iff_dvd_one.1 hu

theorem splits_X_sub_C {x : K} : (X - C x).splits i :=
splits_of_degree_eq_one _ $ degree_X_sub_C x

theorem splits_X : X.splits i :=
splits_of_degree_eq_one _ $ degree_X

theorem splits_id_iff_splits {f : K[X]} :
  (f.map i).splits (ring_hom.id L) ↔ f.splits i :=
by rw [splits_map_iff, ring_hom.id_comp]

theorem splits_mul_iff {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
  (f * g).splits i ↔ f.splits i ∧ g.splits i :=
⟨splits_of_splits_mul i (mul_ne_zero hf hg), λ ⟨hfs, hgs⟩, splits_mul i hfs hgs⟩

theorem splits_prod {ι : Type u} {s : ι → K[X]} {t : finset ι} :
  (∀ j ∈ t, (s j).splits i) → (∏ x in t, s x).splits i :=
begin
  refine finset.induction_on t (λ _, splits_one i) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht, rw finset.prod_insert hat,
  exact splits_mul i ht.1 (ih ht.2)
end

lemma splits_pow {f : K[X]} (hf : f.splits i) (n : ℕ) : (f ^ n).splits i :=
begin
  rw [←finset.card_range n, ←finset.prod_const],
  exact splits_prod i (λ j hj, hf),
end

lemma splits_X_pow (n : ℕ) : (X ^ n).splits i := splits_pow i (splits_X i) n

theorem splits_prod_iff {ι : Type u} {s : ι → K[X]} {t : finset ι} :
  (∀ j ∈ t, s j ≠ 0) → ((∏ x in t, s x).splits i ↔ ∀ j ∈ t, (s j).splits i) :=
begin
  refine finset.induction_on t (λ _, ⟨λ _ _ h, h.elim, λ _, splits_one i⟩) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht ⊢,
  rw [finset.prod_insert hat, splits_mul_iff i ht.1 (finset.prod_ne_zero_iff.2 ht.2), ih ht.2]
end

lemma degree_eq_one_of_irreducible_of_splits {p : L[X]}
  (hp : irreducible p) (hp_splits : splits (ring_hom.id L) p) :
  p.degree = 1 :=
begin
  by_cases h_nz : p = 0,
  { exfalso, simp * at *, },
  rcases hp_splits,
  { contradiction },
  { apply hp_splits hp, simp }
end

lemma exists_root_of_splits {f : K[X]} (hs : splits i f) (hf0 : degree f ≠ 0) :
  ∃ x, eval₂ i x f = 0 :=
if hf0 : f = 0 then by simp [hf0]
else
  let ⟨g, hg⟩ := wf_dvd_monoid.exists_irreducible_factor
    (show ¬ is_unit (f.map i), from mt is_unit_iff_degree_eq_zero.1 (by rwa degree_map))
    (map_ne_zero hf0) in
  let ⟨x, hx⟩ := exists_root_of_degree_eq_one (hs.resolve_left hf0 hg.1 hg.2) in
  let ⟨i, hi⟩ := hg.2 in
  ⟨x, by rw [← eval_map, hi, eval_mul, show _ = _, from hx, zero_mul]⟩

lemma roots_ne_zero_of_splits {f : K[X]} (hs : splits i f) (hf0 : nat_degree f ≠ 0) :
  (f.map i).roots ≠ 0 :=
let ⟨x, hx⟩ := exists_root_of_splits i hs (λ h, hf0 $ nat_degree_eq_of_degree_eq_some h) in
λ h, by { rw ← eval_map at hx,
  cases h.subst ((mem_roots _).2 hx), exact map_ne_zero (λ h, (h.subst hf0) rfl) }

/-- Pick a root of a polynomial that splits. -/
def root_of_splits {f : K[X]} (hf : f.splits i) (hfd : f.degree ≠ 0) : L :=
classical.some $ exists_root_of_splits i hf hfd

theorem map_root_of_splits {f : K[X]} (hf : f.splits i) (hfd) :
  f.eval₂ i (root_of_splits i hf hfd) = 0 :=
classical.some_spec $ exists_root_of_splits i hf hfd

lemma nat_degree_eq_card_roots {p : K[X]} {i : K →+* L}
  (hsplit : splits i p) : p.nat_degree = (p.map i).roots.card :=
begin
  by_cases hp : p = 0,
  { rw [hp, nat_degree_zero, polynomial.map_zero, roots_zero, multiset.card_zero] },
  obtain ⟨q, he, hd, hr⟩ := exists_prod_multiset_X_sub_C_mul (p.map i),
  rw [← splits_id_iff_splits, ← he] at hsplit,
  have hpm : p.map i ≠ 0 := map_ne_zero hp, rw ← he at hpm,
  have hq : q ≠ 0 := λ h, hpm (by rw [h, mul_zero]),
  rw [← nat_degree_map i, ← hd, add_right_eq_self],
  by_contra,
  have := roots_ne_zero_of_splits (ring_hom.id L) (splits_of_splits_mul _ _ hsplit).2 h,
  { rw map_id at this, exact this hr },
  { exact mul_ne_zero monic_prod_multiset_X_sub_C.ne_zero hq },
end

lemma degree_eq_card_roots {p : K[X]} {i : K →+* L} (p_ne_zero : p ≠ 0)
  (hsplit : splits i p) : p.degree = (p.map i).roots.card :=
by rw [degree_eq_nat_degree p_ne_zero, nat_degree_eq_card_roots hsplit]

theorem roots_map {f : K[X]} (hf : f.splits $ ring_hom.id K) :
  (f.map i).roots = f.roots.map i :=
(roots_map_of_injective_card_eq_total_degree i.injective $
  by { convert (nat_degree_eq_card_roots hf).symm, rw map_id }).symm

lemma image_root_set [algebra F K] [algebra F L] {p : F[X]} (h : p.splits (algebra_map F K))
  (f : K →ₐ[F] L) : f '' p.root_set K = p.root_set L :=
begin
  classical,
  rw [root_set, ←finset.coe_image, ←multiset.to_finset_map, ←f.coe_to_ring_hom, ←roots_map ↑f
      ((splits_id_iff_splits (algebra_map F K)).mpr h), map_map, f.comp_algebra_map, ←root_set],
end

lemma adjoin_root_set_eq_range [algebra F K] [algebra F L] {p : F[X]}
  (h : p.splits (algebra_map F K)) (f : K →ₐ[F] L) :
  algebra.adjoin F (p.root_set L) = f.range ↔ algebra.adjoin F (p.root_set K) = ⊤ :=
begin
  rw [←image_root_set h f, algebra.adjoin_image, ←algebra.map_top],
  exact (subalgebra.map_injective f.to_ring_hom.injective).eq_iff,
end

lemma eq_prod_roots_of_splits {p : K[X]} {i : K →+* L} (hsplit : splits i p) :
  p.map i = C (i p.leading_coeff) * ((p.map i).roots.map (λ a, X - C a)).prod :=
begin
  rw ← leading_coeff_map, symmetry,
  apply C_leading_coeff_mul_prod_multiset_X_sub_C,
  rw nat_degree_map, exact (nat_degree_eq_card_roots hsplit).symm,
end

lemma eq_prod_roots_of_splits_id {p : K[X]}
  (hsplit : splits (ring_hom.id K) p) :
  p = C p.leading_coeff * (p.roots.map (λ a, X - C a)).prod :=
by simpa using eq_prod_roots_of_splits hsplit

lemma eq_prod_roots_of_monic_of_splits_id {p : K[X]}
  (m : monic p) (hsplit : splits (ring_hom.id K) p) :
  p = (p.roots.map (λ a, X - C a)).prod :=
begin
  convert eq_prod_roots_of_splits_id hsplit,
  simp [m],
end

lemma eq_X_sub_C_of_splits_of_single_root {x : K} {h : K[X]} (h_splits : splits i h)
  (h_roots : (h.map i).roots = {i x}) : h = C h.leading_coeff * (X - C x) :=
begin
  apply polynomial.map_injective _ i.injective,
  rw [eq_prod_roots_of_splits h_splits, h_roots],
  simp,
end

section UFD

local attribute [instance, priority 10] principal_ideal_ring.to_unique_factorization_monoid
local infix ` ~ᵤ ` : 50 := associated

open unique_factorization_monoid associates

lemma splits_of_exists_multiset {f : K[X]} {s : multiset L}
  (hs : f.map i = C (i f.leading_coeff) * (s.map (λ a : L, X - C a)).prod) :
  splits i f :=
if hf0 : f = 0 then or.inl hf0
else or.inr $ λ p hp hdp, begin
  rw irreducible_iff_prime at hp,
  rw [hs, ← multiset.prod_to_list] at hdp,
  obtain (hd|hd) := hp.2.2 _ _ hdp,
  { refine (hp.2.1 $ is_unit_of_dvd_unit hd _).elim,
    exact is_unit_C.2 ((leading_coeff_ne_zero.2 hf0).is_unit.map i) },
  { obtain ⟨q, hq, hd⟩ := hp.dvd_prod_iff.1 hd,
    obtain ⟨a, ha, rfl⟩ := multiset.mem_map.1 (multiset.mem_to_list.1 hq),
    rw degree_eq_degree_of_associated ((hp.dvd_prime_iff_associated $ prime_X_sub_C a).1 hd),
    exact degree_X_sub_C a },
end

lemma splits_of_splits_id {f : K[X]} : splits (ring_hom.id _) f → splits i f :=
unique_factorization_monoid.induction_on_prime f (λ _, splits_zero _)
  (λ _ hu _, splits_of_degree_le_one _
    ((is_unit_iff_degree_eq_zero.1 hu).symm ▸ dec_trivial))
  (λ a p ha0 hp ih hfi, splits_mul _
    (splits_of_degree_eq_one _
      ((splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).1.resolve_left
        hp.1 hp.irreducible (by rw map_id)))
    (ih (splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).2))

end UFD

lemma splits_iff_exists_multiset {f : K[X]} : splits i f ↔
  ∃ (s : multiset L), f.map i = C (i f.leading_coeff) * (s.map (λ a : L, X - C a)).prod :=
⟨λ hf, ⟨(f.map i).roots, eq_prod_roots_of_splits hf⟩, λ ⟨s, hs⟩, splits_of_exists_multiset i hs⟩

lemma splits_comp_of_splits (j : L →+* F) {f : K[X]}
  (h : splits i f) : splits (j.comp i) f :=
begin
  change i with ((ring_hom.id _).comp i) at h,
  rw [← splits_map_iff],
  rw [← splits_map_iff i] at h,
  exact splits_of_splits_id _ h
end

/-- A polynomial splits if and only if it has as many roots as its degree. -/
lemma splits_iff_card_roots {p : K[X]} :
  splits (ring_hom.id K) p ↔ p.roots.card = p.nat_degree :=
begin
  split,
  { intro H, rw [nat_degree_eq_card_roots H, map_id] },
  { intro hroots,
    rw splits_iff_exists_multiset (ring_hom.id K),
    use p.roots,
    simp only [ring_hom.id_apply, map_id],
    exact (C_leading_coeff_mul_prod_multiset_X_sub_C hroots).symm },
end

lemma aeval_root_derivative_of_splits [algebra K L] {P : K[X]} (hmo : P.monic)
  (hP : P.splits (algebra_map K L)) {r : L} (hr : r ∈ (P.map (algebra_map K L)).roots) :
  aeval r P.derivative = (((P.map $ algebra_map K L).roots.erase r).map (λ a, r - a)).prod :=
begin
  replace hmo := hmo.map (algebra_map K L),
  replace hP := (splits_id_iff_splits (algebra_map K L)).2 hP,
  rw [aeval_def, ← eval_map, ← derivative_map],
  nth_rewrite 0 [eq_prod_roots_of_monic_of_splits_id hmo hP],
  rw [eval_multiset_prod_X_sub_C_derivative hr]
end

/-- If `P` is a monic polynomial that splits, then `coeff P 0` equals the product of the roots. -/
lemma prod_roots_eq_coeff_zero_of_monic_of_split {P : K[X]} (hmo : P.monic)
  (hP : P.splits (ring_hom.id K)) : coeff P 0 = (-1) ^ P.nat_degree * P.roots.prod :=
begin
  nth_rewrite 0 [eq_prod_roots_of_monic_of_splits_id hmo hP],
  rw [coeff_zero_eq_eval_zero, eval_multiset_prod, multiset.map_map],
  simp_rw [function.comp_app, eval_sub, eval_X, zero_sub, eval_C],
  conv_lhs { congr, congr, funext,
    rw [neg_eq_neg_one_mul] },
  rw [multiset.prod_map_mul, multiset.map_const, multiset.prod_repeat, multiset.map_id',
    splits_iff_card_roots.1 hP]
end

/-- If `P` is a monic polynomial that splits, then `P.next_coeff` equals the sum of the roots. -/
lemma sum_roots_eq_next_coeff_of_monic_of_split {P : K[X]} (hmo : P.monic)
  (hP : P.splits (ring_hom.id K)) : P.next_coeff = - P.roots.sum :=
begin
  nth_rewrite 0 [eq_prod_roots_of_monic_of_splits_id hmo hP],
  rw [monic.next_coeff_multiset_prod _ _ (λ a ha, _)],
  { simp_rw [next_coeff_X_sub_C, multiset.sum_map_neg'] },
  { exact monic_X_sub_C a }
end

end splits

end polynomial

section embeddings

variables (F) [field F]

/-- If `p` is the minimal polynomial of `a` over `F` then `F[a] ≃ₐ[F] F[x]/(p)` -/
def alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly
  {R : Type*} [comm_ring R] [algebra F R] (x : R) :
  algebra.adjoin F ({x} : set R) ≃ₐ[F] adjoin_root (minpoly F x) :=
alg_equiv.symm $ alg_equiv.of_bijective
  (alg_hom.cod_restrict
    (adjoin_root.lift_hom _ x $ minpoly.aeval F x) _
    (λ p, adjoin_root.induction_on _ p $ λ p,
      (algebra.adjoin_singleton_eq_range_aeval F x).symm ▸
        (polynomial.aeval _).mem_range.mpr ⟨p, rfl⟩))
  ⟨(alg_hom.injective_cod_restrict _ _ _).2 $ (injective_iff_map_eq_zero _).2 $ λ p,
    adjoin_root.induction_on _ p $ λ p hp, ideal.quotient.eq_zero_iff_mem.2 $
    ideal.mem_span_singleton.2 $ minpoly.dvd F x hp,
  λ y,
    let ⟨p, hp⟩ := (set_like.ext_iff.1
      (algebra.adjoin_singleton_eq_range_aeval F x) (y : R)).1 y.2 in
    ⟨adjoin_root.mk _ p, subtype.eq hp⟩⟩

open finset

/-- If a `subalgebra` is finite_dimensional as a submodule then it is `finite_dimensional`. -/
lemma finite_dimensional.of_subalgebra_to_submodule
  {K V : Type*} [field K] [ring V] [algebra K V] {s : subalgebra K V}
  (h : finite_dimensional K s.to_submodule) : finite_dimensional K s := h

/-- If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`. -/
theorem lift_of_splits {F K L : Type*} [field F] [field K] [field L]
  [algebra F K] [algebra F L] (s : finset K) :
  (∀ x ∈ s, is_integral F x ∧ polynomial.splits (algebra_map F L) (minpoly F x)) →
  nonempty (algebra.adjoin F (↑s : set K) →ₐ[F] L) :=
begin
  refine finset.induction_on s (λ H, _) (λ a s has ih H, _),
  { rw [coe_empty, algebra.adjoin_empty],
    exact ⟨(algebra.of_id F L).comp (algebra.bot_equiv F K)⟩ },
  rw forall_mem_insert at H, rcases H with ⟨⟨H1, H2⟩, H3⟩, cases ih H3 with f,
  choose H3 H4 using H3,
  rw [coe_insert, set.insert_eq, set.union_comm, algebra.adjoin_union_eq_adjoin_adjoin],
  letI := (f : algebra.adjoin F (↑s : set K) →+* L).to_algebra,
  haveI : finite_dimensional F (algebra.adjoin F (↑s : set K)) := (
    (submodule.fg_iff_finite_dimensional _).1
      (fg_adjoin_of_finite s.finite_to_set H3)).of_subalgebra_to_submodule,
  letI := field_of_finite_dimensional F (algebra.adjoin F (↑s : set K)),
  have H5 : is_integral (algebra.adjoin F (↑s : set K)) a := is_integral_of_is_scalar_tower a H1,
  have H6 : (minpoly (algebra.adjoin F (↑s : set K)) a).splits
    (algebra_map (algebra.adjoin F (↑s : set K)) L),
  { refine polynomial.splits_of_splits_of_dvd _
      (polynomial.map_ne_zero $ minpoly.ne_zero H1 :
        polynomial.map (algebra_map _ _) _ ≠ 0)
      ((polynomial.splits_map_iff _ _).2 _)
      (minpoly.dvd _ _ _),
    { rw ← is_scalar_tower.algebra_map_eq, exact H2 },
    { rw [← is_scalar_tower.aeval_apply, minpoly.aeval] } },
  obtain ⟨y, hy⟩ := polynomial.exists_root_of_splits _ H6 (ne_of_lt (minpoly.degree_pos H5)).symm,
  refine ⟨subalgebra.of_restrict_scalars _ _ _⟩,
  refine (adjoin_root.lift_hom (minpoly (algebra.adjoin F (↑s : set K)) a) y hy).comp _,
  exact alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly (algebra.adjoin F (↑s : set K)) a
end

end embeddings


namespace polynomial

variables [field K] [field L] [field F]
open polynomial

section splitting_field

/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : K[X]) : K[X] :=
if H : ∃ g, irreducible g ∧ g ∣ f then classical.some H else X

lemma irreducible_factor (f : K[X]) : irreducible (factor f) :=
begin
  rw factor, split_ifs with H, { exact (classical.some_spec H).1 }, { exact irreducible_X }
end

/-- See note [fact non-instances]. -/
lemma fact_irreducible_factor (f : K[X]) : fact (irreducible (factor f)) :=
⟨irreducible_factor f⟩

local attribute [instance] fact_irreducible_factor

theorem factor_dvd_of_not_is_unit {f : K[X]} (hf1 : ¬is_unit f) : factor f ∣ f :=
begin
  by_cases hf2 : f = 0, { rw hf2, exact dvd_zero _ },
  rw [factor, dif_pos (wf_dvd_monoid.exists_irreducible_factor hf1 hf2)],
  exact (classical.some_spec $ wf_dvd_monoid.exists_irreducible_factor hf1 hf2).2
end

theorem factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree ≠ 0) : factor f ∣ f :=
factor_dvd_of_not_is_unit (mt degree_eq_zero_of_is_unit hf)

theorem factor_dvd_of_nat_degree_ne_zero {f : K[X]} (hf : f.nat_degree ≠ 0) :
  factor f ∣ f :=
factor_dvd_of_degree_ne_zero (mt nat_degree_eq_of_degree_eq_some hf)

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def remove_factor (f : K[X]) : polynomial (adjoin_root $ factor f) :=
map (adjoin_root.of f.factor) f /ₘ (X - C (adjoin_root.root f.factor))

theorem X_sub_C_mul_remove_factor (f : K[X]) (hf : f.nat_degree ≠ 0) :
  (X - C (adjoin_root.root f.factor)) * f.remove_factor = map (adjoin_root.of f.factor) f :=
let ⟨g, hg⟩ := factor_dvd_of_nat_degree_ne_zero hf in
mul_div_by_monic_eq_iff_is_root.2 $ by rw [is_root.def, eval_map, hg, eval₂_mul, ← hg,
    adjoin_root.eval₂_root, zero_mul]

theorem nat_degree_remove_factor (f : K[X]) :
  f.remove_factor.nat_degree = f.nat_degree - 1 :=
by rw [remove_factor, nat_degree_div_by_monic _ (monic_X_sub_C _), nat_degree_map,
       nat_degree_X_sub_C]

theorem nat_degree_remove_factor' {f : K[X]} {n : ℕ} (hfn : f.nat_degree = n+1) :
  f.remove_factor.nat_degree = n :=
by rw [nat_degree_remove_factor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors.

Uses recursion on the degree. For better definitional behaviour, structures
including `splitting_field_aux` (such as instances) should be defined using
this recursion in each field, rather than defining the whole tuple through
recursion.
-/
def splitting_field_aux (n : ℕ) : Π {K : Type u} [field K], by exactI Π (f : K[X]), Type u :=
nat.rec_on n (λ K _ _, K) $ λ n ih K _ f, by exactI
ih f.remove_factor

namespace splitting_field_aux

theorem succ (n : ℕ) (f : K[X]) :
  splitting_field_aux (n+1) f = splitting_field_aux n f.remove_factor := rfl

instance field (n : ℕ) : Π {K : Type u} [field K], by exactI
  Π {f : K[X]}, field (splitting_field_aux n f) :=
nat.rec_on n (λ K _ _, ‹field K›) $ λ n ih K _ f, ih

instance inhabited {n : ℕ} {f : K[X]} :
  inhabited (splitting_field_aux n f) := ⟨37⟩

/-
Note that the recursive nature of this definition and `splitting_field_aux.field` creates
non-definitionally-equal diamonds in the `ℕ`- and `ℤ`- actions.
```lean
example (n : ℕ) {K : Type u} [field K] {f : K[X]} (hfn : f.nat_degree = n) :
    (add_comm_monoid.nat_module : module ℕ (splitting_field_aux n f hfn)) =
  @algebra.to_module _ _ _ _ (splitting_field_aux.algebra n _ hfn) :=
rfl  -- fails
```
It's not immediately clear whether this _can_ be fixed; the failure is much the same as the reason
that the following fails:
```lean
def cases_twice {α} (a₀ aₙ : α) : ℕ → α × α
| 0 := (a₀, a₀)
| (n + 1) := (aₙ, aₙ)

example (x : ℕ) {α} (a₀ aₙ : α) : (cases_twice a₀ aₙ x).1 = (cases_twice a₀ aₙ x).2 := rfl  -- fails
```
We don't really care at this point because this is an implementation detail (which is why this is
not a docstring), but we do in `splitting_field.algebra'` below. -/
instance algebra (n : ℕ) : Π (R : Type*) {K : Type u} [comm_semiring R] [field K],
  by exactI Π [algebra R K] {f : K[X]},
    algebra R (splitting_field_aux n f) :=
nat.rec_on n (λ R K _ _ _ _, by exactI ‹algebra R K›) $
         λ n ih R K _ _ _ f, by exactI ih R

instance is_scalar_tower (n : ℕ) : Π (R₁ R₂ : Type*) {K : Type u}
  [comm_semiring R₁] [comm_semiring R₂] [has_smul R₁ R₂] [field K],
  by exactI Π [algebra R₁ K] [algebra R₂ K],
  by exactI Π [is_scalar_tower R₁ R₂ K] {f : K[X]},
    is_scalar_tower R₁ R₂ (splitting_field_aux n f) :=
nat.rec_on n (λ R₁ R₂ K _ _ _ _ _ _ _ _, by exactI ‹is_scalar_tower R₁ R₂ K›) $
         λ n ih R₁ R₂ K _ _ _ _ _ _ _ f, by exactI ih R₁ R₂

instance algebra''' {n : ℕ} {f : K[X]} :
  algebra (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor) :=
splitting_field_aux.algebra n _

instance algebra' {n : ℕ} {f : K[X]} :
  algebra (adjoin_root f.factor) (splitting_field_aux n.succ f) :=
splitting_field_aux.algebra'''

instance algebra'' {n : ℕ} {f : K[X]} :
  algebra K (splitting_field_aux n f.remove_factor) :=
splitting_field_aux.algebra n K

instance scalar_tower' {n : ℕ} {f : K[X]} :
  is_scalar_tower K (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor) :=
begin
  -- finding this instance ourselves makes things faster
  haveI : is_scalar_tower K (adjoin_root f.factor) (adjoin_root f.factor) :=
    is_scalar_tower.right,
  exact
    splitting_field_aux.is_scalar_tower n K (adjoin_root f.factor),
end

instance scalar_tower {n : ℕ} {f : K[X]} :
  is_scalar_tower K (adjoin_root f.factor) (splitting_field_aux (n + 1) f) :=
splitting_field_aux.scalar_tower'

theorem algebra_map_succ (n : ℕ) (f : K[X]) :
  by exact algebra_map K (splitting_field_aux (n+1) f) =
    (algebra_map (adjoin_root f.factor)
        (splitting_field_aux n f.remove_factor)).comp
      (adjoin_root.of f.factor) :=
is_scalar_tower.algebra_map_eq _ _ _

protected theorem splits (n : ℕ) : ∀ {K : Type u} [field K], by exactI
  ∀ (f : K[X]) (hfn : f.nat_degree = n),
    splits (algebra_map K $ splitting_field_aux n f) f :=
nat.rec_on n (λ K _ _ hf, by exactI splits_of_degree_le_one _
  (le_trans degree_le_nat_degree $ hf.symm ▸ with_bot.coe_le_coe.2 zero_le_one)) $ λ n ih K _ f hf,
by { resetI, rw [← splits_id_iff_splits, algebra_map_succ, ← map_map, splits_id_iff_splits,
    ← X_sub_C_mul_remove_factor f (λ h, by { rw h at hf, cases hf })],
exact splits_mul _ (splits_X_sub_C _) (ih _ (nat_degree_remove_factor' hf)) }

theorem exists_lift (n : ℕ) : ∀ {K : Type u} [field K], by exactI
  ∀ (f : K[X]) (hfn : f.nat_degree = n) {L : Type*} [field L], by exactI
    ∀ (j : K →+* L) (hf : splits j f), ∃ k : splitting_field_aux n f →+* L,
      k.comp (algebra_map _ _) = j :=
nat.rec_on n (λ K _ _ _ L _ j _, by exactI ⟨j, j.comp_id⟩) $ λ n ih K _ f hf L _ j hj, by exactI
have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hf, cases hf },
have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
let ⟨r, hr⟩ := exists_root_of_splits _ (splits_of_splits_of_dvd j hfn0 hj
  (factor_dvd_of_nat_degree_ne_zero hndf))
  (mt is_unit_iff_degree_eq_zero.2 f.irreducible_factor.1) in
have hmf0 : map (adjoin_root.of f.factor) f ≠ 0, from map_ne_zero hfn0,
have hsf : splits (adjoin_root.lift j r hr) f.remove_factor,
by { rw ← X_sub_C_mul_remove_factor _ hndf at hmf0, refine (splits_of_splits_mul _ hmf0 _).2,
  rwa [X_sub_C_mul_remove_factor _ hndf, ← splits_id_iff_splits, map_map, adjoin_root.lift_comp_of,
      splits_id_iff_splits] },
let ⟨k, hk⟩ := ih f.remove_factor (nat_degree_remove_factor' hf) (adjoin_root.lift j r hr) hsf in
⟨k, by rw [algebra_map_succ, ← ring_hom.comp_assoc, hk, adjoin_root.lift_comp_of]⟩

theorem adjoin_roots (n : ℕ) : ∀ {K : Type u} [field K], by exactI
  ∀ (f : K[X]) (hfn : f.nat_degree = n),
    algebra.adjoin K (↑(f.map $ algebra_map K $ splitting_field_aux n f).roots.to_finset :
      set (splitting_field_aux n f)) = ⊤ :=
nat.rec_on n (λ K _ f hf, by exactI algebra.eq_top_iff.2 (λ x, subalgebra.range_le _ ⟨x, rfl⟩)) $
λ n ih K _ f hfn, by exactI
have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hfn, cases hfn },
have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
have hmf0 : map (algebra_map K (splitting_field_aux n.succ f)) f ≠ 0 := map_ne_zero hfn0,
by { rw [algebra_map_succ, ← map_map, ← X_sub_C_mul_remove_factor _ hndf,
         polynomial.map_mul] at hmf0 ⊢,
rw [roots_mul hmf0, polynomial.map_sub, map_X, map_C, roots_X_sub_C, multiset.to_finset_add,
    finset.coe_union, multiset.to_finset_singleton, finset.coe_singleton,
    algebra.adjoin_union_eq_adjoin_adjoin, ← set.image_singleton,
    algebra.adjoin_algebra_map K (adjoin_root f.factor)
      (splitting_field_aux n f.remove_factor),
    adjoin_root.adjoin_root_eq_top, algebra.map_top,
    is_scalar_tower.adjoin_range_to_alg_hom K (adjoin_root f.factor)
      (splitting_field_aux n f.remove_factor),
    ih _ (nat_degree_remove_factor' hfn), subalgebra.restrict_scalars_top] }

end splitting_field_aux

/-- A splitting field of a polynomial. -/
def splitting_field (f : K[X]) :=
splitting_field_aux f.nat_degree f

namespace splitting_field

variables (f : K[X])

instance : field (splitting_field f) :=
splitting_field_aux.field _

instance inhabited : inhabited (splitting_field f) := ⟨37⟩

/-- This should be an instance globally, but it creates diamonds with the `ℕ`, `ℤ`, and `ℚ` algebras
(via their `smul` and `to_fun` fields):

```lean
example :
  (algebra_nat : algebra ℕ (splitting_field f)) = splitting_field.algebra' f :=
rfl  -- fails

example :
  (algebra_int _ : algebra ℤ (splitting_field f)) = splitting_field.algebra' f :=
rfl  -- fails

example [char_zero K] [char_zero (splitting_field f)] :
  (algebra_rat : algebra ℚ (splitting_field f)) = splitting_field.algebra' f :=
rfl  -- fails
```

Until we resolve these diamonds, it's more convenient to only turn this instance on with
`local attribute [instance]` in places where the benefit of having the instance outweighs the cost.

In the meantime, the `splitting_field.algebra` instance below is immune to these particular diamonds
since `K = ℕ` and `K = ℤ` are not possible due to the `field K` assumption. Diamonds in
`algebra ℚ (splitting_field f)` instances are still possible via this instance unfortunately, but
these are less common as they require suitable `char_zero` instances to be present.
-/
instance algebra' {R} [comm_semiring R] [algebra R K] : algebra R (splitting_field f) :=
splitting_field_aux.algebra _ _

instance : algebra K (splitting_field f) :=
splitting_field_aux.algebra _ _

protected theorem splits : splits (algebra_map K (splitting_field f)) f :=
splitting_field_aux.splits _ _ rfl

variables [algebra K L] (hb : splits (algebra_map K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : splitting_field f →ₐ[K] L :=
{ commutes' := λ r, by { have := classical.some_spec (splitting_field_aux.exists_lift _ _ rfl _ hb),
    exact ring_hom.ext_iff.1 this r },
  .. classical.some (splitting_field_aux.exists_lift _ _ _ _ hb) }

theorem adjoin_roots : algebra.adjoin K
    (↑(f.map (algebra_map K $ splitting_field f)).roots.to_finset : set (splitting_field f)) = ⊤ :=
splitting_field_aux.adjoin_roots _ _ rfl

theorem adjoin_root_set : algebra.adjoin K (f.root_set f.splitting_field) = ⊤ :=
adjoin_roots f

end splitting_field

variables (K L) [algebra K L]
/-- Typeclass characterising splitting fields. -/
class is_splitting_field (f : K[X]) : Prop :=
(splits [] : splits (algebra_map K L) f)
(adjoin_roots [] : algebra.adjoin K (↑(f.map (algebra_map K L)).roots.to_finset : set L) = ⊤)

namespace is_splitting_field

variables {K}
instance splitting_field (f : K[X]) : is_splitting_field K (splitting_field f) f :=
⟨splitting_field.splits f, splitting_field.adjoin_roots f⟩

section scalar_tower

variables {K L F} [algebra F K] [algebra F L] [is_scalar_tower F K L]

variables {K}
instance map (f : F[X]) [is_splitting_field F L f] :
  is_splitting_field K L (f.map $ algebra_map F K) :=
⟨by { rw [splits_map_iff, ← is_scalar_tower.algebra_map_eq], exact splits L f },
 subalgebra.restrict_scalars_injective F $
  by { rw [map_map, ← is_scalar_tower.algebra_map_eq, subalgebra.restrict_scalars_top,
    eq_top_iff, ← adjoin_roots L f, algebra.adjoin_le_iff],
  exact λ x hx, @algebra.subset_adjoin K _ _ _ _ _ _ hx }⟩

variables {K} (L)
theorem splits_iff (f : K[X]) [is_splitting_field K L f] :
  polynomial.splits (ring_hom.id K) f ↔ (⊤ : subalgebra K L) = ⊥ :=
⟨λ h, eq_bot_iff.2 $ adjoin_roots L f ▸ (roots_map (algebra_map K L) h).symm ▸
  algebra.adjoin_le_iff.2 (λ y hy,
    let ⟨x, hxs, hxy⟩ := finset.mem_image.1 (by rwa multiset.to_finset_map at hy) in
    hxy ▸ set_like.mem_coe.2 $ subalgebra.algebra_map_mem _ _),
 λ h, @ring_equiv.to_ring_hom_refl K _ ▸
  ring_equiv.self_trans_symm (ring_equiv.of_bijective _ $ algebra.bijective_algebra_map_iff.2 h) ▸
  by { rw ring_equiv.to_ring_hom_trans, exact splits_comp_of_splits _ _ (splits L f) }⟩

theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [is_splitting_field F K f]
  [is_splitting_field K L (g.map $ algebra_map F K)] :
  is_splitting_field F L (f * g) :=
⟨(is_scalar_tower.algebra_map_eq F K L).symm ▸ splits_mul _
  (splits_comp_of_splits _ _ (splits K f))
  ((splits_map_iff _ _).1 (splits L $ g.map $ algebra_map F K)),
 by rw [polynomial.map_mul, roots_mul (mul_ne_zero (map_ne_zero hf : f.map (algebra_map F L) ≠ 0)
        (map_ne_zero hg)), multiset.to_finset_add, finset.coe_union,
      algebra.adjoin_union_eq_adjoin_adjoin,
      is_scalar_tower.algebra_map_eq F K L, ← map_map,
      roots_map (algebra_map K L) ((splits_id_iff_splits $ algebra_map F K).2 $ splits K f),
      multiset.to_finset_map, finset.coe_image, algebra.adjoin_algebra_map, adjoin_roots,
      algebra.map_top, is_scalar_tower.adjoin_range_to_alg_hom, ← map_map, adjoin_roots,
      subalgebra.restrict_scalars_top]⟩

end scalar_tower

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [algebra K F] (f : K[X]) [is_splitting_field K L f]
  (hf : polynomial.splits (algebra_map K F) f) : L →ₐ[K] F :=
if hf0 : f = 0 then (algebra.of_id K F).comp $
  (algebra.bot_equiv K L : (⊥ : subalgebra K L) →ₐ[K] K).comp $
  by { rw ← (splits_iff L f).1 (show f.splits (ring_hom.id K), from hf0.symm ▸ splits_zero _),
  exact algebra.to_top } else
alg_hom.comp (by { rw ← adjoin_roots L f, exact classical.choice (lift_of_splits _ $ λ y hy,
    have aeval y f = 0, from (eval₂_eq_eval_map _).trans $
      (mem_roots $ by exact map_ne_zero hf0).1 (multiset.mem_to_finset.mp hy),
    ⟨is_algebraic_iff_is_integral.1 ⟨f, hf0, this⟩,
      splits_of_splits_of_dvd _ hf0 hf $ minpoly.dvd _ _ this⟩) })
  algebra.to_top

theorem finite_dimensional (f : K[X]) [is_splitting_field K L f] : finite_dimensional K L :=
⟨@algebra.top_to_submodule K L _ _ _ ▸ adjoin_roots L f ▸
  fg_adjoin_of_finite (finset.finite_to_set _) (λ y hy,
  if hf : f = 0
  then by { rw [hf, polynomial.map_zero, roots_zero] at hy, cases hy }
  else is_algebraic_iff_is_integral.1 ⟨f, hf, (eval₂_eq_eval_map _).trans $
    (mem_roots $ by exact map_ne_zero hf).1 (multiset.mem_to_finset.mp hy)⟩)⟩

instance (f : K[X]) : _root_.finite_dimensional K f.splitting_field :=
finite_dimensional f.splitting_field f

/-- Any splitting field is isomorphic to `splitting_field f`. -/
def alg_equiv (f : K[X]) [is_splitting_field K L f] : L ≃ₐ[K] splitting_field f :=
begin
  refine alg_equiv.of_bijective (lift L f $ splits (splitting_field f) f)
    ⟨ring_hom.injective (lift L f $ splits (splitting_field f) f).to_ring_hom, _⟩,
  haveI := finite_dimensional (splitting_field f) f,
  haveI := finite_dimensional L f,
  have : finite_dimensional.finrank K L = finite_dimensional.finrank K (splitting_field f) :=
  le_antisymm
    (linear_map.finrank_le_finrank_of_injective
      (show function.injective (lift L f $ splits (splitting_field f) f).to_linear_map, from
        ring_hom.injective (lift L f $ splits (splitting_field f) f : L →+* f.splitting_field)))
    (linear_map.finrank_le_finrank_of_injective
      (show function.injective (lift (splitting_field f) f $ splits L f).to_linear_map, from
        ring_hom.injective (lift (splitting_field f) f $ splits L f : f.splitting_field →+* L))),
  change function.surjective (lift L f $ splits (splitting_field f) f).to_linear_map,
  refine (linear_map.injective_iff_surjective_of_finrank_eq_finrank this).1 _,
  exact ring_hom.injective (lift L f $ splits (splitting_field f) f : L →+* f.splitting_field)
end

lemma of_alg_equiv [algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [is_splitting_field K F p] :
  is_splitting_field K L p :=
begin
  split,
  { rw ← f.to_alg_hom.comp_algebra_map,
    exact splits_comp_of_splits _ _ (splits F p) },
  { rw [←(algebra.range_top_iff_surjective f.to_alg_hom).mpr f.surjective,
        ←root_set, adjoin_root_set_eq_range (splits F p), root_set, adjoin_roots F p] },
end

end is_splitting_field

end splitting_field

end polynomial

namespace intermediate_field

open polynomial

variables [field K] [field L] [algebra K L] {p : polynomial K}

lemma splits_of_splits {F : intermediate_field K L} (h : p.splits (algebra_map K L))
  (hF : ∀ x ∈ p.root_set L, x ∈ F) : p.splits (algebra_map K F) :=
begin
  simp_rw [root_set, finset.mem_coe, multiset.mem_to_finset] at hF,
  rw splits_iff_exists_multiset,
  refine ⟨multiset.pmap subtype.mk _ hF, map_injective _ (algebra_map F L).injective _⟩,
  conv_lhs { rw [polynomial.map_map, ←is_scalar_tower.algebra_map_eq,
    eq_prod_roots_of_splits h, ←multiset.pmap_eq_map _ _ _ hF] },
  simp_rw [polynomial.map_mul, polynomial.map_multiset_prod,
    multiset.map_pmap, polynomial.map_sub, map_C, map_X],
  refl,
end

end intermediate_field
