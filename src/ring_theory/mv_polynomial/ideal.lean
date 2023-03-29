/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.monoid_algebra.ideal
import data.mv_polynomial.division

/-!
# Lemmas about ideals of `mv_polynomial`

Notably this contains results about monomial ideals.

## Main results

* `mv_polynomial.mem_ideal_span_monomial_image`
* `mv_polynomial.mem_ideal_span_X_image`
-/

variables {σ R : Type*}

namespace mv_polynomial
variables [comm_semiring R]


/-- `x` is in a monomial ideal generated by `s` iff every element of of its support dominates one of
the generators. Note that `si ≤ xi` is analogous to saying that the monomial corresponding to `si`
divides the monomial corresponding to `xi`. -/
lemma mem_ideal_span_monomial_image
  {x : mv_polynomial σ R} {s : set (σ →₀ ℕ)} :
  x ∈ ideal.span ((λ s, monomial s (1 : R)) '' s) ↔ ∀ xi ∈ x.support, ∃ si ∈ s, si ≤ xi :=
begin
  refine add_monoid_algebra.mem_ideal_span_of'_image.trans _,
  simp_rw [le_iff_exists_add, add_comm],
  refl,
end

lemma mem_ideal_span_monomial_image_iff_dvd {x : mv_polynomial σ R} {s : set (σ →₀ ℕ)} :
  x ∈ ideal.span ((λ s, monomial s (1 : R)) '' s) ↔
    ∀ xi ∈ x.support, ∃ si ∈ s, monomial si 1 ∣ monomial xi (x.coeff xi) :=
begin
  refine mem_ideal_span_monomial_image.trans (forall₂_congr $ λ xi hxi, _),
  simp_rw [monomial_dvd_monomial, one_dvd, and_true, mem_support_iff.mp hxi, false_or],
end

/-- `x` is in a monomial ideal generated by variables `X` iff every element of of its support
has a component in `s`. -/
lemma mem_ideal_span_X_image {x : mv_polynomial σ R} {s : set σ} :
  x ∈ ideal.span (mv_polynomial.X '' s : set (mv_polynomial σ R)) ↔
    ∀ m ∈ x.support, ∃ i ∈ s, (m : σ →₀ ℕ) i ≠ 0 :=
begin
  have := @mem_ideal_span_monomial_image σ R _ _ ((λ i, finsupp.single i 1) '' s),
  rw set.image_image at this,
  refine this.trans _,
  simp [nat.one_le_iff_ne_zero],
end

end mv_polynomial
