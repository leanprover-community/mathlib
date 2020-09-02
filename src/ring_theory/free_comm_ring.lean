/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin
-/
import data.equiv.functor
import data.mv_polynomial
import ring_theory.free_ring

/-!
# Free commutative rings

The theory of the free commutative ring generated by a type `α`.
It is isomorphic to the polynomial ring over ℤ with variables
in `α`

## Main definitions

* `free_comm_ring α`     : the free commutative ring on a type α
* `lift_hom (f : α → R)` : the ring hom `free_comm_ring α →+* R` induced by functoriality from `f`.
* `map (f : α → β)`      : the ring hom `free_comm_ring α →*+ free_comm_ring β` induced by
                           functoriality from f.

## Main results

`free_comm_ring` has functorial properties (it is an adjoint to the forgetful functor).
In this file we have:

* `of : α → free_comm_ring α`
* `lift_hom (f : α → R) : free_comm_ring α →+* R`
* `map (f : α → β) : free_comm_ring α →+* free_comm_ring β`

* `free_comm_ring_equiv_mv_polynomial_int : free_comm_ring α ≃+* mv_polynomial α ℤ` :
    `free_comm_ring α` is isomorphic to a polynomial ring.



## Implementation notes

`free_comm_ring α` is implemented not using `mv_polynomial` but
directly as the free abelian group on `multiset α`, the type
of monomials in this free commutative ring.

## Tags

free commutative ring, free ring
-/

noncomputable theory
open_locale classical

universes u v

variables (α : Type u)

/-- `free_comm_ring α` is the free commutative ring on the type `α`. -/
def free_comm_ring (α : Type u) : Type u :=
free_abelian_group $ multiplicative $ multiset α

namespace free_comm_ring

/-- The structure of a commutative ring on `free_comm_ring α`. -/
instance : comm_ring (free_comm_ring α) := free_abelian_group.comm_ring _

instance : inhabited (free_comm_ring α) := ⟨0⟩

variables {α}

/-- The canonical map from `α` to the free commutative ring on `α`. -/
def of (x : α) : free_comm_ring α :=
free_abelian_group.of ([x] : multiset α)

@[elab_as_eliminator] protected lemma induction_on
  {C : free_comm_ring α → Prop} (z : free_comm_ring α)
  (hn1 : C (-1)) (hb : ∀ b, C (of b))
  (ha : ∀ x y, C x → C y → C (x + y))
  (hm : ∀ x y, C x → C y → C (x * y)) : C z :=
have hn : ∀ x, C x → C (-x), from λ x ih, neg_one_mul x ▸ hm _ _ hn1 ih,
have h1 : C 1, from neg_neg (1 : free_comm_ring α) ▸ hn _ hn1,
free_abelian_group.induction_on z
  (add_left_neg (1 : free_comm_ring α) ▸ ha _ _ hn1 h1)
  (λ m, multiset.induction_on m h1 $ λ a m ih, hm _ _ (hb a) ih)
  (λ m ih, hn _ ih)
  ha
section lift

variables {R : Type v} [comm_ring R] (f : α → R)

/-- Lift a map `α → R` to a additive group homomorphism `free_comm_ring α → R`.
For a version producing a bundled homomorphism, see `lift_hom`. -/
def lift : free_comm_ring α →+* R :=
{ map_one' := free_abelian_group.lift.of _ _,
  map_mul' := λ x y,
  begin
    refine free_abelian_group.induction_on y (mul_zero _).symm _ _ _,
    { intros s2, conv_lhs { dsimp only [free_abelian_group.mul_def] },
      simp only [free_abelian_group.lift.of, add_monoid_hom.to_fun_eq_coe],
      refine free_abelian_group.induction_on x (zero_mul _).symm _ _ _,
      { intros s1, iterate 3 { rw free_abelian_group.lift.of },
        calc _ = multiset.prod ((multiset.map f s1) + (multiset.map f s2)) :
            by {congr' 1, exact multiset.map_add _ _ _}
          ... = _ : multiset.prod_add _ _ },
      { intros s1 ih, iterate 3 { rw free_abelian_group.lift.neg }, rw [ih, neg_mul_eq_neg_mul] },
      { intros x1 x2 ih1 ih2, iterate 3 { rw free_abelian_group.lift.add }, rw [ih1, ih2, add_mul] } },
    { intros s2 ih,
      simp only [add_monoid_hom.to_fun_eq_coe] at ih ⊢,
      rw [mul_neg_eq_neg_mul_symm, add_monoid_hom.map_neg, add_monoid_hom.map_neg, mul_neg_eq_neg_mul_symm, ih] },
    { intros y1 y2 ih1 ih2,
      simp only [add_monoid_hom.to_fun_eq_coe] at ih1 ih2 ⊢,
      rw [mul_add, add_monoid_hom.map_add, add_monoid_hom.map_add, mul_add, ih1, ih2] },
  end,
  ..free_abelian_group.lift $ λ s : multiplicative (multiset α), (s.to_add.map f).prod }

@[simp] lemma lift_of (x : α) : lift f (of x) = f x :=
(free_abelian_group.lift.of _ _).trans $ mul_one _

@[simp] lemma lift_comp_of (f : free_comm_ring α →+* R) : lift (f ∘ of) = f :=
ring_hom.ext $ λ x, free_comm_ring.induction_on x
  (by rw [ring_hom.map_neg, ring_hom.map_one, f.map_neg, f.map_one])
  (lift_of _)
  (λ x y ihx ihy, by rw [ring_hom.map_add, f.map_add, ihx, ihy])
  (λ x y ihx ihy, by rw [ring_hom.map_mul, f.map_mul, ihx, ihy])

end lift

variables {β : Type v} (f : α → β)

/-- A map `f : α → β` produces a ring homomorphism `free_comm_ring α →+* free_comm_ring β`. -/
def map : free_comm_ring α →+* free_comm_ring β :=
lift $ of ∘ f

@[simp]
lemma map_of (x : α) : map f (of x) = of (f x) := lift_of _ _

/-- `is_supported x s` means that all monomials showing up in `x` have variables in `s`. -/
def is_supported (x : free_comm_ring α) (s : set α) : Prop :=
x ∈ ring.closure (of '' s)

section is_supported
variables {x y : free_comm_ring α} {s t : set α}

theorem is_supported_upwards (hs : is_supported x s) (hst : s ⊆ t) :
  is_supported x t :=
ring.closure_mono (set.monotone_image hst) hs

theorem is_supported_add (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x + y) s :=
is_add_submonoid.add_mem hxs hys

theorem is_supported_neg (hxs : is_supported x s) :
  is_supported (-x) s :=
is_add_subgroup.neg_mem hxs

theorem is_supported_sub (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x - y) s :=
is_add_subgroup.sub_mem _ _ _ hxs hys

theorem is_supported_mul (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x * y) s :=
is_submonoid.mul_mem hxs hys

theorem is_supported_zero : is_supported 0 s :=
is_add_submonoid.zero_mem

theorem is_supported_one : is_supported 1 s :=
is_submonoid.one_mem

theorem is_supported_int {i : ℤ} {s : set α} : is_supported ↑i s :=
int.induction_on i is_supported_zero
  (λ i hi, by rw [int.cast_add, int.cast_one]; exact is_supported_add hi is_supported_one)
  (λ i hi, by rw [int.cast_sub, int.cast_one]; exact is_supported_sub hi is_supported_one)

end is_supported

/-- The restriction map from `free_comm_ring α` to `free_comm_ring s` where `s : set α`, defined
  by sending all variables not in `s` to zero. -/
def restriction (s : set α) [decidable_pred s] : free_comm_ring α →+* free_comm_ring s :=
lift (λ p, if H : p ∈ s then of ⟨p, H⟩  else 0)

section restriction
variables (s : set α) [decidable_pred s] (x y : free_comm_ring α)
@[simp] lemma restriction_of (p) : restriction s (of p) = if H : p ∈ s then of ⟨p, H⟩ else 0 := lift_of _ _

end restriction

theorem is_supported_of {p} {s : set α} : is_supported (of p) s ↔ p ∈ s :=
suffices is_supported (of p) s → p ∈ s, from ⟨this, λ hps, ring.subset_closure ⟨p, hps, rfl⟩⟩,
assume hps : is_supported (of p) s, begin
  haveI := classical.dec_pred s,
  have : ∀ x, is_supported x s →
    ∃ (n : ℤ), lift (λ a, if a ∈ s then (0 : polynomial ℤ) else polynomial.X) x = n,
  { intros x hx, refine ring.in_closure.rec_on hx _ _ _ _,
    { use 1, rw [ring_hom.map_one], norm_cast },
    { use -1, rw [ring_hom.map_neg, ring_hom.map_one], norm_cast },
    { rintros _ ⟨z, hzs, rfl⟩ _ _, use 0, rw [ring_hom.map_mul, lift_of, if_pos hzs, zero_mul], norm_cast },
    { rintros x y ⟨q, hq⟩ ⟨r, hr⟩, refine ⟨q+r, _⟩, rw [ring_hom.map_add, hq, hr], norm_cast } },
  specialize this (of p) hps, rw [lift_of] at this, split_ifs at this, { exact h },
  exfalso, apply ne.symm int.zero_ne_one,
  rcases this with ⟨w, H⟩, rw ←polynomial.C_eq_int_cast at H,
  have : polynomial.X.coeff 1 = (polynomial.C ↑w).coeff 1, by rw H,
  rwa [polynomial.coeff_C, if_neg (one_ne_zero : 1 ≠ 0), polynomial.coeff_X, if_pos rfl] at this
end

theorem map_subtype_val_restriction {x} (s : set α) [decidable_pred s] (hxs : is_supported x s) :
  map (subtype.val : s → α) (restriction s x) = x :=
begin
  refine ring.in_closure.rec_on hxs _ _ _ _,
  { rw ring_hom.map_one, refl },
  { rw [ring_hom.map_neg, ring_hom.map_neg, ring_hom.map_one], refl },
  { rintros _ ⟨p, hps, rfl⟩ n ih, rw [ring_hom.map_mul, restriction_of, dif_pos hps, ring_hom.map_mul, map_of, ih] },
  { intros x y ihx ihy, rw [ring_hom.map_add, ring_hom.map_add, ihx, ihy] }
end

theorem exists_finite_support (x : free_comm_ring α) : ∃ s : set α, set.finite s ∧ is_supported x s :=
free_comm_ring.induction_on x
  ⟨∅, set.finite_empty, is_supported_neg is_supported_one⟩
  (λ p, ⟨{p}, set.finite_singleton p, is_supported_of.2 $ set.mem_singleton _⟩)
  (λ x y ⟨s, hfs, hxs⟩ ⟨t, hft, hxt⟩, ⟨s ∪ t, hfs.union hft, is_supported_add
    (is_supported_upwards hxs $ set.subset_union_left s t)
    (is_supported_upwards hxt $ set.subset_union_right s t)⟩)
  (λ x y ⟨s, hfs, hxs⟩ ⟨t, hft, hxt⟩, ⟨s ∪ t, hfs.union hft, is_supported_mul
    (is_supported_upwards hxs $ set.subset_union_left s t)
    (is_supported_upwards hxt $ set.subset_union_right s t)⟩)

theorem exists_finset_support (x : free_comm_ring α) : ∃ s : finset α, is_supported x ↑s :=
let ⟨s, hfs, hxs⟩ := exists_finite_support x in ⟨hfs.to_finset, by rwa set.finite.coe_to_finset⟩

end free_comm_ring


namespace free_ring
open function
variable (α)

/-- The canonical ring homomorphism from the free ring generated by `α` to the free commutative ring
    generated by `α`. -/
def to_free_comm_ring {α} : free_ring α →+* free_comm_ring α :=
free_ring.lift free_comm_ring.of

instance : has_coe (free_ring α) (free_comm_ring α) := ⟨to_free_comm_ring⟩

instance coe.is_ring_hom : is_ring_hom (coe : free_ring α → free_comm_ring α) :=
free_ring.to_free_comm_ring.is_ring_hom

@[simp, norm_cast] protected lemma coe_zero : ↑(0 : free_ring α) = (0 : free_comm_ring α) := rfl
@[simp, norm_cast] protected lemma coe_one : ↑(1 : free_ring α) = (1 : free_comm_ring α) := rfl

variable {α}

@[simp] protected lemma coe_of (a : α) : ↑(free_ring.of a) = free_comm_ring.of a :=
free_ring.lift_of _ _
@[simp, norm_cast] protected lemma coe_neg (x : free_ring α) : ↑(-x) = -(x : free_comm_ring α) :=
(free_ring.lift _).map_neg _
@[simp, norm_cast] protected lemma coe_add (x y : free_ring α) : ↑(x + y) = (x : free_comm_ring α) + y :=
(free_ring.lift _).map_add _ _
@[simp, norm_cast] protected lemma coe_sub (x y : free_ring α) : ↑(x - y) = (x : free_comm_ring α) - y :=
(free_ring.lift _).map_sub _ _
@[simp, norm_cast] protected lemma coe_mul (x y : free_ring α) : ↑(x * y) = (x : free_comm_ring α) * y :=
(free_ring.lift _).map_mul _ _

variable (α)

protected lemma coe_surjective : surjective (coe : free_ring α → free_comm_ring α) :=
λ x,
begin
  apply free_comm_ring.induction_on x,
  { use -1, refl },
  { intro x, use free_ring.of x, refl },
  { rintros _ _ ⟨x, rfl⟩ ⟨y, rfl⟩, use x + y, exact (free_ring.lift _).map_add _ _ },
  { rintros _ _ ⟨x, rfl⟩ ⟨y, rfl⟩, use x * y, exact (free_ring.lift _).map_mul _ _ }
end

lemma coe_eq :
  (coe : free_ring α → free_comm_ring α) =
  @functor.map free_abelian_group _ _ _ (λ (l : list α), (l : multiset α)) :=
funext $ λ x, free_abelian_group.lift.unique _ _ $ λ L,
by { simp_rw [free_abelian_group.lift.of, (∘)], exact list.rec_on L rfl
(λ hd tl ih, by { rw [list.map_cons, list.prod_cons, ih], refl }) }

-- FIXME This was in `deprecated.ring`, but only used here.
-- It would be good to inline it into the next construction.
/-- Interpret an equivalence `f : R ≃ S` as a ring equivalence `R ≃+* S`. -/
def of' {R S : Type*} [ring R] [ring S] (e : R ≃ S) [is_ring_hom e] : R ≃+* S :=
{ .. e, .. monoid_hom.of e, .. add_monoid_hom.of e }

/-- If α has size at most 1 then the natural map from the free ring on `α` to the
    free commutative ring on `α` is an isomorphism of rings. -/
def subsingleton_equiv_free_comm_ring [subsingleton α] :
  free_ring α ≃+* free_comm_ring α :=
@of' (free_ring α) (free_comm_ring α) _ _
  (functor.map_equiv free_abelian_group (multiset.subsingleton_equiv α)) $
  begin
    delta functor.map_equiv,
    rw congr_arg is_ring_hom _,
    work_on_goal 2 { symmetry, exact coe_eq α },
    apply_instance
  end

instance [subsingleton α] : comm_ring (free_ring α) :=
{ mul_comm := λ x y,
  by { rw [← (subsingleton_equiv_free_comm_ring α).symm_apply_apply (y * x),
        ((subsingleton_equiv_free_comm_ring α)).map_mul,
        mul_comm,
        ← ((subsingleton_equiv_free_comm_ring α)).map_mul,
        (subsingleton_equiv_free_comm_ring α).symm_apply_apply], },
  .. free_ring.ring α }

end free_ring

/-- The free commutative ring on `α` is isomorphic to the polynomial ring over ℤ with
    variables in `α` -/
def free_comm_ring_equiv_mv_polynomial_int :
  free_comm_ring α ≃+* mv_polynomial α ℤ :=
{ to_fun  := free_comm_ring.lift $ λ a, mv_polynomial.X a,
  inv_fun := mv_polynomial.eval₂ (int.cast_ring_hom (free_comm_ring α)) free_comm_ring.of,
  left_inv :=
  begin
    intro x,
    haveI : is_semiring_hom (coe : int → free_comm_ring α) :=
      (int.cast_ring_hom _).is_semiring_hom,
    refine free_abelian_group.induction_on x rfl _ _ _,
    { intro s,
      refine multiset.induction_on s _ _,
      { unfold free_comm_ring.lift,
        simp only [free_abelian_group.lift.of, ring_hom.coe_mk, add_monoid_hom.to_fun_eq_coe],
        exact mv_polynomial.eval₂_one _ _ },
      { intros hd tl ih,
        show mv_polynomial.eval₂ (int.cast_ring_hom (free_comm_ring α)) free_comm_ring.of
          (free_comm_ring.lift (λ a, mv_polynomial.X a)
          (free_comm_ring.of hd * free_abelian_group.of tl)) =
          free_comm_ring.of hd * free_abelian_group.of tl,
        rw [ring_hom.map_mul, free_comm_ring.lift_of,
          mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X, ih] } },
    { intros s ih,
      rw [ring_hom.map_neg, ← neg_one_mul, mv_polynomial.eval₂_mul,
        ← mv_polynomial.C_1, ← mv_polynomial.C_neg, mv_polynomial.eval₂_C,
        ring_hom.map_neg, ring_hom.map_one, neg_one_mul, ih] },
    { intros x₁ x₂ ih₁ ih₂, rw [ring_hom.map_add, mv_polynomial.eval₂_add, ih₁, ih₂] }
  end,
  right_inv :=
  begin
    intro x,
    haveI : is_semiring_hom (coe : int → free_comm_ring α) :=
      (int.cast_ring_hom _).is_semiring_hom,
    have : ∀ i : ℤ, free_comm_ring.lift (λ (a : α), mv_polynomial.X a) (int.cast_ring_hom _ i) =
      mv_polynomial.C i,
    { exact λ i, int.induction_on i
      (by rw [ring_hom.map_zero, ring_hom.map_zero, mv_polynomial.C_0])
      (λ i ih, by rw [ring_hom.map_add, ring_hom.map_one, ring_hom.map_add,
        ring_hom.map_one, ih, mv_polynomial.C_add, mv_polynomial.C_1])
      (λ i ih, by rw [ring_hom.map_sub, ring_hom.map_one, ring_hom.map_sub,
        ring_hom.map_one, ih, mv_polynomial.C_sub, mv_polynomial.C_1]) },
    apply mv_polynomial.induction_on x,
    { intro i, rw [mv_polynomial.eval₂_C, this] },
    { intros p q ihp ihq, rw [mv_polynomial.eval₂_add, ring_hom.map_add, ihp, ihq] },
    { intros p a ih,
      rw [mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X,
        ring_hom.map_mul, free_comm_ring.lift_of, ih] }
  end,
  .. free_comm_ring.lift $ λ a, mv_polynomial.X a }

/-- The free commutative ring on the empty type is isomorphic to `ℤ`. -/
def free_comm_ring_pempty_equiv_int : free_comm_ring pempty.{u+1} ≃+* ℤ :=
ring_equiv.trans (free_comm_ring_equiv_mv_polynomial_int _) (mv_polynomial.pempty_ring_equiv _)

/-- The free commutative ring on a type with one term is isomorphic to `ℤ[X]`. -/
def free_comm_ring_punit_equiv_polynomial_int : free_comm_ring punit.{u+1} ≃+* polynomial ℤ :=
ring_equiv.trans (free_comm_ring_equiv_mv_polynomial_int _) (mv_polynomial.punit_ring_equiv _)

open free_ring

/-- The free ring on the empty type is isomorphic to `ℤ`. -/
def free_ring_pempty_equiv_int : free_ring pempty.{u+1} ≃+* ℤ :=
ring_equiv.trans (subsingleton_equiv_free_comm_ring _) free_comm_ring_pempty_equiv_int

/-- The free ring on a type with one term is isomorphic to `ℤ[X]`. -/
def free_ring_punit_equiv_polynomial_int : free_ring punit.{u+1} ≃+* polynomial ℤ :=
ring_equiv.trans (subsingleton_equiv_free_comm_ring _) free_comm_ring_punit_equiv_polynomial_int
