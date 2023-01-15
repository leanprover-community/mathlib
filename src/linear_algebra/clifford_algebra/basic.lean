/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Utensil Song
-/

import algebra.ring_quot
import linear_algebra.tensor_algebra.basic
import linear_algebra.quadratic_form.isometry

/-!
# Clifford Algebras

We construct the Clifford algebra of a module `M` over a commutative ring `R`, equipped with
a quadratic_form `Q`.

## Notation

The Clifford algebra of the `R`-module `M` equipped with a quadratic_form `Q` is
an `R`-algebra denoted `clifford_algebra Q`.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m, f m * f m = algebra_map _ _ (Q m)`, there is a (unique) lift of `f` to an `R`-algebra
morphism from `clifford_algebra Q` to `A`, which is denoted `clifford_algebra.lift Q f cond`.

The canonical linear map `M → clifford_algebra Q` is denoted `clifford_algebra.ι Q`.

## Theorems

The main theorems proved ensure that `clifford_algebra Q` satisfies the universal property
of the Clifford algebra.
1. `ι_comp_lift` is the fact that the composition of `ι Q` with `lift Q f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift Q f cond` with respect to 1.

Additionally, when `Q = 0` an `alg_equiv` to the `exterior_algebra` is provided as `as_exterior`.

## Implementation details

The Clifford algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `clifford_algebra.rel Q` on `tensor_algebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `Q m`.
2. The Clifford algebra is the quotient of the tensor algebra by this relation.

This file is almost identical to `linear_algebra/exterior_algebra.lean`.
-/

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

variable {n : ℕ}

namespace clifford_algebra
open tensor_algebra

/-- `rel` relates each `ι m * ι m`, for `m : M`, with `Q m`.

The Clifford algebra of `M` is defined as the quotient modulo this relation.
-/
inductive rel : tensor_algebra R M → tensor_algebra R M → Prop
| of (m : M) : rel (ι R m * ι R m) (algebra_map R _ (Q m))

end clifford_algebra

/--
The Clifford algebra of an `R`-module `M` equipped with a quadratic_form `Q`.

We make it a structure to be sure that Lean can not unfold it, and we will also use
irreducible operations for performance reasons.
-/
structure clifford_algebra :=
(out : ring_quot (clifford_algebra.rel Q))

namespace clifford_algebra

@[irreducible] private def zero : clifford_algebra Q := ⟨0⟩
@[irreducible] private def one : clifford_algebra Q := ⟨1⟩
@[irreducible] private def add : clifford_algebra Q → clifford_algebra Q → clifford_algebra Q
| ⟨a⟩ ⟨b⟩ := ⟨a + b⟩
@[irreducible] private def neg : clifford_algebra Q → clifford_algebra Q | ⟨a⟩ := ⟨-a⟩
@[irreducible] private def sub : clifford_algebra Q → clifford_algebra Q → clifford_algebra Q
| ⟨a⟩ ⟨b⟩ := ⟨a - b⟩
@[irreducible] private def mul : clifford_algebra Q → clifford_algebra Q → clifford_algebra Q
| ⟨a⟩ ⟨b⟩ := ⟨a * b⟩
-- next one not irreducible to avoid diamonds
protected def smul {S : Type*} [comm_semiring S] [algebra S (tensor_algebra R M)] :
  S → clifford_algebra Q → clifford_algebra Q
| r ⟨a⟩ := ⟨r • a⟩
@[irreducible] private def nat_cast : ℕ → clifford_algebra Q := λ n, ⟨n⟩
@[irreducible] private def int_cast : ℤ → clifford_algebra Q := λ n, ⟨n⟩
@[irreducible] private def npow : clifford_algebra Q → ℕ → clifford_algebra Q
| ⟨a⟩ n := ⟨a^n⟩

instance : has_zero (clifford_algebra Q) := ⟨zero Q⟩
instance : has_one (clifford_algebra Q) := ⟨one Q⟩
instance : has_add (clifford_algebra Q) := ⟨add Q⟩
instance : has_mul (clifford_algebra Q) := ⟨mul Q⟩
instance : has_neg (clifford_algebra Q) := ⟨neg Q⟩
instance : has_sub (clifford_algebra Q) := ⟨sub Q⟩

instance {S : Type*} [comm_semiring S] [algebra S (tensor_algebra R M)] :
  has_smul S (clifford_algebra Q) := ⟨clifford_algebra.smul Q⟩

instance : inhabited (clifford_algebra Q) := ⟨0⟩
instance : has_nat_cast (clifford_algebra Q) := ⟨nat_cast Q⟩
instance : has_int_cast (clifford_algebra Q) := ⟨int_cast Q⟩
instance : has_pow (clifford_algebra Q) ℕ := ⟨npow Q⟩

lemma zero_def : (0 : clifford_algebra Q) = ⟨0⟩ := by { show zero Q = _, rw zero }
lemma one_def : (1 : clifford_algebra Q) = ⟨1⟩ := by { show one Q = _, rw one }

lemma add_def {a b : ring_quot (clifford_algebra.rel Q)} :
  (⟨a⟩ + ⟨b⟩ : clifford_algebra Q) = ⟨a + b⟩ := by { show add Q _ _ = _, rw add }

lemma mul_def {a b : ring_quot (clifford_algebra.rel Q)} :
  (⟨a⟩ * ⟨b⟩ : clifford_algebra Q) = ⟨a * b⟩ := by { show mul Q _ _ = _, rw mul }

lemma smul_def {S : Type*} [comm_semiring S] [algebra S (tensor_algebra R M)]
  {s : S} {a : ring_quot (clifford_algebra.rel Q)} :
  (s • ⟨a⟩ : clifford_algebra Q) = ⟨s • a⟩ :=
by { show clifford_algebra.smul Q _ _ = _, rw clifford_algebra.smul }

instance : ring (clifford_algebra Q) :=
begin
  apply function.injective.ring (λ x:clifford_algebra Q, x.out),
  { rintros ⟨a⟩ ⟨b⟩ h, simpa only using h },
  { rw [zero_def] },
  { rw [one_def] },
  { rintros ⟨a⟩ ⟨b⟩, rw add_def },
  { rintros ⟨a⟩ ⟨b⟩, rw mul_def },
  { rintros ⟨a⟩, show (neg Q _).out = _, rw neg },
  { rintros ⟨a⟩ ⟨b⟩, show (sub Q _ _).out = _, rw sub },
  { rintros ⟨a⟩ n, rw smul_def },
  { rintros ⟨a⟩ n, rw smul_def },
  { rintros ⟨a⟩ n, show (npow Q _ _).out = _, rw npow },
  { rintros n, show (nat_cast Q _).out = _, rw nat_cast },
  { rintros n, show (int_cast Q _).out = _, rw int_cast },
end

instance : algebra R (clifford_algebra Q) :=
{ smul      := (•),
  to_fun    := λ r, ⟨algebra_map R _ r⟩,
  map_one'  := by simp [one_def],
  map_mul'  := by simp [mul_def],
  map_zero' := by simp [zero_def],
  map_add'  := by simp [add_def],
  commutes' := λ r, by { rintro ⟨⟩, simp [algebra.commutes, mul_def] },
  smul_def' := λ r, by { rintro ⟨⟩, simp [smul_def, algebra.smul_def, mul_def] } }

/-- The algebra equivalence between the irreducible `clifford_algebra Q` and its model
`ring_quot (clifford_algebra.rel Q) `, useful to set up the API (but should not
be used afterwards). -/
def to_ring_quot : clifford_algebra Q ≃ₐ[R] ring_quot (clifford_algebra.rel Q) :=
{ to_fun := λ a, a.out,
  inv_fun := λ a, ⟨a⟩,
  left_inv := λ ⟨a⟩, rfl,
  right_inv := λ a, rfl,
  map_add' := by { rintros ⟨⟩ ⟨⟩, simp [add_def] },
  map_mul' := by { rintros ⟨⟩ ⟨⟩, simp [mul_def] },
  commutes' := by { rintros r, simp [algebra_map], refl } }

/--
The canonical linear map `M →ₗ[R] clifford_algebra Q`.
-/
@[irreducible] def ι : M →ₗ[R] clifford_algebra Q :=
(to_ring_quot Q).symm.to_linear_map.comp
  ((ring_quot.mk_alg_hom R _).to_linear_map.comp (tensor_algebra.ι R))

/-- As well as being linear, `ι Q` squares to the quadratic form -/
@[simp]
theorem ι_sq_scalar (m : M) : ι Q m * ι Q m = algebra_map R _ (Q m) :=
begin
  simp only [ι, ←alg_hom.map_mul, ring_quot.mk_alg_hom_rel R (rel.of m), alg_hom.commutes,
    alg_hom.to_linear_map_apply, function.comp_app, linear_map.coe_comp, function.comp_app,
    alg_equiv.coe_mk, alg_equiv.to_linear_map_apply, alg_hom.to_linear_map_apply, to_ring_quot ],
  simp [mul_def, ←alg_hom.map_mul, ring_quot.mk_alg_hom_rel R (rel.of m), alg_hom.commutes],
  refl,
end

variables {Q} {A : Type*} [semiring A] [algebra R A]

@[simp]
theorem comp_ι_sq_scalar (g : clifford_algebra Q →ₐ[R] A) (m : M) :
  g (ι Q m) * g (ι Q m) = algebra_map _ _ (Q m) :=
by rw [←alg_hom.map_mul, ι_sq_scalar, alg_hom.commutes]

variables (Q)

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morphism of `R`-algebras
from the model `ring_quot (clifford_algebra.rel Q` to `A`. This is only an intermediate step
to construct the same map `lift` on `clifford_algebra Q`, not for use apart from API building.
-/
def lift_aux :
  {f : M →ₗ[R] A // ∀ m, f m * f m = algebra_map _ _ (Q m)} ≃
    (ring_quot (clifford_algebra.rel Q) →ₐ[R] A) :=
{ to_fun := λ f,
  ring_quot.lift_alg_hom R ⟨tensor_algebra.lift R (f : M →ₗ[R] A),
    (λ x y (h : rel Q x y), by
    { induction h,
      rw [alg_hom.commutes, alg_hom.map_mul, tensor_algebra.lift_ι_apply, f.prop], })⟩,
  inv_fun := λ F, ⟨F.to_linear_map.comp ((ring_quot.mk_alg_hom R _).to_linear_map.comp
    (tensor_algebra.ι R)), λ m, begin
      rw [linear_map.comp_apply, alg_hom.to_linear_map_apply],
      simp only [←alg_hom.map_mul, ring_quot.mk_alg_hom_rel R (rel.of m), alg_hom.commutes,
        linear_map.coe_comp, function.comp_app, alg_hom.to_linear_map_apply],
    end⟩,
  left_inv := λ f, by { ext,
    simp only [alg_hom.to_linear_map_apply, function.comp_app, linear_map.coe_comp,
               subtype.coe_mk, ring_quot.lift_alg_hom_mk_alg_hom_apply,
               tensor_algebra.lift_ι_apply] },
  right_inv := λ F, by { ext,
    simp only [alg_hom.comp_to_linear_map, alg_hom.to_linear_map_apply, function.comp_app,
               linear_map.coe_comp, subtype.coe_mk, ring_quot.lift_alg_hom_mk_alg_hom_apply,
               tensor_algebra.lift_ι_apply] } }

/-- Auxiliary definition for `lift`, pulling the equivalence of `clifford_algebra` with `ring_quot`
into an equivalence of algebra morphisms. -/
def to_ring_quot_alg_hom :
   (clifford_algebra Q →ₐ[R] A) ≃ (ring_quot (clifford_algebra.rel Q) →ₐ[R] A) :=
{ inv_fun := λ f, f.comp (to_ring_quot Q),
  to_fun := λ f, f.comp (to_ring_quot Q).symm,
  right_inv := λ f, begin
    ext x,
    simp only [alg_hom.comp_to_linear_map,
      alg_equiv.to_alg_hom_to_linear_map, linear_map.coe_comp, function.comp_app,
      alg_equiv.to_linear_map_apply, alg_equiv.apply_symm_apply],
  end,
  left_inv := λ f, begin
    ext x,
    simp only [alg_hom.coe_comp, alg_equiv.coe_alg_hom, function.comp_app,
      alg_equiv.symm_apply_apply],
  end }

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `clifford_algebra Q` to `A`.
-/
@[irreducible] def lift :
  {f : M →ₗ[R] A // ∀ m, f m * f m = algebra_map _ _ (Q m)} ≃ (clifford_algebra Q →ₐ[R] A) :=
(lift_aux Q).trans (to_ring_quot_alg_hom Q).symm

lemma coe_lift_symm_apply (f : clifford_algebra Q →ₐ[R] A) :
  ((lift Q).symm f : M →ₗ[R] A) = f.to_linear_map.comp (ι Q):=
begin
  ext x,
  simp only [lift, ι, lift_aux, to_ring_quot_alg_hom, alg_hom.comp_to_linear_map,
    alg_equiv.to_alg_hom_to_linear_map, equiv.symm_trans_apply, equiv.coe_fn_symm_mk,
    subtype.coe_mk, linear_map.coe_comp, equiv.symm_symm, equiv.coe_fn_mk],
end

@[simp] lemma lift_symm_apply (f : clifford_algebra Q →ₐ[R] A) :
  (lift Q).symm f = ⟨f.to_linear_map.comp (ι Q),
    λ m, by rw [linear_map.comp_apply, alg_hom.to_linear_map_apply, comp_ι_sq_scalar]⟩ :=
by { ext1, exact coe_lift_symm_apply Q f }

variables {Q}

@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebra_map _ _ (Q m)) :
  (lift Q ⟨f, cond⟩).to_linear_map.comp (ι Q) = f :=
by simpa using (lift Q).symm_apply_apply ⟨f, cond⟩

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebra_map _ _ (Q m)) (x) :
  lift Q ⟨f, cond⟩ (ι Q x) = f x :=
(linear_map.ext_iff.mp $ ι_comp_lift f cond) x

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m : M, f m * f m = algebra_map _ _ (Q m))
  (g : clifford_algebra Q →ₐ[R] A) :
  g.to_linear_map.comp (ι Q) = f ↔ g = lift Q ⟨f, cond⟩ :=
begin
  convert (lift Q).symm_apply_eq,
  rw lift_symm_apply,
  simp only,
end

@[simp]
theorem lift_comp_ι (g : clifford_algebra Q →ₐ[R] A) :
  lift Q ⟨g.to_linear_map.comp (ι Q), comp_ι_sq_scalar _⟩ = g :=
by simpa using (lift Q).apply_symm_apply g

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {A : Type*} [semiring A] [algebra R A] {f g : clifford_algebra Q →ₐ[R] A} :
  f.to_linear_map.comp (ι Q) = g.to_linear_map.comp (ι Q) → f = g :=
begin
  intro h,
  apply (lift Q).symm.injective,
  rw [lift_symm_apply, lift_symm_apply],
  simp only [h],
end

/-- If `C` holds for the `algebra_map` of `r : R` into `clifford_algebra Q`, the `ι` of `x : M`,
and is preserved under addition and muliplication, then it holds for all of `clifford_algebra Q`.

See also the stronger `clifford_algebra.left_induction` and `clifford_algebra.right_induction`.
-/
-- This proof closely follows `tensor_algebra.induction`
@[elab_as_eliminator]
lemma induction {C : clifford_algebra Q → Prop}
  (h_grade0 : ∀ r, C (algebra_map R (clifford_algebra Q) r))
  (h_grade1 : ∀ x, C (ι Q x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b))
  (a : clifford_algebra Q) :
  C a :=
begin
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : subalgebra R (clifford_algebra Q) :=
  { carrier := C,
    mul_mem' := h_mul,
    add_mem' := h_add,
    algebra_map_mem' := h_grade0, },
  let of : { f : M →ₗ[R] s // ∀ m, f m * f m = algebra_map _ _ (Q m) } :=
  ⟨(ι Q).cod_restrict s.to_submodule h_grade1,
    λ m, subtype.eq $ ι_sq_scalar Q m ⟩,
  -- the mapping through the subalgebra is the identity
  have of_id : alg_hom.id R (clifford_algebra Q) = s.val.comp (lift Q of),
  { ext,
    simp [of], },
  -- finding a proof is finding an element of the subalgebra
  convert subtype.prop (lift Q of a),
  exact alg_hom.congr_fun of_id a,
end

/-- The symmetric product of vectors is a scalar -/
lemma ι_mul_ι_add_swap (a b : M) :
  ι Q a * ι Q b + ι Q b * ι Q a = algebra_map R _ (quadratic_form.polar Q a b) :=
calc  ι Q a * ι Q b + ι Q b * ι Q a
    = ι Q (a + b) * ι Q (a + b) - ι Q a * ι Q a - ι Q b * ι Q b :
        by { rw [(ι Q).map_add, mul_add, add_mul, add_mul], abel, }
... = algebra_map R _ (Q (a + b)) - algebra_map R _ (Q a) - algebra_map R _ (Q b) :
        by rw [ι_sq_scalar, ι_sq_scalar, ι_sq_scalar]
... = algebra_map R _ (Q (a + b) - Q a - Q b) :
        by rw [←ring_hom.map_sub, ←ring_hom.map_sub]
... = algebra_map R _ (quadratic_form.polar Q a b) : rfl

lemma ι_mul_comm (a b : M) :
  ι Q a * ι Q b = algebra_map R _ (quadratic_form.polar Q a b) - ι Q b * ι Q a :=
eq_sub_of_add_eq (ι_mul_ι_add_swap a b)

/-- $aba$ is a vector. -/
lemma ι_mul_ι_mul_ι  (a b : M) :
  ι Q a * ι Q b * ι Q a = ι Q (quadratic_form.polar Q a b • a - Q a • b) :=
by rw [ι_mul_comm, sub_mul, mul_assoc, ι_sq_scalar, ←algebra.smul_def, ←algebra.commutes,
  ←algebra.smul_def, ←map_smul, ←map_smul, ←map_sub]

@[simp]
lemma ι_range_map_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebra_map _ _ (Q m)) :
  (ι Q).range.map (lift Q ⟨f, cond⟩).to_linear_map = f.range :=
by rw [←linear_map.range_comp, ι_comp_lift]

section map

variables {M₁ M₂ M₃ : Type*}
variables [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M₁] [module R M₂] [module R M₃]
variables (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) (Q₃ : quadratic_form R M₃)

/-- Any linear map that preserves the quadratic form lifts to an `alg_hom` between algebras.

See `clifford_algebra.equiv_of_isometry` for the case when `f` is a `quadratic_form.isometry`. -/
def map (f : M₁ →ₗ[R] M₂) (hf : ∀ m, Q₂ (f m) = Q₁ m) :
  clifford_algebra Q₁ →ₐ[R] clifford_algebra Q₂ :=
clifford_algebra.lift Q₁ ⟨(clifford_algebra.ι Q₂).comp f,
  λ m, (ι_sq_scalar _ _).trans $ ring_hom.congr_arg _ $ hf m⟩

@[simp]
lemma map_comp_ι (f : M₁ →ₗ[R] M₂) (hf) :
  (map Q₁ Q₂ f hf).to_linear_map.comp (ι Q₁) = (ι Q₂).comp f :=
ι_comp_lift _ _

@[simp]
lemma map_apply_ι (f : M₁ →ₗ[R] M₂) (hf) (m : M₁):
  map Q₁ Q₂ f hf (ι Q₁ m) = ι Q₂ (f m) :=
lift_ι_apply _ _ m

@[simp]
lemma map_id :
  map Q₁ Q₁ (linear_map.id : M₁ →ₗ[R] M₁) (λ m, rfl) = alg_hom.id R (clifford_algebra Q₁) :=
by { ext m, exact map_apply_ι _ _ _ _ m }

@[simp]
lemma map_comp_map (f : M₂ →ₗ[R] M₃) (hf) (g : M₁ →ₗ[R] M₂) (hg) :
  (map Q₂ Q₃ f hf).comp (map Q₁ Q₂ g hg) = map Q₁ Q₃ (f.comp g) (λ m, (hf _).trans $ hg m) :=
begin
  ext m,
  dsimp only [linear_map.comp_apply, alg_hom.comp_apply, alg_hom.to_linear_map_apply,
    alg_hom.id_apply],
  rw [map_apply_ι, map_apply_ι, map_apply_ι, linear_map.comp_apply],
end

@[simp]
lemma ι_range_map_map (f : M₁ →ₗ[R] M₂) (hf : ∀ m, Q₂ (f m) = Q₁ m) :
  (ι Q₁).range.map (map Q₁ Q₂ f hf).to_linear_map = f.range.map (ι Q₂) :=
(ι_range_map_lift _ _).trans (linear_map.range_comp _ _)

variables {Q₁ Q₂ Q₃}

/-- Two `clifford_algebra`s are equivalent as algebras if their quadratic forms are
equivalent. -/
@[simps apply]
def equiv_of_isometry (e : Q₁.isometry Q₂) :
  clifford_algebra Q₁ ≃ₐ[R] clifford_algebra Q₂ :=
alg_equiv.of_alg_hom
  (map Q₁ Q₂ e e.map_app)
  (map Q₂ Q₁ e.symm e.symm.map_app)
  ((map_comp_map _ _ _ _ _ _ _).trans $ begin
    convert map_id _ using 2,
    ext m,
    exact e.to_linear_equiv.apply_symm_apply m,
  end)
  ((map_comp_map _ _ _ _ _ _ _).trans $ begin
    convert map_id _ using 2,
    ext m,
    exact e.to_linear_equiv.symm_apply_apply m,
  end)

@[simp]
lemma equiv_of_isometry_symm (e : Q₁.isometry Q₂) :
  (equiv_of_isometry e).symm = equiv_of_isometry e.symm := rfl

@[simp]
lemma equiv_of_isometry_trans (e₁₂ : Q₁.isometry Q₂) (e₂₃ : Q₂.isometry Q₃) :
  (equiv_of_isometry e₁₂).trans (equiv_of_isometry e₂₃) = equiv_of_isometry (e₁₂.trans e₂₃) :=
by { ext x, exact alg_hom.congr_fun (map_comp_map Q₁ Q₂ Q₃ _ _ _ _) x }

@[simp]
lemma equiv_of_isometry_refl :
  (equiv_of_isometry $ quadratic_form.isometry.refl Q₁) = alg_equiv.refl :=
by { ext x, exact alg_hom.congr_fun (map_id Q₁) x }

end map

variables (Q)

/-- If the quadratic form of a vector is invertible, then so is that vector. -/
def invertible_ι_of_invertible (m : M) [invertible (Q m)] : invertible (ι Q m) :=
{ inv_of := ι Q (⅟(Q m) • m),
  inv_of_mul_self := by rw [map_smul, smul_mul_assoc, ι_sq_scalar, algebra.smul_def, ←map_mul,
    inv_of_mul_self, map_one],
  mul_inv_of_self := by rw [map_smul, mul_smul_comm, ι_sq_scalar, algebra.smul_def, ←map_mul,
    inv_of_mul_self, map_one] }

/-- For a vector with invertible quadratic form, $v^{-1} = \frac{v}{Q(v)}$ -/
lemma inv_of_ι (m : M) [invertible (Q m)] [invertible (ι Q m)] : ⅟(ι Q m) = ι Q (⅟(Q m) • m) :=
begin
  letI := invertible_ι_of_invertible Q m,
  convert (rfl : ⅟(ι Q m) = _),
end

lemma is_unit_ι_of_is_unit {m : M} (h : is_unit (Q m)) : is_unit (ι Q m) :=
begin
  casesI h.nonempty_invertible,
  letI := invertible_ι_of_invertible Q m,
  exactI is_unit_of_invertible (ι Q m),
end

/-- $aba^{-1}$ is a vector. -/
lemma ι_mul_ι_mul_inv_of_ι (a b : M) [invertible (ι Q a)] [invertible (Q a)] :
  ι Q a * ι Q b * ⅟(ι Q a) = ι Q ((⅟(Q a) * quadratic_form.polar Q a b) • a - b) :=
by rw [inv_of_ι, map_smul, mul_smul_comm, ι_mul_ι_mul_ι, ←map_smul, smul_sub, smul_smul, smul_smul,
  inv_of_mul_self, one_smul]

/-- $a^{-1}ba$ is a vector. -/
lemma inv_of_ι_mul_ι_mul_ι (a b : M) [invertible (ι Q a)] [invertible (Q a)] :
  ⅟(ι Q a) * ι Q b * ι Q a = ι Q ((⅟(Q a) * quadratic_form.polar Q a b) • a - b) :=
by rw [inv_of_ι, map_smul, smul_mul_assoc, smul_mul_assoc, ι_mul_ι_mul_ι, ←map_smul, smul_sub,
  smul_smul, smul_smul, inv_of_mul_self, one_smul]

end clifford_algebra

namespace tensor_algebra

variables {Q}

/-- The canonical image of the `tensor_algebra` in the `clifford_algebra`, which maps
`tensor_algebra.ι R x` to `clifford_algebra.ι Q x`. -/
def to_clifford : tensor_algebra R M →ₐ[R] clifford_algebra Q :=
tensor_algebra.lift R (clifford_algebra.ι Q)

@[simp] lemma to_clifford_ι (m : M) : (tensor_algebra.ι R m).to_clifford = clifford_algebra.ι Q m :=
by simp [to_clifford]

end tensor_algebra
