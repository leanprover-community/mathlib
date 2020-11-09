/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.algebra.basic
import linear_algebra.bilinear_form
import linear_algebra.direct_sum.finsupp
import tactic.noncomm_ring

/-!
# Lie algebras

This file defines Lie rings, and Lie algebras over a commutative ring. It shows how these arise from
associative rings and algebras via the ring commutator. In particular it defines the Lie algebra
of endomorphisms of a module as well as of the algebra of square matrices over a commutative ring.

It also includes definitions of morphisms of Lie algebras, Lie subalgebras, Lie modules, Lie
submodules, and the quotient of a Lie algebra by an ideal.

## Notations

We introduce the notation ⁅x, y⁆ for the Lie bracket. Note that these are the Unicode "square with
quill" brackets rather than the usual square brackets.

We also introduce the notations L →ₗ⁅R⁆ L' for a morphism of Lie algebras over a commutative ring R,
and L →ₗ⁅⁆ L' for the same, when the ring is implicit.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*][bourbaki1975]

## Tags

lie bracket, ring commutator, jacobi identity, lie ring, lie algebra
-/

universes u v w w₁

/-- A binary operation, intended use in Lie algebras and similar structures. -/
class has_bracket (L : Type v) (M : Type w) := (bracket : L → M → M)

notation `⁅`x`,` y`⁆` := has_bracket.bracket x y

/-- An Abelian Lie algebra is one in which all brackets vanish. Arguably this class belongs in the
`has_bracket` namespace but it seems much more user-friendly to compromise slightly and put it in
the `lie_algebra` namespace. -/
class lie_algebra.is_abelian (L : Type v) [has_bracket L L] [has_zero L] : Prop :=
(abelian : ∀ (x y : L), ⁅x, y⁆ = 0)

namespace ring_commutator

variables {A : Type v} [ring A]

/-- The bracket operation for rings is the ring commutator, which captures the extent to which a
ring is commutative. It is identically zero exactly when the ring is commutative. -/
@[priority 100]
instance : has_bracket A A :=
{ bracket := λ x y, x*y - y*x }

lemma commutator (x y : A) : ⁅x, y⁆ = x*y - y*x := rfl

end ring_commutator

/-- A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. The bracket is not associative unless it is identically zero. -/
@[protect_proj] class lie_ring (L : Type v) extends add_comm_group L, has_bracket L L :=
(add_lie : ∀ (x y z : L), ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆)
(lie_add : ∀ (x y z : L), ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆)
(lie_self : ∀ (x : L), ⁅x, x⁆ = 0)
(jacobi : ∀ (x y z : L), ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0)

section lie_ring

variables {L : Type v} [lie_ring L]

@[simp] lemma add_lie (x y z : L) : ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆ := lie_ring.add_lie x y z
@[simp] lemma lie_add (x y z : L) : ⁅z, x + y⁆ = ⁅z, x⁆ + ⁅z, y⁆ := lie_ring.lie_add x y z
@[simp] lemma lie_self (x : L) : ⁅x, x⁆ = 0 := lie_ring.lie_self x

@[simp] lemma lie_skew (x y : L) :
  -⁅y, x⁆ = ⁅x, y⁆ :=
begin
  symmetry,
  rw [←sub_eq_zero_iff_eq, sub_neg_eq_add],
  have H : ⁅x + y, x + y⁆ = 0, from lie_self _,
  rw add_lie at H,
  simpa using H,
end

@[simp] lemma lie_zero (x : L) :
  ⁅x, (0 : L)⁆ = 0 :=
begin
  have H : ⁅x, (0 : L)⁆ + ⁅x, 0⁆ = ⁅x, 0⁆ + 0 := by { rw ←lie_add, simp, },
  exact add_left_cancel H,
end

@[simp] lemma zero_lie (x : L) :
  ⁅(0 : L), x⁆ = 0 := by { rw [←lie_skew, lie_zero], simp, }

@[simp] lemma neg_lie (x y : L) :
  ⁅-x, y⁆ = -⁅x, y⁆ := by { rw [←sub_eq_zero_iff_eq, sub_neg_eq_add, ←add_lie], simp, }

@[simp] lemma lie_neg (x y : L) :
  ⁅x, -y⁆ = -⁅x, y⁆ := by { rw [←lie_skew, ←lie_skew], simp, }

@[simp] lemma gsmul_lie (x y : L) (n : ℤ) :
  ⁅n • x, y⁆ = n • ⁅x, y⁆ :=
add_monoid_hom.map_gsmul ⟨λ (x : L), ⁅x, y⁆, zero_lie y, λ _ _, add_lie _ _ _⟩ _ _

@[simp] lemma lie_gsmul (x y : L) (n : ℤ) :
  ⁅x, n • y⁆ = n • ⁅x, y⁆ :=
begin
  rw [←lie_skew, ←lie_skew x, gsmul_lie],
  unfold has_scalar.smul, rw gsmul_neg,
end

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
@[priority 100]
instance lie_ring.of_associative_ring (A : Type v) [ring A] : lie_ring A :=
{ add_lie  := by simp only [ring_commutator.commutator, right_distrib, left_distrib, sub_eq_add_neg,
    add_comm, add_left_comm, forall_const, eq_self_iff_true, neg_add_rev],
  lie_add  := by simp only [ring_commutator.commutator, right_distrib, left_distrib, sub_eq_add_neg,
    add_comm, add_left_comm, forall_const, eq_self_iff_true, neg_add_rev],
  lie_self := by simp only [ring_commutator.commutator, forall_const, sub_self],
  jacobi   := λ x y z, by { repeat {rw ring_commutator.commutator}, noncomm_ring, } }

lemma lie_ring.of_associative_ring_bracket (A : Type v) [ring A] (x y : A) :
  ⁅x, y⁆ = x*y - y*x := rfl

lemma commutative_ring_iff_abelian_lie_ring (A : Type v) [ring A] :
  is_commutative A (*) ↔ lie_algebra.is_abelian A :=
begin
  have h₁ : is_commutative A (*) ↔ ∀ (a b : A), a * b = b * a := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  have h₂ : lie_algebra.is_abelian A ↔ ∀ (a b : A), ⁅a, b⁆ = 0 := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  simp only [h₁, h₂, lie_ring.of_associative_ring_bracket, sub_eq_zero],
end

end lie_ring

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
class lie_algebra (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] extends semimodule R L :=
(lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆)

@[simp] lemma lie_smul  (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]
  (t : R) (x y : L) : ⁅x, t • y⁆ = t • ⁅x, y⁆ :=
  lie_algebra.lie_smul t x y

@[simp] lemma smul_lie (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]
  (t : R) (x y : L) : ⁅t • x, y⁆ = t • ⁅x, y⁆ :=
  by { rw [←lie_skew, ←lie_skew x y], simp [-lie_skew], }

namespace lie_algebra

set_option old_structure_cmd true
/-- A morphism of Lie algebras is a linear map respecting the bracket operations. -/
structure morphism (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends linear_map R L L' :=
(map_lie : ∀ {x y : L}, to_fun ⁅x, y⁆ = ⁅to_fun x, to_fun y⁆)

attribute [nolint doc_blame] lie_algebra.morphism.to_linear_map

infixr ` →ₗ⁅⁆ `:25 := morphism _
notation L ` →ₗ⁅`:25 R:25 `⁆ `:0 L':0 := morphism R L L'

section morphism_properties

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance : has_coe (L₁ →ₗ⁅R⁆ L₂) (L₁ →ₗ[R] L₂) := ⟨morphism.to_linear_map⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ →ₗ⁅R⁆ L₂) := ⟨_, morphism.to_fun⟩

@[simp] lemma coe_mk (f : L₁ → L₂) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f := rfl

@[simp, norm_cast] lemma coe_to_linear_map (f : L₁ →ₗ⁅R⁆ L₂) : ((f : L₁ →ₗ[R] L₂) : L₁ → L₂) = f :=
rfl

@[simp] lemma map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ := morphism.map_lie f

/-- The constant 0 map is a Lie algebra morphism. -/
instance : has_zero (L₁ →ₗ⁅R⁆ L₂) := ⟨{ map_lie := by simp, ..(0 : L₁ →ₗ[R] L₂)}⟩

/-- The identity map is a Lie algebra morphism. -/
instance : has_one (L₁ →ₗ⁅R⁆ L₁) := ⟨{ map_lie := by simp, ..(1 : L₁ →ₗ[R] L₁)}⟩

instance : inhabited (L₁ →ₗ⁅R⁆ L₂) := ⟨0⟩

lemma morphism.coe_injective : function.injective (λ f : L₁ →ₗ⁅R⁆ L₂, show L₁ → L₂, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] lemma morphism.ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
morphism.coe_injective $ funext h

lemma morphism.ext_iff {f g : L₁ →ₗ⁅R⁆ L₂} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, morphism.ext⟩

/-- The composition of morphisms is a morphism. -/
def morphism.comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
{ map_lie := λ x y, by { change f (g ⁅x, y⁆) = ⁅f (g x), f (g y)⁆, rw [map_lie, map_lie], },
  ..linear_map.comp f.to_linear_map g.to_linear_map }

@[simp] lemma morphism.comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) :
  f.comp g x = f (g x) := rfl

@[norm_cast]
lemma morphism.comp_coe (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
  (f : L₂ → L₃) ∘ (g : L₁ → L₂) = f.comp g := rfl

/-- The inverse of a bijective morphism is a morphism. -/
def morphism.inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
{ map_lie := λ x y, by {
  calc g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ : by { conv_lhs { rw [←h₂ x, ←h₂ y], }, }
            ... = g (f ⁅g x, g y⁆) : by rw map_lie
            ... = ⁅g x, g y⁆ : (h₁ _), },
  ..linear_map.inverse f.to_linear_map g h₁ h₂ }

end morphism_properties

/-- An equivalence of Lie algebras is a morphism which is also a linear equivalence. We could
instead define an equivalence to be a morphism which is also a (plain) equivalence. However it is
more convenient to define via linear equivalence to get `.to_linear_equiv` for free. -/
structure equiv (R : Type u) (L : Type v) (L' : Type w)
  [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
  extends L →ₗ⁅R⁆ L', L ≃ₗ[R] L'

attribute [nolint doc_blame] lie_algebra.equiv.to_morphism
attribute [nolint doc_blame] lie_algebra.equiv.to_linear_equiv

notation L ` ≃ₗ⁅`:50 R `⁆ ` L' := equiv R L L'

namespace equiv

variables {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_ring L₃]
variables [lie_algebra R L₁] [lie_algebra R L₂] [lie_algebra R L₃]

instance has_coe_to_lie_hom : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ →ₗ⁅R⁆ L₂) := ⟨to_morphism⟩
instance has_coe_to_linear_equiv : has_coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) := ⟨to_linear_equiv⟩

/-- see Note [function coercion] -/
instance : has_coe_to_fun (L₁ ≃ₗ⁅R⁆ L₂) := ⟨_, to_fun⟩

@[simp, norm_cast] lemma coe_to_lie_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = e :=
  rfl

@[simp, norm_cast] lemma coe_to_linear_equiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ((e : L₁ ≃ₗ[R] L₂) : L₁ → L₂) = e :=
  rfl

instance : has_one (L₁ ≃ₗ⁅R⁆ L₁) :=
⟨{ map_lie := λ x y, by { change ((1 : L₁→ₗ[R] L₁) ⁅x, y⁆) = ⁅(1 : L₁→ₗ[R] L₁) x, (1 : L₁→ₗ[R] L₁) y⁆, simp, },
  ..(1 : L₁ ≃ₗ[R] L₁)}⟩

@[simp] lemma one_apply (x : L₁) : (1 : (L₁ ≃ₗ⁅R⁆ L₁)) x = x := rfl

instance : inhabited (L₁ ≃ₗ⁅R⁆ L₁) := ⟨1⟩

/-- Lie algebra equivalences are reflexive. -/
@[refl]
def refl : L₁ ≃ₗ⁅R⁆ L₁ := 1

@[simp] lemma refl_apply (x : L₁) : (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x := rfl

/-- Lie algebra equivalences are symmetric. -/
@[symm]
def symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁ :=
{ ..morphism.inverse e.to_morphism e.inv_fun e.left_inv e.right_inv,
  ..e.to_linear_equiv.symm }

@[simp] lemma symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e :=
by { cases e, refl, }

@[simp] lemma apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e (e.symm x) = x :=
  e.to_linear_equiv.apply_symm_apply

@[simp] lemma symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e.symm (e x) = x :=
  e.to_linear_equiv.symm_apply_apply

/-- Lie algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
{ ..morphism.comp e₂.to_morphism e₁.to_morphism,
  ..linear_equiv.trans e₁.to_linear_equiv e₂.to_linear_equiv }

@[simp] lemma trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) :
  (e₁.trans e₂) x = e₂ (e₁ x) := rfl

@[simp] lemma symm_trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₃) :
  (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) := rfl

end equiv

namespace direct_sum
open dfinsupp
open_locale direct_sum

variables {R : Type u} [comm_ring R]
variables {ι : Type v} {L : ι → Type w}
variables [Π i, lie_ring (L i)] [Π i, lie_algebra R (L i)]

/-- The direct sum of Lie rings carries a natural Lie ring structure. -/
instance : lie_ring (⨁ i, L i) :=
{ bracket  := zip_with (λ i, λ x y, ⁅x, y⁆) (λ i, lie_zero 0),
  add_lie  := λ x y z, by { ext, simp only [zip_with_apply, add_apply, add_lie], },
  lie_add  := λ x y z, by { ext, simp only [zip_with_apply, add_apply, lie_add], },
  lie_self := λ x, by { ext, simp only [zip_with_apply, add_apply, lie_self, zero_apply], },
  jacobi   := λ x y z, by { ext, simp only [
    zip_with_apply, add_apply, lie_ring.jacobi, zero_apply], },
  ..(infer_instance : add_comm_group _) }

@[simp] lemma bracket_apply {x y : (⨁ i, L i)} {i : ι} :
  ⁅x, y⁆ i = ⁅x i, y i⁆ := zip_with_apply _ _ x y i

/-- The direct sum of Lie algebras carries a natural Lie algebra structure. -/
instance : lie_algebra R (⨁ i, L i) :=
{ lie_smul := λ c x y, by { ext, simp only [
    zip_with_apply, direct_sum.smul_apply, bracket_apply, lie_smul] },
  ..(infer_instance : module R _) }

end direct_sum

variables {R : Type u} {L : Type v} [comm_ring R] [lie_ring L] [lie_algebra R L]

/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
@[priority 100]
instance lie_algebra.of_associative_algebra {A : Type v} [ring A] [algebra R A] :
  lie_algebra R A :=
{ lie_smul := λ t x y,
    by rw [lie_ring.of_associative_ring_bracket, lie_ring.of_associative_ring_bracket,
           algebra.mul_smul_comm, algebra.smul_mul_assoc, smul_sub], }

instance (M : Type v) [add_comm_group M] [module R M] : lie_ring (module.End R M) :=
lie_ring.of_associative_ring _

/-- The map `of_associative_algebra` associating a Lie algebra to an associative algebra is
functorial. -/
def of_associative_algebra_hom {R : Type u} {A : Type v} {B : Type w}
  [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B] (f : A →ₐ[R] B) : A →ₗ⁅R⁆ B :=
 { map_lie := λ x y, show f ⁅x,y⁆ = ⁅f x,f y⁆,
     by simp only [lie_ring.of_associative_ring_bracket, alg_hom.map_sub, alg_hom.map_mul],
  ..f.to_linear_map, }

@[simp] lemma of_associative_algebra_hom_id {R : Type u} {A : Type v}
  [comm_ring R] [ring A] [algebra R A] : of_associative_algebra_hom (alg_hom.id R A) = 1 := rfl

@[simp] lemma of_associative_algebra_hom_apply {R : Type u} {A : Type v} {B : Type w}
  [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B] (f : A →ₐ[R] B) (x : A) :
  of_associative_algebra_hom f x = f x := rfl

@[simp] lemma of_associative_algebra_hom_comp {R : Type u} {A : Type v} {B : Type w} {C : Type w₁}
  [comm_ring R] [ring A] [ring B] [ring C] [algebra R A] [algebra R B] [algebra R C]
  (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
  of_associative_algebra_hom (g.comp f) = (of_associative_algebra_hom g).comp (of_associative_algebra_hom f) := rfl

/-- An important class of Lie algebras are those arising from the associative algebra structure on
module endomorphisms. We state a lemma and give a definition concerning them. -/
lemma endo_algebra_bracket (M : Type v) [add_comm_group M] [module R M] (f g : module.End R M) :
  ⁅f, g⁆ = f.comp g - g.comp f := rfl

/-- The adjoint action of a Lie algebra on itself. -/
def ad : L →ₗ⁅R⁆ module.End R L :=
{ to_fun    := λ x,
  { to_fun    := has_bracket.bracket x,
    map_add'  := by { intros, apply lie_add, },
    map_smul' := by { intros, apply lie_smul, } },
  map_add'  := by { intros, ext, simp, },
  map_smul' := by { intros, ext, simp, },
  map_lie   := by {
    intros x y, ext z,
    rw endo_algebra_bracket,
    suffices : ⁅⁅x, y⁆, z⁆ = ⁅x, ⁅y, z⁆⁆ + ⁅⁅x, z⁆, y⁆, by simpa [sub_eq_add_neg],
    rw [eq_comm, ←lie_skew ⁅x, y⁆ z, ←lie_skew ⁅x, z⁆ y, ←lie_skew x z, lie_neg, neg_neg,
        ←sub_eq_zero_iff_eq, sub_neg_eq_add, lie_ring.jacobi], } }

end lie_algebra

section lie_subalgebra

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]

set_option old_structure_cmd true
/-- A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra. -/
structure lie_subalgebra extends submodule R L :=
(lie_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x, y⁆ ∈ carrier)

attribute [nolint doc_blame] lie_subalgebra.to_submodule

/-- The zero algebra is a subalgebra of any Lie algebra. -/
instance : has_zero (lie_subalgebra R L) :=
⟨{ lie_mem := λ x y hx hy, by { rw [((submodule.mem_bot R).1 hx), zero_lie],
                                exact submodule.zero_mem (0 : submodule R L), },
   ..(0 : submodule R L) }⟩

instance : inhabited (lie_subalgebra R L) := ⟨0⟩
instance : has_coe (lie_subalgebra R L) (set L) := ⟨lie_subalgebra.carrier⟩
instance : has_mem L (lie_subalgebra R L) := ⟨λ x L', x ∈ (L' : set L)⟩

instance lie_subalgebra_coe_submodule : has_coe (lie_subalgebra R L) (submodule R L) :=
⟨lie_subalgebra.to_submodule⟩

/-- A Lie subalgebra forms a new Lie ring. -/
instance lie_subalgebra_lie_ring (L' : lie_subalgebra R L) : lie_ring L' :=
{ bracket  := λ x y, ⟨⁅x.val, y.val⁆, L'.lie_mem x.property y.property⟩,
  lie_add  := by { intros, apply set_coe.ext, apply lie_add, },
  add_lie  := by { intros, apply set_coe.ext, apply add_lie, },
  lie_self := by { intros, apply set_coe.ext, apply lie_self, },
  jacobi   := by { intros, apply set_coe.ext, apply lie_ring.jacobi, } }

/-- A Lie subalgebra forms a new Lie algebra. -/
instance lie_subalgebra_lie_algebra (L' : lie_subalgebra R L) :
    @lie_algebra R L' _ (lie_subalgebra_lie_ring _ _ _) :=
{ lie_smul := by { intros, apply set_coe.ext, apply lie_smul } }

@[simp] lemma lie_subalgebra.mem_coe {L' : lie_subalgebra R L} {x : L} :
  x ∈ (L' : set L) ↔ x ∈ L' := iff.rfl

@[simp] lemma lie_subalgebra.mem_coe' {L' : lie_subalgebra R L} {x : L} :
  x ∈ (L' : submodule R L) ↔ x ∈ L' := iff.rfl

@[simp, norm_cast] lemma lie_subalgebra.coe_bracket (L' : lie_subalgebra R L) (x y : L') :
  (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ := rfl

@[ext] lemma lie_subalgebra.ext (L₁' L₂' : lie_subalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') :
  L₁' = L₂' :=
by { cases L₁', cases L₂', simp only [], ext x, exact h x, }

lemma lie_subalgebra.ext_iff (L₁' L₂' : lie_subalgebra R L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
⟨λ h x, by rw h, lie_subalgebra.ext R L L₁' L₂'⟩

/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
def lie_subalgebra_of_subalgebra (A : Type v) [ring A] [algebra R A]
  (A' : subalgebra R A) : lie_subalgebra R A :=
{ lie_mem := λ x y hx hy, by {
    change ⁅x, y⁆ ∈ A', change x ∈ A' at hx, change y ∈ A' at hy,
    rw lie_ring.of_associative_ring_bracket,
    have hxy := A'.mul_mem hx hy,
    have hyx := A'.mul_mem hy hx,
    exact submodule.sub_mem A'.to_submodule hxy hyx, },
  ..A'.to_submodule }

variables {R L} {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂]

/-- The embedding of a Lie subalgebra into the ambient space as a Lie morphism. -/
def lie_subalgebra.incl (L' : lie_subalgebra R L) : L' →ₗ⁅R⁆ L :=
{ map_lie := λ x y, by { rw [linear_map.to_fun_eq_coe, submodule.subtype_apply], refl, },
  ..L'.to_submodule.subtype }

/-- The range of a morphism of Lie algebras is a Lie subalgebra. -/
def lie_algebra.morphism.range (f : L →ₗ⁅R⁆ L₂) : lie_subalgebra R L₂ :=
{ lie_mem := λ x y,
    show x ∈ f.to_linear_map.range → y ∈ f.to_linear_map.range → ⁅x, y⁆ ∈ f.to_linear_map.range,
    by { repeat { rw linear_map.mem_range }, rintros ⟨x', hx⟩ ⟨y', hy⟩, refine ⟨⁅x', y'⁆, _⟩,
         rw [←hx, ←hy], change f ⁅x', y'⁆ = ⁅f x', f y'⁆, rw lie_algebra.map_lie, },
  ..f.to_linear_map.range }

@[simp] lemma lie_algebra.morphism.range_bracket (f : L →ₗ⁅R⁆ L₂) (x y : f.range) :
  (↑⁅x, y⁆ : L₂) = ⁅(↑x : L₂), ↑y⁆ := rfl

/-- The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
codomain. -/
def lie_subalgebra.map (f : L →ₗ⁅R⁆ L₂) (L' : lie_subalgebra R L) : lie_subalgebra R L₂ :=
{ lie_mem := λ x y hx hy, by {
    erw submodule.mem_map at hx, rcases hx with ⟨x', hx', hx⟩, rw ←hx,
    erw submodule.mem_map at hy, rcases hy with ⟨y', hy', hy⟩, rw ←hy,
    erw submodule.mem_map,
    exact ⟨⁅x', y'⁆, L'.lie_mem hx' hy', lie_algebra.map_lie f x' y'⟩, },
..((L' : submodule R L).map (f : L →ₗ[R] L₂))}

@[simp] lemma lie_subalgebra.mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (L' : lie_subalgebra R L) (x : L₂) :
  x ∈ L'.map (e : L →ₗ⁅R⁆ L₂) ↔ x ∈ (L' : submodule R L).map (e : L →ₗ[R] L₂) :=
iff.rfl

end lie_subalgebra

namespace lie_algebra

variables {R : Type u} {L₁ : Type v} {L₂ : Type w}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂]

namespace equiv

/-- An injective Lie algebra morphism is an equivalence onto its range. -/
noncomputable def of_injective (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) :
  L₁ ≃ₗ⁅R⁆ f.range :=
have h' : (f : L₁ →ₗ[R] L₂).ker = ⊥ := linear_map.ker_eq_bot_of_injective h,
{ map_lie := λ x y, by { apply set_coe.ext,
    simp only [linear_equiv.of_injective_apply, lie_algebra.morphism.range_bracket],
    apply f.map_lie, },
..(linear_equiv.of_injective ↑f h')}

@[simp] lemma of_injective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) (x : L₁) :
  ↑(of_injective f h x) = f x := rfl

variables (L₁' L₁'' : lie_subalgebra R L₁) (L₂' : lie_subalgebra R L₂)

/-- Lie subalgebras that are equal as sets are equivalent as Lie algebras. -/
def of_eq (h : (L₁' : set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁'' :=
{ map_lie := λ x y, by { apply set_coe.ext, simp, },
  ..(linear_equiv.of_eq ↑L₁' ↑L₁''
      (by {ext x, change x ∈ (L₁' : set L₁) ↔ x ∈ (L₁'' : set L₁), rw h, } )) }

@[simp] lemma of_eq_apply (L L' : lie_subalgebra R L₁) (h : (L : set L₁) = L') (x : L) :
  (↑(of_eq L L' h x) : L₁) = x := rfl

variables (e : L₁ ≃ₗ⁅R⁆ L₂)

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebra : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : lie_subalgebra R L₂) :=
{ map_lie := λ x y, by { apply set_coe.ext, exact lie_algebra.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, }
  ..(linear_equiv.of_submodule (e : L₁ ≃ₗ[R] L₂) ↑L₁'') }

@[simp] lemma of_subalgebra_apply (x : L₁'') : ↑(e.of_subalgebra _  x) = e x := rfl

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebras (h : L₁'.map ↑e = L₂') : L₁' ≃ₗ⁅R⁆ L₂' :=
{ map_lie := λ x y, by { apply set_coe.ext, exact lie_algebra.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, },
  ..(linear_equiv.of_submodules (e : L₁ ≃ₗ[R] L₂) ↑L₁' ↑L₂' (by { rw ←h, refl, })) }

@[simp] lemma of_subalgebras_apply (h : L₁'.map ↑e = L₂') (x : L₁') :
  ↑(e.of_subalgebras _ _ h x) = e x := rfl

@[simp] lemma of_subalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') :
  ↑((e.of_subalgebras _ _ h).symm x) = e.symm x := rfl

end equiv

end lie_algebra

section lie_module

variables (R : Type u) {L : Type v} {M  : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]

/-- A Lie module is a module over a commutative ring, together with a linear action of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endomorphisms. -/
class lie_module (α : has_bracket L M) :=
(add_lie : ∀ (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆)
(lie_add : ∀ (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆)
(smul_lie : ∀ (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆)
(lie_smul : ∀ (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆)
(lie_lie : ∀ (x y : L) (m : M), ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆)

@[simp] lemma lie_module_add_lie
  (α : has_bracket L M) [lie_module R α] (x y : L) (m : M) :
  ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆ :=
lie_module.add_lie R x y m

@[simp] lemma lie_module_lie_add
  (α : has_bracket L M) [lie_module R α] (x : L) (m n : M) :
  ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆ :=
lie_module.lie_add R x m n

@[simp] lemma lie_module_smul_lie
  (α : has_bracket L M) [lie_module R α] (t : R) (x : L) (m : M) :
  ⁅t • x, m⁆ = t • ⁅x, m⁆ :=
lie_module.smul_lie t x m

@[simp] lemma lie_module_lie_smul
  (α : has_bracket L M) [lie_module R α] (t : R) (x : L) (m : M) :
  ⁅x, t • m⁆ = t • ⁅x, m⁆ :=
lie_module.lie_smul t x m

@[simp] lemma lie_lie
  (α : has_bracket L M) [lie_module R α] (x y : L) (m : M) :
  ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ :=
lie_module.lie_lie R x y m

@[simp] lemma lie_module_zero_lie
  (α : has_bracket L M) [lie_module R α] (x : L) :
  ⁅x, 0⁆ = (0 : M) :=
(add_monoid_hom.mk' _ (lie_module.lie_add R x)).map_zero

@[simp] lemma lie_module_lie_zero
  (α : has_bracket L M) [lie_module R α] (m : M) :
  ⁅(0 : L), m⁆ = 0 :=
begin
  refine (add_monoid_hom.mk' (λ (x : L), ⁅x, m⁆) _).map_zero,
  simp [lie_module_add_lie R α],
end

/-- A Lie algebra morphism into the endomorphism algebra of a module yields a bracket action on
that module. -/
def lie_module.of_endo_morphism_bracket (α : L →ₗ⁅R⁆ module.End R M) : has_bracket L M :=
⟨λ x m, α x m⟩

@[simp] lemma lie_module.of_endo_morphism_bracket_apply
  (α : L →ₗ⁅R⁆ module.End R M) (x : L) (m : M) :
  @has_bracket.bracket _ _ (lie_module.of_endo_morphism_bracket R α) x m = α x m :=
rfl

/-- The bracket action of a Lie algebra on a module, obtained from a Lie morphism into its
endomorphism algebra, provides a Lie module structure. -/
def lie_module.of_endo_morphism (α : L →ₗ⁅R⁆ module.End R M) :
  lie_module R (lie_module.of_endo_morphism_bracket R α) :=
{ add_lie  := λ x y m, show (α : L →ₗ[R] module.End R M) _ _ = _, by {rw linear_map.map_add, refl, },
  lie_add  := λ x m n, show (α : L →ₗ[R] module.End R M) _ _ = _, by {rw linear_map.map_add, refl, },
  smul_lie := λ t x m, show (α : L →ₗ[R] module.End R M) _ _ = _, by {rw linear_map.map_smul, refl,},
  lie_smul := λ t x m, show (α : L →ₗ[R] module.End R M) _ _ = _, by {rw linear_map.map_smul, refl,},
  lie_lie  := λ x y m, by
    { simp only [lie_module.of_endo_morphism_bracket_apply, lie_algebra.map_lie,
                 lie_algebra.endo_algebra_bracket, linear_map.sub_apply, linear_map.comp_apply], } }

/-- A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module. -/
def lie_module.to_endo_morphism (α : has_bracket L M) [lie_module R α] :
  L →ₗ⁅R⁆ module.End R M :=
{ to_fun    := λ x,
  { to_fun    := λ m, ⁅x, m⁆,
    map_add'  := λ m n, lie_module.lie_add R x m n,
    map_smul' := λ t m, lie_module.lie_smul t x m, },
  map_add'  := λ x y, by { ext m, apply lie_module_add_lie R α, },
  map_smul' := λ t x, by { ext m, exact lie_module.smul_lie t x m, },
  map_lie   := λ x y, by { ext m, apply lie_lie R α, }, }

/-- Every Lie algebra is a module over itself. -/
instance lie_algebra_self_module : lie_module R (@lie_ring.to_has_bracket L _) :=
{ ..lie_module.of_endo_morphism R lie_algebra.ad }

/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
structure lie_submodule (α : has_bracket L M) [lie_module R α] extends submodule R M :=
(lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x, m⁆ ∈ carrier)

/-- The zero module is a Lie submodule of any Lie module. -/
instance (α : has_bracket L M) [lie_module R α] : has_zero (lie_submodule R α) :=
⟨{ lie_mem := λ x m h, by { rw ((submodule.mem_bot R).1 h), apply lie_module_zero_lie R α, },
   ..(0 : submodule R M)}⟩

instance (α : has_bracket L M) [lie_module R α] : inhabited (lie_submodule R α) := ⟨0⟩

instance lie_submodule_coe_submodule (α : has_bracket L M) [lie_module R α] :
  has_coe (lie_submodule R α) (submodule R M) :=
⟨lie_submodule.to_submodule⟩

instance lie_submodule_has_mem (α : has_bracket L M) [lie_module R α] :
  has_mem M (lie_submodule R α) :=
⟨λ x N, x ∈ (N : set M)⟩

instance lie_submodule_act (α : has_bracket L M) [lie_module R α] (N : lie_submodule R α) :
  has_bracket L N :=
⟨λ (x : L) (m : N), ⟨⁅x, m.val⁆, N.lie_mem m.property⟩⟩

instance lie_submodule_lie_module
  (α : has_bracket L M) [lie_module R α] (N : lie_submodule R α) :
  @lie_module R L N _ _ _ _ _ infer_instance :=
{ add_lie  := by { intros x y m, apply set_coe.ext, exact lie_module.add_lie R x y m, },
  lie_add  := by { intros x m n, apply set_coe.ext, exact lie_module.lie_add R x m n, },
  lie_smul := by { intros t x y, apply set_coe.ext, exact lie_module.lie_smul t x y, },
  smul_lie := by { intros t x y, apply set_coe.ext, exact lie_module.smul_lie t x y, },
  lie_lie  := by { intros x y m, apply set_coe.ext, exact lie_module.lie_lie R x y m, } }

/-- A Lie module is irreducible if its only non-trivial Lie submodule is itself. -/
class lie_module.is_irreducible (α : has_bracket L M) [lie_module R α] : Prop :=
(irreducible : ∀ (M' : lie_submodule R α), (∃ (m : M'), m ≠ 0) → (∀ (m : M), m ∈ M'))

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
class lie_algebra.is_simple : Prop :=
(simple : lie_module.is_irreducible R (@lie_ring.to_has_bracket L _) ∧ ¬lie_algebra.is_abelian L)

variables (L)

/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
abbreviation lie_ideal := lie_submodule R (@lie_ring.to_has_bracket L _)

lemma lie_mem_right (I : lie_ideal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I := I.lie_mem h

lemma lie_mem_left (I : lie_ideal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I := by {
  rw [←lie_skew, ←neg_lie], apply lie_mem_right, assumption, }

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
def lie_ideal_subalgebra (I : lie_ideal R L) : lie_subalgebra R L :=
{ lie_mem := by { intros x y hx hy, apply lie_mem_right, exact hy, },
  ..I.to_submodule, }

end lie_module

namespace lie_submodule

variables {R : Type u} {L : Type v} {M : Type v}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables {α : has_bracket L M} [lie_module R α]
variables (N : lie_submodule R α) (I : lie_ideal R L)

/-- The quotient of a Lie module by a Lie submodule. It is a Lie module. -/
abbreviation quotient := N.to_submodule.quotient

namespace quotient

variables {N I}

/-- Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a
lie_submodule of the lie_module `N`. -/
abbreviation mk : M → N.quotient := submodule.quotient.mk

lemma is_quotient_mk (m : M) :
  quotient.mk' m = (mk m : N.quotient) := rfl

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lie_submodule_invariant : L →ₗ[R] submodule.compatible_maps N.to_submodule N.to_submodule :=
  linear_map.cod_restrict _ (lie_module.to_endo_morphism R α) N.lie_mem

variables (N)

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
def action_as_endo_map : L →ₗ⁅R⁆ module.End R N.quotient :=
{ map_lie := λ x y, by { ext n, apply quotient.induction_on' n, intros m,
                         change mk ⁅⁅x, y⁆, m⁆ = mk (⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆),
                         rw lie_module.lie_lie R x y m, apply_instance, },
  ..linear_map.comp (submodule.mapq_linear (N : submodule R M) ↑N) lie_submodule_invariant }

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
def action_as_endo_map_bracket : has_bracket L N.quotient := ⟨λ x n, action_as_endo_map N x n⟩

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
instance lie_quotient_lie_module : lie_module R (action_as_endo_map_bracket N) :=
lie_module.of_endo_morphism R (action_as_endo_map N)

instance lie_quotient_has_bracket : has_bracket (quotient I) (quotient I) := ⟨by {
  intros x y,
  apply quotient.lift_on₂' x y (λ x' y', mk ⁅x', y'⁆),
  intros x₁ x₂ y₁ y₂ h₁ h₂,
  apply (submodule.quotient.eq I.to_submodule).2,
  have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆ := by simp [-lie_skew, sub_eq_add_neg, add_assoc],
  rw h,
  apply submodule.add_mem,
  { apply lie_mem_right R L I x₁ (x₂ - y₂) h₂, },
  { apply lie_mem_left R L I (x₁ - y₁) y₂ h₁, }, }⟩

@[simp] lemma mk_bracket (x y : L) :
  mk ⁅x, y⁆ = ⁅(mk x : quotient I), (mk y : quotient I)⁆ := rfl

instance lie_quotient_lie_ring : lie_ring (quotient I) :=
{ add_lie  := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply add_lie, },
  lie_add  := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply lie_add, },
  lie_self := by { intros x', apply quotient.induction_on' x', intros x,
                   rw [is_quotient_mk, ←mk_bracket],
                   apply congr_arg, apply lie_self, },
  jacobi   := by { intros x' y' z', apply quotient.induction_on₃' x' y' z', intros x y z,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_add, },
                   apply congr_arg, apply lie_ring.jacobi, } }

instance lie_quotient_lie_algebra : lie_algebra R (quotient I) :=
{ lie_smul := by { intros t x' y', apply quotient.induction_on₂' x' y', intros x y,
                   repeat { rw is_quotient_mk <|>
                            rw ←mk_bracket <|>
                            rw ←submodule.quotient.mk_smul, },
                   apply congr_arg, apply lie_smul, } }

end quotient

end lie_submodule

namespace linear_equiv

variables {R : Type u} {M₁ : Type v} {M₂ : Type w}
variables [comm_ring R] [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]
variables (e : M₁ ≃ₗ[R] M₂)

/-- A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
def lie_conj : module.End R M₁ ≃ₗ⁅R⁆ module.End R M₂ :=
{ map_lie := λ f g, show e.conj ⁅f, g⁆ =  ⁅e.conj f, e.conj g⁆,
             by simp only [lie_algebra.endo_algebra_bracket, e.conj_comp, linear_equiv.map_sub],
  ..e.conj }

@[simp] lemma lie_conj_apply (f : module.End R M₁) : e.lie_conj f = e.conj f := rfl

@[simp] lemma lie_conj_symm : e.lie_conj.symm = e.symm.lie_conj := rfl

end linear_equiv

namespace alg_equiv

variables {R : Type u} {A₁ : Type v} {A₂ : Type w}
variables [comm_ring R] [ring A₁] [ring A₂] [algebra R A₁] [algebra R A₂]
variables (e : A₁ ≃ₐ[R] A₂)

/-- An equivalence of associative algebras is an equivalence of associated Lie algebras. -/
def to_lie_equiv : A₁ ≃ₗ⁅R⁆ A₂ :=
{ to_fun  := e.to_fun,
  map_lie := λ x y, by simp [lie_ring.of_associative_ring_bracket],
  ..e.to_linear_equiv }

@[simp] lemma to_lie_equiv_apply (x : A₁) : e.to_lie_equiv x = e x := rfl

@[simp] lemma to_lie_equiv_symm_apply (x : A₂) : e.to_lie_equiv.symm x = e.symm x := rfl

end alg_equiv

section matrices
open_locale matrix

variables {R : Type u} [comm_ring R]
variables {n : Type w} [decidable_eq n] [fintype n]

/-! ### Matrices

An important class of Lie algebras are those arising from the associative algebra structure on
square matrices over a commutative ring.
-/

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the Lie algebra structures. -/
def lie_equiv_matrix' : module.End R (n → R) ≃ₗ⁅R⁆ matrix n n R :=
{ map_lie := λ T S,
  begin
    let f := @linear_map.to_matrix' R _ n n _ _ _,
    change f (T.comp S - S.comp T) = (f T) * (f S) - (f S) * (f T),
    have h : ∀ (T S : module.End R _), f (T.comp S) = (f T) ⬝ (f S) := linear_map.to_matrix'_comp,
    rw [linear_equiv.map_sub, h, h, matrix.mul_eq_mul, matrix.mul_eq_mul],
  end,
  ..linear_map.to_matrix' }

@[simp] lemma lie_equiv_matrix'_apply (f : module.End R (n → R)) :
  lie_equiv_matrix' f = f.to_matrix' := rfl

@[simp] lemma lie_equiv_matrix'_symm_apply (A : matrix n n R) :
  (@lie_equiv_matrix' R _ n _ _).symm A = A.to_lin' := rfl

/-- An invertible matrix induces a Lie algebra equivalence from the space of matrices to itself. -/
noncomputable def matrix.lie_conj (P : matrix n n R) (h : is_unit P) :
  matrix n n R ≃ₗ⁅R⁆ matrix n n R :=
((@lie_equiv_matrix' R _ n _ _).symm.trans (P.to_linear_equiv h).lie_conj).trans lie_equiv_matrix'

@[simp] lemma matrix.lie_conj_apply (P A : matrix n n R) (h : is_unit P) :
  P.lie_conj h A = P ⬝ A ⬝ P⁻¹ :=
by simp [linear_equiv.conj_apply, matrix.lie_conj, linear_map.to_matrix'_comp,
         linear_map.to_matrix'_to_lin']

@[simp] lemma matrix.lie_conj_symm_apply (P A : matrix n n R) (h : is_unit P) :
  (P.lie_conj h).symm A = P⁻¹ ⬝ A ⬝ P :=
by simp [linear_equiv.symm_conj_apply, matrix.lie_conj, linear_map.to_matrix'_comp,
         linear_map.to_matrix'_to_lin']

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types is an equivalence of Lie algebras. -/
def matrix.reindex_lie_equiv {m : Type w₁} [decidable_eq m] [fintype m]
  (e : n ≃ m) : matrix n n R ≃ₗ⁅R⁆ matrix m m R :=
{ map_lie := λ M N, by simp only [lie_ring.of_associative_ring_bracket, matrix.reindex_mul,
    matrix.mul_eq_mul, linear_equiv.map_sub, linear_equiv.to_fun_apply],
..(matrix.reindex_linear_equiv e e) }

@[simp] lemma matrix.reindex_lie_equiv_apply {m : Type w₁} [decidable_eq m] [fintype m]
  (e : n ≃ m) (M : matrix n n R) :
  matrix.reindex_lie_equiv e M = λ i j, M (e.symm i) (e.symm j) :=
rfl

@[simp] lemma matrix.reindex_lie_equiv_symm_apply {m : Type w₁} [decidable_eq m] [fintype m]
  (e : n ≃ m) (M : matrix m m R) :
  (matrix.reindex_lie_equiv e).symm M = λ i j, M (e i) (e j) :=
rfl

end matrices

section skew_adjoint_endomorphisms
open bilin_form

variables {R : Type u} {M : Type v} [comm_ring R] [add_comm_group M] [module R M]
variables (B : bilin_form R M)

lemma bilin_form.is_skew_adjoint_bracket (f g : module.End R M)
  (hf : f ∈ B.skew_adjoint_submodule) (hg : g ∈ B.skew_adjoint_submodule) :
  ⁅f, g⁆ ∈ B.skew_adjoint_submodule :=
begin
  rw mem_skew_adjoint_submodule at *,
  have hfg : is_adjoint_pair B B (f * g) (g * f), { rw ←neg_mul_neg g f, exact hf.mul hg, },
  have hgf : is_adjoint_pair B B (g * f) (f * g), { rw ←neg_mul_neg f g, exact hg.mul hf, },
  change bilin_form.is_adjoint_pair B B (f * g - g * f) (-(f * g - g * f)), rw neg_sub,
  exact hfg.sub hgf,
end

/-- Given an `R`-module `M`, equipped with a bilinear form, the skew-adjoint endomorphisms form a
Lie subalgebra of the Lie algebra of endomorphisms. -/
def skew_adjoint_lie_subalgebra : lie_subalgebra R (module.End R M) :=
{ lie_mem := B.is_skew_adjoint_bracket, ..B.skew_adjoint_submodule }

variables {N : Type w} [add_comm_group N] [module R N] (e : N ≃ₗ[R] M)

/-- An equivalence of modules with bilinear forms gives equivalence of Lie algebras of skew-adjoint
endomorphisms. -/
def skew_adjoint_lie_subalgebra_equiv :
  skew_adjoint_lie_subalgebra (B.comp (↑e : N →ₗ[R] M) ↑e) ≃ₗ⁅R⁆ skew_adjoint_lie_subalgebra B :=
begin
  apply lie_algebra.equiv.of_subalgebras _ _ e.lie_conj,
  ext f,
  simp only [lie_subalgebra.mem_coe, submodule.mem_map_equiv, lie_subalgebra.mem_map_submodule,
    coe_coe],
  exact (bilin_form.is_pair_self_adjoint_equiv (-B) B e f).symm,
end

@[simp] lemma skew_adjoint_lie_subalgebra_equiv_apply
  (f : skew_adjoint_lie_subalgebra (B.comp ↑e ↑e)) :
  ↑(skew_adjoint_lie_subalgebra_equiv B e f) = e.lie_conj f :=
by simp [skew_adjoint_lie_subalgebra_equiv]

@[simp] lemma skew_adjoint_lie_subalgebra_equiv_symm_apply (f : skew_adjoint_lie_subalgebra B) :
  ↑((skew_adjoint_lie_subalgebra_equiv B e).symm f) = e.symm.lie_conj f :=
by simp [skew_adjoint_lie_subalgebra_equiv]

end skew_adjoint_endomorphisms

section skew_adjoint_matrices
open_locale matrix

variables {R : Type u} {n : Type w} [comm_ring R] [decidable_eq n] [fintype n]
variables (J : matrix n n R)

lemma matrix.lie_transpose (A B : matrix n n R) : ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆ :=
show (A * B - B * A)ᵀ = (Bᵀ * Aᵀ - Aᵀ * Bᵀ), by simp

lemma matrix.is_skew_adjoint_bracket (A B : matrix n n R)
  (hA : A ∈ skew_adjoint_matrices_submodule J) (hB : B ∈ skew_adjoint_matrices_submodule J) :
  ⁅A, B⁆ ∈ skew_adjoint_matrices_submodule J :=
begin
  simp only [mem_skew_adjoint_matrices_submodule] at *,
  change ⁅A, B⁆ᵀ ⬝ J = J ⬝ -⁅A, B⁆, change Aᵀ ⬝ J = J ⬝ -A at hA, change Bᵀ ⬝ J = J ⬝ -B at hB,
  simp only [←matrix.mul_eq_mul] at *,
  rw [matrix.lie_transpose, lie_ring.of_associative_ring_bracket, lie_ring.of_associative_ring_bracket,
    sub_mul, mul_assoc, mul_assoc, hA, hB, ←mul_assoc, ←mul_assoc, hA, hB],
  noncomm_ring,
end

/-- The Lie subalgebra of skew-adjoint square matrices corresponding to a square matrix `J`. -/
def skew_adjoint_matrices_lie_subalgebra : lie_subalgebra R (matrix n n R) :=
{ lie_mem := J.is_skew_adjoint_bracket, ..(skew_adjoint_matrices_submodule J) }

@[simp] lemma mem_skew_adjoint_matrices_lie_subalgebra (A : matrix n n R) :
  A ∈ skew_adjoint_matrices_lie_subalgebra J ↔ A ∈ skew_adjoint_matrices_submodule J :=
iff.rfl

/-- An invertible matrix `P` gives a Lie algebra equivalence between those endomorphisms that are
skew-adjoint with respect to a square matrix `J` and those with respect to `PᵀJP`. -/
noncomputable def skew_adjoint_matrices_lie_subalgebra_equiv (P : matrix n n R) (h : is_unit P) :
  skew_adjoint_matrices_lie_subalgebra J ≃ₗ⁅R⁆ skew_adjoint_matrices_lie_subalgebra (Pᵀ ⬝ J ⬝ P) :=
lie_algebra.equiv.of_subalgebras _ _ (P.lie_conj h).symm
begin
  ext A,
  suffices : P.lie_conj h A ∈ skew_adjoint_matrices_submodule J ↔
    A ∈ skew_adjoint_matrices_submodule (Pᵀ ⬝ J ⬝ P),
  { simp only [lie_subalgebra.mem_coe, submodule.mem_map_equiv, lie_subalgebra.mem_map_submodule,
      coe_coe], exact this, },
  simp [matrix.is_skew_adjoint, J.is_adjoint_pair_equiv _ _ P h],
end

lemma skew_adjoint_matrices_lie_subalgebra_equiv_apply
  (P : matrix n n R) (h : is_unit P) (A : skew_adjoint_matrices_lie_subalgebra J) :
  ↑(skew_adjoint_matrices_lie_subalgebra_equiv J P h A) = P⁻¹ ⬝ ↑A ⬝ P :=
by simp [skew_adjoint_matrices_lie_subalgebra_equiv]

/-- An equivalence of matrix algebras commuting with the transpose endomorphisms restricts to an
equivalence of Lie algebras of skew-adjoint matrices. -/
def skew_adjoint_matrices_lie_subalgebra_equiv_transpose {m : Type w} [decidable_eq m] [fintype m]
  (e : matrix n n R ≃ₐ[R] matrix m m R) (h : ∀ A, (e A)ᵀ = e (Aᵀ)) :
  skew_adjoint_matrices_lie_subalgebra J ≃ₗ⁅R⁆ skew_adjoint_matrices_lie_subalgebra (e J) :=
lie_algebra.equiv.of_subalgebras _ _ e.to_lie_equiv
begin
  ext A,
  suffices : J.is_skew_adjoint (e.symm A) ↔ (e J).is_skew_adjoint A, by simpa [this],
  simp [matrix.is_skew_adjoint, matrix.is_adjoint_pair, ← matrix.mul_eq_mul,
    ← h, ← function.injective.eq_iff e.injective],
end

@[simp] lemma skew_adjoint_matrices_lie_subalgebra_equiv_transpose_apply
  {m : Type w} [decidable_eq m] [fintype m]
  (e : matrix n n R ≃ₐ[R] matrix m m R) (h : ∀ A, (e A)ᵀ = e (Aᵀ))
  (A : skew_adjoint_matrices_lie_subalgebra J) :
  (skew_adjoint_matrices_lie_subalgebra_equiv_transpose J e h A : matrix m m R) = e A :=
rfl

lemma mem_skew_adjoint_matrices_lie_subalgebra_unit_smul (u : units R) (J A : matrix n n R) :
  A ∈ skew_adjoint_matrices_lie_subalgebra ((u : R) • J) ↔ A ∈ skew_adjoint_matrices_lie_subalgebra J :=
begin
  change A ∈ skew_adjoint_matrices_submodule ((u : R) • J) ↔  A ∈ skew_adjoint_matrices_submodule J,
  simp only [mem_skew_adjoint_matrices_submodule, matrix.is_skew_adjoint, matrix.is_adjoint_pair],
  split; intros h,
  { simpa using congr_arg (λ B, (↑u⁻¹ : R) • B) h, },
  { simp [h], },
end

end skew_adjoint_matrices
