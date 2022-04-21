import tactic.ring
import tactic.tidy
import linear_algebra.special_linear_group
import linear_algebra.determinant
import data.matrix.notation
import linear_algebra.matrix
import linear_algebra.general_linear_group
import data.complex.basic


--import .matrix_groups

/-  This is an attempt to update the kbb birthday repo, so most is not orginal to me-/
open finset
open matrix

open_locale matrix

section
universe u

variables (n : Type* )  [decidable_eq n] [fintype n]

def  integral_matrices_with_determinant  (m : ℤ ) :={ A : matrix n n ℤ  // A.det = m }

lemma SLnZ_eq_Mat_1 : (special_linear_group n ℤ) = (integral_matrices_with_determinant n 1):=
begin
refl,
end

variable (m: ℤ)

instance coe_matrix : has_coe (integral_matrices_with_determinant n m) (matrix n n ℤ) :=
⟨λ A, A.val⟩

instance coe_fun : has_coe_to_fun (integral_matrices_with_determinant n m) (λ _, n → n → ℤ) :=
{ coe := λ A, A.val }

def to_lin' (A : integral_matrices_with_determinant n m) := matrix.to_lin' A

namespace integral_matrices_with_determinant

lemma ext_iff (A B :  integral_matrices_with_determinant n m) : A = B ↔ (∀ i j, A i j = B i j) :=
iff.trans subtype.ext_iff_val ⟨(λ h i j, congr_fun (congr_fun h i) j), matrix.ext⟩

@[ext] lemma ext (A B : integral_matrices_with_determinant n m) : (∀ i j, A i j = B i j) → A = B :=
begin
rw ext_iff,
simp,
end


@[simp]lemma mat_m_vals (A : integral_matrices_with_determinant n m): ∀ i j,
A i j = A.1 i j  :=
begin
intros i j, refl,
end

def SLnZ_M (m : ℤ) :
special_linear_group n ℤ → (integral_matrices_with_determinant n  m) → (integral_matrices_with_determinant n m) :=
λ A B, ⟨A.1 ⬝ B.1, by erw [det_mul, A.2, B.2, one_mul]⟩

lemma one_smul'  : ∀ (M: integral_matrices_with_determinant n m ),
  SLnZ_M n m (1:(special_linear_group n ℤ)) M = M :=
begin
rw SLnZ_M,
simp,
end

lemma mul_smul' : ∀ (A B : special_linear_group n ℤ ), ∀ (M: integral_matrices_with_determinant n m ),
 SLnZ_M n  m (A * B ) M= SLnZ_M n m A (SLnZ_M n m B M):=
begin
simp [SLnZ_M],
intros A B M,
simp [matrix.mul_assoc],
end

instance (m: ℤ )  :
mul_action  ( special_linear_group n ℤ) (integral_matrices_with_determinant n  m):=
{ smul := SLnZ_M n (m : ℤ),
  one_smul := one_smul' n (m: ℤ ),
  mul_smul := mul_smul' n (m:ℤ ) }


variables  (A : special_linear_group n ℤ) (M : integral_matrices_with_determinant n m)

@[simp] lemma smul_is_mul (A : special_linear_group n ℤ) (M : integral_matrices_with_determinant n m):
  (A • M).1 =A * M :=
begin
simp [SLnZ_M],
refl,
end

instance : has_coe (integral_matrices_with_determinant n 1) (special_linear_group n ℤ) :=
⟨ λ a, ⟨a.1, a.2⟩⟩

section has_neg

variables  ( B : integral_matrices_with_determinant n m) [fact (even (fintype.card n))]

instance : has_neg (integral_matrices_with_determinant n m) :=
⟨λ g,
  ⟨- g, by {
  have:= det_smul g (-1),
  simp at this,
  rw this,
  simp [nat.neg_one_pow_of_even (fact.out (even (fintype.card n)))],
  have gdet:=g.property,
  simp at gdet,
  exact gdet,}⟩⟩

@[simp] lemma mat_m_coe_neg (g : integral_matrices_with_determinant n m) : ↑(- g) = - (↑g : matrix n n ℤ) :=
rfl

@[simp]lemma mat_m_neg_elt (g : integral_matrices_with_determinant n m):
  ∀ i j, ( ↑(-g): matrix n n ℤ) i j= - (g i j) :=
begin
simp,
end

end has_neg

end integral_matrices_with_determinant


end
