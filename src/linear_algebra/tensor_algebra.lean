import ring_theory.algebra
import linear_algebra

universes u1 u2 u3

variables (R : Type u1) [comm_ring R]
variables (M : Type u2) [add_comm_group M] [module R M]

namespace tensor_algebra

inductive pre
| of : M → pre
| zero : pre
| one : pre
| mul : pre → pre → pre
| add : pre → pre → pre
| smul : R → pre → pre

namespace pre

def has_coe : has_coe M (pre R M) := ⟨of⟩
def has_mul : has_mul (pre R M) := ⟨mul⟩
def has_add : has_add (pre R M) := ⟨add⟩
def has_zero : has_zero (pre R M) := ⟨zero⟩
def has_one : has_one (pre R M) := ⟨one⟩
def has_scalar : has_scalar R (pre R M) := ⟨smul⟩
def has_neg : has_neg (pre R M) := ⟨smul (-1 : R)⟩

end pre

local attribute [instance] pre.has_coe
local attribute [instance] pre.has_mul
local attribute [instance] pre.has_add
local attribute [instance] pre.has_zero
local attribute [instance] pre.has_one
local attribute [instance] pre.has_scalar
local attribute [instance] pre.has_neg

def lift_fun {A : Type u3} [ring A] [algebra R A] (f : M →ₗ[R] A) : pre R M → A :=
  λ t, pre.rec_on t f 0 1 (λ _ _, (*)) (λ _ _, (+)) (λ x _ a, x • a)

inductive rel : (pre R M) → (pre R M) → Prop
-- force of to be linear
| add_lin {a b : M} : rel ↑(a + b) (↑a + ↑b)
| smul_lin {r : R} {a : M} : rel ↑(r • a) (r • ↑a)
| zero_lin : rel ↑(0 : M) 0
-- add gives a commutative group
| add_assoc {a b c : pre R M} : rel (a + b + c) (a + (b + c))
| add_comm {a b : pre R M} : rel (a + b) (b + a)
| neg_add {a : pre R M} : rel (-a + a) 0
| zero_add {a : pre R M} : rel (0 + a) a
-- mul gives a monoid
| mul_assoc {a b c : pre R M} : rel (a * b * c) (a * (b * c))
| one_mul {a : pre R M} : rel (1 * a) a
| mul_one {a : pre R M} : rel (a * 1) a
-- distributivity
| left_distrib {a b c : pre R M} : rel (a * (b + c)) (a * b + a * c)
| right_distrib {a b c : pre R M} : rel ((a + b) * c) (a * c + b * c)
-- algebra structure
| map_one : rel ((1 : R) • (1 : pre R M)) 1
| map_mul {r s : R} : rel ((r * s) • 1) ((r • (1 : pre R M)) * (s • 1))
| map_add {r s : R} : rel ((r + s) • (1 : pre R M)) (r • 1 + s • 1)
| map_zero : rel ((0 : R) • (1 : pre R M)) 0
| commutes {r : R} {a : pre R M} : rel ((r • (1 : pre R M)) * a) (a * (r • 1))
| smul_def {r : R} {a : pre R M} : rel (r • a) ((r • 1) * a)
-- compatibility
| mul_compat_left {a b c : pre R M} : rel a b → rel (a * c) (b * c)
| mul_compat_right {a b c : pre R M} : rel a b → rel (c * a) (c * b)
| add_compat_left {a b c : pre R M} : rel a b → rel (a + c) (b + c)
| add_compat_right {a b c : pre R M} : rel a b → rel (c + a) (c + b)
| smul_compat {r : R} {a b : pre R M} : rel a b → rel (r • a) (r • b)

end tensor_algebra

def tensor_algebra := quot (tensor_algebra.rel R M)

namespace tensor_algebra

local attribute [instance] pre.has_coe
local attribute [instance] pre.has_mul
local attribute [instance] pre.has_add
local attribute [instance] pre.has_zero
local attribute [instance] pre.has_one
local attribute [instance] pre.has_scalar
local attribute [instance] pre.has_neg

instance : ring (tensor_algebra R M) :=
{ add := λ a b, quot.lift_on a (λ x, quot.lift_on b (λ y, quot.mk (rel R M) (x + y))
  begin
    intros a b h,
    dsimp only [],
    apply quot.sound,
    apply rel.add_compat_right h,
  end)
  begin
    intros a b h,
    dsimp only [],
    congr,
    ext,
    apply quot.sound,
    apply rel.add_compat_left h,
  end,
  add_assoc := λ a b c,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quot.sound,
    apply rel.add_assoc,
  end,
  zero := quot.mk _ 0,
  zero_add := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quot.sound,
    apply rel.zero_add,
  end,
  add_zero := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    change quot.mk _ _ = _,
    rw quot.sound rel.add_comm,
    apply quot.sound,
    apply rel.zero_add,
  end,
  neg := λ a, quot.lift_on a (λ x, quot.mk _ $ (-x))
  begin
    intros a b h,
    dsimp only [],
    apply quot.sound,
    apply rel.smul_compat h,
  end,
  add_left_neg := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quot.sound,
    apply rel.neg_add,
  end,
  add_comm := λ a b,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    apply quot.sound,
    apply rel.add_comm,
  end,
  mul := λ a b, quot.lift_on a (λ x, quot.lift_on b (λ y, quot.mk _ (x * y))
  begin
    intros a b h,
    dsimp only [],
    apply quot.sound,
    apply rel.mul_compat_right h,
  end)
  begin
    intros a b h,
    dsimp only [],
    congr,
    ext,
    apply quot.sound,
    apply rel.mul_compat_left h,
  end,
  mul_assoc := λ a b c,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quot.sound,
    apply rel.mul_assoc,
  end,
  one := quot.mk _ 1,
  one_mul := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quot.sound,
    apply rel.one_mul,
  end,
  mul_one := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quot.sound,
    apply rel.mul_one,
  end,
  left_distrib := λ a b c,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quot.sound,
    apply rel.left_distrib,
  end,
  right_distrib := λ a b c,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quot.sound,
    apply rel.right_distrib,
  end }

instance : has_scalar R (tensor_algebra R M) :=
{ smul := λ r a, quot.lift_on a (λ x, quot.mk _ $ r • x)
begin
  intros a b h,
  dsimp only [],
  apply quot.sound,
  apply rel.smul_compat h,
end }

instance : algebra R (tensor_algebra R M) :=
{ to_fun := λ r, r • 1,
  map_one' := by apply quot.sound; apply rel.map_one,
  map_mul' := λ a b, by apply quot.sound; apply rel.map_mul,
  map_zero' := by apply quot.sound; apply rel.map_zero,
  map_add' := λ a b, by apply quot.sound; apply rel.map_add,
  commutes' := λ r x,
  begin
    dsimp only [],
    rcases quot.exists_rep x with ⟨x,rfl⟩,
    apply quot.sound,
    apply rel.commutes,
  end,
  smul_def' := λ r x,
  begin
    dsimp only [],
    rcases quot.exists_rep x with ⟨x,rfl⟩,
    apply quot.sound,
    apply rel.smul_def,
  end }

def univ : M →ₗ[R] (tensor_algebra R M) :=
{ to_fun := λ m, quot.mk _ m,
  map_add' := λ x y, by apply quot.sound; apply rel.add_lin,
  map_smul' := λ r x, by apply quot.sound; apply rel.smul_lin }

def lift {A : Type u3} [ring A] [algebra R A] (f : M →ₗ[R] A) : tensor_algebra R M →ₐ[R] A :=
{ to_fun := λ a, quot.lift_on a (lift_fun _ _ f) $ λ a b h,
  begin
    induction h,
    { change f _ = f _ + f _, rw linear_map.map_add },
    { change f _ = _ • f _, rw linear_map.map_smul },
    { change f _ = _, rw linear_map.map_zero, refl },
    { change _ + _ + _ = _ + (_ + _), rw add_assoc },
    { change _ + _ = _ + _, rw add_comm, },
    { change (-1 : R) • _ + _ = (0 : A),
      rw [neg_one_smul, neg_add_self] },
    { change (0 : A) + _ = _, rw zero_add, refl },
    { change _ * _ * _ = _ * (_ * _), rw mul_assoc },
    { change (1 : A) * _ = _, rw one_mul, refl },
    { change _ * (1 : A) = _, rw mul_one, refl },
    { change _ * ( _ + _ ) = _, rw left_distrib, refl },
    { change (_ + _) * _ = _, rw right_distrib, refl },
    { change (1 : R) • (1 : A) = _, rw one_smul, refl },
    { change (_ * _) • (1 : A) = (_ • (1 : A)) * (_ • (1 : A)),
      simp only [mul_one, algebra.mul_smul_comm, algebra.smul_mul_assoc, mul_smul] },
    { change (_ + _) • (1 : A) = _ + _, rw add_smul, refl },
    { change (0 : R) • (1 : A) = 0, simp, },
    { change (_ • (1 : A)) * _ = _ * (_ • (1 : A)), simp },
    { change _ • _ = (_ • (1 : A)) * _, simp },
    repeat { let G := lift_fun R M f, change G _ * G _ = G _ * G _, simp only * },
    repeat { let G := lift_fun R M f, change G _ + G _ = G _ + G _, simp only * },
    { let G := lift_fun R M f, change _ • G _ = _ • G _, simp only * },
  end,
  map_one' := rfl,
  map_mul' :=
  begin
    intros x y,
    rcases quot.exists_rep x with ⟨x,rfl⟩,
    rcases quot.exists_rep y with ⟨y,rfl⟩,
    refl,
  end,
  map_zero' := rfl,
  map_add' :=
  begin
    intros x y,
    rcases quot.exists_rep x with ⟨x,rfl⟩,
    rcases quot.exists_rep y with ⟨y,rfl⟩,
    refl,
  end,
  commutes' :=
  begin
    intros r,
    have : algebra_map R A r = r • (1 : A), by refine algebra.algebra_map_eq_smul_one r,
    rw this, clear this,
    refl,
  end }

theorem univ_comp_lift {A : Type u3} [ring A] [algebra R A] (f : M →ₗ[R] A) :
  (lift R M f) ∘ (univ R M) = f := rfl

theorem lift_unique {A : Type u3} [ring A] [algebra R A] (f : M →ₗ[R] A)
  (g : tensor_algebra R M →ₐ[R] A) : g ∘ (univ R M) = f → g = lift R M f :=
begin
  intro hyp,
  ext,
  rcases quot.exists_rep x with ⟨x,rfl⟩,
  let G := lift_fun R M f,
  induction x,
  { change (g ∘ (univ R M)) _ = _,
    rw hyp,
    refl },
  { change g 0 = 0,
    exact alg_hom.map_zero g },
  { change g 1 = 1,
    exact alg_hom.map_one g },
  { change g (quot.mk _ x_a * quot.mk _ x_a_1) = _,
    rw alg_hom.map_mul,
    rw x_ih_a, rw x_ih_a_1,
    refl },
  { change g (quot.mk _ x_a + quot.mk _ x_a_1) = _,
    rw alg_hom.map_add,
    rw x_ih_a, rw x_ih_a_1,
    refl },
  { change g (x_a • quot.mk _ x_a_1 ) = _,
    rw alg_hom.map_smul,
    rw x_ih, refl },
end

end tensor_algebra
