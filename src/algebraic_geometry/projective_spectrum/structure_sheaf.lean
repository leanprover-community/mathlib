/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.projective_spectrum.topology
import topology.sheaves.local_predicate
import ring_theory.localization.at_prime
import algebraic_geometry.locally_ringed_space

/-!
# The structure sheaf on `projective_spectrum 𝒜`.

In `src/algebraic_geometry/topology.lean`, we have given a topology on `projective_spectrum 𝒜`; in
this file we will construct a sheaf on `projective_spectrum 𝒜`.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ℕ → submodule R A` is the grading of `A`;
- `U` is opposite object of some open subset of `projective_spectrum.Top`.

## Main definitions and results
* `projective_spectrum.Top`: the topological space of `projective_spectrum 𝒜` endowed with the
  zariski topology
* `algebraic_geometry.projective_spectrum.structure_sheaf.homogeneous_localization`: given `x` in
  `projective_spectrum.Top 𝒜`, homogeneous localization at `x` is the subring of `Aₓ` (`A` localized
  at prime `x`) where the numerator and denominator have same grading.

Then we define the structure sheaf as the subsheaf of all dependent function
`f : Π x : U, homogeneous_localization x` such that `f` is locally expressible as ratio of two
elements of the *same grading*, i.e. `∀ y ∈ U, ∃ (V ⊆ U) (i : ℕ) (a b ∈ 𝒜 i), ∀ z ∈ V, f z = a / b`.

* `algebraic_geometry.projective_spectrum.structure_sheaf.is_locally_fraction`: the predicate that
  a dependent function is locally expressible as ration of two elements of the same grading.
* `algebraic_geometry.projective_spectrum.structure_sheaf.sections_subring`: the dependent functions
  satisfying the above local property forms a subring of all dependent functions
  `Π x : U, homogeneous_localization x`.
* `algebraic_geometry.projective_spectrum.structure_sheaf.structure_sheaf`: the sheaf with
  `U ↦ sections_subring U` and natural restriction map.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

noncomputable theory

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise
open direct_sum set_like

variables {R A: Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]

local notation `at ` x := localization.at_prime x.as_homogeneous_ideal.to_ideal

open Top topological_space category_theory opposite

/--
The underlying topology of `Proj` is the projective spectrum of graded ring `A`.
-/
def projective_spectrum.Top : Top := Top.of (projective_spectrum 𝒜)

namespace projective_spectrum.structure_sheaf

namespace homogeneous_localization

open set_like.graded_monoid submodule

variables {𝒜} {x : projective_spectrum.Top 𝒜}

/--
If `x` is a point in `Proj 𝒜`, then `y ∈ Aₓ` is said to satisfy `num_denom_same_deg` if and only if
`y = a / b` where `a` and `b` are both in `𝒜 i` for some `i`.
-/
@[nolint has_inhabited_instance]
structure num_denom_same_deg (y : at x) :=
(num denom : A)
(denom_not_mem : denom ∉ x.as_homogeneous_ideal)
(deg : ℕ)
(num_mem : num ∈ 𝒜 deg)
(denom_mem : denom ∈ 𝒜 deg)
(eq : (localization.mk num ⟨denom, denom_not_mem⟩ : at x) = y)

attribute [simp] num_denom_same_deg.eq

variable (x)
/--
Auxiliary definition of `homogeneous_localization`: its underlying set.
-/
def carrier : set (at x) :=
{y | nonempty (num_denom_same_deg y)}

variable {x}
lemma one_mem' : (1 : at x) ∈ carrier x := nonempty.intro
{ num := 1,
  denom := 1,
  denom_not_mem := (ideal.ne_top_iff_one _).mp x.is_prime.ne_top,
  deg := 0,
  num_mem := one_mem,
  denom_mem := one_mem,
  eq := by simp }

lemma zero_mem' : (0 : at x) ∈ carrier x := nonempty.intro
{ num := 0,
  denom := 1,
  denom_not_mem := (ideal.ne_top_iff_one _).mp x.is_prime.ne_top,
  deg := 0,
  num_mem := zero_mem _,
  denom_mem := one_mem,
  eq := by simp }

lemma mul_mem' {y1 y2} (hy1 : y1 ∈ carrier x) (hy2 : y2 ∈ carrier x) : y1 * y2 ∈ carrier x :=
match hy1, hy2 with
| ⟨c1⟩, ⟨c2⟩ := nonempty.intro
  { num := c1.num * c2.num,
    denom := c1.denom * c2.denom,
    denom_not_mem := λ r, or.elim (x.is_prime.mem_or_mem r) c1.denom_not_mem c2.denom_not_mem,
    deg := c1.deg + c2.deg,
    num_mem := mul_mem c1.num_mem c2.num_mem,
    denom_mem := mul_mem c1.denom_mem c2.denom_mem,
    eq := by simpa only [← c1.eq, ← c2.eq, localization.mk_mul] }
end

lemma add_mem' {y1 y2} (hy1 : y1 ∈ carrier x) (hy2 : y2 ∈ carrier x) : y1 + y2 ∈ carrier x :=
match hy1, hy2 with
| ⟨c1⟩, ⟨c2⟩ := nonempty.intro
  { num := c1.denom * c2.num + c2.denom * c1.num,
    denom := c1.denom * c2.denom,
    denom_not_mem := λ r, or.elim (x.is_prime.mem_or_mem r) c1.denom_not_mem c2.denom_not_mem,
    deg := c1.deg + c2.deg,
    num_mem := add_mem _ (mul_mem c1.denom_mem c2.num_mem)
      (add_comm c2.deg c1.deg ▸ mul_mem c2.denom_mem c1.num_mem),
    denom_mem := mul_mem c1.denom_mem c2.denom_mem,
    eq := by simpa only [← c1.eq, ← c2.eq, localization.add_mk] }
end

lemma neg_mem' {y} (hy : y ∈ carrier x) : -y ∈ carrier x :=
match hy with
| ⟨c⟩ := nonempty.intro
  { num := -c.num,
    denom := c.denom,
    denom_not_mem := c.denom_not_mem,
    deg := c.deg,
    num_mem := neg_mem _ c.num_mem,
    denom_mem := c.denom_mem,
    eq := by simp only [← c.eq, localization.neg_mk] }
end

end homogeneous_localization

section
variable {𝒜}
open homogeneous_localization

/-- given `x` in `projective_spectrum.Top 𝒜`, homogeneous localization at `x` is the subring of `Aₓ`
(`A` localized at prime `x`) where the numerator and denominator have same grading. -/
@[derive [comm_ring], nolint has_inhabited_instance]
def homogeneous_localization (x : projective_spectrum.Top 𝒜) : Type* :=
subring.mk (carrier x) (λ _ _, mul_mem') one_mem' (λ _ _, add_mem') zero_mem'  (λ _, neg_mem')

end

namespace homogeneous_localization
variables {𝒜} {x : projective_spectrum.Top 𝒜}

/-- numerator of an element in `homogeneous_localization x`-/
def num (f : homogeneous_localization x) : A := (nonempty.some f.2).num
/-- denominator of an element in `homogeneous_localization x`-/
def denom (f : homogeneous_localization x) : A := (nonempty.some f.2).denom
/-- For an element in `homogeneous_localization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def deg (f : homogeneous_localization x) : ℕ := (nonempty.some f.2).deg

lemma denom_not_mem (f : homogeneous_localization x) : f.denom ∉ x.as_homogeneous_ideal :=
(nonempty.some f.2).denom_not_mem

lemma num_mem (f : homogeneous_localization x) : f.num ∈ 𝒜 f.deg := (nonempty.some f.2).num_mem
lemma denom_mem (f : homogeneous_localization x) : f.denom ∈ 𝒜 f.deg :=
(nonempty.some f.2).denom_mem

lemma eq_num_div_denom (f : homogeneous_localization x) :
  f.1 = localization.mk f.num ⟨f.denom, f.denom_not_mem⟩ :=
(nonempty.some f.2).eq.symm

lemma val_add (f g : homogeneous_localization x) : (f + g).1 = f.val + g.val := rfl

lemma val_neg (f : homogeneous_localization x) : (-f).val = -f.val := rfl

lemma val_mul (f g : homogeneous_localization x) : (f * g).val = f.val * g.val := rfl

lemma val_sub (f g : homogeneous_localization x) : (f - g).val = f.val - g.val := rfl

lemma val_zero : (0 : homogeneous_localization x).val = localization.mk 0 1 :=
by rw localization.mk_zero; refl

lemma val_one : (1 : homogeneous_localization x).val = localization.mk 1 1 :=
by rw localization.mk_one; refl

lemma ext_iff_val (f g : homogeneous_localization x) : f = g ↔ f.1 = g.1:= subtype.ext_iff_val

end homogeneous_localization

variables {𝒜}

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` of *same grading* in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (projective_spectrum.Top 𝒜)}
  (f : Π x : U, homogeneous_localization x.1) : Prop :=
∃ (r s : A) (i : ℕ) (r_hom : r ∈ 𝒜 i) (s_hom : s ∈ 𝒜 i),
  ∀ x : U, ∃ (s_nin : ¬ (s ∈ x.1.as_homogeneous_ideal)),
  (f x).1 = localization.mk r ⟨s, s_nin⟩

lemma is_fraction.eq_mk' {U : opens (projective_spectrum.Top 𝒜)}
  {f : Π x : U, homogeneous_localization x.1}
  (hf : is_fraction f) :
  ∃ (r s : A) (i : ℕ) (r_hom : r ∈ 𝒜 i) (s_hom : s ∈ 𝒜 i),
    ∀ x : U, ∃ (s_nin : s ∉ x.1.as_homogeneous_ideal),
    (f x).1 = localization.mk r ⟨s, s_nin⟩ :=
begin
  rcases hf with ⟨r, s, i, r_hom, s_hom, h⟩,
  refine ⟨r, s, i, r_hom, s_hom, h⟩,
end

variables (𝒜)

/--
The predicate `is_fraction` is "prelocal", in the sense that if it holds on `U` it holds on any open
subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (@homogeneous_localization _ _ _ _ _ 𝒜 _) :=
{ pred := λ U f, is_fraction f,
  res := by { rintros V U i f ⟨r, s, j, r_hom, s_hom, w⟩,
    refine ⟨r, s, j, r_hom, s_hom, λ y, w (i y)⟩ } }

/--
We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, homogeneous_localization x`
consisting of those functions which can locally be expressed as a ratio of `A` of same grading.-/
def is_locally_fraction : local_predicate ((@homogeneous_localization _ _ _ _ _ 𝒜 _)) :=
(is_fraction_prelocal 𝒜).sheafify

namespace section_subring
variable {𝒜}

open submodule set_like.graded_monoid homogeneous_localization

lemma zero_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  (is_locally_fraction 𝒜).pred (0 : Π x : unop U, homogeneous_localization x.1) :=
λ x, ⟨unop U, x.2, 𝟙 (unop U), ⟨0, 1, 0, zero_mem _, one_mem,
  λ y, ⟨(ideal.ne_top_iff_one _).mp y.1.is_prime.ne_top, by simp⟩⟩⟩

lemma one_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  (is_locally_fraction 𝒜).pred (1 : Π x : unop U, homogeneous_localization x.1) :=
λ x, ⟨unop U, x.2, 𝟙 (unop U), ⟨1, 1, 0, one_mem, one_mem,
  λ y, ⟨(ideal.ne_top_iff_one _).mp y.1.is_prime.ne_top, by simp⟩⟩⟩

lemma add_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ)
  (a b : Π x : unop U, homogeneous_localization x.1)
  (ha : (is_locally_fraction 𝒜).pred a) (hb : (is_locally_fraction 𝒜).pred b) :
  (is_locally_fraction 𝒜).pred (a + b) := λ x,
begin
  rcases ha x with ⟨Va, ma, ia, ra, sa, ja, ra_hom, sa_hom, wa⟩,
  rcases hb x with ⟨Vb, mb, ib, rb, sb, jb, rb_hom, sb_hom, wb⟩,
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, sb * ra + sa * rb, sa * sb, jb + ja,
    submodule.add_mem _ (set_like.graded_monoid.mul_mem sb_hom ra_hom) begin
      rw add_comm,
      apply set_like.graded_monoid.mul_mem sa_hom rb_hom,
    end,
    begin
      rw add_comm,
      apply set_like.graded_monoid.mul_mem sa_hom sb_hom,
    end,
    λ y, ⟨λ h, _, _⟩⟩,
  { have := (y : projective_spectrum.Top 𝒜).is_prime.mem_or_mem h, cases this,
    obtain ⟨nin, hy⟩ := (wa ⟨y, _⟩), apply nin, exact this,
    suffices : y.1 ∈ Va, exact this,
    exact (opens.inf_le_left Va Vb y).2,
    obtain ⟨nin, hy⟩ := (wb ⟨y, _⟩), apply nin, exact this,
    suffices : y.1 ∈ Vb, exact this,
    exact (opens.inf_le_right Va Vb y).2, },
  { simp only [add_mul, ring_hom.map_add, pi.add_apply, ring_hom.map_mul],
    rw val_add,
    obtain ⟨nin1, hy1⟩ := (wa (opens.inf_le_left Va Vb y)),
    obtain ⟨nin2, hy2⟩ := (wb (opens.inf_le_right Va Vb y)),
    convert congr_arg2 (+) hy1 hy2,
    rw [localization.add_mk],
    congr' 1, rw [add_comm], congr' 1, }
end

lemma neg_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ)
  (a : Π x : unop U, homogeneous_localization x.1)
  (ha : (is_locally_fraction 𝒜).pred a) :
  (is_locally_fraction 𝒜).pred (-a) := λ x,
begin
  rcases ha x with ⟨V, m, i, r, s, j, r_hom_j, s_hom_j, w⟩,
  refine ⟨V, m, i, -r, s, j, submodule.neg_mem _ r_hom_j, s_hom_j, λ y, ⟨_, _⟩⟩,
  choose nin hy using w y, exact nin,
  choose nin hy using w y,
  simp only [ring_hom.map_neg, pi.neg_apply],
  rw val_neg,
  rw ←localization.neg_mk,
  erw ←hy,
end

lemma mul_mem' (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ)
  (a b : Π x : unop U, homogeneous_localization x.1)
  (ha : (is_locally_fraction 𝒜).pred a) (hb : (is_locally_fraction 𝒜).pred b) :
  (is_locally_fraction 𝒜).pred (a * b) := λ x,
begin
  rcases ha x with ⟨Va, ma, ia, ra, sa, ja, ra_hom_ja, sa_hom_ja, wa⟩,
  rcases hb x with ⟨Vb, mb, ib, rb, sb, jb, rb_hom_jb, sb_hom_jb, wb⟩,
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * rb, sa * sb,
    ja + jb, set_like.graded_monoid.mul_mem ra_hom_ja rb_hom_jb,
      set_like.graded_monoid.mul_mem sa_hom_ja sb_hom_jb, λ y, ⟨λ h, _, _⟩⟩,
  { have := (y : projective_spectrum.Top 𝒜).is_prime.mem_or_mem h, cases this,
    choose nin hy using wa ⟨y, (opens.inf_le_left Va Vb y).2⟩,
    apply nin, exact this,
    choose nin hy using wb ⟨y, (opens.inf_le_right Va Vb y).2⟩,
    apply nin, exact this, },
  { simp only [pi.mul_apply, ring_hom.map_mul],
    choose nin1 hy1 using wa (opens.inf_le_left Va Vb y),
    choose nin2 hy2 using wb (opens.inf_le_right Va Vb y),
    rw [val_mul],
    convert congr_arg2 (*) hy1 hy2,
    rw [localization.mk_mul], refl, }
end

end section_subring

section

open section_subring

variable {𝒜}
/--
The functions satisfying `is_locally_fraction` form a subring of all dependent functions
`Π x : U, homogeneous_localization x`.
-/
def sections_subring (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  subring (Π x : unop U, homogeneous_localization x.1) :=
{ carrier := { f | (is_locally_fraction 𝒜).pred f },
  zero_mem' := zero_mem' U,
  one_mem' := one_mem' U,
  add_mem' := add_mem' U,
  neg_mem' := neg_mem' U,
  mul_mem' := mul_mem' U, }

end

/--
The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.
-/
def structure_sheaf_in_Type : sheaf Type* (projective_spectrum.Top 𝒜):=
subsheaf_to_Types (is_locally_fraction 𝒜)

instance comm_ring_structure_sheaf_in_Type_obj
  (U : (opens (projective_spectrum.Top 𝒜))ᵒᵖ) :
  comm_ring ((structure_sheaf_in_Type 𝒜).1.obj U) :=
(sections_subring U).to_comm_ring

/--
The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structure_presheaf_in_CommRing : presheaf CommRing (projective_spectrum.Top 𝒜) :=
{ obj := λ U, CommRing.of ((structure_sheaf_in_Type 𝒜).1.obj U),
  map := λ U V i,
  { to_fun := ((structure_sheaf_in_Type 𝒜).1.map i),
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    map_one' := rfl,
    map_mul' := λ x y, rfl, }, }

/--
Some glue, verifying that that structure presheaf valued in `CommRing` agrees
with the `Type` valued structure presheaf.
-/
def structure_presheaf_comp_forget :
  structure_presheaf_in_CommRing 𝒜 ⋙ (forget CommRing) ≅ (structure_sheaf_in_Type 𝒜).1 :=
nat_iso.of_components
  (λ U, iso.refl _)
  (by tidy)

end projective_spectrum.structure_sheaf

namespace projective_spectrum

open Top.presheaf projective_spectrum.structure_sheaf opens

/--
The structure sheaf on `Proj` 𝒜, valued in `CommRing`.
This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def Proj.structure_sheaf : sheaf CommRing (projective_spectrum.Top 𝒜) :=
⟨structure_presheaf_in_CommRing 𝒜,
  -- We check the sheaf condition under `forget CommRing`.
  (is_sheaf_iff_is_sheaf_comp _ _).mpr
    (is_sheaf_of_iso (structure_presheaf_comp_forget 𝒜).symm
      (structure_sheaf_in_Type 𝒜).property)⟩

end projective_spectrum

section

open projective_spectrum projective_spectrum.structure_sheaf opens

@[simp] lemma res_apply (U V : opens (projective_spectrum.Top 𝒜)) (i : V ⟶ U)
  (s : (Proj.structure_sheaf 𝒜).1.obj (op U)) (x : V) :
  ((Proj.structure_sheaf 𝒜).1.map i.op s).1 x = (s.1 (i x) : _) :=
rfl

def Proj.to_SheafedSpace : SheafedSpace CommRing :=
{ carrier := Top.of (projective_spectrum 𝒜),
  presheaf := (Proj.structure_sheaf 𝒜).1,
  is_sheaf := (Proj.structure_sheaf 𝒜).2 }

def open_to_localization (U : opens (projective_spectrum.Top 𝒜)) (x : projective_spectrum.Top 𝒜)
  (hx : x ∈ U) :
  (Proj.structure_sheaf 𝒜).1.obj (op U) ⟶ CommRing.of (homogeneous_localization x) :=
{ to_fun := λ s, (s.1 ⟨x, hx⟩ : _),
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

def stalk_to_fiber_ring_hom (x : projective_spectrum.Top 𝒜) :
  (Proj.structure_sheaf 𝒜).1.stalk x ⟶ CommRing.of (homogeneous_localization x) :=
limits.colimit.desc (((open_nhds.inclusion x).op) ⋙ (Proj.structure_sheaf 𝒜).1)
  { X := _,
    ι :=
    { app := λ U, open_to_localization 𝒜 ((open_nhds.inclusion _).obj (unop U)) x (unop U).2, } }

@[simp] lemma germ_comp_stalk_to_fiber_ring_hom (U : opens (projective_spectrum.Top 𝒜)) (x : U) :
  (Proj.structure_sheaf 𝒜).1.germ x ≫ stalk_to_fiber_ring_hom 𝒜 x =
  open_to_localization 𝒜 U x x.2 :=
limits.colimit.ι_desc _ _

@[simp] lemma stalk_to_fiber_ring_hom_germ' (U : opens (projective_spectrum.Top 𝒜))
  (x : projective_spectrum.Top 𝒜) (hx : x ∈ U) (s : (Proj.structure_sheaf 𝒜).1.obj (op U)) :
  stalk_to_fiber_ring_hom 𝒜 x ((Proj.structure_sheaf 𝒜).1.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
ring_hom.ext_iff.1 (germ_comp_stalk_to_fiber_ring_hom 𝒜 U ⟨x, hx⟩ : _) s

@[simp] lemma stalk_to_fiber_ring_hom_germ (U : opens (projective_spectrum.Top 𝒜)) (x : U)
  (s : (Proj.structure_sheaf 𝒜).1.obj (op U)) :
  stalk_to_fiber_ring_hom 𝒜 x ((Proj.structure_sheaf 𝒜).1.germ x s) = s.1 x :=
by { cases x, exact stalk_to_fiber_ring_hom_germ' 𝒜 U _ _ _ }

lemma homogeneous_localization.mem_basic_open (x) (f : homogeneous_localization x) :
  x ∈ projective_spectrum.basic_open 𝒜 f.denom :=
begin
  rw projective_spectrum.mem_basic_open,
  exact homogeneous_localization.denom_not_mem _,
end

variable (𝒜)

def section_in_basic_open (x : projective_spectrum.Top 𝒜) :
  Π (f : homogeneous_localization x),
    (Proj.structure_sheaf 𝒜).1.obj (op (projective_spectrum.basic_open 𝒜 f.denom)) :=
λ f, ⟨λ y, ⟨localization.mk f.num ⟨f.denom, y.2⟩,
    nonempty.intro ⟨f.num, f.denom, y.2, f.deg, f.num_mem, f.denom_mem, rfl⟩⟩,
  λ y, ⟨projective_spectrum.basic_open 𝒜 f.denom, y.2, 𝟙 _, f.num, f.denom, f.deg,
      f.num_mem, f.denom_mem, λ z, ⟨z.2, rfl⟩⟩⟩

def section_in_basic_open.apply (x : projective_spectrum.Top 𝒜) (f) (y) :
  (section_in_basic_open 𝒜 x f).1 y =
  ⟨localization.mk f.num ⟨f.denom, y.2⟩, _⟩ := rfl

def homogeneous_localization_to_stalk (x : projective_spectrum.Top 𝒜) :
  (homogeneous_localization x) → (Proj.structure_sheaf 𝒜).1.stalk x :=
λ f, (Proj.structure_sheaf 𝒜).1.germ
  (⟨x, homogeneous_localization.mem_basic_open _ x f⟩ : projective_spectrum.basic_open _ f.denom)
  (section_in_basic_open _ x f)

def stalk_iso' (x : projective_spectrum.Top 𝒜) :
  (Proj.structure_sheaf 𝒜).1.stalk x ≃+* CommRing.of (homogeneous_localization x)  :=
ring_equiv.of_bijective (stalk_to_fiber_ring_hom _ x)
⟨λ z1 z2 eq1, begin
  obtain ⟨u1, memu1, s1, rfl⟩ := (Proj.structure_sheaf 𝒜).1.germ_exist x z1,
  obtain ⟨u2, memu2, s2, rfl⟩ := (Proj.structure_sheaf 𝒜).1.germ_exist x z2,
  obtain ⟨v1, memv1, i1, a1, b1, j1, a1_hom, b1_hom, hs1⟩ := s1.2 ⟨x, memu1⟩,
  obtain ⟨v2, memv2, i2, a2, b2, j2, a2_hom, b2_hom, hs2⟩ := s2.2 ⟨x, memu2⟩,
  obtain ⟨b1_nin_x, eq2⟩ := hs1 ⟨x, memv1⟩,
  obtain ⟨b2_nin_x, eq3⟩ := hs2 ⟨x, memv2⟩,
  erw [stalk_to_fiber_ring_hom_germ 𝒜 u1 ⟨x, memu1⟩,
    stalk_to_fiber_ring_hom_germ 𝒜 u2 ⟨x, memu2⟩, subtype.ext_iff_val] at eq1,
  erw eq1 at eq2,
  erw [eq2, localization.mk_eq_mk', is_localization.eq] at eq3,
  obtain ⟨⟨c, hc⟩, eq3⟩ := eq3,
  have eq3' : ∀ (y : projective_spectrum.Top 𝒜)
    (hy : y ∈ projective_spectrum.basic_open 𝒜 b1 ⊓
      projective_spectrum.basic_open 𝒜 b2 ⊓
      projective_spectrum.basic_open 𝒜 c),
    (localization.mk a1
      ⟨b1, show b1 ∉ y.as_homogeneous_ideal,
        by rw ←projective_spectrum.mem_basic_open;
          exact le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_left _ _) hy⟩ : at y) =
    localization.mk a2
      ⟨b2, show b2 ∉ y.as_homogeneous_ideal,
        by rw ←projective_spectrum.mem_basic_open;
        exact le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_right _ _) hy⟩,
  { intros y hy,
    rw [localization.mk_eq_mk', is_localization.eq],
    exact ⟨⟨c, show c ∉ y.as_homogeneous_ideal, by rw ←projective_spectrum.mem_basic_open;
      exact le_of_hom (opens.inf_le_right _ _) hy⟩, eq3⟩ },
  refine presheaf.germ_ext (Proj.structure_sheaf 𝒜).1
    (projective_spectrum.basic_open _ b1 ⊓
      projective_spectrum.basic_open _ b2 ⊓
      projective_spectrum.basic_open _ c ⊓ v1 ⊓ v2)
    ⟨⟨⟨⟨b1_nin_x, b2_nin_x⟩, hc⟩, memv1⟩, memv2⟩
    (opens.inf_le_left _ _ ≫ opens.inf_le_right _ _ ≫ i1) (opens.inf_le_right _ _ ≫ i2) _,
  rw subtype.ext_iff_val,
  ext1 y,
  simp only [res_apply],
  obtain ⟨b1_nin_y, eq6⟩ := hs1 ⟨_, le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_right _ _) y.2⟩,
  obtain ⟨b2_nin_y, eq7⟩ := hs2 ⟨_, le_of_hom (opens.inf_le_right _ _) y.2⟩,
  rw [subtype.ext_iff_val],
  erw [eq6, eq7],
  exact eq3' _ ⟨⟨le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_left _ _ ≫
      opens.inf_le_left _ _ ≫ opens.inf_le_left _ _) y.2,
    le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_left _ _ ≫
      opens.inf_le_left _ _ ≫ opens.inf_le_right _ _) y.2⟩,
    le_of_hom (opens.inf_le_left _ _ ≫ opens.inf_le_left _ _ ≫
      opens.inf_le_right _ _) y.2⟩,
end, function.surjective_iff_has_right_inverse.mpr ⟨homogeneous_localization_to_stalk 𝒜 x,
  λ f, begin
    rw homogeneous_localization_to_stalk,
    erw stalk_to_fiber_ring_hom_germ 𝒜
      (projective_spectrum.basic_open 𝒜 f.denom) ⟨x, _⟩ (section_in_basic_open _ x f),
    rw [section_in_basic_open, subtype.ext_iff_val, f.eq_num_div_denom],
    refl,
  end⟩⟩

def homogeneous_localization.is_local (x : projective_spectrum.Top 𝒜) :
  local_ring (homogeneous_localization x) :=
{ exists_pair_ne := ⟨0, 1, λ rid, begin
    rw [ subtype.ext_iff_val, homogeneous_localization.val_zero, homogeneous_localization.val_one]
      at rid,
    simpa only [localization.mk_eq_mk', is_localization.mk'_eq_iff_eq, mul_one, map_one,
      submonoid.coe_one, zero_ne_one, map_zero] using rid,
  end⟩,
  is_local := λ ⟨a, ha⟩, begin
    induction a using localization.induction_on with r s,
    rcases ha with ⟨r', s', s'_nin, i, r'_hom, s'_hom, eq1⟩,
    by_cases mem1 : r' ∈ x.as_homogeneous_ideal.1,
    { right,
      have : s' - r' ∉ x.as_homogeneous_ideal.1,
      { intro h, apply s'_nin,
        convert submodule.add_mem' _ h mem1, rw sub_add_cancel, },
      apply is_unit_of_mul_eq_one _
        (⟨localization.mk s' ⟨s' - r', this⟩,
        ⟨⟨s', (s' - r'), this, i, s'_hom, (submodule.sub_mem _ s'_hom r'_hom), rfl⟩⟩⟩ :
        homogeneous_localization _),
      rw [sub_mul, subtype.ext_iff_val, homogeneous_localization.val_sub,
        homogeneous_localization.val_mul, homogeneous_localization.val_mul,
        homogeneous_localization.val_one, localization.mk_mul, one_mul, one_mul],
      dsimp only,
      rw [← eq1, localization.mk_mul, sub_eq_add_neg, localization.neg_mk,
        localization.add_mk, ←subtype.val_eq_coe, ←subtype.val_eq_coe,
        show localization.mk 1 1 = (1 : at x), by convert localization.mk_self _; refl],
      dsimp only,
      change localization.mk ((s' - r') * -(r' * s') + s' * (s' - r') * s')
        ⟨(s' - r') * (s' * (s' - r')), _⟩ = 1,
      convert localization.mk_self _,
      simp only [← subtype.val_eq_coe],
      ring },
    { left,
      apply is_unit_of_mul_eq_one _
        (⟨localization.mk s' ⟨r', mem1⟩, ⟨⟨s', r', mem1, i, s'_hom, r'_hom, rfl⟩⟩⟩ :
          homogeneous_localization _),
      rw [subtype.ext_iff_val, homogeneous_localization.val_mul],
      dsimp only,
      rw [← eq1, localization.mk_mul],
      convert localization.mk_self _, rw mul_comm, refl, },
end}

def Proj.to_LocallyRingedSpace : LocallyRingedSpace :=
{ local_ring := λ x, @@ring_equiv.local_ring _
    (show local_ring (homogeneous_localization x), from homogeneous_localization.is_local 𝒜 x) _
    (stalk_iso' 𝒜 x).symm,
  ..(Proj.to_SheafedSpace 𝒜) }

end

end algebraic_geometry
