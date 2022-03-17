import order.zorn
open zorn

universes u v

structure incidence_system (X : Type u) (I : Type v) :=
(type : X → I)
(r : X → X → Prop)
(r_is_symm : is_symm X r)
(r_is_refl : is_refl X r)
(eq_of_r_of_type_eq : ∀ ⦃x y⦄, r x y → type x = type y → x = y)

instance {X I} (H : incidence_system X I) : is_symm X H.r :=
H.r_is_symm

instance {X I} (H : incidence_system X I) : is_refl X H.r :=
H.r_is_refl

def flag {X I} (H : incidence_system X I) (f : set X) : Prop :=
chain H.r f ∧ H.type '' f = set.univ

def residue_type {X I} (H : incidence_system X I) (c : set X) : Type :=
{x : X // x ∉ c ∧ ∀ e, e ∈ c → H.r x e}

def residue {X I} (H : incidence_system X I) (c : set X) :
  incidence_system (residue_type H c) (set.compl (H.type '' c)) :=
{ type := λ x, ⟨H.type x.1, λ ⟨y, hy, h⟩, x.2.1 (by rwa H.eq_of_r_of_type_eq (x.2.2 y hy) h.symm)⟩,
  r := subrel H.r _,
  r_is_symm := ⟨λ x y h, by { apply H.r_is_symm.symm, exact h }⟩,
  r_is_refl := ⟨λ x, by apply H.r_is_refl.refl⟩,
  eq_of_r_of_type_eq := λ x y hr ht, subtype.ext_val (H.eq_of_r_of_type_eq hr (subtype.mk.inj ht)) }

class incidence_geometry (X : Type u) (I : Type v) extends incidence_system X I :=
(chain_subset_flag : ∀ c, chain r c → ∃ f, c ⊆ f ∧ chain r f ∧ type '' f = set.univ)
