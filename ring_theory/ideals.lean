/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.module

universe u

class is_ideal {α : Type u} [comm_ring α] (S : set α) extends is_submodule S : Prop

class is_proper_ideal {α : Type u} [comm_ring α] (S : set α) extends is_ideal S : Prop :=
(ne_univ : S ≠ set.univ)

class is_prime_ideal {α : Type u} [comm_ring α] (S : set α) extends is_proper_ideal S : Prop :=
(mem_or_mem_of_mul_mem : ∀ {x y : α}, x * y ∈ S → x ∈ S ∨ y ∈ S)

theorem mem_or_mem_of_mul_eq_zero {α : Type u} [comm_ring α] (S : set α) [is_prime_ideal S] :
  ∀ {x y : α}, x * y = 0 → x ∈ S ∨ y ∈ S :=
λ x y hxy, have x * y ∈ S, by rw hxy; from (@is_submodule.zero α α _ _ S _ : (0:α) ∈ S),
is_prime_ideal.mem_or_mem_of_mul_mem this

class is_maximal_ideal {α : Type u} [comm_ring α] (S : set α) extends is_proper_ideal S : Prop :=
mk' ::
  (eq_or_univ_of_subset : ∀ (T : set α) [is_submodule T], S ⊆ T → T = S ∨ T = set.univ)

theorem is_maximal_ideal.mk {α : Type u} [comm_ring α] (S : set α) [is_submodule S]
  (h₁ : (1:α) ∉ S) (h₂ : ∀ x (T : set α) [is_submodule T], S ⊆ T → x ∉ S → x ∈ T → (1:α) ∈ T) :
  is_maximal_ideal S :=
{ ne_univ              := assume hu, have (1:α) ∈ S, by rw hu; trivial, h₁ this,
  eq_or_univ_of_subset := assume T ht hst, classical.or_iff_not_imp_left.2 $ assume (hnst : T ≠ S),
    let ⟨x, hxt, hxns⟩ := set.exists_of_ssubset ⟨hst, hnst.symm⟩ in
    @@is_submodule.univ_of_one_mem _ T ht $ @@h₂ x T ht hst hxns hxt}

def nonunits (α : Type u) [monoid α] : set α := { x | ¬∃ y, y * x = 1 }

theorem not_unit_of_mem_maximal_ideal {α : Type u} [comm_ring α] (S : set α) [is_maximal_ideal S] :
  S ⊆ nonunits α :=
λ x hx ⟨y, hxy⟩, is_proper_ideal.ne_univ S $ is_submodule.eq_univ_of_contains_unit S x y hx hxy

class local_ring (α : Type u) [comm_ring α] :=
(S : set α)
(max : is_maximal_ideal S)
(unique : ∀ T [is_maximal_ideal T], S = T)

def local_of_nonunits_ideal {α : Type u} [comm_ring α] (hnze : (0:α) ≠ 1)
  (h : ∀ x y ∈ nonunits α, x + y ∈ nonunits α) : local_ring α :=
have hi : is_submodule (nonunits α), from
  { zero_ := λ ⟨y, hy⟩, hnze $ by simpa using hy,
    add_  := h,
    smul  := λ x y hy ⟨z, hz⟩, hy ⟨x * z, by rw [← hz]; simp [mul_left_comm, mul_assoc]⟩ },
{ S      := nonunits α,
  max    := @@is_maximal_ideal.mk _ (nonunits α) hi (λ ho, ho ⟨1, mul_one 1⟩) $
    λ x T ht hst hxns hxt,
    let ⟨y, hxy⟩ := classical.by_contradiction hxns in
    by rw [← hxy]; exact @@is_submodule.smul _ _ ht y hxt,
  unique := λ T hmt, or.cases_on
    (@@is_maximal_ideal.eq_or_univ_of_subset _ hmt (nonunits α) hi $
      λ z hz, @@not_unit_of_mem_maximal_ideal _ T hmt hz)
    id
    (λ htu, false.elim $ ((set.set_eq_def _ _).1 htu 1).2 trivial ⟨1, mul_one 1⟩) }
