/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import order.basic
import data.equiv.encodable.basic

/-!
# Order ideals, cofinal sets, and the Rasiowa–Sikorski lemma

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `ideal P`: the type of upward directed, downward closed subsets of `P`.
             Dual to the notion of a filter on a preorder.
- `cofinal P`: the type of subsets of `P` containing arbitrarily large elements.
               Dual to the notion of 'dense set' used in forcing.
- `ideal_of_cofinals p 𝒟`, where `p : P`, and `𝒟` is a countable family of cofinal
  subsets of P: an ideal in `P` which contains `p` and intersects every set in `𝒟`.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>
- <https://en.wikipedia.org/wiki/Cofinal_(mathematics)>
- <https://en.wikipedia.org/wiki/Rasiowa%E2%80%93Sikorski_lemma>

Note that for the Rasiowa–Sikorski lemma, Wikipedia uses the opposite ordering on `P`,
in line with most presentations of forcing.

## Tags

ideal, cofinal, dense, countable, generic

-/

namespace order

variables {P : Type*}

/-- An ideal on a preorder `P` is a subset of `P` that is
  - nonempty
  - upward directed
  - downward closed. -/
structure ideal (P) [preorder P] :=
(carrier   : set P)
(nonempty  : carrier.nonempty)
(directed  : directed_on (≤) carrier)
(mem_of_le : ∀ {x y : P}, x ≤ y → y ∈ carrier → x ∈ carrier)

namespace ideal

section preorder
variables [preorder P] {x : P} {I J : ideal P}

/-- The smallest ideal containing a given element. -/
def principal (p : P) : ideal P :=
{ carrier   := { x | x ≤ p },
  nonempty  := ⟨p, le_refl _⟩,
  directed  := λ x hx y hy, ⟨p, le_refl _, hx, hy⟩,
  mem_of_le := λ x y hxy hy, le_trans hxy hy, }

instance [inhabited P] : inhabited (ideal P) :=
⟨ideal.principal $ default P⟩

/-- An ideal of `P` can be viewed as a subset of `P`. -/
instance : has_coe (ideal P) (set P) := ⟨carrier⟩

/-- For the notation `x ∈ I`. -/
instance : has_mem P (ideal P) := ⟨λ x I, x ∈ (I : set P)⟩

/-- Two ideals are equal when their underlying sets are equal. -/
@[ext] lemma ext : ∀ (I J : ideal P), (I : set P) = J → I = J
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ rfl := rfl

/-- The partial ordering by subset inclusion, inherited from `set P`. -/
instance : partial_order (ideal P) := partial_order.lift coe ext

@[trans] lemma mem_of_mem_of_le : x ∈ I → I ≤ J → x ∈ J :=
@set.mem_of_mem_of_subset P x I J

@[simp] lemma principal_le_iff : principal x ≤ I ↔ x ∈ I :=
⟨λ (h : ∀ {y}, y ≤ x → y ∈ I), h (le_refl x),
 λ h_mem y (h_le : y ≤ x), I.mem_of_le h_le h_mem⟩

end preorder

section order_bot
variables [order_bot P] {I : ideal P}

/-- A specific witness of `I.nonempty` when `P` has a bottom element. -/
@[simp] lemma bot_mem : ⊥ ∈ I :=
I.mem_of_le bot_le I.nonempty.some_mem

/-- There is a bottom ideal when `P` has a bottom element. -/
instance : order_bot (ideal P) :=
{ bot := principal ⊥,
  bot_le := by simp,
  .. ideal.partial_order }

end order_bot

/-- There is a top ideal when `P` has a top element. -/
instance {P} [order_top P] : order_top (ideal P) :=
{ top := principal ⊤,
  le_top := λ I x h, le_top,
  .. ideal.partial_order }

section semilattice_sup
variables [semilattice_sup P] {x y : P} {I : ideal P}

/-- A specific witness of `I.directed` when `P` has joins. -/
lemma sup_mem (x y ∈ I) : x ⊔ y ∈ I :=
let ⟨z, h_mem, hx, hy⟩ := I.directed x ‹_› y ‹_› in
I.mem_of_le (sup_le hx hy) h_mem

@[simp] lemma sup_mem_iff : x ⊔ y ∈ I ↔ x ∈ I ∧ y ∈ I :=
⟨λ h, ⟨I.mem_of_le le_sup_left h, I.mem_of_le le_sup_right h⟩,
 λ h, sup_mem x y h.left h.right⟩

end semilattice_sup

section semilattice_sup_bot
variables [semilattice_sup_bot P] (I J K : ideal P)

/-- The intersection of two ideals is an ideal, when `P` has joins and a bottom. -/
def inf (I J : ideal P) : ideal P :=
{ carrier   := I ∩ J,
  nonempty  := ⟨⊥, bot_mem, bot_mem⟩,
  directed  := λ x ⟨_, _⟩ y ⟨_, _⟩, ⟨x ⊔ y, ⟨sup_mem x y ‹_› ‹_›, sup_mem x y ‹_› ‹_›⟩, by simp⟩,
  mem_of_le := λ x y h ⟨_, _⟩, ⟨mem_of_le I h ‹_›, mem_of_le J h ‹_›⟩ }

/-- There is a smallest ideal containing two ideals, when `P` has joins and a bottom. -/
def sup (I J : ideal P) : ideal P :=
{ carrier   := {x | ∃ (i ∈ I) (j ∈ J), x ≤ i ⊔ j},
  nonempty  := ⟨⊥, ⊥, bot_mem, ⊥, bot_mem, bot_le⟩,
  directed  := λ x ⟨xi, _, xj, _, _⟩ y ⟨yi, _, yj, _, _⟩,
    ⟨x ⊔ y,
     ⟨xi ⊔ yi, sup_mem xi yi ‹_› ‹_›,
      xj ⊔ yj, sup_mem xj yj ‹_› ‹_›,
      sup_le
        (calc x ≤ xi ⊔ xj               : ‹_›
         ...    ≤ (xi ⊔ yi) ⊔ (xj ⊔ yj) : sup_le_sup le_sup_left le_sup_left)
        (calc y ≤ yi ⊔ yj               : ‹_›
         ...    ≤ (xi ⊔ yi) ⊔ (xj ⊔ yj) : sup_le_sup le_sup_right le_sup_right)⟩,
     le_sup_left, le_sup_right⟩,
  mem_of_le := λ x y _ ⟨yi, _, yj, _, _⟩, ⟨yi, ‹_›, yj, ‹_›, le_trans ‹x ≤ y› ‹_›⟩ }

lemma sup_le : I ≤ K → J ≤ K → sup I J ≤ K :=
λ hIK hJK x ⟨i, hiI, j, hjJ, hxij⟩,
K.mem_of_le hxij $ sup_mem i j (mem_of_mem_of_le hiI hIK) (mem_of_mem_of_le hjJ hJK)

instance : lattice (ideal P) :=
{ sup          := sup,
  le_sup_left  := λ I J (i ∈ I), ⟨i, ‹_›, ⊥, bot_mem, by simp only [sup_bot_eq]⟩,
  le_sup_right := λ I J (j ∈ J), ⟨⊥, bot_mem, j, ‹_›, by simp only [bot_sup_eq]⟩,
  sup_le       := sup_le,
  inf          := inf,
  inf_le_left  := λ I J, set.inter_subset_left I J,
  inf_le_right := λ I J, set.inter_subset_right I J,
  le_inf       := λ I J K, set.subset_inter,
  .. ideal.partial_order }

@[simp] lemma mem_inf {x : P} : x ∈ I ⊓ J ↔ x ∈ I ∧ x ∈ J := iff_of_eq rfl

@[simp] lemma mem_sup {x : P} : x ∈ I ⊔ J ↔ ∃ (i ∈ I) (j ∈ J), x ≤ i ⊔ j := iff_of_eq rfl

end semilattice_sup_bot

end ideal

/-- For a preorder `P`, `cofinal P` is the type of subsets of `P`
  containing arbitrarily large elements. They are the dense sets in
  the topology whose open sets are terminal segments. -/
structure cofinal (P) [preorder P] :=
(carrier : set P)
(mem_gt  : ∀ x : P, ∃ y ∈ carrier, x ≤ y)

namespace cofinal

variables [preorder P]

instance : inhabited (cofinal P) :=
⟨{ carrier := set.univ, mem_gt := λ x, ⟨x, trivial, le_refl _⟩}⟩

instance : has_mem P (cofinal P) := ⟨λ x D, x ∈ D.carrier⟩

variables (D : cofinal P) (x : P)
/-- A (noncomputable) element of a cofinal set lying above a given element. -/
noncomputable def above : P := classical.some $ D.mem_gt x

lemma above_mem : D.above x ∈ D :=
exists.elim (classical.some_spec $ D.mem_gt x) $ λ a _, a

lemma le_above : x ≤ D.above x :=
exists.elim (classical.some_spec $ D.mem_gt x) $ λ _ b, b

end cofinal

section ideal_of_cofinals

variables [preorder P] (p : P) {ι : Type*} [encodable ι] (𝒟 : ι → cofinal P)

/-- Given a starting point, and a countable family of cofinal sets,
  this is an increasing sequence that intersects each cofinal set. -/
noncomputable def sequence_of_cofinals : ℕ → P
| 0 := p
| (n+1) := match encodable.decode ι n with
           | none   := sequence_of_cofinals n
           | some i := (𝒟 i).above (sequence_of_cofinals n)
           end

lemma sequence_of_cofinals.monotone : monotone (sequence_of_cofinals p 𝒟) :=
by { apply monotone_of_monotone_nat, intros n, dunfold sequence_of_cofinals,
  cases encodable.decode ι n, { refl }, { apply cofinal.le_above }, }

lemma sequence_of_cofinals.encode_mem (i : ι) :
  sequence_of_cofinals p 𝒟 (encodable.encode i + 1) ∈ 𝒟 i :=
by { dunfold sequence_of_cofinals, rw encodable.encodek, apply cofinal.above_mem, }

/-- Given an element `p : P` and a family `𝒟` of cofinal subsets of a preorder `P`,
  indexed by a countable type, `ideal_of_cofinals p 𝒟` is an ideal in `P` which
  - contains `p`, according to `mem_ideal_of_cofinals p 𝒟`, and
  - intersects every set in `𝒟`, according to `cofinal_meets_ideal_of_cofinals p 𝒟`.

  This proves the Rasiowa–Sikorski lemma. -/
def ideal_of_cofinals : ideal P :=
{ carrier   := { x : P | ∃ n, x ≤ sequence_of_cofinals p 𝒟 n },
  nonempty  := ⟨p, 0, le_refl _⟩,
  directed  := λ x ⟨n, hn⟩ y ⟨m, hm⟩,
               ⟨_, ⟨max n m, le_refl _⟩,
               le_trans hn $ sequence_of_cofinals.monotone p 𝒟 (le_max_left _ _),
               le_trans hm $ sequence_of_cofinals.monotone p 𝒟 (le_max_right _ _) ⟩,
  mem_of_le := λ x y hxy ⟨n, hn⟩, ⟨n, le_trans hxy hn⟩, }

lemma mem_ideal_of_cofinals : p ∈ ideal_of_cofinals p 𝒟 := ⟨0, le_refl _⟩

/-- `ideal_of_cofinals p 𝒟` is `𝒟`-generic. -/
lemma cofinal_meets_ideal_of_cofinals (i : ι) : ∃ x : P, x ∈ 𝒟 i ∧ x ∈ ideal_of_cofinals p 𝒟 :=
⟨_, sequence_of_cofinals.encode_mem p 𝒟 i, _, le_refl _⟩

end ideal_of_cofinals

end order
