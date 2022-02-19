/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import model_theory.finitely_generated
import model_theory.direct_limit
import category_theory.concrete_category.bundled

/-!
# Fraïssé Classes and Fraïssé Limits
This file pertains to the ages of countable first-order structures. The age of a structure is the
class of all finitely-generated structures that embed into it.

Of particular interest are Fraïssé classes, which are exactly the ages of countable
weakly-homogeneous structures. To each is associated a unique (up to nonunique isomorphism)
Fraïssé limit - the countable structure with that age.

## Main Definitions
* `first_order.language.equiv_setoid` is the equivalence relation on bundled `L.Structure`s
indicating that they are isomorphic. Its quotients represent isomorphism classes of structures.
* `first_order.language.is_equiv_invariant_class` indicates that a class of structures is invariant
under isomorphism.
* `first_order.language.is_equiv_invariant_class.to_set_quotient` allows us to view an
isomorphism-invariant class as a set of isomorphism classes.
* `first_order.language.age` is the class of finitely-generated structures that embed into a
particular structure.
* A class `K` has the `first_order.language.hereditary_property` when all finitely-generated
structures that embed into structures in `K` are also in `K`.
* A class `K` has the `first_order.language.joint_embedding_property` when for every `M`, `N` in
`K`, there is another structure in `K` into which both `M` and `N` embed.
* A class `K` has the `first_order.language.amalgamation_property` when for any pair of embeddings
of a structure `M` in `K` into other structures in `K`, those two structures can be embedded into a
fourth structure in `K` such that the resulting square of embeddings commutes.

## Main Results
* We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
joint-embedding properties.
* `first_order.language.age.countable_quotient` shows that the age of any countable structure is
essentially countable.
* `first_order.language.exists_cg_is_age_of` constructs a countably-generated structure with a
particular age.


## Implementation Notes
* Classes of structures are formalized with the type `Π (M : Type w) [L.Structure M], Prop`, as this
is the form that predicates such as `Structure.fg L` take in the rest of the library.
* Some results pertain to countable limit structures, others to countably-generated limit
structures. In the case of a language with countably many function symbols, these are equivalent.

## TODO
* Define weakly homogeneous structures
* Show that any two Fraïssé limits of a Fraïssé class are isomorphic
* Show that any Fraïssé limit is weakly homogeneous
* Show that the age of any weakly homogeneous countable structure is Fraïssé

-/

universes u v w w'

open_locale first_order
open set category_theory

namespace first_order
namespace language
open Structure substructure

variables (L : language.{u v})

/-! ### Isomorphism-Invariant Classes and Essential Countability -/

@[protected] instance category_theory.bundled.Structure (M : bundled L.Structure) :
  L.Structure M :=
M.str

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
instance equiv_setoid : setoid (bundled L.Structure) :=
{ r := λ M N, nonempty (M ≃[L] N),
  iseqv := ⟨λ M, ⟨equiv.refl L M⟩, λ M N, nonempty.map equiv.symm,
    λ M N P, nonempty.map2 (λ MN NP, NP.comp MN)⟩ }

variables {L} (K : Π (M : Type w) [L.Structure M], Prop)

/-- A class `K` is isomorphism-invariant when structure isomorphic to a structure in `K` is also in
  `K`. -/
def is_equiv_invariant_class : Prop :=
∀ (M N : Type w) [strM : L.Structure M] [strN : L.Structure N],
  nonempty (@equiv L M N strM strN) → (@K M strM = @K N strN)

variables {K}

/-- An isomorphism-invariant class can also be thought of as a set of isomorphism classes. -/
def is_equiv_invariant_class.to_set_quotient (h : is_equiv_invariant_class K) :
  set (quotient L.equiv_setoid) :=
{ M | quotient.lift (λ (M : bundled L.Structure), K M) (λ M N MN, h M N MN) M }

@[simp]
lemma is_equiv_invariant_class.mk_mem_to_set_quotient (h : is_equiv_invariant_class K)
  (M : bundled L.Structure) :
  (⟦M⟧ : quotient L.equiv_setoid) ∈ h.to_set_quotient ↔ K M :=
by rw [is_equiv_invariant_class.to_set_quotient, set.mem_set_of_eq, quotient.lift_mk]

/-- If `K` is a nonempty but essentially countable class of structures, there is a family of
  structures in `K`, indexed by `ℕ`, that covers every isomorphism class. -/
lemma exists_nat_transversal_of_countable_quotient (hn : K ≠ λ _ _, false)
  (h : is_equiv_invariant_class K) (hc : h.to_set_quotient.countable) :
  ∃ (f : ℕ → bundled.{w} L.Structure), ∀ (M : Type w) [strM : L.Structure M],
    @K M strM ↔ ∃ (n : ℕ), nonempty (@equiv L M (f n) strM _) :=
begin
  have hne : h.to_set_quotient.nonempty,
  { simp_rw [ne.def, function.funext_iff, not_forall, eq_iff_iff, iff_false, not_not] at hn,
    obtain ⟨M, strM, hM⟩ := hn,
    exact ⟨⟦⟨M, strM⟩⟧, hM⟩ },
  obtain ⟨f, hf⟩ := hc.exists_surjective hne,
  refine ⟨quotient.out ∘ f, λ M strM, _⟩,
  rw [is_equiv_invariant_class.to_set_quotient, set.ext_iff] at hf,
  have hfM := hf ⟦⟨M, strM⟩⟧,
  rw [mem_range, mem_set_of_eq, quotient.lift_mk] at hfM,
  simp_rw [quotient.eq_mk_iff_out] at hfM,
  exact hfM.trans (exists_congr (λ n, ⟨setoid.symm, λ h, setoid.symm h⟩)),
end

/-! ### The Age of a Structure and Fraïssé Classes-/

variables (L)

/-- The age of a structure `M` is the class of finitely-generated structures that embed into it. -/
def age (M : Type w) [L.Structure M] (N : Type w) [L.Structure N] : Prop :=
Structure.fg L N ∧ nonempty (N ↪[L] M)

variables {L} (K)

/-- A class `K` has the hereditary property when all finitely-generated structures that embed into
  structures in `K` are also in `K`.  -/
def hereditary_property : Prop :=
∀ (M N : Type w) [strM : L.Structure M] [strN : L.Structure N],
  nonempty (@embedding L M N strM strN) → @Structure.fg L M strM → @K N strN → @K M strM

/-- A class `K` has the joint embedding property when for every `M`, `N` in `K`, there is another
  structure in `K` into which both `M` and `N` embed. -/
def joint_embedding_property : Prop :=
∀ (M N : Type w) [strM : L.Structure M] [strN : L.Structure N], @K M strM → @K N strN →
  ∃ (P : Type w) [strP : L.Structure P],
  @K P strP ∧ nonempty (@embedding L M P strM strP) ∧ nonempty (@embedding L N P strN strP)

/-- A class `K` has the amalgamation property when for any pair of embeddings of a structure `M` in
  `K` into other structures in `K`, those two structures can be embedded into a fourth structure in
  `K` such that the resulting square of embeddings commutes. -/
def amalgamation_property : Prop :=
∀ (M N P : Type w) [strM : L.Structure M] [strN : L.Structure N] [strP : L.Structure P]
  (MN : @embedding L M N strM strN) (MP : @embedding L M P strM strP),
  @K M strM → @K N strN → @K P strP →
  ∃ (Q : Type w) [strQ : L.Structure Q] (NQ : @embedding L N Q strN strQ)
    (PQ : @embedding L P Q strP strQ), @K Q strQ ∧
    (@embedding.comp L M N strM strN Q strQ NQ MN) = (@embedding.comp L M P strM strP Q strQ PQ MP)

/-- A Fraïssé class is a nonempty, isomorphism-invariant, essentially countable class of structures
satisfying the hereditary, joint embedding, and amalgamation properties. -/
class is_fraisse_class : Prop :=
(is_nonempty : K ≠ λ _ _, false)
(fg : K ≤ Structure.fg L)
(is_equiv_invariant : is_equiv_invariant_class K)
(is_essentially_countable : is_equiv_invariant.to_set_quotient.countable)
(hp : hereditary_property K)
(jep : joint_embedding_property K)
(ap : amalgamation_property K)

variables {K}

lemma Structure.fg.is_equiv_invariant_class : is_equiv_invariant_class (Structure.fg L) :=
begin
  rintro N P strN strP ⟨NP⟩,
  resetI,
  exact iff_iff_eq.1 NP.fg_iff,
end

variables (L) (M : Type w) [L.Structure M]

lemma age.is_equiv_invariant : is_equiv_invariant_class (L.age M) :=
begin
  rintro N P strN strP ⟨NP⟩,
  resetI,
  exact iff_iff_eq.1 (and_congr NP.fg_iff
    ⟨nonempty.map (λ x, embedding.comp x NP.symm.to_embedding),
    nonempty.map (λ x, embedding.comp x NP.to_embedding)⟩),
end

variable {L}

lemma age.hp : hereditary_property (L.age M) :=
begin
  rintro N P strN strP ⟨NP⟩ Nfg ⟨h1, h2⟩,
  resetI,
  exact ⟨Nfg, nonempty.map (λ x, embedding.comp x NP) h2⟩,
end

lemma age.jep : joint_embedding_property (L.age M) :=
begin
  rintro N P strN strP ⟨Nfg, ⟨NM⟩⟩ ⟨Pfg, ⟨PM⟩⟩,
  resetI,
  refine ⟨↥(NM.to_hom.range ⊔ PM.to_hom.range), infer_instance, ⟨_, ⟨subtype _⟩⟩,
    ⟨_⟩, ⟨_⟩⟩,
  { rw ← fg_iff_Structure_fg,
    exact (Nfg.range NM.to_hom).sup (Pfg.range PM.to_hom) },
  { exact embedding.comp (inclusion le_sup_left) NM.equiv_range.to_embedding },
  { exact embedding.comp (inclusion le_sup_right) PM.equiv_range.to_embedding },
end

/-- The age of a countable structure is essentially countable (has countably many isomorphism
classes). -/
lemma age.countable_quotient (h : (univ : set M).countable) :
  (age.is_equiv_invariant L M).to_set_quotient.countable :=
begin
  refine eq.mp (congr rfl (set.ext _)) ((countable_set_of_finite_subset h).image
    (λ s, ⟦⟨closure L s, infer_instance⟩⟧)),
  rw forall_quotient_iff,
  rintro ⟨N, str⟩,
  simp only [subset_univ, and_true, mem_image, is_equiv_invariant_class.mk_mem_to_set_quotient],
  split,
  { rintro ⟨s, hs1, hs2⟩,
    rw ← age.is_equiv_invariant L M _ _ (quotient.exact hs2),
    exact ⟨(fg_iff_Structure_fg _).1 (fg_closure hs1),
      ⟨subtype _⟩⟩ },
  { rintro ⟨⟨s, hs⟩, ⟨NM⟩⟩,
    refine ⟨NM '' s, set.finite.image NM s.finite_to_set, quotient.sound ⟨equiv.symm _⟩⟩,
    have h := closure_image NM.to_hom,
    simp only [embedding.coe_to_hom] at h,
    rw [h, hs, ← hom.range_eq_map],
    exact NM.equiv_range }
end

/-- The age of a direct limit of structures is the union of the ages of the structures. -/
@[simp] theorem age_direct_limit {ι : Type w} [preorder ι]
  [is_directed ι (≤)] [nonempty ι]
  (G : ι → Type (max w w')) [Π i, L.Structure (G i)]
  (f : Π i j, i ≤ j → G i ↪[L] G j) [directed_system G (λ i j h, f i j h)]
  (M : Type (max w w')) [L.Structure M] :
  L.age (direct_limit G f) M ↔ ∃ (i : ι), L.age (G i) M :=
begin
  classical,
  split,
  { rintro ⟨Mfg, ⟨e⟩⟩,
    obtain ⟨s, hs⟩ := Mfg.range e.to_hom,
    let out := @quotient.out _ (direct_limit.setoid G f),
    obtain ⟨i, hi⟩ := finset.exists_le (s.image (sigma.fst ∘ out)),
    have e' := ((direct_limit.of L ι G f i).equiv_range.symm.to_embedding),
    refine ⟨i, Mfg, ⟨e'.comp ((substructure.inclusion _).comp e.equiv_range.to_embedding)⟩⟩,
    rw [← hs, closure_le],
    intros x hx,
    refine ⟨f (out x).1 i (hi (out x).1 (finset.mem_image_of_mem _ hx)) (out x).2, _⟩,
    simp only [directed_system.nat.coe_to_step_of_le, eq_mpr_eq_cast, cast_cast,
      embedding.coe_to_hom, direct_limit.of_apply],
    rw [quotient.mk_eq_iff_out, direct_limit.equiv_iff G f _
      (hi (out x).1 (finset.mem_image_of_mem _ hx)), directed_system.map_self];
    refl },
  { rintro ⟨i, Mfg, ⟨e⟩⟩,
    exact ⟨Mfg, ⟨embedding.comp (direct_limit.of L ι G f i) e⟩⟩ }
end

/-- The direct limit of countably many countably generated structures is countably generated. -/
theorem cg_direct_limit {ι : Type*} [encodable ι] [preorder ι] [is_directed ι (≤)] [nonempty ι]
  {G : ι → Type w} [Π i, L.Structure (G i)]
  (f : Π i j, i ≤ j → G i ↪[L] G j) (h : ∀ i, Structure.cg L (G i))
  [directed_system G (λ i j h, f i j h)] :
  Structure.cg L (direct_limit G f) :=
begin
  refine ⟨⟨⋃ i, direct_limit.of L ι G f i '' (classical.some (h i).out), _, _⟩⟩,
  { exact set.countable_Union (λ i, set.countable.image (classical.some_spec (h i).out).1 _) },
  { rw [eq_top_iff, closure_Union],
    simp_rw [← embedding.coe_to_hom, closure_image],
    rw le_supr_iff,
    intros S hS x hx,
    let out := @quotient.out _ (direct_limit.setoid G f),
    refine hS (out x).1 ⟨(out x).2, _, _⟩,
    { rw [(classical.some_spec (h (out x).1).out).2],
      simp only [coe_top] },
    { simp only [embedding.coe_to_hom, direct_limit.of_apply, sigma.eta, quotient.out_eq] } }
end

/-- Sufficient conditions for a class to be the age of a countably-generated structure. -/
theorem exists_cg_is_age_of (hn : K ≠ λ _ _, false)
  (h : is_equiv_invariant_class K)
  (hc : h.to_set_quotient.countable)
  (fg : K ≤ Structure.fg L)
  (hp : hereditary_property K)
  (jep : joint_embedding_property K) :
  ∃ (M : bundled L.Structure), Structure.cg L M ∧ L.age M = K :=
begin
  obtain ⟨F, hF⟩ := exists_nat_transversal_of_countable_quotient hn h hc,
  have hj := λ (N : {N : (bundled L.Structure) // K N}) (n : ℕ), jep N (F (n + 1)) N.2
    ((hF (F (n + 1))).2 ⟨n + 1, ⟨equiv.refl _ _⟩⟩),
  set G : ℕ → {N : (bundled L.Structure) // K N} :=
    @nat.rec (λ _, {N : (bundled L.Structure) // K N}) (⟨F 0, (hF (F 0)).2 ⟨0, ⟨equiv.refl _ _⟩⟩⟩)
    (λ n N, _) with hG,
  swap,
  { exact ⟨⟨classical.some (hj N n), classical.some (classical.some_spec (hj N n))⟩,
      (classical.some_spec (classical.some_spec (hj N n))).1⟩ },
  let f : Π (i j), i ≤ j → G i ↪[L] G j :=
    directed_system.nat.to_step_of_le (λ n, _), swap,
  { rw [hG, nat.rec_add_one, ← hG],
    exact (classical.some_spec (classical.some_spec (hj _ n))).2.1.some },
  refine ⟨⟨direct_limit (λ n, G n) f, infer_instance⟩,
    cg_direct_limit _ (λ n, (fg _ _ (G n).2).cg), _⟩,
  ext N str,
  resetI,
  refine ⟨λ h, _, λ KN, _⟩,
  { obtain ⟨i, h1, h2⟩ := (age_direct_limit (λ n, G n) f N).1 h,
    exact hp N (G i) h2 h.1 (G i).2, },
  { obtain ⟨n, ⟨e⟩⟩ := (hF N).1 KN,
    refine ⟨fg _ _ KN, ⟨embedding.comp _ e.to_embedding⟩⟩,
    cases n,
    { exact (direct_limit.of L ℕ (λ n, G n) f 0).comp (embedding.refl _ _) },
    refine (direct_limit.of L ℕ (λ n, G n) f (n + 1)).comp _,
    rw hG,
    exact (classical.some_spec (classical.some_spec (hj _ n))).2.2.some }
end

variable (K)

/-- A Fraïssé limit of a Fraïssé class. -/
noncomputable def fraisse_limit [h : is_fraisse_class K] : bundled L.Structure :=
classical.some (exists_cg_is_age_of
  h.is_nonempty
  h.is_equiv_invariant
  h.is_essentially_countable
  h.fg h.hp h.jep)

instance cg_fraisse_limit [h : is_fraisse_class K] : Structure.cg L (fraisse_limit K) :=
(classical.some_spec (exists_cg_is_age_of h.is_nonempty h.is_equiv_invariant
  h.is_essentially_countable h.fg h.hp h.jep)).1

theorem age_fraisse_limit [h : is_fraisse_class K] : L.age (fraisse_limit K) = K :=
(classical.some_spec (exists_cg_is_age_of h.is_nonempty h.is_equiv_invariant
  h.is_essentially_countable h.fg h.hp h.jep)).2

end language
end first_order
