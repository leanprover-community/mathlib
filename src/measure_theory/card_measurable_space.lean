/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Violeta Hernández Palacios
-/
import measure_theory.measurable_space_def
import set_theory.continuum
import set_theory.cofinality

/-!
# Cardinal of sigma-algebras

If a sigma-algebra is generated by a set of sets `s`, then the cardinality of the sigma-algebra is
bounded by `(max (#s) 2) ^ ω`. This is stated in `measurable_space.cardinal_generate_measurable_le`
and `measurable_space.cardinal_measurable_set_le`.

In particular, if `#s ≤ 𝔠`, then the generated sigma-algebra has cardinality at most `𝔠`, see
`measurable_space.cardinal_measurable_set_le_continuum`.

For the proof, we rely on an explicit inductive construction of the sigma-algebra generated by
`s` (instead of the inductive predicate `generate_measurable`). This transfinite inductive
construction is parameterized by an ordinal `< ω₁`, and the cardinality bound is preserved along
each step of the construction.
-/

universe u
variables {α : Type u}

open_locale cardinal
open cardinal set

local notation `ω₁`:= (aleph 1 : cardinal.{u}).ord.out.α

namespace measurable_space

/-- Transfinite induction construction of the sigma-algebra generated by a set of sets `s`. At each
step, we add all elements of `s`, the empty set, the complements of already constructed sets, and
countable unions of already constructed sets. We index this construction by an ordinal `< ω₁`, as
this will be enough to generate all sets in the sigma-algebra. -/
def generate_measurable_rec (s : set (set α)) : ω₁ → set (set α)
| i := let S := ⋃ j : {j // j < i}, generate_measurable_rec j.1 in
    s ∪ {∅} ∪ compl '' S ∪ (set.range (λ (f : ℕ → S), ⋃ n, (f n).1))
using_well_founded {dec_tac := `[exact j.2]}

/-- At each step of the inductive construction, the cardinality bound `≤ (max (#s) 2) ^ ω`
holds. -/
lemma cardinal_generate_measurable_rec_le (s : set (set α)) (i : ω₁) :
  #(generate_measurable_rec s i) ≤ (max (#s) 2) ^ omega.{u} :=
begin
  apply (aleph 1).ord.out.wo.wf.induction i,
  assume i IH,
  have A := omega_le_aleph 1,
  have B : aleph 1 ≤ (max (#s) 2) ^ omega.{u} :=
    aleph_one_le_continuum.trans (power_le_power_right (le_max_right _ _)),
  have C : omega.{u} ≤ (max (#s) 2) ^ omega.{u} := A.trans B,
  have J : #(⋃ (j : {j // j < i}), generate_measurable_rec s j.1) ≤ (max (#s) 2) ^ omega.{u},
  { apply (mk_Union_le _).trans,
    have D : # {j // j < i} ≤ aleph 1 := (mk_subtype_le _).trans (le_of_eq (aleph 1).mk_ord_out),
    have E : cardinal.sup.{u u}
      (λ (j : {j // j < i}), #(generate_measurable_rec s j.1)) ≤ (max (#s) 2) ^ omega.{u} :=
    cardinal.sup_le (λ ⟨j, hj⟩, IH j hj),
    apply (mul_le_mul' D E).trans,
    rw mul_eq_max A C,
    exact max_le B le_rfl },
  rw [generate_measurable_rec],
  apply_rules [(mk_union_le _ _).trans, add_le_of_le C, mk_image_le.trans],
  { exact (le_max_left _ _).trans (self_le_power _ one_lt_omega.le) },
  { rw [mk_singleton],
    exact one_lt_omega.le.trans C },
  { apply mk_range_le.trans,
    simp only [mk_pi, subtype.val_eq_coe, prod_const, lift_uzero, mk_denumerable, lift_omega],
    have := @power_le_power_right _ _ omega.{u} J,
    rwa [← power_mul, omega_mul_omega] at this }
end

lemma cardinal_Union_generate_measurable_rec_le (s : set (set α)) :
  #(⋃ i, generate_measurable_rec s i) ≤ (max (#s) 2) ^ omega.{u} :=
begin
  apply (mk_Union_le _).trans,
  rw [(aleph 1).mk_ord_out],
  refine le_trans (mul_le_mul' aleph_one_le_continuum
    (cardinal.sup_le (λ i, cardinal_generate_measurable_rec_le s i))) _,
  have := power_le_power_right (le_max_right (#s) 2),
  rw mul_eq_max omega_le_continuum (omega_le_continuum.trans this),
  exact max_le this le_rfl
end

/-- A set in the sigma-algebra generated by a set of sets `s` is constructed at some step of the
transfinite induction defining `generate_measurable_rec`.
The other inclusion is also true, but not proved here as it is not needed for the cardinality
bounds.-/
theorem generate_measurable_subset_rec (s : set (set α)) ⦃t : set α⦄
  (ht : generate_measurable s t) :
  t ∈ ⋃ i, generate_measurable_rec s i :=
begin
  inhabit ω₁,
  induction ht with u hu u hu IH f hf IH,
  { refine mem_Union.2 ⟨default, _⟩,
    rw generate_measurable_rec,
    simp only [hu, mem_union_eq, true_or] },
  { refine mem_Union.2 ⟨default, _⟩,
    rw generate_measurable_rec,
    simp only [union_singleton, mem_union_eq, mem_insert_iff, eq_self_iff_true, true_or] },
  { rcases mem_Union.1 IH with ⟨i, hi⟩,
    obtain ⟨j, hj⟩ : ∃ j, i < j := ordinal.has_succ_of_type_succ_lt
      (by { rw ordinal.type_lt, exact (ord_aleph_is_limit 1).2 }) _,
    apply mem_Union.2 ⟨j, _⟩,
    rw generate_measurable_rec,
    have : ∃ a, (a < j) ∧ u ∈ generate_measurable_rec s a := ⟨i, hj, hi⟩,
    simp [this] },
  { have : ∀ n, ∃ i, f n ∈ generate_measurable_rec s i := λ n, by simpa using IH n,
    choose I hI using this,
    obtain ⟨j, hj⟩ : ∃ j, ∀ k, k ∈ range I → (k < j),
    { apply ordinal.lt_cof_type,
      simp only [is_regular_aleph_one.2, mk_singleton, ordinal.type_lt],
      have : #(range I) = lift.{0} (#(range I)), by simp only [lift_uzero],
      rw this,
      apply mk_range_le_lift.trans_lt _,
      simp [omega_lt_aleph_one] },
    apply mem_Union.2 ⟨j, _⟩,
    rw generate_measurable_rec,
    have : ∃ (g : ℕ → (↥⋃ (i : {i // i < j}), generate_measurable_rec s i.1)),
      (⋃ (n : ℕ), ↑(g n)) = (⋃ n, f n),
    { refine ⟨λ n, ⟨f n, _⟩, rfl⟩,
      exact mem_Union.2 ⟨⟨I n, hj (I n) (mem_range_self _)⟩, hI n⟩ },
    simp [this] }
end

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma
algebra has cardinality at most `(max (#s) 2) ^ ω`. -/
theorem cardinal_generate_measurable_le (s : set (set α)) :
  #{t | generate_measurable s t} ≤ (max (#s) 2) ^ omega.{u} :=
(mk_subtype_le_of_subset (generate_measurable_subset_rec s)).trans
  (cardinal_Union_generate_measurable_rec_le s)

/-- If a sigma-algebra is generated by a set of sets `s`, then the sigma
algebra has cardinality at most `(max (#s) 2) ^ ω`. -/
theorem cardinal_measurable_set_le (s : set (set α)) :
  #{t | @measurable_set α (generate_from s) t} ≤ (max (#s) 2) ^ omega.{u} :=
cardinal_generate_measurable_le s

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_generate_measurable_le_continuum {s : set (set α)} (hs : #s ≤ 𝔠) :
  #{t | generate_measurable s t} ≤ 𝔠 :=
calc
#{t | generate_measurable s t}
    ≤ (max (#s) 2) ^ omega.{u} : cardinal_generate_measurable_le s
... ≤ 𝔠 ^ omega.{u} :
  by exact_mod_cast power_le_power_right (max_le hs (nat_lt_continuum 2).le)
... = 𝔠 : continuum_power_omega

/-- If a sigma-algebra is generated by a set of sets `s` with cardinality at most the continuum,
then the sigma algebra has the same cardinality bound. -/
theorem cardinal_measurable_set_le_continuum {s : set (set α)} (hs : #s ≤ 𝔠) :
  #{t | @measurable_set α (generate_from s) t} ≤ 𝔠 :=
cardinal_generate_measurable_le_continuum hs

end measurable_space
