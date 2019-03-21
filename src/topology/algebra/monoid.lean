/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Theory of topological monoids.

TODO: generalize `topological_monoid` and `topological_add_monoid` to semigroups, or add a type class
`topological_operator α (*)`.
-/
import topology.constructions

open classical set lattice filter topological_space
local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

section topological_monoid

/-- A topological monoid is a monoid in which the multiplication is continuous as a function
`α × α → α`. -/
class topological_monoid (α : Type u) [topological_space α] [monoid α] : Prop :=
(continuous_mul : continuous (λp:α×α, p.1 * p.2))

/-- A topological (additive) monoid is a monoid in which the addition is
  continuous as a function `α × α → α`. -/
class topological_add_monoid (α : Type u) [topological_space α] [add_monoid α] : Prop :=
(continuous_add : continuous (λp:α×α, p.1 + p.2))

attribute [to_additive topological_add_monoid] topological_monoid
attribute [to_additive topological_add_monoid.mk] topological_monoid.mk
attribute [to_additive topological_add_monoid.continuous_add] topological_monoid.continuous_mul

section
variables [topological_space α] [monoid α] [topological_monoid α]

@[to_additive continuous_add']
lemma continuous_mul' : continuous (λp:α×α, p.1 * p.2) :=
topological_monoid.continuous_mul α

@[to_additive continuous_add]
lemma continuous_mul [topological_space β] {f : β → α} {g : β → α}
  (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
(hf.prod_mk hg).comp continuous_mul'

-- @[to_additive continuous_smul]
lemma continuous_pow : ∀ n : ℕ, continuous (λ a : α, a ^ n)
| 0 := by simpa using continuous_const
| (k+1) := show continuous (λ (a : α), a * a ^ k), from continuous_mul continuous_id (continuous_pow _)

@[to_additive tendsto_add']
lemma tendsto_mul' {a b : α} : tendsto (λp:α×α, p.fst * p.snd) (nhds (a, b)) (nhds (a * b)) :=
continuous_iff_continuous_at.mp (topological_monoid.continuous_mul α) (a, b)

@[to_additive tendsto_add]
lemma tendsto_mul {f : β → α} {g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) :
  tendsto (λx, f x * g x) x (nhds (a * b)) :=
(hf.prod_mk hg).comp (by rw [←nhds_prod_eq]; exact tendsto_mul')

@[to_additive tendsto_list_sum]
lemma tendsto_list_prod {f : γ → β → α} {x : filter β} {a : γ → α} :
  ∀l:list γ, (∀c∈l, tendsto (f c) x (nhds (a c))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (nhds ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp,
    exact tendsto_mul
      (h f (list.mem_cons_self _ _))
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end

@[to_additive continuous_list_sum]
lemma continuous_list_prod [topological_space β] {f : γ → β → α} (l : list γ)
  (h : ∀c∈l, continuous (f c)) :
  continuous (λa, (l.map (λc, f c a)).prod) :=
continuous_iff_continuous_at.2 $ assume x, tendsto_list_prod l $ assume c hc,
  continuous_iff_continuous_at.1 (h c hc) x

@[to_additive prod.topological_add_monoid]
instance [topological_space β] [monoid β] [topological_monoid β] : topological_monoid (α × β) :=
⟨continuous.prod_mk
  (continuous_mul (continuous_fst.comp continuous_fst) (continuous_snd.comp continuous_fst))
  (continuous_mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd)) ⟩

attribute [instance] prod.topological_add_monoid

end

section
variables [topological_space α] [comm_monoid α] [topological_monoid α]

@[to_additive tendsto_multiset_sum]
lemma tendsto_multiset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : multiset γ) :
  (∀c∈s, tendsto (f c) x (nhds (a c))) →
    tendsto (λb, (s.map (λc, f c b)).prod) x (nhds ((s.map a).prod)) :=
by { rcases s with ⟨l⟩, simp, exact tendsto_list_prod l }

@[to_additive tendsto_finset_sum]
lemma tendsto_finset_prod {f : γ → β → α} {x : filter β} {a : γ → α} (s : finset γ) :
  (∀c∈s, tendsto (f c) x (nhds (a c))) → tendsto (λb, s.prod (λc, f c b)) x (nhds (s.prod a)) :=
tendsto_multiset_prod _

@[to_additive continuous_multiset_sum]
lemma continuous_multiset_prod [topological_space β] {f : γ → β → α} (s : multiset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, (s.map (λc, f c a)).prod) :=
by { rcases s with ⟨l⟩, simp, exact continuous_list_prod l }

@[to_additive continuous_finset_sum]
lemma continuous_finset_prod [topological_space β] {f : γ → β → α} (s : finset γ) :
  (∀c∈s, continuous (f c)) → continuous (λa, s.prod (λc, f c a)) :=
continuous_multiset_prod _

@[to_additive is_add_submonoid.mem_nhds_zero]
lemma is_submonoid.mem_nhds_one (β : set α) [is_submonoid β] (oβ : is_open β) :
  β ∈ nhds (1 : α) :=
mem_nhds_sets_iff.2 ⟨β, (by refl), oβ, is_submonoid.one_mem _⟩

end

end topological_monoid
