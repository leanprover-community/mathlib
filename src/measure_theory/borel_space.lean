/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Borel (measurable) space -- the smallest σ-algebra generated by open sets

It would be nice to encode this in the topological space type class, i.e. each topological space
carries a measurable space, the Borel space. This would be similar how each uniform space carries a
topological space. The idea is to allow definitional equality for product instances.
We would like to have definitional equality for

  borel t₁ × borel t₂ = borel (t₁ × t₂)

Unfortunately, this only holds if t₁ and t₂ are second-countable topologies.
-/
import measure_theory.measurable_space topology.instances.ennreal analysis.normed_space.basic
noncomputable theory

open classical set
open_locale classical

universes u v w x y
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ι : Sort y} {s t u : set α}

open measurable_space topological_space

/-- `measurable_space` structure generated by `topological_space`. -/
def borel (α : Type u) [topological_space α] : measurable_space α :=
generate_from {s : set α | is_open s}

lemma borel_eq_top_of_discrete [topological_space α] [discrete_topology α] :
  borel α = ⊤ :=
top_le_iff.1 $ λ s hs, generate_measurable.basic s (is_open_discrete s)

lemma borel_eq_top_of_encodable [topological_space α] [t1_space α] [encodable α] :
  borel α = ⊤ :=
begin
  refine (top_le_iff.1 $ λ s hs, bUnion_of_singleton s ▸ _),
  apply is_measurable.bUnion s.countable_encodable,
  intros x hx,
  apply is_measurable.of_compl,
  apply generate_measurable.basic,
  exact is_closed_singleton
end

lemma borel_eq_generate_from_of_subbasis {s : set (set α)}
  [t : topological_space α] [second_countable_topology α] (hs : t = generate_from s) :
  borel α = generate_from s :=
le_antisymm
  (generate_from_le $ assume u (hu : t.is_open u),
    begin
      rw [hs] at hu,
      induction hu,
      case generate_open.basic : u hu
      { exact generate_measurable.basic u hu },
      case generate_open.univ
      { exact @is_measurable.univ α (generate_from s) },
      case generate_open.inter : s₁ s₂ _ _ hs₁ hs₂
      { exact @is_measurable.inter α (generate_from s) _ _ hs₁ hs₂ },
      case generate_open.sUnion : f hf ih {
        rcases is_open_sUnion_countable f (by rwa hs) with ⟨v, hv, vf, vu⟩,
        rw ← vu,
        exact @is_measurable.sUnion α (generate_from s) _ hv
          (λ x xv, ih _ (vf xv)) }
    end)
  (generate_from_le $ assume u hu, generate_measurable.basic _ $
    show t.is_open u, by rw [hs]; exact generate_open.basic _ hu)

lemma borel_eq_generate_Iio (α)
  [topological_space α] [second_countable_topology α]
  [linear_order α] [order_topology α] :
  borel α = generate_from (range Iio) :=
begin
  refine le_antisymm _ (generate_from_le _),
  { rw borel_eq_generate_from_of_subbasis (order_topology.topology_eq_generate_intervals α),
    have H : ∀ a:α, is_measurable (measurable_space.generate_from (range Iio)) (Iio a) :=
      λ a, generate_measurable.basic _ ⟨_, rfl⟩,
    refine generate_from_le _, rintro _ ⟨a, rfl | rfl⟩; [skip, apply H],
    by_cases h : ∃ a', ∀ b, a < b ↔ a' ≤ b,
    { rcases h with ⟨a', ha'⟩,
      rw (_ : Ioi a = -Iio a'), {exact (H _).compl _},
      simp [set.ext_iff, ha'] },
    { rcases is_open_Union_countable
        (λ a' : {a' : α // a < a'}, {b | a'.1 < b})
        (λ a', is_open_lt' _) with ⟨v, ⟨hv⟩, vu⟩,
      simp [set.ext_iff] at vu,
      have : Ioi a = ⋃ x : v, -Iio x.1.1,
      { simp [set.ext_iff],
        refine λ x, ⟨λ ax, _, λ ⟨a', ⟨h, av⟩, ax⟩, lt_of_lt_of_le h ax⟩,
        rcases (vu x).2 _ with ⟨a', h₁, h₂⟩,
        { exact ⟨a', h₁, le_of_lt h₂⟩ },
        refine not_imp_comm.1 (λ h, _) h,
        exact ⟨x, λ b, ⟨λ ab, le_of_not_lt (λ h', h ⟨b, ab, h'⟩),
          lt_of_lt_of_le ax⟩⟩ },
      rw this, resetI,
      apply is_measurable.Union,
      exact λ _, (H _).compl _ } },
  { simp, rintro _ a rfl,
    exact generate_measurable.basic _ is_open_Iio }
end

lemma borel_eq_generate_Ioi (α)
  [topological_space α] [second_countable_topology α]
  [linear_order α] [order_topology α] :
  borel α = generate_from (range Ioi) :=
begin
  refine le_antisymm _ (generate_from_le _),
  { rw borel_eq_generate_from_of_subbasis (order_topology.topology_eq_generate_intervals α),
    have H : ∀ a:α, is_measurable (measurable_space.generate_from (range (λ a, {x | a < x}))) {x | a < x} :=
      λ a, generate_measurable.basic _ ⟨_, rfl⟩,
    refine generate_from_le _, rintro _ ⟨a, rfl | rfl⟩, {apply H},
    by_cases h : ∃ a', ∀ b, b < a ↔ b ≤ a',
    { rcases h with ⟨a', ha'⟩,
      rw (_ : Iio a = -Ioi a'), {exact (H _).compl _},
      simp [set.ext_iff, ha'] },
    { rcases is_open_Union_countable
        (λ a' : {a' : α // a' < a}, {b | b < a'.1})
        (λ a', is_open_gt' _) with ⟨v, ⟨hv⟩, vu⟩,
      simp [set.ext_iff] at vu,
      have : Iio a = ⋃ x : v, -Ioi x.1.1,
      { simp [set.ext_iff],
        refine λ x, ⟨λ ax, _, λ ⟨a', ⟨h, av⟩, ax⟩, lt_of_le_of_lt ax h⟩,
        rcases (vu x).2 _ with ⟨a', h₁, h₂⟩,
        { exact ⟨a', h₁, le_of_lt h₂⟩ },
        refine not_imp_comm.1 (λ h, _) h,
        exact ⟨x, λ b, ⟨λ ab, le_of_not_lt (λ h', h ⟨b, ab, h'⟩),
          λ h, lt_of_le_of_lt h ax⟩⟩ },
      rw this, resetI,
      apply is_measurable.Union,
      exact λ _, (H _).compl _ } },
  { simp, rintro _ a rfl,
    exact generate_measurable.basic _ (is_open_lt' _) }
end

lemma borel_comap {f : α → β} {t : topological_space β} :
  @borel α (t.induced f) = (@borel β t).comap f :=
comap_generate_from.symm

lemma continuous.borel_measurable [topological_space α] [topological_space β]
  {f : α → β} (hf : continuous f) :
  @measurable α β (borel α) (borel β) f :=
generate_from_le $ λ s hs, generate_measurable.basic (f ⁻¹' s) (hf s hs)

/-- A space with `measurable_space` and `topological_space` structures such that
all open sets are measurable. -/
class opens_measurable_space (α : Type*) [topological_space α] [h : measurable_space α] : Prop :=
(borel_le : borel α ≤ h)

/-- A space with `measurable_space` and `topological_space` structures such that
the `σ`-algebra of measurable sets is exactly the `σ`-algebra generated by open sets. -/
class borel_space (α : Type*) [topological_space α] [measurable_space α] : Prop :=
(measurable_eq : ‹measurable_space α› = borel α)

/-- In a `borel_space` all open sets are measurable. -/
@[priority 100]
instance borel_space.opens_measurable {α : Type*} [topological_space α] [measurable_space α]
  [borel_space α] : opens_measurable_space α :=
⟨ge_of_eq $ borel_space.measurable_eq α⟩

instance subtype.borel_space {α : Type*} [topological_space α] [measurable_space α]
  [hα : borel_space α] (s : set α) :
  borel_space s :=
⟨by { rw [hα.1, subtype.measurable_space, ← borel_comap], refl }⟩

instance subtype.opens_measurable_space {α : Type*} [topological_space α] [measurable_space α]
  [h : opens_measurable_space α] (s : set α) :
  opens_measurable_space s :=
⟨by { rw [borel_comap], exact comap_mono h.1 }⟩

section
variables [topological_space α] [measurable_space α] [opens_measurable_space α]
   [topological_space β] [measurable_space β] [opens_measurable_space β]
   [topological_space γ] [measurable_space γ] [borel_space γ]
   [measurable_space δ]
   
lemma is_open.is_measurable (h : is_open s) : is_measurable s :=
opens_measurable_space.borel_le α _ $ generate_measurable.basic _ h

lemma is_measurable_interior : is_measurable (interior s) := is_open_interior.is_measurable

lemma is_closed.is_measurable (h : is_closed s) : is_measurable s :=
is_measurable.compl_iff.1 $ h.is_measurable

lemma is_measurable_singleton [t1_space α] {x : α} : is_measurable ({x} : set α) :=
is_closed_singleton.is_measurable

lemma is_measurable_closure : is_measurable (closure s) :=
is_closed_closure.is_measurable

section order_closed_topology
variables [preorder α] [order_closed_topology α] {a b : α}

lemma is_measurable_Ici : is_measurable (Ici a) := is_closed_Ici.is_measurable
lemma is_measurable_Iic : is_measurable (Iic a) := is_closed_Iic.is_measurable
lemma is_measurable_Icc : is_measurable (Icc a b) := is_closed_Icc.is_measurable

end order_closed_topology

section order_closed_topology
variables [linear_order α] [order_closed_topology α] {a b : α}

lemma is_measurable_Iio : is_measurable (Iio a) := is_open_Iio.is_measurable
lemma is_measurable_Ioi : is_measurable (Ioi a) := is_open_Ioi.is_measurable
lemma is_measurable_Ioo : is_measurable (Ioo a b) := is_open_Ioo.is_measurable
lemma is_measurable_Ioc : is_measurable (Ioc a b) := is_measurable_Ioi.inter is_measurable_Iic
lemma is_measurable_Ico : is_measurable (Ico a b) := is_measurable_Ici.inter is_measurable_Iio

end order_closed_topology

lemma is_measurable_interval [decidable_linear_order α] [order_closed_topology α] {a b : α} :
  is_measurable (interval a b) :=
is_measurable_Icc

instance prod.opens_measurable_space [second_countable_topology α] [second_countable_topology β] :
  opens_measurable_space (α × β) :=
begin
  refine ⟨_⟩,
  rcases is_open_generated_countable_inter α with ⟨a, ha₁, ha₂, ha₃, ha₄, ha₅⟩,
  rcases is_open_generated_countable_inter β with ⟨b, hb₁, hb₂, hb₃, hb₄, hb₅⟩,
  have : prod.topological_space = generate_from {g | ∃u∈a, ∃v∈b, g = set.prod u v},
  { rw [ha₅, hb₅], exact prod_generate_from_generate_from_eq ha₄ hb₄ },
  rw [borel_eq_generate_from_of_subbasis this],
  apply generate_from_le,
  rintros _ ⟨u, hu, v, hv, rfl⟩,
  have hu : is_open u, by { rw [ha₅], exact generate_open.basic _ hu },
  have hv : is_open v, by { rw [hb₅], exact generate_open.basic _ hv },
  exact hu.is_measurable.prod hv.is_measurable
end

/-- A continuous function from an `opens_measurable_space` to a `borel_space`
is measurable. -/
lemma continuous.measurable {f : α → γ} (hf : continuous f) :
  measurable f :=
hf.borel_measurable.mono (opens_measurable_space.borel_le _)
  (le_of_eq $ borel_space.measurable_eq _)

lemma continuous.measurable2 [second_countable_topology α] [second_countable_topology β]
  {f : δ → α} {g : δ → β} {c : α → β → γ}
  (h : continuous (λp:α×β, c p.1 p.2)) (hf : measurable f) (hg : measurable g) :
  measurable (λa, c (f a) (g a)) :=
h.measurable.comp (hf.prod_mk hg)

lemma measurable.smul [semiring α] [second_countable_topology α]
  [add_comm_monoid γ] [second_countable_topology γ]
  [semimodule α γ] [topological_semimodule α γ]
  {f : δ → α} {g : δ → γ} (hf : measurable f) (hg : measurable g) :
  measurable (λ c, f c • g c) :=
continuous_smul.measurable2 hf hg

lemma measurable.const_smul {α : Type*} [topological_space α] [semiring α]
  [add_comm_monoid γ] [semimodule α γ] [topological_semimodule α γ]
  {f : δ → γ} (hf : measurable f) (c : α) :
  measurable (λ x, c • f x) :=
(continuous_const.smul continuous_id).measurable.comp hf

lemma measurable_const_smul_iff {α : Type*} [topological_space α]
  [division_ring α] [add_comm_monoid γ]
  [semimodule α γ] [topological_semimodule α γ]
  {f : δ → γ} {c : α} (hc : c ≠ 0) :
  measurable (λ x, c • f x) ↔ measurable f :=
⟨λ h, by simpa only [smul_smul, inv_mul_cancel hc, one_smul] using h.const_smul c⁻¹,
  λ h, h.const_smul c⟩

lemma is_measurable_le' [partial_order α] [order_closed_topology α] [second_countable_topology α] :
  is_measurable {p : α × α | p.1 ≤ p.2} :=
(order_closed_topology.is_closed_le' _).is_measurable

lemma is_measurable_le [partial_order α] [order_closed_topology α] [second_countable_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  is_measurable {a | f a ≤ g a} :=
(hf.prod_mk hg).preimage is_measurable_le'

lemma measurable.max [decidable_linear_order α] [order_closed_topology α] [second_countable_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  measurable (λa, max (f a) (g a)) :=
measurable.if (is_measurable_le hf hg) hg hf

lemma measurable.min [decidable_linear_order α] [order_closed_topology α] [second_countable_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  measurable (λa, min (f a) (g a)) :=
measurable.if (is_measurable_le hf hg) hf hg

end

section borel_space
variables [topological_space α] [measurable_space α] [borel_space α]
  [topological_space β] [measurable_space β] [borel_space β]
  [topological_space γ] [measurable_space γ] [borel_space γ]
  [measurable_space δ]

lemma prod_le_borel_prod : prod.measurable_space ≤ borel (α × β) :=
begin
  rw [‹borel_space α›.measurable_eq, ‹borel_space β›.measurable_eq],
  refine sup_le _ _,
  { exact comap_le_iff_le_map.mpr continuous_fst.borel_measurable },
  { exact comap_le_iff_le_map.mpr continuous_snd.borel_measurable }
end

instance prod.borel_space [second_countable_topology α] [second_countable_topology β] :
  borel_space (α × β) :=
⟨le_antisymm prod_le_borel_prod (opens_measurable_space.borel_le (α × β))⟩

@[to_additive]
lemma measurable_mul [monoid α] [topological_monoid α] [second_countable_topology α] :
  measurable (λ p : α × α, p.1 * p.2) :=
continuous_mul.measurable

@[to_additive]
lemma measurable.mul [monoid α] [topological_monoid α] [second_countable_topology α]
  {f : δ → α} {g : δ → α} : measurable f → measurable g → measurable (λa, f a * g a) :=
continuous_mul.measurable2

@[to_additive]
lemma finset.measurable_prod {ι : Type*} [comm_monoid α] [topological_monoid α]
  [second_countable_topology α] {f : ι → δ → α} (s : finset ι) (hf : ∀i, measurable (f i)) :
  measurable (λa, s.prod (λi, f i a)) :=
finset.induction_on s
  (by simp only [finset.prod_empty, measurable_const])
  (assume i s his ih, by simpa [his] using (hf i).mul ih)

@[to_additive]
lemma measurable.inv [group α] [topological_group α] {f : δ → α} (hf : measurable f) :
  measurable (λa, (f a)⁻¹) :=
continuous_inv.measurable.comp hf

@[to_additive]
lemma measurable.of_inv [group α] [topological_group α] {f : δ → α}
  (hf : measurable (λ a, (f a)⁻¹)) : measurable f :=
by simpa only [inv_inv] using hf.inv

@[to_additive]
lemma measurable_inv_iff [group α] [topological_group α] {f : δ → α} :
  measurable (λ a, (f a)⁻¹) ↔ measurable f :=
⟨measurable.of_inv, measurable.inv⟩

lemma measurable.sub [add_group α] [topological_add_group α] [second_countable_topology α]
  {f g : δ → α} (hf : measurable f) (hg : measurable g) :
  measurable (λ x, f x - g x) :=
hf.add hg.neg

lemma measurable.is_lub [linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, measurable (f i))
  (hg : ∀ b, is_lub {a | ∃ i, f i b = a} (g b)) :
  measurable g :=
begin
  change ∀ b, is_lub (range $ λ i, f i b) (g b) at hg,
  rw [‹borel_space α›.measurable_eq, borel_eq_generate_Ioi α],
  apply measurable_generate_from,
  rintro _ ⟨a, rfl⟩,
  simp only [set.preimage, mem_Ioi, lt_is_lub_iff (hg _), exists_range_iff, set_of_exists],
  exact is_measurable.Union (λ i, hf i _ (is_open_lt' _).is_measurable)
end

lemma measurable.is_glb [linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, measurable (f i))
  (hg : ∀ b, is_glb {a | ∃ i, f i b = a} (g b)) :
  measurable g :=
begin
  change ∀ b, is_glb (range $ λ i, f i b) (g b) at hg,
  rw [‹borel_space α›.measurable_eq, borel_eq_generate_Iio α],
  apply measurable_generate_from,
  rintro _ ⟨a, rfl⟩,
  simp only [set.preimage, mem_Iio, is_glb_lt_iff (hg _), exists_range_iff, set_of_exists],
  exact is_measurable.Union (λ i, hf i _ (is_open_gt' _).is_measurable)
end

lemma measurable_supr [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] {f : ι → δ → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨆ i, f i b) :=
measurable.is_lub hf $ λ b, is_lub_supr

lemma measurable_infi [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] {f : ι → δ → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨅ i, f i b) :=
measurable.is_glb hf $ λ b, is_glb_infi

lemma measurable.supr_Prop {α} [measurable_space α] [complete_lattice α]
  (p : Prop) {f : δ → α} (hf : measurable f) :
  measurable (λ b, ⨆ h : p, f b) :=
classical.by_cases
  (assume h : p, begin convert hf, funext, exact supr_pos h end)
  (assume h : ¬p, begin convert measurable_const, funext, exact supr_neg h end)

lemma measurable.infi_Prop {α} [measurable_space α] [complete_lattice α]
  (p : Prop) {f : δ → α} (hf : measurable f) :
  measurable (λ b, ⨅ h : p, f b) :=
classical.by_cases
  (assume h : p, begin convert hf, funext, exact infi_pos h end )
  (assume h : ¬p, begin convert measurable_const, funext, exact infi_neg h end)

lemma measurable_bsupr [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] (p : ι → Prop) {f : ι → δ → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨆ i (hi : p i), f i b) :=
measurable_supr $ λ i, (hf i).supr_Prop (p i)

lemma measurable_binfi [complete_linear_order α] [order_topology α] [second_countable_topology α]
  {ι} [encodable ι] (p : ι → Prop) {f : ι → δ → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨅ i (hi : p i), f i b) :=
measurable_infi $ λ i, (hf i).infi_Prop (p i)

/-- Convert a `homeomorph` to a `measurable_equiv`. -/
def homemorph.to_measurable_equiv (h : α ≃ₜ β) :
  measurable_equiv α β :=
{ to_equiv := h.to_equiv,
  measurable_to_fun := h.continuous_to_fun.measurable,
  measurable_inv_fun := h.continuous_inv_fun.measurable }

end borel_space

instance empty.borel_space : borel_space empty := ⟨borel_eq_top_of_discrete.symm⟩
instance unit.borel_space : borel_space unit := ⟨borel_eq_top_of_discrete.symm⟩
instance bool.borel_space : borel_space bool := ⟨borel_eq_top_of_discrete.symm⟩
instance nat.borel_space : borel_space ℕ := ⟨borel_eq_top_of_discrete.symm⟩
instance int.borel_space : borel_space ℤ := ⟨borel_eq_top_of_discrete.symm⟩
instance rat.borel_space : borel_space ℚ := ⟨borel_eq_top_of_encodable.symm⟩

instance real.measurable_space : measurable_space ℝ := borel ℝ
instance real.borel_space : borel_space ℝ := ⟨rfl⟩

instance nnreal.measurable_space : measurable_space nnreal := borel nnreal
instance nnreal.borel_space : borel_space nnreal := ⟨rfl⟩

instance ennreal.measurable_space : measurable_space ennreal := borel ennreal
instance ennreal.borel_space : borel_space ennreal := ⟨rfl⟩

section metric_space

variables [metric_space α] [measurable_space α] [opens_measurable_space α] {x : α} {ε : ℝ}

lemma is_measurable_ball : is_measurable (metric.ball x ε) :=
metric.is_open_ball.is_measurable

lemma is_measurable_closed_ball : is_measurable (metric.closed_ball x ε) :=
metric.is_closed_ball.is_measurable

lemma measurable_dist [second_countable_topology α] :
  measurable (λp:α×α, dist p.1 p.2) :=
continuous_dist.measurable

lemma measurable.dist [second_countable_topology α] [measurable_space β] {f g : β → α}
  (hf : measurable f) (hg : measurable g) : measurable (λ b, dist (f b) (g b)) :=
continuous_dist.measurable2 hf hg

lemma measurable_nndist [second_countable_topology α] : measurable (λp:α×α, nndist p.1 p.2) :=
continuous_nndist.measurable

lemma measurable.nndist [second_countable_topology α] [measurable_space β] {f g : β → α} :
  measurable f → measurable g → measurable (λ b, nndist (f b) (g b)) :=
continuous_nndist.measurable2

end metric_space

section emetric_space

variables [emetric_space α] [measurable_space α] [opens_measurable_space α] {x : α} {ε : ennreal}

lemma is_measurable_eball : is_measurable (emetric.ball x ε) :=
emetric.is_open_ball.is_measurable

lemma measurable_edist [second_countable_topology α] :
  measurable (λp:α×α, edist p.1 p.2) :=
continuous_edist.measurable

lemma measurable.edist [second_countable_topology α] [measurable_space β] {f g : β → α} :
  measurable f → measurable g → measurable (λ b, edist (f b) (g b)) :=
continuous_edist.measurable2

end emetric_space

namespace real
open measurable_space

lemma borel_eq_generate_from_Ioo_rat :
  borel ℝ = generate_from (⋃(a b : ℚ) (h : a < b), {Ioo a b}) :=
borel_eq_generate_from_of_subbasis is_topological_basis_Ioo_rat.2.2

lemma borel_eq_generate_from_Iio_rat :
  borel ℝ = generate_from (⋃a:ℚ, {Iio a}) :=
begin
  let g, swap,
  apply le_antisymm (_ : _ ≤ g) (measurable_space.generate_from_le (λ t, _)),
  { rw borel_eq_generate_from_Ioo_rat,
    refine generate_from_le (λ t, _),
    simp only [mem_Union], rintro ⟨a, b, h, rfl|⟨⟨⟩⟩⟩,
    rw (set.ext (λ x, _) : Ioo (a:ℝ) b = (⋃c>a, - Iio c) ∩ Iio b),
    { have hg : ∀q:ℚ, g.is_measurable (Iio q) :=
        λ q, generate_measurable.basic _ (by simp; exact ⟨_, rfl⟩),
      refine @is_measurable.inter _ g _ _ _ (hg _),
      refine @is_measurable.bUnion _ _ g _ _ (countable_encodable _) (λ c h, _),
      exact @is_measurable.compl _ _ g (hg _) },
    { simp [Ioo, Iio],
      refine and_congr _ iff.rfl,
      exact ⟨λ h,
        let ⟨c, ac, cx⟩ := exists_rat_btwn h in
        ⟨c, rat.cast_lt.1 ac, le_of_lt cx⟩,
       λ ⟨c, ac, cx⟩, lt_of_lt_of_le (rat.cast_lt.2 ac) cx⟩ } },
  { simp, rintro r rfl,
    exact is_open_Iio.is_measurable }
end

end real

lemma measurable.sub_nnreal [measurable_space α] {f g : α → nnreal} :
  measurable f → measurable g → measurable (λ a, f a - g a) :=
nnreal.continuous_sub.measurable2

lemma measurable.nnreal_of_real [measurable_space α] {f : α → ℝ} (hf : measurable f) :
  measurable (λ x, nnreal.of_real (f x)) :=
nnreal.continuous_of_real.measurable.comp hf

lemma measurable.nnreal_coe [measurable_space α] {f : α → nnreal} (hf : measurable f) :
  measurable (λ x, (f x : ℝ)) :=
nnreal.continuous_coe.measurable.comp hf

lemma measurable.ennreal_coe [measurable_space α] {f : α → nnreal} (hf : measurable f) :
  measurable (λ x, (f x : ennreal)) :=
(ennreal.continuous_coe.2 continuous_id).measurable.comp hf

lemma measurable.ennreal_of_real [measurable_space α] {f : α → ℝ} (hf : measurable f) :
  measurable (λ x, ennreal.of_real (f x)) :=
ennreal.continuous_of_real.measurable.comp hf

namespace ennreal
open filter

lemma measurable_coe : measurable (coe : nnreal → ennreal) :=
measurable_id.ennreal_coe

def ennreal_equiv_nnreal : measurable_equiv {r : ennreal | r < ⊤} nnreal :=
{ to_fun    := λr, ennreal.to_nnreal r,
  inv_fun   := λr, ⟨r, coe_lt_top⟩,
  left_inv  := assume ⟨r, hr⟩, subtype.eq $ coe_to_nnreal (ne_of_lt hr),
  right_inv := assume r, to_nnreal_coe,
  measurable_to_fun  :=
  begin
    refine (continuous_iff_continuous_at.2 _).measurable,
    rintros ⟨r, hr⟩,
    simp [continuous_at, nhds_subtype_eq_comap],
    refine tendsto.comp (tendsto_to_nnreal (ne_of_lt hr)) tendsto_comap
  end,
  measurable_inv_fun := measurable_id.ennreal_coe.subtype_mk }

lemma measurable_of_measurable_nnreal [measurable_space α] {f : ennreal → α}
  (h : measurable (λp:nnreal, f p)) : measurable f :=
begin
  refine measurable_of_measurable_union_cover {⊤} {r : ennreal | r < ⊤}
    is_closed_singleton.is_measurable
    (is_open_gt' _).is_measurable
    (assume r _, by cases r; simp [ennreal.none_eq_top, ennreal.some_eq_coe])
    _
    _,
  exact (measurable_equiv.set.singleton ⊤).symm.measurable_coe_iff.1 (measurable_unit _),
  exact (ennreal_equiv_nnreal.symm.measurable_coe_iff.1 h)
end

def ennreal_equiv_sum :
  @measurable_equiv ennreal (nnreal ⊕ unit) _ sum.measurable_space :=
{ to_fun    :=
    @option.rec nnreal (λ_, nnreal ⊕ unit) (sum.inr ()) (sum.inl : nnreal → nnreal ⊕ unit),
  inv_fun   :=
    @sum.rec nnreal unit (λ_, ennreal) (coe : nnreal → ennreal) (λ_, ⊤),
  left_inv  := assume s, by cases s; refl,
  right_inv := assume s, by rcases s with r | ⟨⟨⟩⟩; refl,
  measurable_to_fun  := measurable_of_measurable_nnreal measurable_inl,
  measurable_inv_fun := measurable_sum measurable_coe (@measurable_const ennreal unit _ _ ⊤) }

lemma measurable_of_measurable_nnreal_nnreal [measurable_space α] [measurable_space β]
  (f : ennreal → ennreal → β) {g : α → ennreal} {h : α → ennreal}
  (h₁ : measurable (λp:nnreal × nnreal, f p.1 p.2))
  (h₂ : measurable (λr:nnreal, f ⊤ r))
  (h₃ : measurable (λr:nnreal, f r ⊤))
  (hg : measurable g) (hh : measurable h) : measurable (λa, f (g a) (h a)) :=
let e : measurable_equiv (ennreal × ennreal)
  (((nnreal × nnreal) ⊕ (nnreal × unit)) ⊕ ((unit × nnreal) ⊕ (unit × unit))) :=
  (measurable_equiv.prod_congr ennreal_equiv_sum ennreal_equiv_sum).trans
    (measurable_equiv.sum_prod_sum _ _ _ _) in
have measurable (λp:ennreal×ennreal, f p.1 p.2),
begin
  refine e.symm.measurable_coe_iff.1 (measurable_sum (measurable_sum _ _) (measurable_sum _ _)),
  { show measurable (λp:nnreal × nnreal, f p.1 p.2),
    exact h₁ },
  { show measurable (λp:nnreal × unit, f p.1 ⊤),
    exact h₃.comp (measurable.fst measurable_id) },
  { show measurable ((λp:nnreal, f ⊤ p) ∘ (λp:unit × nnreal, p.2)),
    exact h₂.comp (measurable.snd measurable_id) },
  { show measurable (λp:unit × unit, f ⊤ ⊤),
    exact measurable_const }
end,
this.comp (measurable.prod_mk hg hh)

lemma measurable_of_real : measurable ennreal.of_real :=
ennreal.continuous_of_real.measurable

end ennreal

lemma measurable.ennreal_mul {α : Type*} [measurable_space α] {f g : α → ennreal} :
  measurable f → measurable g → measurable (λa, f a * g a) :=
begin
  refine ennreal.measurable_of_measurable_nnreal_nnreal (*) _ _ _,
  { simp only [ennreal.coe_mul.symm],
    exact ennreal.measurable_coe.comp measurable_mul },
  { simp [ennreal.top_mul],
    exact measurable.if
      (is_closed_eq continuous_id continuous_const).is_measurable
      measurable_const
      measurable_const },
  { simp [ennreal.mul_top],
    exact measurable.if
      (is_closed_eq continuous_id continuous_const).is_measurable
      measurable_const
      measurable_const }
end

lemma measurable.ennreal_add {α : Type*} [measurable_space α] {f g : α → ennreal} :
  measurable f → measurable g → measurable (λa, f a + g a) :=
begin
  refine ennreal.measurable_of_measurable_nnreal_nnreal (+) _ _ _,
  { simp only [ennreal.coe_add.symm],
    exact ennreal.measurable_coe.comp measurable_add },
  { simp [measurable_const] },
  { simp [measurable_const] }
end

lemma measurable.ennreal_sub {α : Type*} [measurable_space α] {f g : α → ennreal} :
  measurable f → measurable g → measurable (λa, f a - g a) :=
begin
  refine ennreal.measurable_of_measurable_nnreal_nnreal (has_sub.sub) _ _ _,
  { simp only [ennreal.coe_sub.symm],
    exact ennreal.measurable_coe.comp nnreal.continuous_sub.measurable },
  { simp [measurable_const] },
  { simp [measurable_const] }
end

section normed_group

variables [measurable_space α] [normed_group α] [opens_measurable_space α] [measurable_space β]

lemma measurable_norm : measurable (norm : α → ℝ) :=
continuous_norm.measurable

lemma measurable.norm {f : β → α} (hf : measurable f) : measurable (λa, norm (f a)) :=
measurable_norm.comp hf

lemma measurable_nnnorm : measurable (nnnorm : α → nnreal) :=
continuous_nnnorm.measurable

lemma measurable.nnnorm {f : β → α} (hf : measurable f) : measurable (λa, nnnorm (f a)) :=
measurable_nnnorm.comp hf

lemma measurable.ennnorm {f : β → α} (hf : measurable f) :
  measurable (λa, (nnnorm (f a) : ennreal)) :=
hf.nnnorm.ennreal_coe

end normed_group
#lint
