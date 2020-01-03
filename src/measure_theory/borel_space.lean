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

open classical set lattice real
open_locale classical

universes u v w x y
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ι : Sort y} {s t u : set α}

open measurable_space topological_space

@[instance, priority 900] def borel (α : Type u) [topological_space α] : measurable_space α :=
generate_from {s : set α | is_open s}

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
  [linear_order α] [orderable_topology α] :
  borel α = generate_from (range Iio) :=
begin
  refine le_antisymm _ (generate_from_le _),
  { rw borel_eq_generate_from_of_subbasis (orderable_topology.topology_eq_generate_intervals α),
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
  [linear_order α] [orderable_topology α] :
  borel α = generate_from (range (λ a, {x | a < x})) :=
begin
  refine le_antisymm _ (generate_from_le _),
  { rw borel_eq_generate_from_of_subbasis (orderable_topology.topology_eq_generate_intervals α),
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
calc @borel α (t.induced f) =
    measurable_space.generate_from (preimage f '' {s | is_open s }) :
      congr_arg measurable_space.generate_from $ set.ext $ assume s : set α,
      show (t.induced f).is_open s ↔ s ∈ preimage f '' {s | is_open s},
        by simp [topological_space.induced, set.image, eq_comm]; refl
  ... = (@borel β t).comap f : comap_generate_from.symm

section
variables [topological_space α]

lemma is_measurable_of_is_open : is_open s → is_measurable s := generate_measurable.basic s

lemma is_measurable_interior : is_measurable (interior s) :=
is_measurable_of_is_open is_open_interior

lemma is_measurable_ball [metric_space β] {x : β} {ε : ℝ} : is_measurable (metric.ball x ε) :=
is_measurable_of_is_open metric.is_open_ball

lemma is_measurable_of_is_closed (h : is_closed s) : is_measurable s :=
is_measurable.compl_iff.1 $ is_measurable_of_is_open h

lemma is_measurable_singleton [t1_space α] {x : α} : is_measurable ({x} : set α) :=
is_measurable_of_is_closed is_closed_singleton

lemma is_measurable_closure : is_measurable (closure s) :=
is_measurable_of_is_closed is_closed_closure

lemma measurable_of_continuous [topological_space β] {f : α → β} (h : continuous f) :
  measurable f :=
measurable_generate_from $ assume t ht, is_measurable_of_is_open $ h t ht

lemma borel_prod_le [topological_space β] :
  prod.measurable_space ≤ borel (α × β) :=
sup_le
  (comap_le_iff_le_map.mpr $ measurable_of_continuous continuous_fst)
  (comap_le_iff_le_map.mpr $ measurable_of_continuous continuous_snd)

lemma borel_induced {α β} [t : topological_space β] (f : α → β) :
  @borel α (t.induced f) = (borel β).comap f :=
comap_generate_from.symm

lemma borel_eq_subtype (s : set α) : borel s = subtype.measurable_space :=
borel_induced coe

lemma borel_prod [second_countable_topology α] [topological_space β] [second_countable_topology β] :
  prod.measurable_space = borel (α × β) :=
let ⟨a, ha₁, ha₂, ha₃, ha₄, ha₅⟩ := @is_open_generated_countable_inter α _ _ in
let ⟨b, hb₁, hb₂, hb₃, hb₄, hb₅⟩ := @is_open_generated_countable_inter β _ _ in
le_antisymm borel_prod_le begin
    have : prod.topological_space = generate_from {g | ∃u∈a, ∃v∈b, g = set.prod u v},
    { rw [ha₅, hb₅], exact prod_generate_from_generate_from_eq ha₄ hb₄ },
    rw [borel_eq_generate_from_of_subbasis this],
    exact generate_from_le (assume p ⟨u, hu, v, hv, eq⟩,
      have hu : is_open u, by rw [ha₅]; exact generate_open.basic _ hu,
      have hv : is_open v, by rw [hb₅]; exact generate_open.basic _ hv,
      eq.symm ▸ is_measurable_set_prod (is_measurable_of_is_open hu) (is_measurable_of_is_open hv))
end

lemma measurable_of_continuous2 {α β γ}
  [topological_space α] [second_countable_topology α]
  [topological_space β] [second_countable_topology β]
  [topological_space γ] [measurable_space δ] {f : δ → α} {g : δ → β} {c : α → β → γ}
  (h : continuous (λp:α×β, c p.1 p.2)) (hf : measurable f) (hg : measurable g) :
  measurable (λa, c (f a) (g a)) :=
show measurable ((λp:α×β, c p.1 p.2) ∘ (λa, (f a, g a))),
begin
  apply measurable.comp,
  { rw borel_prod,
    exact measurable_of_continuous h },
  { exact measurable.prod_mk hf hg }
end

lemma measurable.add
  [add_monoid α] [topological_add_monoid α] [second_countable_topology α] [measurable_space β]
  {f : β → α} {g : β → α} : measurable f → measurable g → measurable (λa, f a + g a) :=
measurable_of_continuous2 continuous_add

lemma measurable_finset_sum {ι : Type*}
  [add_comm_monoid α] [topological_add_monoid α] [second_countable_topology α] [measurable_space β]
  {f : ι → β → α} (s : finset ι) (hf : ∀i, measurable (f i)) : measurable (λa, s.sum (λi, f i a)) :=
finset.induction_on s
  (by simpa using measurable_const)
  (assume i s his ih, by simpa [his] using measurable.add (hf i) ih)

lemma measurable.neg
  [add_group α] [topological_add_group α] [measurable_space β] {f : β → α}
  (hf : measurable f) : measurable (λa, - f a) :=
(measurable_of_continuous continuous_neg).comp hf

lemma measurable_neg_iff
  [add_group α] [topological_add_group α] [measurable_space β] (f : β → α) :
  measurable (-f) ↔ measurable f :=
iff.intro
begin
  assume h,
  have := measurable.neg h,
  convert this,
  funext,
  simp only [pi.neg_apply, _root_.neg_neg]
end
$ measurable.neg

lemma measurable.sub
  [add_group α] [topological_add_group α] [second_countable_topology α] [measurable_space β]
  {f : β → α} {g : β → α} : measurable f → measurable g → measurable (λa, f a - g a) :=
measurable_of_continuous2 continuous_sub

lemma measurable.mul
  [monoid α] [topological_monoid α] [second_countable_topology α] [measurable_space β]
  {f : β → α} {g : β → α} : measurable f → measurable g → measurable (λa, f a * g a) :=
measurable_of_continuous2 continuous_mul

lemma is_measurable_le {α β}
  [topological_space α] [partial_order α] [ordered_topology α] [second_countable_topology α]
  [measurable_space β] {f : β → α} {g : β → α} (hf : measurable f) (hg : measurable g) :
  is_measurable {a | f a ≤ g a} :=
have is_measurable {p : α × α | p.1 ≤ p.2},
  by rw borel_prod; exact is_measurable_of_is_closed (ordered_topology.is_closed_le' _),
show is_measurable {a | (f a, g a).1 ≤ (f a, g a).2},
begin
  refine measurable.preimage _ this,
  exact measurable.prod_mk hf hg
end

lemma measurable.max {α β}
  [topological_space α] [decidable_linear_order α] [ordered_topology α] [second_countable_topology α]
  [measurable_space β] {f : β → α} {g : β → α} (hf : measurable f) (hg : measurable g) :
  measurable (λa, max (f a) (g a)) :=
measurable.if (is_measurable_le hf hg) hg hf

lemma measurable.min {α β}
  [topological_space α] [decidable_linear_order α] [ordered_topology α] [second_countable_topology α]
  [measurable_space β] {f : β → α} {g : β → α} (hf : measurable f) (hg : measurable g) :
  measurable (λa, min (f a) (g a)) :=
measurable.if (is_measurable_le hf hg) hf hg

-- generalize
lemma measurable_coe_int_real : measurable (λa, a : ℤ → ℝ) :=
assume s (hs : is_measurable s), by trivial

section ordered_topology
variables [linear_order α] [ordered_topology α] {a b c : α}

lemma is_measurable_Ioo : is_measurable (Ioo a b) := is_measurable_of_is_open is_open_Ioo

lemma is_measurable_Iio : is_measurable (Iio a) := is_measurable_of_is_open is_open_Iio

lemma is_measurable_Ico : is_measurable (Ico a b) :=
(is_measurable_of_is_closed $ is_closed_le continuous_const continuous_id).inter
  is_measurable_Iio

end ordered_topology

lemma measurable.is_lub {α} [topological_space α] [linear_order α]
  [orderable_topology α] [second_countable_topology α]
  {β} [measurable_space β] {ι} [encodable ι]
  {f : ι → β → α} {g : β → α} (hf : ∀ i, measurable (f i))
  (hg : ∀ b, is_lub {a | ∃ i, f i b = a} (g b)) :
  measurable g :=
begin
  rw borel_eq_generate_Ioi α,
  apply measurable_generate_from,
  rintro _ ⟨a, rfl⟩,
  have : {b | a < g b} = ⋃ i, {b | a < f i b},
  { simp [set.ext_iff], intro b, rw [lt_is_lub_iff (hg b)],
    exact ⟨λ ⟨_, ⟨i, rfl⟩, h⟩, ⟨i, h⟩, λ ⟨i, h⟩, ⟨_, ⟨i, rfl⟩, h⟩⟩ },
  show is_measurable {b | a < g b}, rw this,
  exact is_measurable.Union (λ i, hf i _
    (is_measurable_of_is_open (is_open_lt' _)))
end

lemma measurable.is_glb {α} [topological_space α] [linear_order α]
  [orderable_topology α] [second_countable_topology α]
  {β} [measurable_space β] {ι} [encodable ι]
  {f : ι → β → α} {g : β → α} (hf : ∀ i, measurable (f i))
  (hg : ∀ b, is_glb {a | ∃ i, f i b = a} (g b)) :
  measurable g :=
begin
  rw borel_eq_generate_Iio α,
  apply measurable_generate_from,
  rintro _ ⟨a, rfl⟩,
  have : {b | g b < a} = ⋃ i, {b | f i b < a},
  { simp [set.ext_iff], intro b, rw [is_glb_lt_iff (hg b)],
    exact ⟨λ ⟨_, ⟨i, rfl⟩, h⟩, ⟨i, h⟩, λ ⟨i, h⟩, ⟨_, ⟨i, rfl⟩, h⟩⟩ },
  show is_measurable {b | g b < a}, rw this,
  exact is_measurable.Union (λ i, hf i _
    (is_measurable_of_is_open (is_open_gt' _)))
end

lemma measurable.supr {α} [topological_space α] [complete_linear_order α]
  [orderable_topology α] [second_countable_topology α]
  {β} [measurable_space β] {ι} [encodable ι]
  {f : ι → β → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨆ i, f i b) :=
measurable.is_lub hf $ λ b, is_lub_supr

lemma measurable.infi {α} [topological_space α] [complete_linear_order α]
  [orderable_topology α] [second_countable_topology α]
  {β} [measurable_space β] {ι} [encodable ι]
  {f : ι → β → α} (hf : ∀ i, measurable (f i)) :
  measurable (λ b, ⨅ i, f i b) :=
measurable.is_glb hf $ λ b, is_glb_infi

lemma measurable.supr_Prop {α} [topological_space α] [complete_linear_order α]
  {β} [measurable_space β] {p : Prop} {f : β → α} (hf : measurable f) :
  measurable (λ b, ⨆ h : p, f b) :=
classical.by_cases
  (assume h : p, begin convert hf, funext, exact supr_pos h end)
  (assume h : ¬p, begin convert measurable_const, funext, exact supr_neg h end)

lemma measurable.infi_Prop {α} [topological_space α] [complete_linear_order α]
  {β} [measurable_space β] {p : Prop} {f : β → α} (hf : measurable f) :
  measurable (λ b, ⨅ h : p, f b) :=
classical.by_cases
  (assume h : p, begin convert hf, funext, exact infi_pos h end )
  (assume h : ¬p, begin convert measurable_const, funext, exact infi_neg h end)

end

def homemorph.to_measurable_equiv [topological_space α] [topological_space β] (h : α ≃ₜ β) :
  measurable_equiv α β :=
{ to_equiv := h.to_equiv,
  measurable_to_fun := measurable_of_continuous h.continuous_to_fun,
  measurable_inv_fun := measurable_of_continuous h.continuous_inv_fun }

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
    exact is_measurable_of_is_open (is_open_gt' _) }
end

end real

namespace nnreal
open filter

lemma measurable.add [measurable_space α] {f : α → nnreal} {g : α → nnreal} :
  measurable f → measurable g → measurable (λa, f a + g a) :=
measurable_of_continuous2 continuous_add

lemma measurable.sub [measurable_space α] {f g: α → nnreal}
  (hf : measurable f) (hg : measurable g) : measurable (λ a, f a - g a) :=
measurable_of_continuous2 continuous_sub hf hg

lemma measurable.mul [measurable_space α] {f : α → nnreal} {g : α → nnreal} :
  measurable f → measurable g → measurable (λa, f a * g a) :=
measurable_of_continuous2 continuous_mul

lemma measurable_of_real : measurable nnreal.of_real :=
measurable_of_continuous nnreal.continuous_of_real

end nnreal

namespace ennreal
open filter

lemma measurable_coe : measurable (coe : nnreal → ennreal) :=
measurable_of_continuous (continuous_coe.2 continuous_id)

def ennreal_equiv_nnreal : measurable_equiv {r : ennreal | r < ⊤} nnreal :=
{ to_fun    := λr, ennreal.to_nnreal r.1,
  inv_fun   := λr, ⟨r, coe_lt_top⟩,
  left_inv  := assume ⟨r, hr⟩, by simp [coe_to_nnreal (ne_of_lt hr)],
  right_inv := assume r, to_nnreal_coe,
  measurable_to_fun  :=
  begin
    rw [← borel_eq_subtype],
    refine measurable_of_continuous (continuous_iff_continuous_at.2 _),
    rintros ⟨r, hr⟩,
    simp [continuous_at, nhds_subtype_eq_comap],
    refine tendsto.comp (tendsto_to_nnreal (ne_of_lt hr)) tendsto_comap
  end,
  measurable_inv_fun := measurable.subtype_mk measurable_coe }

lemma measurable_of_measurable_nnreal [measurable_space α] {f : ennreal → α}
  (h : measurable (λp:nnreal, f p)) : measurable f :=
begin
  refine measurable_of_measurable_union_cover {⊤} {r : ennreal | r < ⊤}
    (is_measurable_of_is_closed $ is_closed_singleton)
    (is_measurable_of_is_open $ is_open_gt' _)
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

lemma measurable.mul {α : Type*} [measurable_space α] {f g : α → ennreal} :
  measurable f → measurable g → measurable (λa, f a * g a) :=
begin
  refine measurable_of_measurable_nnreal_nnreal (*) _ _ _,
  { simp only [ennreal.coe_mul.symm],
    exact measurable_coe.comp
      (measurable.mul (measurable.fst measurable_id) (measurable.snd measurable_id)) },
  { simp [top_mul],
    exact measurable.if
      (is_measurable_of_is_closed $ is_closed_eq continuous_id continuous_const)
      measurable_const
      measurable_const },
  { simp [mul_top],
    exact measurable.if
      (is_measurable_of_is_closed $ is_closed_eq continuous_id continuous_const)
      measurable_const
      measurable_const }
end

lemma measurable.add {α : Type*} [measurable_space α] {f g : α → ennreal} :
  measurable f → measurable g → measurable (λa, f a + g a) :=
begin
  refine measurable_of_measurable_nnreal_nnreal (+) _ _ _,
  { simp only [ennreal.coe_add.symm],
    exact measurable_coe.comp
      (measurable.add (measurable.fst measurable_id) (measurable.snd measurable_id)) },
  { simp [measurable_const] },
  { simp [measurable_const] }
end

lemma measurable.sub {α : Type*} [measurable_space α] {f g : α → ennreal} :
  measurable f → measurable g → measurable (λa, f a - g a) :=
begin
  refine measurable_of_measurable_nnreal_nnreal (has_sub.sub) _ _ _,
  { simp only [ennreal.coe_sub.symm],
    exact measurable_coe.comp
      (nnreal.measurable.sub (measurable.fst measurable_id) (measurable.snd measurable_id)) },
  { simp [measurable_const] },
  { simp [measurable_const] }
end

lemma measurable_of_real : measurable ennreal.of_real :=
measurable_of_continuous ennreal.continuous_of_real

end ennreal

namespace measure_theory

open topological_space

lemma measurable_smul' {α : Type*} {β : Type*} {γ : Type*}
  [semiring α] [topological_space α] [second_countable_topology α]
  [topological_space β] [add_comm_monoid β] [second_countable_topology β]
  [semimodule α β] [topological_semimodule α β] [measurable_space γ]
  {f : γ → α} {g : γ → β} (hf : measurable f) (hg : measurable g) :
  measurable (λ c, f c • g c) :=
measurable_of_continuous2 (continuous_fst.smul continuous_snd) hf hg

lemma measurable_smul {α : Type*} {β : Type*} {γ : Type*}
  [semiring α] [topological_space α]
  [topological_space β] [add_comm_monoid β]
  [semimodule α β] [topological_semimodule α β] [measurable_space γ]
  (c : α) {f : γ → β} (hf : measurable f) : measurable (λ x, c • f x) :=
measurable.comp (measurable_of_continuous (continuous_const.smul continuous_id)) hf

lemma measurable_smul_iff {α : Type*} {β : Type*} {γ : Type*}
  [division_ring α] [topological_space α]
  [topological_space β] [add_comm_monoid β]
  [semimodule α β] [topological_semimodule α β] [measurable_space γ]
  {c : α} (hc : c ≠ 0) (f : γ → β) : measurable (λ x, c • f x) ↔ measurable f :=
iff.intro
begin
  assume h,
  have eq : (λ (x : γ), c⁻¹ • (λ (x : γ), c • f x) x) = f,
  { funext, rw [smul_smul, inv_mul_cancel hc, one_smul] },
  have := measurable_smul c⁻¹ h,
  rwa eq at this
end
$ measurable_smul c

lemma measurable_dist' {α : Type*} [metric_space α] [second_countable_topology α] :
  measurable (λp:α×α, dist p.1 p.2) :=
begin
  rw [borel_prod],
  apply measurable_of_continuous,
  exact continuous_dist continuous_fst continuous_snd
end

lemma measurable_dist {α : Type*} [metric_space α] [second_countable_topology α]
  [measurable_space β] {f g : β → α} (hf : measurable f) (hg : measurable g) :
	measurable (λ b, dist (f b) (g b)) :=
measurable.comp measurable_dist' (measurable.prod_mk hf hg)

lemma measurable_nndist' {α : Type*} [metric_space α] [second_countable_topology α] :
  measurable (λp:α×α, nndist p.1 p.2) :=
begin
  rw [borel_prod],
  apply measurable_of_continuous,
  exact continuous_nndist continuous_fst continuous_snd
end

lemma measurable_nndist {α : Type*} [metric_space α] [second_countable_topology α]
  [measurable_space β] {f g : β → α} (hf : measurable f) (hg : measurable g) :
	measurable (λ b, nndist (f b) (g b)) :=
measurable.comp measurable_nndist' (measurable.prod_mk hf hg)

lemma measurable_edist' {α : Type*} [epremetric_space α] [second_countable_topology α] :
  measurable (λp:α×α, edist p.1 p.2) :=
begin
  rw [borel_prod],
  apply measurable_of_continuous,
  exact continuous_edist continuous_fst continuous_snd
end

lemma measurable_edist {α : Type*} [epremetric_space α] [second_countable_topology α]
  [measurable_space β] {f g : β → α} (hf : measurable f) (hg : measurable g) :
	measurable (λ b, edist (f b) (g b)) :=
measurable.comp measurable_edist' (measurable.prod_mk hf hg)

lemma measurable_norm' {α : Type*} [normed_group α] : measurable (norm : α → ℝ) :=
measurable_of_continuous continuous_norm

lemma measurable_norm {α : Type*} [normed_group α] [measurable_space β]
  {f : β → α} (hf : measurable f) : measurable (λa, norm (f a)) :=
measurable.comp measurable_norm' hf

lemma measurable_nnnorm' {α : Type*} [normed_group α] : measurable (nnnorm : α → nnreal) :=
measurable_of_continuous continuous_nnnorm

lemma measurable_nnnorm {α : Type*} [normed_group α] [measurable_space β]
  {f : β → α} (hf : measurable f) : measurable (λa, nnnorm (f a)) :=
measurable.comp measurable_nnnorm' hf

lemma measurable_coe_nnnorm {α : Type*} [normed_group α] [measurable_space β]
  {f : β → α} (hf : measurable f) : measurable (λa, (nnnorm (f a) : ennreal)) :=
measurable.comp ennreal.measurable_coe $ measurable_nnnorm hf

end measure_theory
