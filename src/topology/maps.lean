/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

Specific classes of maps between topological spaces: embeddings, open maps, quotient maps.
-/
import topology.order topology.separation
noncomputable theory

open set filter lattice
local attribute [instance] classical.prop_decidable

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section embedding

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : set α`, `s` is open iff it is the preimage of an open set. -/
def embedding [tα : topological_space α] [tβ : topological_space β] (f : α → β) : Prop :=
function.injective f ∧ tα = tβ.induced f

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

lemma embedding_id : embedding (@id α) :=
⟨assume a₁ a₂ h, h, induced_id.symm⟩

lemma embedding_compose {f : α → β} {g : β → γ} (hf : embedding f) (hg : embedding g) :
  embedding (g ∘ f) :=
⟨assume a₁ a₂ h, hf.left $ hg.left h, by rw [hf.right, hg.right, induced_compose]⟩

lemma embedding_prod_mk {f : α → β} {g : γ → δ} (hf : embedding f) (hg : embedding g) :
  embedding (λx:α×γ, (f x.1, g x.2)) :=
⟨assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, by simp; exact assume h₁ h₂, ⟨hf.left h₁, hg.left h₂⟩,
  by rw [prod.topological_space, prod.topological_space, hf.right, hg.right,
         induced_compose, induced_compose, induced_sup, induced_compose, induced_compose]⟩

lemma embedding_of_embedding_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g)
  (hgf : embedding (g ∘ f)) : embedding f :=
⟨assume a₁ a₂ h, hgf.left $ by simp [h, (∘)],
  le_antisymm
    (by rw [hgf.right, ← continuous_iff_induced_le];
        apply continuous_induced_dom.comp hg)
    (by rwa ← continuous_iff_induced_le)⟩

lemma embedding_open {f : α → β} {s : set α}
  (hf : embedding f) (h : is_open (range f)) (hs : is_open s) : is_open (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.right] at hs; exact hs in
have is_open (t ∩ range f), from is_open_inter ht h,
h_eq ▸ by rwa [image_preimage_eq_inter_range]

lemma embedding_is_closed {f : α → β} {s : set α}
  (hf : embedding f) (h : is_closed (range f)) (hs : is_closed s) : is_closed (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.right, is_closed_induced_iff] at hs; exact hs in
have is_closed (t ∩ range f), from is_closed_inter ht h,
h_eq.symm ▸ by rwa [image_preimage_eq_inter_range]

lemma embedding.map_nhds_eq [topological_space α] [topological_space β] {f : α → β}
  (hf : embedding f) (a : α) (h : range f ∈ nhds (f a)) : (nhds a).map f = nhds (f a) :=
by rw [hf.2]; exact map_nhds_induced_eq h

lemma embedding.tendsto_nhds_iff {ι : Type*}
  {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : embedding g) :
  tendsto f a (nhds b) ↔ tendsto (g ∘ f) a (nhds (g b)) :=
by rw [tendsto, tendsto, hg.right, nhds_induced_eq_comap, ← map_le_iff_le_comap, filter.map_map]

lemma embedding.continuous_iff {f : α → β} {g : β → γ} (hg : embedding g) :
  continuous f ↔ continuous (g ∘ f) :=
by simp [continuous_iff_continuous_at, continuous_at, embedding.tendsto_nhds_iff hg]

lemma embedding.continuous {f : α → β} (hf : embedding f) : continuous f :=
hf.continuous_iff.mp continuous_id

lemma embedding.closure_eq_preimage_closure_image {e : α → β} (he : embedding e) (s : set α) :
  closure s = e ⁻¹' closure (e '' s) :=
by ext x; rw [set.mem_preimage_eq, ← closure_induced he.1, he.2]

end embedding


-- TODO: use embeddings from above!
structure dense_embedding [topological_space α] [topological_space β] (e : α → β) : Prop :=
(dense   : ∀x, x ∈ closure (range e))
(inj     : function.injective e)
(induced : ∀a, comap e (nhds (e a)) = nhds a)

theorem dense_embedding.mk'
  [topological_space α] [topological_space β] (e : α → β)
  (c     : continuous e)
  (dense : ∀x, x ∈ closure (range e))
  (inj   : function.injective e)
  (H     : ∀ (a:α) s ∈ nhds a,
    ∃t ∈ nhds (e a), ∀ b, e b ∈ t → b ∈ s) :
  dense_embedding e :=
⟨dense, inj, λ a, le_antisymm
  (by simpa [le_def] using H a)
  (tendsto_iff_comap.1 $ c.tendsto _)⟩

namespace dense_embedding
variables [topological_space α] [topological_space β]
variables {e : α → β} (de : dense_embedding e)

protected lemma embedding (de : dense_embedding e) : embedding e :=
⟨de.inj, eq_of_nhds_eq_nhds begin intro a, rw [← de.induced a, nhds_induced_eq_comap] end⟩

protected lemma continuous_at (de : dense_embedding e) {a : α} : continuous_at e a :=
by rw [continuous_at, ←de.induced a]; exact tendsto_comap

protected lemma continuous (de : dense_embedding e) {a : α} : continuous e :=
continuous_iff_continuous_at.mpr $ λ a, de.continuous_at

lemma inj_iff (de : dense_embedding e) {x y} : e x = e y ↔ x = y := de.inj.eq_iff

lemma closure_range : closure (range e) = univ :=
let h := de.dense in
set.ext $ assume x, ⟨assume _, trivial, assume _, @h x⟩

lemma self_sub_closure_image_preimage_of_open {s : set β} (de : dense_embedding e) :
  is_open s → s ⊆ closure (e '' (e ⁻¹' s)) :=
begin
  intros s_op b b_in_s,
  rw [image_preimage_eq_inter_range, mem_closure_iff],
  intros U U_op b_in,
  rw ←inter_assoc,
  have ne_e : U ∩ s ≠ ∅ := ne_empty_of_mem ⟨b_in, b_in_s⟩,
  exact (dense_iff_inter_open.1 de.closure_range) _ (is_open_inter U_op s_op) ne_e
end

lemma closure_image_nhds_of_nhds {s : set α} {a : α} (de : dense_embedding e) :
  s ∈ nhds a → closure (e '' s) ∈ nhds (e a) :=
begin
  rw [← de.induced a, mem_comap_sets],
  intro h,
  rcases h with ⟨t, t_nhd, sub⟩,
  rw mem_nhds_sets_iff at t_nhd,
  rcases t_nhd with ⟨U, U_sub, ⟨U_op, e_a_in_U⟩⟩,
  have := calc e ⁻¹' U ⊆ e⁻¹' t : preimage_mono U_sub
                   ... ⊆ s      : sub,
  have := calc U ⊆ closure (e '' (e ⁻¹' U)) : self_sub_closure_image_preimage_of_open de U_op
             ... ⊆ closure (e '' s)         : closure_mono (image_subset e this),
  have U_nhd : U ∈ nhds (e a) := mem_nhds_sets U_op e_a_in_U,
  exact (nhds (e a)).sets_of_superset U_nhd this
end

variables [topological_space δ] {f : γ → α} {g : γ → δ} {h : δ → β}
/--
 γ -f→ α
g↓     ↓e
 δ -h→ β
-/
lemma tendsto_comap_nhds_nhds  {d : δ} {a : α} (de : dense_embedding e) (H : tendsto h (nhds d) (nhds (e a)))
  (comm : h ∘ g = e ∘ f) : tendsto f (comap g (nhds d)) (nhds a) :=
begin
  have lim1 : map g (comap g (nhds d)) ≤ nhds d := map_comap_le,
  replace lim1 : map h (map g (comap g (nhds d))) ≤ map h (nhds d) := map_mono lim1,
  rw [filter.map_map, comm, ← filter.map_map, map_le_iff_le_comap] at lim1,
  have lim2 :  comap e (map h (nhds d)) ≤  comap e  (nhds (e a)) := comap_mono H,
  rw de.induced at lim2,
  exact le_trans lim1 lim2,
end

protected lemma nhds_inf_neq_bot (de : dense_embedding e) {b : β} : nhds b ⊓ principal (range e) ≠ ⊥ :=
begin
  have h := de.dense,
  simp [closure_eq_nhds] at h,
  exact h _
end

lemma comap_nhds_neq_bot (de : dense_embedding e) {b : β} : comap e (nhds b) ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $
assume s ⟨t, ht, (hs : e ⁻¹' t ⊆ s)⟩,
have t ∩ range e ∈ nhds b ⊓ principal (range e),
  from inter_mem_inf_sets ht (subset.refl _),
let ⟨_, ⟨hx₁, y, rfl⟩⟩ := inhabited_of_mem_sets de.nhds_inf_neq_bot this in
subset_ne_empty hs $ ne_empty_of_mem hx₁

variables [topological_space γ]
/-- If `e : α → β` is a dense embedding, then any function `α → γ` extends to a function `β → γ`.
It only extends the parts of `β` which are not mapped by `e`, everything else equal to `f (e a)`.
This allows us to gain equality even if `γ` is not T2. -/
def extend (de : dense_embedding e) (f : α → γ) (b : β) : γ :=
have nonempty γ, from
  let ⟨_, ⟨_, a, _⟩⟩ := exists_mem_of_ne_empty (mem_closure_iff.1 (de.dense b) _ is_open_univ trivial) in
  ⟨f a⟩,
if hb : b ∈ range e
then f (classical.some hb)
else @lim _ _ (classical.inhabited_of_nonempty this) (map f (comap e (nhds b)))

lemma extend_e_eq {f : α → γ} (a : α) : de.extend f (e a) = f a :=
have e a ∈ range e := ⟨a, rfl⟩,
begin
  simp [extend, this],
  congr,
  refine classical.some_spec2 (λx, x = a) _,
  exact assume a h, de.inj h
end

lemma extend_eq [t2_space γ] {b : β} {c : γ} {f : α → γ} (hf : map f (comap e (nhds b)) ≤ nhds c) :
  de.extend f b = c :=
begin
  by_cases hb : b ∈ range e,
  { rcases hb with ⟨a, rfl⟩,
    rw [extend_e_eq],
    have f_a_c : tendsto f (pure a) (nhds c),
    { rw [de.induced] at hf,
      refine le_trans (map_mono _) hf,
      exact pure_le_nhds a },
    have f_a_fa : tendsto f (pure a) (nhds (f a)),
    { rw [tendsto, filter.map_pure], exact pure_le_nhds _  },
    exact tendsto_nhds_unique pure_neq_bot f_a_fa f_a_c },
  { simp [extend, hb],
    exact @lim_eq _ _ (id _) _ _ _ (by simp; exact comap_nhds_neq_bot de) hf }
end

lemma tendsto_extend [regular_space γ] {b : β} {f : α → γ} (de : dense_embedding e)
  (hf : {b | ∃c, tendsto f (comap e $ nhds b) (nhds c)} ∈ nhds b) :
  tendsto (de.extend f) (nhds b) (nhds (de.extend f b)) :=
let φ := {b | tendsto f (comap e $ nhds b) (nhds $ de.extend f b)} in
have hφ : φ ∈ nhds b,
  from (nhds b).sets_of_superset hf $ assume b ⟨c, hc⟩,
    show tendsto f (comap e (nhds b)) (nhds (de.extend f b)), from (de.extend_eq hc).symm ▸ hc,
assume s hs,
let ⟨s'', hs''₁, hs''₂, hs''₃⟩ := nhds_is_closed hs in
let ⟨s', hs'₁, (hs'₂ : e ⁻¹' s' ⊆ f ⁻¹' s'')⟩ := mem_of_nhds hφ hs''₁ in
let ⟨t, (ht₁ : t ⊆ φ ∩ s'), ht₂, ht₃⟩ := mem_nhds_sets_iff.mp $ inter_mem_sets hφ hs'₁ in
have h₁ : closure (f '' (e ⁻¹' s')) ⊆ s'',
  by rw [closure_subset_iff_subset_of_is_closed hs''₃, image_subset_iff]; exact hs'₂,
have h₂ : t ⊆ de.extend f ⁻¹' closure (f '' (e ⁻¹' t)), from
  assume b' hb',
  have nhds b' ≤ principal t, by simp; exact mem_nhds_sets ht₂ hb',
  have map f (comap e (nhds b')) ≤ nhds (de.extend f b') ⊓ principal (f '' (e ⁻¹' t)),
    from calc _ ≤ map f (comap e (nhds b' ⊓ principal t)) : map_mono $ comap_mono $ le_inf (le_refl _) this
      ... ≤ map f (comap e (nhds b')) ⊓ map f (comap e (principal t)) :
        le_inf (map_mono $ comap_mono $ inf_le_left) (map_mono $ comap_mono $ inf_le_right)
      ... ≤ map f (comap e (nhds b')) ⊓ principal (f '' (e ⁻¹' t)) : by simp [le_refl]
      ... ≤ _ : inf_le_inf ((ht₁ hb').left) (le_refl _),
  show de.extend f b' ∈ closure (f '' (e ⁻¹' t)),
  begin
    rw [closure_eq_nhds],
    apply neq_bot_of_le_neq_bot _ this,
    simp,
    exact de.comap_nhds_neq_bot
  end,
(nhds b).sets_of_superset
  (show t ∈ nhds b, from mem_nhds_sets ht₂ ht₃)
  (calc t ⊆ de.extend f ⁻¹' closure (f '' (e ⁻¹' t)) : h₂
    ... ⊆ de.extend f ⁻¹' closure (f '' (e ⁻¹' s')) :
      preimage_mono $ closure_mono $ image_subset f $ preimage_mono $ subset.trans ht₁ $ inter_subset_right _ _
    ... ⊆ de.extend f ⁻¹' s'' : preimage_mono h₁
    ... ⊆ de.extend f ⁻¹' s : preimage_mono hs''₂)

lemma continuous_extend [regular_space γ] {f : α → γ} (de : dense_embedding e)
  (hf : ∀b, ∃c, tendsto f (comap e (nhds b)) (nhds c)) : continuous (de.extend f) :=
continuous_iff_continuous_at.mpr $ assume b, de.tendsto_extend $ univ_mem_sets' hf

end dense_embedding


/-- A function between topological spaces is a quotient map if it is surjective,
  and for all `s : set β`, `s` is open iff its preimage is an open set. -/
def quotient_map {α : Type*} {β : Type*} [tα : topological_space α] [tβ : topological_space β] (f : α → β) : Prop :=
function.surjective f ∧ tβ = tα.coinduced f

namespace quotient_map
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

protected lemma id : quotient_map (@id α) :=
⟨assume a, ⟨a, rfl⟩, coinduced_id.symm⟩

protected lemma comp {f : α → β} {g : β → γ} (hf : quotient_map f) (hg : quotient_map g) :
  quotient_map (g ∘ f) :=
⟨function.surjective_comp hg.left hf.left, by rw [hg.right, hf.right, coinduced_compose]⟩

protected lemma of_quotient_map_compose {f : α → β} {g : β → γ}
  (hf : continuous f) (hg : continuous g)
  (hgf : quotient_map (g ∘ f)) : quotient_map g :=
⟨assume b, let ⟨a, h⟩ := hgf.left b in ⟨f a, h⟩,
  le_antisymm
    (by rwa ← continuous_iff_le_coinduced)
    (by rw [hgf.right, ← continuous_iff_le_coinduced];
        apply hf.comp continuous_coinduced_rng)⟩

protected lemma continuous_iff {f : α → β} {g : β → γ} (hf : quotient_map f) :
  continuous g ↔ continuous (g ∘ f) :=
by rw [continuous_iff_le_coinduced, continuous_iff_le_coinduced, hf.right, coinduced_compose]

protected lemma continuous {f : α → β} (hf : quotient_map f) : continuous f :=
hf.continuous_iff.mp continuous_id

end quotient_map

section is_open_map
variables [topological_space α] [topological_space β]

def is_open_map (f : α → β) := ∀ U : set α, is_open U → is_open (f '' U)

lemma is_open_map_iff_nhds_le (f : α → β) : is_open_map f ↔ ∀(a:α), nhds (f a) ≤ (nhds a).map f :=
begin
  split,
  { assume h a s hs,
    rcases mem_nhds_sets_iff.1 hs with ⟨t, hts, ht, hat⟩,
    exact filter.mem_sets_of_superset
      (mem_nhds_sets (h t ht) (mem_image_of_mem _ hat))
      (image_subset_iff.2 hts) },
  { refine assume h s hs, is_open_iff_mem_nhds.2 _,
    rintros b ⟨a, ha, rfl⟩,
    exact h _ (filter.image_mem_map $ mem_nhds_sets hs ha) }
end

end is_open_map

namespace is_open_map
variables [topological_space α] [topological_space β] [topological_space γ]
open function

protected lemma id : is_open_map (@id α) := assume s hs, by rwa [image_id]

protected lemma comp
  {f : α → β} {g : β → γ} (hf : is_open_map f) (hg : is_open_map g) : is_open_map (g ∘ f) :=
by intros s hs; rw [image_comp]; exact hg _ (hf _ hs)

lemma of_inverse {f : α → β} {f' : β → α}
  (h : continuous f') (l_inv : left_inverse f f') (r_inv : right_inverse f f') :
  is_open_map f :=
assume s hs,
have f' ⁻¹' s = f '' s, by ext x; simp [mem_image_iff_of_inverse r_inv l_inv],
this ▸ h s hs

lemma to_quotient_map {f : α → β}
  (open_map : is_open_map f) (cont : continuous f) (surj : function.surjective f) :
  quotient_map f :=
⟨ surj,
  begin
    ext s,
    show is_open s ↔ is_open (f ⁻¹' s),
    split,
    { exact cont s },
    { assume h,
      rw ← @image_preimage_eq _ _ _ s surj,
      exact open_map _ h }
  end⟩

end is_open_map

section is_closed_map
variables [topological_space α] [topological_space β]

def is_closed_map (f : α → β) := ∀ U : set α, is_closed U → is_closed (f '' U)

end is_closed_map

namespace is_closed_map

variables [topological_space α] [topological_space β] [topological_space γ]
open function

protected lemma id : is_closed_map (@id α) := assume s hs, by rwa image_id

protected lemma comp {f : α → β} {g : β → γ} (hf : is_closed_map f) (hg : is_closed_map g) :
  is_closed_map (g ∘ f) :=
by { intros s hs, rw image_comp, exact hg _ (hf _ hs) }

lemma of_inverse {f : α → β} {f' : β → α}
  (h : continuous f') (l_inv : left_inverse f f') (r_inv : right_inverse f f') :
  is_closed_map f :=
assume s hs,
have f' ⁻¹' s = f '' s, by ext x; simp [mem_image_iff_of_inverse r_inv l_inv],
this ▸ continuous_iff_is_closed.mp h s hs

end is_closed_map

section sierpinski
variables [topological_space α]

@[simp] lemma is_open_singleton_true : is_open ({true} : set Prop) :=
topological_space.generate_open.basic _ (by simp)

lemma continuous_Prop {p : α → Prop} : continuous p ↔ is_open {x | p x} :=
⟨assume h : continuous p,
  have is_open (p ⁻¹' {true}),
    from h _ is_open_singleton_true,
  by simp [preimage, eq_true] at this; assumption,
  assume h : is_open {x | p x},
  continuous_generated_from $ assume s (hs : s ∈ {{true}}),
    by simp at hs; simp [hs, preimage, eq_true, h]⟩

end sierpinski

section closed_embedding
variables [topological_space α] [topological_space β] [topological_space γ]

/-- A closed embedding is an embedding with closed image. -/
def closed_embedding (f : α → β) : Prop := embedding f ∧ is_closed (range f)

lemma closed_embedding.closed_iff_image_closed {f : α → β} (hf : closed_embedding f)
  {s : set α} : is_closed s ↔ is_closed (f '' s) :=
⟨embedding_is_closed hf.1 hf.2,
 λ h, begin
   convert ←continuous_iff_is_closed.mp hf.1.continuous _ h,
   apply preimage_image_eq _ hf.1.1
 end⟩

lemma closed_embedding.closed_iff_preimage_closed {f : α → β} (hf : closed_embedding f)
  {s : set β} (hs : s ⊆ range f) : is_closed s ↔ is_closed (f ⁻¹' s) :=
begin
  convert ←hf.closed_iff_image_closed.symm,
  rwa [image_preimage_eq_inter_range, inter_eq_self_of_subset_left]
end

lemma closed_embedding_of_continuous_injective_closed {f : α → β} (h₁ : continuous f)
  (h₂ : function.injective f) (h₃ : is_closed_map f) : closed_embedding f :=
begin
  refine ⟨⟨h₂, _⟩, by convert h₃ univ is_closed_univ; simp⟩,
  apply le_antisymm _ (continuous_iff_induced_le.mp h₁),
  intro s',
  change is_open _ ≤ is_open _,
  rw [←is_closed_compl_iff, ←is_closed_compl_iff],
  generalize : -s' = s,
  rw is_closed_induced_iff,
  refine λ hs, ⟨f '' s, h₃ s hs, _⟩,
  rw preimage_image_eq _ h₂
end

lemma closed_embedding_id : closed_embedding (@id α) :=
⟨embedding_id, by convert is_closed_univ; apply range_id⟩

lemma closed_embedding_compose {f : α → β} {g : β → γ}
  (hf : closed_embedding f) (hg : closed_embedding g) : closed_embedding (g ∘ f) :=
⟨embedding_compose hf.1 hg.1, show is_closed (range (g ∘ f)),
 by rw [range_comp, ←hg.closed_iff_image_closed]; exact hf.2⟩

end closed_embedding
