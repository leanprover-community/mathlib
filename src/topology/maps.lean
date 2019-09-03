/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot

Specific classes of maps between topological spaces: embeddings, open maps, quotient maps.
-/
import topology.order topology.separation
noncomputable theory

open set filter lattice
open_locale classical

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section dense_range
variables [topological_space α] [topological_space β] [topological_space γ]
          (f : α → β) (g : β → γ)

def dense_range := ∀ x, x ∈ closure (range f)

lemma dense_range_iff_closure_eq : dense_range f ↔ closure (range f) = univ :=
eq_univ_iff_forall.symm

variables {f}

lemma dense_range.comp (hg : dense_range g) (hf : dense_range f) (cg : continuous g) :
  dense_range (g ∘ f) :=
begin
  have : g '' (closure $ range f) ⊆ closure (g '' range f),
    from image_closure_subset_closure_image cg,
  have : closure (g '' closure (range f)) ⊆ closure (g '' range f),
    by simpa [closure_closure] using (closure_mono this),
  intro c,
  rw range_comp,
  apply this,
  rw [(dense_range_iff_closure_eq f).1 hf, image_univ],
  exact hg c
end

lemma dense_range.inhabited (df : dense_range f) (b : β) : inhabited α :=
⟨begin
  have := exists_mem_of_ne_empty (mem_closure_iff.1 (df b) _ is_open_univ trivial),
  simp only [mem_range, univ_inter] at this,
  exact classical.some (classical.some_spec this),
 end⟩

lemma dense_range.nonempty (hf : dense_range f) : nonempty α ↔ nonempty β :=
begin
  split ; intro h ; cases classical.inhabited_of_nonempty h with x,
  { exact ⟨f x⟩ },
  { rcases exists_mem_of_ne_empty (mem_closure_iff.1 (hf x) _ is_open_univ trivial)
      with ⟨_, ⟨_, a, _⟩⟩,
    exact ⟨a⟩ },
end
end dense_range

section inducing
structure inducing [tα : topological_space α] [tβ : topological_space β] (f : α → β) : Prop :=
(induced : tα = tβ.induced f)

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

lemma inducing_id : inducing (@id α) :=
⟨induced_id.symm⟩

lemma inducing.comp {f : α → β} {g : β → γ} (hg : inducing g) (hf : inducing f) :
  inducing (g ∘ f) :=
⟨by rw [hf.induced, hg.induced, induced_compose]⟩

lemma inducing.prod_mk {f : α → β} {g : γ → δ} (hf : inducing f) (hg : inducing g) :
  inducing (λx:α×γ, (f x.1, g x.2)) :=
⟨by rw [prod.topological_space, prod.topological_space, hf.induced, hg.induced,
         induced_compose, induced_compose, induced_inf, induced_compose, induced_compose]⟩

lemma inducing_of_inducing_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g)
  (hgf : inducing (g ∘ f)) : inducing f :=
⟨le_antisymm
    (by rwa ← continuous_iff_le_induced)
    (by { rw [hgf.induced, ← continuous_iff_le_induced], apply hg.comp continuous_induced_dom })⟩

lemma inducing_open {f : α → β} {s : set α}
  (hf : inducing f) (h : is_open (range f)) (hs : is_open s) : is_open (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.induced] at hs; exact hs in
have is_open (t ∩ range f), from is_open_inter ht h,
h_eq ▸ by rwa [image_preimage_eq_inter_range]

lemma inducing_is_closed {f : α → β} {s : set α}
  (hf : inducing f) (h : is_closed (range f)) (hs : is_closed s) : is_closed (f '' s) :=
let ⟨t, ht, h_eq⟩ := by rw [hf.induced, is_closed_induced_iff] at hs; exact hs in
have is_closed (t ∩ range f), from is_closed_inter ht h,
h_eq.symm ▸ by rwa [image_preimage_eq_inter_range]

lemma inducing.nhds_eq_comap [topological_space α] [topological_space β] {f : α → β}
  (hf : inducing f) : ∀ (a : α), nhds a = comap f (nhds $ f a) :=
(induced_iff_nhds_eq f).1 hf.induced

lemma inducing.map_nhds_eq [topological_space α] [topological_space β] {f : α → β}
  (hf : inducing f) (a : α) (h : range f ∈ nhds (f a)) : (nhds a).map f = nhds (f a) :=
hf.induced.symm ▸ map_nhds_induced_eq h

lemma inducing.tendsto_nhds_iff {ι : Type*}
  {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : inducing g) :
  tendsto f a (nhds b) ↔ tendsto (g ∘ f) a (nhds (g b)) :=
by rw [tendsto, tendsto, hg.induced, nhds_induced, ← map_le_iff_le_comap, filter.map_map]

lemma inducing.continuous_iff {f : α → β} {g : β → γ} (hg : inducing g) :
  continuous f ↔ continuous (g ∘ f) :=
by simp [continuous_iff_continuous_at, continuous_at, inducing.tendsto_nhds_iff hg]

lemma inducing.continuous {f : α → β} (hf : inducing f) : continuous f :=
hf.continuous_iff.mp continuous_id
end inducing
section embedding

/-- A function between topological spaces is an embedding if it is injective,
  and for all `s : set α`, `s` is open iff it is the preimage of an open set. -/
structure embedding [tα : topological_space α] [tβ : topological_space β] (f : α → β)
  extends inducing f : Prop :=
(inj : function.injective f)

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

def embedding.mk' (f : α → β) (inj : function.injective f)
  (induced : ∀a, comap f (nhds (f a)) = nhds a) : embedding f :=
⟨⟨(induced_iff_nhds_eq f).2 (λ a, (induced a).symm)⟩, inj⟩

lemma embedding_id : embedding (@id α) :=
⟨inducing_id, assume a₁ a₂ h, h⟩

lemma embedding.comp {f : α → β} {g : β → γ} (hg : embedding g) (hf : embedding f) :
  embedding (g ∘ f) :=
{ inj:= assume a₁ a₂ h, hf.inj $ hg.inj h,
  ..hg.to_inducing.comp hf.to_inducing }

lemma embedding.prod_mk {f : α → β} {g : γ → δ} (hf : embedding f) (hg : embedding g) :
  embedding (λx:α×γ, (f x.1, g x.2)) :=
{ inj := assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, by simp; exact assume h₁ h₂, ⟨hf.inj h₁, hg.inj h₂⟩,
  ..hf.to_inducing.prod_mk hg.to_inducing }


lemma embedding_of_embedding_compose {f : α → β} {g : β → γ} (hf : continuous f) (hg : continuous g)
  (hgf : embedding (g ∘ f)) : embedding f :=
{ induced := (inducing_of_inducing_compose hf hg hgf.to_inducing).induced,
  inj := assume a₁ a₂ h, hgf.inj $ by simp [h, (∘)] }

lemma embedding_open {f : α → β} {s : set α}
  (hf : embedding f) (h : is_open (range f)) (hs : is_open s) : is_open (f '' s) :=
inducing_open hf.1 h hs

lemma embedding_is_closed {f : α → β} {s : set α}
  (hf : embedding f) (h : is_closed (range f)) (hs : is_closed s) : is_closed (f '' s) :=
inducing_is_closed hf.1 h hs

lemma embedding.map_nhds_eq [topological_space α] [topological_space β] {f : α → β}
  (hf : embedding f) (a : α) (h : range f ∈ nhds (f a)) : (nhds a).map f = nhds (f a) :=
inducing.map_nhds_eq hf.1 a h

lemma embedding.tendsto_nhds_iff {ι : Type*}
  {f : ι → β} {g : β → γ} {a : filter ι} {b : β} (hg : embedding g) :
  tendsto f a (nhds b) ↔ tendsto (g ∘ f) a (nhds (g b)) :=
by rw [tendsto, tendsto, hg.induced, nhds_induced, ← map_le_iff_le_comap, filter.map_map]

lemma embedding.continuous_iff {f : α → β} {g : β → γ} (hg : embedding g) :
  continuous f ↔ continuous (g ∘ f) :=
inducing.continuous_iff hg.1

lemma embedding.continuous {f : α → β} (hf : embedding f) : continuous f :=
inducing.continuous hf.1

lemma embedding.closure_eq_preimage_closure_image {e : α → β} (he : embedding e) (s : set α) :
  closure s = e ⁻¹' closure (e '' s) :=
by { ext x, rw [set.mem_preimage, ← closure_induced he.inj, he.induced] }

end embedding

structure dense_inducing [topological_space α] [topological_space β] (i : α → β)
  extends inducing i : Prop :=
(dense   : ∀x, x ∈ closure (range i))

namespace dense_inducing
variables [topological_space α] [topological_space β]
variables {i : α → β} (di : dense_inducing i)

lemma nhds_eq_comap (di : dense_inducing i) :
  ∀ a : α, nhds a = comap i (nhds $ i a) :=
di.induced.symm ▸ nhds_induced i

protected lemma continuous_at (di : dense_inducing i) {a : α} : continuous_at i a :=
by rw [continuous_at, di.nhds_eq_comap a]; exact tendsto_comap

protected lemma continuous (di : dense_inducing i) : continuous i :=
continuous_iff_continuous_at.mpr $ λ a, di.continuous_at

lemma closure_range : closure (range i) = univ :=
let h := di.dense in
set.ext $ assume x, ⟨assume _, trivial, assume _, @h x⟩

lemma self_sub_closure_image_preimage_of_open {s : set β} (di : dense_inducing i) :
  is_open s → s ⊆ closure (i '' (i ⁻¹' s)) :=
begin
  intros s_op b b_in_s,
  rw [image_preimage_eq_inter_range, mem_closure_iff],
  intros U U_op b_in,
  rw ←inter_assoc,
  have ne_e : U ∩ s ≠ ∅ := ne_empty_of_mem ⟨b_in, b_in_s⟩,
  exact (dense_iff_inter_open.1 di.closure_range) _ (is_open_inter U_op s_op) ne_e
end

lemma closure_image_nhds_of_nhds {s : set α} {a : α} (di : dense_inducing i) :
  s ∈ nhds a → closure (i '' s) ∈ nhds (i a) :=
begin
  rw [di.nhds_eq_comap a, mem_comap_sets],
  intro h,
  rcases h with ⟨t, t_nhd, sub⟩,
  rw mem_nhds_sets_iff at t_nhd,
  rcases t_nhd with ⟨U, U_sub, ⟨U_op, e_a_in_U⟩⟩,
  have := calc i ⁻¹' U ⊆ i⁻¹' t : preimage_mono U_sub
                   ... ⊆ s      : sub,
  have := calc U ⊆ closure (i '' (i ⁻¹' U)) : self_sub_closure_image_preimage_of_open di U_op
             ... ⊆ closure (i '' s)         : closure_mono (image_subset i this),
  have U_nhd : U ∈ nhds (i a) := mem_nhds_sets U_op e_a_in_U,
  exact (nhds (i a)).sets_of_superset U_nhd this
end

variables [topological_space δ] {f : γ → α} {g : γ → δ} {h : δ → β}
/--
 γ -f→ α
g↓     ↓e
 δ -h→ β
-/
lemma tendsto_comap_nhds_nhds  {d : δ} {a : α} (di : dense_inducing i) (H : tendsto h (nhds d) (nhds (i a)))
  (comm : h ∘ g = i ∘ f) : tendsto f (comap g (nhds d)) (nhds a) :=
begin
  have lim1 : map g (comap g (nhds d)) ≤ nhds d := map_comap_le,
  replace lim1 : map h (map g (comap g (nhds d))) ≤ map h (nhds d) := map_mono lim1,
  rw [filter.map_map, comm, ← filter.map_map, map_le_iff_le_comap] at lim1,
  have lim2 :  comap i (map h (nhds d)) ≤  comap i  (nhds (i a)) := comap_mono H,
  rw ← di.nhds_eq_comap at lim2,
  exact le_trans lim1 lim2,
end

protected lemma nhds_inf_neq_bot (di : dense_inducing i) {b : β} : nhds b ⊓ principal (range i) ≠ ⊥ :=
begin
  have h := di.dense,
  simp [closure_eq_nhds] at h,
  exact h _
end

lemma comap_nhds_neq_bot (di : dense_inducing i) {b : β} : comap i (nhds b) ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $
assume s ⟨t, ht, (hs : i ⁻¹' t ⊆ s)⟩,
have t ∩ range i ∈ nhds b ⊓ principal (range i),
  from inter_mem_inf_sets ht (subset.refl _),
let ⟨_, ⟨hx₁, y, rfl⟩⟩ := inhabited_of_mem_sets di.nhds_inf_neq_bot this in
subset_ne_empty hs $ ne_empty_of_mem hx₁

variables [topological_space γ]
/-- If `i : α → β` is a dense inducing, then any function `α → γ` "extends" to a function `β → γ`. -/
def extend (di : dense_inducing i) (f : α → γ) (b : β) : γ :=
@lim _ _ ⟨f (dense_range.inhabited di.dense b).default⟩ (map f (comap i (nhds b)))

lemma extend_eq [t2_space γ] {b : β} {c : γ} {f : α → γ} (hf : map f (comap i (nhds b)) ≤ nhds c) :
  di.extend f b = c :=
@lim_eq _ _ (id _) _ _ _ (by simp; exact comap_nhds_neq_bot di) hf

lemma extend_e_eq [t2_space γ] {f : α → γ} (a : α) (hf : continuous_at f a) :
  di.extend f (i a) = f a :=
extend_eq _ $ di.nhds_eq_comap a ▸ hf

lemma extend_eq_of_cont [t2_space γ] {f : α → γ} (hf : continuous f) (a : α) :
  di.extend f (i a) = f a :=
di.extend_e_eq a (continuous_iff_continuous_at.1 hf a)

lemma tendsto_extend [regular_space γ] {b : β} {f : α → γ} (di : dense_inducing i)
  (hf : {b | ∃c, tendsto f (comap i $ nhds b) (nhds c)} ∈ nhds b) :
  tendsto (di.extend f) (nhds b) (nhds (di.extend f b)) :=
let φ := {b | tendsto f (comap i $ nhds b) (nhds $ di.extend f b)} in
have hφ : φ ∈ nhds b,
  from (nhds b).sets_of_superset hf $ assume b ⟨c, hc⟩,
    show tendsto f (comap i (nhds b)) (nhds (di.extend f b)), from (di.extend_eq hc).symm ▸ hc,
assume s hs,
let ⟨s'', hs''₁, hs''₂, hs''₃⟩ := nhds_is_closed hs in
let ⟨s', hs'₁, (hs'₂ : i ⁻¹' s' ⊆ f ⁻¹' s'')⟩ := mem_of_nhds hφ hs''₁ in
let ⟨t, (ht₁ : t ⊆ φ ∩ s'), ht₂, ht₃⟩ := mem_nhds_sets_iff.mp $ inter_mem_sets hφ hs'₁ in
have h₁ : closure (f '' (i ⁻¹' s')) ⊆ s'',
  by rw [closure_subset_iff_subset_of_is_closed hs''₃, image_subset_iff]; exact hs'₂,
have h₂ : t ⊆ di.extend f ⁻¹' closure (f '' (i ⁻¹' t)), from
  assume b' hb',
  have nhds b' ≤ principal t, by simp; exact mem_nhds_sets ht₂ hb',
  have map f (comap i (nhds b')) ≤ nhds (di.extend f b') ⊓ principal (f '' (i ⁻¹' t)),
    from calc _ ≤ map f (comap i (nhds b' ⊓ principal t)) : map_mono $ comap_mono $ le_inf (le_refl _) this
      ... ≤ map f (comap i (nhds b')) ⊓ map f (comap i (principal t)) :
        le_inf (map_mono $ comap_mono $ inf_le_left) (map_mono $ comap_mono $ inf_le_right)
      ... ≤ map f (comap i (nhds b')) ⊓ principal (f '' (i ⁻¹' t)) : by simp [le_refl]
      ... ≤ _ : inf_le_inf ((ht₁ hb').left) (le_refl _),
  show di.extend f b' ∈ closure (f '' (i ⁻¹' t)),
  begin
    rw [closure_eq_nhds],
    apply neq_bot_of_le_neq_bot _ this,
    simp,
    exact di.comap_nhds_neq_bot
  end,
(nhds b).sets_of_superset
  (show t ∈ nhds b, from mem_nhds_sets ht₂ ht₃)
  (calc t ⊆ di.extend f ⁻¹' closure (f '' (i ⁻¹' t)) : h₂
    ... ⊆ di.extend f ⁻¹' closure (f '' (i ⁻¹' s')) :
      preimage_mono $ closure_mono $ image_subset f $ preimage_mono $ subset.trans ht₁ $ inter_subset_right _ _
    ... ⊆ di.extend f ⁻¹' s'' : preimage_mono h₁
    ... ⊆ di.extend f ⁻¹' s : preimage_mono hs''₂)

lemma continuous_extend [regular_space γ] {f : α → γ} (di : dense_inducing i)
  (hf : ∀b, ∃c, tendsto f (comap i (nhds b)) (nhds c)) : continuous (di.extend f) :=
continuous_iff_continuous_at.mpr $ assume b, di.tendsto_extend $ univ_mem_sets' hf

lemma mk'
  [topological_space α] [topological_space β] (i : α → β)
  (c     : continuous i)
  (dense : ∀x, x ∈ closure (range i))
  (H     : ∀ (a:α) s ∈ nhds a,
    ∃t ∈ nhds (i a), ∀ b, i b ∈ t → b ∈ s) :
  dense_inducing i :=
{ induced := (induced_iff_nhds_eq i).2 $
    λ a, le_antisymm (tendsto_iff_comap.1 $ c.tendsto _) (by simpa [le_def] using H a),
  dense := dense }
end dense_inducing

structure dense_embedding [topological_space α] [topological_space β] (e : α → β)
  extends dense_inducing e : Prop :=
(inj : function.injective e)

theorem dense_embedding.mk'
  [topological_space α] [topological_space β] (e : α → β)
  (c     : continuous e)
  (dense : ∀x, x ∈ closure (range e))
  (inj   : function.injective e)
  (H     : ∀ (a:α) s ∈ nhds a,
    ∃t ∈ nhds (e a), ∀ b, e b ∈ t → b ∈ s) :
  dense_embedding e :=
{ inj := inj,
  ..dense_inducing.mk' e c dense H}

namespace dense_embedding
variables [topological_space α] [topological_space β]
variables {e : α → β} (de : dense_embedding e)

lemma inj_iff {x y} : e x = e y ↔ x = y := de.inj.eq_iff

lemma to_embedding : embedding e :=
{ induced := de.induced,
  inj := de.inj }
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
    (by rw [hgf.right, ← continuous_iff_coinduced_le];
        apply continuous_coinduced_rng.comp hf)
    (by rwa ← continuous_iff_coinduced_le)⟩

protected lemma continuous_iff {f : α → β} {g : β → γ} (hf : quotient_map f) :
  continuous g ↔ continuous (g ∘ f) :=
by rw [continuous_iff_coinduced_le, continuous_iff_coinduced_le, hf.right, coinduced_compose]

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

section closed_embedding
variables [topological_space α] [topological_space β] [topological_space γ]

/-- A closed embedding is an embedding with closed image. -/
def closed_embedding (f : α → β) : Prop := embedding f ∧ is_closed (range f)

lemma closed_embedding.closed_iff_image_closed {f : α → β} (hf : closed_embedding f)
  {s : set α} : is_closed s ↔ is_closed (f '' s) :=
⟨embedding_is_closed hf.1 hf.2,
 λ h, begin
   convert ←continuous_iff_is_closed.mp hf.1.continuous _ h,
   apply preimage_image_eq _ hf.1.inj
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
  refine ⟨⟨⟨_⟩, h₂⟩, by convert h₃ univ is_closed_univ; simp⟩,
  apply le_antisymm (continuous_iff_le_induced.mp h₁) _,
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

lemma closed_embedding.comp {f : α → β} {g : β → γ}
  (hg : closed_embedding g) (hf : closed_embedding f) : closed_embedding (g ∘ f) :=
⟨hg.1.comp hf.1, show is_closed (range (g ∘ f)),
 by rw [range_comp, ←hg.closed_iff_image_closed]; exact hf.2⟩

end closed_embedding
