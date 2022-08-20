import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import category_theory.functor.basic
import .mathlib

open function finset set classical simple_graph.walk relation

local attribute [instance] prop_decidable

universes u v w

noncomputable theory

namespace simple_graph


variables  {V : Type u} (G : simple_graph V)
            [Gpc : preconnected G] (K : finset V)


def compl (S : set V) : subgraph G := (⊤ : subgraph G).delete_verts S

lemma outside_to_compl {S : set V} {v : V} (h : v ∉ S) : v ∈ (G.compl S).verts := by simp [compl, h]

-- `def` rather than `instance` because of typeclass problems
def vertex_coe {K L : set V} {G : simple_graph V} (h : K ⊆ L) : (G.compl L).verts → (G.compl K).verts :=
  λ ⟨v, ⟨htop, hnL⟩⟩, ⟨v, ⟨htop, λ hK, hnL (h hK)⟩⟩

def compl_coe {K L : set V} {G : simple_graph V} (h : K ⊆ L) : (set ↥((G.compl K).verts)) → (set ↥((G.compl L).verts)) := λ S v, S (vertex_coe h v)

lemma compl_coe_mem_iff_vert_coe {K L : set V} (h : K ⊆ L) {v : (G.compl L).verts} {S : set (G.compl K).verts}: v ∈ compl_coe h S ↔ (vertex_coe h v) ∈ S := by refl


def conn_comp_outside : Type u :=
  (G.compl K).coe.connected_component

/- The vertices in the compl of `K` that lie in the component `C` -/
@[reducible, simp] def conn_comp_outside.verts {G : simple_graph V} {K : finset V} (C : conn_comp_outside G K) :=
  {v : (G.compl K).verts | connected_component_mk _ v = C}

def inf_conn_comp_outside :=
 {C : G.conn_comp_outside K // infinite C.verts}

def fin_conn_comp_outside :=
  {C : G.conn_comp_outside K // finite C.verts}


namespace conn_comp_outside

@[reducible, simp] def component_of (v : (G.compl K).verts) : conn_comp_outside G K := connected_component_mk _ v

def component_of_set (S : set (G.compl K).verts) (hnonempty : nonempty S) : conn_comp_outside G K :=
begin
  rcases nonempty.some hnonempty with ⟨v, hvS⟩,
  exact component_of G K v, -- technically this is illegal since the function is not well-defined
end

-- Will it be better to make this a function of `S : (G.compl K).verts`?
def component_of_set' (S : set V) (hdisjoint : disjoint S K) (hconn : subgraph.connected (subgraph.induce (G.compl K) S)) : conn_comp_outside G K :=
begin
  rcases hconn,
  rcases nonempty.some hconn_nonempty with ⟨v, hvS : v ∈ S⟩,
  let ν : (G.compl K).verts := ⟨v, _⟩,
  exact component_of G K ν,
  show v ∈ (G.compl K).verts, from by {
    apply outside_to_compl, intro h,
    dsimp [disjoint] at hdisjoint,
    apply hdisjoint,
    split, assumption, assumption,},
end
-- Strategy: pick a random point in `S` and form the connected component containing it. The choice does not matter since `S` is connected

lemma reachable_coe {K L : finset V} (h : K ⊆ L)
{v a: ↥((G.compl ↑L).verts)} (hreach: (G.compl ↑L).coe.reachable a v) : (G.compl ↑K).coe.reachable (vertex_coe h a) (vertex_coe h v) := sorry


section finite_components

  /- The boundary of a set, consisting of all adjacent vertices not in the set -/
  def bdry (S : set V) := {v : (G.compl S).verts | ∃ x ∈ S, G.adj v x}

  /- This is the portion of the connected component that is a part of the boundary -/
  def border {G : simple_graph V} {K : finset V} (C : conn_comp_outside G K) : set (compl G K).verts := C.verts ∩ (bdry G K)

  lemma components_cover : set.Union (λ C : conn_comp_outside G K, C.verts) = ⊤ :=
  begin
    ext, simp [verts], use component_of G K x,
  end

  lemma components_nonempty : ∀ (C : conn_comp_outside G K), nonempty (C.verts) :=
  begin
    apply connected_component.ind,
    rintro v, apply nonempty.intro,
    use v, dsimp [verts], refl,
  end

  -- TODO: Show that the boundary is precisely the union of all the borders.
  lemma bdry_eq_border_union : (bdry G K) = set.Union (λ C : conn_comp_outside G K, C.border) :=
    calc bdry G K = ⊤ ∩ (bdry G K) : by simp
    ... = (set.Union (λ C : conn_comp_outside G K, C.verts)) ∩ (bdry G K) : by rw [components_cover]
    ... = set.Union (λ C : conn_comp_outside G K, C.verts ∩ (bdry G K)) : (bdry G K).Union_inter (λ (i : conn_comp_outside G K), i.verts)
    ... = set.Union (λ C : conn_comp_outside G K, C.border) : by refl

  -- for mathlib:
  lemma symm_iff {X : Type u} (P : X → X → Prop) : (∀ {a b}, P a b → P b a) → (∀ {a b}, P a b ↔ P b a) := by tidy

  lemma bdry.iff : bdry G K = set.Union (λ k : K, {v : (G.compl K).verts | v.val ∈ G.neighbor_set k}) :=
  begin
    ext, unfold bdry, simp,
    conv in (G.adj ↑_ _)
      {rw [symm_iff G.adj (λ _ _, G.adj_symm)],},
  end

  lemma bdry.iso : ↥(bdry G K) ≃ Σ C : conn_comp_outside G K, ↥(border C) := {
    to_fun := λ ⟨v, h⟩, ⟨component_of G K v, v, rfl, h⟩,
    inv_fun := λ ⟨C, v, h⟩, ⟨v, h.2⟩,
    left_inv := by {simp [left_inverse],},
    right_inv := by {simp [function.right_inverse, left_inverse],
      dsimp [conn_comp_outside, border],
      intro a, rintro ⟨b, _, _⟩,
      tidy, -- yay!
    } }

  lemma bdry_finite [Glocfin : locally_finite G] : (bdry G K).finite :=
  begin
    rw [bdry.iff], refine finite_Union _, rintro k,
    apply set.finite.preimage,
    { apply injective.inj_on, tidy, },
    { exact (neighbor_set G k).to_finite, }
  end

  -- for mathlib
  lemma fintype.iso {A B : Type u} (hA : fintype A) (hiso : A ≃ B) : fintype B :=
  begin
    fsplit,
    { refine finset.map ⟨hiso.to_fun, _⟩ hA.elems,
      unfold injective, intros _ _ h,
      have := congr_arg hiso.inv_fun h,
      simp at this, assumption,
    },
    intro b,
    let a := hiso.inv_fun b,
    have : hiso.to_fun a = b := by {show hiso.to_fun (hiso.inv_fun b) = id b, simp,},
    rw ← this,
    refine mem_map.mpr _,
    use a, split,
    apply hA.complete,
    refl,
  end

  instance border_sum_fin [locally_finite G] : fintype (Σ C : conn_comp_outside G K, ↥(border C)) :=
  begin
    apply fintype.iso, rotate,
    exact (bdry.iso G K),
    refine finite.fintype _,
    apply bdry_finite,
  end

  lemma border_finite [locally_finite G] (C : conn_comp_outside G K) :  (border C).finite :=
  begin
    refine finite.inter_of_right _ C.verts, apply bdry_finite,
  end


  #check @walk.rec

  -- for mathlib
  lemma reachable_of_adj {u v : V} : G.adj u v → G.reachable u v := sorry

  lemma good_path {V : Type u} {G : simple_graph V} :
  ∀ (u v : V) (p : G.walk u v) (S : set V) (uS : u ∈ S) (vS : v ∉ S),
    ∃ (x y : V) (w : G.walk u x), G.adj x y ∧  (w.support.to_finset : set V) ⊆ S ∧ y ∉ S
  | _ _ nil p up vnp := (vnp up).elim
  | _ _ (cons' u x v a q) p up vnp := by {
    by_cases h : p x,
    { obtain ⟨xx,yy,ww,aa,dd,mm⟩ := good_path x v q p h vnp,
      use [xx,yy,cons a ww,aa],split,rotate, exact mm,
      simp, rw set.insert_subset,exact ⟨up,dd⟩,
    },
    { use [u,x,nil,a],simp,exact ⟨up,h⟩, }
  }

  lemma walk.compl {G : simple_graph V} (S : set V)
    (x y : V)  (hx : x ∉ S) (hy : y ∉ S)
    (w : G.walk x y) (hw : disjoint (w.support.to_finset : set V) S) :
    (G.compl S).coe.reachable ⟨x, outside_to_compl G hx⟩ ⟨y, outside_to_compl G hy⟩ := sorry

  lemma walk.to_boundary {G : simple_graph V} (S : set V) (src : (G.compl S).verts) (tgt : S) (w : G.walk ↑src tgt) :
    ∃ b ∈ bdry G S, (G.compl S).coe.reachable src b :=
  begin
    dsimp [simple_graph.compl],
    obtain ⟨s,hs⟩ := src, simp [compl] at hs,
    obtain ⟨t,ht⟩ := tgt,
    obtain ⟨a,b,w,adj,sub,mem⟩ := good_path s t w (Sᶜ) (hs : s ∈ Sᶜ) (by {simp, exact ht} : t ∉ Sᶜ),
    have : a ∉ S, by {sorry},
    simp,
    use [a,this],
    unfold bdry,simp,
    split,
    { use [b], simp at mem, exact ⟨mem,adj⟩, },
    { unfold simple_graph.reachable,
      fapply walk.compl S s a hs this w,
      rw subset_compl_iff_disjoint_right at sub,
      exact sub,}
  end

  lemma border_nonempty (Gpc : preconnected G) (Knempty : K.nonempty) : ∀ (C : conn_comp_outside G K), nonempty (border C) :=
  begin
    apply connected_component.ind,
    intro v, rcases Knempty with ⟨k, kK⟩,
    let w := (Gpc ↑v k).some,
    rcases (walk.to_boundary ↑K v ⟨k, kK⟩ w) with ⟨b, hbdry, hreach⟩,
    apply nonempty.intro,
    use b, unfold border, simp,
    exact ⟨reachable.symm hreach, hbdry⟩,
  end

  def to_border (Gpc : preconnected G) (Knempty : K.nonempty) : Π (C : conn_comp_outside G K), ↥(border C) := λ C, nonempty.some $ @border_nonempty _ G K Gpc Knempty C

  -- for mathlib
  lemma sigma.fintype_of_nonempty_fintype {α : Type u} (β : Π (a : α), Type v) (fin_sigma : fintype Σ a : α, β a) (hnonempty : Π a : α, nonempty (β a)) : fintype α :=
  begin
    refine fintype_of_not_infinite _,
    intro hinf,
    refine infinite.false (_ : infinite Σ a : α, β a),

    let φ : α → Σ a : α, β a := λ a, ⟨a, nonempty.some (hnonempty a)⟩,
    refine @infinite.of_injective _ _ hinf φ _,

    rintros _ _ hφ,
    cases hφ, simp [φ] at hφ,
  end

  lemma finite_components [Glf : locally_finite G] (Gpc : preconnected G) :
    fintype (conn_comp_outside G K) :=
  begin
    by_cases Knempty : K.nonempty,
    {
      have border_map_fin : fintype (Σ C : conn_comp_outside G K, ↥(border C)) := by {apply_instance}, -- needed for some reason
      refine sigma.fintype_of_nonempty_fintype _ _ _, rotate,
      apply border_map_fin,
      apply border_nonempty,
      assumption, assumption,
    },
    { rw [finset.not_nonempty_iff_eq_empty] at Knempty,
      subst Knempty,
      -- refine ⟨{_}, _⟩,
      by_cases nonempty V, {
        refine ⟨{_}, _⟩,
        have v := nonempty.some h,

        exact component_of G ∅ ⟨v, outside_to_compl G (by simp)⟩,

        apply connected_component.ind,
        intro v', dsimp [compl, component_of],
        simp, sorry -- all pairs of vertices are reachable in `G`
      },
      {
        refine ⟨{_}, _⟩,
        sorry, sorry,
      }
    }
  end

  lemma nonempty_components (Vinf : (univ : set V).infinite) : nonempty (conn_comp_outside G K) :=
  begin
    suffices inh : nonempty (G.compl K).verts, from nonempty.intro (component_of G K (nonempty.some inh)),
    suffices inf : ((univ : set V) \ ↑K).infinite, from by { rcases set.nonempty_def.mp (set.infinite.nonempty inf) with ⟨v, h⟩, exact nonempty.intro ⟨v, h⟩,},
    apply set.infinite.diff,
    exact Vinf, exact K.finite_to_set,
  end

end finite_components

lemma conn_comp_outside_back_unique {K L : finset V} (h : K ⊆ L) :
∀ C : conn_comp_outside G L,
  ∃! D : conn_comp_outside G K,
    C.verts ⊆ (compl_coe h D.verts) :=
begin
  apply connected_component.ind,
  intro v,
  refine exists_unique_of_exists_of_unique _ _,
  use component_of G K (vertex_coe h v),
  intro a,
  simp,
  intro hreach,
  rw [compl_coe_mem_iff_vert_coe],
  show (G.compl K).coe.reachable _ _,
  apply reachable_coe, assumption,

  dsimp [conn_comp_outside],
  -- apply connected_component.ind₂, -- why doesn't this work?
  rw [simple_graph.connected_component.forall], intro v₁,
  rw [simple_graph.connected_component.forall], intro v₂,
  simp,
  intro hreachvv₁, intro hreachvv₂,
  apply simple_graph.reachable.trans _ _,
  exact (vertex_coe h v),
  { apply simple_graph.reachable.symm,
    apply hreachvv₁,
    apply simple_graph.reachable.refl,},
  { apply hreachvv₂,
    apply simple_graph.reachable.refl, }
end

-- this is the `bwd_map`
def conn_comp_outside_back {K L : finset V} (h : K ⊆ L) : Π (C : conn_comp_outside G L), conn_comp_outside G K := by {
  intro C,
  refine quot.lift_on C _ _,
  exact λ v, component_of G K (vertex_coe h v),

  intros v w hreach,
  rw [connected_component.eq],
  apply reachable_coe,
  exact hreach,
}

/-
  classical.some (exists_of_exists_unique (conn_comp_outside_back_unique G h C))
-/

def conn_comp_outside_back.iff {K L : finset V} (h : K ⊆ L) (C : conn_comp_outside G L) (D : conn_comp_outside G K):
  conn_comp_outside_back G h C = D ↔ C.verts ⊆ (compl_coe h D.verts) :=
begin
  sorry, /-split,
  { rintro equ, induction equ, exact (exists_of_exists_unique (conn_comp_outside_back_unique G h C)).some_spec},
  { exact unique_of_exists_unique (conn_comp_outside_back_unique G h C) (exists_of_exists_unique (conn_comp_outside_back_unique G h C)).some_spec},-/
end

lemma conn_comp_outside_back.refl (K : finset V) (C : conn_comp_outside G K) :
  conn_comp_outside_back G (finset.subset.refl K) C = C :=
begin
  dsimp [conn_comp_outside_back],
  sorry,
end
/-
  unique_of_exists_unique
  (conn_comp_outside_back_unique G (finset.subset.refl K) C)
  (classical.some_spec (exists_of_exists_unique (conn_comp_outside_back_unique G (finset.subset.refl K) C)))
  (set.subset.refl C.verts)
-/

lemma conn_comp_outside_back.comm  {J K L : finset V} (k : J ⊆ K) (h : K ⊆ L) (C : conn_comp_outside G L) :
  conn_comp_outside_back G k (conn_comp_outside_back G h C) = conn_comp_outside_back G (k.trans h) C := sorry
/-
unique_of_exists_unique
  (conn_comp_outside_back_unique G (k.trans h) C)
  ((exists_of_exists_unique (conn_comp_outside_back_unique G h C)).some_spec.trans
     (exists_of_exists_unique (conn_comp_outside_back_unique G k (conn_comp_outside_back G h C))).some_spec)
  (classical.some_spec (exists_of_exists_unique (conn_comp_outside_back_unique G (k.trans h) C)))
-/

-- TODO: An infinite graph has at least one infinite connected component
lemma inf_graph_has_conn_comp [infinite V] : nonempty (conn_comp_outside G K) := sorry

-- TODO: A locally finite graph has finitely many infinite connected components
lemma inf_graph_fin_inf_conn_comp [locally_finite G] : finite (inf_conn_comp_outside G K) := sorry

-- def ends_system := category_theory.functor.mk (conn_comp_outside G) (conn_comp_outside_back G)

-- TODO: Mapping of connected sets under homomorphisms
-- TODO: Show that components are preserved under isomorphisms

-- Returns K ∪ (all finite connected components in the compl)
def conn_comp_outside.extend_fin [Glf : locally_finite G] (K : finset V) : finset V := sorry

-- TODO: Build all the associated lemmas. Mainly prove that the resulting set of connected components are precisely the infinite connected components of the original graph.

-- TODO: Prove lemmas about cofinite infinite components

end conn_comp_outside

end simple_graph
