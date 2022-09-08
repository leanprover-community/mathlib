/-
Copyright (c) 2022 George Peter Banyard, Yaël Dillies, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Peter Banyard, Yaël Dillies, Kyle Miller
-/
import combinatorics.simple_graph.connectivity

/-!
# Graph products

This file defines the box product of graphs and other product constructions. The box product of `G`
and `H` is the graph on the product of the vertices such that `x` and `y` are related iff they agree
on one component and the other one is related via either `G` or `H`. For example, the box product of
two edges is a square.

## Main declarations

* `simple_graph.box_prod`: The box product.

## Notation

* `G □ H`: The box product of `G` and `H`.

## TODO

Define all other graph products!
-/

variables {α β γ : Type*}

namespace simple_graph
variables {G : simple_graph α} {H : simple_graph β} {I : simple_graph γ} {a a₁ a₂ : α} {b b₁ b₂ : β}
  {x y : α × β}

/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
def box_prod (G : simple_graph α) (H : simple_graph β) : simple_graph (α × β) :=
{ adj := λ x y, G.adj x.1 y.1 ∧ x.2 = y.2 ∨ H.adj x.2 y.2 ∧ x.1 = y.1,
  symm := λ x y, by simp [and_comm, or_comm, eq_comm, adj_comm],
  loopless := λ x, by simp }

infix ` □ `:70 := box_prod

@[simp] lemma box_prod_adj :
  (G □ H).adj x y ↔ G.adj x.1 y.1 ∧ x.2 = y.2 ∨ H.adj x.2 y.2 ∧ x.1 = y.1 := iff.rfl

@[simp] lemma box_prod_adj_left : (G □ H).adj (a₁, b) (a₂, b) ↔ G.adj a₁ a₂ :=
by rw [box_prod_adj, and_iff_left rfl, or_iff_left (λ h : H.adj b b ∧ _, h.1.ne rfl)]

@[simp] lemma box_prod_adj_right : (G □ H).adj (a, b₁) (a, b₂) ↔ H.adj b₁ b₂ :=
by rw [box_prod_adj, and_iff_left rfl, or_iff_right (λ h : G.adj a a ∧ _, h.1.ne rfl)]

lemma box_prod_neighbor_set (a : α) (b : β) :
  (G □ H).neighbor_set ⟨a,b⟩ = ((λ x, (⟨x,b⟩ : α × β)) '' (G.neighbor_set a)) ∪
                               ((λ y, (⟨a,y⟩ : α × β)) '' (H.neighbor_set b)) :=
begin
  ext ⟨x,y⟩,
  simp only [mem_neighbor_set, box_prod_adj, set.mem_union_eq, set.mem_image, prod.mk.inj_iff,
             exists_eq_right_right],
  simp_rw [and_comm _ (b = y), exists_eq_right_right],
  finish,
end

variables (G H I)

/-- The box product is commutative up to isomorphism. `equiv.prod_comm` as a graph isomorphism. -/
@[simps] def box_prod_comm : G □ H ≃g H □ G := ⟨equiv.prod_comm _ _, λ x y, or_comm _ _⟩

/-- The box product is associative up to isomorphism. `equiv.prod_assoc` as a graph isomorphism. -/
@[simps] def box_prod_assoc : (G □ H) □ I ≃g G □ (H □ I) :=
⟨equiv.prod_assoc _ _ _, λ x y, by simp only [box_prod_adj, equiv.prod_assoc_apply,
  or_and_distrib_right, or_assoc, prod.ext_iff, and_assoc, @and.comm (x.1.1 = _)]⟩

/-- The embedding of `G` into `G □ H` given by `b`. -/
@[simps] def box_prod_left (b : β) : G ↪g G □ H :=
{ to_fun := λ a, (a , b),
  inj' := λ a₁ a₂, congr_arg prod.fst,
  map_rel_iff' := λ a₁ a₂, box_prod_adj_left }

/-- The embedding of `H` into `G □ H` given by `a`. -/
@[simps] def box_prod_right (a : α) : H ↪g G □ H :=
{ to_fun := prod.mk a,
  inj' := λ b₁ b₂, congr_arg prod.snd,
  map_rel_iff' := λ b₁ b₂, box_prod_adj_right }

namespace walk
variables {G}

/-- Turn a walk on `G` into a walk on `G □ H`. -/
protected def box_prod_left (b : β) : G.walk a₁ a₂ → (G □ H).walk (a₁, b) (a₂, b) :=
walk.map (G.box_prod_left H b).to_hom

variables (G) {H}

/-- Turn a walk on `H` into a walk on `G □ H`. -/
protected def box_prod_right (a : α) : H.walk b₁ b₂ → (G □ H).walk (a, b₁) (a, b₂) :=
walk.map (G.box_prod_right H a).to_hom

variables {G}

/-- Project a walk on `G □ H` to a walk on `G` by discarding the moves in the direction of `H`. -/
def of_box_prod_left [decidable_eq β] [decidable_rel G.adj] :
  Π {x y : α × β}, (G □ H).walk x y → G.walk x.1 y.1
| _ _ nil := nil
| x z (cons h w) := or.by_cases h (λ hG, w.of_box_prod_left.cons hG.1)
    (λ hH, show G.walk x.1 z.1, by rw hH.2; exact w.of_box_prod_left)

/-- Project a walk on `G □ H` to a walk on `H` by discarding the moves in the direction of `G`. -/
def of_box_prod_right [decidable_eq α] [decidable_rel H.adj] :
  Π {x y : α × β}, (G □ H).walk x y → H.walk x.2 y.2
| _ _ nil := nil
| x z (cons h w) := (or.symm h).by_cases (λ hH, w.of_box_prod_right.cons hH.1)
  (λ hG, show H.walk x.2 z.2, by rw hG.2; exact w.of_box_prod_right)

@[simp] lemma of_box_prod_left_box_prod_left [decidable_eq β] [decidable_rel G.adj] :
  ∀ {a₁ a₂ : α} (w : G.walk a₁ a₂), (w.box_prod_left H b).of_box_prod_left = w
| _ _ nil := rfl
| _ _ (cons' x y z h w) := begin
  rw [walk.box_prod_left, map_cons, of_box_prod_left, or.by_cases, dif_pos, ←walk.box_prod_left,
    of_box_prod_left_box_prod_left],
  exacts [rfl, ⟨h, rfl⟩],
end

@[simp] lemma of_box_prod_left_box_prod_right [decidable_eq α] [decidable_rel G.adj] :
  ∀ {b₁ b₂ : α} (w : G.walk b₁ b₂), (w.box_prod_right G a).of_box_prod_right = w
| _ _ nil := rfl
| _ _ (cons' x y z h w) := begin
  rw [walk.box_prod_right, map_cons, of_box_prod_right, or.by_cases, dif_pos, ←walk.box_prod_right,
    of_box_prod_left_box_prod_right],
  exacts [rfl, ⟨h, rfl⟩],
end

end walk

variables {G H}

protected lemma preconnected.box_prod (hG : G.preconnected) (hH : H.preconnected) :
  (G □ H).preconnected :=
begin
  rintro x y,
  obtain ⟨w₁⟩ := hG x.1 y.1,
  obtain ⟨w₂⟩ := hH x.2 y.2,
  rw [←@prod.mk.eta _ _ x, ←@prod.mk.eta _ _ y],
  exact ⟨(w₁.box_prod_left _ _).append (w₂.box_prod_right _ _)⟩,
end

protected lemma preconnected.of_box_prod_left [nonempty β] (h : (G □ H).preconnected) :
  G.preconnected :=
begin
  classical,
  rintro a₁ a₂,
  obtain ⟨w⟩ := h (a₁, classical.arbitrary _) (a₂, classical.arbitrary _),
  exact ⟨w.of_box_prod_left⟩,
end

protected lemma preconnected.of_box_prod_right [nonempty α] (h : (G □ H).preconnected) :
  H.preconnected :=
begin
  classical,
  rintro b₁ b₂,
  obtain ⟨w⟩ := h (classical.arbitrary _, b₁) (classical.arbitrary _, b₂),
  exact ⟨w.of_box_prod_right⟩,
end

protected lemma connected.box_prod (hG : G.connected) (hH : H.connected) : (G □ H).connected :=
by { haveI := hG.nonempty, haveI := hH.nonempty, exact ⟨hG.preconnected.box_prod hH.preconnected⟩ }

protected lemma connected.of_box_prod_left (h : (G □ H).connected) : G.connected :=
by { haveI := (nonempty_prod.1 h.nonempty).1, haveI := (nonempty_prod.1 h.nonempty).2,
  exact ⟨h.preconnected.of_box_prod_left⟩ }

protected lemma connected.of_box_prod_right (h : (G □ H).connected) : H.connected :=
by { haveI := (nonempty_prod.1 h.nonempty).1, haveI := (nonempty_prod.1 h.nonempty).2,
  exact ⟨h.preconnected.of_box_prod_right⟩ }

@[simp] lemma box_prod_connected : (G □ H).connected ↔ G.connected ∧ H.connected :=
⟨λ h, ⟨h.of_box_prod_left, h.of_box_prod_right⟩, λ h, h.1.box_prod h.2⟩

instance [decidable_eq α] [decidable_eq β] [locally_finite G] [locally_finite H] :
  locally_finite (G □ H) :=
begin
  rintro ⟨_,_⟩,
  rw box_prod_neighbor_set,
  apply_instance,
end

lemma box_prod_degree [decidable_eq α] [decidable_eq β]
  [locally_finite G] [locally_finite H] (a : α) (b : β) :
  (G □ H).degree ⟨a,b⟩ = G.degree a + H.degree b :=
begin
  dsimp only [degree,neighbor_finset],
  simp_rw [box_prod_neighbor_set a b,set.to_finset_union],
  rw finset.card_disjoint_union,
  have l : ((λ (x : α), (x, b)) '' G.neighbor_set a).to_finset.card
         = (G.neighbor_set a).to_finset.card, by
  { simp only [set.to_finset_card, fintype.card_of_finset,
               finset.card_image_of_injective _ (prod.mk.inj_right b)],},
  have r : ((λ (x' : β), (a, x')) '' H.neighbor_set b).to_finset.card
         = (H.neighbor_set b).to_finset.card, by
  { simp only [set.to_finset_card, fintype.card_of_finset,
               finset.card_image_of_injective _ (prod.mk.inj_left a)],},
  rw [l, r],
  { rintro ⟨x,x'⟩ q,
    simp only [finset.inf_eq_inter, finset.mem_inter, set.mem_to_finset, set.mem_image,
               mem_neighbor_set,prod.mk.inj_iff,exists_eq_right_right] at q,
    obtain ⟨⟨_,_,rfl,rfl⟩,⟨a,_,_,_⟩⟩ := q,
    exact (a.ne (rfl)).elim, },
end

end simple_graph

