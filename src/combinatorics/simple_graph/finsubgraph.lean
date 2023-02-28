/-
Copyright (c) 2022 Joanna Choules. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joanna Choules
-/
import topology.category.Top.limits
import combinatorics.simple_graph.subgraph

/-!
# Homomorphisms from finite subgraphs

This file defines the type of finite subgraphs of a `simple_graph` and proves a compactness result
for homomorphisms to a finite codomain.

## Main statements

* `simple_graph.exists_hom_of_all_finite_homs`: If every finite subgraph of a (possibly infinite)
  graph `G` has a homomorphism to some finite graph `F`, then there is also a homomorphism `G →g F`.

## Notations

`→fg` is a module-local variant on `→g` where the domain is a finite subgraph of some supergraph
`G`.

## Implementation notes

The proof here uses compactness as formulated in `nonempty_sections_of_fintype_inverse_system`. For
finite subgraphs `G'' ≤ G'`, the inverse system `finsubgraph_hom_functor` restricts homomorphisms
`G' →fg F` to domain `G''`.
-/

universes u v
variables {V : Type u} {W : Type v} {G : simple_graph V} {F : simple_graph W}

namespace simple_graph

/-- The subtype of `G.subgraph` comprising those subgraphs with finite vertex sets. -/
abbreviation finsubgraph (G : simple_graph V) := { G' : G.subgraph // G'.verts.finite }

/-- A graph homomorphism from a finite subgraph of G to F. -/
abbreviation finsubgraph_hom (G' : G.finsubgraph) (F : simple_graph W) := G'.val.coe →g F

local infix ` →fg ` : 50 := finsubgraph_hom

/-- The finite subgraph of G generated by a single vertex. -/
def singleton_finsubgraph (v : V) : G.finsubgraph := ⟨simple_graph.singleton_subgraph _ v, by simp⟩

/-- The finite subgraph of G generated by a single edge. -/
def finsubgraph_of_adj {u v : V} (e : G.adj u v) : G.finsubgraph :=
⟨simple_graph.subgraph_of_adj _ e, by simp⟩

/- Lemmas establishing the ordering between edge- and vertex-generated subgraphs. -/

lemma singleton_finsubgraph_le_adj_left {u v : V} {e : G.adj u v} :
  singleton_finsubgraph u ≤ finsubgraph_of_adj e :=
by simp [singleton_finsubgraph, finsubgraph_of_adj]

lemma singleton_finsubgraph_le_adj_right {u v : V} {e : G.adj u v} :
  singleton_finsubgraph v ≤ finsubgraph_of_adj e :=
by simp [singleton_finsubgraph, finsubgraph_of_adj]

/-- Given a homomorphism from a subgraph to `F`, construct its restriction to a sub-subgraph. -/
def finsubgraph_hom.restrict {G' G'' : G.finsubgraph} (h : G'' ≤ G') (f : G' →fg F) : G'' →fg F :=
begin
  refine ⟨λ ⟨v, hv⟩, f.to_fun ⟨v, h.1 hv⟩, _⟩,
  rintros ⟨u, hu⟩ ⟨v, hv⟩ huv,
  exact f.map_rel' (h.2 huv),
end

/-- The inverse system of finite homomorphisms. -/
def finsubgraph_hom_functor (G : simple_graph V) (F : simple_graph W) :
  (G.finsubgraph)ᵒᵖ ⥤ Type (max u v) :=
{ obj := λ G', G'.unop →fg F,
  map := λ G' G'' g f, f.restrict (category_theory.le_of_hom g.unop), }

/-- If every finite subgraph of a graph `G` has a homomorphism to a finite graph `F`, then there is
a homomorphism from the whole of `G` to `F`. -/
lemma nonempty_hom_of_forall_finite_subgraph_hom [finite W]
  (h : Π (G' : G.subgraph), G'.verts.finite → G'.coe →g F) : nonempty (G →g F) :=
begin
  /- Obtain a `fintype` instance for `W`. -/
  casesI nonempty_fintype W,
  /- Establish the required interface instances. -/
  haveI : is_directed G.finsubgraph (≤) :=
    ⟨λ i j : G.finsubgraph, ⟨⟨simple_graph.subgraph.union ↑i ↑j,
                              set.finite.union i.property j.property⟩,
                              by { simp_rw [← subtype.coe_le_coe, subtype.coe_mk],
                                   exact ⟨le_sup_left, le_sup_right⟩ }⟩⟩,
  haveI : ∀ (G' : (G.finsubgraph)ᵒᵖ), nonempty ((finsubgraph_hom_functor G F).obj G') :=
    λ G', ⟨h G'.unop G'.unop.property⟩,
  haveI : Π (G' : (G.finsubgraph)ᵒᵖ), fintype ((finsubgraph_hom_functor G F).obj G') :=
  begin
    intro G',
    haveI : fintype (↥(G'.unop.val.verts)) := G'.unop.property.fintype,
    haveI : fintype (↥(G'.unop.val.verts) → W) := begin
      classical,
      exact pi.fintype
    end,
    exact fintype.of_injective (λ f, f.to_fun) rel_hom.coe_fn_injective
  end,
  /- Use compactness to obtain a section. -/
  obtain ⟨u, hu⟩ := nonempty_sections_of_fintype_inverse_system (finsubgraph_hom_functor G F),
  refine ⟨⟨λ v, _, _⟩⟩,
  { /- Map each vertex using the homomorphism provided for its singleton subgraph. -/
    exact (u (opposite.op (singleton_finsubgraph v))).to_fun
      ⟨v, by {unfold singleton_finsubgraph, simp}⟩, },
  { /- Prove that the above mapping preserves adjacency. -/
    intros v v' e,
    /- The homomorphism for each edge's singleton subgraph agrees with those for its source and
    target vertices. -/
    have hv : opposite.op (finsubgraph_of_adj e) ⟶ opposite.op (singleton_finsubgraph v) :=
      quiver.hom.op (category_theory.hom_of_le singleton_finsubgraph_le_adj_left),
    have hv' : opposite.op (finsubgraph_of_adj e) ⟶ opposite.op (singleton_finsubgraph v') :=
      quiver.hom.op (category_theory.hom_of_le singleton_finsubgraph_le_adj_right),
    rw [← (hu hv), ← (hu hv')],
    apply simple_graph.hom.map_adj,
    /- `v` and `v'` are definitionally adjacent in `finsubgraph_of_adj e` -/
    simp [finsubgraph_of_adj], }
end

end simple_graph
