/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara
-/
import combinatorics.simple_graph.connectivity
import data.nat.lattice

/-!
# Graph metric

This module defines the `simple_graph.dist` function, which takes
pairs of vertices to the length of the shortest walk between them.

## Main definitions

- `simple_graph.dist` is the graph metric.

## Tags

graph metric

-/

namespace simple_graph
variables {V : Type*} (G : simple_graph V)

/-! ## Metric -/

/-- The distance between two vertices is the length of the shortest walk between them.
If no such walk exists, this uses the junk value of `0`. -/
noncomputable
def dist (u v : V) : ℕ := Inf (set.range (walk.length : G.walk u v → ℕ))

variables {G}

lemma reachable.range_length_walk_nonempty {u v : V} (hr : G.reachable u v) :
  (set.range (walk.length : G.walk u v → ℕ)).nonempty :=
set.range_nonempty_iff_nonempty.mpr hr

lemma reachable.exists_walk_of_dist {u v : V} (hr : G.reachable u v) :
  ∃ (p : G.walk u v), p.length = G.dist u v :=
nat.Inf_mem hr.range_length_walk_nonempty

lemma connected.range_length_walk_nonempty (hconn : G.connected) (u v : V) :
  (set.range (walk.length : G.walk u v → ℕ)).nonempty :=
(hconn.preconnected u v).range_length_walk_nonempty

lemma connected.exists_walk_of_dist (hconn : G.connected) (u v : V) :
  ∃ (p : G.walk u v), p.length = G.dist u v :=
(hconn.preconnected u v).exists_walk_of_dist

lemma dist_le {u v : V} (p : G.walk u v) : G.dist u v ≤ p.length :=
by { apply nat.Inf_le, use p }

@[simp] lemma dist_self {v : V} : dist G v v = 0 :=
le_antisymm (dist_le (walk.nil : walk G v v)) (zero_le _)

@[simp]
lemma dist_eq_zero_iff_eq_or_not_reachable {u v : V} : G.dist u v = 0 ↔ u = v ∨ ¬ G.reachable u v :=
by simp [dist, nat.Inf_eq_zero, reachable]

lemma reachable.dist_eq_zero_iff {u v : V} (hr : G.reachable u v) :
  G.dist u v = 0 ↔ u = v := by simp [hr]

lemma connected.dist_eq_zero_iff (hconn : G.connected) {u v : V} :
  G.dist u v = 0 ↔ u = v := by simp [hconn.preconnected u v]

lemma dist_eq_zero_of_not_reachable {u v : V} (h : ¬ G.reachable u v) : G.dist u v = 0 :=
by simp [h]

lemma nonempty_of_pos_dist {u v : V} (h : 0 < G.dist u v) :
  (set.univ : set (G.walk u v)).nonempty :=
by simpa [set.range_nonempty_iff_nonempty, set.nonempty_iff_univ_nonempty]
     using nat.nonempty_of_pos_Inf h

lemma connected.dist_triangle (hconn : G.connected) {u v w : V} :
  G.dist u w ≤ dist G u v + dist G v w :=
begin
  obtain ⟨p, hp⟩ := hconn.exists_walk_of_dist u v,
  obtain ⟨q, hq⟩ := hconn.exists_walk_of_dist v w,
  rw [← hp, ← hq, ← walk.length_append],
  exact dist_le _,
end

lemma dist_comm' {u v : V} (h : G.reachable u v) : G.dist u v ≤ G.dist v u :=
begin
  obtain ⟨p, hp⟩ := h.symm.exists_walk_of_dist,
  rw [← hp, ← walk.length_reverse],
  apply dist_le,
end

lemma dist_comm {u v : V} : G.dist u v = G.dist v u :=
begin
  by_cases h : G.reachable u v,
  { apply le_antisymm (dist_comm' h) (dist_comm' h.symm), },
  { have h' : ¬ G.reachable v u := λ h', absurd h'.symm h,
    simp [h, h', dist_eq_zero_of_not_reachable], },
end

end simple_graph
