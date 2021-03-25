import tactic
import data.real.basic
import linear_algebra.affine_space.independent
import linear_algebra.std_basis
import linear_algebra.affine_space.finite_dimensional
import linear_algebra.affine_space.combination
import linear_algebra.finite_dimensional
import analysis.convex.topology
import combinatorics.simplicial_complex.dump
import combinatorics.simplicial_complex.extreme_point
import combinatorics.simplicial_complex.basic
-- import data.nat.parity

namespace affine

open_locale classical affine big_operators
open set
variables {m n : ℕ} {S : simplicial_complex m}
local notation `E` := fin m → ℝ

/--
The underlying space of a simplicial complex.
-/
def simplicial_complex.space (S : simplicial_complex m) : set E :=
⋃ X ∈ S.faces, convex_hull (X : set E)

/--
The boundary of a simplex as a subspace.
-/
def boundary (X : finset E) : set E :=
⋃ Y ⊂ X, convex_hull Y

lemma boundaries_agree_of_high_dimension {X : finset E} (hXcard : X.card = m + 1) :
  boundary X = frontier (convex_hull X) :=
begin
  ext x,
  split,
  {
    unfold boundary,
    simp_rw mem_Union,
    rintro ⟨Y, hYX, hx⟩,
    split,
    { exact subset_closure (convex_hull_mono hYX.1 hx) },
    {
      rintro h,
      sorry,
      --have :=  finset.convex_hull_eq,
    }
  },
  {
    rintro ⟨h, g⟩,
    sorry
  }
end

/--
The interior of a simplex as a subspace. Note this is *not* the same thing as the topological
interior of the underlying space.
-/
def combi_interior (X : finset E) : set E :=
convex_hull X \ boundary X

lemma boundary_subset_convex_hull {X : finset E} : boundary X ⊆ convex_hull X :=
bUnion_subset (λ Y hY, convex_hull_mono hY.1)

lemma convex_hull_eq_interior_union_boundary (X : finset E) :
  convex_hull ↑X = combi_interior X ∪ boundary X :=
(sdiff_union_of_subset boundary_subset_convex_hull).symm

lemma disjoint_interiors {S : simplicial_complex m} {X Y : finset E}
  (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (x : E) :
  x ∈ combi_interior X ∩ combi_interior Y → X = Y :=
begin
  rintro ⟨⟨hxX, hXbound⟩, ⟨hyY, hYbound⟩⟩,
  by_contra,
  have hXY : X ∩ Y ⊂ X,
  { use finset.inter_subset_left X Y,
    intro H,
    apply hYbound,
    apply set.mem_bUnion _ _,
    exact X,
    exact ⟨subset.trans H (finset.inter_subset_right X Y),
      (λ H2, h (finset.subset.antisymm (subset.trans H (finset.inter_subset_right X Y)) H2))⟩,
    exact hxX },
  refine hXbound (mem_bUnion hXY _),
  exact_mod_cast S.disjoint hX hY ⟨hxX, hyY⟩,
end

lemma disjoint_interiors_aux {S : simplicial_complex m} {X Y : finset E}
  (hX : X ∈ S.faces) (hY : Y ∈ S.faces) (h : X ≠ Y) :
  disjoint (combi_interior X) (combi_interior Y) :=
λ x hx, h (disjoint_interiors hX hY _ hx)

lemma simplex_interior_covers (X : finset E) :
  convex_hull ↑X = ⋃ (Y ⊆ X), combi_interior Y :=
begin
  apply subset.antisymm _ _,
  { apply X.strong_induction_on,
    rintro s ih x hx,
    by_cases x ∈ boundary s,
    { rw [boundary] at h,
      simp only [exists_prop, set.mem_Union] at h,
      obtain ⟨t, st, ht⟩ := h,
      specialize ih _ st ht,
      simp only [exists_prop, set.mem_Union] at ⊢ ih,
      obtain ⟨Z, Zt, hZ⟩ := ih,
      exact ⟨_, subset.trans Zt st.1, hZ⟩ },
    { exact subset_bUnion_of_mem (λ _ t, t) ⟨hx, h⟩ } },
  { exact bUnion_subset (λ Y hY, subset.trans (diff_subset _ _) (convex_hull_mono hY)) },
end

lemma interiors_cover (S : simplicial_complex m) :
  S.space = ⋃ X ∈ S.faces, combi_interior X :=
begin
  apply subset.antisymm _ _,
  { apply bUnion_subset,
    rintro X hX,
    rw simplex_interior_covers,
    exact Union_subset (λ Y, Union_subset (λ YX, subset_bUnion_of_mem (S.down_closed hX YX)))},
  { apply bUnion_subset,
    rintro Y hY,
    exact subset.trans (diff_subset _ _) (subset_bUnion_of_mem hY) }
end

/- The simplices interiors form a partition of the underlying space (except that they contain the
empty set) -/
lemma combi_interiors_partition {S : simplicial_complex m} {x} (hx : x ∈ S.space) :
  ∃! X, X ∈ S.faces ∧ x ∈ combi_interior X :=
begin
  rw interiors_cover S at hx,
  simp only [set.mem_bUnion_iff] at hx,
  obtain ⟨X, hX, hxX⟩ := hx,
  exact ⟨X, ⟨⟨hX, hxX⟩, (λ Y ⟨hY, hxY⟩, disjoint_interiors hY hX x ⟨hxY, hxX⟩)⟩⟩,
end

lemma is_closed_convex_hull {X : finset E} : is_closed (convex_hull (X : set E)) :=
X.finite_to_set.is_closed_convex_hull

lemma is_closed_boundary {X : finset E} : is_closed (boundary X) :=
begin
  apply is_closed_bUnion,
  { suffices : set.finite {Y | Y ⊆ X},
    { exact this.subset (λ i h, h.1) },
    convert X.powerset.finite_to_set using 1,
    ext,
    simp },
  { intros i hi,
    apply is_closed_convex_hull }
end

/- interior X is the topological interior iff X is of dimension m -/
lemma interiors_agree_of_high_dimension {S : simplicial_complex m}
  {X} (hX : X ∈ S.faces) (hXdim : X.card = m + 1) :
  combi_interior X = interior X :=
begin
  sorry
end

/-
S₁ ≤ S₂ (S₁ is a subdivision of S₂) iff their underlying space is the same and each face of S₁ is
contained in some face of S₂
-/
instance : has_le (simplicial_complex m) := ⟨λ S₁ S₂, S₁.space = S₂.space ∧
  ∀ {X₁ : finset (fin m → ℝ)}, X₁ ∈ S₁.faces → ∃ X₂ ∈ S₂.faces,
  convex_hull (X₁ : set(fin m → ℝ)) ⊆ convex_hull (X₂ : set(fin m → ℝ))⟩

def subdivision_order : partial_order (simplicial_complex m) :=
  {le := λ S₁ S₂, S₁ ≤ S₂,
  le_refl := (λ S, ⟨rfl, (λ X hX, ⟨X, hX, subset.refl _⟩)⟩),
  le_trans := begin
    rintro S₁ S₂ S₃ h₁₂ h₂₃,
    use eq.trans h₁₂.1 h₂₃.1,
    rintro X₁ hX₁,
    obtain ⟨X₂, hX₂, hX₁₂⟩ := h₁₂.2 hX₁,
    obtain ⟨X₃, hX₃, hX₂₃⟩ := h₂₃.2 hX₂,
    exact ⟨X₃, hX₃, subset.trans hX₁₂ hX₂₃⟩,
  end,
  le_antisymm := begin
    have aux_lemma : ∀ {S₁ S₂ : simplicial_complex m}, S₁ ≤ S₂ → S₂ ≤ S₁ → ∀ {X},
      X ∈ S₁.faces → X ∈ S₂.faces,
    {
      rintro S₁ S₂ h₁ h₂ W hW,
      apply finset.strong_downward_induction_on (λ X hX, simplex_dimension_le_space_dimension hX)
        hW,
      {
        rintro X hX h,
        obtain ⟨Y, hY, hXYhull⟩ := h₁.2 hX,
        obtain ⟨Z, hZ, hYZhull⟩ := h₂.2 hY,
        have hXZhull := subset.trans (inter_subset_inter_right (convex_hull ↑X)
          (subset.trans hXYhull hYZhull)) (S₁.disjoint hX hZ),
        rw inter_self at hXZhull,
        norm_cast at hXZhull,
        have hXZ : X ⊆ Z := subset.trans
          (subset_of_convex_hull_eq_convex_hull_of_linearly_independent (S₁.indep hX)
          (subset.antisymm hXZhull (convex_hull_mono (finset.inter_subset_left X Z))))
          (finset.inter_subset_right _ _),
        by_cases hZX : Z ⊆ X,
        {
          rw finset.subset.antisymm hZX hXZ at hYZhull,
          rw eq_of_convex_hull_eq_convex_hull_of_linearly_independent_of_linearly_independent
            (S₁.indep hX) (S₂.indep hY) (subset.antisymm hXYhull hYZhull),
          exact hY,
        },
        { exact S₂.down_closed (h hZ ⟨hXZ, hZX⟩) hXZ }
      }
    },
    rintro S₁ S₂ h₁ h₂,
    ext X,
    exact ⟨λ hX, aux_lemma h₁ h₂ hX, λ hX, aux_lemma h₂ h₁ hX⟩,
  end}

/-A simplicial complex is connected iff its space is-/
def simplicial_complex.connected (S : simplicial_complex m) : Prop := connected_space S.space

lemma empty_space_of_empty_simplicial_complex (m : ℕ) : (empty_simplicial_complex m).space = ∅ :=
begin
  unfold empty_simplicial_complex simplicial_complex.space,
  simp,
end

/-A simplicial complex is connected iff its 1-skeleton is-/
lemma connected_iff_one_skeleton_connected {S : simplicial_complex m} :
  S.connected ↔ (S.skeleton 1).connected :=
begin
  split,
  { rintro h,
    unfold simplicial_complex.connected,
    sorry
  },
  {
    sorry
  }
end

/-A simplex is locally finite iff each face belongs to finitely many faces-/
def simplicial_complex.locally_finite (S : simplicial_complex m) : Prop :=
  ∀ x : fin m → ℝ, finite {X | X ∈ S.faces ∧ x ∈ convex_hull (X : set(fin m → ℝ))}

lemma locally_compact_realisation_of_locally_finite (S : simplicial_complex m)
  (hS : S.locally_finite) : locally_compact_space S.space :=
  {local_compact_nhds := begin
    rintro x X hX,
    sorry
  end}

/-The pyramid of a vertex v with respect to a simplicial complex S is the surcomplex consisting of
all faces of S along with all faces of S with v added -/
def pyramid {S : simplicial_complex m}
  (hS : ∀ X ∈ S.faces, finset.card X ≤ m) {v : fin m → ℝ} (hv : v ∉ convex_hull S.space) :
  simplicial_complex m :=
 {faces := {X' | ∃ X ∈ S.faces, X' ⊆ X ∪ {v}},
   --an alternative is S.faces ∪ S.faces.image (insert v)
   --a problem is that S.faces = ∅ should output (S.pyramid hS v hv).faces = {v} but this def doesn't
   --as said in the definition of empty_simplicial_complex, a solution is to define faces = {∅}
   --instead of faces = ∅.
  indep := begin
    rintro X' ⟨X, hX, hX'X⟩,
    sorry
  end,
  down_closed := λ X' Y ⟨X, hX, hX'X⟩ hYX', ⟨X, hX, subset.trans hYX' hX'X⟩,
  disjoint := begin
    rintro X' Y' ⟨X, hX, hX'X⟩ ⟨Y, hY, hY'Y⟩,
    sorry
  end}

lemma subcomplex_pyramid {S : simplicial_complex m} {v : fin m → ℝ}
  (hS : ∀ X ∈ S.faces, finset.card X ≤ m) (hv : v ∉ convex_hull S.space) :
  S.faces ⊆ (pyramid hS hv).faces := λ X hX, ⟨X, hX, finset.subset_union_left X {v}⟩

--S₁ ≤ S₂ → S₁.space = S₂.space so maybe we can get rid of hv₂?
lemma pyramid_mono {S₁ S₂ : simplicial_complex m} {v : fin m → ℝ}
  (hS₁ : ∀ X ∈ S₁.faces, finset.card X ≤ m) (hS₂ : ∀ X ∈ S₂.faces, finset.card X ≤ m)
  (hv₁ : v ∉ convex_hull S₁.space) (hv₂ : v ∉ convex_hull S₂.space) :
  S₁ ≤ S₂ → pyramid hS₁ hv₁ ≤ pyramid hS₂ hv₂ :=
begin
  rintro h,
  split,
  {
    sorry
  },
  {
    rintro X ⟨Y, hY, hXYv⟩,
    obtain ⟨Z, hZ, hYZhull⟩ := h.2 hY,
    use Z ∪ {v},
    split,
    {
      exact ⟨Z, hZ, subset.refl _⟩,
    },
    have hXYvhull : convex_hull ↑X ⊆ convex_hull ↑(Y ∪ {v}) := convex_hull_mono hXYv,
    have hYvZvhull : convex_hull ↑(Y ∪ {v}) ⊆ convex_hull ↑(Z ∪ {v}),
    {
      sorry
    },
    exact subset.trans hXYvhull hYvZvhull,
  }
end

/--
A polytope of dimension `n` in `R^m` is a subset for which there exists a simplicial complex which
is pure of dimension `n` and has the same underlying space.
-/
@[ext] structure polytope (m n : ℕ) :=
(space : set (fin m → ℝ))
(realisable : ∃ (S : simplicial_complex m), S.pure ∧ space = S.space)

def polytope.vertices (P : polytope m n) : set (fin m → ℝ) :=
  ⋂ (S : simplicial_complex m) (H : P.space = S.space), {x | {x} ∈ S.faces}

def polytope.edges (P : polytope m n) : set (finset (fin m → ℝ)) :=
  ⋂ (S : simplicial_complex m) (H : P.space = S.space), {X | X ∈ S.faces ∧ X.card = 2}

noncomputable def polytope.realisation (P : polytope m n) :
  simplicial_complex m := classical.some P.realisable

lemma pure_polytope_realisation (P : polytope m n) : P.realisation.pure :=
begin
  sorry --trivial by definition but I don't know how to do it
end

--def polytope.faces {n : ℕ} (P : polytope m n) : set (finset (fin m → ℝ)) :=
--  P.realisation.boundary.faces

/- Every convex polytope can be realised by a simplicial complex with the same vertices-/
lemma polytope.triangulable_of_convex {P : polytope m n} : convex P.space
  → ∃ (S : simplicial_complex m), P.space = S.space ∧ ∀ x, {x} ∈ S.faces → x ∈ P.vertices :=
begin
  rintro hPconvex,
  cases P.space.eq_empty_or_nonempty with hPempty hPnonempty,
  {
    use empty_simplicial_complex m,
    rw empty_space_of_empty_simplicial_complex m,
    use hPempty,
    rintro X (hX : {X} ∈ {∅}),
    simp at hX,
    exfalso,
    exact hX,
  },
  obtain ⟨x, hx⟩ := hPnonempty,
  --consider the boundary of some realisation of P and remove it x,
  --have := P.realisation.boundary.erasure {x},
  --then add it back by taking the pyramid of this monster with x
  sorry
end

noncomputable def polytope.triangulation_of_convex {P : polytope m n} (hP : convex P.space) :
  simplicial_complex m := classical.some (polytope.triangulable_of_convex hP)

end affine
