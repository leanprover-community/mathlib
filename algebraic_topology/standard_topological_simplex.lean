import algebraic_topology.simplex_category algebraic_topology.simplicial_set analysis.topology.topological_space analysis.nnreal
noncomputable theory
open finset

local notation `ℝ≥0` := nnreal

/- Powers of types -/
section typepown

instance typepown : has_pow Type* ℕ := ⟨λ α n, fin n → α⟩

instance Rge0pown_topology {n : ℕ} : topological_space (ℝ≥0^n) :=
by show topological_space (fin n → ℝ≥0); apply_instance

end typepown

/-- The n-th standard topological simplex: Δ_n = { x ∈ ℝ^{n+1} | ∀ i, x_i ≥ 0, and ∑ x_i = 1 } -/
definition standard_topological_simplex (n : ℕ) : set (ℝ≥0^(n+1)) :=
 λ x : fin (n+1) → ℝ≥0, sum univ x = 1

local notation ` Δ `   := standard_topological_simplex
local notation ` [`n`] ` := fin (n+1)

namespace standard_topological_simplex

variable {n : ℕ}

-- definition induced_map {m n : ℕ} (f : [m] → [n]): Δ m → Δ n :=
-- λ x, ⟨finsupp.map_domain f x.val, sorry⟩

-- this looks like finsupp.map_domain
definition induced_map {m n : ℕ} (f : [m] → [n]): Δ m → Δ n :=
λ x, ⟨λ j, sum (univ.filter (λ i, f i = j)) x.val,
begin
  show sum univ (λ (j : [n]), sum (univ.filter (λ i, f i = j)) (x.val)) = 1,
  rw ←finset.sum_bind,
  { rw show finset.bind univ (λ (x : [n]), filter (λ (i : [m]), f i = x) univ) = univ,
    begin
      apply ext.2,
      simp,
      intro i,
      exact exists.intro (f i) (eq.refl (f i)),
    end,
    exact x.property },
  { intros x hx y hy xney,
    apply ext.2,
    simp,
    intros i hfi,
    rw hfi,
    exact xney}
end⟩

@[simp] lemma induced_map_id {n : ℕ} : induced_map (@id [n]) = id :=
begin
  funext x,
  simp [induced_map],
  apply subtype.eq,
  funext j,
  simp,
  rw show filter (λ (i : [n]), i = j) univ = (finset.singleton j), by ext; split; finish,
  apply finset.sum_singleton
end

lemma induced_map_comp {l m n : ℕ} (f : [l] → [m]) (g : [m] → [n]) :
induced_map (g ∘ f) = (induced_map g) ∘ (induced_map f) :=
begin
  funext x,
  simp [induced_map],
  funext j,
  rw ←finset.sum_bind,
  { have H :
    finset.bind (filter (λ (i : [m]), g i = j) univ)
      (λ (x : [m]), filter (λ (i : [l]), f i = x) univ) =
    filter (λ (i : [l]), g (f i) = j) univ :=
    begin
      apply ext.2, simp
    end,
    rw H},
  { intros i hi k hk inek,
    apply ext.2,
    simp,
    intros x hx,
    rw hx,
    exact inek}
end

definition sum_map {m n : ℕ} (f : fin m → fin n) : (ℝ≥0^m) → (ℝ≥0^n) :=
λ x j, sum (univ.filter (λ i, f i = j)) x

lemma commuting_square {m n : ℕ} (f : [m] → [n]) :
subtype.val ∘ (induced_map f) = (sum_map f) ∘ subtype.val := rfl

lemma continuous.pi_mk {X I : Type*} {Y : I → Type*}
[t₁ : topological_space X] [t₂ : Πi, topological_space (Y i)] (f : Πi, X → (Y i)) (H : Πi, continuous (f i))
: continuous (λ x i, f i x) :=
begin
let YY := (Πi, Y i),
apply continuous_Sup_rng,
intros t ht,
cases ht with i hi,
simp at *,
rw hi,
apply continuous_induced_rng,
unfold function.comp,
exact H i,
end

lemma continuous.pi_proj {I : Type*} {Y : I → Type*} [Πi, topological_space (Y i)]
(i : I) : continuous (λ y : Πj, Y j, y i) :=
begin
apply continuous_Sup_dom _ continuous_induced_dom,
existsi i,
simp
end

lemma continuous_sums {α : Type*} [decidable_eq α] {s : finset α} : continuous (λ x : (α → ℝ≥0), s.sum x) :=
begin
apply finset.induction_on s,
{ have triv : (λ (x : α → ℝ≥0), sum ∅ x) = λ (x : α → ℝ≥0), (0 : ℝ≥0) :=
  begin
    apply funext,
    intro x,
    apply finset.sum_empty
  end,
  rw triv,
  apply @continuous_const _ _ _ _ _},
{ intros a s ha hs,
  have triv : (λ (x : α → ℝ≥0), sum (insert a s) x) =
              ((λ (p : ℝ≥0 × ℝ≥0), p.fst + p.snd) ∘ (λ x, (x a, sum s x))) :=
  begin
    apply funext,
    intro x,
    apply finset.sum_insert ha
  end,
  rw triv,
  apply continuous.comp (continuous.prod_mk (continuous.pi_proj a) hs)
                        (@topological_add_monoid.continuous_add ℝ≥0 _ _ _)}
end

lemma continuous_sum_map {m n : ℕ} (f : fin m → fin n) : continuous (sum_map f):=
begin
apply @continuous.pi_mk (ℝ≥0^m) (fin n) _ _ _ _ _,
intro j,
simp,
apply continuous_sums,
end

theorem continuous_induced_map {m n : ℕ} (f : [m] → [n]) : continuous (induced_map f):=
begin
rw continuous_iff_induced_le,
unfold subtype.topological_space,
rw show topological_space.induced (induced_map f) (topological_space.induced subtype.val Rge0pown_topology) =
  ((topological_space.induced (induced_map f)) ∘ (topological_space.induced subtype.val)) Rge0pown_topology, by unfold function.comp,
rw [←induced_comp, commuting_square, ←continuous_iff_induced_le],
apply continuous.comp continuous_induced_dom (continuous_sum_map f)
end

/-- The i-th face map from Δ_n to Δ_{n+1} -/
def δ {n : ℕ} (i : [n+1]) : Δ n → Δ n.succ := induced_map (simplex_category.δ i)

lemma continuous_δ {n : ℕ} (i : [n+1]) : continuous (δ i)
:= continuous_induced_map (simplex_category.δ i)

end standard_topological_simplex

namespace singular_set

open simplicial_set standard_topological_simplex

/-- The singular set associated with a topological space X: its n-simplices are the continuous maps from Δ_n to X -/
definition S {X: Type*} [topological_space X] : simplicial_set :=
{ objs := λ n, {φ : Δ n → X // continuous φ},
  maps := λ m n f hf φ, ⟨φ.val ∘ induced_map f, continuous.comp (continuous_induced_map f) φ.property⟩,
  id := λ n, funext $ assume φ, by simp,
  comp := λ l m n f g hf hg, funext $ assume φ,
  begin
    simp,
    rw function.comp.assoc,
    rw ←induced_map_comp
  end}

end singular_set