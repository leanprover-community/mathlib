import tactic data.stream.basic data.set.basic data.finset data.multiset
       category.traversable.derive
open tactic

universe u
variable {α : Type}

example (s t u : set ℕ) (h : s ⊆ t ∩ u) (h' : u ⊆ s) : u ⊆ s → true :=
begin
  dunfold has_subset.subset has_inter.inter at *,
--  trace_state,
  intro1, triv
end

example (s t u : set ℕ) (h : s ⊆ t ∩ u) (h' : u ⊆ s) : u ⊆ s → true :=
begin
  delta has_subset.subset has_inter.inter at *,
--  trace_state,
  intro1, triv
end

example (x y z : ℕ) (h'' : true) (h : 0 + y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp at *,
--  trace_state,
  rw [←h, ←h']
end

example (x y z : ℕ) (h'' : true) (h : 0 + y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp at *,
  simp [h] at h',
  simp [*]
end

def my_id (x : α) := x

def my_id_def (x : α) : my_id x = x := rfl

example (x y z : ℕ) (h'' : true) (h : 0 + my_id y = x) (h' : 0 + y = z) : x = z + 0 :=
begin
  simp [my_id_def] at *, simp [h] at h', simp [*]
end

@[simp] theorem mem_set_of {a : α} {p : α → Prop} : a ∈ {a | p a} = p a := rfl

-- TODO: write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl
theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl
theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} := rfl

theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
begin
  dsimp [subset_def, union_def] at *,
  intros x h,
  cases h; back_chaining_using_hs
end

theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
begin
  dsimp [subset_def, inter_def] at *,
  intros x h,
  split; back_chaining_using_hs
end

/- extensionality -/

example : true :=
begin
  have : ∀ (s₀ s₁ : set ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target x ∈ s₀ ↔ x ∈ s₁,
    admit },
  have : ∀ (s₀ s₁ : finset ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target a ∈ s₀ ↔ a ∈ s₁,
    admit },
  have : ∀ (s₀ s₁ : multiset ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target multiset.count a s₀ = multiset.count a s₁,
    admit },
  have : ∀ (s₀ s₁ : list ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target list.nth s₀ n = list.nth s₁ n,
    admit },
  have : ∀ (s₀ s₁ : stream ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target stream.nth n s₀ = stream.nth n s₁,
    admit },
  have : ∀ n (s₀ s₁ : array n ℕ), s₀ = s₁,
  { intros, ext1,
    guard_target array.read s₀ i = array.read s₁ i,
    admit },
  trivial
end

/- tauto -/

example (p : Prop) : p ∧ true ↔ p := by tauto

example (p : Prop) : p ∨ false ↔ p := by tauto
-- local attribute [instance] classical.prop_decidable
example (p q r : Prop) [decidable p] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
example (p q r : Prop) [decidable q] [decidable r] : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : ¬ p) : q := by tauto
example (p q : Prop) [decidable q] [decidable p] (h : ¬ (p ↔ q)) (h' : q) : ¬ p := by tauto

/- traversable -/

meta def check_defn (n : name) (e : pexpr) : tactic unit :=
do (declaration.defn _ _ _ d _ _) ← get_decl n,
   e' ← to_expr e,
   guard (d =ₐ e') <|> trace d >> failed

set_option trace.app_builder true

@[derive traversable]
structure my_struct (α : Type) :=
  (y : ℤ)

run_cmd do
check_defn ``my_struct.traversable
  ``( { traversable .
        to_functor := my_struct.functor,
        traverse := λ (m : Type → Type) (_inst : applicative m) (α β : Type) (f : α → m β) (x : my_struct α),
               my_struct.rec (λ (x : ℤ), pure (λ (a : ulift ℤ), {y := a.down}) <*> pure {down := x}) x} )

@[derive traversable]
structure my_struct2 (α : Type u) : Type u :=
  (x : α)
  (y : ℤ)
  (z : list α)
  (k : list (list α))

run_cmd do
check_defn ``my_struct2.traversable
  ``( { traversable .
        to_functor := my_struct2.functor,
        traverse := λ (m : Type u → Type u) (_inst : applicative m) (α β : Type u) (f : α → m β) (x : my_struct2 α),
               my_struct2.rec
                 (λ (x_x : α) (x_y : ℤ) (x_z : list α) (x_k : list (list α)),
                    pure
                              (λ (a : β) (a_1 : ulift ℤ) (a_2 : list β) (a_3 : list (list β)),
                                 {x := a, y := a_1.down, z := a_2, k := a_3}) <*>
                            f x_x <*>
                          pure {down := x_y} <*>
                        traverse f x_z <*>
                      traverse (traverse f) x_k)
                 x } )
