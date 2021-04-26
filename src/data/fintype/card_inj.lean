/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import data.fintype.card
import data.nat.factorial
import tactic

/-!
# Birthday Problem

This file establishes the cardinality of `α ↪ β` in full generality.begin
-/

open_locale classical nat

open finset function
local notation `|` x `|` := finset.card x
local notation `‖` x `‖` := fintype.card x

-- is there some way to tell only `norm_num` to expand this out, but not `simp`?

/-- desc_fac n k = (n + k)! / n!, but implemented in a recursive way for calculation. -/
def desc_fac (n : ℕ) : ℕ → ℕ
| 0 := 1
| (k + 1) := (n + k + 1) * desc_fac k

@[simp] lemma desc_fac_zero (n : ℕ) : desc_fac n 0 = 1 := rfl

@[simp] lemma zero_desc_fac (k : ℕ) : desc_fac 0 k = k! :=
begin
  induction k with t ht, refl,
  unfold desc_fac, rw [ht, zero_add, nat.factorial_succ]
end

lemma desc_fac_succ {n k : ℕ} : desc_fac n k.succ = (n + k + 1) * desc_fac n k := rfl

lemma succ_desc_fac {n k : ℕ} : (n + 1) * desc_fac n.succ k = (n + k + 1) * desc_fac n k :=
begin
  induction k with t ht, simp!, rw desc_fac_succ, rw desc_fac_succ,
  have : (n + 1) * ((n.succ + t + 1) * desc_fac n.succ t)
       = (n.succ + t + 1) * ((n + 1) * desc_fac n.succ t), by ac_refl,
  rw this, rw ht, repeat {rw nat.succ_eq_add_one}, ac_refl
end

/-- Prove that `desc_fac` is what it is promised to be. Stated divison-less for ease. -/
theorem eval_desc_fac (n : ℕ) : ∀ k : ℕ, (n + k)! = n! * desc_fac n k
| 0 := by simp!
| (k + 1) := by unfold desc_fac; rw [←mul_assoc, mul_comm n!, mul_assoc, ←eval_desc_fac]; simp!

/-- An equivalence between all injective functions and all embeddings. -/
def embedding.equiv_inj_subtype (α β) : {f : α → β // injective f} ≃ (α ↪ β) :=
{ to_fun := λ f, ⟨f.val, f.property⟩,
  inv_fun := λ f, ⟨f, f.injective⟩,
  left_inv := λ f, by simp,
  right_inv := λ f, by {ext, simp} }

-- `decidable_pred (@injective α β)` and various variations didn't give me an instance 🤷‍♂️
noncomputable instance fintype.embedding {α β} [fintype α] [fintype β] : fintype (α ↪ β) :=
fintype.of_equiv {f : α → β // injective f} (embedding.equiv_inj_subtype α β)

/-- Establishes the cardinality of the type of injective functions `fin n ↪ β`. -/
lemma fintype.card_inj_aux (n : ℕ) (β) [fintype β] (h : n ≤ ‖β‖) :
  ‖fin n ↪ β‖ = desc_fac (‖β‖ - n) n :=
begin
  induction n with n hn,
  { rw [desc_fac_zero], nontriviality (fin 0 ↪ β),
    obtain ⟨f, g, ne⟩ := exists_pair_ne (fin 0 ↪ β),
    exfalso, apply ne, ext x, exact x.elim0 },

  -- type-checker doesn't like just using fin.cons
  let extend : (fin n → β) → β → fin n.succ → β :=
    λ f : fin n → β, λ b : β, fin.cons b f,

  let equiv_classes : (fin n ↪ β) → finset (fin n.succ ↪ β) :=
    λ f : fin n ↪ β, univ.filter (λ g : fin n.succ ↪ β, ∃ k : β, extend f k = g),

  have mem_equiv : ∀ f g, g ∈ equiv_classes f ↔ ∃ k : β, extend f k = g, by simp [equiv_classes],

  have all_injf_covered : univ = univ.bUnion equiv_classes,
  { apply subset.antisymm,
    { rintros f -, rw mem_bUnion,
      refine ⟨⟨fin.tail f, λ _ _ h, fin.succ_inj.mp $ f.injective h⟩, _⟩,
      suffices : ∃ (a : β), extend (fin.tail ⇑f) a = ⇑f, by simpa,
      use f 0, simp [extend] },
    { exact subset_univ _ } },

  have equiv_class_size : ∀ f : fin n ↪ β, |equiv_classes f| = ‖β‖ - n,
  {
    intro f, let poss_vals := univ \ finset.map ⟨f, f.inj'⟩ univ,

    have num_poss_vals : |poss_vals| = ‖β‖ - n, by simp [poss_vals, card_univ, card_sdiff],
    have mem_poss_vals : ∀ t, t ∈ poss_vals ↔ ∀ (x : fin n), ¬f x = t, by simp [poss_vals],

    apply le_antisymm,
    { by_contra card_too_big, let first := λ g : fin n.succ ↪ β, g 0,
      -- (if I just write down x 0 = y 0, it won't work! need this shim)
      suffices : ∃ x ∈ equiv_classes f, ∃ y ∈ equiv_classes f, x ≠ y ∧ first x = first y,
      { obtain ⟨x, x_equiv, y, y_equiv, x_ne_y, x_y_agree⟩ := this,
        rw [mem_equiv] at x_equiv y_equiv,
        obtain ⟨x_zero, x_equiv⟩ := x_equiv, obtain ⟨y_zero, y_equiv⟩ := y_equiv,
        simp only [extend, first] at x_y_agree x_equiv y_equiv,

        apply x_ne_y, ext t, revert t,
        refine fin.induction _ _,
          exact x_y_agree,
        rintros t -, rw [←x_equiv, ←y_equiv, fin.cons_succ, fin.cons_succ] },

      apply finset.exists_ne_map_eq_of_card_lt_of_maps_to,
      push_neg at card_too_big, rw ←num_poss_vals at card_too_big, exact card_too_big,

      intros g g_equiv, rw mem_equiv at g_equiv, obtain ⟨k, g_equiv⟩ := g_equiv,
      simp only [first, mem_poss_vals], simp only [extend] at g_equiv,
      have : g 0 = k, by rw [←g_equiv, fin.cons_zero],
      intros x eq, have : g x.succ = g 0, by rw [←eq, ←g_equiv, fin.cons_succ],
      apply fin.succ_ne_zero x, exact g.injective this },

    { let extended : finset (fin n.succ ↪ β) :=
        finset.map ⟨λ x : {x // x ∈ poss_vals}, ⟨extend f x, _⟩, _⟩ poss_vals.attach,
      rotate,
      { intros a₁ a₂, apply fin.induction_on a₁; apply fin.induction_on a₂,
        -- not sure how to do this `induction_on` using the `induction` tactic
        -- (all variants of `induction using fin.something` didn't work for me)
        { intro _, refl },
        { rintros i - eq, simp only [extend, fin.cons_zero, fin.cons_succ] at eq,
        have := x.prop, rw mem_poss_vals at this, exfalso, apply this i, exact eq.symm},
        { rintros i - eq, simp only [extend, fin.cons_zero, fin.cons_succ] at eq,
        have := x.prop, rw mem_poss_vals at this, exfalso, apply this i, exact eq},
        -- how can I undo this duplication?
        { rintros i₂ - i₁ -, simp only [extend, fin.cons_succ, fin.succ_inj],
          intro eq, exact f.injective eq } },

      { intros a₁ a₂ eq, simp only [extend] at eq,
        ext, rw funext_iff at eq,
        specialize eq 0, rwa [fin.cons_zero, fin.cons_zero] at eq },
      -- simp is getting hung up on `bex_def` here sadly, so have to do it manually
      have mem_extended : ∀ {g : fin n.succ ↪ β}, g ∈ extended → ∃ a ∈ poss_vals, extend ⇑f a = g,
        intros g g_extended, simp only [extended, mem_map] at g_extended,
        obtain ⟨⟨a, a_poss⟩, -, g_extended⟩ := g_extended,
        simp only [embedding.coe_fn_mk, subtype.coe_mk] at g_extended,
        refine ⟨a, a_poss, _⟩, rw ←g_extended, simp,

      have : |extended| = ‖β‖ - n, by simp [extended, poss_vals, card_sdiff, card_univ],

      rw ←this, apply card_le_of_subset, rintros g g_extended,
      simp only [extend, mem_equiv],
      use g 0, ext t, revert t,
      refine fin.induction (by rw fin.cons_zero) _,
      rintros i -,
      obtain ⟨k, untouched, g_extended⟩ := mem_extended g_extended,
      rw ←g_extended, simp [extend] } },

  rw [←card_univ, all_injf_covered, card_bUnion], swap, -- card_bUnion has a disjointness req
  { rintros g - j - g_ne_j, rw disjoint_iff_ne, intros a a_equiv b b_equiv,
    intro a_eq_b, apply g_ne_j, rw mem_equiv at a_equiv b_equiv,
    obtain ⟨k₁, a_equiv⟩ := a_equiv, obtain ⟨k₂, b_equiv⟩ := b_equiv,
    simp only [extend] at a_equiv b_equiv, subst a_eq_b, rw ←b_equiv at a_equiv,
    apply_fun fin.tail at a_equiv, repeat { rw fin.tail_cons at a_equiv },
    ext, rw a_equiv },
  unfold desc_fac,

  suffices : ‖fin n ↪ β‖ * (‖β‖ - n) = (‖β‖ - n.succ + n + 1) * desc_fac (‖β‖ - n.succ) n,
  { simpa [equiv_class_size, card_univ] },

  rw hn (nat.lt_of_succ_le h).le,
  set t := ‖β‖ - n.succ with ht,
  have : ‖β‖ - n = t.succ,
  { rw [ht, nat.succ_eq_add_one, ←nat.sub_sub_assoc, nat.succ_sub_one],
    exact h, exact nat.succ_pos _ },
  rw [this, mul_comm, succ_desc_fac]
end

/-- Embeddings are equivalent under equivalences. -/
def equiv.embedding {α β γ δ : Type*} (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪ δ) :=
{ to_fun := λ f,
    ⟨h' ∘ f ∘ h.symm, (h'.comp_injective _).mpr $ (h.symm.injective_comp _).mpr f.injective⟩,
  inv_fun := λ f,
    ⟨h'.symm ∘ f ∘ h, (h'.symm.comp_injective _).mpr $ (h.injective_comp _).mpr f.injective⟩,
  left_inv := λ x, by {ext, simp},
  right_inv := λ x, by {ext, simp} }

/- The cardinality of the type of all embeddings is given by the size of  -/
@[simp] theorem fintype.card_inj {α β} [fintype α] [fintype β] (h : ‖α‖ ≤ ‖β‖)
  : ‖α ↪ β‖ = (desc_fac (‖β‖ - ‖α‖) ‖α‖) :=
begin
  trunc_cases fintype.equiv_fin α with eq,
  rw fintype.card_congr (equiv.embedding eq (equiv.refl β)),
  exact fintype.card_inj_aux _ _ h,
end

theorem fintype.card_inj' {α β} [fintype α] [fintype β] (h : ‖β‖ < ‖α‖) : ‖α ↪ β‖ = 0 :=
begin
  rw fintype.card_eq_zero_iff, intro f,
  obtain ⟨x, y, eq, fne⟩ := fintype.exists_ne_map_eq_of_card_lt f h,
  have := f.injective fne, contradiction
end

theorem fintype.card_inj'' {α β} [fintype α] [fintype β] :
  ‖α ↪ β‖ = if ‖α‖ ≤ ‖β‖ then desc_fac (‖β‖ - ‖α‖) ‖α‖ else 0 :=
begin
  split_ifs with h,
    exact fintype.card_inj h,
    exact fintype.card_inj' (not_le.mp h)
end

-- just realised; is it worth registering `subsingleton` instances for `‖α ↪ β‖`
-- for when they either have equal cards or `α` is empty?
