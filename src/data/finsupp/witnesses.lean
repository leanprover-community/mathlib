/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finsupp.basic

/-!
#  Witnesses for finitely supported functions

Let `α N` be two Types, and assume that `N` has a `0` and let `f g : α →₀ N` be finitely supported
functions

##  Main definitions

*  `finset.diff f g : finset α`, the finite subset of `α` where `f` and `g` differ,
*  `finset.wit f g : α`, [assuming that `a` is non-empty and `N` is linearly ordered]
   the minimum of `finset.diff f g` (or a random element of `α` if
   `finset.diff f g` is empty, i.e. if `f = g`).

In the case in which `N` is an additive group, `finset.diff f g` coincides with
`finset.support (f - g)`.
-/

variables {α N : Type*}

namespace finsupp
variables [decidable_eq α] [decidable_eq N]

section diff

section N_has_zero
variables [has_zero N] {f g : α →₀ N}

/--  Given two finitely supported functions `f g : α →₀ N`, `finsupp.diff f g` is the `finset`
where `f` and `g` differ. -/
def diff (f g : α →₀ N) : finset α :=
(f.support ∪ g.support).filter (λ x, f x ≠ g x)

lemma diff_comm : f.diff g = g.diff f :=
by simp_rw [diff, finset.union_comm, ne_comm]

@[simp] lemma diff_eq_empty : f.diff g = ∅ ↔ f = g :=
begin
  refine ⟨λ h, _, λ h, h ▸ by simp [diff]⟩,
  ext a,
  refine not_ne_iff.mp (λ fg, not_ne_iff.mpr h _),
  refine finset.ne_empty_of_mem (_ : a ∈ _),
  simp only [diff, finset.mem_filter, finset.mem_union, finsupp.mem_support_iff],
  exact ⟨fg.ne_or_ne _, fg⟩,
end

@[simp] lemma nonempty_diff_iff : (f.diff g).nonempty ↔ f ≠ g :=
finset.nonempty_iff_ne_empty.trans diff_eq_empty.not

@[simp]
lemma diff_zero_right : f.diff 0 = f.support :=
by simp only [diff, coe_zero, pi.zero_apply, support_zero, finset.union_empty,
    finset.filter_true_of_mem, mem_support_iff, imp_self, implies_true_iff]

@[simp]
lemma diff_zero_left : (0 : α →₀ N).diff f = f.support :=
diff_comm.trans diff_zero_right

@[simp]
lemma mem_diff {a : α} : a ∈ f.diff g ↔ f a ≠ g a :=
by simpa only [diff, finset.mem_filter, finset.mem_union, mem_support_iff, and_iff_right_iff_imp]
    using ne.ne_or_ne _

lemma set_ne_eq_diff : {x | f x ≠ g x} = f.diff g :=
by { ext, simp only [set.mem_set_of_eq, finset.mem_coe, mem_diff] }

lemma subset_map_range_diff {M} [decidable_eq M] [has_zero M] (F : zero_hom N M) :
  (f.map_range F F.map_zero).diff (g.map_range F F.map_zero) ⊆ f.diff g :=
begin
  refine λ x, _,
  simp only [mem_diff, map_range_apply, not_not],
  exact not_imp_not.mpr (λ h, h ▸ rfl),
end

lemma map_range_diff_eq {M} [decidable_eq M] [has_zero M]
  (F : zero_hom N M) (hF : function.injective F) :
  (f.map_range F F.map_zero).diff (g.map_range F F.map_zero) = f.diff g :=
by { ext, simpa only [mem_diff] using hF.ne_iff }

end N_has_zero

lemma add_diff_add_eq_left [add_left_cancel_monoid N] (f : α →₀ N) {g h : α →₀ N} :
  (f + g).diff (f + h) = g.diff h  :=
begin
  ext,
  simp only [diff, ne.def, add_right_inj, finset.mem_filter, finset.mem_union, mem_support_iff,
    coe_add, pi.add_apply, and.congr_left_iff],
  exact λ bc, ⟨λ h, ne.ne_or_ne 0 bc, λ h, ne.ne_or_ne _ ((add_right_inj _).not.mpr bc)⟩,
end

--  can this proof by replaced by the previous one applied to `Nᵃᵒᵖ` and interlaced with `op unop`?
lemma add_diff_add_eq_right [add_right_cancel_monoid N] {f g : α →₀ N} (h : α →₀ N):
  (f + h).diff (g + h) = f.diff g  :=
begin
  ext,
  simp only [diff, ne.def, add_left_inj, finset.mem_filter, finset.mem_union, mem_support_iff,
    coe_add, pi.add_apply, and.congr_left_iff],
  exact λ bc, ⟨λ h, ne.ne_or_ne 0 bc, λ h, ne.ne_or_ne _ ((add_left_inj _).not.mpr bc)⟩,
end

@[simp] lemma diff_neg_left [add_group N] {f g : α →₀ N} :
  (- f).diff g = f.diff (- g) :=
begin
  nth_rewrite 0 ← neg_neg g,
  apply map_range_diff_eq ⟨has_neg.neg, _⟩,
  exacts [neg_injective, neg_zero],
end

@[simp] lemma diff_eq_support_sub [add_group N] {f g : α →₀ N} :
  f.diff g = (f - g).support :=
by rw [← add_diff_add_eq_right (- g), add_right_neg, diff_zero_right, sub_eq_add_neg]

end diff

section wit
variables [nonempty α] [linear_order α]

section N_has_zero
variables [has_zero N] {f g : α →₀N}

/--  Given two finitely supported functions `f g : α →₀ N`, `finsupp.wit f g` is an element of `α`.
It is a "generic" element of `α` (namely, `nonempty.some _ : α`) if and only if `f = g`.
Otherwise, it is `a` if `a : α` is the smallest value for which `f a ≠ g a`. -/
noncomputable def wit (f g : α →₀ N) : α :=
dite (f.diff g).nonempty (λ h, (f.diff g).min' h) (λ _, nonempty.some ‹_›)

lemma wit_congr {f' g' : α →₀ N} (h : f.diff g = f'.diff g') :
  f.wit g = f'.wit g' :=
by { unfold wit, rw h }

lemma wit_mem_diff_iff_ne : f.wit g ∈ f.diff g ↔ f ≠ g :=
begin
  unfold wit,
  split_ifs,
  { simp [finset.min'_mem, nonempty_diff_iff.mp h] },
  { simp [not_ne_iff.mp (nonempty_diff_iff.not.mp h)] }
end

lemma wit_le {x : α} (hx : f x ≠ g x) : (f.wit g) ≤ x :=
begin
  unfold wit,
  split_ifs,
  { exact (f.diff g).min'_le x (mem_diff.mpr hx) },
  { exact (hx (congr_fun ((not_not.mp (nonempty_diff_iff.not.mp h))) x)).elim }
end

lemma wit_comm (f g : α →₀ N) : f.wit g = g.wit f :=
wit_congr diff_comm

lemma min'_eq_wit_of_ne (fg : f ≠ g) :
  (f.diff g).min' (nonempty_diff_iff.mpr fg) = f.wit g :=
(dif_pos _).symm

lemma wit_eq_wit_iff : f (f.wit g) = g (f.wit g) ↔ f = g :=
begin
  refine ⟨λ h, _, λ h, congr_fun h _⟩,
  refine not_ne_iff.mp (λ fg, not_ne_iff.mpr h _),
  exact mem_diff.mp (wit_mem_diff_iff_ne.mpr fg),
end

end N_has_zero

lemma wit_add_left [add_left_cancel_monoid N] {f g h : α →₀ N} :
  (f + g).wit (f + h) = g.wit h :=
wit_congr (add_diff_add_eq_left _)

lemma wit_add_right [add_right_cancel_monoid N] {f g h : α →₀ N} :
  (f + h).wit (g + h) = f.wit g :=
wit_congr (add_diff_add_eq_right _)

lemma wit_neg [add_group N] {f g : α →₀ N} :
  (- f).wit g = f.wit (- g) :=
wit_congr diff_neg_left

end wit

end finsupp
