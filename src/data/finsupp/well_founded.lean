/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import data.dfinsupp.well_founded
import data.finsupp.lex

/-!
# Well-foundedness of the lexicographic and product orders on `finsupp`

-/

variables {α N : Type*}

namespace finsupp

variables [hz : has_zero N] {r : α → α → Prop} {s : N → N → Prop}
  (hbot : ∀ ⦃n⦄, ¬ s n 0) (hs : well_founded s)
include hbot hs

lemma lex.acc (x : α →₀ N) (h : ∀ a ∈ x.support, acc (rᶜ ⊓ (≠)) a) : acc (finsupp.lex r s) x :=
begin
  rw lex_eq_inv_image_dfinsupp_lex, classical,
  refine inv_image.accessible to_dfinsupp (dfinsupp.lex.acc (λ a, hbot) (λ a, hs) _ _),
  simpa only [to_dfinsupp_support] using h,
end

theorem lex.well_founded (hr : well_founded $ rᶜ ⊓ (≠)) : well_founded (finsupp.lex r s) :=
⟨λ x, lex.acc hbot hs x $ λ a _, hr.apply a⟩

theorem lex.well_founded' [is_trichotomous α r]
  (hr : well_founded r.swap) : well_founded (finsupp.lex r s) :=
(lex_eq_inv_image_dfinsupp_lex r s).symm ▸
  inv_image.wf _ (dfinsupp.lex.well_founded' (λ a, hbot) (λ a, hs) hr)

omit hbot hs

instance lex.well_founded_lt [has_lt α] [is_trichotomous α (<)] [hα : well_founded_gt α]
  [canonically_ordered_add_monoid N] [hN : well_founded_lt N] : well_founded_lt (lex (α →₀ N)) :=
⟨lex.well_founded' (λ n, (zero_le n).not_lt) hN.wf hα.wf⟩

variable (r)

theorem lex.well_founded_of_finite [is_strict_total_order α r] [finite α] [has_zero N]
  (hs : well_founded s) : well_founded (finsupp.lex r s) :=
have _ := fintype.of_finite α,
  by exactI inv_image.wf (@equiv_fun_on_fintype α N _ _) (pi.lex.well_founded r $ λ a, hs)

theorem lex.well_founded_lt_of_finite [linear_order α] [finite α] [has_zero N] [has_lt N]
  [hwf : well_founded_lt N] : well_founded_lt (lex (α →₀ N)) :=
⟨finsupp.lex.well_founded_of_finite (<) hwf.1⟩

end finsupp
