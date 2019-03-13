/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

The module `lc α β` of linear combinations over `β` (`α` is the scalar ring)
-/
import linear_algebra.basic
noncomputable theory

open classical function lattice
local attribute [instance] prop_decidable

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- The type of linear coefficients, which are simply the finitely supported functions
from the module `β` to the scalar ring `α`. -/
@[reducible] def lc (α β) [ring α] [add_comm_group β] [module α β] : Type* := β →₀ α

namespace lc
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
open submodule linear_map

instance : add_comm_group (lc α β) := finsupp.add_comm_group

instance : has_scalar α (lc α β) := finsupp.to_has_scalar

instance : module α (lc α β) := finsupp.to_module β α

variables (α)
def supported (s : set β) : submodule α (lc α β) :=
{ carrier := {l | ↑l.support ⊆ s},
  zero := by simp,
  add := λ l₁ l₂ h₁ h₂, set.subset.trans (finset.coe_subset.2 finsupp.support_add)
    (by simpa using set.union_subset h₁ h₂),
  smul := λ a l h, set.subset.trans (finset.coe_subset.2 finsupp.support_smul)
    (by simpa using h) }
variables {α}

theorem mem_supported {s : set β} {l : lc α β} :
  l ∈ supported α s ↔ ↑l.support ⊆ s := iff.rfl

theorem mem_supported' {s : set β} {l : lc α β} :
  l ∈ supported α s ↔ ∀ x ∉ s, l x = 0 :=
by simp [mem_supported, set.subset_def, not_imp_comm]

theorem single_mem_supported {s : set β} (a : α) {b : β} (h : b ∈ s) :
  finsupp.single b a ∈ supported α s :=
set.subset.trans finsupp.support_single_subset (set.singleton_subset_iff.2 h)

theorem supported_eq_span_single (s : set β) :
  lc.supported α s = span α ((λ x, finsupp.single x (1:α)) '' s) :=
begin
  refine (span_eq_of_le _ _ (le_def'.2 $ λ l hl, _)).symm,
  { rintro _ ⟨l, hl, rfl⟩, exact single_mem_supported _ hl },
  { rw ← l.sum_single,
    refine sum_mem _ (λ x xl, _),
    rw (by simp : finsupp.single x (l x) = l x • finsupp.single x 1),
    exact smul_mem _ _ (subset_span ⟨_, hl xl, rfl⟩) }
end

variables (α)
def restrict_dom (s : set β) : lc α β →ₗ supported α s :=
linear_map.cod_restrict _
  { to_fun := finsupp.filter (∈ s),
    add := λ l₁ l₂, finsupp.filter_add,
    smul := λ a l, finsupp.filter_smul }
  (λ l, mem_supported'.2 $ λ x, finsupp.filter_apply_neg (∈ s) l)
variables {α}

@[simp] theorem restrict_dom_apply (s : set β) (l : lc α β) :
  ↑((restrict_dom α s : lc α β →ₗ supported α s) l) = finsupp.filter (∈ s) l := rfl

theorem restrict_dom_comp_subtype (s : set β) :
  (restrict_dom α s).comp (submodule.subtype _) = linear_map.id :=
by ext l; apply subtype.coe_ext.2; simp; ext a;
   by_cases a ∈ s; simp [h]; exact (mem_supported'.1 l.2 _ h).symm

theorem range_restrict_dom (s : set β) : (restrict_dom α s).range = ⊤ :=
begin
  have := linear_map.range_comp (submodule.subtype _) (restrict_dom α s),
  rw [restrict_dom_comp_subtype, linear_map.range_id] at this,
  exact eq_top_mono (submodule.map_mono le_top) this.symm
end

theorem supported_mono {s t : set β} (st : s ⊆ t) :
  supported α s ≤ supported α t :=
λ l h, set.subset.trans h st

@[simp] theorem supported_empty : supported α (∅ : set β) = ⊥ :=
eq_bot_iff.2 $ λ l h, (submodule.mem_bot α).2 $
by ext; simp [*, mem_supported'] at *

@[simp] theorem supported_univ : supported α (set.univ : set β) = ⊤ :=
eq_top_iff.2 $ λ l _, set.subset_univ _

theorem supported_Union {ι : Type*} (s : ι → set β) :
  supported α (⋃ i, s i) = ⨆ i, supported α (s i) :=
begin
  refine le_antisymm _ (supr_le $ λ i, supported_mono $ set.subset_Union _ _),
  suffices : ((submodule.subtype _).comp (restrict_dom α (⋃ i, s i))).range ≤ ⨆ i, supported α (s i),
  { rwa [range_comp, range_restrict_dom, map_top, range_subtype] at this },
  rw [range_le_iff_comap, eq_top_iff],
  rintro l ⟨⟩, rw mem_coe,
  apply finsupp.induction l, {exact zero_mem _},
  refine λ x a l hl a0, add_mem _ _,
  by_cases (∃ i, x ∈ s i); simp [h],
  cases h with i hi,
  exact le_supr (λ i, supported α (s i)) i (single_mem_supported _ hi)
end

theorem supported_union (s t : set β) :
  supported α (s ∪ t) = supported α s ⊔ supported α t :=
by erw [set.union_eq_Union, supported_Union, supr_bool_eq]; refl

theorem supported_Inter {ι : Type*} (s : ι → set β) :
  supported α (⋂ i, s i) = ⨅ i, supported α (s i) :=
begin
  refine le_antisymm (le_infi $ λ i, supported_mono $ set.Inter_subset _ _) _,
  simp [le_def, infi_coe, set.subset_def],
  exact λ l, set.subset_Inter
end

def apply (x : β) : lc α β →ₗ α :=
⟨λ l, l x, λ _ _, finsupp.add_apply, λ _ _, finsupp.smul_apply⟩

@[simp] theorem apply_apply (x : β) (l : lc α β) :
  (lc.apply x : lc α β →ₗ α) l = l x := rfl

protected def lsum (f : β → α →ₗ[α] γ) : lc α β →ₗ[α] γ :=
⟨λ d, d.sum (λ b, f b),
  assume d₁ d₂, by simp [finsupp.sum_add_index],
  assume a d, by simp [finsupp.sum_smul_index, finsupp.smul_sum,
    -smul_eq_mul, smul_eq_mul.symm]⟩

@[simp] theorem lsum_apply (f : β → α →ₗ γ) (l : lc α β) :
  (lc.lsum f : lc α β →ₗ γ) l = l.sum (λ b, f b) := rfl

section
variables (α β)
protected def total : lc α β →ₗ β := lc.lsum linear_map.id.smul_right
end

theorem total_apply (l : lc α β) :
  lc.total α β l = l.sum (λ b a, a • b) := rfl

@[simp] theorem total_single (a : α) (x : β) :
  lc.total α β (finsupp.single x a) = a • x :=
by simp [total_apply, finsupp.sum_single_index]

@[simp] theorem total_range : (lc.total α β).range = ⊤ :=
range_eq_top.2 $ λ x, ⟨finsupp.single x 1, by simp⟩

variables (α)
protected def map (f : β → γ) : lc α β →ₗ[α] lc α γ :=
{ to_fun := finsupp.map_domain f,
  add := λ l₁ l₂, finsupp.map_domain_add,
  smul := λ a l, finsupp.map_domain_smul _ _ }
variables {α}

@[simp] theorem map_apply (f : β → γ) (l : lc α β) :
  (lc.map α f : _ →ₗ _) l = finsupp.map_domain f l := rfl

@[simp] theorem map_id : (lc.map α id : lc α β →ₗ[α] lc α β) = linear_map.id :=
linear_map.ext $ λ l, finsupp.map_domain_id

theorem map_comp (f : β → γ) (g : γ → δ) :
  lc.map α (g ∘ f) = (lc.map α g).comp (lc.map α f) :=
linear_map.ext $ λ l, finsupp.map_domain_comp

theorem supported_comap_map (f : β → γ) (s : set γ) :
  supported α (f ⁻¹' s) ≤ (supported α s).comap (lc.map α f) :=
λ l (hl : ↑l.support ⊆ f ⁻¹' s),
show ↑(finsupp.map_domain f l).support ⊆ s, begin
  rw [← set.image_subset_iff, ← finset.coe_image] at hl,
  exact set.subset.trans finsupp.map_domain_support hl
end

theorem map_supported (f : β → γ) (s : set β) :
  (supported α s).map (lc.map α f) = supported α (f '' s) :=
begin
  refine le_antisymm (map_le_iff_le_comap.2 $
    le_trans (supported_mono $ set.subset_preimage_image _ _)
       (supported_comap_map _ _)) _,
  intros l hl, haveI : inhabited β := ⟨0⟩,
  refine ⟨(lc.map α (inv_fun_on f s) : lc α γ →ₗ lc α β) l, λ x hx, _, _⟩,
  { rcases finset.mem_image.1 (finsupp.map_domain_support hx) with ⟨c, hc, rfl⟩,
    exact inv_fun_on_mem (by simpa using hl hc) },
  { rw [← linear_map.comp_apply, ← map_comp],
    refine (finsupp.map_domain_congr $ λ c hc, _).trans finsupp.map_domain_id,
    exact inv_fun_on_eq (by simpa using hl hc) }
end

theorem map_disjoint_ker (f : β → γ) {s : set β}
  (H : ∀ a b ∈ s, f a = f b → a = b) :
  disjoint (supported α s) (lc.map α f).ker :=
begin
  rintro l ⟨h₁, h₂⟩,
  rw [mem_coe, mem_ker, map_apply, finsupp.map_domain] at h₂,
  simp, ext x,
  by_cases xs : x ∈ s,
  { have : finsupp.sum l (λ a, finsupp.single (f a)) (f x) = 0, {rw h₂, refl},
    rw [finsupp.sum_apply, finsupp.sum, finset.sum_eq_single x] at this,
    { simpa [finsupp.single_apply] },
    { intros y hy xy, simp [mt (H _ _ (h₁ hy) xs) xy] },
    { simp {contextual := tt} } },
  { by_contra h, exact xs (h₁ $ finsupp.mem_support_iff.2 h) }
end

theorem map_total (f : β →ₗ[α] γ) :
  (lc.total α γ).comp (lc.map α f) = f.comp (lc.total α β) :=
by ext; simp [total_apply, finsupp.sum_map_domain_index, add_smul]

end lc

namespace lc
variables [discrete_field α] [add_comm_group β] [vector_space α β]

instance : vector_space α (lc α β) := { .. lc.module }

end lc

section module
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables {a b : α} {s t : set β} {x y : β}
include α
open submodule

theorem span_eq_map_lc : span α s = (lc.supported α s).map (lc.total α β) :=
begin
  apply span_eq_of_le,
  { exact λ x hx, ⟨_, lc.single_mem_supported 1 hx, by simp⟩ },
  { refine map_le_iff_le_comap.2 (λ v hv, _),
    have : ∀c, v c • c ∈ span α s,
    { intro c, by_cases c ∈ s,
      { exact smul_mem _ _ (subset_span h) },
      { simp [lc.mem_supported'.1 hv _ h] } },
    refine sum_mem _ _, simp [this] }
end

theorem mem_span_iff_lc : x ∈ span α s ↔ ∃ l ∈ lc.supported α s, lc.total α β l = x :=
by rw span_eq_map_lc; simp

variables (α)
def lc.total_on (s : set β) : lc.supported α s →ₗ span α s :=
linear_map.cod_restrict _ ((lc.total α _).comp (submodule.subtype _)) $
  λ ⟨l, hl⟩, mem_span_iff_lc.2 ⟨l, hl, rfl⟩
variables {α}

theorem lc.total_on_range (s : set β) : (lc.total_on α s).range = ⊤ :=
by rw [lc.total_on, linear_map.range, linear_map.map_cod_restrict, ← linear_map.range_le_iff_comap,
  range_subtype, map_top, linear_map.range_comp, range_subtype]; exact le_of_eq span_eq_map_lc

lemma linear_eq_on {f g : β →ₗ[α] γ} (H : ∀x∈s, f x = g x) {x} (h : x ∈ span α s) : f x = g x :=
by apply span_induction h H; simp {contextual := tt}

open finsupp finset
def finsupp_equiv_lc [decidable_pred s] : (s →₀ α) ≃ lc.supported α s :=
{ to_fun := λ f, ⟨map_domain subtype.val f,
    assume a h,
    have h0 : a ∈ image _ _, from mem_of_subset map_domain_support h,
    let ⟨ap, _, hs⟩ := mem_image.mp h0 in hs ▸ ap.property⟩,
  inv_fun := (finsupp.subtype_domain s) ∘ subtype.val,
  left_inv := subtype_domain_right_inv _,
  right_inv := λ f, subtype.eq $ subtype_domain_left_inv _ f.val f.property }

end module
