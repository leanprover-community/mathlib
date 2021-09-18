/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import logic.function.iterate
import order.basic
import order.bounded_lattice
import order.complete_lattice
import tactic.monotonicity

/-!
# Preorder homomorphisms

Bundled monotone functions, `x ≤ y → f x ≤ f y`.
-/

/-- Bundled monotone (aka, increasing) function -/
structure preorder_hom (α β : Type*) [preorder α] [preorder β] :=
(to_fun   : α → β)
(mono' : monotone to_fun)

infixr ` →ₘ `:25 := preorder_hom

namespace preorder_hom
variables {α β γ δ : Type*} [preorder α] [preorder β] [preorder γ] [preorder δ]

instance : has_coe_to_fun (α →ₘ β) :=
{ F := λ f, α → β,
  coe := preorder_hom.to_fun }

initialize_simps_projections preorder_hom (to_fun → coe)

protected lemma mono (f : α →ₘ β) : monotone f :=
preorder_hom.mono' f

@[simp] lemma to_fun_eq_coe {f : α →ₘ β} : f.to_fun = f := rfl
@[simp] lemma coe_fun_mk {f : α → β} (hf : _root_.monotone f) : (mk f hf : α → β) = f := rfl

@[ext] -- See library note [partially-applied ext lemmas]
lemma ext (f g : α →ₘ β) (h : (f : α → β) = g) : f = g :=
by { cases f, cases g, congr, exact h }

/-- One can lift an unbundled monotone function to a bundled one. -/
instance : can_lift (α → β) (α →ₘ β) :=
{ coe := coe_fn,
  cond := monotone,
  prf := λ f h, ⟨⟨f, h⟩, rfl⟩ }

/-- The identity function as bundled monotone function. -/
@[simps {fully_applied := ff}]
def id : α →ₘ α := ⟨id, monotone_id⟩

instance : inhabited (α →ₘ α) := ⟨id⟩

/-- The preorder structure of `α →ₘ β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
instance : preorder (α →ₘ β) :=
@preorder.lift (α →ₘ β) (α → β) _ coe_fn

instance {β : Type*} [partial_order β] : partial_order (α →ₘ β) :=
@partial_order.lift (α →ₘ β) (α → β) _ coe_fn ext

lemma le_def {f g : α →ₘ β} : f ≤ g ↔ ∀ x, f x ≤ g x := iff.rfl

@[simp, norm_cast] lemma coe_le_coe {f g : α →ₘ β} : (f : α → β) ≤ g ↔ f ≤ g := iff.rfl

@[simp] lemma mk_le_mk {f g : α → β} {hf hg} : mk f hf ≤ mk g hg ↔ f ≤ g := iff.rfl

@[mono] lemma apply_mono {f g : α →ₘ β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) :
  f x ≤ g y :=
(h₁ x).trans $ g.mono h₂

/-- Curry/uncurry as an order isomorphism between `α × β →ₘ γ` and `α →ₘ β →ₘ γ`. -/
def curry : (α × β →ₘ γ) ≃o (α →ₘ β →ₘ γ) :=
{ to_fun := λ f, ⟨λ x, ⟨function.curry f x, λ y₁ y₂ h, f.mono ⟨le_rfl, h⟩⟩,
    λ x₁ x₂ h y, f.mono ⟨h, le_rfl⟩⟩,
  inv_fun := λ f, ⟨function.uncurry (λ x, f x), λ x y h, (f.mono h.1 x.2).trans $ (f y.1).mono h.2⟩,
  left_inv := λ f, by { ext ⟨x, y⟩, refl },
  right_inv := λ f, by { ext x y, refl },
  map_rel_iff' := λ f g, by simp [le_def] }

@[simp] lemma curry_apply (f : α × β →ₘ γ) (x : α) (y : β) : curry f x y = f (x, y) := rfl

@[simp] lemma curry_symm_apply (f : α →ₘ β →ₘ γ) (x : α × β) : curry.symm f x = f x.1 x.2 := rfl

/-- The composition of two bundled monotone functions. -/
@[simps {fully_applied := ff}]
def comp (g : β →ₘ γ) (f : α →ₘ β) : α →ₘ γ := ⟨g ∘ f, g.mono.comp f.mono⟩

@[mono] lemma comp_mono ⦃g₁ g₂ : β →ₘ γ⦄ (hg : g₁ ≤ g₂) ⦃f₁ f₂ : α →ₘ β⦄ (hf : f₁ ≤ f₂) :
  g₁.comp f₁ ≤ g₂.comp f₂ :=
λ x, (hg _).trans (g₂.mono $ hf _)

/-- The composition of two bundled monotone functions, a fully bundled version. -/
@[simps {fully_applied := ff}]
def compₘ : (β →ₘ γ) →ₘ (α →ₘ β) →ₘ α →ₘ γ :=
curry ⟨λ f : (β →ₘ γ) × (α →ₘ β), f.1.comp f.2, λ f₁ f₂ h, comp_mono h.1 h.2⟩

@[simp] lemma comp_id (f : α →ₘ β) : comp f id = f :=
by { ext, refl }

@[simp] lemma id_comp (f : α →ₘ β) : comp id f = f :=
by { ext, refl }

/-- Constant function bundled as a `preorder_hom`. -/
@[simps {fully_applied := ff}]
def const (α : Type*) [preorder α] {β : Type*} [preorder β] : β →ₘ α →ₘ β :=
{ to_fun := λ b, ⟨function.const α b, λ _ _ _, le_rfl⟩,
  mono' := λ b₁ b₂ h x, h }

@[simp] lemma const_comp (f : α →ₘ β) (c : γ) : (const β c).comp f = const α c := rfl

@[simp] lemma comp_const (γ : Type*) [preorder γ] (f : α →ₘ β) (c : α) :
  f.comp (const γ c) = const γ (f c) := rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`preorder_hom`. -/
@[simps] protected def prod (f : α →ₘ β) (g : α →ₘ γ) : α →ₘ (β × γ) :=
⟨λ x, (f x, g x), λ x y h, ⟨f.mono h, g.mono h⟩⟩

@[mono] lemma prod_mono {f₁ f₂ : α →ₘ β} (hf : f₁ ≤ f₂) {g₁ g₂ : α →ₘ γ} (hg : g₁ ≤ g₂) :
  f₁.prod g₁ ≤ f₂.prod g₂ :=
λ x, prod.le_def.2 ⟨hf _, hg _⟩

lemma comp_prod_comp_same (f₁ f₂ : β →ₘ γ) (g : α →ₘ β) :
  (f₁.comp g).prod (f₂.comp g) = (f₁.prod f₂).comp g :=
rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`preorder_hom`. This is a fully bundled version. -/
@[simps] def prodₘ : (α →ₘ β) →ₘ (α →ₘ γ) →ₘ α →ₘ β × γ :=
curry ⟨λ f : (α →ₘ β) × (α →ₘ γ), f.1.prod f.2, λ f₁ f₂ h, prod_mono h.1 h.2⟩

/-- Diagonal embedding of `α` into `α × α` as a `preorder_hom`. -/
@[simps] def diag : α →ₘ α × α := id.prod id

/-- Restriction of `f : α →ₘ α →ₘ β` to the diagonal. -/
@[simps {simp_rhs := tt}] def on_diag (f : α →ₘ α →ₘ β) : α →ₘ β := (curry.symm f).comp diag

@[simps] def fst : α × β →ₘ α := ⟨prod.fst, λ x y h, h.1⟩

@[simps] def snd : α × β →ₘ β := ⟨prod.snd, λ x y h, h.2⟩

@[simp] lemma fst_prod_snd : (fst : α × β →ₘ α).prod snd = id :=
by { ext ⟨x, y⟩ : 2, refl }

@[simp] lemma fst_comp_prod (f : α →ₘ β) (g : α →ₘ γ) : fst.comp (f.prod g) = f := ext _ _ rfl

@[simp] lemma snd_comp_prod (f : α →ₘ β) (g : α →ₘ γ) : snd.comp (f.prod g) = g := ext _ _ rfl

/-- Order isomorphism between the space of monotone maps to `β × γ` and the product of the spaces
of monotone maps to `β` and `γ`. -/
@[simps] def prod_iso : (α →ₘ β × γ) ≃o (α →ₘ β) × (α →ₘ γ) :=
{ to_fun := λ f, (fst.comp f, snd.comp f),
  inv_fun := λ f, f.1.prod f.2,
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl,
  map_rel_iff' := λ f g, forall_and_distrib.symm }

/-- `prod.map` of two `preorder_hom`s as a `preorder_hom`. -/
@[simps] def prod_map (f : α →ₘ β) (g : γ →ₘ δ) : α × γ →ₘ β × δ :=
⟨prod.map f g, λ x y h, ⟨f.mono h.1, g.mono h.2⟩⟩

variables {ι : Type*} {π : ι → Type*} [Π i, preorder (π i)]

/-- Evaluation of an unbundled function at a point as a `preorder_hom`. -/
@[simps {fully_applied := ff}]
def eval (i : ι) : (Π j, π j) →ₘ π i := ⟨function.eval i, function.monotone_eval i⟩

/-- The "forgetful functor" from `α →ₘ β` to `α → β` that takes the underlying function,
is monotone. -/
@[simps {fully_applied := ff}] def to_fun_hom : (α →ₘ β) →ₘ (α → β) :=
{ to_fun := λ f, f,
  mono' := λ x y h, h }

@[simps {fully_applied := ff}] def apply (x : α) : (α →ₘ β) →ₘ β :=
(eval x).comp to_fun_hom

/-- Construct a bundled monotone map `α →ₘ Π i, π i` from a family of monotone maps
`f i : α →ₘ π i`. -/
@[simps] def pi (f : Π i, α →ₘ π i) : α →ₘ (Π i, π i) :=
⟨λ x i, f i x, λ x y h i, (f i).mono h⟩

/-- Order isomorphism between bundled monotone maps `α →ₘ Π i, π i` and families of bundled monotone
maps `Π i, α →ₘ π i`. -/
@[simps] def pi_iso : (α →ₘ Π i, π i) ≃o Π i, α →ₘ π i :=
{ to_fun := λ f i, (eval i).comp f,
  inv_fun := pi,
  left_inv := λ f, by { ext x i, refl },
  right_inv := λ f, by { ext x i, refl },
  map_rel_iff' := λ f g, forall_swap }

/-- `subtype.val` as a bundled monotone function.  -/
@[simps {fully_applied := ff}]
def subtype.val (p : α → Prop) : subtype p →ₘ α :=
⟨subtype.val, λ x y h, h⟩

-- TODO[gh-6025]: make this a global instance once safe to do so
/-- There is a unique monotone map from a subsingleton to itself. -/
local attribute [instance]
def unique [subsingleton α] : unique (α →ₘ α) :=
{ default := preorder_hom.id, uniq := λ a, ext _ _ (subsingleton.elim _ _) }

lemma preorder_hom_eq_id [subsingleton α] (g : α →ₘ α) : g = preorder_hom.id :=
subsingleton.elim _ _

/-- Reinterpret a bundled monotone function as a monotone function between dual orders. -/
@[simps] protected def dual : (α →ₘ β) ≃ (order_dual α →ₘ order_dual β) :=
{ to_fun := λ f, ⟨order_dual.to_dual ∘ f ∘ order_dual.of_dual, f.mono.order_dual⟩,
  inv_fun := λ f, ⟨order_dual.of_dual ∘ f ∘ order_dual.to_dual, f.mono.order_dual⟩,
  left_inv := λ f, ext _ _ rfl,
  right_inv := λ f, ext _ _ rfl }

/-- `preorder_hom.dual` as an order isomorphism. -/
def dual_iso (α β : Type*) [preorder α] [preorder β] :
  (α →ₘ β) ≃o order_dual (order_dual α →ₘ order_dual β) :=
{ to_equiv := preorder_hom.dual.trans order_dual.to_dual,
  map_rel_iff' := λ f g, iff.rfl }

@[simps]
instance {β : Type*} [semilattice_sup β] : has_sup (α →ₘ β) :=
{ sup := λ f g, ⟨λ a, f a ⊔ g a, f.mono.sup g.mono⟩ }

instance {β : Type*} [semilattice_sup β] : semilattice_sup (α →ₘ β) :=
{ sup := has_sup.sup,
  le_sup_left := λ a b x, le_sup_left,
  le_sup_right := λ a b x, le_sup_right,
  sup_le := λ a b c h₀ h₁ x, sup_le (h₀ x) (h₁ x),
  .. (_ : partial_order (α →ₘ β)) }

@[simps]
instance {β : Type*} [semilattice_inf β] : has_inf (α →ₘ β) :=
{ inf := λ f g, ⟨λ a, f a ⊓ g a, f.mono.inf g.mono⟩ }

instance {β : Type*} [semilattice_inf β] : semilattice_inf (α →ₘ β) :=
{ inf := (⊓),
  .. (_ : partial_order (α →ₘ β)),
  .. (dual_iso α β).symm.to_galois_insertion.lift_semilattice_inf }

instance {β : Type*} [lattice β] : lattice (α →ₘ β) :=
{ .. (_ : semilattice_sup (α →ₘ β)),
  .. (_ : semilattice_inf (α →ₘ β)) }

@[simps]
instance {β : Type*} [order_bot β] : has_bot (α →ₘ β) :=
{ bot := const α ⊥ }

instance {β : Type*} [order_bot β] : order_bot (α →ₘ β) :=
{ bot := ⊥,
  bot_le := λ a x, bot_le,
  .. (_ : partial_order (α →ₘ β)) }

@[simps]
instance {β : Type*} [order_top β] : has_top (α →ₘ β) :=
{ top := const α ⊤ }

instance {β : Type*} [order_top β] : order_top (α →ₘ β) :=
{ top := ⊤,
  le_top := λ a x, le_top,
  .. (_ : partial_order (α →ₘ β)) }

instance {β : Type*} [complete_lattice β] : has_Inf (α →ₘ β) :=
{ Inf := λ s, ⟨λ x, ⨅ f ∈ s, (f : _) x, λ x y h, binfi_le_binfi (λ f _, f.mono h)⟩ }

@[simp] lemma Inf_apply {β : Type*} [complete_lattice β] (s : set (α →ₘ β)) (x : α) :
  Inf s x = ⨅ f ∈ s, (f : _) x := rfl

lemma infi_apply {ι : Sort*} {β : Type*} [complete_lattice β] (f : ι → α →ₘ β) (x : α) :
  (⨅ i, f i) x = ⨅ i, f i x :=
(Inf_apply _ _).trans infi_range

@[simp, norm_cast] lemma coe_infi {ι : Sort*} {β : Type*} [complete_lattice β] (f : ι → α →ₘ β) :
  ((⨅ i, f i : α →ₘ β) : α → β) = ⨅ i, f i :=
funext $ λ x, (infi_apply f x).trans (@_root_.infi_apply _ _ _ _ (λ i, f i) _).symm

instance {β : Type*} [complete_lattice β] : has_Sup (α →ₘ β) :=
{ Sup := λ s, ⟨λ x, ⨆ f ∈ s, (f : _) x, λ x y h, bsupr_le_bsupr (λ f _, f.mono h)⟩ }

@[simp] lemma Sup_apply {β : Type*} [complete_lattice β] (s : set (α →ₘ β)) (x : α) :
  Sup s x = ⨆ f ∈ s, (f : _) x := rfl

lemma supr_apply {ι : Sort*} {β : Type*} [complete_lattice β] (f : ι → α →ₘ β) (x : α) :
  (⨆ i, f i) x = ⨆ i, f i x :=
(Sup_apply _ _).trans supr_range

@[simp, norm_cast] lemma coe_supr {ι : Sort*} {β : Type*} [complete_lattice β] (f : ι → α →ₘ β) :
  ((⨆ i, f i : α →ₘ β) : α → β) = ⨆ i, f i :=
funext $ λ x, (supr_apply f x).trans (@_root_.supr_apply _ _ _ _ (λ i, f i) _).symm

instance {β : Type*} [complete_lattice β] : complete_lattice (α →ₘ β) :=
{ Sup := Sup,
  le_Sup := λ s f hf x, le_supr_of_le f (le_supr _ hf),
  Sup_le := λ s f hf x, bsupr_le (λ g hg, hf g hg x),
  Inf := Inf,
  le_Inf := λ s f hf x, le_binfi (λ g hg, hf g hg x),
  Inf_le := λ s f hf x, infi_le_of_le f (infi_le _ hf),
  .. (_ : lattice (α →ₘ β)),
  .. (_ : order_top (α →ₘ β)),
  .. (_ : order_bot (α →ₘ β)) }

lemma iterate_sup_le_sup_iff {α : Type*} [semilattice_sup α] (f : α →ₘ α) :
  (∀ n₁ n₂ a₁ a₂, f^[n₁ + n₂] (a₁ ⊔ a₂) ≤ (f^[n₁] a₁) ⊔ (f^[n₂] a₂)) ↔
  (∀ a₁ a₂, f (a₁ ⊔ a₂) ≤ (f a₁) ⊔ a₂) :=
begin
  split; intros h,
  { exact h 1 0, },
  { intros n₁ n₂ a₁ a₂, have h' : ∀ n a₁ a₂, f^[n] (a₁ ⊔ a₂) ≤ (f^[n] a₁) ⊔ a₂,
    { intros n, induction n with n ih; intros a₁ a₂,
      { refl, },
      { calc f^[n + 1] (a₁ ⊔ a₂) = (f^[n] (f (a₁ ⊔ a₂))) : function.iterate_succ_apply f n _
                             ... ≤ (f^[n] ((f a₁) ⊔ a₂)) : f.mono.iterate n (h a₁ a₂)
                             ... ≤ (f^[n] (f a₁)) ⊔ a₂ : ih _ _
                             ... = (f^[n + 1] a₁) ⊔ a₂ : by rw ← function.iterate_succ_apply, }, },
    calc f^[n₁ + n₂] (a₁ ⊔ a₂) = (f^[n₁] (f^[n₂] (a₁ ⊔ a₂))) : function.iterate_add_apply f n₁ n₂ _
                           ... = (f^[n₁] (f^[n₂] (a₂ ⊔ a₁))) : by rw sup_comm
                           ... ≤ (f^[n₁] ((f^[n₂] a₂) ⊔ a₁)) : f.mono.iterate n₁ (h' n₂ _ _)
                           ... = (f^[n₁] (a₁ ⊔ (f^[n₂] a₂))) : by rw sup_comm
                           ... ≤ (f^[n₁] a₁) ⊔ (f^[n₂] a₂) : h' n₁ a₁ _, },
end

end preorder_hom

namespace order_embedding

/-- Convert an `order_embedding` to a `preorder_hom`. -/
@[simps {fully_applied := ff}]
def to_preorder_hom {X Y : Type*} [preorder X] [preorder Y] (f : X ↪o Y) : X →ₘ Y :=
{ to_fun := f,
  mono' := f.monotone }

end order_embedding
section rel_hom

variables {α β : Type*} [partial_order α] [preorder β]

namespace rel_hom

variables (f : ((<) : α → α → Prop) →r ((<) : β → β → Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotonic
is weakly monotonic. -/
@[simps {fully_applied := ff}]
def to_preorder_hom : α →ₘ β :=
{ to_fun    := f,
  mono' := strict_mono.monotone (λ x y, f.map_rel), }

end rel_hom

lemma rel_embedding.to_preorder_hom_injective (f : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop)) :
  function.injective (f : ((<) : α → α → Prop) →r ((<) : β → β → Prop)).to_preorder_hom :=
λ _ _ h, f.injective h

end rel_hom
