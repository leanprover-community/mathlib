/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import ring_theory.ideal.basic
import category_theory.preadditive.injective
import algebra.category.Module.abelian

/-!
# Injective modules

## Main definitions

* `module.injective`: an `R`-module `Q` is injective if and only if every injective `R`-linear
  map descends to a linear map to `Q`, i.e. in the following diagram, if `f` is injective then there
  is an `R`-linear map `h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
* `module.Baer`: an `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an
  `ideal R` extends to an `R`-linear map `R ⟶ Q`

## Main statements

* `module.Baer.criterion`: an `R`-module is injective if it is Baer.

-/


noncomputable theory

universes u v

variables (R : Type u) [ring R] (Q : Type (max u v)) [add_comm_group Q] [module R Q]

/--An `R`-module `Q` is injective if and only if every injective `R`-linear map descends to a linear
map to `Q`, i.e. in the following diagram, if `f` is injective then there is an `R`-linear map
`h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
-/
class module.injective : Prop :=
(out : ∀ (X Y : Type (max u v)) [add_comm_group X] [add_comm_group Y] [module R X] [module R Y]
  (f : X →ₗ[R] Y) (hf : function.injective f) (g : X →ₗ[R] Q),
  ∃ (h : Y →ₗ[R] Q), ∀ x, h (f x) = g x)

lemma module.injective_object_of_injective_module [module.injective.{u v} R Q] :
  category_theory.injective.{max u v} (⟨Q⟩ : Module.{max u v} R) :=
{ factors := λ X Y g f mn, begin
    rcases module.injective.out X Y f ((Module.mono_iff_injective f).mp mn) g with ⟨h, eq1⟩,
    exact ⟨h, linear_map.ext eq1⟩,
  end }

lemma module.injective_module_of_injective_object
  [category_theory.injective.{max u v} (⟨Q⟩ : Module.{max u v} R)] :
  module.injective.{u v} R Q :=
{ out := λ X Y ins1 ins2 ins3 ins4 f hf g, begin
    resetI,
    rcases @category_theory.injective.factors (Module R) _ ⟨Q⟩ _ ⟨X⟩ ⟨Y⟩ g f
      ((Module.mono_iff_injective _).mpr hf) with ⟨h, eq1⟩,
    refine ⟨h, λ x, by rw ← eq1; refl⟩,
  end }

lemma module.injective_iff_injective_object :
  module.injective.{u v} R Q ↔ category_theory.injective.{max u v} (⟨Q⟩ : Module.{max u v} R) :=
⟨λ h, @@module.injective_object_of_injective_module R _ Q _ _ h,
 λ h, @@module.injective_module_of_injective_object R _ Q _ _ h⟩

/--An `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an `ideal R` extends to
an `R`-linear map `R ⟶ Q`-/
def module.Baer : Prop := ∀ (I : ideal R) (g : I →ₗ[R] Q), ∃ (g' : R →ₗ[R] Q),
  ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩

namespace module.Baer

variables {R} {M N : Type (max u v)} [add_comm_group M] [add_comm_group N]
variables [module R M] [module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)
variable {Q}

/-- If we view `M` as a submodule of `N` via the injective linear map `i : M ↪ N`, then a submodule
between `M` and `N` is a submodule `N'` of `N`. To prove Baer's criterion, we need to consider
pairs of `(N', f')` such that `M ≤ N' ≤ N` and `f'` extends `f`. -/
structure extension_of extends linear_pmap R N Q :=
(le : i.range ≤ domain)
(is_extension: ∀ (m : M), f m = to_fun ⟨i m, le ⟨m, rfl⟩⟩)

section ext

variables {i f}

@[ext] lemma extension_of.ext {a b : extension_of i f}
  (domain_eq : a.domain = b.domain)
  (to_fun_eq : ∀ x, a.to_fun x = b.to_fun ⟨x, domain_eq ▸ x.2⟩) :
  a = b :=
begin
  rcases a with ⟨a, a_le, e1⟩,
  rcases b with ⟨b, b_le, e2⟩,
  dsimp only at *,
  congr,
  refine linear_pmap.ext domain_eq to_fun_eq,
end

end ext

lemma extension_of.ext_iff (a b : extension_of i f) :
  a = b ↔ ∃ (domain_eq : a.domain = b.domain),
    ∀ x, a.to_fun x = b.to_fun ⟨x, domain_eq ▸ x.2⟩ :=
⟨λ r, r ▸ ⟨rfl, λ x, congr_arg a.to_fun $ subtype.ext_val rfl⟩,
  λ ⟨h1, h2⟩, extension_of.ext h1 h2⟩

instance : has_inf (extension_of i f) :=
{ inf := λ X1 X2,
  { le := λ x hx, (begin
      refine ⟨X1.le hx, X2.le hx, _⟩,
      have := X1.is_extension hx.some,
      simp only [hx.some_spec] at this,
      erw ←this,
      have := X2.is_extension hx.some,
      simp only [hx.some_spec] at this,
      erw ←this,
    end : x ∈ X1.to_linear_pmap.eq_locus X2.to_linear_pmap),
    is_extension := λ m, (begin
      dsimp,
      change _ = X1.to_linear_pmap.to_fun.comp _ _,
      convert X1.is_extension _,
    end),
    .. (X1.to_linear_pmap ⊓ X2.to_linear_pmap)} }

instance : semilattice_inf (extension_of i f) :=
function.injective.semilattice_inf extension_of.to_linear_pmap
  (λ X Y h, extension_of.ext (by rw h) $ λ x, (linear_pmap.ext_iff.mp h).some_spec _) $ λ X Y,
    linear_pmap.ext rfl $ λ x, rfl

variables {R i f}

lemma chain_linear_pmap_of_chain_extension_of
  {c : set (extension_of i f)} (hchain : is_chain (≤) c) :
  (is_chain (≤) $ (λ x : extension_of i f, x.to_linear_pmap) '' c) :=
begin
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ neq,
  rcases hchain a_mem b_mem (λ r, neq $ r ▸ rfl) with ⟨⟨le1, le2⟩⟩ | ⟨⟨le1, le2⟩⟩,
  { left, exact ⟨le1, le2⟩, },
  { right, exact ⟨le1, le2⟩, },
end

/--The maximal element of every nonempty chain of `extension_of` f-/
def extension_of.max {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) :
  extension_of i f :=
{ le := le_trans hnonempty.some.le $ (linear_pmap.le_Sup _ $ begin
    rw set.mem_image,
    exact ⟨hnonempty.some, hnonempty.some_spec, rfl⟩,
  end).1,
  is_extension := λ m, begin
    refine eq.trans (hnonempty.some.is_extension m) _,
    dsimp,
    symmetry,
    generalize_proofs _ h0 h1,
    erw linear_pmap.Sup_apply
      (is_chain.directed_on $ chain_linear_pmap_of_chain_extension_of hchain) begin
        rw set.mem_image,
        exact ⟨hnonempty.some, hnonempty.some_spec, rfl⟩,
      end ⟨i m, h1⟩,
  end,
  ..linear_pmap.Sup (extension_of.to_linear_pmap '' c)
    (is_chain.directed_on $ chain_linear_pmap_of_chain_extension_of hchain) }

lemma extension_of.le_max {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) (a : extension_of i f) (ha : a ∈ c) :
  a ≤ extension_of.max hchain hnonempty :=
linear_pmap.le_Sup (is_chain.directed_on $ chain_linear_pmap_of_chain_extension_of hchain) begin
  rw set.mem_image,
  exact ⟨a, ha, rfl⟩,
end

lemma extension_of.aux1 : ∀ (c : set (extension_of i f)),
  is_chain has_le.le c →
  c.nonempty →
  (∃ (ub : extension_of i f), ∀ (a : extension_of i f), a ∈ c → a ≤ ub) :=
λ c hchain hnonempty,
  ⟨extension_of.max hchain hnonempty, extension_of.le_max hchain hnonempty⟩

variables (i f) [fact $ function.injective i]

instance extension_of.inhabited : inhabited (extension_of i f) :=
{ default :=
  { domain := i.range,
    to_fun :=
    { to_fun := λ x, f x.2.some,
      map_add' := λ x y, begin
        have eq1  : _ + _ = (x + y).1 := congr_arg2 (+) x.2.some_spec y.2.some_spec,
        rw [← map_add, ← (x + y).2.some_spec] at eq1,
        rw [← fact.out (function.injective i) eq1, map_add],
      end,
      map_smul' := λ r x, begin
        have eq1 : r • _ = (r • x).1 := congr_arg ((•) r) x.2.some_spec,
        rw [← linear_map.map_smul, ← (r • x).2.some_spec] at eq1,
        rw [ring_hom.id_apply, ← fact.out (function.injective i) eq1, linear_map.map_smul],
      end },
    le := le_refl _,
    is_extension := λ m, begin
      simp only [linear_map.coe_mk],
      erw fact.out (function.injective i) (⟨i m, ⟨_, rfl⟩⟩ : i.range).2.some_spec,
    end } }

/--Since every nonempty chain has a maximal element, by Zorn's lemma, there is a maximal
`extension_of hi f`-/
def extension_of_max : extension_of i f :=
(@zorn_nonempty_partial_order (extension_of i f) _ ⟨inhabited.default⟩
  (extension_of.aux1)).some

lemma extension_of_max_is_max :
  ∀ (a : extension_of i f),
    (extension_of_max i f) ≤ a → a = (extension_of_max i f) :=
(@zorn_nonempty_partial_order (extension_of i f) _ ⟨inhabited.default⟩
  (extension_of.aux1)).some_spec

variables {f}
lemma extension_of_max_adjoin.aux1
  {y : N}
  (x : (extension_of_max i f).domain ⊔ submodule.span R {y}) :
  ∃ (a : (extension_of_max i f).domain) (b : R), x.1 = a.1 + b • y :=
begin
  have mem1 : x.1 ∈ (_ : set _) := x.2,
  rw submodule.coe_sup at mem1,
  rcases mem1 with ⟨a, b, a_mem, (b_mem : b ∈ (submodule.span R _ : submodule R N)), eq1⟩,
  rw submodule.mem_span_singleton at b_mem,
  rcases b_mem with ⟨z, eq2⟩,
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩,
end

/--If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `fst` pick an arbitrary such `m`.-/
def extension_of_max_adjoin.fst
  {y : N} (x : (extension_of_max i f).domain ⊔ submodule.span R {y}) :
  (extension_of_max i f).domain :=
(extension_of_max_adjoin.aux1 i x).some

/--If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `snd` pick an arbitrary such `r`.-/
def extension_of_max_adjoin.snd
  {y : N} (x : (extension_of_max i f).domain ⊔ submodule.span R {y}) : R :=
(extension_of_max_adjoin.aux1 i x).some_spec.some

lemma extension_of_max_adjoin.eqn
  {y : N} (x : (extension_of_max i f).domain ⊔ submodule.span R {y}) :
  x.1 = (extension_of_max_adjoin.fst i x).1 + (extension_of_max_adjoin.snd i x) • y :=
(extension_of_max_adjoin.aux1 i x).some_spec.some_spec

variables (f)
/--the ideal `I = {r | r • y ∈ N}`-/
def extension_of_max_adjoin.ideal (y : N) :
  ideal R :=
(extension_of_max i f).domain.comap (linear_map.id.smul_right y)

/--A linear map `I ⟶ Q` by `x ↦ f' (x • y)` where `f'` is the maximal extension-/
def extension_of_max_adjoin.ideal_to (y : N) :
  extension_of_max_adjoin.ideal i f y →ₗ[R] Q :=
{ to_fun := λ z, (extension_of_max i f).to_fun ⟨z.1 • y, z.2⟩,
  map_add' := λ z1 z2, by rw [← map_add]; congr; erw add_smul,
  map_smul' := λ z1 z2, begin
    rw [ring_hom.id_apply, ← linear_map.map_smul],
    exact congr_arg _ (subtype.ext_val (mul_smul _ _ _)),
  end }

/-- Since we assumed `Q` being Baer, the linear map `x ↦ f' (x • y) : I ⟶ Q` extends to `R ⟶ Q`,
call this extended map `φ`-/
def extension_of_max_adjoin.extend_ideal_to (h : module.Baer R Q) (y : N) : R →ₗ[R] Q :=
(h (extension_of_max_adjoin.ideal i f y) (extension_of_max_adjoin.ideal_to i f y)).some

lemma extension_of_max_adjoin.extend_ideal_to_is_extension (h : module.Baer R Q) (y : N) :
  ∀ (x : R) (mem : x ∈ extension_of_max_adjoin.ideal i f y),
  extension_of_max_adjoin.extend_ideal_to i f h y x =
  extension_of_max_adjoin.ideal_to i f y ⟨x, mem⟩ :=
(h (extension_of_max_adjoin.ideal i f y) (extension_of_max_adjoin.ideal_to i f y)).some_spec

lemma extension_of_max_adjoin.extend_ideal_to_wd' (h : module.Baer R Q) {y : N} (r : R)
  (eq1 : r • y = 0) :
  extension_of_max_adjoin.extend_ideal_to i f h y r = 0 :=
begin
  rw extension_of_max_adjoin.extend_ideal_to_is_extension i f h y r
    (by rw eq1; exact submodule.zero_mem _ : r • y ∈ _),
  unfold extension_of_max_adjoin.ideal_to,
  simp only [linear_map.coe_mk, eq1],
  convert map_zero _,
end

lemma extension_of_max_adjoin.extend_ideal_to_wd (h : module.Baer R Q) {y : N} (r r' : R)
  (eq1 : r • y = r' • y) :
  extension_of_max_adjoin.extend_ideal_to i f h y r =
  extension_of_max_adjoin.extend_ideal_to i f h y r' :=
begin
  rw [← sub_eq_zero, ← map_sub],
  convert extension_of_max_adjoin.extend_ideal_to_wd' i f h (r - r') _,
  rw [sub_smul, sub_eq_zero, eq1],
end

lemma extension_of_max_adjoin.extend_ideal_to_eq (h : module.Baer R Q) {y : N} (r : R)
  (hr : r • y ∈ (extension_of_max i f).domain) :
  extension_of_max_adjoin.extend_ideal_to i f h y r =
  (extension_of_max i f).to_fun ⟨r • y, hr⟩ :=
by rw extension_of_max_adjoin.extend_ideal_to_is_extension i f h _ _ hr; refl

/--We can finally define a linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r`
-/
def extension_of_max_adjoin.extension_to_fun (h : module.Baer R Q)
  {y : N} :
  (extension_of_max i f).domain ⊔ submodule.span R {y} → Q :=
λ x, (extension_of_max i f).to_fun (extension_of_max_adjoin.fst i x) +
  extension_of_max_adjoin.extend_ideal_to i f h y (extension_of_max_adjoin.snd i x)

lemma extension_of_max_adjoin.extension_to_fun_wd (h : module.Baer R Q)
  {y : N} (x : (extension_of_max i f).domain ⊔ submodule.span R {y})
  (a : (extension_of_max i f).domain) (r : R)
  (eq1 : x.1 = a.1 + r • y) :
  extension_of_max_adjoin.extension_to_fun i f h x =
  (extension_of_max i f).to_fun a +
  extension_of_max_adjoin.extend_ideal_to i f h y r :=
begin
  have eq2 := eq1,
  rw [extension_of_max_adjoin.eqn, ← sub_eq_zero,
    show ∀ (a b c d : N), (a + b) - (c + d) = (a - c) - (d - b), from λ _ _ _ _, by abel,
    sub_eq_zero, ← sub_smul] at eq2,
  have eq3 := extension_of_max_adjoin.extend_ideal_to_eq i f h (r - extension_of_max_adjoin.snd i x)
    (by rw ← eq2; exact submodule.sub_mem _ (extension_of_max_adjoin.fst i x).2 a.2),
  simp only [map_sub, sub_smul, sub_eq_iff_eq_add] at eq3,
  unfold extension_of_max_adjoin.extension_to_fun,
  rw [eq3, ← add_assoc],
  congr' 1,
  rw [← map_add, show ∀ (a b : (extension_of_max i f).domain), a + b = ⟨a.1 + b.1, _⟩,
    from λ _ _, rfl],
  have eq4 := extension_of_max_adjoin.eqn i x,
  rw eq1 at eq4,
  simp only [eq4, add_sub, add_sub_cancel],
  exact congr_arg _ (subtype.ext_val rfl),
end

/--The linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r` is an extension of `f`-/
def extension_of_max_adjoin (h : module.Baer R Q) (y : N) :
  extension_of i f :=
{ domain := (extension_of_max i f).domain ⊔ submodule.span R {y},
  le := le_trans (extension_of_max i f).le le_sup_left,
  to_fun :=
    { to_fun := extension_of_max_adjoin.extension_to_fun i f h,
      map_add' := λ a b, begin
        have eq1 : (a + b).val =
          ((extension_of_max_adjoin.fst i a) + (extension_of_max_adjoin.fst i b)).1 +
          (extension_of_max_adjoin.snd i a + extension_of_max_adjoin.snd i b) • y,
        { change a.1 + b.1 = _ + _,
          rw [extension_of_max_adjoin.eqn, extension_of_max_adjoin.eqn, add_smul],
          abel, },
        rw [extension_of_max_adjoin.extension_to_fun_wd i f h (a + b) _ _ eq1, map_add, map_add],
        unfold extension_of_max_adjoin.extension_to_fun,
        abel,
      end,
      map_smul' := λ r a, begin
        rw [ring_hom.id_apply],
        have eq1 : (r • a).1 = (r • extension_of_max_adjoin.fst i a).1 +
          (r • extension_of_max_adjoin.snd i a) • y,
        { change r • a.1 = _,
          rw [extension_of_max_adjoin.eqn, smul_add, smul_eq_mul, mul_smul],
          refl, },
        rw [extension_of_max_adjoin.extension_to_fun_wd i f h (r • a) _ _ eq1,
          linear_map.map_smul, linear_map.map_smul, ← smul_add],
        congr',
      end },
  is_extension := λ m, begin
    simp only [linear_map.coe_mk],
    rw [(extension_of_max i f).is_extension, extension_of_max_adjoin.extension_to_fun_wd i f h
      _ ⟨i m, _⟩ 0 _, map_zero, add_zero],
    simp,
  end }

lemma extension_of_max_le (h : module.Baer R Q) {y : N} :
  extension_of_max i f ≤ extension_of_max_adjoin i f h y :=
⟨le_sup_left, λ x x' EQ, begin
  symmetry,
  change extension_of_max_adjoin.extension_to_fun i f h _ = _,
  rw [extension_of_max_adjoin.extension_to_fun_wd i f h x' x 0, map_zero, add_zero],
  refl,

  rw [zero_smul, add_zero],
  exact EQ.symm,
end⟩

lemma extension_of_max_eq (h : module.Baer R Q) (y : N) :
  extension_of_max_adjoin i f h y = extension_of_max i f :=
extension_of_max_is_max i f _ (extension_of_max_le i f h)

lemma extension_of_max_to_submodule_eq_top (h : module.Baer R Q) :
  (extension_of_max i f).domain = ⊤ :=
begin
  by_contra rid,
  rcases show ∃ (y : N), y ∉ (extension_of_max i f).domain,
    by contrapose! rid; ext; exact ⟨λ _, trivial, λ _, rid _⟩ with ⟨y, hy⟩,
  apply hy,
  erw [← extension_of_max_eq i f h y, submodule.mem_sup],
  exact ⟨0, submodule.zero_mem _, y, submodule.mem_span_singleton_self _, zero_add _⟩,
end

/--**Baer's criterion** for injective module : a Baer module is an injective module, i.e. if every
linear map from an ideal can be extended, then the module is injective.-/
protected theorem injective (h : module.Baer R Q) :
  module.injective R Q :=
{ out := λ X Y ins1 ins2 ins3 ins4 i hi f, begin
  haveI : fact (function.injective i) := ⟨hi⟩,
  resetI,
  have eq1 := extension_of_max_to_submodule_eq_top i f h,
  set f'' : (⊤ : submodule R Y) →ₗ[R] Q :=
  { to_fun := λ y, (extension_of_max i f).to_fun ⟨y.1, eq1.symm ▸ y.2⟩,
    map_add' := λ x y, by { dsimp, erw ← map_add,  congr' 1 },
    map_smul' := λ r x, by { dsimp, erw ← linear_map.map_smul, congr' 1 } } with f''_eq,
  use
  { to_fun := λ y, f'' ⟨y, trivial⟩,
    map_add' := λ x y, by rw ← map_add; congr',
    map_smul' := λ r x, by rw [ring_hom.id_apply, ← linear_map.map_smul]; refl },
  intros x,
  exact ((extension_of_max i f).is_extension x).symm,
end }

end module.Baer
