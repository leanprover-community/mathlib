/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed_space.multilinear

/-!
# Formal multilinear series

In this file we define `formal_multilinear_series 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `cont_diff` in `mathlib`) and analytic functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/

noncomputable theory

open set fin
open_locale topological_space

variables {𝕜 𝕜' E F G : Type*}

section
variables [comm_ring 𝕜]
  [add_comm_group E] [module 𝕜 E] [topological_space E] [topological_add_group E]
  [has_continuous_const_smul 𝕜 E]
  [add_comm_group F] [module 𝕜 F] [topological_space F] [topological_add_group F]
  [has_continuous_const_smul 𝕜 F]
  [add_comm_group G] [module 𝕜 G] [topological_space G] [topological_add_group G]
  [has_continuous_const_smul 𝕜 G]


/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
@[derive add_comm_group, nolint unused_arguments]
def formal_multilinear_series (𝕜 : Type*) (E : Type*) (F : Type*)
  [ring 𝕜]
  [add_comm_group E] [module 𝕜 E] [topological_space E] [topological_add_group E]
    [has_continuous_const_smul 𝕜 E]
  [add_comm_group F] [module 𝕜 F] [topological_space F] [topological_add_group F]
    [has_continuous_const_smul 𝕜 F] :=
Π (n : ℕ), (E [×n]→L[𝕜] F)

instance : inhabited (formal_multilinear_series 𝕜 E F) := ⟨0⟩

section module
/- `derive` is not able to find the module structure, probably because Lean is confused by the
dependent types. We register it explicitly. -/

instance : module 𝕜 (formal_multilinear_series 𝕜 E F) :=
begin
  letI : Π n, module 𝕜 (continuous_multilinear_map 𝕜 (λ (i : fin n), E) F) :=
    λ n, by apply_instance,
  refine pi.module _ _ _,
end

end module

namespace formal_multilinear_series

/-- Killing the zeroth coefficient in a formal multilinear series -/
def remove_zero (p : formal_multilinear_series 𝕜 E F) : formal_multilinear_series 𝕜 E F
| 0       := 0
| (n + 1) := p (n + 1)

@[simp] lemma remove_zero_coeff_zero (p : formal_multilinear_series 𝕜 E F) :
  p.remove_zero 0 = 0 := rfl

@[simp] lemma remove_zero_coeff_succ (p : formal_multilinear_series 𝕜 E F) (n : ℕ) :
  p.remove_zero (n+1) = p (n+1) := rfl

lemma remove_zero_of_pos (p : formal_multilinear_series 𝕜 E F) {n : ℕ} (h : 0 < n) :
  p.remove_zero n = p n :=
by { rw ← nat.succ_pred_eq_of_pos h, refl }

/-- Convenience congruence lemma stating in a dependent setting that, if the arguments to a formal
multilinear series are equal, then the values are also equal. -/
lemma congr (p : formal_multilinear_series 𝕜 E F) {m n : ℕ} {v : fin m → E} {w : fin n → E}
  (h1 : m = n) (h2 : ∀ (i : ℕ) (him : i < m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩) :
  p m v = p n w :=
by { cases h1, congr' with ⟨i, hi⟩, exact h2 i hi hi }

/-- Composing each term `pₙ` in a formal multilinear series with `(u, ..., u)` where `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.comp_continuous_linear_map u`. -/
def comp_continuous_linear_map (p : formal_multilinear_series 𝕜 F G) (u : E →L[𝕜] F) :
  formal_multilinear_series 𝕜 E G :=
λ n, (p n).comp_continuous_linear_map (λ (i : fin n), u)

@[simp] lemma comp_continuous_linear_map_apply
  (p : formal_multilinear_series 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ) (v : fin n → E) :
  (p.comp_continuous_linear_map u) n v = p n (u ∘ v) := rfl

variables (𝕜) [comm_ring 𝕜'] [has_smul 𝕜 𝕜']
variables [module 𝕜' E] [has_continuous_const_smul 𝕜' E] [is_scalar_tower 𝕜 𝕜' E]
variables [module 𝕜' F] [has_continuous_const_smul 𝕜' F] [is_scalar_tower 𝕜 𝕜' F]

/-- Reinterpret a formal `𝕜'`-multilinear series as a formal `𝕜`-multilinear series. -/
@[simp] protected def restrict_scalars (p : formal_multilinear_series 𝕜' E F) :
  formal_multilinear_series 𝕜 E F :=
λ n, (p n).restrict_scalars 𝕜

end formal_multilinear_series

end

namespace formal_multilinear_series

variables [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [normed_add_comm_group G] [normed_space 𝕜 G]

variables (p : formal_multilinear_series 𝕜 E F)

/-- Forgetting the zeroth term in a formal multilinear series, and interpreting the following terms
as multilinear maps into `E →L[𝕜] F`. If `p` corresponds to the Taylor series of a function, then
`p.shift` is the Taylor series of the derivative of the function. -/
def shift : formal_multilinear_series 𝕜 E (E →L[𝕜] F) :=
λn, (p n.succ).curry_right

/-- Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`. This
corresponds to starting from a Taylor series for the derivative of a function, and building a Taylor
series for the function itself. -/
def unshift (q : formal_multilinear_series 𝕜 E (E →L[𝕜] F)) (z : F) :
  formal_multilinear_series 𝕜 E F
| 0       := (continuous_multilinear_curry_fin0 𝕜 E F).symm z
| (n + 1) := continuous_multilinear_curry_right_equiv' 𝕜 n E F (q n)

end formal_multilinear_series

namespace continuous_linear_map
variables [comm_ring 𝕜]
  [add_comm_group E] [module 𝕜 E] [topological_space E] [topological_add_group E]
  [has_continuous_const_smul 𝕜 E]
  [add_comm_group F] [module 𝕜 F] [topological_space F] [topological_add_group F]
  [has_continuous_const_smul 𝕜 F]
  [add_comm_group G] [module 𝕜 G] [topological_space G] [topological_add_group G]
  [has_continuous_const_smul 𝕜 G]

/-- Composing each term `pₙ` in a formal multilinear series with a continuous linear map `f` on the
left gives a new formal multilinear series `f.comp_formal_multilinear_series p` whose general term
is `f ∘ pₙ`. -/
def comp_formal_multilinear_series (f : F →L[𝕜] G) (p : formal_multilinear_series 𝕜 E F) :
  formal_multilinear_series 𝕜 E G :=
λ n, f.comp_continuous_multilinear_map (p n)

@[simp] lemma comp_formal_multilinear_series_apply
  (f : F →L[𝕜] G) (p : formal_multilinear_series 𝕜 E F) (n : ℕ) :
  (f.comp_formal_multilinear_series p) n = f.comp_continuous_multilinear_map (p n) :=
rfl

lemma comp_formal_multilinear_series_apply'
  (f : F →L[𝕜] G) (p : formal_multilinear_series 𝕜 E F) (n : ℕ) (v : fin n → E) :
  (f.comp_formal_multilinear_series p) n v = f (p n v) :=
rfl

end continuous_linear_map

namespace formal_multilinear_series

section order

variables [comm_ring 𝕜] {n : ℕ}
  [add_comm_group E] [module 𝕜 E] [topological_space E] [topological_add_group E]
  [has_continuous_const_smul 𝕜 E] [decidable_eq E]
  [add_comm_group F] [module 𝕜 F] [topological_space F] [topological_add_group F]
  [has_continuous_const_smul 𝕜 F] [decidable_eq F]
  {p : formal_multilinear_series 𝕜 E F}

open_locale classical

lemma eq_zero_iff : p = 0 ↔ ∀ n, p n = 0 :=
by simp only [function.funext_iff, pi.zero_apply]

lemma exists_ne_zero_of_ne_zero (hp : p ≠ 0) : ∃ n, p n ≠ 0 :=
by simpa using eq_zero_iff.not.mp hp

/-- The index of the first non-zero coefficient in `p` (or `0` if all coefficients are zero). This
  is the order of the isolated zero of an analytic function `f` at a point if `p` is the Taylor
  series of `f` at that point. -/
noncomputable def order (p : formal_multilinear_series 𝕜 E F) : ℕ :=
Inf { n | p n ≠ 0 }

@[simp] lemma order_zero : (0 : formal_multilinear_series 𝕜 E F).order = 0 := by simp [order]

lemma ne_zero_of_order_ne_zero (hp : p.order ≠ 0) : p ≠ 0 :=
λ h, by simpa [h] using hp

lemma order_eq_find (hp : ∃ n, p n ≠ 0) : p.order = nat.find hp :=
by simp [order, Inf, hp]

lemma order_eq_find' (hp : p ≠ 0) : p.order = nat.find (exists_ne_zero_of_ne_zero hp) :=
order_eq_find _

lemma order_eq_zero_iff (hp : p ≠ 0) : p.order = 0 ↔ p 0 ≠ 0 :=
begin
  have : ∃ n, p n ≠ 0 := exists_ne_zero_of_ne_zero hp,
  simp [order_eq_find this, hp]
end

lemma order_eq_zero_iff' : p.order = 0 ↔ p = 0 ∨ p 0 ≠ 0 :=
by { by_cases h : p = 0; simp [h, order_eq_zero_iff] }

lemma apply_order_ne_zero (hp : p ≠ 0) : p p.order ≠ 0 :=
let h := exists_ne_zero_of_ne_zero hp in (order_eq_find h).symm ▸ nat.find_spec h

lemma apply_order_ne_zero' (hp : p.order ≠ 0) : p p.order ≠ 0 :=
apply_order_ne_zero (ne_zero_of_order_ne_zero hp)

lemma apply_eq_zero_of_lt_order (hp : n < p.order) : p n = 0 :=
begin
  by_cases p = 0,
  { simp [h] },
  { rw [order_eq_find' h] at hp,
    simpa using nat.find_min _ hp }
end

end order

section coef

variables [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E] {s : E}
  {p : formal_multilinear_series 𝕜 𝕜 E} {f : 𝕜 → E}
  {n : ℕ} {z z₀ : 𝕜} {y : fin n → 𝕜}

open_locale big_operators

/-- The `n`th coefficient of `p` when seen as a power series. -/
def coef (p : formal_multilinear_series 𝕜 𝕜 E) (n : ℕ) : E := p n 1

@[simp] lemma apply_eq_prod_smul_coef : p n y = (∏ i, y i) • p.coef n :=
begin
  convert (p n).to_multilinear_map.map_smul_univ y 1,
  funext; simp only [pi.one_apply, algebra.id.smul_eq_mul, mul_one],
end

lemma coef_eq_zero : p.coef n = 0 ↔ p n = 0 :=
begin
  split; intro h,
  { ext; simp [h] },
  { simp [coef, h] }
end

@[simp] lemma apply_eq_pow_smul_coef : p n (λ _, z) = z ^ n • p.coef n :=
by simp

@[simp] lemma norm_apply_eq_norm_coef : ∥p n∥ = ∥coef p n∥ :=
begin
  apply le_antisymm,
  { refine (p n).op_norm_le_bound (norm_nonneg (coef p n)) (λ y, _); simp [norm_smul, mul_comm] },
  { apply le_of_le_of_eq ((p n).le_op_norm 1); simp }
end

end coef

section fslope

variables [nontrivially_normed_field 𝕜]
  [normed_add_comm_group E] [normed_space 𝕜 E]
  {p : formal_multilinear_series 𝕜 𝕜 E} {n : ℕ}

/-- The formal counterpart of `dslope`, corresponding to the expansion of `(f z - f 0) / z`. If `f`
has `p` as a power series, then `dslope f` has `fslope p` as a power series. -/
noncomputable def fslope (p : formal_multilinear_series 𝕜 𝕜 E) : formal_multilinear_series 𝕜 𝕜 E :=
  λ n, (p (n + 1)).curry_left 1

@[simp] lemma coef_fslope : p.fslope.coef n = p.coef (n + 1) :=
begin
  have : @fin.cons n (λ _, 𝕜) 1 (1 : fin n → 𝕜) = 1 := fin.cons_self_tail 1,
  simp only [fslope, coef, continuous_multilinear_map.curry_left_apply, this],
end

@[simp] lemma coef_iterate_fslope (k n : ℕ) :
  (fslope^[k] p).coef n = p.coef (n + k) :=
by induction k with k ih generalizing p; refl <|> simpa [ih]

end fslope

end formal_multilinear_series
