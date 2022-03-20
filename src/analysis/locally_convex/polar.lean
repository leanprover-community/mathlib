import analysis.normed.normed_field
import analysis.convex.basic

variables {𝕜 E F : Type*}

section normed_ring

variables [normed_comm_ring 𝕜] [add_comm_monoid E] [add_comm_monoid F]
variables [module 𝕜 E] [module 𝕜 F]
variables (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

def polar (M : set E) : set F :=
  {y : F | ∀ (x ∈ M), ∥B x y∥ ≤ 1 }

lemma polar_mem_iff (M : set E) (y : F) :
  y ∈ polar B M ↔ ∀ (x ∈ M), ∥B x y∥ ≤ 1 := iff.rfl

lemma polar_mem (M : set E) (y : F) (hy : y ∈ polar B M) :
  ∀ (x ∈ M), ∥B x y∥ ≤ 1 := hy

@[simp] lemma zero_mem_polar (s : set E) :
  (0 : F) ∈ polar B s :=
λ _ _, by simp only [map_zero, norm_zero, zero_le_one]

lemma polar_eq_Inter {s : set E} :
  polar B s = ⋂ x ∈ s, {y : F | ∥B x y∥ ≤ 1} :=
by { ext, simp only [polar_mem_iff, set.mem_Inter, set.mem_set_of_eq] }

lemma polar_gc : galois_connection (order_dual.to_dual ∘ polar B)
  (polar B.flip ∘ order_dual.of_dual) :=
λ s t, ⟨λ h _ hx _ hy, h hy _ hx, λ h _ hx _ hy, h hy _ hx⟩

@[simp] lemma polar_Union {ι} {s : ι → set E} :
  polar B (⋃ i, s i) = ⋂ i, polar B (s i) :=
(polar_gc B).l_supr

@[simp] lemma polar_union {s t : set E} : polar B (s ∪ t) = polar B s ∩ polar B t :=
(polar_gc B).l_sup

lemma polar_antitone : antitone (polar B : set E → set F) := (polar_gc B).monotone_l

@[simp] lemma polar_empty : polar B ∅ = set.univ := (polar_gc B).l_bot

@[simp] lemma polar_zero : polar B ({0} : set E) = set.univ :=
begin
  sorry,
end

end normed_ring

section nondiscrete_normed_field

variables [nondiscrete_normed_field 𝕜] [add_comm_monoid E] [add_comm_monoid F]
variables [module 𝕜 E] [module 𝕜 F]
variables (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

def separating_right (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Prop :=
∀ y : F, (∀ x : E, B x y = 0) → y = 0

lemma polar_univ (h : separating_right B) :
  polar B set.univ = {(0 : F)} :=
begin
  rw set.eq_singleton_iff_unique_mem,
  refine ⟨by simp only [zero_mem_polar], λ y hy, h _ (λ x, _)⟩,
  refine norm_le_zero_iff.mp (le_of_forall_le_of_dense $ λ ε hε, _),
  rcases normed_field.exists_norm_lt 𝕜 hε with ⟨c, hc, hcε⟩,
  calc ∥B x y∥ = ∥c∥ * ∥B (c⁻¹ • x) y∥ :
    by rw [B.map_smul, linear_map.smul_apply, algebra.id.smul_eq_mul, norm_mul, norm_inv,
      mul_inv_cancel_left₀ hc.ne']
  ... ≤ ε * 1 : mul_le_mul hcε.le (hy _ trivial) (norm_nonneg _) hε.le
  ... = ε : mul_one _
end

end nondiscrete_normed_field
