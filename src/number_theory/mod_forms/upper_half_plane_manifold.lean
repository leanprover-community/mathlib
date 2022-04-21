import analysis.complex.upper_half_plane
import geometry.manifold.mfderiv
import number_theory.mod_forms.holomorphic_functions

local notation `ℍ`:=upper_half_plane



noncomputable theory

open_locale classical topological_space manifold
/--The upper half space as a subset of `ℂ` which is convenient sometimes.-/
def upper_half_space := {z : ℂ | 0 <  z.im}

lemma hcoe : upper_half_space = coe '' (set.univ : set upper_half_plane) :=
begin
simp, refl,
end

lemma upper_half_plane_is_open: is_open upper_half_space  :=
begin
  have : upper_half_space = complex.im⁻¹' set.Ioi 0 :=
    set.ext (λ z, iff.intro (λ hz, set.mem_preimage.mp hz) $ λ hz, hz),
  exact is_open.preimage complex.continuous_im is_open_Ioi,
end

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane


variable (f : ℍ' → ℂ)

instance : inhabited ℍ' :=
begin
let  x := (⟨complex.I, by {simp,} ⟩ : ℍ),
apply inhabited.mk x,
end

lemma ext_chart (z : ℍ') : (extend_by_zero f) z = (f ∘ ⇑((chart_at ℂ z).symm)) z :=
begin
simp_rw chart_at,
simp_rw extend_by_zero,
simp,
have :=  (local_homeomorph.subtype_restr_coe  (local_homeomorph.refl ℂ) ℍ').symm,
congr,
simp_rw local_homeomorph.subtype_restr,
simp,
have hf:= topological_space.opens.local_homeomorph_subtype_coe_coe ℍ',
simp_rw ← hf,
apply symm,
apply local_homeomorph.left_inv,
simp only [topological_space.opens.local_homeomorph_subtype_coe_source],
end

lemma holo_to_mdiff (f : ℍ' → ℂ) (hf : is_holomorphic_on f ) : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
begin
rw ← is_holomorphic_on_iff_differentiable_on at hf,
simp_rw mdifferentiable,
 simp only [mdifferentiable_at, differentiable_within_at_univ] with mfld_simps,
intro x,
split,
have hc:= hf.continuous_on,
simp at hc,
rw continuous_on_iff_continuous_restrict at hc,
have hcc:= hc.continuous_at,
convert hcc,
funext y,
simp_rw extend_by_zero,
simp_rw set.restrict,
simp [y.2],
rw ← dite_eq_ite,
rw dif_pos,
apply y.2,
have hfx := hf x x.2,
have hH: ℍ'.1 ∈ 𝓝 (((chart_at ℂ x) x)), by {simp_rw metric.mem_nhds_iff, simp,
simp_rw chart_at, simp, have:= upper_half_plane_is_open, rw metric.is_open_iff at this,
have ht:= this x.1 x.2, simp at ht, exact ht,},
apply differentiable_on.differentiable_at _ hH,
apply differentiable_on.congr hf,
intros y hy,
have HH:= ext_chart f (⟨y,hy⟩ : ℍ'),
simp at HH,
simp only [function.comp_app],
simp_rw HH,
congr,
end

lemma mdiff_to_holo (f : ℍ' → ℂ) (hf :  (mdifferentiable 𝓘(ℂ) 𝓘(ℂ) f) ) : is_holomorphic_on f :=
begin
rw ← is_holomorphic_on_iff_differentiable_on,
simp_rw mdifferentiable at hf,
simp only [mdifferentiable_at, differentiable_within_at_univ] with mfld_simps at hf,
simp_rw differentiable_on,
intros x hx,
have hff:= (hf ⟨x, hx⟩).2,
apply differentiable_at.differentiable_within_at,
simp_rw differentiable_at at *,
obtain ⟨g, hg⟩:= hff,
use g,
apply has_fderiv_at.congr_of_eventually_eq hg,
simp_rw filter.eventually_eq_iff_exists_mem,
use ℍ',
split,
simp_rw metric.mem_nhds_iff, simp,
simp_rw chart_at, simp,
have:= upper_half_plane_is_open,
rw metric.is_open_iff at this,
have ht:= this x hx,
simp at ht,
exact ht,
simp_rw set.eq_on,
intros y hy,
apply ext_chart f (⟨y,hy⟩ : ℍ'),
end

lemma mdiff_iff_holo (f : ℍ' → ℂ) : (mdifferentiable 𝓘(ℂ) 𝓘(ℂ) f) ↔ is_holomorphic_on f :=
begin
split,
apply mdiff_to_holo f,
apply holo_to_mdiff f,
end
