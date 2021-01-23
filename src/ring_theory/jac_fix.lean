import ring_theory.jacobson

namespace ideal

section comm_ring
open polynomial localization_map ideal

variables {R : Type*} [comm_ring R] {I : ideal (polynomial R)}

lemma factor :
  (map_ring_hom (((quotient.mk I).comp C).range_restrict)).ker ≤ I :=
begin
  refine λ f hf, polynomial_mem_ideal_of_coeff_mem_ideal I f (λ n, _),
  replace hf := congr_arg (λ (g : polynomial (((quotient.mk I).comp C).range)), g.coeff n) hf,
  change (polynomial.map ((quotient.mk I).comp C).range_restrict f).coeff n = 0 at hf,
  rw [coeff_map, subtype.ext_iff] at hf,
  rwa [mem_comap, ← quotient.eq_zero_iff_mem, ← ring_hom.comp_apply],
end

theorem is_jacobson_polynomial_of_is_jacobson (jR : is_jacobson R) :
  is_jacobson (polynomial R) :=
begin
  rw is_jacobson_iff_prime_eq,
  intros I hI,
  let R' : subring I.quotient := ((quotient.mk I).comp C).range,
  let i : R →+* R' := ((quotient.mk I).comp C).range_restrict,
  have hi : function.surjective (i : R → R') := ((quotient.mk I).comp C).surjective_onto_range,
  have hi' : (polynomial.map_ring_hom i : polynomial R →+* polynomial R').ker ≤ I :=
    @factor R _ I,
  let j : polynomial R →+* polynomial R' := @polynomial.map_ring_hom R R' _ _ i,
  haveI : (ideal.map (map_ring_hom i) I).is_prime := begin
    apply map_is_prime_of_surjective _ _,
    apply (polynomial.map_surjective i hi),
    exact hI,
    exact hi',
  end,
  suffices : (I.map (polynomial.map_ring_hom i)).jacobson = (I.map (polynomial.map_ring_hom i)),
  { replace this := congr_arg (comap (polynomial.map_ring_hom i)) this,
    rw [← map_jacobson_of_surjective _ hi',
      comap_map_of_surjective _ _, comap_map_of_surjective _ _] at this,
    refine le_antisymm (le_trans (le_sup_left_of_le le_rfl)
      (le_trans (le_of_eq this) (sup_le le_rfl hi'))) le_jacobson,
    all_goals {exact polynomial.map_surjective i hi} },
  exact @polynomial.is_jacobson_polynomial_of_domain R' _ (is_jacobson_of_surjective ⟨i, hi⟩)
    (ideal.map (map_ring_hom i) I) _ (eq_zero_of_polynomial_mem_map_range I),
end

theorem is_jacobson_polynomial_iff_is_jacobson :
  is_jacobson (polynomial R) ↔ is_jacobson R :=
begin
  refine ⟨_, is_jacobson_polynomial_of_is_jacobson⟩,
  introI H,
  exact is_jacobson_of_surjective ⟨eval₂_ring_hom (ring_hom.id _) 1, λ x,
    ⟨C x, by simp only [coe_eval₂_ring_hom, ring_hom.id_apply, eval₂_C]⟩⟩,
end

instance [is_jacobson R] : is_jacobson (polynomial R) :=
is_jacobson_polynomial_iff_is_jacobson.mpr ‹is_jacobson R›

end comm_ring

section integral_domain
variables {R : Type*} [integral_domain R] [is_jacobson R]
variables (I : ideal (polynomial R))
open polynomial ideal

lemma passo [hI : I.is_maximal] :
  let I' : ideal R := I.comap C,
      i : R →+* I'.quotient := quotient.mk I',
      f : polynomial R →+* polynomial I'.quotient := map_ring_hom (quotient.mk I'),
      J : ideal (polynomial I'.quotient) := map f I
  in function.surjective ⇑f → I = comap f J :=
begin
  intros I' i f J hf,
  rw comap_map_of_surjective f hf,
  refine le_antisymm (le_sup_left_of_le le_rfl) (sup_le le_rfl _),
  refine λ p hp, polynomial_mem_ideal_of_coeff_mem_ideal I p (λ n, _),
  rw ← quotient.eq_zero_iff_mem,
  rw [mem_comap, ideal.mem_bot, polynomial.ext_iff] at hp,
  simp_rw coeff_zero at hp,
  simpa only [coeff_map, coe_map_ring_hom] using hp n,
end

/-- If `R` is a jacobson field, and `P` is a maximal ideal of `polynomial R`,
  then `R → (polynomial R)/P` is an integral map. -/
lemma quotient_mk_comp_C_is_integral_of_jacobson
 [hI : I.is_maximal] :
  ((quotient.mk I).comp C : R →+* I.quotient).is_integral :=
begin
  let I' : ideal R := I.comap C,
  haveI : I'.is_prime := @comap_is_prime R _ _ _ C I (is_maximal.is_prime hI),
  let i : R →+* I'.quotient := quotient.mk I',
  let f : polynomial R →+* polynomial I'.quotient := polynomial.map_ring_hom (quotient.mk I'),
  have hf : function.surjective f := map_surjective i quotient.mk_surjective,
--  let J : ideal (polynomial I'.quotient) := I.map f,
  have hIJ : I = (@map (polynomial R) (polynomial I'.quotient) _ _ f I).comap f := I.passo hf,
  haveI : (@map (polynomial R) (polynomial I'.quotient) _ _ f I).is_maximal :=
    or.rec_on (map_eq_top_or_is_maximal_of_surjective f hf hI)
    (λ h, absurd (trans (h ▸ hIJ : I = comap f ⊤) comap_top : I = ⊤) hI.1) id,
  let i' : I.quotient →+* (I.map f).quotient := quotient_map (I.map f) f le_comap_map,
  have hi' : function.injective i' := quotient_map_injective' (le_of_eq hIJ.symm),
  let ϕ : R →+* I.quotient := (quotient.mk I).comp C,
  let ϕ' : I'.quotient →+* (@map (polynomial R) (polynomial I'.quotient) _ _ f I).quotient :=
    (quotient.mk (@map (polynomial R) (polynomial I'.quotient) _ _ f I)).comp C,
  refine ring_hom.is_integral_tower_bot_of_is_integral ϕ _ hi' _,
  refine (ring_hom.ext (λ _, by simp) : ϕ'.comp i = i'.comp ϕ) ▸ ring_hom.is_integral_trans i ϕ'
    (i.is_integral_of_surjective quotient.mk_surjective)
    (ideal.polynomial.quotient_mk_comp_C_is_integral_of_jacobson' (I.map f) (λ x hx, _)),
  obtain ⟨z, rfl⟩ := quotient.mk_surjective x,
  rwa [quotient.eq_zero_iff_mem, mem_comap, hIJ, mem_comap, coe_map_ring_hom, map_C],
end

lemma comp_C_integral_of_surjective_of_jacobson
  {S : Type*} [field S] (f : (polynomial R) →+* S) (hf : function.surjective f) :
  (f.comp C).is_integral :=
begin
  haveI : (f.ker).is_maximal := @comap_is_maximal_of_surjective _ _ _ _ f ⊥ hf bot_is_maximal,
  let g : f.ker.quotient →+* S := ideal.quotient.lift f.ker f (λ _ h, h),
  have hfg : (g.comp (quotient.mk f.ker)) = f := quotient.lift_comp_mk f.ker f _,
  rw [← hfg, ring_hom.comp_assoc],
  refine ring_hom.is_integral_trans _ g (quotient_mk_comp_C_is_integral_of_jacobson f.ker)
    (g.is_integral_of_surjective (quotient.lift_surjective f.ker f _ hf)),
end

lemma is_maximal_comap_C_of_is_jacobson
  (P : ideal (polynomial R)) [hP : P.is_maximal] : (P.comap (C : R →+* polynomial R)).is_maximal :=
begin
  have := is_maximal_comap_of_is_integral_of_is_maximal' _
    (quotient_mk_comp_C_is_integral_of_jacobson P) ⊥ (by rwa bot_quotient_is_maximal_iff),
  rwa [← comap_comap, ← ring_hom.ker_eq_comap_bot, mk_ker] at this,
end
end integral_domain

namespace mv_polynomial
open mv_polynomial
section comm_ring

variables {R : Type*} [comm_ring R] [H : is_jacobson R]

lemma is_jacobson_mv_polynomial_fin :
  ∀ (n : ℕ), is_jacobson (mv_polynomial (fin n) R)
| 0 := ((is_jacobson_iso ((ring_equiv_of_equiv R
  (equiv.equiv_pempty $ fin.elim0)).trans (pempty_ring_equiv R))).mpr H)
| (n+1) := (is_jacobson_iso (fin_succ_equiv R n)).2
  (is_jacobson_polynomial_iff_is_jacobson.2 (is_jacobson_mv_polynomial_fin n))

/-- General form of the nullstellensatz for jacobson rings, since in a jacobson ring we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are always jacobson,
  and in that special case this is (most of) the classical nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is then `I.radical` -/
instance {ι : Type*} [fintype ι] [is_jacobson R] : is_jacobson (mv_polynomial ι R) :=
begin
  haveI := classical.dec_eq ι,
  obtain ⟨e⟩ := fintype.equiv_fin ι,
  rw is_jacobson_iso (ring_equiv_of_equiv R e),
  exact is_jacobson_mv_polynomial_fin _
end

end comm_ring

section integral_domain
open function
variables {R : Type*} [integral_domain R] [is_jacobson R]
variables {n : ℕ} (P : ideal (mv_polynomial (fin n) R)) [hP : P.is_maximal]

noncomputable def ϕ1 (n : ℕ) : R →+* mv_polynomial (fin n) R := mv_polynomial.C
noncomputable def ϕ2 (n : ℕ) : (mv_polynomial (fin n) R) →+* polynomial (mv_polynomial (fin n) R) :=
  polynomial.C
noncomputable def P3 (P : ideal (mv_polynomial (fin n.succ) R)) :
  ideal (polynomial (mv_polynomial (fin n) R)) :=
      P.comap ((fin_succ_equiv R n).symm.to_ring_hom)

--noncomputable def ϕ3 (n : ℕ) :
--  polynomial (mv_polynomial (fin n) R) →+* mv_polynomial (fin (n.succ)) R :=
--    (fin_succ_equiv R n).symm.to_ring_hom
--noncomputable def P2 (P : ideal (mv_polynomial (fin n.succ) R)) : ideal (mv_polynomial (fin n) R) :=
--      (@comap (polynomial (mv_polynomial (fin n) R)) (mv_polynomial (fin (n + 1)) R)
--        _ _ (ϕ3 n) P).comap (ϕ2 n)


lemma quotient_mk_comp_C_is_integral_of_jacobson_zero
  (P : ideal (mv_polynomial (fin 0) R)) :
  ((quotient.mk P).comp C).is_integral :=
ring_hom.is_integral_of_surjective _ ( quotient.mk_surjective.comp C_surjective_fin_0)

lemma quotient_mk_comp_C_is_integral_of_jacobson_zero_induction
  (IH : ∀ (P : ideal (mv_polynomial (fin n) R)), ((quotient.mk P).comp C).is_integral)
  (P : ideal (mv_polynomial (fin n.succ) R)) :
  ((quotient.mk P).comp C).is_integral :=
begin
    --let ϕ1 : R →+* mv_polynomial (fin n) R := mv_polynomial.C,
    --let ϕ2 : (mv_polynomial (fin n) R) →+* polynomial (mv_polynomial (fin n) R) := polynomial.C,
    let ϕ3 := (fin_succ_equiv R n).symm.to_ring_hom,
    let ϕ : R →+* (mv_polynomial (fin (n+1)) R) :=
      ((fin_succ_equiv R n).symm.to_ring_hom).comp ((ϕ2 n).comp (ϕ1 n)),
--    let P3 : ideal (polynomial (mv_polynomial (fin n) R)) :=
--      P.comap ((fin_succ_equiv R n).symm.to_ring_hom),
    let P2 : ideal (mv_polynomial (fin n) R) :=
      (@comap (polynomial (mv_polynomial (fin n) R)) (mv_polynomial (fin (n + 1)) R)
        _ _ (ϕ3) P).comap (ϕ2 n),
    let P1 : ideal R := (P2).comap (ϕ1 n),
    have : (P.comap (ϕ3)).is_maximal,
    apply comap_is_maximal_of_surjective (ϕ3) (fin_succ_equiv R n).symm.surjective,
sorry,
    haveI : P2.is_maximal := polynomial.is_maximal_comap_C_of_is_jacobson P3,
    let φ3 : P3.quotient →+* P.quotient := quotient_map P ϕ3 le_rfl,
    let φ2 : P2.quotient →+* P3.quotient := quotient_map P3 ϕ2 le_rfl,
    let φ1 : P1.quotient →+* P2.quotient := quotient_map P2 ϕ1 le_rfl,
    let φ : P1.quotient →+* P.quotient := φ3.comp (φ2.comp φ1),
    have hφ3 : φ3.is_integral := φ3.is_integral_of_surjective
      (quotient_map_surjective (fin_succ_equiv R n).symm.surjective),
    have hφ2 : φ2.is_integral,
    { rw is_integral_quotient_map_iff ϕ2,
      refine polynomial.quotient_mk_comp_C_is_integral_of_jacobson P3 } ,
    have hφ1 : φ1.is_integral,
    { rw is_integral_quotient_map_iff ϕ1,
      refine IH P2 },
    have hφ : φ.is_integral := ring_hom.is_integral_trans (φ2.comp φ1) φ3
      (ring_hom.is_integral_trans φ1 φ2 hφ1 hφ2) hφ3,
    have : (quotient.mk P).comp ϕ = φ.comp (quotient.mk P1),
    by rw [ring_hom.comp_assoc, ring_hom.comp_assoc, quotient_map_comp_mk, ← ring_hom.comp_assoc ϕ1,
      quotient_map_comp_mk, ← ring_hom.comp_assoc, ← ring_hom.comp_assoc, ← ring_hom.comp_assoc,
      ← ring_hom.comp_assoc, quotient_map_comp_mk],
    rw [← fin_succ_equiv_comp_C_eq_C n, this],
    refine ring_hom.is_integral_trans (quotient.mk P1) φ _ hφ,
    exact (quotient.mk P1).is_integral_of_surjective (quotient.mk_surjective)
end

--#exit
lemma quotient_mk_comp_C_is_integral_of_jacobson :
  ((quotient.mk P).comp mv_polynomial.C : R →+* P.quotient).is_integral :=
begin
  unfreezingI {induction n with n IH},
  { exact quotient_mk_comp_C_is_integral_of_jacobson_zero P
  --have := (ring_equiv_of_equiv R (equiv.equiv_pempty $ fin.elim0)).trans (pempty_ring_equiv R),
  --  refine ring_hom.is_integral_of_surjective _ (function.surjective.comp quotient.mk_surjective _),
  --  exact C_surjective_fin_0
  },
  { --extract_goal,
--    let ϕ1 : R →+* mv_polynomial (fin n) R := mv_polynomial.C,
--    let ϕ2 : (mv_polynomial (fin n) R) →+* polynomial (mv_polynomial (fin n) R) := polynomial.C,
    let ϕ : R →+* (mv_polynomial (fin (n+1)) R) :=
      ((fin_succ_equiv R n).symm.to_ring_hom).comp ((polynomial.C).comp (mv_polynomial.C)),
--    let P3 : ideal (polynomial (mv_polynomial (fin n) R)) :=
--      P.comap ((fin_succ_equiv R n).symm.to_ring_hom),
    let ϕ3 := (fin_succ_equiv R n).symm.to_ring_hom,
    let P2 : ideal (mv_polynomial (fin n) R) :=(@comap (polynomial (mv_polynomial (fin n) R)) (mv_polynomial (fin (n + 1)) R)
        _ _ (ϕ3) P).comap (polynomial.C),
--      (@comap (polynomial (mv_polynomial (fin n) R)) (mv_polynomial (fin (n + 1)) R)
--        _ _ (ϕ3) P).comap (ϕ2),
    let P1 : ideal R := P2.comap (mv_polynomial.C),
    haveI : (P.comap (ϕ3)).is_maximal :=
      comap_is_maximal_of_surjective (ϕ3) (fin_succ_equiv R n).symm.surjective,
sorry },
    haveI : P2.is_maximal := polynomial.is_maximal_comap_C_of_is_jacobson P3,
    let φ3 : P3.quotient →+* P.quotient := quotient_map P ϕ3 le_rfl,
    let φ2 : P2.quotient →+* P3.quotient := quotient_map P3 ϕ2 le_rfl,
    let φ1 : P1.quotient →+* P2.quotient := quotient_map P2 ϕ1 le_rfl,
    let φ : P1.quotient →+* P.quotient := φ3.comp (φ2.comp φ1),
    have hφ3 : φ3.is_integral := φ3.is_integral_of_surjective
      (quotient_map_surjective (fin_succ_equiv R n).symm.surjective),
    have hφ2 : φ2.is_integral,
    { rw is_integral_quotient_map_iff ϕ2,
      refine polynomial.quotient_mk_comp_C_is_integral_of_jacobson P3 } ,
    have hφ1 : φ1.is_integral,
    { rw is_integral_quotient_map_iff ϕ1,
      refine IH P2 },
    have hφ : φ.is_integral := ring_hom.is_integral_trans (φ2.comp φ1) φ3
      (ring_hom.is_integral_trans φ1 φ2 hφ1 hφ2) hφ3,
    have : (quotient.mk P).comp ϕ = φ.comp (quotient.mk P1),
    by rw [ring_hom.comp_assoc, ring_hom.comp_assoc, quotient_map_comp_mk, ← ring_hom.comp_assoc ϕ1,
      quotient_map_comp_mk, ← ring_hom.comp_assoc, ← ring_hom.comp_assoc, ← ring_hom.comp_assoc,
      ← ring_hom.comp_assoc, quotient_map_comp_mk],
    rw [← fin_succ_equiv_comp_C_eq_C n, this],
    refine ring_hom.is_integral_trans (quotient.mk P1) φ _ hφ,
    exact (quotient.mk P1).is_integral_of_surjective (quotient.mk_surjective) }
end

lemma comp_C_integral_of_surjective_of_jacobson
  {S : Type*} [field S] {n : ℕ} (f : (mv_polynomial (fin n) R) →+* S) (hf : function.surjective f) :
  (f.comp C).is_integral :=
begin
  haveI : (f.ker).is_maximal := @comap_is_maximal_of_surjective _ _ _ _ f ⊥ hf bot_is_maximal,
  let g : f.ker.quotient →+* S := ideal.quotient.lift f.ker f (λ _ h, h),
  have hfg : (g.comp (quotient.mk f.ker)) = f := quotient.lift_comp_mk f.ker f _,
  rw [← hfg, ring_hom.comp_assoc],
  refine ring_hom.is_integral_trans _ g (quotient_mk_comp_C_is_integral_of_jacobson f.ker)
    (g.is_integral_of_surjective (quotient.lift_surjective f.ker f _ hf)),
end

end integral_domain

end mv_polynomial

end ideal
