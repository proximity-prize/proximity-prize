import ProximityPrize.SubmissionLower.Z62SyBc
set_option Elab.async false
namespace q1kuFjb
noncomputable section
open Polynomial qQ9yWTb qb0hmCe



open cu (L FX)
open scoped Classical WithZero
theorem map_liftAt {E :Type} [Field E] [Algebra L E]
  (a :E →ₐ[L] LaurentSeries L) (f :E[X][X]) (hf) :
  mapTwice IntSeries.subtype (Ua a f hf)=mapTwice a.toRingHom f := by
 apply Polynomial.ext
 intro i
 apply Polynomial.ext
 intro j
 simp only [mapTwice,coe_mapRingHom,coeff_map,Subring.subtype_apply,coeff_liftAt]
 rfl
theorem integral_restrict {q:Curve} {Cq:CurveModel q} {s :Fin 2→L}
    (A:AtSite Cq s) (F:Raw) :
    ∃ g:IntSeries[X][X],mapTwice IntSeries.subtype g=mapTwice A.map.toRingHom (restrict Cq F) ∧
      mapTwice residue g=restrictOver (RingHom.id L) s F:= by
  obtain ⟨z,hz,hs,_⟩:=A.arc
  let eqv :=LaurentSeries.powerSeriesEquivSubring L
  let b:L →+* IntSeries :=eqv.toRingHom.comp PowerSeries.C
  refine ⟨restrictOver b (eqv ∘ z) F,?_,?_⟩
  · unfold restrict
    rw [mapTwice_restrict,mapTwice_restrict]
    have hb:IntSeries.subtype.comp b=A.map.toRingHom.comp (algebraMap L Cq.E) := by
      apply RingHom.ext
      intro c
      change ((eqv (PowerSeries.C c) :IntSeries) :LaurentSeries L)=A.map (algebraMap L Cq.E c)
      rw [LaurentSeries.powerSeriesEquivSubring_coe_apply,A.map.commutes,
        LaurentSeries.algebraMap_apply,PowerSeries.coe_C]
    have he :IntSeries.subtype ∘ (eqv ∘ z)=A.map.toRingHom ∘ Cq.seed := by
      funext i
      exact (hz i).symm
    rw [hb,he]
  · rw [mapTwice_restrict]
    have hr (g:PowerSeries L) :residue (eqv g)=PowerSeries.constantCoeff g:= by
      change PowerSeries.constantCoeff (eqv.symm (eqv g))= _
      rw [RingEquiv.symm_apply_apply]
    have hb:residue.comp b=RingHom.id L:= by
      apply RingHom.ext
      intro c
      change residue (eqv (PowerSeries.C c))=c
      rw [hr,PowerSeries.constantCoeff_C]
    have he :residue ∘ (eqv ∘ z)=s := by
      funext i
      exact (hr (z i)).trans (hs i)
    rw [hb,he]
private theorem specialize_phys_ne {E :Type} [Field E] [Algebra L E]
   (a :E →ₐ[L] LaurentSeries L) {g:E[X]} (hg:g.Monic) (P Q:L[X]) :
   specialize (cLN a 0 (C g)) P Q≠0:= by
 let b:=(cLN a 0 (C g)).coeff 0
 have he :cLN a 0 (C g)=C b:= by
   apply Polynomial.ext
   intro i
   by_cases hi:i=0
   · subst i
     exact coeff_C_zero.symm
   · apply Polynomial.ext
     intro j
     rw [expansion_coeff,coeff_C,ite_eq_right hi,coeff_C,ite_eq_right hi]
     simp
 have hb:b.coeff g.natDegree=1 := by
   change ((cLN a 0 (C g)).coeff 0).coeff g.natDegree=1
   rw [expansion_coeff,coeff_C_zero,coeff_natDegree,hg,map_one]
   simp
 rw [he,specialize,eval₂_C]
 exact fun h=>one_ne_zero (hb.symm.trans (by
   rw [(map_eq_zero_iff _ (IsFractionRing.injective L[X] FX)).mp h,coeff_zero]))
end
end q1kuFjb
