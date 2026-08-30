import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactDifferentialRing
namespace ProximityPrize.SubmissionLower.ContactRegularPoint
open ContactDifferentialRing
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
section Evaluation
variable {K L:Type*} [CommRing K] [Field L]
def extendPoint (v:Fin 4 → L) (inverseValue:L):Fin 5 → L:=
  ![v 0,v 1,v 2,v 3,inverseValue]
theorem extendPoint_castSucc (v:Fin 4 → L) (inverseValue:L) (i:Fin 4):
    extendPoint v inverseValue i.castSucc=v i:=by
  fin_cases i <;> rfl
theorem extendPoint_last (v:Fin 4 → L) (inverseValue:L):
    extendPoint v inverseValue (4:Fin 5)=inverseValue:=rfl
theorem eval_liftFour
    (coefficients:K →+*L) (v:Fin 4 → L) (inverseValue:L) (P:Poly4 K):
    MvPolynomial.eval₂Hom coefficients (extendPoint v inverseValue) (liftFour K P)=
      MvPolynomial.eval₂Hom coefficients v P:=by
  have hhom:
      (MvPolynomial.eval₂Hom coefficients (extendPoint v inverseValue)).comp
          (MvPolynomial.rename (Fin.castSucc:Fin 4 → Fin 5):
            Poly4 K →ₐ[K] Poly5 K).toRingHom=
        MvPolynomial.eval₂Hom coefficients v:=by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        MvPolynomial.rename_C,MvPolynomial.eval₂Hom_C]
    · intro i
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        MvPolynomial.rename_X,MvPolynomial.eval₂Hom_X',extendPoint_castSucc]
  exact RingHom.congr_fun hhom P
noncomputable def pointEvaluation
    (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L):Poly5 K →+*L:=
  MvPolynomial.eval₂Hom coefficients
    (extendPoint v ((MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2:Fin 4) F))⁻¹))
theorem pointEvaluation_liftFour
    (coefficients:K →+*L) (F P:Poly4 K) (v:Fin 4 → L):
    pointEvaluation coefficients F v (liftFour K P)=
      MvPolynomial.eval₂Hom coefficients v P:=
  eval_liftFour coefficients v _ P
theorem pointEvaluation_H
    (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L):
    pointEvaluation coefficients F v (contactH K F)=
      MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F):=by
  have h:=partial_liftFour K F (2:Fin 4)
  change contactH K F=liftFour K (MvPolynomial.pderiv (2:Fin 4) F) at h
  rw [h,pointEvaluation_liftFour]
theorem pointEvaluation_U
    (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L):
    pointEvaluation coefficients F v (MvPolynomial.X (4:Fin 5))=
      (MvPolynomial.eval₂Hom coefficients v (MvPolynomial.pderiv (2:Fin 4) F))⁻¹:=by
  simp only [pointEvaluation,MvPolynomial.eval₂Hom_X',extendPoint_last]
theorem contactIdeal_le_ker_pointEvaluation
    (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
    (hF:MvPolynomial.eval₂Hom coefficients v F=0)
    (hregular:MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2:Fin 4) F)≠0):
    contactIdeal K F ≤ RingHom.ker (pointEvaluation coefficients F v):=by
  apply Ideal.span_le.mpr
  intro P hP
  change pointEvaluation coefficients F v P=0
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl
  · rw [pointEvaluation_liftFour,hF]
  · rw [inverseRelation,map_sub,map_mul,map_one,pointEvaluation_H,
      pointEvaluation_U,mul_inv_cancel₀ hregular,sub_self]
noncomputable def regularPointValue
    (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
    (hF:MvPolynomial.eval₂Hom coefficients v F=0)
    (hregular:MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2:Fin 4) F)≠0):ContactRing K F →+*L:=
  Ideal.Quotient.lift (contactIdeal K F) (pointEvaluation coefficients F v)
    (fun P hP => RingHom.mem_ker.mp
      (contactIdeal_le_ker_pointEvaluation coefficients F v hF hregular hP))
theorem regularPointValue_mk
    (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
    (hF:MvPolynomial.eval₂Hom coefficients v F=0)
    (hregular:MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2:Fin 4) F)≠0) (P:Poly5 K):
    regularPointValue coefficients F v hF hregular
      (Ideal.Quotient.mk (contactIdeal K F) P)=pointEvaluation coefficients F v P:=rfl
theorem regularPointValue_algebraMap
    (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
    (hF:MvPolynomial.eval₂Hom coefficients v F=0)
    (hregular:MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2:Fin 4) F)≠0) (c:K):
    regularPointValue coefficients F v hF hregular
      (algebraMap K (ContactRing K F) c)=coefficients c:=by
  change regularPointValue coefficients F v hF hregular
    (Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.C c))=coefficients c
  rw [regularPointValue_mk]
  simp only [pointEvaluation,MvPolynomial.eval₂Hom_C]
theorem regularPointValue_comp_algebraMap
    (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
    (hF:MvPolynomial.eval₂Hom coefficients v F=0)
    (hregular:MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2:Fin 4) F)≠0):
    (regularPointValue coefficients F v hF hregular).comp
      (algebraMap K (ContactRing K F))=coefficients:=by
  ext c
  exact regularPointValue_algebraMap coefficients F v hF hregular c
end Evaluation
section Coordinates
variable (K:Type*) [CommRing K]
noncomputable def contactCoordinate (F:Poly4 K) (i:Fin 4):ContactRing K F:=
  Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X i.castSucc)
theorem coordinate_relation (F:Poly4 K):
    MvPolynomial.eval₂Hom (algebraMap K (ContactRing K F))
      (contactCoordinate K F) F=0:=by
  have hhom:
      (Ideal.Quotient.mk (contactIdeal K F)).comp
          (MvPolynomial.rename (Fin.castSucc:Fin 4 → Fin 5):
            Poly4 K →ₐ[K] Poly5 K).toRingHom=
        MvPolynomial.eval₂Hom (algebraMap K (ContactRing K F))
          (contactCoordinate K F):=by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        MvPolynomial.rename_C,MvPolynomial.eval₂Hom_C]
      rfl
    · intro i
      simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
        MvPolynomial.rename_X,MvPolynomial.eval₂Hom_X']
      rfl
  have hF:=RingHom.congr_fun hhom F
  change Ideal.Quotient.mk (contactIdeal K F) (liftFour K F)=
    MvPolynomial.eval₂Hom (algebraMap K (ContactRing K F)) (contactCoordinate K F) F at hF
  rw [contactRing_relation] at hF
  exact hF.symm
theorem derivation_coordinate_X (F:Poly4 K):
    contactDerivation K F (contactCoordinate K F (0:Fin 4))=1:=by
  rw [contactCoordinate,contactDerivation_mk]
  change Ideal.Quotient.mk (contactIdeal K F)
    (inverseVectorField K (contactG K F) (contactH K F) (MvPolynomial.X (0:Fin 5)))=1
  rw [inverseVectorField_X,map_one]
theorem derivation_coordinate_Y (F:Poly4 K):
    contactDerivation K F (contactCoordinate K F (1:Fin 4))=
      contactCoordinate K F (2:Fin 4):=by
  rw [contactCoordinate,contactDerivation_mk]
  change Ideal.Quotient.mk (contactIdeal K F)
    (inverseVectorField K (contactG K F) (contactH K F) (MvPolynomial.X (1:Fin 5)))=
      Ideal.Quotient.mk (contactIdeal K F) (MvPolynomial.X (2:Fin 5))
  rw [inverseVectorField_Y]
theorem derivation_coordinate_Z (F:Poly4 K):
    contactDerivation K F (contactCoordinate K F (3:Fin 4))=0:=by
  rw [contactCoordinate,contactDerivation_mk]
  change Ideal.Quotient.mk (contactIdeal K F)
    (inverseVectorField K (contactG K F) (contactH K F) (MvPolynomial.X (3:Fin 5)))=0
  rw [inverseVectorField_Z,map_zero]
variable {L:Type*} [Field L]
theorem regularPointValue_coordinate
    (coefficients:K →+*L) (F:Poly4 K) (v:Fin 4 → L)
    (hF:MvPolynomial.eval₂Hom coefficients v F=0)
    (hregular:MvPolynomial.eval₂Hom coefficients v
      (MvPolynomial.pderiv (2:Fin 4) F)≠0) (i:Fin 4):
    regularPointValue coefficients F v hF hregular (contactCoordinate K F i)=v i:=by
  rw [contactCoordinate,regularPointValue_mk]
  simp only [pointEvaluation,MvPolynomial.eval₂Hom_X',extendPoint_castSucc]
end Coordinates
end ProximityPrize.SubmissionLower.ContactRegularPoint
