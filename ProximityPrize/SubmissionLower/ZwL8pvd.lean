import ProximityPrize.SubmissionLower.ZWpWUpd
import ProximityPrize.SubmissionLower.ZRtQEca
import ProximityPrize.SubmissionLower.ZalmDpd
import ProximityPrize.SubmissionLower.Znc9Sbd
import ProximityPrize.SubmissionLower.ZPkJuGd
set_option Elab.async false
open _root_ renaming Algebra → zZE, Ideal.Quotient.lift → zP2, Ideal.Quotient.mk → zVv, Ideal.map_le_iff_le_comap → zo0, Ideal.mem_map_of_mem → z7X, IsFractionRing.injective → zxb, IsFractionRing.lift_algebraMap → zoc, MvPolynomial.X → z9v, MvPolynomial.ringHom_ext → zXT, Polynomial → zM1, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.aeval → zEU, Polynomial.aeval_C → z8q, Polynomial.aeval_X → zw0, RingHom.congr_fun → zLs
section
set_option autoImplicit true
namespace qlUWVtd
theorem proof :qqwac6b.c2 :=
  qvWbALd.of_children q9aDOab.proof qmpFDTd.proof
end qlUWVtd
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace qJVcWac
noncomputable section
open cu (FX aZ)
open gT (Ambient aQ ek Dk Y0 Pp)
open pI (pN)
open OH (Q6 N8)
open aiM (Gd b4A)
open q3rjQGe (AxisSection)
open qgscZIa (axisIdeal axisCoord freeAxis fixedAxis)
open MvPolynomial
open private axis_fixed from ProximityPrize.SubmissionLower.ZPkJuGd
open scoped RatFunc TensorProduct
attribute [local instance] Polynomial.algebra
private abbrev E :=RatFunc aQ
private abbrev D:=MvPolynomial (Fin 2) E
private abbrev B:=zM1 aQ
section
variable (a :Fin 2)
private def aXB:aZ →+* zM1 aZ :=
  eval₂Hom (Polynomial.C.comp C)
    (fun i=>if i=a then z7y else z1z (z9v 1))
private def undoSubstitution :zM1 aZ →+* aZ :=
  Polynomial.eval₂RingHom (eval₂Hom C ![0,z9v (if a=0 then 1 else 0)])
    (z9v a)
private theorem gow :
    Function.Injective (aXB a) := by
  have h: (undoSubstitution a).comp (aXB a)=RingHom.id aZ:= by
    apply zXT
    · intro c
      simp [undoSubstitution,aXB]
    · intro i
      fin_cases a <;> fin_cases i <;> simp [undoSubstitution,aXB]
  exact Function.LeftInverse.injective (zLs h)
private def bNL:aZ →+* E :=
  (algebraMap B E).comp ((Polynomial.mapRingHom (algebraMap aZ aQ)).comp
    (aXB a))
private def IL:aQ →+* E :=
  IsFractionRing.lift (g:=bNL a) ((zxb B E).comp
    ((Polynomial.map_injective _ (zxb aZ aQ)).comp
      (gow a)))
private def seedValue (i:Fin 2) :E :=
  if i=a then RatFunc.X else RatFunc.C (ek 1)
private theorem coW (c:FX) :
    IL a (algebraMap FX aQ c)=RatFunc.C (algebraMap FX aQ c) := by
  change IL a (algebraMap aZ aQ (C c))= _
  rw [IL,zoc]
  simp [bNL,aXB,RatFunc.algebraMap_C]
  rfl
private theorem seedCoefficients_var (i:Fin 2) :
    IL a (ek i)=seedValue a i:= by
  rw [ek,IL,zoc]
  by_cases h:i=a <;>
    simp [bNL,aXB,seedValue,h,ek,RatFunc.algebraMap_C,
      RatFunc.algebraMap_X]
private def beb:Ambient →+* D :=
  (MvPolynomial.map (IL a)).comp Dk
private def ajs :N8 →+* D :=
  eval₂Hom (C.comp RatFunc.C)
    ![C (seedValue a 0),C (seedValue a 1),z9v 0,z9v 1]
private theorem cIW: (ajs a).comp Q6=beb a := by
  apply zXT
  · intro c
    simp [ajs,Q6,beb,Dk,coW]
  · intro i
    fin_cases i <;> simp [ajs,Q6,beb,Dk,seedCoefficients_var]
private theorem cutEval_fixed:ajs a (Pp (fixedAxis a))=0:= by
  fin_cases a <;> simp [ajs,seedValue,fixedAxis,Pp]
end
section
variable (q:Ideal Ambient) (a :Fin 2)
private abbrev aiB:=D ⧸ q.map (beb a)
private abbrev F :=
  Gd aQ (AxisSection q a) (axisCoord q a (freeAxis a))
private local instance gRr :
    zZE B (AxisSection q a) :=
  (zEU (axisCoord q a (freeAxis a)) :B →ₐ[aQ] AxisSection q a).toRingHom.toAlgebra
private local instance cutParameterAlgebra :zZE B (aiB q a) :=
  Algebra.compHom (aiB q a) (algebraMap B E)
private local instance cutParameterTower :
    @IsScalarTower B E (aiB q a) (show zZE B E from inferInstance).toSMul
      (show zZE E (aiB q a) from inferInstance).toSMul (cutParameterAlgebra q a).toSMul :=
  IsScalarTower.of_algebraMap_eq' rfl
private def bhX:AxisSection q a →+* aiB q a :=
  zP2 (axisIdeal q a) ((zVv (q.map (beb a))).comp (ajs a)) <| by
    change axisIdeal q a≤RingHom.ker _
    apply sup_le
    · rw [zo0]
      intro p hp
      change zVv _ (((ajs a).comp Q6) p)=0
      rw [cIW]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (z7X _ hp)
    · rw [Ideal.span_singleton_le_iff_mem]
      change zVv _ (ajs a (Pp (fixedAxis a)))=0
      rw [cutEval_fixed,map_zero]
private theorem cts (p:N8) :
    bhX q a (zVv (axisIdeal q a) p) =
      zVv (q.map (beb a)) (ajs a p) :=rfl
private def dhk :AxisSection q a →ₐ[B] aiB q a :=
  { bhX q a with
    commutes' := by
      have h: (bhX q a).comp (algebraMap B (AxisSection q a)) =
          algebraMap B (aiB q a) := by
        apply Polynomial.ringHom_ext
        · intro c
          change bhX q a (zEU (axisCoord q a (freeAxis a)) (z1z c)) =
            algebraMap E (aiB q a) (algebraMap B E (z1z c))
          rw [z8q,RatFunc.algebraMap_C]
          change bhX q a (zVv (axisIdeal q a) (C c))= _
          rw [cts]
          simp only [ajs,eval₂Hom_C,RingHom.comp_apply]
          rfl
        · change bhX q a (zEU (axisCoord q a (freeAxis a)) z7y) =
            algebraMap E (aiB q a) (algebraMap B E z7y)
          rw [zw0,RatFunc.algebraMap_X,axisCoord,cts]
          fin_cases a <;> simp [ajs,freeAxis,seedValue] <;> rfl
      exact zLs h }
private def bOW:F q a →ₐ[E] aiB q a :=
  AlgHom.liftEquiv B E (AxisSection q a) (aiB q a) (dhk q a)
private abbrev right:AxisSection q a →ₐ[B] F q a :=
  Algebra.TensorProduct.includeRight
private def inc:N8 →+* F q a :=
  (right q a).toRingHom.comp (zVv (axisIdeal q a))
private theorem cUY (c:aQ) :
    inc q a (C c)=algebraMap E (F q a) (RatFunc.C c) := by
  have h:=(right q a).commutes (z1z c)
  change right q a (zEU (axisCoord q a (freeAxis a)) (z1z c)) =
    algebraMap E (F q a) (algebraMap B E (z1z c)) at h
  rw [z8q,RatFunc.algebraMap_C] at h
  exact h
private theorem inc_free :
    inc q a (z9v (freeAxis a))=algebraMap E (F q a) RatFunc.X:= by
  have h:=(right q a).commutes (z7y:B)
  change right q a (zEU (axisCoord q a (freeAxis a)) z7y) =
    algebraMap E (F q a) (algebraMap B E z7y) at h
  rw [zw0,RatFunc.algebraMap_X] at h
  exact h
private theorem inc_fixed :
    inc q a (z9v (fixedAxis a))=algebraMap E (F q a) (RatFunc.C (ek 1)) := by
  change right q a (axisCoord q a (fixedAxis a))= _
  rw [axis_fixed]
  exact cUY q a (ek 1)
private def yZ:D →ₐ[E] F q a :=
  aeval ![inc q a (z9v 2),inc q a (z9v 3)]
private theorem cVO :
    (yZ q a).toRingHom.comp (ajs a)=inc q a := by
  apply zXT
  · intro c
    simp [ajs,yZ,cUY]
  · intro i
    fin_cases i <;> fin_cases a <;> simp [ajs,yZ,seedValue]
    · exact (inc_free q 0).symm
    · exact (inc_fixed q 1).symm
    · exact (inc_fixed q 0).symm
    · exact (inc_free q 1).symm
private def bG2 :aiB q a →ₐ[E] F q a :=
  { zP2 (q.map (beb a)) (yZ q a).toRingHom (by
      change q.map (beb a)≤RingHom.ker (yZ q a).toRingHom
      rw [zo0]
      intro p hp
      change yZ q a (beb a p)=0
      rw [← cIW]
      change ((yZ q a).toRingHom.comp (ajs a)) (Q6 p)=0
      rw [cVO]
      have hm:Q6 p∈axisIdeal q a :=
        Ideal.mem_sup_left (z7X _ hp)
      change right q a (zVv (axisIdeal q a) (Q6 p))=0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm,map_zero]) with
    commutes' := fun c=>(yZ q a).commutes c }
private theorem cTf (p:D) :
    bG2 q a (zVv (q.map (beb a)) p)=yZ q a p:=rfl
private theorem dhl (p:N8) :
    bOW q a (inc q a p)=zVv (q.map (beb a)) (ajs a p) := by
  have h:=AlgHom.congr_fun
    ((AlgHom.liftEquiv B E (AxisSection q a) (aiB q a)).left_inv (dhk q a))
    (zVv (axisIdeal q a) p)
  exact h.trans (cts q a p)
private def bp4 :F q a ≃ₐ[E] aiB q a :=
  AlgEquiv.ofAlgHom (bOW q a) (bG2 q a) (by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [cTf,yZ,dhl,ajs]) (by
    apply AlgHom.coe_ringHom_injective
    apply Algebra.TensorProduct.ringHom_ext (R:=B) (A:=E) (B:=AxisSection q a)
    · apply RingHom.ext
      intro c
      exact ((bG2 q a).comp (bOW q a)).commutes c
    · apply Ideal.Quotient.ringHom_ext
      apply RingHom.ext
      intro p
      change bG2 q a (bOW q a (inc q a p))=inc q a p
      rw [dhl,cTf]
      exact zLs (cVO q a) p)
private theorem fibre_length :
    Module.finrank E (F q a)=pN q 0:= by
  let:zZE aQ E :=(IL a).toAlgebra
  let e :E ⊗[aQ] Y0 q ≃ₐ[E] aiB q a :=
    (czE.aPw (E :=E) (q.map Dk)).trans
      (Ideal.quotientEquivAlgOfEq E (Ideal.map_map _ _))
  exact (bp4 q a).toLinearEquiv.finrank_eq.trans
    (e.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange)
end
theorem proof :qgscZIa.c1 := by
  intro q a hq
  obtain ⟨hp,hd⟩:=axis_geometry q a hq
  refine ⟨hp,hd,?_⟩
  intro
  exact (b4A aQ (AxisSection q a) (FractionRing (AxisSection q a))
    (axisCoord q a (freeAxis a))).trans (fibre_length q a)
end
end qJVcWac
end
