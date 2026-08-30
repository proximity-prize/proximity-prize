import ProximityPrize.SubmissionLower.ContactMovingProjection
import ProximityPrize.SubmissionLower.ArbitraryRationalProjection
import ProximityPrize.SubmissionLower.ContactRegularComponentCover
import ProximityPrize.SubmissionLower.ContactGenericFiberEmbeddings

namespace ProximityPrize.SubmissionLower.ContactMovingProjectionDegree

open scoped Classical
open ActualCurveCoordinateField ContactCurveComponents ContactRegularComponentCover
open ArbitraryRationalProjection ContactMovingProjection
open ContactGenericFiberEmbeddings

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000

variable {K L : Type} [Field K] [Field L]

def coordinateFieldMap (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (ev : MvPolynomial (Fin 3) K →+* L) (hker : RingHom.ker ev=P) :
    CoordinateField K P →+* L :=
  let hz : ∀ A, A ∈ P → ev A=0 := fun A hA ↦ by
    exact RingHom.mem_ker.mp (hker.symm ▸ hA)
  IsFractionRing.lift (K := CoordinateField K P)
    (RingHom.lift_injective_of_ker_le_ideal P hz hker.le)

theorem coordinateFieldMap_eval (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (ev : MvPolynomial (Fin 3) K →+* L) (hker : RingHom.ker ev=P)
    (A : MvPolynomial (Fin 3) K) :
    coordinateFieldMap P ev hker (coordinateEvaluation K P A)=ev A := by
  unfold coordinateFieldMap
  change IsFractionRing.lift _
    (algebraMap (CoordinateRing K P) (CoordinateField K P) (Ideal.Quotient.mk P A))=ev A
  rw [IsFractionRing.lift_algebraMap, Ideal.Quotient.lift_mk]

def movingValue (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (H G Q U : MvPolynomial (Fin 3) K) : CoordinateField K P :=
  coordinateEvaluation K P Q +
    coordinateEvaluation K P U * coordinateEvaluation K P G /
      coordinateEvaluation K P H

def scalarPolynomialMap (K E : Type) [Field K] [Field E] [Algebra K E] :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) E :=
  MvPolynomial.map (algebraMap K E)

theorem comap_le_of_embedding_point {E : Type} [Field E] [Algebra K E]
    (P : Ideal (MvPolynomial (Fin 3) K)) [P.IsPrime]
    (f : CoordinateField K P →ₐ[K] E) (D : Ideal (MvPolynomial (Fin 3) E))
    (hD : D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint P f) : MvPolynomial (Fin 3) E →ₐ[E] E).toRingHom) :
    D.comap (scalarPolynomialMap K E) ≤ P := by
  intro A hA
  rw [← embeddingPoint_kernel P f]
  apply RingHom.mem_ker.mpr
  have hv := RingHom.mem_ker.mp (hD hA)
  simpa only [MvPolynomial.aeval_eq_eval₂Hom, scalarPolynomialMap,
    MvPolynomial.eval₂Hom_map_hom, Algebra.algebraMap_self, RingHom.id_comp,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hv

end
end ProximityPrize.SubmissionLower.ContactMovingProjectionDegree
