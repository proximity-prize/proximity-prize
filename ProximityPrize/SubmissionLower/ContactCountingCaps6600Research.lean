import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactCountingCaps
import ProximityPrize.SubmissionLower.ContactParameters6600Research
namespace ProximityPrize.SubmissionLower.ContactCountingCaps6600Research
open ContactParameters6600Research ContactInterpolation ContactGenericSurface
open ContactCountingCaps ContactPrimeSeedIncidence
noncomputable section
def legacyVector (v:ContactParameters6600Research.DegreeVector):
    ContactAlignmentParameters.DegreeVector:=⟨v.y,v.r,v.z⟩
variable {K Omega:Type} [Field K] [Field Omega]
theorem fixed_implicit_agreement_caps
    (phi:Polynomial K →+*Omega) (F:MvPolynomial (Fin 4) K)
    (hY:F.degreeOf 1 ≤ implicitYCap)
    (hR:F.degreeOf 2 ≤ 1) (hZ:F.degreeOf 3 ≤ algebraicCap)
    (x u0 u1:K):
    HasCaps (agreementPolynomial phi F w x u0 u1)
      (legacyVector liftedAgreement):=by
  have h:=surface_agreement_caps phi F implicitYCap 1 algebraicCap
    (by decide) hY hR hZ w (fun j => (j.factorial:K)⁻¹) x u0 u1
  simpa [agreementPolynomial,agreementCaps,legacyVector,
    liftedAgreement] using h
theorem fixed_implicit_surface_caps_below_characteristic:
    forall j,capAt (legacyVector liftedSurface) j < prime:=by
  intro j
  fin_cases j <;>
    norm_num [capAt,legacyVector,liftedSurface,implicitYCap,
      implicitWeightedCap,algebraicCap,weightedCap,
      ContactParameters6600Research.multiplicity,agreements,n,errors,
      w,slopeCap,seedTotalCap,prime]
theorem fixed_implicit_characteristic_gates
    (G T:MvPolynomial (Fin 3) Omega)
    (hG:HasCaps G (legacyVector liftedSurface))
    (hT:HasCaps T (legacyVector implicitCut)):
    (forall j,G.degreeOf j < prime)∧
      forall j k:Fin 3,j≠k->
        T.degreeOf j*G.degreeOf k+G.degreeOf j*T.degreeOf k < prime:=by
  apply actual_characteristic_gates G T _ _ prime hG hT
    fixed_implicit_surface_caps_below_characteristic
  · norm_num [ContactAlignmentParameters.mixed,legacyVector,liftedSurface,
      implicitCut,ContactAlignmentParameters.unitY,implicitYCap,
      implicitWeightedCap,algebraicCap,weightedCap,
      ContactParameters6600Research.multiplicity,agreements,n,errors,
      w,slopeCap,seedTotalCap,prime]
  · norm_num [ContactAlignmentParameters.mixed,legacyVector,liftedSurface,
      implicitCut,ContactAlignmentParameters.unitR,implicitYCap,
      implicitWeightedCap,algebraicCap,weightedCap,
      ContactParameters6600Research.multiplicity,agreements,n,errors,
      w,slopeCap,seedTotalCap,prime]
  · norm_num [ContactAlignmentParameters.mixed,legacyVector,liftedSurface,
      implicitCut,ContactAlignmentParameters.unitZ,implicitYCap,
      implicitWeightedCap,algebraicCap,weightedCap,
      ContactParameters6600Research.multiplicity,agreements,n,errors,
      w,slopeCap,seedTotalCap,prime]
end
end ProximityPrize.SubmissionLower.ContactCountingCaps6600Research
