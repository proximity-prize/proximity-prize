import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Y4
import ProximityPrize.SubmissionLower.R
namespace ProximityPrize.SubmissionLower.RCN069
open RCN223 RCN174 RCN136
open RCN068 RCN238
noncomputable section
def legacyVector (v:RCN223.DegreeVector):
   RCN051.DegreeVector:=⟨v.y,v.r,v.z⟩
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
     RCN223.multiplicity,agreements,n,errors,
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
 · norm_num [RCN051.mixed,legacyVector,liftedSurface,
     implicitCut,RCN051.unitY,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
 · norm_num [RCN051.mixed,legacyVector,liftedSurface,
     implicitCut,RCN051.unitR,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
 · norm_num [RCN051.mixed,legacyVector,liftedSurface,
     implicitCut,RCN051.unitZ,implicitYCap,
     implicitWeightedCap,algebraicCap,weightedCap,
     RCN223.multiplicity,agreements,n,errors,
     w,slopeCap,seedTotalCap,prime]
end
end ProximityPrize.SubmissionLower.RCN069
