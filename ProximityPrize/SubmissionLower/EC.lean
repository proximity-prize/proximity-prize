import ProximityPrize.SubmissionLower.DM
import ProximityPrize.SubmissionLower.L8
import ProximityPrize.SubmissionLower.Y7
namespace ProximityPrize.SubmissionLower.RCN113
open RCN002 RCN011
open RCN371 RCN021
open RCN125
open RCN093
open RCN034
open RCN190
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable (K:Type) [Field K]
def flagPlaneMap (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Original K →+*PlaneRing K:=
 (planeMap K order).comp (flagAlgHom lam mu nu).toRingHom
def flagPlaneDenominators (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Submonoid (Original K):=
 (planeDenominators K order).map (flagEquiv lam mu nu).symm.toMonoidHom
@[reducible] def flagPlaneAlgebra
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   Algebra (Original K) (PlaneRing K):=
 (flagPlaneMap K lam mu nu order).toAlgebra
theorem flagPlaneRingLocalization
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   letI:=flagPlaneAlgebra K lam mu nu order
   IsLocalization (flagPlaneDenominators K lam mu nu order) (PlaneRing K):=by
 letI:=planeAlgebra K order
 letI:IsLocalization (planeDenominators K order) (PlaneRing K):=
   planeRingLocalization K order
 exact IsLocalization.isLocalization_of_base_ringEquiv
   (planeDenominators K order) (PlaneRing K)
     (flagEquiv lam mu nu).symm.toRingEquiv
def flagRelationKernel
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   Ideal (PlaneRing K):=
 relationKernel K (CoordinateField K P) order
   (flagEvaluation K P lam mu nu) ht
theorem flagRelationKernel_contract
   (P:Ideal (Original K)) [P.IsPrime]
   (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   letI:=flagPlaneAlgebra K lam mu nu order
   (flagRelationKernel K P lam mu nu order ht).comap
     (algebraMap (Original K) (PlaneRing K))=P:=by
 letI:=flagPlaneAlgebra K lam mu nu order
 change (flagRelationKernel K P lam mu nu order ht).comap
     ((planeMap K order).comp (flagAlgHom lam mu nu).toRingHom)=P
 rw [←Ideal.comap_comap,flagRelationKernel,relationKernel_contract,
   flagEvaluation_kernel_contract]
theorem flag_map_surfaceIdeal
   (G:Original K) (lam mu nu:K) (order:Fin 3 ≃ Fin 3):
   letI:=flagPlaneAlgebra K lam mu nu order
   Ideal.map (algebraMap (Original K) (PlaneRing K)) (Ideal.span {G})=
     Ideal.span {planeMap K order (flagAlgHom lam mu nu G)}:=by
 letI:=flagPlaneAlgebra K lam mu nu order
 rw [Ideal.map_span]
 simp only [Set.image_singleton]
 rfl
noncomputable def flagSurfaceComponentToPlaneLocalEquiv
   (G:Original K) (P:Ideal (Original K)) [P.IsPrime]
   (hGmem:G∈P) (lam mu nu:K) (order:Fin 3 ≃ Fin 3)
   (ht:Transcendental K
     (flagEvaluation K P lam mu nu (MvPolynomial.X (order 0)))):
   letI:=flagPlaneAlgebra K lam mu nu order
   letI:(flagRelationKernel K P lam mu nu order ht).IsPrime:=
     RingHom.ker_isPrime _
   SourceLocal (Ideal.span {G}) P
       (by simpa only [Ideal.span_singleton_le_iff_mem] using hGmem) ≃+*
     TargetLocal (Ideal.span {G}) P
       (flagRelationKernel K P lam mu nu order ht)
       (by simpa only [Ideal.span_singleton_le_iff_mem] using hGmem)
       (flagRelationKernel_contract K P lam mu nu order ht):=by
 letI:=flagPlaneAlgebra K lam mu nu order
 letI:IsLocalization (flagPlaneDenominators K lam mu nu order)
     (PlaneRing K):=flagPlaneRingLocalization K lam mu nu order
 letI:(flagRelationKernel K P lam mu nu order ht).IsPrime:=
   RingHom.ker_isPrime _
 exact surfaceLocalEquiv (flagPlaneDenominators K lam mu nu order)
   (Ideal.span {G}) P (flagRelationKernel K P lam mu nu order ht)
   (by simpa only [Ideal.span_singleton_le_iff_mem] using hGmem)
   (flagRelationKernel_contract K P lam mu nu order ht)
end
end ProximityPrize.SubmissionLower.RCN113
