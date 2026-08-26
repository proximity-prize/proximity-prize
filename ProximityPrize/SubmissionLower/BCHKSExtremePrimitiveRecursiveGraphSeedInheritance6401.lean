import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveFactorClosure6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFaithfulGraphGauge6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveRecursiveGraphSeedInheritance6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphGaugeFork6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveFaithfulGraphGauge6401
open BCHKSFrobeniusGraphHilbert90Audit6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
section Scaling
variable {F : Type} [Field F] [DecidableEq F]
noncomputable def graphHilbert90CommonFactorFive6401
    (sigma : F →+* F) (q : Nat) (K : F[X][X]) : F[X][X] :=
  K * graphTwist6401 sigma q K * graphTwistTwo6401 sigma q K *
    graphTwistThree6401 sigma q K * graphTwistFour6401 sigma q K
theorem graphHilbert90Numerator_commonFactor6401
    (sigma : F →+* F) (q : Nat)
    (K A B : F[X][X]) (t : F) :
    graphHilbert90Numerator6401 sigma q (K * A) (K * B) t =
      graphHilbert90CommonFactorFive6401 sigma q K *
        graphHilbert90Numerator6401 sigma q A B t := by
  simp only [graphHilbert90Numerator6401,
    graphHilbert90Denominator6401,
    graphHilbert90CommonFactorFive6401,
    graphTwist6401, graphTwistTwo6401, graphTwistThree6401,
    graphTwistFour6401, Polynomial.map_mul]
  ring
theorem graphHilbert90CommonFactorFive_ne_zero6401
    (sigma : F →+* F) (q : Nat) (hq : 0 < q)
    (K : F[X][X]) (hK : K ≠ 0) :
    graphHilbert90CommonFactorFive6401 sigma q K ≠ 0 := by
  have h1 : graphTwist6401 sigma q K ≠ 0 :=
    graphTwist_ne_zero6401 sigma q hq K hK
  have h2 : graphTwistTwo6401 sigma q K ≠ 0 := by
    exact graphTwist_ne_zero6401 sigma q hq _ h1
  have h3 : graphTwistThree6401 sigma q K ≠ 0 := by
    exact graphTwist_ne_zero6401 sigma q hq _ h2
  have h4 : graphTwistFour6401 sigma q K ≠ 0 := by
    exact graphTwist_ne_zero6401 sigma q hq _ h3
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hK h1) h2) h3) h4
end Scaling
section RecursiveInheritance
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
variable {W : PrimitivePuncturedOwnerWindow6401
  sigma alpha u0 u1 S Aset Owner}
theorem originalLaneZero_factor6401
    (C : RecursivePrimitiveLaneState6401 W) :
    primitiveBivariateFailureLaneZero6401 W =
      C.cumulativeFactor * C.laneZero6401 := by
  simpa [primitiveBivariateFailureLaneZero6401,
    RecursivePrimitiveLaneState6401.laneZero6401] using
      C.component_factor 2
theorem originalLaneOne_factor6401
    (C : RecursivePrimitiveLaneState6401 W) :
    primitiveBivariateFailureLaneOne6401 W =
      C.cumulativeFactor * C.laneOne6401 := by
  rw [primitiveBivariateFailureLaneOne6401,
    RecursivePrimitiveLaneState6401.laneOne6401,
    C.component_factor 1]
  ring
theorem primitiveFamilyGraphGaugeNumerator_recursiveFactor6401
    (C : RecursivePrimitiveLaneState6401 W) (t : F) :
    primitiveFamilyGraphGaugeNumerator6401 W t =
      graphHilbert90CommonFactorFive6401 sigma q6401
          C.cumulativeFactor *
        graphHilbert90Numerator6401 sigma q6401
          C.laneZero6401 C.laneOne6401 t := by
  rw [primitiveFamilyGraphGaugeNumerator6401,
    originalLaneZero_factor6401 C, originalLaneOne_factor6401 C]
  exact graphHilbert90Numerator_commonFactor6401
    sigma q6401 C.cumulativeFactor C.laneZero6401 C.laneOne6401 t
theorem graphCommonFactorFive_ne_zero6401
    (C : RecursivePrimitiveLaneState6401 W) :
    graphHilbert90CommonFactorFive6401 sigma q6401
      C.cumulativeFactor ≠ 0 := by
  exact graphHilbert90CommonFactorFive_ne_zero6401 sigma q6401
    (by native_decide) C.cumulativeFactor C.cumulativeFactor_ne_zero
theorem recursiveGraphHilbert90Numerator_eq_zero_of_original_allSeedsZero6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hall : ∀ t : F, primitiveFamilyGraphGaugeNumerator6401 W t = 0) :
    ∀ t : F, graphHilbert90Numerator6401 sigma q6401
      C.laneZero6401 C.laneOne6401 t = 0 := by
  intro t
  have hfactor := primitiveFamilyGraphGaugeNumerator_recursiveFactor6401 C t
  rw [hall t] at hfactor
  exact (mul_eq_zero.mp hfactor.symm).resolve_left
    (graphCommonFactorFive_ne_zero6401 C)
end RecursiveInheritance
end BCHKSExtremePrimitiveRecursiveGraphSeedInheritance6401
end ProximityPrize.SubmissionLower
