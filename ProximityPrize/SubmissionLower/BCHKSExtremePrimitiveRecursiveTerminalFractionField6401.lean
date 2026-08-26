import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveFactorClosure6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveResultantFractionField6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveRecursiveTerminalFractionField6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveResultantFractionField6401
section RecursiveTerminal
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
variable {W : PrimitivePuncturedOwnerWindow6401
  sigma alpha u0 u1 S Aset Owner}
theorem recursiveLanes_not_both_zero6401
    (C : RecursivePrimitiveLaneState6401 W) :
    C.laneZero6401 ≠ 0 ∨ C.laneOne6401 ≠ 0 := by
  rcases W.sourcePuncture.pivot_homogeneous with hpivot | hpivot
  · right
    simpa [RecursivePrimitiveLaneState6401.laneOne6401, hpivot] using
      C.quotient_pivot_ne_zero
  · left
    simpa [RecursivePrimitiveLaneState6401.laneZero6401, hpivot] using
      C.quotient_pivot_ne_zero
theorem recursiveLaneResultant_ne_zero_isCoprime_fractionMap6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hresultant : C.laneResultant6401 ≠ 0) :
    IsCoprime
      (C.laneZero6401.map
        (algebraMap F[X] (FractionRing F[X])))
      (C.laneOne6401.map
        (algebraMap F[X] (FractionRing F[X]))) := by
  exact resultant_ne_zero_isCoprime_fractionMap6401
    C.laneZero6401 C.laneOne6401
    (recursiveLanes_not_both_zero6401 C) hresultant
end RecursiveTerminal
end BCHKSExtremePrimitiveRecursiveTerminalFractionField6401
end ProximityPrize.SubmissionLower
