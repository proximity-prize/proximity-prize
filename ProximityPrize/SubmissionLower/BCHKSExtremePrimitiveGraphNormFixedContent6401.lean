import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveGraphNormContentRigidity6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveNormObstruction6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveTerminalFractionField6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveGraphNormFixedContent6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphNormRigidity6401
open BCHKSExtremePrimitiveGraphNormContentRigidity6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveRecursiveNormObstruction6401
open BCHKSExtremePrimitiveRecursiveTerminalFractionField6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section FixedPrimitiveParts
variable {F : Type} [Field F] [DecidableEq F]
theorem exists_fixedPrimitiveParts_of_resultant_ne_zero_of_graphNorm_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hresultant : Polynomial.resultant A B ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    ∃ A0 B0 : F[X],
      A.primPart = A0.map Polynomial.C ∧
        B.primPart = B0.map Polynomial.C := by
  rcases
      primitiveParts_challengeConstant_of_resultant_ne_zero_of_graphNorm_eq6401
        sigma q hq A B hA hB hresultant hnorm with ⟨hAc, hBc⟩
  obtain ⟨A0, hA0⟩ :=
    (challengeConstant_iff_exists_map_C6401 A.primPart).mp hAc
  obtain ⟨B0, hB0⟩ :=
    (challengeConstant_iff_exists_map_C6401 B.primPart).mp hBc
  exact ⟨A0, B0, hA0, hB0⟩
theorem exists_contentScaledFixedLanes_of_resultant_ne_zero_of_graphNorm_eq6401
    (sigma : F →+* F) (q : Nat) (hq : 1 < q)
    (A B : F[X][X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (hresultant : Polynomial.resultant A B ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    ∃ A0 B0 : F[X],
      A = Polynomial.C A.content * A0.map Polynomial.C ∧
        B = Polynomial.C B.content * B0.map Polynomial.C := by
  obtain ⟨A0, B0, hA0, hB0⟩ :=
    exists_fixedPrimitiveParts_of_resultant_ne_zero_of_graphNorm_eq6401
      sigma q hq A B hA hB hresultant hnorm
  refine ⟨A0, B0, ?_, ?_⟩
  · calc
      A = Polynomial.C A.content * A.primPart :=
        A.eq_C_content_mul_primPart
      _ = Polynomial.C A.content * A0.map Polynomial.C := by rw [hA0]
  · calc
      B = Polynomial.C B.content * B.primPart :=
        B.eq_C_content_mul_primPart
      _ = Polynomial.C B.content * B0.map Polynomial.C := by rw [hB0]
end FixedPrimitiveParts
section RecursiveFixedPrimitiveParts
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
variable {W : PrimitivePuncturedOwnerWindow6401
  sigma alpha u0 u1 S Aset Owner}
theorem recursiveLanes_ne_zero_of_graphNorm_eq6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 C.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 C.laneOne6401) :
    C.laneZero6401 ≠ 0 ∧ C.laneOne6401 ≠ 0 := by
  have hq0 : 0 < q6401 := by native_decide
  rcases recursiveLanes_not_both_zero6401 C with hA | hB
  · refine ⟨hA, ?_⟩
    intro hBzero
    have hnormA := graphFrobeniusNormSix_ne_zero6401
      sigma q6401 hq0 C.laneZero6401 hA
    apply hnormA
    rw [hnorm, hBzero]
    simp [graphFrobeniusNormSix6401, graphTwist6401,
      graphTwistTwo6401, graphTwistThree6401,
      graphTwistFour6401, graphTwistFive6401]
  · refine ⟨?_, hB⟩
    intro hAzero
    have hnormB := graphFrobeniusNormSix_ne_zero6401
      sigma q6401 hq0 C.laneOne6401 hB
    apply hnormB
    rw [← hnorm, hAzero]
    simp [graphFrobeniusNormSix6401, graphTwist6401,
      graphTwistTwo6401, graphTwistThree6401,
      graphTwistFour6401, graphTwistFive6401]
theorem exists_recursiveFixedPrimitiveParts_of_resultant_ne_zero_of_graphNorm_eq6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hresultant : C.laneResultant6401 ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 C.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 C.laneOne6401) :
    ∃ A0 B0 : F[X],
      C.laneZero6401.primPart = A0.map Polynomial.C ∧
        C.laneOne6401.primPart = B0.map Polynomial.C := by
  obtain ⟨hA, hB⟩ := recursiveLanes_ne_zero_of_graphNorm_eq6401 C hnorm
  exact exists_fixedPrimitiveParts_of_resultant_ne_zero_of_graphNorm_eq6401
    sigma q6401 (by native_decide)
    C.laneZero6401 C.laneOne6401 hA hB hresultant hnorm
theorem exists_recursiveContentScaledFixedLanes_of_resultant_ne_zero_of_graphNorm_eq6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hresultant : C.laneResultant6401 ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 C.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 C.laneOne6401) :
    ∃ A0 B0 : F[X],
      C.laneZero6401 = Polynomial.C C.laneZero6401.content *
          A0.map Polynomial.C ∧
        C.laneOne6401 = Polynomial.C C.laneOne6401.content *
          B0.map Polynomial.C := by
  obtain ⟨hA, hB⟩ := recursiveLanes_ne_zero_of_graphNorm_eq6401 C hnorm
  exact exists_contentScaledFixedLanes_of_resultant_ne_zero_of_graphNorm_eq6401
    sigma q6401 (by native_decide)
    C.laneZero6401 C.laneOne6401 hA hB hresultant hnorm
end RecursiveFixedPrimitiveParts
end BCHKSExtremePrimitiveGraphNormFixedContent6401
end ProximityPrize.SubmissionLower
