import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTerminalFixedPairOrbit6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFixedLaneRecurrence6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTerminalFixedPairPackage6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveFixedLaneRecurrence6401
open BCHKSExtremePrimitiveTerminalFixedPairOrbit6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
section RecursiveTerminalPackage
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
theorem exists_recursiveTerminalPuncturedCoprimeNormFixedPair6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (hresultant : R.laneResultant6401 ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 R.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 R.laneOne6401)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i) :
    ∃ G U0 U1 : F[X],
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧ IsCoprime U0 U1 ∧
        polynomialFrobeniusNormSix sigma U0 =
          polynomialFrobeniusNormSix sigma U1 ∧
        U0.natDegree ≤ homogeneousDirectionCap6401 ∧
        U1.natDegree ≤ homogeneousDirectionCap6401 ∧
        R.laneZero6401 = Polynomial.C G * U0.map Polynomial.C ∧
        R.laneOne6401 = Polynomial.C G * U1.map Polynomial.C ∧
        ∀ z ∈ R.goodChallenges6401, G.eval z ≠ 0 →
          TwoLaneFailureRelation sigma W.puncturedAlpha
            (W.puncturedOwnerError z) U0 U1 := by
  obtain ⟨G, U0, U1, hG, hU0, hU1, hcop, hnormFixed,
      hzero, hone⟩ :=
    exists_recursiveCommonContent_coprimeFixedPair_normEq6401
      R horder hresultant hnorm
  have hzeroMap : U0.map Polynomial.C ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hU0
  have honeMap : U1.map Polynomial.C ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hU1
  have hzeroDegree : R.laneZero6401.natDegree = U0.natDegree := by
    rw [hzero, Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr hG) hzeroMap,
      Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
    simp
  have honeDegree : R.laneOne6401.natDegree = U1.natDegree := by
    rw [hone, Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr hG) honeMap,
      Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
    simp
  have hU0degree : U0.natDegree ≤ homogeneousDirectionCap6401 := by
    rw [← hzeroDegree]
    simpa [RecursivePrimitiveLaneState6401.laneZero6401,
      primitiveThreeShiftXCap6401, homogeneousDirectionCap6401] using
        R.quotient_caps6401 (2 : Fin 3)
  have hU1degree : U1.natDegree ≤ homogeneousDirectionCap6401 := by
    rw [← honeDegree]
    simpa [RecursivePrimitiveLaneState6401.laneOne6401,
      primitiveThreeShiftXCap6401, homogeneousDirectionCap6401] using
        R.quotient_caps6401 (1 : Fin 3)
  refine ⟨G, U0, U1, hG, hU0, hU1, hcop, hnormFixed,
    hU0degree, hU1degree, hzero, hone, ?_⟩
  intro z hz hGz
  exact recursiveFixedFailureRelation_of_commonScalarLanes6401
    W R G U0 U1 hzero hone hsigma hfixed z hz hGz
end RecursiveTerminalPackage
end BCHKSExtremePrimitiveTerminalFixedPairPackage6401
end ProximityPrize.SubmissionLower
