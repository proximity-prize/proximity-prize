import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveOwnerMassResultantZero6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveTerminalCommonContent6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveFixedLaneRecurrence6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveRecursiveOwnerMassResultantZero6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveTerminalCommonContent6401
set_option maxHeartbeats 3000000
set_option maxRecDepth 1000000
section FixedRecurrence
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
theorem recursiveFixedFailureRelation_of_commonScalarLanes6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G A0 B0 : F[X])
    (hzero : R.laneZero6401 =
      Polynomial.C G * A0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * B0.map Polynomial.C)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ R.goodChallenges6401)
    (hGz : G.eval z ≠ 0) :
    TwoLaneFailureRelation sigma W.puncturedAlpha
      (W.puncturedOwnerError z) A0 B0 := by
  have hrel := recursivePuncturedTwoLaneFailureRelation6401
    W R hsigma hfixed z hz
  have hspecZero : specializeCoeffZ z R.laneZero6401 =
      Polynomial.C (G.eval z) * A0 := by
    have h := congrArg (specializeCoeffZ z) hzero
    simpa [specializeCoeffZ, Polynomial.map_mul] using h
  have hspecOne : specializeCoeffZ z R.laneOne6401 =
      Polynomial.C (G.eval z) * B0 := by
    have h := congrArg (specializeCoeffZ z) hone
    simpa [specializeCoeffZ, Polynomial.map_mul] using h
  intro i
  have hi := hrel i
  rw [hspecZero, hspecOne] at hi
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hi
  apply mul_left_cancel₀ hGz
  simpa only [mul_assoc] using hi
theorem recursiveFixedFailureRelation_of_constantContentRatio6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (cA cB G A0 B0 : F[X]) (a b : F)
    (hzero : R.laneZero6401 =
      Polynomial.C cA * A0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C cB * B0.map Polynomial.C)
    (hcA : cA = G * Polynomial.C a)
    (hcB : cB = G * Polynomial.C b)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ R.goodChallenges6401)
    (hGz : G.eval z ≠ 0) :
    TwoLaneFailureRelation sigma W.puncturedAlpha
      (W.puncturedOwnerError z)
      (Polynomial.C a * A0) (Polynomial.C b * B0) := by
  apply recursiveFixedFailureRelation_of_commonScalarLanes6401
    W R G (Polynomial.C a * A0) (Polynomial.C b * B0)
      ?_ ?_ hsigma hfixed z hz hGz
  · rw [hzero, hcA]
    simp only [Polynomial.C_mul, Polynomial.map_mul, Polynomial.map_C]
    ring
  · rw [hone, hcB]
    simp only [Polynomial.C_mul, Polynomial.map_mul, Polynomial.map_C]
    ring
theorem exists_recursiveCommonContentFixedFailurePair6401
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
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧
      R.laneZero6401 = Polynomial.C G * U0.map Polynomial.C ∧
      R.laneOne6401 = Polynomial.C G * U1.map Polynomial.C ∧
      ∀ z ∈ R.goodChallenges6401, G.eval z ≠ 0 →
        TwoLaneFailureRelation sigma W.puncturedAlpha
          (W.puncturedOwnerError z) U0 U1 := by
  obtain ⟨G, U0, U1, hG, hU0, hU1, hzeroCommon, honeCommon⟩ :=
    exists_recursiveCommonContent_fixedPair_of_resultant_ne_zero_of_graphNorm_eq6401
      R horder hresultant hnorm
  refine ⟨G, U0, U1, hG, hU0, hU1,
    hzeroCommon, honeCommon, ?_⟩
  intro z hz hGz
  exact recursiveFixedFailureRelation_of_commonScalarLanes6401
    W R G U0 U1 hzeroCommon honeCommon hsigma hfixed z hz hGz
end FixedRecurrence
end BCHKSExtremePrimitiveFixedLaneRecurrence6401
end ProximityPrize.SubmissionLower
