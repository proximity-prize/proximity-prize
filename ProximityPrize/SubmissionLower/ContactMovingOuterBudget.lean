import ProximityPrize.SubmissionLower.ContactMovingCurveFamily
import ProximityPrize.SubmissionLower.ContactMovingDerivativeFlags
import ProximityPrize.SubmissionLower.ContactMovingPositiveLedger

namespace ProximityPrize.SubmissionLower.ContactMovingOuterBudget
open scoped Classical BigOperators
open ContactGenericSurface ContactTaylorNumerators ContactPrimeSeedIncidence
open ContactProperCutSeedCount ContactRegularComponentCover
open ContactWeakSeparableSeparator ContactAdaptiveUnitPoleFamily
open ContactFlagBezout ContactMovingCurveBudget
open ContactMovingCurveFamily ContactMovingProjection
open ContactMovingAgreementCertificate
open ContactMovingDerivativeFlags ContactResidualSupportParameters
open ContactSharpTaylorFixedMeet
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000
variable {K Ω E : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable [Field E] [IsAlgClosed E] [Algebra Ω E] [Algebra (RatFunc Ω) E]
variable [IsScalarTower Ω (RatFunc Ω) E]

def paddedCut (a b s d : ℕ) : FlagDegree :=
  ContactMovingPositiveLedger.centreFlag a b s +
    d • ContactMovingPositiveLedger.directionFlag a b s

theorem mixed_add_second (p q r t : FlagDegree) :
    flagMixed p (q+r) t = flagMixed p q t + flagMixed p r t := by
  simp only [flagMixed, add_zOnly, add_yz, add_all]
  ring

theorem mixed_affine_third (p q C R : FlagDegree) (k : ℕ) :
    flagMixed p q (C+k • R) = flagMixed p q C + k*flagMixed p q R := by
  simp only [flagMixed, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all]
  ring

theorem mixed_sharp_le_padded (a b s d : ℕ) (p r : FlagDegree) :
    flagMixed p (sharpResidualAgreementFlag (support a b s) d) r ≤
      flagMixed p (paddedCut a b s d) r := by
  have he : paddedCut a b s d =
      sharpResidualAgreementFlag (support a b s) d + direction a b s := by
    rw [sharp_flag_eq]
    change FlagDegree.mk _ _ _ = FlagDegree.mk _ _ _
    congr 1 <;> simp [ContactMovingPositiveLedger.centreFlag,
      ContactMovingPositiveLedger.directionFlag, direction, unitYZFlag] <;> ring
  rw [he, mixed_add_second]
  exact Nat.le_add_right _ _

end
end ProximityPrize.SubmissionLower.ContactMovingOuterBudget
