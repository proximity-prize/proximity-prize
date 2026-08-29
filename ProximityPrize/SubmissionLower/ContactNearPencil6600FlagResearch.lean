import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactNearPencil6600ArithmeticResearch

/-!
# Exact variable-degree flag identities for the 66.00 route

This module ties the residual agreement flag proved from the actual global
substitution to the quadratic and linear mixed coefficients used by the
stratified-incidence ledger.  The identities hold for arbitrary residual
degrees `d,e`; they are not numerical samples at `w`.
-/

namespace ProximityPrize.SubmissionLower.ContactNearPencil6600FlagResearch

open ContactFlagBezout6543Research
open ContactIdentityResidualGlobalFlagResearch
open ContactNearPencil6600ArithmeticResearch

/-- Surface flag for `(errors,m,s,L)=(78777,24,8,576)`. -/
def surfaceFlag6600 : FlagDegree := ⟨460, 35, 8⟩

/-- Derivative flag after one derivative in the residual `R` coordinate. -/
def derivativeFlag6600 : FlagDegree := ⟨460, 35, 7⟩

/-- One contact-recurrence order contributes the surface plus derivative
flags. -/
def agreementDirection6600 : FlagDegree := ⟨920, 70, 15⟩

theorem agreementDirection6600_eq :
    agreementDirection6600 = surfaceFlag6600 + derivativeFlag6600 := by
  rfl

theorem residualAgreementFlag_eq_affine (d : ℕ) :
    residualAgreementFlag d =
      unitYZFlag + d • agreementDirection6600 := by
  change (⟨920 * d, 1 + 70 * d, 15 * d⟩ : FlagDegree) =
    (⟨0 + d * 920, 1 + d * 70, 0 + d * 15⟩ : FlagDegree)
  congr 1 <;> omega

/-- Exact bilinear expansion of the whole proper-intersection cost. -/
theorem flagMixed_residualAgreementFlag
    (d e : ℕ) :
    flagMixed surfaceFlag6600 (residualAgreementFlag d)
        (residualAgreementFlag e) =
      mixedQuadratic * d * e + mixedLinear * (d + e) + mixedUnit := by
  norm_num [flagMixed, surfaceFlag6600, residualAgreementFlag,
    mixedQuadratic, mixedLinear, mixedUnit]
  ring

/-- Exact affine expansion of the exceptional `Z` projection cost. -/
theorem flagMixed_residualAgreementFlag_unitZ (d : ℕ) :
    flagMixed surfaceFlag6600 (residualAgreementFlag d) unitZFlag =
      zLinear * d + zUnit := by
  norm_num [flagMixed, surfaceFlag6600, residualAgreementFlag, unitZFlag,
    zLinear, zUnit]
  ring

theorem flagMixed_direction_values :
    flagMixed surfaceFlag6600 agreementDirection6600 agreementDirection6600 =
        mixedQuadratic ∧
      flagMixed surfaceFlag6600 agreementDirection6600 unitYZFlag =
        mixedLinear ∧
      flagMixed surfaceFlag6600 unitYZFlag unitYZFlag = mixedUnit ∧
      flagMixed surfaceFlag6600 agreementDirection6600 unitZFlag = zLinear ∧
      flagMixed surfaceFlag6600 unitYZFlag unitZFlag = zUnit := by
  norm_num [flagMixed, surfaceFlag6600, agreementDirection6600,
    unitYZFlag, unitZFlag, mixedQuadratic, mixedLinear, mixedUnit,
    zLinear, zUnit]

end ProximityPrize.SubmissionLower.ContactNearPencil6600FlagResearch
