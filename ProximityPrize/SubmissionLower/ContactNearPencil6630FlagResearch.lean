import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research
import ProximityPrize.SubmissionLower.ContactNearPencil6630ArithmeticResearch

/-!
# Exact variable-degree flag identities for score 66.75

The sharp surface flag is obtained from the cumulative nested caps
`all <= 10`, `yz+all <= 48`, and `z+yz+all <= 825`.
-/

namespace ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch

open ContactFlagBezout6543Research
open ContactNearPencil6630ArithmeticResearch

def surfaceFlag6630 : FlagDegree := ⟨777, 38, 10⟩
def derivativeFlag6630 : FlagDegree := ⟨777, 38, 9⟩

/-- The reduced Taylor agreement numerator saves one slope degree while
preserving the sharp middle and total cumulative caps. Its nested direction
is `(2*(L-M), 2*(M-s), 2*s-2)`. -/
def agreementDirection6630 : FlagDegree := ⟨1554, 76, 18⟩

/-- The affine agreement flag associated to residual degree `d`. -/
def residualAgreementFlag6630 (d : ℕ) : FlagDegree :=
  unitYZFlag + d • agreementDirection6630

theorem residualAgreementFlag6630_value (d : ℕ) :
    residualAgreementFlag6630 d = ⟨1554 * d, 1 + 76 * d, 18 * d⟩ := by
  change (⟨0 + d * 1554, 1 + d * 76, 0 + d * 18⟩ : FlagDegree) =
    ⟨1554 * d, 1 + 76 * d, 18 * d⟩
  congr 1 <;> omega

theorem flagMixed_residualAgreementFlag6630 (d e : ℕ) :
    flagMixed surfaceFlag6630 (residualAgreementFlag6630 d)
        (residualAgreementFlag6630 e) =
      mixedQuadratic * d * e + mixedLinear * (d + e) + mixedUnit := by
  norm_num [flagMixed, surfaceFlag6630, residualAgreementFlag6630,
    agreementDirection6630, unitYZFlag, mixedQuadratic, mixedLinear,
    mixedUnit]
  ring

theorem flagMixed_residualAgreementFlag6630_unitZ (d : ℕ) :
    flagMixed surfaceFlag6630 (residualAgreementFlag6630 d) unitZFlag =
      zLinear * d + zUnit := by
  norm_num [flagMixed, surfaceFlag6630, residualAgreementFlag6630,
    agreementDirection6630, unitYZFlag, unitZFlag, zLinear, zUnit]
  ring

theorem flagMixed_residualAgreementFlag6630_unitYZ (d : ℕ) :
    flagMixed surfaceFlag6630 (residualAgreementFlag6630 d) unitYZFlag =
      mixedLinear * d + mixedUnit := by
  norm_num [flagMixed, surfaceFlag6630, residualAgreementFlag6630,
    agreementDirection6630, unitYZFlag, mixedLinear, mixedUnit]
  ring

theorem flagMixed_direction_values6630 :
    flagMixed surfaceFlag6630 agreementDirection6630 agreementDirection6630 =
        mixedQuadratic ∧
      flagMixed surfaceFlag6630 agreementDirection6630 unitYZFlag =
        mixedLinear ∧
      flagMixed surfaceFlag6630 unitYZFlag unitYZFlag = mixedUnit ∧
      flagMixed surfaceFlag6630 agreementDirection6630 unitZFlag = zLinear ∧
      flagMixed surfaceFlag6630 unitYZFlag unitZFlag = zUnit := by
  norm_num [flagMixed, surfaceFlag6630, agreementDirection6630,
    unitYZFlag, unitZFlag, mixedQuadratic, mixedLinear, mixedUnit,
    zLinear, zUnit]

end ProximityPrize.SubmissionLower.ContactNearPencil6630FlagResearch
