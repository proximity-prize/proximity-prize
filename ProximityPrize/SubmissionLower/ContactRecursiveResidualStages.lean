import ProximityPrize.SubmissionLower.ContactProperCutSeedCount
import ProximityPrize.SubmissionLower.ContactStackedParameters
import ProximityPrize.SubmissionLower.ContactTightSingularLedger

namespace ProximityPrize.SubmissionLower.ContactRecursiveResidualStages

open scoped BigOperators
open ContactTightSingularLedger
open ContactParameters
open ContactSingularLedger

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

structure UnequalParameters where
  n : ℕ
  w : ℕ
  a : ℕ
  leftY : ℕ
  leftR : ℕ
  leftZ : ℕ
  rightY : ℕ
  rightR : ℕ
  rightZ : ℕ
  deriving DecidableEq

namespace UnequalParameters

def errors (P : UnequalParameters) : ℕ := P.n - P.a
def gap (P : UnequalParameters) : ℕ := P.a - P.w

def leftAgreement (P : UnequalParameters) : ContactParameters.DegreeVector :=
  ⟨1 + 2 * P.w * P.leftY,
    P.w * (2 * P.leftR - 1),
    2 * P.w * P.leftZ + 1⟩

def rightAgreement (P : UnequalParameters) : ContactParameters.DegreeVector :=
  ⟨1 + 2 * P.w * P.rightY,
    P.w * (2 * P.rightR - 1),
    2 * P.w * P.rightZ + 1⟩

def agreement (P : UnequalParameters) : ContactParameters.DegreeVector :=
  ⟨max P.leftAgreement.y P.rightAgreement.y,
    max P.leftAgreement.r P.rightAgreement.r,
    max P.leftAgreement.z P.rightAgreement.z⟩

def mixedCost (P : UnequalParameters) : ContactParameters.DegreeVector :=
  ⟨P.leftR * P.rightZ + P.leftZ * P.rightR,
    P.leftY * P.rightZ + P.leftZ * P.rightY,
    P.leftY * P.rightR + P.leftR * P.rightY⟩

def regularNumerator (P : UnequalParameters) : ℕ :=
  (P.n - P.w) * dot P.agreement P.mixedCost +
    (P.errors + 1) * P.gap * P.mixedCost.z

def regularCountCap (P : UnequalParameters) : ℕ := P.regularNumerator / P.gap

theorem regular_count_le (P : UnequalParameters) (count : ℕ)
    (hgap : 0 < P.gap) (hcount : count * P.gap ≤ P.regularNumerator) :
    count ≤ P.regularCountCap :=
  (Nat.le_div_iff_mul_le hgap).mpr hcount

end UnequalParameters

end ProximityPrize.SubmissionLower.ContactRecursiveResidualStages
