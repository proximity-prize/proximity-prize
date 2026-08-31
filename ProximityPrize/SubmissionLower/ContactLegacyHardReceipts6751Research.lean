import ProximityPrize.SubmissionLower.ContactLegacyNonbasicArithmetic6750Research

namespace ProximityPrize.SubmissionLower.ContactLegacyHardReceipts6751Research

open ContactAnchoredHardCellSelector6750Research
open ContactOrdinaryHardShell6750Research
open ContactRouterCellCosts6750Research
open ContactLegacyNonbasicArithmetic6750Research

set_option autoImplicit false
set_option maxHeartbeats 50000000
set_option maxRecDepth 50000

def hardQuotientD (y r : Nat) : Nat :=
  max 131072 (8729952 - (131071 * y - r))

def hardPureZeroCost (y r : Nat) : Nat :=
  cellRegularCost 3 3 2 +
    (cellTightProfile (hardQuotientD y r) 3 2).countCap

def hardPurePositiveBoundaryCost (y r : Nat) : Nat :=
  (cellTightProfile (hardQuotientD y r) (1692 - hardMinT y r) 1).countCap

theorem hardPureAndThirdBoundaryReceipt :
    ∀ (y : Fin 66) (r : Fin 15),
      OrdinaryHardCell (hardMinT y.1 r.1) y.1 r.1 →
      hardPureZeroCost y.1 r.1 ≤
          ContactRouterUniformCaps6750Research.hardThirdCap ∧
        hardPurePositiveBoundaryCost y.1 r.1 ≤
          ContactRouterUniformCaps6750Research.hardThirdCap ∧
        nonBasicThirdCost (hardMinT y.1 r.1) y.1 r.1 ≤
          ContactRouterUniformCaps6750Research.hardThirdCap := by
  unfold OrdinaryHardCell
  decide

end ProximityPrize.SubmissionLower.ContactLegacyHardReceipts6751Research
