import ProximityPrize.SubmissionLower.LocatorResidualGrouped6803
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptCore

/-! Identification of the geometric residual components with the checked
receipt's residual charge at the same retained flag. -/

namespace ProximityPrize.SubmissionLower.LocatorResidualCharge6803

open RCN095
open LocatorFactorAggregate LocatorRetainedQuotient6803

set_option autoImplicit false

theorem residual_components_eq_receipt (p : FlagDegree) :
    (LocatorResidualRegular6803.residualPairStage p).regularCountCap +
        (LocatorGroupedNonRegularCardinality6803.residualBGroupedStage p).regularCountCap +
      LocatorGroupedNonRegularCardinality6803.residualBMaxEscapeDot +
        (LocatorResidualGrouped6803.residualBExactTailStage p).countCap =
      LocatorPhase6803ReceiptCore.residualCharge p.all p.yz p.zOnly := by
  have hpair : LocatorResidualRegular6803.residualPairStage p =
      LocatorPhase6803ReceiptCore.residualPairStage p.all p.yz p.zOnly := by
    cases p
    simp only [LocatorResidualRegular6803.residualPairStage,
      LocatorPhase6803ReceiptCore.residualPairStage,
      LocatorRetainedQuotient6803.middle,
      LocatorRetainedQuotient6803.total]
    congr 1 <;> omega
  have hgroup : LocatorGroupedNonRegularCardinality6803.residualBGroupedStage p =
      LocatorPhase6803ReceiptCore.residualGroupedStage p.all p.yz p.zOnly := by
    cases p
    simp only [LocatorGroupedNonRegularCardinality6803.residualBGroupedStage,
      LocatorGroupedNonRegularCardinality6803.adjacentGroupedStage,
      LocatorPhase6803ReceiptCore.residualGroupedStage,
      LocatorRetainedQuotient6803.middle,
      LocatorRetainedQuotient6803.total]
    congr 1 <;> omega
  have htail : LocatorResidualGrouped6803.residualBExactTailStage p =
      LocatorPhase6803ReceiptCore.residualTailStage p.all p.yz p.zOnly := by
    cases p
    simp only [LocatorResidualGrouped6803.residualBExactTailStage,
      LocatorPhase6803ReceiptCore.residualTailStage, retainedContact,
      LocatorRetainedQuotient6803.middle,
      LocatorRetainedQuotient6803.total]
    congr 1 <;> omega
  rw [hpair, hgroup, htail,
    LocatorGroupedNonRegularCardinality6803.residualBMaxEscapeDot_exact]
  simp only [LocatorPhase6803ReceiptCore.residualCharge,
    LocatorPhase6803ReceiptCore.residualBMaxEscapeDot]

end ProximityPrize.SubmissionLower.LocatorResidualCharge6803
