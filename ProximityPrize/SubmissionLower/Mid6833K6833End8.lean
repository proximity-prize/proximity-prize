/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
import ProximityPrize.SubmissionLower.Mid6833K6833End7
import ProximityPrize.SubmissionLower.Mid6833K6833AdaptiveEndBase
namespace ProximityPrize.SubmissionLower.K6833AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open K6833FlowSources K6833FlowStages K6833FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000000 in
theorem checkedEnd8 : checkedRank 8=true := by decide +kernel
end ProximityPrize.SubmissionLower.K6833AdaptiveCert
