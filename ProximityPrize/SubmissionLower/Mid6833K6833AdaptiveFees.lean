/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Adaptive interval certificates for 68.33. After Lucieno, BitWonka and Bome2017. -/
import ProximityPrize.SubmissionLower.Mid6833K6833Fee0
import ProximityPrize.SubmissionLower.Mid6833K6833Fee1
import ProximityPrize.SubmissionLower.Mid6833K6833Fee2
import ProximityPrize.SubmissionLower.Mid6833K6833Fee3
import ProximityPrize.SubmissionLower.Mid6833K6833Fee4
namespace ProximityPrize.SubmissionLower.K6833AdaptiveCert
open RCN095 RCN130 RCN263 RCN275 LocatorFactorAggregate
open K6833FlowSources K6833FlowStages K6833FlowPaid Koala6831MovingPairIncidence Koala6831MovingLedger
open Lower80899.ThresholdFast (evalPowerBandBudget evalPowerBandBudget_eq)
set_option autoImplicit false
set_option maxRecDepth 100000
theorem fee_bound (j : Fin 5) (f : FlagDegree) (hpos : 0<f.all)
    (hcap : Below f primaryIncoming) (hprior : Prior j.val f) :
    stagePrice f hpos (capStage j) (capStage j).numbers.slopeCap ≤ fee j := by
  have r : f.all≤98 := hcap.1
  have y : middle f≤440 := hcap.2.1
  have t : total f≤53215 := hcap.2.2
  have p : 1≤middle f := hpos.trans_le (Nat.le_add_left _ _)
  fin_cases j
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee0 (by decide) hpos r p y
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee1 (by decide) hpos r p y
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee2 (by decide) hpos r p y
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee3 (by decide) hpos r p y
  · exact cost_of_tile _ f hpos t hprior _ _ _ _ _ checkedFee4 (by decide) hpos r p y
#print axioms fee_bound
end ProximityPrize.SubmissionLower.K6833AdaptiveCert
