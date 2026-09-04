import ProximityPrize.SubmissionLower.LocatorCapArithmetic6803
import ProximityPrize.SubmissionLower.LocatorSelectionArithmetic6803

/-! The isolated A-profile positive-nullity gate. -/

namespace ProximityPrize.SubmissionLower.LocatorCapsAGate6803

open ProximityPrize.Benchmark RCN100 RCN119

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

theorem gateA : Fintype.card IRSProfile.Index * localRankBound 98 130000 29 <
    coefficientCount 17773574 131071 130000 29 := by
  rw [LocatorCapArithmetic6803.index_card]
  simpa only [LocatorSelectionArithmetic6803.weightedA] using
    LocatorSelectionArithmetic6803.kernelA_gate

end ProximityPrize.SubmissionLower.LocatorCapsAGate6803
