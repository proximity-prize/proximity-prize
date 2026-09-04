import ProximityPrize.SubmissionLower.LocatorCapArithmetic6803
import ProximityPrize.SubmissionLower.LocatorSelectionArithmetic6803

/-! The isolated B-profile positive-nullity gate. -/

namespace ProximityPrize.SubmissionLower.LocatorCapsBGate6803

open ProximityPrize.Benchmark RCN100 RCN119

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

theorem gateB :
    Fintype.card IRSProfile.Index * localRankBound 111 14261 34 <
      coefficientCount 20131293 131071 14261 34 := by
  rw [LocatorCapArithmetic6803.index_card]
  simpa only [LocatorSelectionArithmetic6803.weightedB] using
    LocatorSelectionArithmetic6803.kernelB_gate

end ProximityPrize.SubmissionLower.LocatorCapsBGate6803
