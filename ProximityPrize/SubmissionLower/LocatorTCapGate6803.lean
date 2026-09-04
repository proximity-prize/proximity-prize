import ProximityPrize.SubmissionLower.LocatorCapArithmetic6803
import ProximityPrize.SubmissionLower.LocatorSelectionArithmetic6803

/-! The isolated TCap positive-nullity gate. -/

namespace ProximityPrize.SubmissionLower.LocatorTCapGate6803

open ProximityPrize.Benchmark RCN100 RCN119

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

theorem gateTCap :
    Fintype.card IRSProfile.Index * localRankBound 181 6679 56 <
      coefficientCount 32826703 131071 6679 56 := by
  rw [LocatorCapArithmetic6803.index_card]
  simpa only [LocatorSelectionArithmetic6803.weightedTCap] using
    LocatorSelectionArithmetic6803.kernelTCap_gate

end ProximityPrize.SubmissionLower.LocatorTCapGate6803
