import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck11

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck15

open LocatorPhase6800BaseSparseCore

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 15 := by
  decide +kernel

theorem shape : CachedShapeLayer 15 := by
  decide +kernel

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck15
