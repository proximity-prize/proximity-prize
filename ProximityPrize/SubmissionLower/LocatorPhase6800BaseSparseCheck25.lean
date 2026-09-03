import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck21

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck25

open LocatorPhase6800BaseSparseCore

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 25 := by
  decide +kernel

theorem shape : CachedShapeLayer 25 := by
  decide +kernel

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck25
