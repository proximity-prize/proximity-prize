import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCore

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck04

open LocatorPhase6800BaseSparseCore

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 4 := by
  decide +kernel

theorem shape : CachedShapeLayer 4 := by
  decide +kernel

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck04
