import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck22

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck26

open LocatorPhase6800BaseSparseCore

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 26 := by
  decide +kernel

theorem shape : CachedShapeLayer 26 := by
  decide +kernel

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck26
