import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck12

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck16

open LocatorPhase6800BaseSparseCore

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 16 := by
  decide +kernel

theorem shape : CachedShapeLayer 16 := by
  decide +kernel

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck16
