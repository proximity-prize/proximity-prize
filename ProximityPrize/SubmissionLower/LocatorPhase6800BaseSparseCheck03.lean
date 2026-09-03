import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCore

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck03

open LocatorPhase6800BaseSparseCore

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 3 := by
  decide +kernel

theorem shape : CachedShapeLayer 3 := by
  decide +kernel

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck03
