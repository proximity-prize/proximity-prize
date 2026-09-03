import ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck23

namespace ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck27

open LocatorPhase6800BaseSparseCore

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 27 := by
  decide +kernel

theorem shape : CachedShapeLayer 27 := by
  decide +kernel

end ProximityPrize.SubmissionLower.LocatorPhase6800BaseSparseCheck27
