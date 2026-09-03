import ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck16

namespace ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck17

open LocatorPhaseBaseSparseCoreC2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 17 := by
  decide +kernel

theorem shape : CachedShapeLayer 17 := by
  decide +kernel

#print axioms sparse
#print axioms shape

end ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck17
