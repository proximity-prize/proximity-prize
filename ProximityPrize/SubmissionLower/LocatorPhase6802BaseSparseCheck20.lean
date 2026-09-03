import ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck19

namespace ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck20

open LocatorPhaseBaseSparseCoreC2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 20 := by
  decide +kernel

theorem shape : CachedShapeLayer 20 := by
  decide +kernel

#print axioms sparse
#print axioms shape

end ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck20
