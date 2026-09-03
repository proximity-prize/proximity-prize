import ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck15

namespace ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck16

open LocatorPhaseBaseSparseCoreC2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sparse : CachedSparseLayer 16 := by
  decide +kernel

theorem shape : CachedShapeLayer 16 := by
  decide +kernel

#print axioms sparse
#print axioms shape

end ProximityPrize.SubmissionLower.LocatorPhase6802BaseSparseCheck16
