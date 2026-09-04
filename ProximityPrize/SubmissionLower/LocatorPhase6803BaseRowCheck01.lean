import ProximityPrize.SubmissionLower.LocatorPhase6803BaseDirectAudit

namespace ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck01

open LocatorPhase6803BaseDirectAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked : CandidateRCheck #[] 1 := by native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck01

