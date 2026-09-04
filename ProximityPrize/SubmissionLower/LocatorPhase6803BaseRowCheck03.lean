import ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck02

namespace ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck03

open LocatorPhase6803BaseDirectAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked : CandidateRCheck #[] 3 := by native_decide

end ProximityPrize.SubmissionLower.LocatorPhase6803BaseRowCheck03
