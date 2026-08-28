import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.AlignmentProtocol6630ConditionalResearch
import ProximityPrize.SubmissionLower.ContactGlobalAdaptiveAlignment6630Research

/-!
# Score-66.30 protocol endpoint from terminal adaptive YZ families

The terminal projection-family premise first gives the exact frozen global
count.  The frozen interpolation bridge turns that count into alignment, and
the row-specialized conditional certificate closes the protocol claim.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6630AdaptiveResearch

set_option autoImplicit false

open ProximityPrize.Benchmark
open ContactGlobalAdaptiveAlignment6630Research

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- A submission-shaped score-66.30 theorem whose sole premise is the
terminal adaptive YZ projection-family constructor. -/
theorem protocolClaim6630_of_terminal_projection_families
    (hprojection : FrozenTerminalAdaptiveProjectionFamiliesYZ6630) :
    ProtocolClaim 6630 316299 1048576 := by
  have hcount : ContactFrozenAlignment6630Research.GlobalCountLtAlignment6630 :=
    global_count_lt_alignment6630_of_terminal_projection_families hprojection
  have halign : AffineLineAlignmentBound IRSProfile.baseCode
      ContactParameters6630Research.errors
      ContactParameters6630Research.alignmentBudget :=
    ContactFrozenAlignment6630Research.alignment_of_global_count_lt_alignment6630
      hcount
  apply AlignmentProtocol6630ConditionalResearch.protocolClaim6630_of_alignment
  simpa only [AlignmentProtocol6630ConditionalResearch.errors6630,
    ContactScore6630Research.errors6630,
    ContactParameters6630Research.errors,
    AlignmentProtocol6630ConditionalResearch.budget6630,
    ContactParameters6630Research.alignmentBudget] using halign

end ProximityPrize.SubmissionLower.ContactProtocol6630AdaptiveResearch

#print axioms ProximityPrize.SubmissionLower.ContactProtocol6630AdaptiveResearch.protocolClaim6630_of_terminal_projection_families
