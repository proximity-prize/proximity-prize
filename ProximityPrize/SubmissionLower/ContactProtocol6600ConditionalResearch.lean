import ProximityPrize.SubmissionLower.ContactFrozenAlignment6600Research
import ProximityPrize.SubmissionLower.AlignmentProtocol6600ConditionalResearch

/-!
# Solution-shaped score-66 endpoint

This joins the entire frozen interpolation/alignment/protocol frontend.  Its
only premise is the global selected-family counting proposition; once the
regular-factor geometry proves that proposition, the conclusion can be used
verbatim as the submission's `candidate` theorem.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6600ConditionalResearch

open ProximityPrize.Benchmark

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- A `Solution.lean`-compatible score-66 claim conditional only on the
remaining global selected-family count. -/
theorem protocolClaim6600_of_global_count_lt_alignment
    (global_count_lt_alignment :
      ContactFrozenAlignment6600Research.GlobalCountLtAlignment6600) :
    ProtocolClaim 6621 315947 1048576 := by
  have halign : AffineLineAlignmentBound IRSProfile.baseCode
      ContactParameters6600Research.errors
      ContactParameters6600Research.alignmentBudget :=
    ContactFrozenAlignment6600Research.alignment_of_global_count_lt_alignment6600
      global_count_lt_alignment
  exact AlignmentProtocol6600ConditionalResearch.protocolClaim6600_of_alignment
    halign

end ProximityPrize.SubmissionLower.ContactProtocol6600ConditionalResearch

#print axioms ProximityPrize.SubmissionLower.ContactProtocol6600ConditionalResearch.protocolClaim6600_of_global_count_lt_alignment
