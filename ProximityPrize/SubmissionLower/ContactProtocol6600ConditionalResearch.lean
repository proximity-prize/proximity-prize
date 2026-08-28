import ProximityPrize.SubmissionLower.ContactFrozenAlignment6600Research
import ProximityPrize.SubmissionLower.AlignmentProtocol6600ConditionalResearch

namespace ProximityPrize.SubmissionLower.ContactProtocol6600ConditionalResearch

open ProximityPrize.Benchmark

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem protocolClaim6600_of_global_count_lt_alignment
    (global_count_lt_alignment :
      ContactFrozenAlignment6600Research.GlobalCountLtAlignment6600) :
    ProtocolClaim 6619 315871 1048576 := by
  have halign : AffineLineAlignmentBound IRSProfile.baseCode
      ContactParameters6600Research.errors
      ContactParameters6600Research.alignmentBudget :=
    ContactFrozenAlignment6600Research.alignment_of_global_count_lt_alignment6600
      global_count_lt_alignment
  exact AlignmentProtocol6600ConditionalResearch.protocolClaim6600_of_alignment
    halign

end ProximityPrize.SubmissionLower.ContactProtocol6600ConditionalResearch
