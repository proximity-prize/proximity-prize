import ProximityPrize.SubmissionLower.AlignmentProtocol6670ConditionalResearch
import ProximityPrize.SubmissionLower.ContactAlignmentBridge

/-!
# Promoted-budget endpoint for the stacked 66.70 route

This module contains only the final selected-family-to-alignment adapter.  The
protocol endpoint remains conditional on the exact selected-family bound; no
geometric counting premise is introduced here.
-/

namespace ProximityPrize.SubmissionLower.ContactStackedPromotedEndpoint6670Research

open ProximityPrize.Benchmark
open ContactAlignmentBridge

/-- The exact selected-family bound feeds the stock alignment bridge and the
target-specific conditional 66.70 protocol endpoint. -/
theorem protocolClaim6670_of_selected_count
    (hcount : SelectedNoLargePencilBound IRSProfile.domain
      131071 79476 137490364055697543) :
    ProtocolClaim 6670 317907 1048576 := by
  apply AlignmentProtocol6670ConditionalResearch.protocolClaim6670
  change AffineLineAlignmentBound
    (ReedSolomon.code IRSProfile.domain (131071 + 1))
      79476 137490364055697543
  exact alignmentBound_of_selected_count IRSProfile.domain
    131071 79476 137490364055697543 hcount

end ProximityPrize.SubmissionLower.ContactStackedPromotedEndpoint6670Research

#print axioms ProximityPrize.SubmissionLower.ContactStackedPromotedEndpoint6670Research.protocolClaim6670_of_selected_count
