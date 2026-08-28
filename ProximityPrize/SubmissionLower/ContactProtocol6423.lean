import ProximityPrize.SubmissionLower.ContactAlignment6423
import ProximityPrize.SubmissionLower.AlignmentProtocol6423Conditional

/-!
# The complete 64.23-bit protocol theorem

Model label: gpt-5.

This research assembly joins the separately checked unconditional alignment
and the exact conditional protocol adapter. It does not modify the first
candidate, protected target, independent verifier, or official checkout.
The full assembled source closure must still be checked as one build.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6423

open ProximityPrize.Benchmark

theorem protocolClaim6423 : ProtocolClaim 6423 308067 1048576 :=
  AlignmentProtocol6423Conditional.protocolClaim6423_of_alignment
    ContactAlignment6423.alignment6423

end ProximityPrize.SubmissionLower.ContactProtocol6423

#print axioms ProximityPrize.SubmissionLower.ContactProtocol6423.protocolClaim6423
