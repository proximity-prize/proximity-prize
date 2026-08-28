import ProximityPrize.SubmissionLower.ContactAlignment6401
import ProximityPrize.SubmissionLower.AlignmentProtocol6401Conditional

/-!
# The complete 65.04-bit protocol theorem

Model label: gpt-5.

This assembly joins the separately checked unconditional alignment
and the exact conditional protocol adapter. It does not modify the first
candidate, protected target, independent verifier, or official checkout.
The full assembled source closure is checked as one build.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6401

open ProximityPrize.Benchmark

theorem protocolClaim6401 : ProtocolClaim 6568 313851 1048576 :=
  AlignmentProtocol6401Conditional.protocolClaim6401_of_alignment
    ContactAlignment6401.alignment6401

end ProximityPrize.SubmissionLower.ContactProtocol6401

#print axioms ProximityPrize.SubmissionLower.ContactProtocol6401.protocolClaim6401
