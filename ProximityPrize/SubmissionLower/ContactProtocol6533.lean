import ProximityPrize.SubmissionLower.ContactAlignment6533
import ProximityPrize.SubmissionLower.AlignmentProtocol6533Conditional

/-!
# Complete 65.67-bit protocol theorem

This final assembly joins the unconditional 78,455-error alignment theorem
to the independently checked radius and protocol adapter.
-/

namespace ProximityPrize.SubmissionLower.ContactProtocol6533

open ProximityPrize.Benchmark

theorem protocolClaim6533 : ProtocolClaim 6567 313823 1048576 :=
  AlignmentProtocol6533Conditional.protocolClaim6533_of_alignment
    ContactAlignment6533.alignment6533

end ProximityPrize.SubmissionLower.ContactProtocol6533
