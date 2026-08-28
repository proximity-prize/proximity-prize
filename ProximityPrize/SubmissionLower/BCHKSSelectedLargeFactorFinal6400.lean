import ProximityPrize.SubmissionLower.BCHKSAlignmentRepeatedInterface6400
import ProximityPrize.SubmissionLower.BCHKSFinal6400

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark

/-- The entire score-64 claim is reduced to the explicitly stated
degree-at-least-115 selected-factor alignment problem. -/
theorem alignmentBound6400_of_selectedLargeFactorAlignment
    (hlarge : BCHKSSelectedLargeFactorAlignment6400) :
    AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400 :=
  alignmentBound6400_of_polynomialAlignment
    (polynomialAlignment6400_of_selectedLargeFactorAlignment hlarge)

/-- After the strict factor-specific low-identity closure, only the
degree-at-least-115 high-identity branch is required. -/
theorem alignmentBound6400_of_selectedLargeFactorHighIdentityAlignment
    (hhigh : BCHKSSelectedLargeFactorHighIdentityAlignment6400) :
    AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400 :=
  alignmentBound6400_of_selectedLargeFactorAlignment
    (selectedLargeFactorAlignment6400_of_highIdentity hhigh)

/-- Low identity and the large simple-root locus have both been discharged;
only the explicitly selected repeated-coordinate branch remains. -/
theorem alignmentBound6400_of_selectedLargeFactorRepeatedAlignment
    (hrepeated : BCHKSSelectedLargeFactorRepeatedAlignment6400) :
    AffineLineAlignmentBound IRSProfile.baseCode
      bchksErrors6400 bchksNumerator6400 :=
  alignmentBound6400_of_selectedLargeFactorHighIdentityAlignment
    (selectedLargeFactorHighIdentityAlignment6400_of_repeated hrepeated)

end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

/-- Conditional end-to-end score-64 certificate.  The hypothesis is exactly
the sole large-degree branch left open by the fixed-factor ledger. -/
theorem protocolClaim6400_of_selectedLargeFactorAlignment
    (hlarge :
      ProximityPrize.SubmissionLower.BCHKSSelectedLargeFactorAlignment6400) :
    ProtocolClaim 6400 307121 1048576 :=
  protocolClaim6400_of_alignment
    (ProximityPrize.SubmissionLower.alignmentBound6400_of_selectedLargeFactorAlignment
      hlarge)

/-- Conditional end-to-end certificate with the low-identity branch removed
from the remaining hypothesis. -/
theorem protocolClaim6400_of_selectedLargeFactorHighIdentityAlignment
    (hhigh :
      ProximityPrize.SubmissionLower.BCHKSSelectedLargeFactorHighIdentityAlignment6400) :
    ProtocolClaim 6400 307121 1048576 :=
  protocolClaim6400_of_alignment
    (ProximityPrize.SubmissionLower.alignmentBound6400_of_selectedLargeFactorHighIdentityAlignment
      hhigh)

/-- Conditional end-to-end certificate whose hypothesis is exactly the
large-degree repeated-coordinate residual. -/
theorem protocolClaim6400_of_selectedLargeFactorRepeatedAlignment
    (hrepeated :
      ProximityPrize.SubmissionLower.BCHKSSelectedLargeFactorRepeatedAlignment6400) :
    ProtocolClaim 6400 307121 1048576 :=
  protocolClaim6400_of_alignment
    (ProximityPrize.SubmissionLower.alignmentBound6400_of_selectedLargeFactorRepeatedAlignment
      hrepeated)

end ProximityPrize.Benchmark
