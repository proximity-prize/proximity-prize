import ProximityPrize.SubmissionLower.R6960RetainedCompressionPureNodes
import ProximityPrize.SubmissionLower.R6960RetainedCompressionDiscriminant
import ProximityPrize.SubmissionLower.R6960Front6960Assembly

set_option Elab.async false
namespace Lower6960

/-- The 69.60 claim reduces to the remaining bounded-weight,
positive-seed, nonpure marked-factor estimate. -/
theorem protocol_claim_of_nonpure (count : RetainedCompression.NonPureFactorPrice) :
    ProximityPrize.Benchmark.ProtocolClaim 6960
      ProximityPrize.SubmissionLower.Front6960Radius.p
      ProximityPrize.SubmissionLower.Front6960Radius.q :=
  protocol_claim_of_retained (RetainedCompression.retained_of_nonpure count)

#print axioms protocol_claim_of_nonpure
end Lower6960
