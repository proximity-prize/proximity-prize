import ProximityPrize.SubmissionLower.Assembly6921
import ProximityPrize.SubmissionLower.CompleteHigh6921
import ProximityPrize.SubmissionLower.HighProducer6921
import ProximityPrize.SubmissionLower.HighSource6921
import ProximityPrize.SubmissionLower.Bridge6925Endpoint

set_option Elab.async false

/- The two-pole source uses joint projective grades and certified
four-by-four savings. The anchored cover tests reserves 0, 6 and 25. -/
theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6930 335972916 1073741824 :=
  Assembly6921.protocol_of_high (CompleteHigh6921.of_producers
    HighSource6921.proof Bridge6925.first HighProducer6921.P.K1_14_3R)
