import ProximityPrize.SubmissionLower.Cell82073
import ProximityPrize.SubmissionLower.Assembly6921
import ProximityPrize.SubmissionLower.CompleteHigh6921
import ProximityPrize.SubmissionLower.HighProducer6921
import ProximityPrize.SubmissionLower.HighSource6921
import ProximityPrize.SubmissionLower.Bridge6925Endpoint

set_option Elab.async false

/- The two-pole source uses joint projective grades and certified
up to 128-by-128 rectangles. The anchored cover tests reserves 0, 6 and 25. -/
theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6935 2887722154818789274 9223372036854749317 :=
  ProximityPrize.SubmissionLower.Cell82073.extend
    (Assembly6921.protocol_of_high (CompleteHigh6921.of_producers
      HighSource6921.proof Bridge6925.first HighProducer6921.P.K1_14_3R))
