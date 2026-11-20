import ProximityPrize.SubmissionLower.Cell82005
import ProximityPrize.SubmissionLower.Assembly6921
import ProximityPrize.SubmissionLower.CompleteHigh6921
import ProximityPrize.SubmissionLower.HighProducer6921
import ProximityPrize.SubmissionLower.HighSource6921
import ProximityPrize.SubmissionLower.Bridge6925Endpoint

set_option Elab.async false

/- Dadon's PR 627 supplies the Frobenius rank classification. The first
interval extends the PR 631 cover to reserves 0, 6 and 25. The physical
count shares the anchor degree between its leading coefficient and factors. -/
theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6928 2885329617516738934 9223372036854718083 :=
  ProximityPrize.SubmissionLower.Cell82005.extend
    (Assembly6921.protocol_of_high (CompleteHigh6921.of_producers
      HighSource6921.proof Bridge6925.first HighProducer6921.P.K1_14_3R))
