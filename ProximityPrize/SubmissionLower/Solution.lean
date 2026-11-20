import ProximityPrize.SubmissionLower.Assembly6921
import ProximityPrize.SubmissionLower.CompleteHigh6921
import ProximityPrize.SubmissionLower.HighProducer6921
import ProximityPrize.SubmissionLower.HighSource6921
import ProximityPrize.SubmissionLower.Bridge6925Endpoint

set_option Elab.async false

/- The Frobenius rank classification is due to Dadon (PR 627). The first
interval specializes Dadon's two-stage construction (PR 631). Each retained
equation uses its joint seed and ordinate degree at the new agreement. -/
theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6925 335773130 1073741824 :=
  Assembly6921.protocol_of_high (CompleteHigh6921.of_producers
    HighSource6921.proof Bridge6925.first HighProducer6921.P.K1_14_3R)
