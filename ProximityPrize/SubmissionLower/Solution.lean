import ProximityPrize.SubmissionLower.R6960MonicChartActual
import ProximityPrize.SubmissionLower.R6961Front6961HighCount
import ProximityPrize.SubmissionLower.Gate61Table

set_option Elab.async false

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6962 2896975644678137418 9223372036854702689 :=
  Lower6960.protocol_claim Gate61Fin.gates (fun M F lo hi => Lower6961.high_count M F lo hi)

#print axioms ProximityPrize.Benchmark.candidate
