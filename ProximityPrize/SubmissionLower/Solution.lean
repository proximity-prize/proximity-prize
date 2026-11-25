import ProximityPrize.SubmissionLower.R6962B1HighCount
import ProximityPrize.SubmissionLower.Gate61Table
set_option Elab.async false

theorem ProximityPrize.Benchmark.candidate : ProximityPrize.Benchmark.ProtocolClaim 6962 2896975644678137418 9223372036854702689 :=
  Lower6962.B1.HighCount.candidate_of_gates Gate61Fin.gates

#print axioms ProximityPrize.Benchmark.candidate
