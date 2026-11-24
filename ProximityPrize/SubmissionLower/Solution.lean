import ProximityPrize.SubmissionLower.R6960MarkedProtocol
import ProximityPrize.SubmissionLower.Gate61Table

theorem ProximityPrize.Benchmark.candidate : ProximityPrize.Benchmark.ProtocolClaim 6962 2896975644678137418 9223372036854702689 :=
  Lower6960.MarkedEvaluation.candidate_of_gates Gate61Fin.gates

#print axioms ProximityPrize.Benchmark.candidate
