import ProximityPrize.SubmissionLower.R6960MarkedProtocol
import ProximityPrize.SubmissionLower.Gate61Table

theorem ProximityPrize.Benchmark.candidate : ProximityPrize.Benchmark.ProtocolClaim 6961 2896623800957216602 9223372036854599207 :=
  Lower6960.MarkedEvaluation.candidate_of_gates Gate61Fin.gates

#print axioms ProximityPrize.Benchmark.candidate
