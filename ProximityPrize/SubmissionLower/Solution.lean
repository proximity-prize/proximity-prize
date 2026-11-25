import ProximityPrize.SubmissionLower.R6960MarkedProtocol
import ProximityPrize.SubmissionLower.Gate61Table
import ProximityPrize.SubmissionLower.R6963LoHighCount

theorem ProximityPrize.Benchmark.candidate : ProximityPrize.Benchmark.ProtocolClaim 6963 2897327488399042352 9223372036854755587 :=
  Lower6960.MarkedEvaluation.candidate_of_gates Gate61Fin.gates
    (fun M F l h => Lower6961.lo_band_count_6963 M F l h)

#print axioms ProximityPrize.Benchmark.candidate
