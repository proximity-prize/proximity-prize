import ProximityPrize.SubmissionLower.Z6970FullJoin
import ProximityPrize.SubmissionLower.Z6970Height2307Count

set_option Elab.async false

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6970 2899720025701049676 9223372036854649837 :=
  Research6970.FullJoin.candidate_of_native_low fun _ _ M _ F lo hi =>
    Height2307Count6970.family_count M F lo hi

#print axioms ProximityPrize.Benchmark.candidate
