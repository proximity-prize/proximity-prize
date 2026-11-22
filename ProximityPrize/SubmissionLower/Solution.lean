import ProximityPrize.SubmissionLower.FrontAssembly82200
import ProximityPrize.SubmissionLower.KoalaWeightedProof
import ProximityPrize.SubmissionLower.KoalaLow6954
import ProximityPrize.SubmissionLower.KoalaHigh6954

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6954 2894231263655162954 9223372036854557403 := by
  apply Front82200.of_core_counts_at_maximal_radius
  · intro _ _ M _ F lo hi
    exact KoalaLow6954.count_with
      (fun w Γ s => @KoalaWeightedProof.count w Γ s) M F lo hi
  · intro _ _ M _ F lo hi
    exact KoalaHigh6954.count M F lo hi

#print axioms ProximityPrize.Benchmark.candidate
