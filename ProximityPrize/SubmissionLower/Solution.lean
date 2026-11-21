import ProximityPrize.SubmissionLower.KoalaSoundness6950
import ProximityPrize.SubmissionLower.KoalaTwoCutProof

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6950 2892859073143766509 9223372036854774115 :=
  KoalaSoundness6950.of_two_cut SplitCut.TwoCut.two_cut_count

#print axioms ProximityPrize.Benchmark.candidate
