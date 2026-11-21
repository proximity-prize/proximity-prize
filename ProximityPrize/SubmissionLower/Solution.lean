import ProximityPrize.SubmissionLower.FrontAssembly82200
import ProximityPrize.SubmissionLower.Low48GeometryFinish
import ProximityPrize.SubmissionLower.KoalaHigh6951

theorem ProximityPrize.Benchmark.candidate :
    ProximityPrize.Benchmark.ProtocolClaim 6951 2893210916864619832 9223372036854662547 := by
  apply Front82200.of_core_counts_at_maximal_radius
  · intro _ _ M _ F lo hi
    exact (Low48Geometry.count M F lo hi).trans (by decide)
  · intro _ _ M _ F lo hi
    exact KoalaHigh6951.count M F lo hi

#print axioms ProximityPrize.Benchmark.candidate
