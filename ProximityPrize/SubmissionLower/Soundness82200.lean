import ProximityPrize.SubmissionLower.FrontAssembly82200
import ProximityPrize.SubmissionLower.Low48GeometryFinish
import ProximityPrize.SubmissionLower.HighCore82200Finish

namespace Soundness82200
open ProximityPrize.Benchmark

theorem protocol :
    ProtocolClaim 6948 2892190570074008202 9223372036854549289 :=
  Front82200.of_core_counts_at_maximal_radius
    (fun _ _ M _ F lo hi => Low48Geometry.count M F lo hi)
    (fun _ _ M _ F lo hi => HighCore82200.ordinary_high M F lo hi)

#print axioms protocol
end Soundness82200
