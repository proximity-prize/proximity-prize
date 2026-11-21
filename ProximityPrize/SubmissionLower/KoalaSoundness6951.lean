import ProximityPrize.SubmissionLower.FrontAssembly82200
import ProximityPrize.SubmissionLower.Final50GeoFinish
import ProximityPrize.SubmissionLower.HighCore82229Finish

set_option Elab.async false

namespace KoalaSoundness6951
open ProximityPrize.Benchmark

/-- 69.51 at 82,229 errors: low 1..2353 (Euler anchor, tilted tariff, taper+theta primary), high 2354... -/
theorem proof :
    ProtocolClaim 6951 ProximityPrize.SubmissionLower.Cell82200.p
      ProximityPrize.SubmissionLower.Cell82200.q := by
  apply Front82200.of_low_mid_high 2353
  · intro _ _ M _ F lo hi
    exact (Final50Geo.count M F lo (le_trans hi (by decide))).trans (by decide)
  · intro _ _ M _ F lo hi
    exact (Final50Geo.count M F (le_trans (by decide) lo) hi).trans (by decide)
  · intro _ _ M _ F lo hi
    exact (HighCore82229.count M F (le_trans (by decide) lo) hi).trans (by decide)

#print axioms proof
end KoalaSoundness6951
