import ProximityPrize.SubmissionLower.FrontRank1282190
import ProximityPrize.SubmissionLower.FrontRank382190
import ProximityPrize.SubmissionLower.FrontRank482190
import ProximityPrize.SubmissionLower.LowFamily82190
import ProximityPrize.SubmissionLower.Heights82190

set_option Elab.async false

namespace Soundness82190
open ProximityPrize.Benchmark

theorem low : Front82190.c6 :=
  fun _ _ M _ F lo hi => (LowFamily82190.count M F lo hi).trans (by decide)

theorem protocol : ProtocolClaim 6947 336654335 1073741824 :=
  Front82190.of_children Front82190_1.proof Front82190_2.proof
    (Front82190_3.of_children Front82190_3_1.proof Front82190_3_2.proof)
    (Front82190_4.of_children Front82190_4_1.proof Front82190_4_2.proof)
    Front82190_5.proof low Heights82190.high

#print axioms protocol
end Soundness82190
