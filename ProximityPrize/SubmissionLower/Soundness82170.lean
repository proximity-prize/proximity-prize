import ProximityPrize.SubmissionLower.FrontRank1282170
import ProximityPrize.SubmissionLower.FrontRank382170
import ProximityPrize.SubmissionLower.FrontRank482170
import ProximityPrize.SubmissionLower.LowFamily82170
import ProximityPrize.SubmissionLower.HighSource82170
import ProximityPrize.SubmissionLower.HighPairs82170
import ProximityPrize.SubmissionLower.HighRegular82170
import ProximityPrize.SubmissionLower.HighSchedule82170

set_option Elab.async false

namespace Soundness82170
open ProximityPrize.Benchmark

theorem high : Front82170.c7 :=
  HighFamily82170.of_children HighFamily82170_1.proof HighFamily82170_2.proof
    (HighFamily82170_3.of_children HighFamily82170_3_1.proof HighFamily82170_3_2.proof
      HighFamily82170_3.schedule HighFamily82170_3.ledger)
    HighFamily82170_2.terminal
    (HighFamily82170_5.of_children HighFamily82170_5_1.proof
      (HighFamily82170_5_2.of_children HighFamily82170_5_2_1.proof HighFamily82170_5_2_2.proof))

theorem low : Front82170.c6 :=
  fun _ _ M _ F lo hi => LowFamily82170.count M F lo hi

theorem protocol : ProtocolClaim 6945 336572415 1073741824 :=
  Front82170.of_children Front82170_1.proof Front82170_2.proof
    (Front82170_3.of_children Front82170_3_1.proof Front82170_3_2.proof)
    (Front82170_4.of_children Front82170_4_1.proof Front82170_4_2.proof)
    Front82170_5.proof low high

#print axioms protocol
end Soundness82170
