import ProximityPrize.SubmissionLower.R6961Front6961List
import ProximityPrize.SubmissionLower.R6961Front6961HighCount
import ProximityPrize.SubmissionLower.R6961Front6961Rank2
import ProximityPrize.SubmissionLower.R6961Front6961Rank3
import ProximityPrize.SubmissionLower.R6961Front6961Rank4
import ProximityPrize.SubmissionLower.R6961Front6961Rank5
import ProximityPrize.SubmissionLower.R6961Low6961Count

set_option Elab.async false
namespace Lower6961
open ProximityPrize.Benchmark
open ProximityPrize.SubmissionLower.Front6961Radius (p q)

theorem low_front_count : Front6961.c6 := by
  intro _ _ M _ F lo hi
  exact Low.count M F lo hi

/-- Unconditional 69.61 lower-track protocol claim at radius `337210382 / 1073741824`. -/
theorem protocol_6961 : ProtocolClaim 6961 p q := by
  apply Front6961.of_children Front6961ListBank.scalar_list
    Front6961_1.proof Front6961_2.proof
    (Front6961_3.of_children Front6961_3_1.proof Front6961_3_2.proof)
    (Front6961_4.of_children Front6961_4_1.proof Front6961_4_2.proof)
    Front6961_5.proof low_front_count
  intro _ _ M _ F lo hi
  exact high_count M F lo hi

#print axioms protocol_6961
end Lower6961
