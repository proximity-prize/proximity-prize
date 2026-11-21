import ProximityPrize.SubmissionLower.ThetaSumData0
import ProximityPrize.SubmissionLower.ThetaSumData1
import ProximityPrize.SubmissionLower.ThetaSumData2
import ProximityPrize.SubmissionLower.ThetaSumData3
import ProximityPrize.SubmissionLower.ThetaSumData4
import ProximityPrize.SubmissionLower.ThetaSumData5
import ProximityPrize.SubmissionLower.ThetaSumData6
import ProximityPrize.SubmissionLower.ThetaSumData7

/-! The theta savings sum over the grades 1354..3011. -/

namespace ThetaSum

theorem t0 : chunk 1354 208 = 151843403 := part0
theorem t1 : chunk 1354 416 = 4136255920 := by
  have h := chunk_join t0 part1
  exact h
theorem t2 : chunk 1354 624 = 25983679429 := by
  have h := chunk_join t1 part2
  exact h
theorem t3 : chunk 1354 832 = 84043480999 := by
  have h := chunk_join t2 part3
  exact h
theorem t4 : chunk 1354 1040 = 172558809210 := by
  have h := chunk_join t3 part4
  exact h
theorem t5 : chunk 1354 1248 = 245276890439 := by
  have h := chunk_join t4 part5
  exact h
theorem t6 : chunk 1354 1456 = 280015706919 := by
  have h := chunk_join t5 part6
  exact h
theorem t7 : chunk 1354 1658 = 288366984459 := by
  have h := chunk_join t6 part7
  exact h

theorem total : chunk 1354 1658 = 288366984459 := t7

#print axioms total

end ThetaSum
