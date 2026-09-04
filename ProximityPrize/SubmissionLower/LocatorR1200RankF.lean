import ProximityPrize.SubmissionLower.LocatorR1200RankE

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankF. -/
section PackedLocator_LocatorR1200RankF

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_1600 :
    (∑ i ∈ Finset.range 64, rankRow (1600 + i)) = 50574344364800 := by decide

theorem chunk_1664 :
    (∑ i ∈ Finset.range 64, rankRow (1664 + i)) = 52551899542272 := by decide

theorem chunk_1728 :
    (∑ i ∈ Finset.range 64, rankRow (1728 + i)) = 54529066484480 := by decide

theorem chunk_1792 :
    (∑ i ∈ Finset.range 64, rankRow (1792 + i)) = 56505845191424 := by decide

theorem chunk_1856 :
    (∑ i ∈ Finset.range 64, rankRow (1856 + i)) = 58482235663104 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankF

