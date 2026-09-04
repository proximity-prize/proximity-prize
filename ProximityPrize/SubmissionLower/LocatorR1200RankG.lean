import ProximityPrize.SubmissionLower.LocatorR1200RankF

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankG. -/
section PackedLocator_LocatorR1200RankG

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_1920 :
    (∑ i ∈ Finset.range 64, rankRow (1920 + i)) = 60458237899520 := by decide

theorem chunk_1984 :
    (∑ i ∈ Finset.range 64, rankRow (1984 + i)) = 62433851900672 := by decide

theorem chunk_2048 :
    (∑ i ∈ Finset.range 64, rankRow (2048 + i)) = 64409077666560 := by decide

theorem chunk_2112 :
    (∑ i ∈ Finset.range 64, rankRow (2112 + i)) = 66383915197184 := by decide

theorem chunk_2176 :
    (∑ i ∈ Finset.range 64, rankRow (2176 + i)) = 68358364492544 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankG

