import ProximityPrize.SubmissionLower.LocatorR1200RankK

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankL. -/
section PackedLocator_LocatorR1200RankL

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_3520 :
    (∑ i ∈ Finset.range 64, rankRow (3520 + i)) = 98545419432800 := by decide

theorem chunk_3584 :
    (∑ i ∈ Finset.range 64, rankRow (3584 + i)) = 96645817658208 := by decide

theorem chunk_3648 :
    (∑ i ∈ Finset.range 64, rankRow (3648 + i)) = 94404938736480 := by decide

theorem chunk_3712 :
    (∑ i ∈ Finset.range 64, rankRow (3712 + i)) = 91822883330912 := by decide

theorem chunk_3776 :
    (∑ i ∈ Finset.range 64, rankRow (3776 + i)) = 88899752104800 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankL

