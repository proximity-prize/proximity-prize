import ProximityPrize.SubmissionLower.LocatorR1200RankJ

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankK. -/
section PackedLocator_LocatorR1200RankK

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_3200 :
    (∑ i ∈ Finset.range 64, rankRow (3200 + i)) = 99896753222400 := by decide

theorem chunk_3264 :
    (∑ i ∈ Finset.range 64, rankRow (3264 + i)) = 101842887095228 := by decide

theorem chunk_3328 :
    (∑ i ∈ Finset.range 64, rankRow (3328 + i)) = 102195555240800 := by decide

theorem chunk_3392 :
    (∑ i ∈ Finset.range 64, rankRow (3392 + i)) = 101320388887392 := by decide

theorem chunk_3456 :
    (∑ i ∈ Finset.range 64, rankRow (3456 + i)) = 100103643396960 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankK

