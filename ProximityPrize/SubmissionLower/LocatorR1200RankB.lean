import ProximityPrize.SubmissionLower.LocatorR1200RankA

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankB. -/
section PackedLocator_LocatorR1200RankB

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_320 :
    (∑ i ∈ Finset.range 64, rankRow (320 + i)) = 10941711409920 := by decide

theorem chunk_384 :
    (∑ i ∈ Finset.range 64, rankRow (384 + i)) = 12927031292672 := by decide

theorem chunk_448 :
    (∑ i ∈ Finset.range 64, rankRow (448 + i)) = 14911962940160 := by decide

theorem chunk_512 :
    (∑ i ∈ Finset.range 64, rankRow (512 + i)) = 16896506352384 := by decide

theorem chunk_576 :
    (∑ i ∈ Finset.range 64, rankRow (576 + i)) = 18880661529344 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankB

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier23 : True := by trivial
end ProximityPrize.SubmissionLower

