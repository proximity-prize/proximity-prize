import ProximityPrize.SubmissionLower.LocatorR1200RankG

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankH. -/
section PackedLocator_LocatorR1200RankH

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_2240 :
    (∑ i ∈ Finset.range 64, rankRow (2240 + i)) = 70332425552640 := by decide

theorem chunk_2304 :
    (∑ i ∈ Finset.range 64, rankRow (2304 + i)) = 72306098377472 := by decide

theorem chunk_2368 :
    (∑ i ∈ Finset.range 64, rankRow (2368 + i)) = 74279382967040 := by decide

theorem chunk_2432 :
    (∑ i ∈ Finset.range 64, rankRow (2432 + i)) = 76252279321344 := by decide

theorem chunk_2496 :
    (∑ i ∈ Finset.range 64, rankRow (2496 + i)) = 78224787440384 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankH

