import ProximityPrize.SubmissionLower.LocatorR1200RankL

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankM. -/
section PackedLocator_LocatorR1200RankM

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_3840 :
    (∑ i ∈ Finset.range 64, rankRow (3840 + i)) = 85635645721440 := by decide

theorem chunk_3904 :
    (∑ i ∈ Finset.range 64, rankRow (3904 + i)) = 82030664844128 := by decide

theorem chunk_3968 :
    (∑ i ∈ Finset.range 64, rankRow (3968 + i)) = 78084910136160 := by decide

theorem chunk_4032 :
    (∑ i ∈ Finset.range 64, rankRow (4032 + i)) = 73798482260832 := by decide

theorem chunk_4096 :
    (∑ i ∈ Finset.range 64, rankRow (4096 + i)) = 69171481881440 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankM

