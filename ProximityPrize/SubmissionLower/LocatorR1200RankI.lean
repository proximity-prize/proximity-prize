import ProximityPrize.SubmissionLower.LocatorR1200RankH

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankI. -/
section PackedLocator_LocatorR1200RankI

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_2560 :
    (∑ i ∈ Finset.range 64, rankRow (2560 + i)) = 80196907324160 := by decide

theorem chunk_2624 :
    (∑ i ∈ Finset.range 64, rankRow (2624 + i)) = 82168638972672 := by decide

theorem chunk_2688 :
    (∑ i ∈ Finset.range 64, rankRow (2688 + i)) = 84139982385920 := by decide

theorem chunk_2752 :
    (∑ i ∈ Finset.range 64, rankRow (2752 + i)) = 86110937563904 := by decide

theorem chunk_2816 :
    (∑ i ∈ Finset.range 64, rankRow (2816 + i)) = 88081504506624 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankI

