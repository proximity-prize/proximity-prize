import ProximityPrize.SubmissionLower.LocatorR1Coefficient

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankA. -/
section PackedLocator_LocatorR1RankA

namespace ProximityPrize.SubmissionLower.LocatorR1Rank

open scoped BigOperators
open LocatorR1Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ i ∈ Finset.range 64, rankRow i) = 63196733600 := by decide

theorem chunk_64 :
    (∑ i ∈ Finset.range 64, rankRow (64 + i)) = 187580342432 := by decide

theorem chunk_128 :
    (∑ i ∈ Finset.range 64, rankRow (128 + i)) = 311866695840 := by decide

theorem chunk_192 :
    (∑ i ∈ Finset.range 64, rankRow (192 + i)) = 436055793824 := by decide

theorem chunk_256 :
    (∑ i ∈ Finset.range 64, rankRow (256 + i)) = 560147636384 := by decide

end ProximityPrize.SubmissionLower.LocatorR1Rank
end PackedLocator_LocatorR1RankA

