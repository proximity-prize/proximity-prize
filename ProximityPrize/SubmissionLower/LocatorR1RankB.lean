import ProximityPrize.SubmissionLower.LocatorR1RankA

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1RankB. -/
section PackedLocator_LocatorR1RankB

namespace ProximityPrize.SubmissionLower.LocatorR1Rank

open scoped BigOperators
open LocatorR1Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_320 :
    (∑ i ∈ Finset.range 64, rankRow (320 + i)) = 684142223520 := by decide

theorem chunk_384 :
    (∑ i ∈ Finset.range 64, rankRow (384 + i)) = 808039555232 := by decide

theorem chunk_448 :
    (∑ i ∈ Finset.range 64, rankRow (448 + i)) = 931839631520 := by decide

theorem chunk_512 :
    (∑ i ∈ Finset.range 64, rankRow (512 + i)) = 1055542452384 := by decide

theorem chunk_576 :
    (∑ i ∈ Finset.range 64, rankRow (576 + i)) = 1179148017824 := by decide

end ProximityPrize.SubmissionLower.LocatorR1Rank
end PackedLocator_LocatorR1RankB

