import ProximityPrize.SubmissionLower.LocatorR1200RankC

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankD. -/
section PackedLocator_LocatorR1200RankD

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_960 :
    (∑ i ∈ Finset.range 64, rankRow (960 + i)) = 30777439650560 := by decide

theorem chunk_1024 :
    (∑ i ∈ Finset.range 64, rankRow (1024 + i)) = 32758877180672 := by decide

theorem chunk_1088 :
    (∑ i ∈ Finset.range 64, rankRow (1088 + i)) = 34739926475520 := by decide

theorem chunk_1152 :
    (∑ i ∈ Finset.range 64, rankRow (1152 + i)) = 36720587535104 := by decide

theorem chunk_1216 :
    (∑ i ∈ Finset.range 64, rankRow (1216 + i)) = 38700860359424 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankD

