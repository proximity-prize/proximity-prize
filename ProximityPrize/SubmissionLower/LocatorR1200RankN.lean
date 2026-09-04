import ProximityPrize.SubmissionLower.LocatorR1200RankM

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankN. -/
section PackedLocator_LocatorR1200RankN

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_4160 :
    (∑ i ∈ Finset.range 64, rankRow (4160 + i)) = 64204009661280 := by decide

theorem chunk_4224 :
    (∑ i ∈ Finset.range 64, rankRow (4224 + i)) = 58896166263648 := by decide

theorem chunk_4288 :
    (∑ i ∈ Finset.range 64, rankRow (4288 + i)) = 53248052351840 := by decide

theorem chunk_4352 :
    (∑ i ∈ Finset.range 64, rankRow (4352 + i)) = 47259768589152 := by decide

theorem chunk_4416 :
    (∑ i ∈ Finset.range 64, rankRow (4416 + i)) = 40931415638880 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankN

