import ProximityPrize.SubmissionLower.LocatorR1200RankD

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankE. -/
section PackedLocator_LocatorR1200RankE

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_1280 :
    (∑ i ∈ Finset.range 64, rankRow (1280 + i)) = 40680744948480 := by decide

theorem chunk_1344 :
    (∑ i ∈ Finset.range 64, rankRow (1344 + i)) = 42660241302272 := by decide

theorem chunk_1408 :
    (∑ i ∈ Finset.range 64, rankRow (1408 + i)) = 44639349420800 := by decide

theorem chunk_1472 :
    (∑ i ∈ Finset.range 64, rankRow (1472 + i)) = 46618069304064 := by decide

theorem chunk_1536 :
    (∑ i ∈ Finset.range 64, rankRow (1536 + i)) = 48596400952064 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankE

