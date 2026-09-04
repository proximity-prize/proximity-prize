import ProximityPrize.SubmissionLower.LocatorSplit500RankB

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankC. -/
section PackedLocator_LocatorSplit500RankC

namespace ProximityPrize.SubmissionLower.LocatorSplit500Rank

open scoped BigOperators
open LocatorSplit500Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_640 :
    (∑ i ∈ Finset.range 64, rankRow (640 + i)) = 553893967770 := by decide

theorem chunk_704 :
    (∑ i ∈ Finset.range 64, rankRow (704 + i)) = 547969611648 := by decide

theorem chunk_768 :
    (∑ i ∈ Finset.range 64, rankRow (768 + i)) = 482699870080 := by decide

theorem chunk_832 :
    (∑ i ∈ Finset.range 64, rankRow (832 + i)) = 374104278912 := by decide

theorem chunk_896 :
    (∑ i ∈ Finset.range 64, rankRow (896 + i)) = 222283501440 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit500Rank
end PackedLocator_LocatorSplit500RankC

