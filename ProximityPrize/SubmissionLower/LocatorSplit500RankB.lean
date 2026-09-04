import ProximityPrize.SubmissionLower.LocatorSplit500RankA

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankB. -/
section PackedLocator_LocatorSplit500RankB

namespace ProximityPrize.SubmissionLower.LocatorSplit500Rank

open scoped BigOperators
open LocatorSplit500Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_320 :
    (∑ i ∈ Finset.range 64, rankRow (320 + i)) = 292361745120 := by decide

theorem chunk_384 :
    (∑ i ∈ Finset.range 64, rankRow (384 + i)) = 345178362592 := by decide

theorem chunk_448 :
    (∑ i ∈ Finset.range 64, rankRow (448 + i)) = 397913453280 := by decide

theorem chunk_512 :
    (∑ i ∈ Finset.range 64, rankRow (512 + i)) = 450567017184 := by decide

theorem chunk_576 :
    (∑ i ∈ Finset.range 64, rankRow (576 + i)) = 503139054304 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit500Rank
end PackedLocator_LocatorSplit500RankB

