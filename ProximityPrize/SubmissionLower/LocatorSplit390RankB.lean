import ProximityPrize.SubmissionLower.LocatorSplit390RankA

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390RankB. -/
section PackedLocator_LocatorSplit390RankB

namespace ProximityPrize.SubmissionLower.LocatorSplit390Rank

open scoped BigOperators
open LocatorSplit390Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_256 :
    (∑ i ∈ Finset.range 64, rankRow (256 + i)) = 37791122159 := by decide

theorem chunk_320 :
    (∑ i ∈ Finset.range 64, rankRow (320 + i)) = 19811668800 := by decide

theorem chunk_384 :
    (∑ i ∈ Finset.range 6, rankRow (384 + i)) = 203453075 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit390Rank
end PackedLocator_LocatorSplit390RankB

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier40 : True := by trivial
end ProximityPrize.SubmissionLower

