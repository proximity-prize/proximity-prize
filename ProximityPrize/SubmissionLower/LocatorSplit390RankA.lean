import ProximityPrize.SubmissionLower.LocatorSplit390Coefficient

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit390RankA. -/
section PackedLocator_LocatorSplit390RankA

namespace ProximityPrize.SubmissionLower.LocatorSplit390Rank

open scoped BigOperators
open LocatorSplit390Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ i ∈ Finset.range 64, rankRow i) = 4887625600 := by decide

theorem chunk_64 :
    (∑ i ∈ Finset.range 64, rankRow (64 + i)) = 14491176832 := by decide

theorem chunk_128 :
    (∑ i ∈ Finset.range 64, rankRow (128 + i)) = 24063008640 := by decide

theorem chunk_192 :
    (∑ i ∈ Finset.range 64, rankRow (192 + i)) = 33603121024 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit390Rank
end PackedLocator_LocatorSplit390RankA

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier39 : True := by trivial
end ProximityPrize.SubmissionLower

