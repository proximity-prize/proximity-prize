import ProximityPrize.SubmissionLower.LocatorSplit500Coefficient

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankA. -/
section PackedLocator_LocatorSplit500RankA

namespace ProximityPrize.SubmissionLower.LocatorSplit500Rank

open scoped BigOperators
open LocatorSplit500Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ i ∈ Finset.range 64, rankRow i) = 27055756000 := by decide

theorem chunk_64 :
    (∑ i ∈ Finset.range 64, rankRow (64 + i)) = 80280007392 := by decide

theorem chunk_128 :
    (∑ i ∈ Finset.range 64, rankRow (128 + i)) = 133422732000 := by decide

theorem chunk_192 :
    (∑ i ∈ Finset.range 64, rankRow (192 + i)) = 186483929824 := by decide

theorem chunk_256 :
    (∑ i ∈ Finset.range 64, rankRow (256 + i)) = 239463600864 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit500Rank
end PackedLocator_LocatorSplit500RankA

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier33 : True := by trivial
end ProximityPrize.SubmissionLower

