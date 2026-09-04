import ProximityPrize.SubmissionLower.LocatorR1200Coefficient

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankA. -/
section PackedLocator_LocatorR1200RankA

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ i ∈ Finset.range 64, rankRow i) = 1009288467200 := by decide

theorem chunk_64 :
    (∑ i ∈ Finset.range 64, rankRow (64 + i)) = 2996549526272 := by decide

theorem chunk_128 :
    (∑ i ∈ Finset.range 64, rankRow (128 + i)) = 4983422350080 := by decide

theorem chunk_192 :
    (∑ i ∈ Finset.range 64, rankRow (192 + i)) = 6969906938624 := by decide

theorem chunk_256 :
    (∑ i ∈ Finset.range 64, rankRow (256 + i)) = 8956003291904 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankA

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier22 : True := by trivial
end ProximityPrize.SubmissionLower

