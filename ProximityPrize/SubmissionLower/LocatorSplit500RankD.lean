import ProximityPrize.SubmissionLower.LocatorSplit500RankC

/-! Packed from ProximityPrize.SubmissionLower.LocatorSplit500RankD. -/
section PackedLocator_LocatorSplit500RankD

namespace ProximityPrize.SubmissionLower.LocatorSplit500Rank

open scoped BigOperators
open LocatorSplit500Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_960 :
    (∑ i ∈ Finset.range 40, rankRow (960 + i)) = 42664731200 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit500Rank
end PackedLocator_LocatorSplit500RankD

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier34 : True := by trivial
end ProximityPrize.SubmissionLower

