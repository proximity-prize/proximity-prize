import ProximityPrize.SubmissionLower.LocatorR1200RankN

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankO. -/
section PackedLocator_LocatorR1200RankO

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_4480 :
    (∑ i ∈ Finset.range 64, rankRow (4480 + i)) = 34263094164320 := by decide

theorem chunk_4544 :
    (∑ i ∈ Finset.range 64, rankRow (4544 + i)) = 27254904828768 := by decide

theorem chunk_4608 :
    (∑ i ∈ Finset.range 64, rankRow (4608 + i)) = 19906948295520 := by decide

theorem chunk_4672 :
    (∑ i ∈ Finset.range 64, rankRow (4672 + i)) = 12219325227872 := by decide

theorem chunk_4736 :
    (∑ i ∈ Finset.range 64, rankRow (4736 + i)) = 4192136289120 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankO

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier25 : True := by trivial
end ProximityPrize.SubmissionLower

