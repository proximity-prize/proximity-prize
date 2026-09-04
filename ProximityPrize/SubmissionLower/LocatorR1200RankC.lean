import ProximityPrize.SubmissionLower.LocatorR1200RankB

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankC. -/
section PackedLocator_LocatorR1200RankC

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_640 :
    (∑ i ∈ Finset.range 64, rankRow (640 + i)) = 20864428471040 := by decide

theorem chunk_704 :
    (∑ i ∈ Finset.range 64, rankRow (704 + i)) = 22847807177472 := by decide

theorem chunk_768 :
    (∑ i ∈ Finset.range 64, rankRow (768 + i)) = 24830797648640 := by decide

theorem chunk_832 :
    (∑ i ∈ Finset.range 64, rankRow (832 + i)) = 26813399884544 := by decide

theorem chunk_896 :
    (∑ i ∈ Finset.range 64, rankRow (896 + i)) = 28795613885184 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankC

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier24 : True := by trivial
end ProximityPrize.SubmissionLower

