import ProximityPrize.SubmissionLower.LocatorR1200RankI

/-! Packed from ProximityPrize.SubmissionLower.LocatorR1200RankJ. -/
section PackedLocator_LocatorR1200RankJ

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_2880 :
    (∑ i ∈ Finset.range 64, rankRow (2880 + i)) = 90051683214080 := by decide

theorem chunk_2944 :
    (∑ i ∈ Finset.range 64, rankRow (2944 + i)) = 92021473686272 := by decide

theorem chunk_3008 :
    (∑ i ∈ Finset.range 64, rankRow (3008 + i)) = 93990875923200 := by decide

theorem chunk_3072 :
    (∑ i ∈ Finset.range 64, rankRow (3072 + i)) = 95959889924864 := by decide

theorem chunk_3136 :
    (∑ i ∈ Finset.range 64, rankRow (3136 + i)) = 97928515691264 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
end PackedLocator_LocatorR1200RankJ

