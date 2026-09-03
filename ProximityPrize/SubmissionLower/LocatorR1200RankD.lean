import ProximityPrize.SubmissionLower.LocatorR1200Parameters

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_960 :
    (∑ i ∈ Finset.range 64, rankRow (960 + i)) = 1251326569920 := by decide

theorem chunk_1024 :
    (∑ i ∈ Finset.range 64, rankRow (1024 + i)) = 962142377408 := by decide

theorem chunk_1088 :
    (∑ i ∈ Finset.range 64, rankRow (1088 + i)) = 587876990400 := by decide

theorem chunk_1152 :
    (∑ i ∈ Finset.range 48, rankRow (1152 + i)) = 144171197072 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
