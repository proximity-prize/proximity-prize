import ProximityPrize.SubmissionLower.LocatorR1200Parameters

namespace ProximityPrize.SubmissionLower.LocatorR1200Rank

open scoped BigOperators
open LocatorR1200Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_640 :
    (∑ i ∈ Finset.range 64, rankRow (640 + i)) = 1302656327840 := by decide

theorem chunk_704 :
    (∑ i ∈ Finset.range 64, rankRow (704 + i)) = 1426067382432 := by decide

theorem chunk_768 :
    (∑ i ∈ Finset.range 64, rankRow (768 + i)) = 1549268140176 := by decide

theorem chunk_832 :
    (∑ i ∈ Finset.range 64, rankRow (832 + i)) = 1574048718272 := by decide

theorem chunk_896 :
    (∑ i ∈ Finset.range 64, rankRow (896 + i)) = 1455328904640 := by decide

end ProximityPrize.SubmissionLower.LocatorR1200Rank
