import ProximityPrize.SubmissionLower.LocatorSplit500Parameters

namespace ProximityPrize.SubmissionLower.LocatorSplit500Rank

open scoped BigOperators
open LocatorSplit500Parameters

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_256 :
    (∑ i ∈ Finset.range 64, rankRow (256 + i)) = 59851955904 := by decide

theorem chunk_320 :
    (∑ i ∈ Finset.range 64, rankRow (320 + i)) = 69107989600 := by decide

theorem chunk_384 :
    (∑ i ∈ Finset.range 64, rankRow (384 + i)) = 53769638208 := by decide

theorem chunk_448 :
    (∑ i ∈ Finset.range 52, rankRow (448 + i)) = 16736449392 := by decide

end ProximityPrize.SubmissionLower.LocatorSplit500Rank
