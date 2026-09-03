import ProximityPrize.SubmissionLower.LocatorScalarParameters

namespace ProximityPrize.SubmissionLower.LocatorScalarRank

open scoped BigOperators
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ r ∈ Finset.range 24, rankRow r) = 8400 := by decide

theorem chunk_24 :
    (∑ r ∈ Finset.range 24, rankRow (24 + r)) = 24528 := by decide

end ProximityPrize.SubmissionLower.LocatorScalarRank
