import ProximityPrize.SubmissionLower.LocatorScalarParameters

namespace ProximityPrize.SubmissionLower.LocatorScalarRank

open scoped BigOperators
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_48 :
    (∑ r ∈ Finset.range 24, rankRow (48 + r)) = 39340 := by decide

theorem chunk_72 :
    (∑ r ∈ Finset.range 20, rankRow (72 + r)) = 19670 := by decide

end ProximityPrize.SubmissionLower.LocatorScalarRank
