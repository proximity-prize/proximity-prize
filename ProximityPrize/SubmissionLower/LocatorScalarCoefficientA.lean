import ProximityPrize.SubmissionLower.LocatorScalarParameters

namespace ProximityPrize.SubmissionLower.LocatorScalarCoefficient

open scoped BigOperators
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_0 :
    (∑ i ∈ Finset.range 16, coefficientRow i) = 6243142752 := by decide

theorem chunk_16 :
    (∑ i ∈ Finset.range 16, coefficientRow (16 + i)) = 5303625824 := by decide

theorem chunk_32 :
    (∑ i ∈ Finset.range 16, coefficientRow (32 + i)) = 4364108896 := by decide

theorem chunk_48 :
    (∑ i ∈ Finset.range 16, coefficientRow (48 + i)) = 3424591968 := by decide

end ProximityPrize.SubmissionLower.LocatorScalarCoefficient
