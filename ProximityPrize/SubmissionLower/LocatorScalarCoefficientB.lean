import ProximityPrize.SubmissionLower.LocatorScalarParameters

namespace ProximityPrize.SubmissionLower.LocatorScalarCoefficient

open scoped BigOperators
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem chunk_64 :
    (∑ i ∈ Finset.range 16, coefficientRow (64 + i)) = 2485075040 := by decide

theorem chunk_80 :
    (∑ i ∈ Finset.range 16, coefficientRow (80 + i)) = 1545558112 := by decide

theorem chunk_96 :
    (∑ i ∈ Finset.range 16, coefficientRow (96 + i)) = 640750826 := by decide

theorem chunk_112 :
    (∑ i ∈ Finset.range 16, coefficientRow (112 + i)) = 94847352 := by decide

end ProximityPrize.SubmissionLower.LocatorScalarCoefficient
