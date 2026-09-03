import ProximityPrize.SubmissionLower.LocatorScalarCoefficientA
import ProximityPrize.SubmissionLower.LocatorScalarCoefficientB

/-! Assembly of the separately checked scalar coefficient-count chunks. -/

namespace ProximityPrize.SubmissionLower.LocatorScalarCoefficient

open scoped BigOperators
open ProximityPrize.Benchmark RCN279
open LocatorScalarParameters

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem coefficientCount_exact :
    coefficientCount 16688064 131071 127 27 = 24101700770 := by
  change (∑ i ∈ Finset.range 128, coefficientRow i) = _
  rw [Finset.sum_range_add coefficientRow 112 16,
    Finset.sum_range_add coefficientRow 96 16,
    Finset.sum_range_add coefficientRow 80 16,
    Finset.sum_range_add coefficientRow 64 16,
    Finset.sum_range_add coefficientRow 48 16,
    Finset.sum_range_add coefficientRow 32 16,
    Finset.sum_range_add coefficientRow 16 16,
    chunk_0, chunk_16, chunk_32, chunk_48,
    chunk_64, chunk_80, chunk_96, chunk_112]

end ProximityPrize.SubmissionLower.LocatorScalarCoefficient
