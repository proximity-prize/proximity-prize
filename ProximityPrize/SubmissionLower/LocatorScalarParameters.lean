import ProximityPrize.SubmissionLower.E9

/-! Small shared rows for the 6800 scalar-interpolation receipts. -/

namespace ProximityPrize.SubmissionLower.LocatorScalarParameters

open scoped BigOperators
open ProximityPrize.Benchmark RCN279 RCN285

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
set_option Elab.async false

/-- One coefficient row for the retuned seedless interpolant. -/
def coefficientRow (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range 28,
    min 1 (128 - i - j) * (16688064 - 131071 * i - 131070 * j)

/-- One local contact-rank row for the retuned seedless interpolant. -/
def rankRow (r : ℕ) : ℕ :=
  seedlessContactRankBound (min r 127) 127 27 (92 - r)

end ProximityPrize.SubmissionLower.LocatorScalarParameters
