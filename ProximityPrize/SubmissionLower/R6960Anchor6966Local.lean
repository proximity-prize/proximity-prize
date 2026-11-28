import ProximityPrize.SubmissionLower.A6966FinalAnchorSpace
import Mathlib.Algebra.BigOperators.Intervals
import ProximityPrize.SubmissionLower.A6966FinalRankBlocks
import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false

namespace A6966LowBase
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative

/-- Bound the sum of the total and differentiated degrees at each monomial. -/
def ActiveFits (P : Row 4) (n : ℕ) : Prop :=
  ∀ m ∈ P.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ n

end
end A6966LowBase
