import ProximityPrize.SubmissionLower.Low48AnchorSpace
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
namespace Low50Anchor
noncomputable section
open K1 K1_13 K1_13_1_1 Polynomial PolynomialDifferential ReedSolomon.HiddenDerivative
/-- Bound the sum of the total and differentiated degrees at each monomial. -/
def ActiveFits (P : Row 4) (n : ℕ) : Prop :=
  ∀ m ∈ P.support, m 0 + 2*m 1 + 2*m 2 + 2*m 3 ≤ n
end
end Low50Anchor
