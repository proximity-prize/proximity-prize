import ProximityPrize.SubmissionLower.Low48PrimaryPivotRect
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBaseline

set_option Elab.async false
set_option maxHeartbeats 2500000

namespace Low48PrimaryPivot
open K1_13 (Geom)
open K1_13_2 K1_13_2_3
open PolynomialDifferential ReedSolomon.HiddenDerivative
open scoped BigOperators



open private baseline_budget_on bound_le_baseline from ProximityPrize.SubmissionLower.Fast022



attribute [local irreducible] Finset.univ







end Low48PrimaryPivot
