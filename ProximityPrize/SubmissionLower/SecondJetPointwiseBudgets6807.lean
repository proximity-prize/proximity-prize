import ProximityPrize.SubmissionLower.ReducedCommonLinear6807
/-
UNCOMPILED SOURCE EXTRACTION. No new geometric assertion is postulated.
The frozen proof already establishes hpoint; this file returns it instead
of discarding it. The entire hpoint block is preserved byte-for-byte.
See pointwise_extraction_audit.json. A real Lean build is still required.
-/
import ProximityPrize.SubmissionLower.LowerGeometry

section Compact_SecondJetActiveMovingBudget6807
/-! Moving budgets for the retained components, using their actual integer
projection degrees and the second-jet weighted root bound. -/
namespace ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget6807
open scoped BigOperators
open RCN005 RCN006 RCN064 RCN002 RCN095 RCN187 RCN204 RCN207 RCN264 RCN341 RCN046 RCN199
open RCN344 (SeparableCoordinate coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K : Type} [Field K] [IsAlgClosed K]

end
end ProximityPrize.SubmissionLower.SecondJetActiveMovingBudget6807

end Compact_SecondJetActiveMovingBudget6807

section Compact_SecondJetRetainedBudgets6807
/-! The weighted moving-degree estimate on the actual first-tail components,
assuming the proper derivative-helper alternatives have been excluded. -/
namespace ProximityPrize.SubmissionLower.SecondJetRetainedBudgets6807
open scoped Classical BigOperators
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open RCN002 RCN136 RCN264 RCN341 RCN046 RCN095 RCN199
open RCN344 (coordinateDegree)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

end
end ProximityPrize.SubmissionLower.SecondJetRetainedBudgets6807

end Compact_SecondJetRetainedBudgets6807
