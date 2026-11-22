import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Numeric5Certificate
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1500000
namespace K1_14_2_2
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
open scoped Classical
def c1 : Prop :=
  ∀ P s, P ≠ 0 → RowCaps P s → Nonempty (FixedPart P s)
end
end K1_14_2_2
end
