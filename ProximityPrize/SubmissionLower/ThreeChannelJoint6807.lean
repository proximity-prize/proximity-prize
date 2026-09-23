/-
UNCOMPILED. All THREE unit cuts are supplied by the actual generic-channel
construction; none is a theorem premise here. The remaining pointwise moving
inequality is the original actual-source output, consumed at the Stage entry.
-/
import ProximityPrize.SubmissionLower.ActualGenericChannel6807
import ProximityPrize.SubmissionLower.CommonLinearChannels6807
import ProximityPrize.SubmissionLower.JointBudgetArithmetic6807

namespace ProximityPrize.SubmissionLower.ThreeChannelJoint6807
open RCN057 (WeightBound)
open RCN086 RCN074
open scoped Classical BigOperators
open RCN002 RCN095 RCN135 RCN136 RCN156 RCN207 RCN244 RCN264 RCN313
open RCN341 RCN344 RCN046 RCN237
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807 CommonLinearChannels6807
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 500000
variable {K I E : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "w" => RCN326.w

end
end ProximityPrize.SubmissionLower.ThreeChannelJoint6807
