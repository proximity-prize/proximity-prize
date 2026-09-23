/-
UNCOMPILED. Actual retained proper-first-tail Stage adapter. The joint budget is
built inside the body from actual-source pointwise budgets and three actual
common linear channels. Neither hcut nor hjoint is a theorem premise.
This is not an unconditional ProtocolClaim or a full mixed-branch regular bound.
-/
import ProximityPrize.SubmissionLower.BoundaryTailProvider
import ProximityPrize.SubmissionLower.ThreeChannelJoint6807
import ProximityPrize.SubmissionLower.ReducedCommonLinear6807
import ProximityPrize.SubmissionLower.SecondJetPointwiseBudgets6807
import ProximityPrize.SubmissionLower.BoundaryTailJointBudget6807

namespace ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807
open RCN057 (WeightBound)
open scoped Classical BigOperators
open RCN135 RCN136 RCN159 RCN264 RCN074 RCN086 RCN243 RCN238 RCN095 RCN237 RCN198 RCN275 RCN244 RCN327 RCN263 RCN334 RCN332 RCN336 RCN312 RCN339 RCN330 RCN174 RCN319
open RCN206 RCN287 RCN066 RCN338 RCN199 RCN207 RCN271 RCN313 RCN234 RCN156 RCN341 RCN085
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider
open LocatorHybridTailProviderC1 LocatorHybridTransportC2
open BoundaryTailProvider
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
variable [CharP (GenericField K) p] [CharP K p]
variable {stageErrorCap : ℕ}

end
end ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807
