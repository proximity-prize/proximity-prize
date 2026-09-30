import ProximityPrize.SubmissionLower.MovingSourceOuterStageFrames6814
namespace ProximityPrize.SubmissionLower.MovingSourceCheckedIdentityStage6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider MovingFiberThreeSources6811
open MovingSourcePairEnvelope6814 MovingSourceTwoProfiles6814
open MovingSourceCoupledClearing6814
local notation "w" => RCN326.w

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

end
end ProximityPrize.SubmissionLower.MovingSourceCheckedIdentityStage6814
