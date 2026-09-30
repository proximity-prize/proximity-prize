import ProximityPrize.SubmissionLower.MovingSourcePairEnvelope6814
namespace ProximityPrize.SubmissionLower.MovingSourceCheckedPairStage6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical BigOperators
open RCN086 RCN095 RCN135 RCN136 RCN156 RCN159 RCN174 RCN234 RCN243 RCN244 RCN260 RCN264
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814 MovingSourceCoupledClearing6814
open MovingSourcePairRetainedStage6814 MovingSourcePairStageSupplier6814
open MovingSourcePairEnvelope6814 LocatorHybridCells

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}
local notation "w" => RCN326.w

end
end ProximityPrize.SubmissionLower.MovingSourceCheckedPairStage6814
