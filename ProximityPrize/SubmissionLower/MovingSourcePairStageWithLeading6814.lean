import ProximityPrize.SubmissionLower.MovingSourceStageRestriction6814
import ProximityPrize.SubmissionLower.MovingSourceDenominatorSeeds6814
namespace ProximityPrize.SubmissionLower.MovingSourcePairStageWithLeading6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 25000
open scoped Classical
open RCN086 RCN095 RCN135 RCN136 RCN156 RCN159 RCN174 RCN234 RCN243 RCN244 RCN260 RCN264 RCN275
open MovingFiberThreeSources6811 MovingSourceTwoProfiles6814
open MovingSourcePairStageSupplier6814 MovingSourceCoupledClearing6814
open LocatorHybridCells

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}
local notation "w" => RCN326.w

end
end ProximityPrize.SubmissionLower.MovingSourcePairStageWithLeading6814
