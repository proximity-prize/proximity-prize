import ProximityPrize.SubmissionLower.MovingSourcePairRetainedStage6814
namespace ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider LocatorHybridTransportC2
open BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
open HFreeDir6813 MovingSourcePairRetainedStage6814 MovingSourceCoupledClearing6814
open MovingSourceExtendedPointCount6814
open MovingSourceReducedGamma6814
local notation "w" => RCN326.w

def stageScale {K : Type} [Field K] {F : MvPolynomial (Fin 4) K} (SZ : Source F) (delta : ℕ) : ℕ := SZ.d*delta
def pairStageCost {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (SZ SP SQ : Source F) (delta t y r : ℕ) (flag : FlagDegree) : ℕ :=
  pairNumerator (stageScale SZ delta)
    (delta*flagMixed ⟨t-y,y-r,r⟩ unitZFlag SZ.flag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag)
    (SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag)
    t y r flag/(3*stageScale SZ delta)

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)

end
end ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814
