import ProximityPrize.SubmissionLower.MovingSourcePairFirstChannel6814
namespace ProximityPrize.SubmissionLower.MovingSourcePairRetainedStage6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 35000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN084 RCN085 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTransportC2 LocatorHybridTailProvider
open BoundaryTailProvider CommonLinearChannels6807 MovingFiberThreeSources6811 MovingFiberRetainedStage6811 HFreeDir6813
open MovingSourceExtendedPointCount6814
local notation "w" => RCN326.w

def price (W : FlagDegree) (z u v : ℕ) : ℕ := W.zOnly*z+W.yz*u+W.all*v
def pairNumerator (scale z u v t y r : ℕ) (flag : FlagDegree) : ℕ :=
  scale*(∑ j : Fin 3, weight (cellNormal t y r) j*flagMixed flag
    (hfreeFirstDir t y r j) (MovingFiberThreeSources6811.direction j))+
    4*(w+1)*price (cellNormal t y r) z u v+
    3*65539*price (rawFirstFlag t y r) z u v

theorem sum_weight_price (W : FlagDegree) (z u v : ℕ) :
    (∑ j : Fin 3, weight W j*price (MovingFiberThreeSources6811.direction j) z u v)=price W z u v := by
  simp [Fin.sum_univ_three,weight,MovingFiberThreeSources6811.direction,price,unitZFlag,unitYZFlag,unitAllFlag]

variable {K I : Type} [Field K] [CharP K 2130706433]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
local notation "Ω" => GenericField K
local notation "Ext" => AlgebraicClosure (RatFunc Ω)

end
end ProximityPrize.SubmissionLower.MovingSourcePairRetainedStage6814
