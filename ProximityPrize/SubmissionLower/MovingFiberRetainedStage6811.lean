import ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811
import ProximityPrize.SubmissionLower.BoundaryTailDualRetained6807
import ProximityPrize.SubmissionLower.HFreeFirstSlice6812
namespace ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
open scoped Classical BigOperators
open RCN002 RCN046 RCN057 RCN074 RCN084 RCN085 RCN086 RCN095 RCN135 RCN136 RCN156 RCN159
open RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN263 RCN264 RCN271 RCN275
open RCN287 RCN313 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339 RCN340 RCN341 RCN344
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTransportC2 LocatorHybridTailProvider
open BoundaryTailProvider CommonLinearChannels6807 MovingFiberThreeSources6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 100000
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap : ℕ}
local notation "Ω" => GenericField K

def rawFirstFlag (t y r : ℕ) : FlagDegree :=
  RCN198.center (cellA t y) (cellB y r) (cellS r) +
    w • (⟨cellA t y,cellB y r+1,cellS r+2⟩ : FlagDegree)

def hfreeFirst (t y r : ℕ) : FlagDegree :=
  HFreeFirstSlice6812.hfreeFlag r (y-r) (t-y) unitAllFlag

def numerator {F : MvPolynomial (Fin 4) K} (source : Fin 3 → Source F)
    (scale t y r : ℕ) (flag : FlagDegree) : ℕ :=
  scale/3*flagMixed flag (hfreeFirst t y r) (cellNormal t y r) +
    ∑ j : Fin 3, (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(source j).d))+
      65539*weight (rawFirstFlag t y r) j*(scale/(source j).d))*
      flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag

def channel {t y r : ℕ}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r))
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag < p) :
    Fin 3 → MvPolynomial (Fin 3) Ω :=
  let common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed
  ![CommonLinearChannels6807.linearZ,CommonLinearChannels6807.linearU common.lam,
    CommonLinearChannels6807.linearA common.mu common.lam]

end
end ProximityPrize.SubmissionLower.MovingFiberRetainedStage6811
