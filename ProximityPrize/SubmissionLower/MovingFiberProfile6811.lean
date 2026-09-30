import ProximityPrize.SubmissionLower.MovingFiberRegularData6811
import ProximityPrize.SubmissionLower.MovingFiberInterpolation6811
import ProximityPrize.SubmissionLower.SecondJetRefinements
import ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6811
namespace ProximityPrize.SubmissionLower.MovingFiberProfile6811
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider
open MovingFiberRegularData6811 MovingFiberThreeSources6811 MovingFiberInterpolation6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

structure Params where
  m : ℕ
  B : ℕ
  s : ℕ
  U : ℕ
  L : ℕ
  k : ℕ
  n0 : ℕ
  deriving DecidableEq, Repr

def Params.d (P : Params) : ℕ := P.k+1
def Params.flag (P : Params) : FlagDegree := SecondJetRelaxedFlag.budgetFlag P.B P.U P.L P.d P.n0
def Params.WellFormed (P : Params) : Prop :=
  2*P.s ≤ P.B ∧ P.B ≤ P.U ∧ P.U ≤ P.L ∧ P.k ≤ P.s ∧ P.s < P.m ∧
    P.k+1 ≤ P.n0 ∧ 2*(P.n0-(P.k+1)) ≤ P.B ∧ P.s < 2130706433
def number (cfg : Fin 3 → Params) (scale t y r : ℕ) (f : FlagDegree) : ℕ :=
  scale/3*flagMixed f (MovingFiberRetainedStage6811.hfreeFirst t y r) (cellNormal t y r) +
    ∑ j : Fin 3, (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(cfg j).d))+
      65539*weight (MovingFiberRetainedStage6811.rawFirstFlag t y r) j*(scale/(cfg j).d))*
      flagMixed f (MovingFiberThreeSources6811.direction j) (cfg j).flag

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {nodes : I ↪ K} {u0 u1 : I → K}

def helperCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair (P.B+P.s*(S.r-1)) (P.U+P.s*(S.y-1)) (P.L+P.s*(S.t-1)))
def coefficientCap (S : Data nodes u0 u1) (P : Params) : ℕ :=
  AsymmetricHelper.leftRegularCountCap (S.pair P.B P.U P.L)
def bound (S : Data nodes u0 u1) (cfg : Fin 3 → Params) (scale : ℕ) : ℕ :=
  max (Finset.univ.sup (fun j : Fin 3 => helperCap S (cfg j)))
    (number cfg scale S.t S.y S.r (originalCumulativeFlag S.F)/scale +
      ∑ j : Fin 3, coefficientCap S (cfg j))

end
end ProximityPrize.SubmissionLower.MovingFiberProfile6811
