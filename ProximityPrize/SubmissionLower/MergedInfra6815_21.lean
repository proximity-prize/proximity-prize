import ProximityPrize.SubmissionLower.MergedInfra6815_14
import ProximityPrize.SubmissionLower.MergedInfra6815_6
import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.MergedInfra6815_10
set_option Elab.async false
-- Modified from prior Proximity Prize sources.
section MergedPart3
namespace ProximityPrize.SubmissionLower.MovingFiberProfile6815
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider
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
end
end ProximityPrize.SubmissionLower.MovingFiberProfile6815
end MergedPart3

section MergedPart5
namespace ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6815
open scoped BigOperators
open RCN095 RCN146 RCN260 RCN294 RCN327 LocatorHybridCells LocatorHybridCellsC1
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def normal (a b c : ℕ) : FlagDegree := ⟨131074*c,131074*b+131076,131074*a+262148⟩
def raw (a b c : ℕ) : FlagDegree := ⟨131073*c,131073*b+262146,131073*a+393218⟩
end ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6815
end MergedPart5
