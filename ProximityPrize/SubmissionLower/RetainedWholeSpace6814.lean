import ProximityPrize.SubmissionLower.MovingFiberProfile6811
namespace ProximityPrize.SubmissionLower.RetainedWholeSpace6814
open scoped Classical
open MvPolynomial RCN095 RCN130 RCN135 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open MovingFiberRegularData6811 MovingFiberInterpolation6811 MovingFiberProfile6811
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {nodes : I ↪ K} {u0 u1 : I → K}

end
end ProximityPrize.SubmissionLower.RetainedWholeSpace6814
