import ProximityPrize.SubmissionLower.GenericSlicePoints6807
/-
UNCOMPILED. Reuses the frozen original-DVR multiplier argument.
It proves an order LOWER BOUND. It does not claim that arbitrary field
extension preserves the original DVR order exactly.
-/
import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.FirstCutMultiplicityTransport6807
open RCN244 RCN135 RCN095 RCN074 RCN218 RCN186 RCN310 RCN313 RCN086 RCN217 RCN248
noncomputable section
set_option autoImplicit false
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

end
end ProximityPrize.SubmissionLower.FirstCutMultiplicityTransport6807
