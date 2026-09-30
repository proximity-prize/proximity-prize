import ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814
namespace ProximityPrize.SubmissionLower.MovingSourceStageRestriction6814
noncomputable section
set_option autoImplicit false
open RCN135 RCN136 RCN159 RCN174 RCN243 RCN275
variable {K I : Type} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p errorCap d : ℕ} [CharP (GenericField K) p]
  {flag : RCN095.FlagDegree} {support : ResidualSupportParameters}

end
end ProximityPrize.SubmissionLower.MovingSourceStageRestriction6814
