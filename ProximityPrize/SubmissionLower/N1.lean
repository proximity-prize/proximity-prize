import ProximityPrize.SubmissionLower.N0
namespace ProximityPrize.SubmissionLower.RCN253
open RCN135 RCN086 RCN244 RCN249 RCN250 RCN252 RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 {A:Type} [Fintype A]
theorem properStage_indexedFixedFactor_groupedPowerDvd
   (S:Stage K I Gamma x p flag errorCap stageSupport)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   W.q^stageFamilyGroupedExponent S A hfirstProper F W.q∣
     stageFamilyResultant S A F:=
 properStage_indexedFixedFactor_groupedPowerDvd_of_surfaceMod S hfirstProper F W
   (stageFamily_surface_mod_ne S F W)
end
end ProximityPrize.SubmissionLower.RCN253
