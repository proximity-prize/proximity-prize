import ProximityPrize.SubmissionLower.N0
namespace ProximityPrize.SubmissionLower.RCN253
open RCN135 RCN086
open RCN244
open RCN249
open RCN250
open RCN252
open RCN095
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {errorCap : ℕ}
variable {stageSupport : RCN275.ResidualSupportParameters}
variable {A:Type} [Fintype A]
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
