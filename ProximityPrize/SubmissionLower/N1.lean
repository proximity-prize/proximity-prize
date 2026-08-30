import ProximityPrize.SubmissionLower.N0
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedPower6733Research
open ContactGenericInitialPoint ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6732Research
open ContactProperStageIndexedFamily6733Research
open ContactProperStageIndexedFixedFactor6733Research
open ContactProperStageIndexedPbar6733Research
open ContactFlagBezout6543Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {A:Type} [Fintype A]
theorem properStage_indexedFixedFactor_groupedPowerDvd
   (S:Stage K I Gamma x p flag)
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (ContactTwoTailParameters6733Research.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   W.q^stageFamilyGroupedExponent S A hfirstProper F W.q∣
     stageFamilyResultant S A F:=
 properStage_indexedFixedFactor_groupedPowerDvd_of_surfaceMod S hfirstProper F W
   (stageFamily_surface_mod_ne S F W)
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedPower6733Research
