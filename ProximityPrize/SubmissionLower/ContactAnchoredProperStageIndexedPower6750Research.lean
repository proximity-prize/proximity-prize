import ProximityPrize.SubmissionLower.ContactAnchoredProperStageIndexedPbar6750Research
namespace ProximityPrize.SubmissionLower.ContactAnchoredProperStageIndexedPower6750Research
open ContactGenericInitialPoint ContactFirstTailCertificate6731Research
open ContactAnchoredDelayedTailLocalDVR6750Research
open ContactAnchoredProperStageIndexedFamily6750Research
open ContactAnchoredProperStageIndexedFixedFactor6750Research
open ContactAnchoredProperStageIndexedPbar6750Research
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
    (S:AnchoredStage K I Gamma x p flag)
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (anchoredW+1))
    (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
    W.q^stageFamilyGroupedExponent S A hfirstProper F W.q∣
      stageFamilyResultant S A F:=
  properStage_indexedFixedFactor_groupedPowerDvd_of_surfaceMod S hfirstProper F W
    (stageFamily_surface_mod_ne S F W)
end
end ProximityPrize.SubmissionLower.ContactAnchoredProperStageIndexedPower6750Research
