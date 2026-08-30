import ProximityPrize.SubmissionLower.ContactAnchoredProperStageIndexedGeometry6750Research
import ProximityPrize.SubmissionLower.ContactFlagPlaneResultantBounds6733Research
namespace ProximityPrize.SubmissionLower.ContactAnchoredProperStageIndexedResultant6750Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactFirstTailCertificate6731Research
open ContactAnchoredDelayedTailLocalDVR6750Research
open ContactAnchoredProperFlagFiberData6750Research
open ContactAnchoredProperStageIndexedFamily6750Research
open ContactFlagPlaneResultantBounds6733Research
open ContactFlagPlaneFiberSurface6733Research
open ContactFlagPlaneSurfaceLocalAdapter6732Research
open ContactFlagAffineFamilyDegree6543Research ContactFlagBezout6543Research
open ActualPlaneCoordinateKernel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable (S:AnchoredStage K I Gamma x p flag) {A:Type} [Fintype A]
theorem stageFamily_resultant_ne
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (anchoredW+1))
    (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
    stageFamilyResultant S A F≠0:=by
  change flagPlaneResultant F.lam F.mu F.nu F.order S.G
    (globalTailCut (polynomialEmbedding K) S.F
      (anchoredW+1))≠0
  exact flagPlaneResultant_ne F.lam F.mu F.nu F.order S.irreducible_G hfirstProper
    (F.component W.witness.1) (F.ht W.witness.1) F.positive
end
end ProximityPrize.SubmissionLower.ContactAnchoredProperStageIndexedResultant6750Research
