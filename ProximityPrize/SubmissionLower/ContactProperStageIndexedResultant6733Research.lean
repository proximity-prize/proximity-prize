import ProximityPrize.SubmissionLower.ContactProperStageIndexedGeometry6733Research
import ProximityPrize.SubmissionLower.ContactFlagPlaneResultantBounds6733Research
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedResultant6733Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6732Research
open ContactProperFlagFiberData6733Research
open ContactProperStageIndexedFamily6733Research
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
variable (S:Stage K I Gamma x p flag) {A:Type} [Fintype A]
theorem stageFamily_resultant_ne
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6733Research.w+1))
    (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
    stageFamilyResultant S A F≠0:=by
  change flagPlaneResultant F.lam F.mu F.nu F.order S.G
    (globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6733Research.w+1))≠0
  exact flagPlaneResultant_ne F.lam F.mu F.nu F.order S.irreducible_G hfirstProper
    (F.component W.witness.1) (F.ht W.witness.1) F.positive
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedResultant6733Research
