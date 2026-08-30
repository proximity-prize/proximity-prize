import ProximityPrize.SubmissionLower.ContactProperStageIndexedGeometry6733Research
import ProximityPrize.SubmissionLower.ContactProperStageIndexedResultant6733Research
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedFixedFactor6733Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6732Research
open ContactProperFlagFiberData6733Research
open ContactProperStageIndexedFamily6733Research
open ContactProperStageIndexedGeometry6733Research
open ContactProperStageIndexedResultant6733Research
open ContactFlagPlaneFiberPrimary6733Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedFiberCertificate6733Research
open ContactFlagPlaneIndexedGrouped6733Research
open ContactFlagResidueDegreeCostAdapter6732Research
open ContactFlagBezout6543Research
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {A:Type} [Fintype A]
def StageFamilySurfaceModNonzero
    (S:Stage K I Gamma x p flag) (F:StageIndexedFlagFamily S A)
    (W:StageIndexedFactor S A F):Prop:=
  (indexedFiberSurface W.q W.irreducible
    (stageSurfacePlane S F.lam F.mu F.nu F.order)).map
      (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0
@[simp] theorem stageFamilySurfaceModNonzero_eq
    (S:Stage K I Gamma x p flag) (F:StageIndexedFlagFamily S A)
    (W:StageIndexedFactor S A F):
    StageFamilySurfaceModNonzero S F W ↔
      (indexedFiberSurface W.q W.irreducible
        (stageSurfacePlane S F.lam F.mu F.nu F.order)).map
          (IsLocalRing.residue (FiberCoefficient W.q W.irreducible))≠0:=Iff.rfl
theorem properStage_indexedFixedFactor_groupedPowerDvd_of_surfaceMod
    (S:Stage K I Gamma x p flag)
    (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6733Research.w+1))
    (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F)
    (hPbar:StageFamilySurfaceModNonzero S F W):
    W.q^stageFamilyGroupedExponent S A hfirstProper F W.q∣
      stageFamilyResultant S A F:=by
  let surface:=stageSurfacePlane S F.lam F.mu F.nu F.order
  let tail:=stageTailPlane S F.lam F.mu F.nu F.order
  letI:(Ideal.span {indexedFiberSurface W.q W.irreducible surface}).IsPrime:=
    stageFamily_surfacePrime S F W
  have hpower:=indexedFixedFactor_grouped_resultant_power_dvd_of_geometry
    F.component F.injective F.lam F.mu F.nu F.order F.ht F.finite F.generates
      W.q W.irreducible W.monic surface tail surface.natDegree tail.natDegree
      (fun a => stageFamily_surface_mem S F W a)
      (fun a => stageFamily_bar_ne S F W hfirstProper a)
      (fun a => localMultiplicity S (canonicalLocalDVRFamily S hfirstProper)
        (F.component a.1))
      (fun a => stageFamily_tail_mem S F W hfirstProper a)
      Polynomial.natDegree_map_le Polynomial.natDegree_map_le
      (stageFamily_resultant_ne S hfirstProper F W) hPbar
  simpa only [stageFamilyGroupedExponent_eq,stageFamilyResultant] using hpower
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedFixedFactor6733Research
