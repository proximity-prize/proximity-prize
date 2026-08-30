import ProximityPrize.SubmissionLower.RFreeBasisOrders

set_option autoImplicit true

section
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedSpecialization6735Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactProperDelayedTailCertificate6735Research
open ContactProperStageIndexedFamily6735Research
open ContactProperFlagFiberData6733Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneFiberSurface6733Research
open ContactFlagAffineFamilyDegree6543Research ContactFlagBezout6543Research
open ContactFlagTriangularProjectionResearch
open ActualPlaneCoordinateKernel ArbitraryPlaneEvaluationFamilyResearch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {Omega:Type} [Field Omega]
theorem planeSurface_map_adjoinRoot_ne_zero
    (q:Polynomial (RatFunc Omega)) (hq:Irreducible q)
    (surface:PlaneRing Omega) (hirr:Irreducible surface)
    (hpositive:0 < surface.natDegree):
    surface.map (AdjoinRoot.mk q)≠0:=by
  letI:Fact (Irreducible q):=⟨hq⟩
  have hcoeff:Polynomial.eval₂RingHom
      (algebraMap (RatFunc Omega) (AdjoinRoot q))
        (AdjoinRoot.root q)=AdjoinRoot.mk q:=by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,
        AdjoinRoot.mk_C,AdjoinRoot.algebraMap_eq]
    · simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X,AdjoinRoot.mk_X]
  have hs:=PlaneCoefficientExtension.bimap_specialization_ne_zero
    (algebraMap (RatFunc Omega) (AdjoinRoot q)) surface
    (hirr.isPrimitive (Nat.ne_of_gt hpositive)) (AdjoinRoot.root q)
  rw [PlaneCoefficientExtension.bimap_specialization,hcoeff] at hs
  exact hs
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable (S:Stage K I Gamma x p flag) {A:Type} [Fintype A]
def StageFamilySurfaceSpecializationNonzero
    (F:StageIndexedFlagFamily S A)
    (q:Polynomial (RatFunc (GenericField K))):Prop:=
  (stageSurfacePlane S F.lam F.mu F.nu F.order).map (AdjoinRoot.mk q)≠0
theorem stageFamily_surface_specialization_ne
    (F:StageIndexedFlagFamily S A)
    (q:Polynomial (RatFunc (GenericField K))) (hq:Irreducible q)
    (a:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q):
    StageFamilySurfaceSpecializationNonzero S F q:=by
  change (planeMap (GenericField K) F.order
    (flagAlgHom F.lam F.mu F.nu S.G)).map (AdjoinRoot.mk q)≠0
  exact planeSurface_map_adjoinRoot_ne_zero q hq
    (planeMap (GenericField K) F.order (flagAlgHom F.lam F.mu F.nu S.G))
    (transformedSurface_irreducible F.lam F.mu F.nu F.order S.irreducible_G
      (F.component a.1) (F.ht a.1)) F.positive
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedSpecialization6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedResultant6735Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6735Research
open ContactProperFlagFiberData6733Research
open ContactProperStageIndexedFamily6735Research
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
      (ContactTwoTailParameters6735Research.w+1))
    (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
    stageFamilyResultant S A F≠0:=by
  change flagPlaneResultant F.lam F.mu F.nu F.order S.G
    (globalTailCut (polynomialEmbedding K) S.F
      (ContactTwoTailParameters6735Research.w+1))≠0
  exact flagPlaneResultant_ne F.lam F.mu F.nu F.order S.irreducible_G hfirstProper
    (F.component W.witness.1) (F.ht W.witness.1) F.positive
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedResultant6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedFixedFactor6735Research
open scoped Classical BigOperators
open ContactGenericInitialPoint ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6735Research
open ContactProperFlagFiberData6733Research
open ContactProperStageIndexedFamily6735Research
open ContactProperStageIndexedGeometry6735Research
open ContactProperStageIndexedResultant6735Research
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
      (ContactTwoTailParameters6735Research.w+1))
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
end ProximityPrize.SubmissionLower.ContactProperStageIndexedFixedFactor6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedPbar6735Research
open ContactGenericInitialPoint ContactGenericSurface
open ContactDelayedTailMultiplicityProvider6732Research
open ContactProperDelayedTailCertificate6735Research
open ContactProperStageIndexedFamily6735Research
open ContactProperFlagFiberData6733Research
open ContactFlagPlaneIndexedFiber6733Research
open ContactFlagPlaneIndexedFiberCertificate6733Research
open ContactFlagPlaneIndexedFiberSurface6733Research
open ContactFlagPlaneFiberSurface6733Research
open ContactFlagPlaneFiberPrimary6733Research
open ContactLocalizedSurfaceNonzero6733Research
open ContactProperStageIndexedSpecialization6735Research
open ContactProperStageIndexedFixedFactor6735Research
open ContactFlagAffineFamilyDegree6543Research ContactFlagBezout6543Research
open ActualCurveCoordinateField ActualPlaneCoordinateKernel
open ArbitraryPlaneEvaluationFamilyResearch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable (S:Stage K I Gamma x p flag) {A:Type} [Fintype A]
theorem stageFamily_surface_mod_ne
    (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
    StageFamilySurfaceModNonzero S F W:=by
  rcases W with ⟨q,hq,_hqMonic,⟨a,hqeq⟩⟩
  let surface:=stageSurfacePlane S F.lam F.mu F.nu F.order
  have hspecial:=stageFamily_surface_specialization_ne S F q hq
    (⟨a,hqeq⟩:IndexedFactorFiber F.component F.lam F.mu F.nu F.order F.ht q)
  change surface.map (AdjoinRoot.mk q)≠0 at hspecial
  change (indexedFiberSurface q hq surface).map
    (IsLocalRing.residue (FiberCoefficient q hq))≠0
  subst q
  exact localized_surface_residue_ne_zero (GenericField K)
    (CoordinateField (GenericField K) (F.component a).1) F.order
    (flagEvaluation (GenericField K) (F.component a).1 F.lam F.mu F.nu) (F.ht a)
    (F.finite a) surface hspecial
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedPbar6735Research
end
section
namespace ProximityPrize.SubmissionLower.ContactProperStageIndexedPower6735Research
open ContactGenericInitialPoint ContactFirstTailCertificate6731Research
open ContactProperDelayedTailCertificate6735Research
open ContactProperStageIndexedFamily6735Research
open ContactProperStageIndexedFixedFactor6735Research
open ContactProperStageIndexedPbar6735Research
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
      (ContactTwoTailParameters6735Research.w+1))
    (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
    W.q^stageFamilyGroupedExponent S A hfirstProper F W.q∣
      stageFamilyResultant S A F:=
  properStage_indexedFixedFactor_groupedPowerDvd_of_surfaceMod S hfirstProper F W
    (stageFamily_surface_mod_ne S F W)
end
end ProximityPrize.SubmissionLower.ContactProperStageIndexedPower6735Research
end
