import ProximityPrize.SubmissionLower.E2
namespace ProximityPrize.SubmissionLower.RCN255
open RCN135 RCN136
open RCN244
open RCN249
open RCN245
open RCN106
open RCN103
open RCN093 RCN095
open RCN125
open RCN011 RCN021
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
 have hs:=RCN360.bimap_specialization_ne_zero
   (algebraMap (RatFunc Omega) (AdjoinRoot q)) surface
   (hirr.isPrimitive (Nat.ne_of_gt hpositive)) (AdjoinRoot.root q)
 rw [RCN360.bimap_specialization,hcoeff] at hs
 exact hs
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {errorCap : ℕ}
variable {stageSupport : RCN275.ResidualSupportParameters}
variable (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
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
end ProximityPrize.SubmissionLower.RCN255
