import ProximityPrize.SubmissionLower.N3
import ProximityPrize.SubmissionLower.FZ
namespace ProximityPrize.SubmissionLower.RCN252
open RCN135 RCN136
open RCN074
open RCN244
open RCN249
open RCN245
open RCN106
open RCN107
open RCN108
open RCN103
open RCN102
open RCN195
open RCN255
open RCN250
open RCN093 RCN095
open RCN002 RCN011
open RCN021
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 60000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
variable [CharP (GenericField K) p]
variable {errorCap : ℕ}
variable {stageSupport : RCN275.ResidualSupportParameters}
variable (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
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
end ProximityPrize.SubmissionLower.RCN252
