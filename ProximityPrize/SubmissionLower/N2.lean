import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.C4
namespace ProximityPrize.SubmissionLower.RCN254
open RCN135 RCN136 RCN086 RCN244 RCN245 RCN249 RCN112 RCN103 RCN113 RCN093 RCN095 RCN011
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K I:Type} [Field K]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {Gamma:Finset K} {x:I → K} {p:ℕ} {flag:FlagDegree}
 [CharP (GenericField K) p]
 {errorCap:ℕ}
 {stageSupport:RCN275.ResidualSupportParameters}
 (S:Stage K I Gamma x p flag errorCap stageSupport) {A:Type} [Fintype A]
theorem stageFamily_resultant_ne
   (hfirstProper:¬ S.G∣globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))
   (F:StageIndexedFlagFamily S A) (W:StageIndexedFactor S A F):
   stageFamilyResultant S A F≠0:=by
 change flagPlaneResultant F.lam F.mu F.nu F.order S.G
   (globalTailCut (polynomialEmbedding K) S.F
     (RCN326.w+1))≠0
 exact flagPlaneResultant_ne F.lam F.mu F.nu F.order S.irreducible_G hfirstProper
   (F.component W.witness.1) (F.ht W.witness.1) F.positive
end
end ProximityPrize.SubmissionLower.RCN254
