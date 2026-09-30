import ProximityPrize.SubmissionLower.MovingSourceFirstChargeAlgebra6814
namespace ProximityPrize.SubmissionLower.MovingSourceIdentityFirstCharge6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 25000
open scoped BigOperators
open RCN095 RCN198 RCN327 LocatorHybridCells MovingSourcePairRetainedStage6814
open MovingSourceFirstChargeAlgebra6814

def identityDegree (p : FlagDegree) : ℕ :=
  RCN146.identityCurveDegree p (cellA 3561 57) (cellB 57 12) (cellS 12) RCN326.w

theorem identityDegree_linear (p : FlagDegree) :
    identityDegree p=p.zOnly*identityDegree unitZFlag+p.yz*identityDegree unitYZFlag+p.all*identityDegree unitAllFlag := by
  exact mixed_sum_linear p (RCN203.paddedCut (cellA 3561 57) (cellB 57 12) (cellS 12) (RCN326.w+1))
    unitZFlag unitYZFlag

end
end ProximityPrize.SubmissionLower.MovingSourceIdentityFirstCharge6814
