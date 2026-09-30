import ProximityPrize.SubmissionLower.MovingSourceCheckedIdentityStage6814
namespace ProximityPrize.SubmissionLower.MovingSourceFirstChargeAlgebra6814
set_option autoImplicit false
set_option maxHeartbeats 300000
open scoped BigOperators
open RCN095

theorem mixed_linear_first (p q r : FlagDegree) :
    flagMixed p q r=p.zOnly*flagMixed unitZFlag q r+
      p.yz*flagMixed unitYZFlag q r+p.all*flagMixed unitAllFlag q r := by
  unfold flagMixed unitZFlag unitYZFlag unitAllFlag
  ring

theorem mixed_sum_linear (p q r s : FlagDegree) :
    flagMixed p q r+flagMixed p q s=
      p.zOnly*(flagMixed unitZFlag q r+flagMixed unitZFlag q s)+
      p.yz*(flagMixed unitYZFlag q r+flagMixed unitYZFlag q s)+
      p.all*(flagMixed unitAllFlag q r+flagMixed unitAllFlag q s) := by
  rw [mixed_linear_first p q r,mixed_linear_first p q s]
  ring

end ProximityPrize.SubmissionLower.MovingSourceFirstChargeAlgebra6814
