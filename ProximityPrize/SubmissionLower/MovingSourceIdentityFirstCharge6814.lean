import ProximityPrize.SubmissionLower.MovingSourceFirstChargeAlgebra6814

/-! Identity Stages consume only their share of the fixed first-cut
charge. They must not add another whole mixed-pair budget in the outer
sum. The scalar absorption is proved for every Stage flag. -/
namespace ProximityPrize.SubmissionLower.MovingSourceIdentityFirstCharge6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 25000
open scoped BigOperators
open RCN095 RCN198 RCN327 LocatorHybridCells MovingSourcePairRetainedStage6814
open MovingSourceFirstChargeAlgebra6814

def fixedFirst (p : FlagDegree) : ℕ :=
  ∑ j : Fin 3, MovingFiberThreeSources6811.weight (BoundaryTailProvider.cellNormal 3561 57 12) j*
    flagMixed p (HFreeDir6813.hfreeFirstDir 3561 57 12 j) (MovingFiberThreeSources6811.direction j)
def identityDegree (p : FlagDegree) : ℕ :=
  RCN146.identityCurveDegree p (cellA 3561 57) (cellB 57 12) (cellS 12) RCN326.w

theorem fixedFirst_linear (p : FlagDegree) :
    fixedFirst p=p.zOnly*fixedFirst unitZFlag+p.yz*fixedFirst unitYZFlag+p.all*fixedFirst unitAllFlag := by
  exact sum_mixed_linear (fun j : Fin 3 => MovingFiberThreeSources6811.weight
    (BoundaryTailProvider.cellNormal 3561 57 12) j)
    (HFreeDir6813.hfreeFirstDir 3561 57 12) MovingFiberThreeSources6811.direction p

theorem identityDegree_linear (p : FlagDegree) :
    identityDegree p=p.zOnly*identityDegree unitZFlag+p.yz*identityDegree unitYZFlag+p.all*identityDegree unitAllFlag := by
  exact mixed_sum_linear p (RCN203.paddedCut (cellA 3561 57) (cellB 57 12) (cellS 12) (RCN326.w+1))
    unitZFlag unitYZFlag

theorem fixed_z : fixedFirst unitZFlag=33071778890064 := by decide +kernel
theorem fixed_u : fixedFirst unitYZFlag=2380841183499120 := by decide +kernel
theorem fixed_v : fixedFirst unitAllFlag=12983732894585712 := by decide +kernel
theorem identity_z : identityDegree unitZFlag=3014679 := by decide +kernel
theorem identity_u : identityDegree unitYZFlag=6029358 := by decide +kernel
theorem identity_v : identityDegree unitAllFlag=947919938 := by decide +kernel

theorem identity_first_unit (j : Fin 3) :
    3*131073*80890*identityDegree (MovingFiberThreeSources6811.direction j)≤
      50184*fixedFirst (MovingFiberThreeSources6811.direction j) := by
  fin_cases j
  · change 3*131073*80890*identityDegree unitZFlag≤50184*fixedFirst unitZFlag
    norm_num only [identity_z,fixed_z]
  · change 3*131073*80890*identityDegree unitYZFlag≤50184*fixedFirst unitYZFlag
    norm_num only [identity_u,fixed_u]
  · change 3*131073*80890*identityDegree unitAllFlag≤50184*fixedFirst unitAllFlag
    norm_num only [identity_v,fixed_v]

theorem identity_absorbed_in_first (p : FlagDegree) :
    3*131073*80890*identityDegree p≤50184*fixedFirst p := by
  rw [identityDegree_linear,fixedFirst_linear]
  exact weighted_three_le p.zOnly p.yz p.all
    (identityDegree unitZFlag) (identityDegree unitYZFlag) (identityDegree unitAllFlag)
    (fixedFirst unitZFlag) (fixedFirst unitYZFlag) (fixedFirst unitAllFlag)
    (3*131073*80890) 50184 (identity_first_unit 0) (identity_first_unit 1) (identity_first_unit 2)

#print axioms identity_absorbed_in_first
end
end ProximityPrize.SubmissionLower.MovingSourceIdentityFirstCharge6814
