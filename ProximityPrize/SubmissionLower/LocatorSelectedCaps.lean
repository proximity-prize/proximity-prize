import ProximityPrize.SubmissionLower.LocatorSelection
import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.AB
namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_C_flag {u0 u1:I → K} (S:SelectedPair u0 u1) :
    gcd S.QA S.QB ∈ globalCoefficientBox K 17269670 131071 40000 29 :=
  LocatorCaps.full_C_divisor_mem_box u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_C
theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB)≤2029 :=
  LocatorCaps.common_B_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB)≤71 :=
  LocatorCaps.common_A_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_A
theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB)≤15 :=
  LocatorCaps.common_Thin_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_Thin
theorem common_degreeR_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    (gcd S.QA S.QB).degreeOf (2:Fin 4)≤15:=by
  simpa only [LocatorContact.slope_weight_eq_degreeR] using S.common_slope_le
end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
