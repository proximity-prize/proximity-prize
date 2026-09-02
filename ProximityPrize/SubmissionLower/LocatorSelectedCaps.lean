import ProximityPrize.SubmissionLower.LocatorSelection
import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.AB
namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 3411:=
  LocatorCaps.common_TCap_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_TCap
theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 93:=
  LocatorCaps.common_A_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_A
theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 21:=
  LocatorCaps.common_A_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_A
end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
