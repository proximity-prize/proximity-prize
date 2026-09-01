import ProximityPrize.SubmissionLower.LocatorSelection
import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.AB
namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open ProximityPrize.Benchmark
open RCN100 RCN180 RCN234 RCN156
noncomputable section
set_option maxHeartbeats 600000
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 2992:=
  LocatorCaps.common_TCap_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_TCap
theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 88:=
  LocatorCaps.common_A_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_A
theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 19:=
  LocatorCaps.common_A_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_A
end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
