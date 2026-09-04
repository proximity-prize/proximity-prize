import ProximityPrize.SubmissionLower.LocatorCaps

/-! Packed from ProximityPrize.SubmissionLower.LocatorSelectedCaps. -/
section PackedLocator_LocatorSelectedCaps
namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 6412:=
  LocatorCaps.common_TCap_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_TCap
theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 153:=
  LocatorCaps.common_B_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 33:=
  LocatorCaps.common_B_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
end PackedLocator_LocatorSelectedCaps

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier64 : True := by trivial
end ProximityPrize.SubmissionLower

