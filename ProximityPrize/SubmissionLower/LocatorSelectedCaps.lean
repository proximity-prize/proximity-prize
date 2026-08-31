import ProximityPrize.SubmissionLower.LocatorSelection
import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.AB

/-!
The whole gcd receives its YS and R caps from the thin A48/s14 kernel,
and its total cap from the B94/s29 kernel. In LocatorSelection the thin
kernel is named CKernel; in LocatorCaps it is named AKernel.
-/

namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

theorem common_C_flag {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    gcd S.QA S.QB ∈ globalCoefficientBox K 8729952 131071 109000 14 :=
  LocatorCaps.full_A_divisor_mem_box u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_C

theorem common_total_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 1698 :=
  LocatorCaps.common_B_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B

theorem common_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 64 :=
  LocatorCaps.common_A_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_C

theorem common_slope_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 14 :=
  LocatorCaps.common_A_slope_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_C

theorem common_degreeR_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    (gcd S.QA S.QB).degreeOf (2 : Fin 4) ≤ 14 := by
  simpa only [LocatorContact.slope_weight_eq_degreeR] using S.common_slope_le

end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
