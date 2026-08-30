import ProximityPrize.SubmissionLower.LocatorSelection
import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
import ProximityPrize.SubmissionLower.AB
namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_C_flag {u0 u1 : I → K} (S : SelectedPair u0 u1) :
   gcd S.QA S.QB ∈ globalCoefficientBox K 8187885 131071 100000 13 :=
 LocatorCaps.full_C_divisor_mem_box u0 u1 _
   (gcd_ne_zero_of_left S.QA_ne) S.common_divides_C
theorem common_total_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
   wt residualTotalWeights (gcd S.QA S.QB) ≤ 1469 :=
 LocatorCaps.common_B_total_le u0 u1 _
   (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
theorem common_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
   wt residualYSWeights (gcd S.QA S.QB) ≤ 60 :=
 LocatorCaps.common_C_ys_le u0 u1 _
   (gcd_ne_zero_of_left S.QA_ne) S.common_C_flag S.common_divides_C
theorem common_slope_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
   wt residualSWeights (gcd S.QA S.QB) ≤ 13 :=
 ((mem_flagGlobalCoefficientBox_iff (gcd S.QA S.QB)
   8187885 131071 100000 13 (by decide)).mp S.common_C_flag).2.1
theorem factor_r13_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1)
   (F : P4) (hF : Irreducible F) (hdiv : F ∣ RCN259.gcd12 S.QA S.QB)
   (hR : F.degreeOf (2 : Fin 4) = 13) :
   wt residualYSWeights F ≤ 56 := by
 have hdivH : F ∣ gcd S.QA S.QB := by
   simpa only [RCN259.gcd12] using hdiv
 refine LocatorIrreducibleCaps.full_C_r13_factor_ys_le u0 u1 F hF ?_ hR
 intro v
 exact hdivH.trans (S.common_divides_C v)
end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
