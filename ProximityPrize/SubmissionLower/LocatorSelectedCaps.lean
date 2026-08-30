import ProximityPrize.SubmissionLower.LocatorSelection
import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
import ProximityPrize.SubmissionLower.AB
namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4
theorem common_C_flag {u0 u1:I → K} (S:SelectedPair u0 u1) :
   gcd S.QA S.QB ∈ globalCoefficientBox K 8551321 131071 100000 13 :=
 LocatorCaps.full_C_divisor_mem_box u0 u1 _
   (gcd_ne_zero_of_left S.QA_ne) S.common_divides_C
theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
   wt residualTotalWeights (gcd S.QA S.QB) ≤ 1495 :=
 LocatorCaps.common_B_total_le u0 u1 _
   (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B
theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
   wt residualYSWeights (gcd S.QA S.QB) ≤ 62 :=
 LocatorCaps.common_C_ys_le u0 u1 _
   (gcd_ne_zero_of_left S.QA_ne) S.common_C_flag S.common_divides_C
theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1) :
   wt residualSWeights (gcd S.QA S.QB) ≤ 13 :=
 ((mem_flagGlobalCoefficientBox_iff (gcd S.QA S.QB)
   8551321 131071 100000 13 (by decide)).mp S.common_C_flag).2.1
private theorem factor_divides_C {u0 u1:I → K} (S:SelectedPair u0 u1)
   (F:P4) (hdiv:F ∣ RCN259.gcd12 S.QA S.QB) :
   ∀ v:LocatorCaps.CKernel u0 u1,
     F ∣ reconstruct K 8551321 131071 100000 13 v.1:=by
 have hdivH:F ∣ gcd S.QA S.QB:=by
   simpa only [RCN259.gcd12] using hdiv
 intro v
 exact hdivH.trans (S.common_divides_C v)
theorem factor_r7_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
   (F:P4) (hF:Irreducible F) (hdiv:F ∣ RCN259.gcd12 S.QA S.QB)
   (hR:F.degreeOf (2:Fin 4) = 7):wt residualYSWeights F ≤ 61 :=
 LocatorIrreducibleCaps.full_C_factor_r7_ys_le u0 u1 F hF
   (factor_divides_C S F hdiv) hR
theorem factor_r8_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
   (F:P4) (hF:Irreducible F) (hdiv:F ∣ RCN259.gcd12 S.QA S.QB)
   (hR:F.degreeOf (2:Fin 4) = 8):wt residualYSWeights F ≤ 61 :=
 LocatorIrreducibleCaps.full_C_factor_r8_ys_le u0 u1 F hF
   (factor_divides_C S F hdiv) hR
theorem factor_r9_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
   (F:P4) (hF:Irreducible F) (hdiv:F ∣ RCN259.gcd12 S.QA S.QB)
   (hR:F.degreeOf (2:Fin 4) = 9):wt residualYSWeights F ≤ 61 :=
 LocatorIrreducibleCaps.full_C_factor_r9_ys_le u0 u1 F hF
   (factor_divides_C S F hdiv) hR
theorem factor_r10_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
   (F:P4) (hF:Irreducible F) (hdiv:F ∣ RCN259.gcd12 S.QA S.QB)
   (hR:F.degreeOf (2:Fin 4) = 10):wt residualYSWeights F ≤ 60 :=
 LocatorIrreducibleCaps.full_C_factor_r10_ys_le u0 u1 F hF
   (factor_divides_C S F hdiv) hR
theorem factor_r11_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
   (F:P4) (hF:Irreducible F) (hdiv:F ∣ RCN259.gcd12 S.QA S.QB)
   (hR:F.degreeOf (2:Fin 4) = 11):wt residualYSWeights F ≤ 60 :=
 LocatorIrreducibleCaps.full_C_factor_r11_ys_le u0 u1 F hF
   (factor_divides_C S F hdiv) hR
theorem factor_r12_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
   (F:P4) (hF:Irreducible F) (hdiv:F ∣ RCN259.gcd12 S.QA S.QB)
   (hR:F.degreeOf (2:Fin 4) = 12):wt residualYSWeights F ≤ 59 :=
 LocatorIrreducibleCaps.full_C_factor_r12_ys_le u0 u1 F hF
   (factor_divides_C S F hdiv) hR
theorem factor_r13_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
   (F:P4) (hF:Irreducible F) (hdiv:F ∣ RCN259.gcd12 S.QA S.QB)
   (hR:F.degreeOf (2:Fin 4) = 13) :
   wt residualYSWeights F ≤ 54 :=
 LocatorIrreducibleCaps.full_C_factor_r13_ys_le u0 u1 F hF
   (factor_divides_C S F hdiv) hR
end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
