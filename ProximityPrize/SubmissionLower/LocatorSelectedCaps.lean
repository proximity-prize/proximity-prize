import ProximityPrize.SubmissionLower.LocatorSelection
import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
import ProximityPrize.SubmissionLower.AB

namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance:GCDMonoid P4:=UniqueFactorizationMonoid.toGCDMonoid P4

theorem common_C_flag {u0 u1:I → K} (S:SelectedPair u0 u1):
    gcd S.QA S.QB∈globalCoefficientBox K 8187885 131071 24496 13:=
  LocatorCaps.full_C_divisor_mem_box u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_C

theorem common_total_le {u0 u1:I → K} (S:SelectedPair u0 u1):
    wt residualTotalWeights (gcd S.QA S.QB)≤1469:=
  LocatorCaps.common_B_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B

theorem common_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1):
    wt residualYSWeights (gcd S.QA S.QB)≤60:=
  LocatorCaps.common_C_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_C_flag S.common_divides_C

theorem common_slope_le {u0 u1:I → K} (S:SelectedPair u0 u1):
    wt residualSWeights (gcd S.QA S.QB)≤13:=
  ((mem_flagGlobalCoefficientBox_iff (gcd S.QA S.QB)
    8187885 131071 24496 13 (by decide)).mp S.common_C_flag).2.1

private theorem factor_divides_common {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hdiv:F∣RCN259.gcd12 S.QA S.QB):F∣gcd S.QA S.QB:=by
  simpa only [RCN259.gcd12] using hdiv

theorem factor_r10_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=10):
    wt residualYSWeights F≤56:=by
  refine LocatorIrreducibleCaps.full_R10_r10_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact (factor_divides_common S F hdiv).trans (S.common_divides_R10 v)

theorem factor_r11_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=11):
    wt residualYSWeights F≤52:=by
  refine LocatorIrreducibleCaps.full_R11_r11_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact (factor_divides_common S F hdiv).trans (S.common_divides_R11 v)

theorem factor_r12_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=12):
    wt residualYSWeights F≤48:=by
  refine LocatorIrreducibleCaps.full_R1213_r12_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact (factor_divides_common S F hdiv).trans (S.common_divides_R1213 v)

theorem factor_r13_ys_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=13):
    wt residualYSWeights F≤44:=by
  refine LocatorIrreducibleCaps.full_R1213_r13_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact (factor_divides_common S F hdiv).trans (S.common_divides_R1213 v)

private theorem factor_total_divides {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hdiv:F∣RCN259.gcd12 S.QA S.QB):
    ∀ v:TotalKernel u0 u1,
      F∣reconstruct K 21834360 131071 2505 37 v.1:=by
  intro v
  exact (factor_divides_common S F hdiv).trans (S.common_divides_Total v)

theorem factor_r9_ys60_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=9) (hY:60≤wt residualYSWeights F):
    wt residualTotalWeights F≤1252:=
  LocatorIrreducibleCaps.full_Total_r9_ys60_factor_total_le
    u0 u1 F hF (factor_total_divides S F hdiv) hR hY

theorem factor_r10_ys40_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=10) (hY:40≤wt residualYSWeights F):
    wt residualTotalWeights F≤1406:=
  LocatorIrreducibleCaps.full_Total_r10_ys40_factor_total_le
    u0 u1 F hF (factor_total_divides S F hdiv) hR hY

theorem factor_r11_ys36_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=11) (hY:36≤wt residualYSWeights F):
    wt residualTotalWeights F≤1407:=
  LocatorIrreducibleCaps.full_Total_r11_ys36_factor_total_le
    u0 u1 F hF (factor_total_divides S F hdiv) hR hY

theorem factor_r12_ys32_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=12) (hY:32≤wt residualYSWeights F):
    wt residualTotalWeights F≤1405:=
  LocatorIrreducibleCaps.full_Total_r12_ys32_factor_total_le
    u0 u1 F hF (factor_total_divides S F hdiv) hR hY

theorem factor_r13_ys27_total_le {u0 u1:I → K} (S:SelectedPair u0 u1)
    (F:P4) (hF:Irreducible F) (hdiv:F∣RCN259.gcd12 S.QA S.QB)
    (hR:F.degreeOf (2:Fin 4)=13) (hY:27≤wt residualYSWeights F):
    wt residualTotalWeights F≤1408:=
  LocatorIrreducibleCaps.full_Total_r13_ys27_factor_total_le
    u0 u1 F hF (factor_total_divides S F hdiv) hR hY

end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
