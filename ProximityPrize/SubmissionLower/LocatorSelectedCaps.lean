import ProximityPrize.SubmissionLower.LocatorSelection
import ProximityPrize.SubmissionLower.LocatorCaps
import ProximityPrize.SubmissionLower.LocatorIrreducibleCaps
import ProximityPrize.SubmissionLower.AB

/-!
The whole gcd receives its YS and R caps from the C45/s13 kernel and its
total cap from the B87/s27 kernel. The A70 and auxiliary A63
collar caps apply only to irreducible factors of that gcd, by transitivity
of the selected pair's whole-kernel divisibility.
-/

namespace ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4

theorem common_C_flag {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    gcd S.QA S.QB ∈ globalCoefficientBox K 8187435 131071 43759 13 :=
  LocatorCaps.full_C_divisor_mem_box u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_C

theorem common_total_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 1497 :=
  LocatorCaps.common_B_total_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_divides_B

theorem common_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 62 :=
  LocatorCaps.common_C_ys_le u0 u1 _
    (gcd_ne_zero_of_left S.QA_ne) S.common_C_flag S.common_divides_C

theorem common_slope_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 13 :=
  ((mem_flagGlobalCoefficientBox_iff (gcd S.QA S.QB)
    8187435 131071 43759 13 (by decide)).mp S.common_C_flag).2.1

theorem common_degreeR_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    (gcd S.QA S.QB).degreeOf (2 : Fin 4) ≤ 13 := by
  simpa only [LocatorContact.slope_weight_eq_degreeR] using S.common_slope_le

theorem factor_r12_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1)
    (F : P4) (hF : Irreducible F) (hdiv : F ∣ RCN259.gcd12 S.QA S.QB)
    (hR : F.degreeOf (2 : Fin 4) = 12) :
    wt residualYSWeights F ≤ 52 := by
  have hdivH : F ∣ gcd S.QA S.QB := by
    simpa only [RCN259.gcd12] using hdiv
  refine LocatorIrreducibleCaps.full_A_r12_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact hdivH.trans (S.common_divides_A v)

theorem factor_r11_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1)
    (F : P4) (hF : Irreducible F) (hdiv : F ∣ RCN259.gcd12 S.QA S.QB)
    (hR : F.degreeOf (2 : Fin 4) = 11) :
    wt residualYSWeights F ≤ 55 := by
  have hdivH : F ∣ gcd S.QA S.QB := by
    simpa only [RCN259.gcd12] using hdiv
  refine LocatorIrreducibleCaps.full_A_r11_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact hdivH.trans (S.common_divides_A v)

theorem factor_r10_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1)
    (F : P4) (hF : Irreducible F) (hdiv : F ∣ RCN259.gcd12 S.QA S.QB)
    (hR : F.degreeOf (2 : Fin 4) = 10) :
    wt residualYSWeights F ≤ 59 := by
  have hdivH : F ∣ gcd S.QA S.QB := by
    simpa only [RCN259.gcd12] using hdiv
  refine LocatorIrreducibleCaps.full_Aux_r10_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact hdivH.trans (S.common_divides_Aux v)

theorem factor_r13_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1)
    (F : P4) (hF : Irreducible F) (hdiv : F ∣ RCN259.gcd12 S.QA S.QB)
    (hR : F.degreeOf (2 : Fin 4) = 13) :
    wt residualYSWeights F ≤ 47 := by
  have hdivH : F ∣ gcd S.QA S.QB := by
    simpa only [RCN259.gcd12] using hdiv
  refine LocatorIrreducibleCaps.full_A_r13_factor_ys_le u0 u1 F hF ?_ hR
  intro v
  exact hdivH.trans (S.common_divides_A v)

end
end ProximityPrize.SubmissionLower.LocatorSelection.SelectedPair
