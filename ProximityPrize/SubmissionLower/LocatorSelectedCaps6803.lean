import ProximityPrize.SubmissionLower.LocatorCapsB6803
import ProximityPrize.SubmissionLower.LocatorSelection6803
import ProximityPrize.SubmissionLower.LocatorTCap6803

namespace ProximityPrize.SubmissionLower.LocatorSelection6803.SelectedPair

open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN234 RCN156

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

local instance : GCDMonoid P4 :=
  UniqueFactorizationMonoid.toGCDMonoid P4

theorem common_ne {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    gcd S.QA S.QB ≠ 0 :=
  gcd_ne_zero_of_left S.QA_ne

theorem common_divides_TCap_kernel {u0 u1 : I → K}
    (S : SelectedPair u0 u1) :
    ∀ v : TCapKernel u0 u1,
      gcd S.QA S.QB ∣ reconstruct K 32826703 131071 6679 56 v.1 :=
  S.common_divides_TCap

theorem common_divides_B_kernel {u0 u1 : I → K}
    (S : SelectedPair u0 u1) :
    ∀ v : BKernel u0 u1,
      gcd S.QA S.QB ∣ reconstruct K 20131293 131071 14261 34 v.1 :=
  S.common_divides_B

theorem common_TCap_box {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    gcd S.QA S.QB ∈
      globalCoefficientBox K 32826703 131071 6679 56 :=
  LocatorTCap6803.full_TCap_divisor_mem_box u0 u1 _ S.common_ne
    S.common_divides_TCap

theorem common_B_box {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    gcd S.QA S.QB ∈
      globalCoefficientBox K 20131293 131071 14261 34 :=
  LocatorCapsB6803.full_B_divisor_mem_box u0 u1 _ S.common_ne
    S.common_divides_B

theorem common_B_total_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 14261 :=
  ((mem_flagGlobalCoefficientBox_iff (gcd S.QA S.QB)
    20131293 131071 14261 34 (by decide)).mp S.common_B_box).1

theorem common_total_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualTotalWeights (gcd S.QA S.QB) ≤ 6676 :=
  LocatorTCap6803.common_total_le u0 u1 _
    S.common_ne S.common_divides_TCap

theorem common_ys_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualYSWeights (gcd S.QA S.QB) ≤ 153 :=
  LocatorCapsB6803.common_B_ys_le u0 u1 _
    S.common_ne S.common_divides_B

theorem common_slope_le {u0 u1 : I → K} (S : SelectedPair u0 u1) :
    wt residualSWeights (gcd S.QA S.QB) ≤ 34 :=
  LocatorCapsB6803.common_B_slope_le u0 u1 _
    S.common_ne S.common_divides_B

end

end ProximityPrize.SubmissionLower.LocatorSelection6803.SelectedPair
