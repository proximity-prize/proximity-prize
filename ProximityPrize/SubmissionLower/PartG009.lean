import ProximityPrize.SubmissionLower.PartG008


section Compact_Kernels80791
/-! Checked kernel ingredients for the proposed error-80791 certificate.
These receipts alone do not assert a protocol claim. -/
namespace ProximityPrize.SubmissionLower.Kernels80791
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace A
theorem coefficient_exact : coefficientCount 17953947 131071 217073 30 = 6649102266853221 := by
  rw [show 17953947 = 136*131071+128291 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 136 128291 131071 217073 30
    (by decide) (by decide) (by decide) (by decide)]
  decide

theorem rank_exact : localRankBound 99 217073 30 = 25364312220 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide

theorem nullity_exact : coefficientCount 17953947 131071 217073 30 -
    262144 * localRankBound 99 217073 30 = 4253541 := by
  norm_num only [coefficient_exact, rank_exact]

theorem shape : 17953947+30 ≤ 131071*(136+1) := by decide

theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    4253541 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 17953947 131071 217073 30 99
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    17953947 217073 30 99 4253541 u0 u1 (by rw [nullity_exact])

end A

namespace B
theorem coefficient_exact : coefficientCount 20130183 131071 17570 33 = 742286632246555 := by
  rw [show 20130183 = 153*131071+76320 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 153 76320 131071 17570 33
    (by decide) (by decide) (by decide) (by decide)]
  decide

theorem rank_exact : localRankBound 111 17570 33 = 2831598455 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide

theorem nullity_exact : coefficientCount 20130183 131071 17570 33 -
    262144 * localRankBound 111 17570 33 = 86859035 := by
  norm_num only [coefficient_exact, rank_exact]

theorem shape : 20130183+33 ≤ 131071*(153+1) := by decide

theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    86859035 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 20130183 131071 17570 33 111
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    20130183 17570 33 111 86859035 u0 u1 (by rw [nullity_exact])

end B

namespace T
theorem coefficient_exact : coefficientCount 35726541 131071 6923 61 = 1638225312367765 := by
  rw [show 35726541 = 272*131071+75229 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 272 75229 131071 6923 61
    (by decide) (by decide) (by decide) (by decide)]
  decide

theorem rank_exact : localRankBound 197 6923 61 = 6249325371 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide

theorem nullity_exact : coefficientCount 35726541 131071 6923 61 -
    262144 * localRankBound 197 6923 61 = 2162312341 := by
  norm_num only [coefficient_exact, rank_exact]

theorem shape : 35726541+61 ≤ 131071*(272+1) := by decide

theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    2162312341 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 35726541 131071 6923 61 197
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    35726541 6923 61 197 2162312341 u0 u1 (by rw [nullity_exact])

theorem quotient_count_lt :
    coefficientCount 35726541 131071 5 61 < 2162312341 := by decide

end T

namespace Source00
theorem coefficient_lower : 30749041762160159459382320 ≤ coefficientCount 11606592000 131071 3840000 19840 := by
  rw [show 11606592000 = 88551*131071+123879 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 88551 123879 131071 3840000 19840
    (by decide) (by decide) (by decide) (by decide)
  exact (show 30749041762160159459382320 = oneResidueCoefficientCount 88551 123879 131071 3840000 19840 by decide).le.trans h

theorem rank_exact : localRankBound 64000 3840000 19840 = 116784455894414962240 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide

theorem nullity_lower : 134697356174643597939760 ≤ coefficientCount 11606592000 131071 3840000 19840 -
    262144 * localRankBound 64000 3840000 19840 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*116784455894414962240)
  rw [rank_exact]
  exact (show 134697356174643597939760 = 30749041762160159459382320-262144*116784455894414962240 by decide).le.trans h

theorem shape : 11606592000+19840 ≤ 131071*(88552+1) := by decide

theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    134697356174643597939760 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 11606592000 131071 3840000 19840 64000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    11606592000 3840000 19840 64000 134697356174643597939760 u0 u1 nullity_lower

end Source00

namespace Source01
theorem coefficient_lower : 3207335673145674579156736 ≤ coefficientCount 5803296000 131071 3200000 9888 := by
  rw [show 5803296000 = 44275*131071+127475 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 44275 127475 131071 3200000 9888
    (by decide) (by decide) (by decide) (by decide)
  exact (show 3207335673145674579156736 = oneResidueCoefficientCount 44275 127475 131071 3200000 9888 by decide).le.trans h

theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide

theorem nullity_lower : 16318384747680689397504 ≤ coefficientCount 5803296000 131071 3200000 9888 -
    262144 * localRankBound 32000 3200000 9888 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*12172764924613929328)
  rw [rank_exact]
  exact (show 16318384747680689397504 = 3207335673145674579156736-262144*12172764924613929328 by decide).le.trans h

theorem shape : 5803296000+9888 ≤ 131071*(44276+1) := by decide

theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    16318384747680689397504 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5803296000 131071 3200000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5803296000 3200000 9888 32000 16318384747680689397504 u0 u1 nullity_lower

end Source01

namespace Source02
theorem coefficient_lower : 2884810221941192670036736 ≤ coefficientCount 5803296000 131071 2880000 9888 := by
  rw [show 5803296000 = 44275*131071+127475 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 44275 127475 131071 2880000 9888
    (by decide) (by decide) (by decide) (by decide)
  exact (show 2884810221941192670036736 = oneResidueCoefficientCount 44275 127475 131071 2880000 9888 by decide).le.trans h

theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide

theorem nullity_lower : 14331250594091559797504 ≤ coefficientCount 5803296000 131071 2880000 9888 -
    262144 * localRankBound 32000 2880000 9888 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*10950008283031849328)
  rw [rank_exact]
  exact (show 14331250594091559797504 = 2884810221941192670036736-262144*10950008283031849328 by decide).le.trans h

theorem shape : 5803296000+9888 ≤ 131071*(44276+1) := by decide

theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    14331250594091559797504 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5803296000 131071 2880000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5803296000 2880000 9888 32000 14331250594091559797504 u0 u1 nullity_lower

end Source02

namespace Source03
theorem coefficient_lower : 132613245729002891234367 ≤ coefficientCount 2901648000 131071 1062000 4940 := by
  rw [show 2901648000 = 22137*131071+129273 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 22137 129273 131071 1062000 4940
    (by decide) (by decide) (by decide) (by decide)
  exact (show 132613245729002891234367 = oneResidueCoefficientCount 22137 129273 131071 1062000 4940 by decide).le.trans h

theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide

theorem nullity_lower : 599258578713824185407 ≤ coefficientCount 2901648000 131071 1062000 4940 -
    262144 * localRankBound 16000 1062000 4940 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*503593395806461590)
  rw [rank_exact]
  exact (show 599258578713824185407 = 132613245729002891234367-262144*503593395806461590 by decide).le.trans h

theorem shape : 2901648000+4940 ≤ 131071*(22138+1) := by decide

theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    599258578713824185407 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2901648000 131071 1062000 4940 16000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    2901648000 1062000 4940 16000 599258578713824185407 u0 u1 nullity_lower

end Source03

namespace Source04
theorem coefficient_lower : 8290453043311497697513 ≤ coefficientCount 1450824000 131071 531000 2470 := by
  rw [show 1450824000 = 11068*131071+130172 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 11068 130172 131071 531000 2470
    (by decide) (by decide) (by decide) (by decide)
  exact (show 8290453043311497697513 = oneResidueCoefficientCount 11068 130172 131071 531000 2470 by decide).le.trans h

theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide

theorem nullity_lower : 37145459499482470633 ≤ coefficientCount 1450824000 131071 531000 2470 -
    262144 * localRankBound 8000 531000 2470 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*31483869872329770)
  rw [rank_exact]
  exact (show 37145459499482470633 = 8290453043311497697513-262144*31483869872329770 by decide).le.trans h

theorem shape : 1450824000+2470 ≤ 131071*(11069+1) := by decide

theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    37145459499482470633 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 1450824000 131071 531000 2470 8000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    1450824000 531000 2470 8000 37145459499482470633 u0 u1 nullity_lower

end Source04

namespace Source05
theorem coefficient_lower : 2721499612037318715 ≤ coefficientCount 181353000 131071 88902 308 := by
  rw [show 181353000 = 1383*131071+81807 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 1383 81807 131071 88902 308
    (by decide) (by decide) (by decide) (by decide)
  exact (show 2721499612037318715 = oneResidueCoefficientCount 1383 81807 131071 88902 308 by decide).le.trans h

theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide

theorem nullity_lower : 11849708316198971 ≤ coefficientCount 181353000 131071 88902 308 -
    262144 * localRankBound 1000 88902 308 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*10336494078526)
  rw [rank_exact]
  exact (show 11849708316198971 = 2721499612037318715-262144*10336494078526 by decide).le.trans h

theorem shape : 181353000+308 ≤ 131071*(1383+1) := by decide

theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    11849708316198971 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 181353000 131071 88902 308 1000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    181353000 88902 308 1000 11849708316198971 u0 u1 nullity_lower

end Source05

end ProximityPrize.SubmissionLower.Kernels80791

end Compact_Kernels80791
