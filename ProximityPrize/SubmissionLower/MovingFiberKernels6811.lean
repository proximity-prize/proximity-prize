import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.MovingFiberKernels6811
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace A
theorem coefficient_exact : coefficientCount 21390450 131071 380088 35 = 19259989490012535 := by
  rw [show 21390450 = 163*131071+25877 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 163 25877 131071 380088 35
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 118 380088 35 = 73471029240 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 21390450 131071 380088 35 -
    262144*localRankBound 118 380088 35 = 921975 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 921975 ≤ coefficientCount 21390450 131071 380088 35 -
    262144*localRankBound 118 380088 35 := by rw [nullity_exact]
theorem positive_kernel : 0 < 921975 := by decide +kernel
theorem shape : 21390450+35 ≤ 131071*(163+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    921975 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 21390450 131071 380088 35 118
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    21390450 380088 35 118 921975 u0 u1 nullity_lower
#print axioms finrank_gap
end A

namespace B
theorem coefficient_exact : coefficientCount 24290850 131071 22192 40 = 1642642931574520 := by
  rw [show 24290850 = 185*131071+42715 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 185 42715 131071 22192 40
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 134 22192 40 = 6266185390 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 24290850 131071 22192 40 -
    262144*localRankBound 134 22192 40 = 28698360 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 28698360 ≤ coefficientCount 24290850 131071 22192 40 -
    262144*localRankBound 134 22192 40 := by rw [nullity_exact]
theorem positive_kernel : 0 < 28698360 := by decide +kernel
theorem shape : 24290850+40 ≤ 131071*(185+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    28698360 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 24290850 131071 22192 40 134
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    24290850 22192 40 134 28698360 u0 u1 nullity_lower
#print axioms finrank_gap
end B

namespace TCap
theorem coefficient_exact : coefficientCount 40968150 131071 9682 70 = 3457309875930871 := by
  rw [show 40968150 = 312*131071+73998 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 312 73998 131071 9682 70
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 226 9682 70 = 13188585688 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 40968150 131071 9682 70 -
    262144*localRankBound 226 9682 70 = 1269335799 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1269335799 ≤ coefficientCount 40968150 131071 9682 70 -
    262144*localRankBound 226 9682 70 := by rw [nullity_exact]
theorem positive_kernel : 0 < 1269335799 := by decide +kernel
theorem shape : 40968150+70 ≤ 131071*(312+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1269335799 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 40968150 131071 9682 70 226
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    40968150 9682 70 226 1269335799 u0 u1 nullity_lower
#print axioms finrank_gap
end TCap

namespace Source00
theorem coefficient_exact : coefficientCount 11601418725 131071 3840000 19840 = 30718452132706767232490917 := by
  rw [show 11601418725 = 88512*131071+62373 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 88512 62373 131071 3840000 19840
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 63999 3840000 19840 = 116780376202356671680 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 11601418725 131071 3840000 19840 -
    262144*localRankBound 63999 3840000 19840 = 105177193516179891608997 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 105177193516179891608997 ≤ coefficientCount 11601418725 131071 3840000 19840 -
    262144*localRankBound 63999 3840000 19840 := by rw [nullity_exact]
theorem positive_kernel : 0 < 105177193516179891608997 := by decide +kernel
theorem shape : 11601418725+19840 ≤ 131071*(88512+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    105177193516179891608997 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 11601418725 131071 3840000 19840 63999
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    11601418725 3840000 19840 63999 105177193516179891608997 u0 u1 nullity_lower
#print axioms finrank_gap
end Source00

namespace Source01
theorem coefficient_exact : coefficientCount 5800618725 131071 3200000 9888 = 3204029723104132234936536 := by
  rw [show 5800618725 = 44255*131071+71620 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44255 71620 131071 3200000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 31999 3200000 9888 = 12171913805696239760 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5800618725 131071 3200000 9888 -
    262144*localRankBound 31999 3200000 9888 = 13235550423697159291096 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 13235550423697159291096 ≤ coefficientCount 5800618725 131071 3200000 9888 -
    262144*localRankBound 31999 3200000 9888 := by rw [nullity_exact]
theorem positive_kernel : 0 < 13235550423697159291096 := by decide +kernel
theorem shape : 5800618725+9888 ≤ 131071*(44255+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    13235550423697159291096 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5800618725 131071 3200000 9888 31999
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    5800618725 3200000 9888 31999 13235550423697159291096 u0 u1 nullity_lower
#print axioms finrank_gap
end Source01

namespace Source02
theorem coefficient_exact : coefficientCount 5800618725 131071 2880000 9888 = 2881837417552635807416536 := by
  rw [show 5800618725 = 44255*131071+71620 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44255 71620 131071 2880000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 31999 2880000 9888 = 10949242782285039760 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5800618725 131071 2880000 9888 -
    262144*localRankBound 31999 2880000 9888 = 11559117633306344571096 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 11559117633306344571096 ≤ coefficientCount 5800618725 131071 2880000 9888 -
    262144*localRankBound 31999 2880000 9888 := by rw [nullity_exact]
theorem positive_kernel : 0 < 11559117633306344571096 := by decide +kernel
theorem shape : 5800618725+9888 ≤ 131071*(44255+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    11559117633306344571096 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5800618725 131071 2880000 9888 31999
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    5800618725 2880000 9888 31999 11559117633306344571096 u0 u1 nullity_lower
#print axioms finrank_gap
end Source02

namespace Source03
theorem coefficient_exact : coefficientCount 2900400000 131071 1062000 4940 = 132485959385433055757223 := by
  rw [show 2900400000 = 22128*131071+60912 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22128 60912 131071 1062000 4940
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2900400000 131071 1062000 4940 -
    262144*localRankBound 16000 1062000 4940 = 471972235143988708263 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 471972235143988708263 ≤ coefficientCount 2900400000 131071 1062000 4940 -
    262144*localRankBound 16000 1062000 4940 := by rw [nullity_exact]
theorem positive_kernel : 0 < 471972235143988708263 := by decide +kernel
theorem shape : 2900400000+4940 ≤ 131071*(22128+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    471972235143988708263 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2900400000 131071 1062000 4940 16000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    2900400000 1062000 4940 16000 471972235143988708263 u0 u1 nullity_lower
#print axioms finrank_gap
end Source03

namespace Source04
theorem coefficient_exact : coefficientCount 1450200000 131071 531000 2470 = 8282495835096086111235 := by
  rw [show 1450200000 = 11064*131071+30456 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11064 30456 131071 531000 2470
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 1450200000 131071 531000 2470 -
    262144*localRankBound 8000 531000 2470 = 29188251284070884355 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 29188251284070884355 ≤ coefficientCount 1450200000 131071 531000 2470 -
    262144*localRankBound 8000 531000 2470 := by rw [nullity_exact]
theorem positive_kernel : 0 < 29188251284070884355 := by decide +kernel
theorem shape : 1450200000+2470 ≤ 131071*(11064+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    29188251284070884355 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 1450200000 131071 531000 2470 8000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    1450200000 531000 2470 8000 29188251284070884355 u0 u1 nullity_lower
#print axioms finrank_gap
end Source04

namespace Source05
theorem coefficient_exact : coefficientCount 181275000 131071 88902 308 = 2718886728357158715 := by
  rw [show 181275000 = 1383*131071+3807 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1383 3807 131071 88902 308
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 181275000 131071 88902 308 -
    262144*localRankBound 1000 88902 308 = 9236824636038971 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 9236824636038971 ≤ coefficientCount 181275000 131071 88902 308 -
    262144*localRankBound 1000 88902 308 := by rw [nullity_exact]
theorem positive_kernel : 0 < 9236824636038971 := by decide +kernel
theorem shape : 181275000+308 ≤ 131071*(1383+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    9236824636038971 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 181275000 131071 88902 308 1000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    181275000 88902 308 1000 9236824636038971 u0 u1 nullity_lower
#print axioms finrank_gap
end Source05

namespace Source06
theorem coefficient_exact : coefficientCount 2537850000 131071 3640000 4267 = 303132392221649288519353 := by
  rw [show 2537850000 = 19362*131071+53298 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19362 53298 131071 3640000 4267
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 14000 3640000 4267 = 1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2537850000 131071 3640000 4267 -
    262144*localRankBound 14000 3640000 4267 = 1436749666131204071097 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1436749666131204071097 ≤ coefficientCount 2537850000 131071 3640000 4267 -
    262144*localRankBound 14000 3640000 4267 := by rw [nullity_exact]
theorem positive_kernel : 0 < 1436749666131204071097 := by decide +kernel
theorem shape : 2537850000+4267 ≤ 131071*(19362+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1436749666131204071097 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2537850000 131071 3640000 4267 14000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    2537850000 3640000 4267 14000 1436749666131204071097 u0 u1 nullity_lower
#print axioms finrank_gap
end Source06

namespace TCap
theorem quotient_count_exact : coefficientCount 40968150 131071 3 70 = 815430885 := by decide +kernel
theorem quotient_count_lt : coefficientCount 40968150 131071 3 70 < 1269335799 := by
  rw [quotient_count_exact]
  decide +kernel
end TCap

end ProximityPrize.SubmissionLower.MovingFiberKernels6811
