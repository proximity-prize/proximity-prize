import ProximityPrize.SubmissionLower.BoundaryTailRouting6808
namespace ProximityPrize.SubmissionLower.Kernels80830
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace A
theorem coefficient_exact : coefficientCount 19581912 131071 233846 32 = 9110872339832978 := by
  rw [show 19581912 = 149*131071+52333 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 149 52333 131071 233846 32
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 108 233846 32 = 34755219796 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 19581912 131071 233846 32 -
    262144 * localRankBound 108 233846 32 = 1630354 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1630354 ≤ coefficientCount 19581912 131071 233846 32 -
    262144 * localRankBound 108 233846 32 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 1630354 := by decide
theorem shape : 19581912+32 ≤ 131071*(149+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1630354 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 19581912 131071 233846 32 108
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    19581912 233846 32 108 1630354 u0 u1 nullity_lower
end A

namespace B
theorem coefficient_exact : coefficientCount 20488482 131071 38915 35 = 1789038716553237 := by
  rw [show 20488482 = 156*131071+41406 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 156 41406 131071 38915 35
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 113 38915 35 = 6824641092 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 20488482 131071 38915 35 -
    262144 * localRankBound 113 38915 35 = 2131989 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 2131989 ≤ coefficientCount 20488482 131071 38915 35 -
    262144 * localRankBound 113 38915 35 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 2131989 := by decide
theorem shape : 20488482+35 ≤ 131071*(156+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    2131989 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 20488482 131071 38915 35 113
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    20488482 38915 35 113 2131989 u0 u1 nullity_lower
end B

namespace T
theorem coefficient_exact : coefficientCount 38619882 131071 8125 66 = 2429565902131987 := by
  rw [show 38619882 = 294*131071+85008 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 294 85008 131071 8125 66
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 213 8125 66 = 9268053854 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 38619882 131071 8125 66 -
    262144 * localRankBound 213 8125 66 = 1192629011 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1192629011 ≤ coefficientCount 38619882 131071 8125 66 -
    262144 * localRankBound 213 8125 66 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 1192629011 := by decide
theorem shape : 38619882+66 ≤ 131071*(294+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1192629011 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 38619882 131071 8125 66 213
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    38619882 8125 66 213 1192629011 u0 u1 nullity_lower
theorem quotient_count_exact : coefficientCount 38619882 131071 3 66 = 768465525 := by decide
theorem quotient_count_lt : coefficientCount 38619882 131071 3 66 < 1192629011 := by
  rw [quotient_count_exact]
  decide
end T

namespace Source00
theorem coefficient_lower : 30734280990071327650919932 ≤ coefficientCount 11604096000 131071 3840000 19840 := by
  have h := OneResidueLower.oneResidue_le_coefficientCount 88532 118228 131071 3840000 19840
    (by decide) (by decide) (by decide) (by decide)
  exact (show 30734280990071327650919932 = oneResidueCoefficientCount 88532 118228 131071 3840000 19840 by decide).le.trans h
theorem rank_exact : localRankBound 64000 3840000 19840 = 116784455894414962240 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 119936584085811789477372 ≤ coefficientCount 11604096000 131071 3840000 19840 -
    262144 * localRankBound 64000 3840000 19840 := by
  have h := coefficient_lower
  rw [rank_exact]
  omega
theorem positive_kernel : 0 < 119936584085811789477372 := by decide
theorem shape : 11604096000+19840 ≤ 131071*(88533+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    119936584085811789477372 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 11604096000 131071 3840000 19840 64000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    11604096000 3840000 19840 64000 119936584085811789477372 u0 u1 nullity_lower
end Source00

namespace Source01
theorem coefficient_exact : coefficientCount 5802048000 131071 3200000 9888 = 3205794406975651055685406 := by
  rw [show 5802048000 = 44266*131071+59114 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44266 59114 131071 3200000 9888
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 5802048000 131071 3200000 9888 -
    262144 * localRankBound 32000 3200000 9888 = 14777118577657165926174 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 14777118577657165926174 ≤ coefficientCount 5802048000 131071 3200000 9888 -
    262144 * localRankBound 32000 3200000 9888 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 14777118577657165926174 := by decide
theorem shape : 5802048000+9888 ≤ 131071*(44266+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    14777118577657165926174 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5802048000 131071 3200000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5802048000 3200000 9888 32000 14777118577657165926174 u0 u1 nullity_lower
end Source01

namespace Source02
theorem coefficient_exact : coefficientCount 5802048000 131071 2880000 9888 = 2883424271659386651525406 := by
  rw [show 5802048000 = 44266*131071+59114 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44266 59114 131071 2880000 9888
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 5802048000 131071 2880000 9888 -
    262144 * localRankBound 32000 2880000 9888 = 12945300312285541286174 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 12945300312285541286174 ≤ coefficientCount 5802048000 131071 2880000 9888 -
    262144 * localRankBound 32000 2880000 9888 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 12945300312285541286174 := by decide
theorem shape : 5802048000+9888 ≤ 131071*(44266+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    12945300312285541286174 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5802048000 131071 2880000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5802048000 2880000 9888 32000 12945300312285541286174 u0 u1 nullity_lower
end Source02

namespace Source03
theorem coefficient_exact : coefficientCount 2901024000 131071 1062000 4940 = 132549594946438988298483 := by
  rw [show 2901024000 = 22133*131071+29557 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22133 29557 131071 1062000 4940
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 2901024000 131071 1062000 4940 -
    262144 * localRankBound 16000 1062000 4940 = 535607796149921249523 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 535607796149921249523 ≤ coefficientCount 2901024000 131071 1062000 4940 -
    262144 * localRankBound 16000 1062000 4940 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 535607796149921249523 := by decide
theorem shape : 2901024000+4940 ≤ 131071*(22133+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    535607796149921249523 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2901024000 131071 1062000 4940 16000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    2901024000 1062000 4940 16000 535607796149921249523 u0 u1 nullity_lower
end Source03

namespace Source04
theorem coefficient_exact : coefficientCount 1450512000 131071 531000 2470 = 8286473974303856581320 := by
  rw [show 1450512000 = 11066*131071+80314 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11066 80314 131071 531000 2470
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 1450512000 131071 531000 2470 -
    262144 * localRankBound 8000 531000 2470 = 33166390491841354440 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 33166390491841354440 ≤ coefficientCount 1450512000 131071 531000 2470 -
    262144 * localRankBound 8000 531000 2470 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 33166390491841354440 := by decide
theorem shape : 1450512000+2470 ≤ 131071*(11066+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    33166390491841354440 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 1450512000 131071 531000 2470 8000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    1450512000 531000 2470 8000 33166390491841354440 u0 u1 nullity_lower
end Source04

namespace Source05
theorem coefficient_exact : coefficientCount 181314000 131071 88902 308 = 2720193170197238715 := by
  rw [show 181314000 = 1383*131071+42807 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1383 42807 131071 88902 308
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 181314000 131071 88902 308 -
    262144 * localRankBound 1000 88902 308 = 10543266476118971 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 10543266476118971 ≤ coefficientCount 181314000 131071 88902 308 -
    262144 * localRankBound 1000 88902 308 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 10543266476118971 := by decide
theorem shape : 181314000+308 ≤ 131071*(1383+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    10543266476118971 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 181314000 131071 88902 308 1000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    181314000 88902 308 1000 10543266476118971 u0 u1 nullity_lower
end Source05

namespace Source06
theorem coefficient_exact : coefficientCount 2538396000 131071 3640000 4267 = 303278126831381883117805 := by
  rw [show 2538396000 = 19366*131071+75014 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19366 75014 131071 3640000 4267
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 14000 3640000 4267 = 1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 2538396000 131071 3640000 4267 -
    262144 * localRankBound 14000 3640000 4267 = 1582484275863798669549 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1582484275863798669549 ≤ coefficientCount 2538396000 131071 3640000 4267 -
    262144 * localRankBound 14000 3640000 4267 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 1582484275863798669549 := by decide
theorem shape : 2538396000+4267 ≤ 131071*(19366+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1582484275863798669549 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2538396000 131071 3640000 4267 14000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    2538396000 3640000 4267 14000 1582484275863798669549 u0 u1 nullity_lower
end Source06
end ProximityPrize.SubmissionLower.Kernels80830
