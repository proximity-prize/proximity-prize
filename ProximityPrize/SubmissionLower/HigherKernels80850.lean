import ProximityPrize.SubmissionLower.HigherRouting6810
namespace ProximityPrize.SubmissionLower.Kernels80850
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace A
theorem coefficient_exact : coefficientCount 20486222 131071 157823 34 = 7109078813039525 := by
  rw [show 20486222 = 156*131071+39146 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 156 39146 131071 157823 34
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 113 157823 34 = 27118983500 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 20486222 131071 157823 34 -
    262144 * localRankBound 113 157823 34 = 2415525 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 2415525 ≤ coefficientCount 20486222 131071 157823 34 -
    262144 * localRankBound 113 157823 34 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 2415525 := by decide
theorem shape : 20486222+34 ≤ 131071*(156+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    2415525 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 20486222 131071 157823 34 113
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    20486222 157823 34 113 2415525 u0 u1 nullity_lower
end A

namespace B
theorem coefficient_exact : coefficientCount 21573986 131071 38980 37 = 2094391856650855 := by
  rw [show 21573986 = 164*131071+78342 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 164 78342 131071 38980 37
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 119 38980 37 = 7989470835 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 21573986 131071 38980 37 -
    262144 * localRankBound 119 38980 37 = 14080615 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 14080615 ≤ coefficientCount 21573986 131071 38980 37 -
    262144 * localRankBound 119 38980 37 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 14080615 := by decide
theorem shape : 21573986+37 ≤ 131071*(164+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    14080615 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 21573986 131071 38980 37 119
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    21573986 38980 37 119 14080615 u0 u1 nullity_lower
end B

namespace T
theorem coefficient_exact : coefficientCount 40428562 131071 8870 69 = 3038966664478955 := by
  rw [show 40428562 = 308*131071+58694 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 308 58694 131071 8870 69
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 223 8870 69 = 11592731815 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 40428562 131071 8870 69 -
    262144 * localRankBound 223 8870 69 = 1575567595 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1575567595 ≤ coefficientCount 40428562 131071 8870 69 -
    262144 * localRankBound 223 8870 69 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 1575567595 := by decide
theorem shape : 40428562+69 ≤ 131071*(308+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1575567595 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 40428562 131071 8870 69 223
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    40428562 8870 69 223 1575567595 u0 u1 nullity_lower
theorem quotient_count_exact : coefficientCount 40428562 131071 4 69 = 1405824735 := by decide
theorem quotient_count_lt : coefficientCount 40428562 131071 4 69 < 1575567595 := by
  rw [quotient_count_exact]
  decide
end T

namespace Source00
theorem coefficient_exact : coefficientCount 11602816000 131071 3840000 19840 = 30726712736325466626690088 := by
  rw [show 11602816000 = 88523*131071+17867 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 88523 17867 131071 3840000 19840
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 64000 3840000 19840 = 116784455894414962240 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 11602816000 131071 3840000 19840 -
    262144 * localRankBound 64000 3840000 19840 = 112368330339950765247528 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 112368330339950765247528 ≤ coefficientCount 11602816000 131071 3840000 19840 -
    262144 * localRankBound 64000 3840000 19840 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 112368330339950765247528 := by decide
theorem shape : 11602816000+19840 ≤ 131071*(88523+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    112368330339950765247528 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 11602816000 131071 3840000 19840 64000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    11602816000 3840000 19840 64000 112368330339950765247528 u0 u1 nullity_lower
end Source00

namespace Source01
theorem coefficient_exact : coefficientCount 5801408000 131071 3200000 9888 = 3205004157618378035411216 := by
  rw [show 5801408000 = 44261*131071+74469 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44261 74469 131071 3200000 9888
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 5801408000 131071 3200000 9888 -
    262144 * localRankBound 32000 3200000 9888 = 13986869220384145651984 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 13986869220384145651984 ≤ coefficientCount 5801408000 131071 3200000 9888 -
    262144 * localRankBound 32000 3200000 9888 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 13986869220384145651984 := by decide
theorem shape : 5801408000+9888 ≤ 131071*(44261+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    13986869220384145651984 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5801408000 131071 3200000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5801408000 3200000 9888 32000 13986869220384145651984 u0 u1 nullity_lower
end Source01

namespace Source02
theorem coefficient_exact : coefficientCount 5801408000 131071 2880000 9888 = 2882713656919150111251216 := by
  rw [show 5801408000 = 44261*131071+74469 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44261 74469 131071 2880000 9888
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 5801408000 131071 2880000 9888 -
    262144 * localRankBound 32000 2880000 9888 = 12234685572049001011984 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 12234685572049001011984 ≤ coefficientCount 5801408000 131071 2880000 9888 -
    262144 * localRankBound 32000 2880000 9888 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 12234685572049001011984 := by decide
theorem shape : 5801408000+9888 ≤ 131071*(44261+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    12234685572049001011984 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5801408000 131071 2880000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5801408000 2880000 9888 32000 12234685572049001011984 u0 u1 nullity_lower
end Source02

namespace Source03
theorem coefficient_exact : coefficientCount 2900704000 131071 1062000 4940 = 132516959398586311991535 := by
  rw [show 2900704000 = 22130*131071+102770 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22130 102770 131071 1062000 4940
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 2900704000 131071 1062000 4940 -
    262144 * localRankBound 16000 1062000 4940 = 502972248297244942575 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 502972248297244942575 ≤ coefficientCount 2900704000 131071 1062000 4940 -
    262144 * localRankBound 16000 1062000 4940 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 502972248297244942575 := by decide
theorem shape : 2900704000+4940 ≤ 131071*(22130+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    502972248297244942575 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2900704000 131071 1062000 4940 16000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    2900704000 1062000 4940 16000 502972248297244942575 u0 u1 nullity_lower
end Source03

namespace Source04
theorem coefficient_exact : coefficientCount 1450352000 131071 531000 2470 = 8284433786396315733955 := by
  rw [show 1450352000 = 11065*131071+51385 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11065 51385 131071 531000 2470
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 1450352000 131071 531000 2470 -
    262144 * localRankBound 8000 531000 2470 = 31126202584300507075 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 31126202584300507075 ≤ coefficientCount 1450352000 131071 531000 2470 -
    262144 * localRankBound 8000 531000 2470 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 31126202584300507075 := by decide
theorem shape : 1450352000+2470 ≤ 131071*(11065+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    31126202584300507075 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 1450352000 131071 531000 2470 8000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    1450352000 531000 2470 8000 31126202584300507075 u0 u1 nullity_lower
end Source04

namespace Source05
theorem coefficient_exact : coefficientCount 181294000 131071 88902 308 = 2719523200022838715 := by
  rw [show 181294000 = 1383*131071+22807 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1383 22807 131071 88902 308
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 181294000 131071 88902 308 -
    262144 * localRankBound 1000 88902 308 = 9873296301718971 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 9873296301718971 ≤ coefficientCount 181294000 131071 88902 308 -
    262144 * localRankBound 1000 88902 308 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 9873296301718971 := by decide
theorem shape : 181294000+308 ≤ 131071*(1383+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    9873296301718971 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 181294000 131071 88902 308 1000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    181294000 88902 308 1000 9873296301718971 u0 u1 nullity_lower
end Source05

namespace Source06
theorem coefficient_exact : coefficientCount 2538116000 131071 3640000 4267 = 303203386748257969615367 := by
  rw [show 2538116000 = 19364*131071+57156 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19364 57156 131071 3640000 4267
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 14000 3640000 4267 = 1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 2538116000 131071 3640000 4267 -
    262144 * localRankBound 14000 3640000 4267 = 1507744192739885167111 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1507744192739885167111 ≤ coefficientCount 2538116000 131071 3640000 4267 -
    262144 * localRankBound 14000 3640000 4267 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 1507744192739885167111 := by decide
theorem shape : 2538116000+4267 ≤ 131071*(19364+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1507744192739885167111 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2538116000 131071 3640000 4267 14000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    2538116000 3640000 4267 14000 1507744192739885167111 u0 u1 nullity_lower
end Source06
end ProximityPrize.SubmissionLower.Kernels80850
