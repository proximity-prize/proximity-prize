import ProximityPrize.SubmissionLower.BoundaryTailRouting6808
namespace ProximityPrize.SubmissionLower.Kernels80840
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace A
theorem coefficient_exact : coefficientCount 19943440 131071 245562 33 = 10193934970574740 := by
  rw [show 19943440 = 152*131071+20648 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 152 20648 131071 245562 33
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 110 245562 33 = 38886775851 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 19943440 131071 245562 33 -
    262144 * localRankBound 110 245562 33 = 1890196 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1890196 ≤ coefficientCount 19943440 131071 245562 33 -
    262144 * localRankBound 110 245562 33 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 1890196 := by decide
theorem shape : 19943440+33 ≤ 131071*(152+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1890196 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 19943440 131071 245562 33 110
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    19943440 245562 33 110 1890196 u0 u1 nullity_lower
end A

namespace B
theorem coefficient_exact : coefficientCount 23388216 131071 16146 39 = 1076900247026090 := by
  rw [show 23388216 = 178*131071+57578 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 178 57578 131071 16146 39
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 129 16146 39 = 4108048360 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 23388216 131071 16146 39 -
    262144 * localRankBound 129 16146 39 = 17742250 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 17742250 ≤ coefficientCount 23388216 131071 16146 39 -
    262144 * localRankBound 129 16146 39 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 17742250 := by decide
theorem shape : 23388216+39 ≤ 131071*(178+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    17742250 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 23388216 131071 16146 39 129
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    23388216 16146 39 129 17742250 u0 u1 nullity_lower
end B

namespace T
theorem coefficient_exact : coefficientCount 39161664 131071 8486 67 = 2648414951530759 := by
  rw [show 39161664 = 298*131071+102506 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 298 102506 131071 8486 67
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 216 8486 67 = 10102899196 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 39161664 131071 8486 67 -
    262144 * localRankBound 216 8486 67 = 544694535 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 544694535 ≤ coefficientCount 39161664 131071 8486 67 -
    262144 * localRankBound 216 8486 67 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 544694535 := by decide
theorem shape : 39161664+67 ≤ 131071*(298+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    544694535 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 39161664 131071 8486 67 216
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    39161664 8486 67 216 544694535 u0 u1 nullity_lower
theorem quotient_count_exact : coefficientCount 39161664 131071 2 67 = 390305935 := by decide
theorem quotient_count_lt : coefficientCount 39161664 131071 2 67 < 544694535 := by
  rw [quotient_count_exact]
  decide
end T

namespace Source00
theorem coefficient_lower : 30730496746854150400770448 ≤ coefficientCount 11603456000 131071 3840000 19840 := by
  have h := OneResidueLower.oneResidue_le_coefficientCount 88528 2512 131071 3840000 19840
    (by decide) (by decide) (by decide) (by decide)
  exact (show 30730496746854150400770448 = oneResidueCoefficientCount 88528 2512 131071 3840000 19840 by decide).le.trans h
theorem rank_exact : localRankBound 64000 3840000 19840 = 116784455894414962240 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 116152340868634539327888 ≤ coefficientCount 11603456000 131071 3840000 19840 -
    262144 * localRankBound 64000 3840000 19840 := by
  have h := coefficient_lower
  rw [rank_exact]
  omega
theorem positive_kernel : 0 < 116152340868634539327888 := by decide
theorem shape : 11603456000+19840 ≤ 131071*(88528+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    116152340868634539327888 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 11603456000 131071 3840000 19840 64000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    11603456000 3840000 19840 64000 116152340868634539327888 u0 u1 nullity_lower
end Source00

namespace Source01
theorem coefficient_exact : coefficientCount 5801728000 131071 3200000 9888 = 3205399269699120936551120 := by
  rw [show 5801728000 = 44264*131071+1256 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44264 1256 131071 3200000 9888
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 5801728000 131071 3200000 9888 -
    262144 * localRankBound 32000 3200000 9888 = 14381981301127046791888 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 14381981301127046791888 ≤ coefficientCount 5801728000 131071 3200000 9888 -
    262144 * localRankBound 32000 3200000 9888 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 14381981301127046791888 := by decide
theorem shape : 5801728000+9888 ≤ 131071*(44264+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    14381981301127046791888 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5801728000 131071 3200000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5801728000 3200000 9888 32000 14381981301127046791888 u0 u1 nullity_lower
end Source01

namespace Source02
theorem coefficient_exact : coefficientCount 5801728000 131071 2880000 9888 = 2883068952968834210151120 := by
  rw [show 5801728000 = 44264*131071+1256 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44264 1256 131071 2880000 9888
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 5801728000 131071 2880000 9888 -
    262144 * localRankBound 32000 2880000 9888 = 12589981621733099911888 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 12589981621733099911888 ≤ coefficientCount 5801728000 131071 2880000 9888 -
    262144 * localRankBound 32000 2880000 9888 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 12589981621733099911888 := by decide
theorem shape : 5801728000+9888 ≤ 131071*(44264+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    12589981621733099911888 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5801728000 131071 2880000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5801728000 2880000 9888 32000 12589981621733099911888 u0 u1 nullity_lower
end Source02

namespace Source03
theorem coefficient_exact : coefficientCount 2900864000 131071 1062000 4940 = 132533276620795006212207 := by
  rw [show 2900864000 = 22132*131071+628 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22132 628 131071 1062000 4940
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 2900864000 131071 1062000 4940 -
    262144 * localRankBound 16000 1062000 4940 = 519289470505939163247 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 519289470505939163247 ≤ coefficientCount 2900864000 131071 1062000 4940 -
    262144 * localRankBound 16000 1062000 4940 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 519289470505939163247 := by decide
theorem shape : 2900864000+4940 ≤ 131071*(22132+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    519289470505939163247 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2900864000 131071 1062000 4940 16000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    2900864000 1062000 4940 16000 519289470505939163247 u0 u1 nullity_lower
end Source03

namespace Source04
theorem coefficient_exact : coefficientCount 1450432000 131071 531000 2470 = 8285453829954756901320 := by
  rw [show 1450432000 = 11066*131071+314 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11066 314 131071 531000 2470
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 1450432000 131071 531000 2470 -
    262144 * localRankBound 8000 531000 2470 = 32146246142741674440 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 32146246142741674440 ≤ coefficientCount 1450432000 131071 531000 2470 -
    262144 * localRankBound 8000 531000 2470 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 32146246142741674440 := by decide
theorem shape : 1450432000+2470 ≤ 131071*(11066+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    32146246142741674440 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 1450432000 131071 531000 2470 8000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    1450432000 531000 2470 8000 32146246142741674440 u0 u1 nullity_lower
end Source04

namespace Source05
theorem coefficient_exact : coefficientCount 181304000 131071 88902 308 = 2719858185110038715 := by
  rw [show 181304000 = 1383*131071+32807 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1383 32807 131071 88902 308
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 181304000 131071 88902 308 -
    262144 * localRankBound 1000 88902 308 = 10208281388918971 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 10208281388918971 ≤ coefficientCount 181304000 131071 88902 308 -
    262144 * localRankBound 1000 88902 308 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 10208281388918971 := by decide
theorem shape : 181304000+308 ≤ 131071*(1383+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    10208281388918971 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 181304000 131071 88902 308 1000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    181304000 88902 308 1000 10208281388918971 u0 u1 nullity_lower
end Source05

namespace Source06
theorem coefficient_exact : coefficientCount 2538256000 131071 3640000 4267 = 303240755639129521666255 := by
  rw [show 2538256000 = 19365*131071+66085 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19365 66085 131071 3640000 4267
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 14000 3640000 4267 = 1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 2538256000 131071 3640000 4267 -
    262144 * localRankBound 14000 3640000 4267 = 1545113083611437217999 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1545113083611437217999 ≤ coefficientCount 2538256000 131071 3640000 4267 -
    262144 * localRankBound 14000 3640000 4267 := by
  rw [nullity_exact]
theorem positive_kernel : 0 < 1545113083611437217999 := by decide
theorem shape : 2538256000+4267 ≤ 131071*(19365+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1545113083611437217999 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2538256000 131071 3640000 4267 14000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    2538256000 3640000 4267 14000 1545113083611437217999 u0 u1 nullity_lower
end Source06
end ProximityPrize.SubmissionLower.Kernels80840
