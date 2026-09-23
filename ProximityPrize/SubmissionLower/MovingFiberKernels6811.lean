import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.MovingFiberKernels6811
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace A
theorem coefficient_exact : coefficientCount 22476860 131071 202144 36 = 11674614171802651 := by
  rw [show 22476860 = 171*131071+63719 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 171 63719 131071 202144 36
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 124 202144 36 = 44535118746 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
end A

namespace B
theorem coefficient_exact : coefficientCount 24289510 131071 27313 40 = 2022694216449045 := by
  rw [show 24289510 = 185*131071+41375 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 185 41375 131071 27313 40
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 134 27313 40 = 7715966095 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
end B

namespace TCap
theorem coefficient_exact : coefficientCount 40965890 131071 10172 70 = 3634109525134041 := by
  rw [show 40965890 = 312*131071+71738 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 312 71738 131071 10172 70
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 226 10172 70 = 13863024628 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 40965890 131071 10172 70 -
    262144*localRankBound 226 10172 70 = 797051609 := by
  norm_num only [coefficient_exact,rank_exact]
end TCap

namespace Source00
theorem coefficient_exact : coefficientCount 11600778735 131071 3840000 19840 = 30714668921207249212874582 := by
  rw [show 11600778735 = 88507*131071+77738 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 88507 77738 131071 3840000 19840
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 63999 3840000 19840 = 116780376202356671680 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 11600778735 131071 3840000 19840 -
    262144*localRankBound 63999 3840000 19840 = 101393982016661871992662 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 101393982016661871992662 ≤ coefficientCount 11600778735 131071 3840000 19840 -
    262144*localRankBound 63999 3840000 19840 := by rw [nullity_exact]
theorem shape : 11600778735+19840 ≤ 131071*(88507+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    101393982016661871992662 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 11600778735 131071 3840000 19840 63999
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    11600778735 3840000 19840 63999 101393982016661871992662 u0 u1 nullity_lower
#print axioms finrank_gap
end Source00

namespace Source01
theorem coefficient_exact : coefficientCount 5800480000 131071 3200000 9888 = 3203858469329955302754570 := by
  rw [show 5800480000 = 44254*131071+63966 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44254 63966 131071 3200000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5800480000 131071 3200000 9888 -
    262144*localRankBound 32000 3200000 9888 = 12841180931961412995338 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 12841180931961412995338 ≤ coefficientCount 5800480000 131071 3200000 9888 -
    262144*localRankBound 32000 3200000 9888 := by rw [nullity_exact]
theorem shape : 5800480000+9888 ≤ 131071*(44254+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    12841180931961412995338 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5800480000 131071 3200000 9888 32000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    5800480000 3200000 9888 32000 12841180931961412995338 u0 u1 nullity_lower
#print axioms finrank_gap
end Source01

namespace Source02
theorem coefficient_exact : coefficientCount 5800480000 131071 2880000 9888 = 2881683421254439889954570 := by
  rw [show 5800480000 = 44254*131071+63966 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44254 63966 131071 2880000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5800480000 131071 2880000 9888 -
    262144*localRankBound 32000 2880000 9888 = 11204449907338779715338 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 11204449907338779715338 ≤ coefficientCount 5800480000 131071 2880000 9888 -
    262144*localRankBound 32000 2880000 9888 := by rw [nullity_exact]
theorem shape : 5800480000+9888 ≤ 131071*(44254+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    11204449907338779715338 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5800480000 131071 2880000 9888 32000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    5800480000 2880000 9888 32000 11204449907338779715338 u0 u1 nullity_lower
#print axioms finrank_gap
end Source02

namespace Source03
theorem coefficient_exact : coefficientCount 2900240000 131071 1062000 4940 = 132469645009087989525897 := by
  rw [show 2900240000 = 22127*131071+31983 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22127 31983 131071 1062000 4940
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2900240000 131071 1062000 4940 -
    262144*localRankBound 16000 1062000 4940 = 455657858798922476937 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 455657858798922476937 ≤ coefficientCount 2900240000 131071 1062000 4940 -
    262144*localRankBound 16000 1062000 4940 := by rw [nullity_exact]
theorem shape : 2900240000+4940 ≤ 131071*(22127+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    455657858798922476937 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2900240000 131071 1062000 4940 16000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    2900240000 1062000 4940 16000 455657858798922476937 u0 u1 nullity_lower
#print axioms finrank_gap
end Source03

namespace Source04
theorem coefficient_exact : coefficientCount 1450120000 131071 531000 2470 = 8281475958374365584278 := by
  rw [show 1450120000 = 11063*131071+81527 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11063 81527 131071 531000 2470
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 1450120000 131071 531000 2470 -
    262144*localRankBound 8000 531000 2470 = 28168374562350357398 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 28168374562350357398 ≤ coefficientCount 1450120000 131071 531000 2470 -
    262144*localRankBound 8000 531000 2470 := by rw [nullity_exact]
theorem shape : 1450120000+2470 ≤ 131071*(11063+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    28168374562350357398 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 1450120000 131071 531000 2470 8000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    1450120000 531000 2470 8000 28168374562350357398 u0 u1 nullity_lower
#print axioms finrank_gap
end Source04

namespace Source05
theorem coefficient_exact : coefficientCount 181265000 131071 88902 308 = 2718551906586742235 := by
  rw [show 181265000 = 1382*131071+124878 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1382 124878 131071 88902 308
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 181265000 131071 88902 308 -
    262144*localRankBound 1000 88902 308 = 8902002865622491 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 8902002865622491 ≤ coefficientCount 181265000 131071 88902 308 -
    262144*localRankBound 1000 88902 308 := by rw [nullity_exact]
theorem shape : 181265000+308 ≤ 131071*(1382+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    8902002865622491 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 181265000 131071 88902 308 1000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    181265000 88902 308 1000 8902002865622491 u0 u1 nullity_lower
#print axioms finrank_gap
end Source05

namespace Source06
theorem coefficient_exact : coefficientCount 2537710000 131071 3640000 4267 = 303095030018583785570115 := by
  rw [show 2537710000 = 19361*131071+44369 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19361 44369 131071 3640000 4267
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 14000 3640000 4267 = 1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2537710000 131071 3640000 4267 -
    262144*localRankBound 14000 3640000 4267 = 1399387463065701121859 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1399387463065701121859 ≤ coefficientCount 2537710000 131071 3640000 4267 -
    262144*localRankBound 14000 3640000 4267 := by rw [nullity_exact]
theorem shape : 2537710000+4267 ≤ 131071*(19361+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1399387463065701121859 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2537710000 131071 3640000 4267 14000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    2537710000 3640000 4267 14000 1399387463065701121859 u0 u1 nullity_lower
#print axioms finrank_gap
end Source06

namespace TCap
theorem quotient_count_exact : coefficientCount 40965890 131071 2 70 = 408348195 := by decide +kernel
theorem quotient_count_lt : coefficientCount 40965890 131071 2 70 < 797051609 := by
  rw [quotient_count_exact]
  decide +kernel
end TCap

end ProximityPrize.SubmissionLower.MovingFiberKernels6811
