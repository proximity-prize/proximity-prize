import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.MovingFiberKernels6811
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace A
theorem coefficient_exact : coefficientCount 20847660 131071 274277 35 = 13125118927898685 := by
  rw [show 20847660 = 159*131071+7371 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 159 7371 131071 274277 35
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 115 274277 35 = 50068355280 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 20847660 131071 274277 35 -
    262144*localRankBound 115 274277 35 = 1378365 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1378365 ≤ coefficientCount 20847660 131071 274277 35 -
    262144*localRankBound 115 274277 35 := by rw [nullity_exact]
theorem positive_kernel : 0 < 1378365 := by decide +kernel
theorem shape : 20847660+35 ≤ 131071*(159+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1378365 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 20847660 131071 274277 35 115
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    20847660 274277 35 115 1378365 u0 u1 nullity_lower
#print axioms finrank_gap
end A

namespace B
theorem coefficient_exact : coefficientCount 24292056 131071 18992 40 = 1405157241467798 := by
  rw [show 24292056 = 185*131071+43921 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 185 43921 131071 18992 40
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 134 18992 40 = 5360249390 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 24292056 131071 18992 40 -
    262144*localRankBound 134 18992 40 = 25375638 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 25375638 ≤ coefficientCount 24292056 131071 18992 40 -
    262144*localRankBound 134 18992 40 := by rw [nullity_exact]
theorem positive_kernel : 0 < 25375638 := by decide +kernel
theorem shape : 24292056+40 ≤ 131071*(185+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    25375638 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 24292056 131071 18992 40 134
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    24292056 18992 40 134 25375638 u0 u1 nullity_lower
#print axioms finrank_gap
end B

namespace TCap
theorem coefficient_exact : coefficientCount 40970184 131071 9281 70 = 3312623460539726 := by
  rw [show 40970184 = 312*131071+76032 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 312 76032 131071 9281 70
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 226 9281 70 = 12636646882 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 40970184 131071 9281 70 -
    262144*localRankBound 226 9281 70 = 2300304718 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 2300304718 ≤ coefficientCount 40970184 131071 9281 70 -
    262144*localRankBound 226 9281 70 := by rw [nullity_exact]
theorem positive_kernel : 0 < 2300304718 := by decide +kernel
theorem shape : 40970184+70 ≤ 131071*(312+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    2300304718 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 40970184 131071 9281 70 226
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    40970184 9281 70 226 2300304718 u0 u1 nullity_lower
#print axioms finrank_gap
end TCap

namespace Source00
theorem coefficient_exact : coefficientCount 11602176000 131071 3840000 19840 = 30722928958268011253484378 := by
  rw [show 11602176000 = 88518*131071+33222 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 88518 33222 131071 3840000 19840
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 64000 3840000 19840 = 116784455894414962240 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 11602176000 131071 3840000 19840 -
    262144*localRankBound 64000 3840000 19840 = 108584552282495392041818 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 108584552282495392041818 ≤ coefficientCount 11602176000 131071 3840000 19840 -
    262144*localRankBound 64000 3840000 19840 := by rw [nullity_exact]
theorem positive_kernel : 0 < 108584552282495392041818 := by decide +kernel
theorem shape : 11602176000+19840 ≤ 131071*(88518+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    108584552282495392041818 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 11602176000 131071 3840000 19840 64000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    11602176000 3840000 19840 64000 108584552282495392041818 u0 u1 nullity_lower
#print axioms finrank_gap
end Source00

namespace Source01
theorem coefficient_exact : coefficientCount 5801088000 131071 3200000 9888 = 3204609069314829266599520 := by
  rw [show 5801088000 = 44259*131071+16611 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44259 16611 131071 3200000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5801088000 131071 3200000 9888 -
    262144*localRankBound 32000 3200000 9888 = 13591780916835376840288 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 13591780916835376840288 ≤ coefficientCount 5801088000 131071 3200000 9888 -
    262144*localRankBound 32000 3200000 9888 := by rw [nullity_exact]
theorem positive_kernel : 0 < 13591780916835376840288 := by decide +kernel
theorem shape : 5801088000+9888 ≤ 131071*(44259+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    13591780916835376840288 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5801088000 131071 3200000 9888 32000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    5801088000 3200000 9888 32000 13591780916835376840288 u0 u1 nullity_lower
#print axioms finrank_gap
end Source01

namespace Source02
theorem coefficient_exact : coefficientCount 5801088000 131071 2880000 9888 = 2882358382235592200999520 := by
  rw [show 5801088000 = 44259*131071+16611 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44259 16611 131071 2880000 9888
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 5801088000 131071 2880000 9888 -
    262144*localRankBound 32000 2880000 9888 = 11879410888491090760288 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 11879410888491090760288 ≤ coefficientCount 5801088000 131071 2880000 9888 -
    262144*localRankBound 32000 2880000 9888 := by rw [nullity_exact]
theorem positive_kernel : 0 < 11879410888491090760288 := by decide +kernel
theorem shape : 5801088000+9888 ≤ 131071*(44259+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    11879410888491090760288 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5801088000 131071 2880000 9888 32000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    5801088000 2880000 9888 32000 11879410888491090760288 u0 u1 nullity_lower
#print axioms finrank_gap
end Source02

namespace Source03
theorem coefficient_exact : coefficientCount 2900544000 131071 1062000 4940 = 132500643163012151609895 := by
  rw [show 2900544000 = 22129*131071+73841 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22129 73841 131071 1062000 4940
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2900544000 131071 1062000 4940 -
    262144*localRankBound 16000 1062000 4940 = 486656012723084560935 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 486656012723084560935 ≤ coefficientCount 2900544000 131071 1062000 4940 -
    262144*localRankBound 16000 1062000 4940 := by rw [nullity_exact]
theorem positive_kernel : 0 < 486656012723084560935 := by decide +kernel
theorem shape : 2900544000+4940 ≤ 131071*(22129+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    486656012723084560935 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2900544000 131071 1062000 4940 16000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    2900544000 1062000 4940 16000 486656012723084560935 u0 u1 nullity_lower
#print axioms finrank_gap
end Source03

namespace Source04
theorem coefficient_exact : coefficientCount 1450272000 131071 531000 2470 = 8283413780004746471235 := by
  rw [show 1450272000 = 11064*131071+102456 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11064 102456 131071 531000 2470
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 1450272000 131071 531000 2470 -
    262144*localRankBound 8000 531000 2470 = 30106196192731244355 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 30106196192731244355 ≤ coefficientCount 1450272000 131071 531000 2470 -
    262144*localRankBound 8000 531000 2470 := by rw [nullity_exact]
theorem positive_kernel : 0 < 30106196192731244355 := by decide +kernel
theorem shape : 1450272000+2470 ≤ 131071*(11064+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    30106196192731244355 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 1450272000 131071 531000 2470 8000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    1450272000 531000 2470 8000 30106196192731244355 u0 u1 nullity_lower
#print axioms finrank_gap
end Source04

namespace Source05
theorem coefficient_exact : coefficientCount 181284000 131071 88902 308 = 2719188214935638715 := by
  rw [show 181284000 = 1383*131071+12807 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1383 12807 131071 88902 308
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 181284000 131071 88902 308 -
    262144*localRankBound 1000 88902 308 = 9538311214518971 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 9538311214518971 ≤ coefficientCount 181284000 131071 88902 308 -
    262144*localRankBound 1000 88902 308 := by rw [nullity_exact]
theorem positive_kernel : 0 < 9538311214518971 := by decide +kernel
theorem shape : 181284000+308 ≤ 131071*(1383+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    9538311214518971 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 181284000 131071 88902 308 1000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    181284000 88902 308 1000 9538311214518971 u0 u1 nullity_lower
#print axioms finrank_gap
end Source05

namespace Source06
theorem coefficient_exact : coefficientCount 2537976000 131071 3640000 4267 = 303166020158767900703085 := by
  rw [show 2537976000 = 19363*131071+48227 by decide +kernel]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19363 48227 131071 3640000 4267
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem rank_exact : localRankBound 14000 3640000 4267 = 1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel
theorem nullity_exact : coefficientCount 2537976000 131071 3640000 4267 -
    262144*localRankBound 14000 3640000 4267 = 1470377603249816254829 := by
  norm_num only [coefficient_exact,rank_exact]
theorem nullity_lower : 1470377603249816254829 ≤ coefficientCount 2537976000 131071 3640000 4267 -
    262144*localRankBound 14000 3640000 4267 := by rw [nullity_exact]
theorem positive_kernel : 0 < 1470377603249816254829 := by decide +kernel
theorem shape : 2537976000+4267 ≤ 131071*(19363+1) := by decide +kernel
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1470377603249816254829 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2537976000 131071 3640000 4267 14000
        IRSProfile.domain u0 u1) :=
  challengeConstraintKernel_finrank_lower_bound_of_numeric
    2537976000 3640000 4267 14000 1470377603249816254829 u0 u1 nullity_lower
#print axioms finrank_gap
end Source06

namespace TCap
theorem quotient_count_exact : coefficientCount 40970184 131071 5 70 = 2275980434 := by decide +kernel
theorem quotient_count_lt : coefficientCount 40970184 131071 5 70 < 2300304718 := by
  rw [quotient_count_exact]
  decide +kernel
end TCap

end ProximityPrize.SubmissionLower.MovingFiberKernels6811
