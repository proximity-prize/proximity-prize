import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.Kernels80811
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace A
theorem coefficient_exact : coefficientCount 18677299 131071 230326 31 = 7891160963269240 := by
  rw [show 18677299 = 142*131071+65217 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 142 65217 131071 230326 31 (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 103 230326 31 = 30102390144 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 18677299 131071 230326 31 - 262144 * localRankBound 103 230326 31 = 1360504 := by
  norm_num only [coefficient_exact, rank_exact]
theorem shape : 18677299+31 ≤ 131071*(142+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1360504 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 18677299 131071 230326 31 103
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    18677299 230326 31 103 1360504 u0 u1 (by rw [nullity_exact])
end A

namespace B
theorem coefficient_exact : coefficientCount 20127963 131071 27312 33 = 1154986854732095 := by
  rw [show 20127963 = 153*131071+74100 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 153 74100 131071 27312 33 (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 111 27312 33 = 4405925139 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 20127963 131071 27312 33 - 262144 * localRankBound 111 27312 33 = 15094079 := by
  norm_num only [coefficient_exact, rank_exact]
theorem shape : 20127963+33 ≤ 131071*(153+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    15094079 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 20127963 131071 27312 33 111
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    20127963 27312 33 111 15094079 u0 u1 (by rw [nullity_exact])
end B

namespace T
theorem coefficient_exact : coefficientCount 36266600 131071 7506 62 = 1860998983917549 := by
  rw [show 36266600 = 276*131071+91004 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 276 91004 131071 7506 62 (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 200 7506 62 = 7099142484 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 36266600 131071 7506 62 - 262144 * localRankBound 200 7506 62 = 1376591853 := by
  norm_num only [coefficient_exact, rank_exact]
theorem shape : 36266600+62 ≤ 131071*(276+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1376591853 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 36266600 131071 7506 62 200
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    36266600 7506 62 200 1376591853 u0 u1 (by rw [nullity_exact])
theorem quotient_count_lt : coefficientCount 36266600 131071 4 62 < 1376591853 := by decide
end T

namespace Source00
theorem coefficient_lower : 30741471694423385850377602 ≤ coefficientCount 11605312000 131071 3840000 19840 := by
  rw [show 11605312000 = 88542*131071+23518 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 88542 23518 131071 3840000 19840 (by decide) (by decide) (by decide) (by decide)
  exact (show 30741471694423385850377602 = oneResidueCoefficientCount 88542 23518 131071 3840000 19840 by decide).le.trans h
theorem rank_exact : localRankBound 64000 3840000 19840 = 116784455894414962240 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 127127288437869988935042 ≤ coefficientCount 11605312000 131071 3840000 19840 - 262144 * localRankBound 64000 3840000 19840 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*116784455894414962240)
  rw [rank_exact]
  exact (show 127127288437869988935042 = 30741471694423385850377602-262144*116784455894414962240 by decide).le.trans h
theorem shape : 11605312000+19840 ≤ 131071*(88542+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    127127288437869988935042 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 11605312000 131071 3840000 19840 64000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 11605312000 3840000 19840 64000 127127288437869988935042 u0 u1 nullity_lower
end Source00

namespace Source01
theorem coefficient_lower : 3206545233890405553657896 ≤ coefficientCount 5802656000 131071 3200000 9888 := by
  rw [show 5802656000 = 44271*131071+11759 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 44271 11759 131071 3200000 9888 (by decide) (by decide) (by decide) (by decide)
  exact (show 3206545233890405553657896 = oneResidueCoefficientCount 44271 11759 131071 3200000 9888 by decide).le.trans h
theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 15527945492411663898664 ≤ coefficientCount 5802656000 131071 3200000 9888 - 262144 * localRankBound 32000 3200000 9888 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*12172764924613929328)
  rw [rank_exact]
  exact (show 15527945492411663898664 = 3206545233890405553657896-262144*12172764924613929328 by decide).le.trans h
theorem shape : 5802656000+9888 ≤ 131071*(44271+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    15527945492411663898664 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 5802656000 131071 3200000 9888 32000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 5802656000 3200000 9888 32000 15527945492411663898664 u0 u1 nullity_lower
end Source01

namespace Source02
theorem coefficient_lower : 2884099436559143701497896 ≤ coefficientCount 5802656000 131071 2880000 9888 := by
  rw [show 5802656000 = 44271*131071+11759 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 44271 11759 131071 2880000 9888 (by decide) (by decide) (by decide) (by decide)
  exact (show 2884099436559143701497896 = oneResidueCoefficientCount 44271 11759 131071 2880000 9888 by decide).le.trans h
theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 13620465212042591258664 ≤ coefficientCount 5802656000 131071 2880000 9888 - 262144 * localRankBound 32000 2880000 9888 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*10950008283031849328)
  rw [rank_exact]
  exact (show 13620465212042591258664 = 2884099436559143701497896-262144*10950008283031849328 by decide).le.trans h
theorem shape : 5802656000+9888 ≤ 131071*(44271+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    13620465212042591258664 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 5802656000 131071 2880000 9888 32000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 5802656000 2880000 9888 32000 13620465212042591258664 u0 u1 nullity_lower
end Source02

namespace Source03
theorem coefficient_lower : 132580602447137515505025 ≤ coefficientCount 2901328000 131071 1062000 4940 := by
  rw [show 2901328000 = 22135*131071+71415 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 22135 71415 131071 1062000 4940 (by decide) (by decide) (by decide) (by decide)
  exact (show 132580602447137515505025 = oneResidueCoefficientCount 22135 71415 131071 1062000 4940 by decide).le.trans h
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 566615296848448456065 ≤ coefficientCount 2901328000 131071 1062000 4940 - 262144 * localRankBound 16000 1062000 4940 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*503593395806461590)
  rw [rank_exact]
  exact (show 566615296848448456065 = 132580602447137515505025-262144*503593395806461590 by decide).le.trans h
theorem shape : 2901328000+4940 ≤ 131071*(22135+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    566615296848448456065 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 2901328000 131071 1062000 4940 16000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 2901328000 1062000 4940 16000 566615296848448456065 u0 u1 nullity_lower
end Source03

namespace Source04
theorem coefficient_lower : 8288412380226465006212 ≤ coefficientCount 1450664000 131071 531000 2470 := by
  rw [show 1450664000 = 11067*131071+101243 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 11067 101243 131071 531000 2470 (by decide) (by decide) (by decide) (by decide)
  exact (show 8288412380226465006212 = oneResidueCoefficientCount 11067 101243 131071 531000 2470 by decide).le.trans h
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 35104796414449779332 ≤ coefficientCount 1450664000 131071 531000 2470 - 262144 * localRankBound 8000 531000 2470 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*31483869872329770)
  rw [rank_exact]
  exact (show 35104796414449779332 = 8288412380226465006212-262144*31483869872329770 by decide).le.trans h
theorem shape : 1450664000+2470 ≤ 131071*(11067+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    35104796414449779332 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 1450664000 131071 531000 2470 8000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 1450664000 531000 2470 8000 35104796414449779332 u0 u1 nullity_lower
end Source04

namespace Source05
theorem coefficient_lower : 2720829641862918715 ≤ coefficientCount 181333000 131071 88902 308 := by
  rw [show 181333000 = 1383*131071+61807 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 1383 61807 131071 88902 308 (by decide) (by decide) (by decide) (by decide)
  exact (show 2720829641862918715 = oneResidueCoefficientCount 1383 61807 131071 88902 308 by decide).le.trans h
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 11179738141798971 ≤ coefficientCount 181333000 131071 88902 308 - 262144 * localRankBound 1000 88902 308 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*10336494078526)
  rw [rank_exact]
  exact (show 11179738141798971 = 2720829641862918715-262144*10336494078526 by decide).le.trans h
theorem shape : 181333000+308 ≤ 131071*(1383+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    11179738141798971 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 181333000 131071 88902 308 1000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 181333000 88902 308 1000 11179738141798971 u0 u1 nullity_lower
end Source05

end ProximityPrize.SubmissionLower.Kernels80811
