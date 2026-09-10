import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.Kernels80801
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace A
theorem coefficient_exact : coefficientCount 18315643 131071 350390 30 = 11220335138994680 := by
  rw [show 18315643 = 139*131071+96774 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 139 96774 131071 350390 30 (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 101 350390 30 = 42802181771 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 18315643 131071 350390 30 - 262144 * localRankBound 101 350390 30 = 817656 := by
  norm_num only [coefficient_exact, rank_exact]
theorem shape : 18315643+30 ≤ 131071*(139+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    817656 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 18315643 131071 350390 30 101
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    18315643 350390 30 101 817656 u0 u1 (by rw [nullity_exact])
end A

namespace B
theorem coefficient_exact : coefficientCount 20129073 131071 21378 33 = 903604845898865 := by
  rw [show 20129073 = 153*131071+75210 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 153 75210 131071 21378 33 (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 111 21378 33 = 3446978871 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 20129073 131071 21378 33 - 262144 * localRankBound 111 21378 33 = 16739441 := by
  norm_num only [coefficient_exact, rank_exact]
theorem shape : 20129073+33 ≤ 131071*(153+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    16739441 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 20129073 131071 21378 33 111
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    20129073 21378 33 111 16739441 u0 u1 (by rw [nullity_exact])
end B

namespace T
theorem coefficient_exact : coefficientCount 36268600 131071 7204 62 = 1785229835798871 := by
  rw [show 36268600 = 276*131071+93004 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 276 93004 131071 7204 62 (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 200 7204 62 = 6810105834 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 36268600 131071 7204 62 - 262144 * localRankBound 200 7204 62 = 1452050775 := by
  norm_num only [coefficient_exact, rank_exact]
theorem shape : 36268600+62 ≤ 131071*(276+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1452050775 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 36268600 131071 7204 62 200
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    36268600 7204 62 200 1452050775 u0 u1 (by rw [nullity_exact])
theorem quotient_count_lt : coefficientCount 36268600 131071 4 62 < 1452050775 := by decide
end T

namespace Source00
theorem coefficient_lower : 30745256612158425592082712 ≤ coefficientCount 11605952000 131071 3840000 19840 := by
  rw [show 11605952000 = 88547*131071+8163 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 88547 8163 131071 3840000 19840 (by decide) (by decide) (by decide) (by decide)
  exact (show 30745256612158425592082712 = oneResidueCoefficientCount 88547 8163 131071 3840000 19840 by decide).le.trans h
theorem rank_exact : localRankBound 64000 3840000 19840 = 116784455894414962240 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 130912206172909730640152 ≤ coefficientCount 11605952000 131071 3840000 19840 - 262144 * localRankBound 64000 3840000 19840 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*116784455894414962240)
  rw [rank_exact]
  exact (show 130912206172909730640152 = 30745256612158425592082712-262144*116784455894414962240 by decide).le.trans h
theorem shape : 11605952000+19840 ≤ 131071*(88547+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    130912206172909730640152 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 11605952000 131071 3840000 19840 64000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 11605952000 3840000 19840 64000 130912206172909730640152 u0 u1 nullity_lower
end Source00

namespace Source01
theorem coefficient_lower : 3206940441726229701831800 ≤ coefficientCount 5802976000 131071 3200000 9888 := by
  rw [show 5802976000 = 44273*131071+69617 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 44273 69617 131071 3200000 9888 (by decide) (by decide) (by decide) (by decide)
  exact (show 3206940441726229701831800 = oneResidueCoefficientCount 44273 69617 131071 3200000 9888 by decide).le.trans h
theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 15923153328235812072568 ≤ coefficientCount 5802976000 131071 3200000 9888 - 262144 * localRankBound 32000 3200000 9888 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*12172764924613929328)
  rw [rank_exact]
  exact (show 15923153328235812072568 = 3206940441726229701831800-262144*12172764924613929328 by decide).le.trans h
theorem shape : 5802976000+9888 ≤ 131071*(44273+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    15923153328235812072568 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 5802976000 131071 3200000 9888 32000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 5802976000 3200000 9888 32000 15923153328235812072568 u0 u1 nullity_lower
end Source01

namespace Source02
theorem coefficient_lower : 2884454818654081905031800 ≤ coefficientCount 5802976000 131071 2880000 9888 := by
  rw [show 5802976000 = 44273*131071+69617 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 44273 69617 131071 2880000 9888 (by decide) (by decide) (by decide) (by decide)
  exact (show 2884454818654081905031800 = oneResidueCoefficientCount 44273 69617 131071 2880000 9888 by decide).le.trans h
theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 13975847306980794792568 ≤ coefficientCount 5802976000 131071 2880000 9888 - 262144 * localRankBound 32000 2880000 9888 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*10950008283031849328)
  rw [rank_exact]
  exact (show 13975847306980794792568 = 2884454818654081905031800-262144*10950008283031849328 by decide).le.trans h
theorem shape : 5802976000+9888 ≤ 131071*(44273+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    13975847306980794792568 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 5802976000 131071 2880000 9888 32000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 5802976000 2880000 9888 32000 13975847306980794792568 u0 u1 nullity_lower
end Source02

namespace Source03
theorem coefficient_lower : 132596923602714481688535 ≤ coefficientCount 2901488000 131071 1062000 4940 := by
  rw [show 2901488000 = 22136*131071+100344 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 22136 100344 131071 1062000 4940 (by decide) (by decide) (by decide) (by decide)
  exact (show 132596923602714481688535 = oneResidueCoefficientCount 22136 100344 131071 1062000 4940 by decide).le.trans h
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 582936452425414639575 ≤ coefficientCount 2901488000 131071 1062000 4940 - 262144 * localRankBound 16000 1062000 4940 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*503593395806461590)
  rw [rank_exact]
  exact (show 582936452425414639575 = 132596923602714481688535-262144*503593395806461590 by decide).le.trans h
theorem shape : 2901488000+4940 ≤ 131071*(22136+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    582936452425414639575 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 2901488000 131071 1062000 4940 16000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 2901488000 1062000 4940 16000 582936452425414639575 u0 u1 nullity_lower
end Source03

namespace Source04
theorem coefficient_lower : 8289432693401489457513 ≤ coefficientCount 1450744000 131071 531000 2470 := by
  rw [show 1450744000 = 11068*131071+50172 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 11068 50172 131071 531000 2470 (by decide) (by decide) (by decide) (by decide)
  exact (show 8289432693401489457513 = oneResidueCoefficientCount 11068 50172 131071 531000 2470 by decide).le.trans h
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 36125109589474230633 ≤ coefficientCount 1450744000 131071 531000 2470 - 262144 * localRankBound 8000 531000 2470 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*31483869872329770)
  rw [rank_exact]
  exact (show 36125109589474230633 = 8289432693401489457513-262144*31483869872329770 by decide).le.trans h
theorem shape : 1450744000+2470 ≤ 131071*(11068+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    36125109589474230633 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 1450744000 131071 531000 2470 8000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 1450744000 531000 2470 8000 36125109589474230633 u0 u1 nullity_lower
end Source04

namespace Source05
theorem coefficient_lower : 2721164626950118715 ≤ coefficientCount 181343000 131071 88902 308 := by
  rw [show 181343000 = 1383*131071+71807 by decide]
  have h := OneResidueLower.oneResidue_le_coefficientCount 1383 71807 131071 88902 308 (by decide) (by decide) (by decide) (by decide)
  exact (show 2721164626950118715 = oneResidueCoefficientCount 1383 71807 131071 88902 308 by decide).le.trans h
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_lower : 11514723228998971 ≤ coefficientCount 181343000 131071 88902 308 - 262144 * localRankBound 1000 88902 308 := by
  have h := Nat.sub_le_sub_right coefficient_lower (262144*10336494078526)
  rw [rank_exact]
  exact (show 11514723228998971 = 2721164626950118715-262144*10336494078526 by decide).le.trans h
theorem shape : 181343000+308 ≤ 131071*(1383+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    11514723228998971 ≤ Module.finrank IRSProfile.Field (ConstraintKernel (K := IRSProfile.Field) 181343000 131071 88902 308 1000 IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric 181343000 88902 308 1000 11514723228998971 u0 u1 nullity_lower
end Source05

end ProximityPrize.SubmissionLower.Kernels80801
