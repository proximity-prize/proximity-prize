import ProximityPrize.SubmissionLower.BoundaryTailRouting6807
/-
UNCOMPILED. Exact kernel and shape instances for agreement181324.
No 181333 instance is reused with its constants silently changed. These are
source-existence inputs only, NOT phase, strict/zero, or alignment certificates.
-/
import ProximityPrize.SubmissionLower.LowerGeometry

namespace ProximityPrize.SubmissionLower.Kernels80820
open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180 LocatorFastKernelArithmetic LocatorLowQuotient
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace A
theorem coefficient_exact : coefficientCount 19220344 131071 497436 31 = 18164603255152040 := by
  rw [show 19220344 = 146*131071+83978 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 146 83978 131071 497436 31
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 106 497436 31 = 69292462368 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 19220344 131071 497436 31 -
    262144 * localRankBound 106 497436 31 = 155048 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 155048 := by decide
theorem shape : 19220344+31 ≤ 131071*(146+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    155048 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 19220344 131071 497436 31 106
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    19220344 497436 31 106 155048 u0 u1 (by rw [nullity_exact])
end A

namespace B
theorem coefficient_exact : coefficientCount 20126964 131071 33395 34 = 1444115836449825 := by
  rw [show 20126964 = 153*131071+73101 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 153 73101 131071 33395 34
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 111 33395 34 = 5508864690 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 20126964 131071 33395 34 -
    262144 * localRankBound 111 33395 34 = 11154465 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 11154465 := by decide
theorem shape : 20126964+34 ≤ 131071*(153+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    11154465 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 20126964 131071 33395 34 111
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    20126964 33395 34 111 11154465 u0 u1 (by rw [nullity_exact])
end B

namespace T
theorem coefficient_exact : coefficientCount 38078040 131071 7789 65 = 2230220351496995 := by
  rw [show 38078040 = 290*131071+67450 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 290 67450 131071 7789 65
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 210 7789 65 = 8507610210 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 38078040 131071 7789 65 -
    262144 * localRankBound 210 7789 65 = 1380606755 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 1380606755 := by decide
theorem shape : 38078040+65 ≤ 131071*(290+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1380606755 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 38078040 131071 7789 65 210
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    38078040 7789 65 210 1380606755 u0 u1 (by rw [nullity_exact])
theorem quotient_count_exact : coefficientCount 38078040 131071 4 65 = 1323556465 := by decide
theorem quotient_count_lt : coefficientCount 38078040 131071 4 65 < 1380606755 := by
  rw [quotient_count_exact]
  decide
end T

namespace Source00
theorem coefficient_exact : coefficientCount 11604736000 131071 3840000 19840 = 30738065466684476564272592 := by
  rw [show 11604736000 = 88537*131071+102873 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 88537 102873 131071 3840000 19840
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 64000 3840000 19840 = 116784455894414962240 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 11604736000 131071 3840000 19840 -
    262144 * localRankBound 64000 3840000 19840 = 123721060698960702830032 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 123721060698960702830032 := by decide
theorem shape : 11604736000+19840 ≤ 131071*(88537+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    123721060698960702830032 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 11604736000 131071 3840000 19840 64000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    11604736000 3840000 19840 64000 123721060698960702830032 u0 u1 (by rw [nullity_exact])
end Source00

namespace Source01
theorem coefficient_exact : coefficientCount 5802368000 131071 3200000 9888 = 3206189567835854632356060 := by
  rw [show 5802368000 = 44268*131071+116972 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44268 116972 131071 3200000 9888
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 32000 3200000 9888 = 12172764924613929328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 5802368000 131071 3200000 9888 -
    262144 * localRankBound 32000 3200000 9888 = 15172279437860742596828 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 15172279437860742596828 := by decide
theorem shape : 5802368000+9888 ≤ 131071*(44268+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    15172279437860742596828 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5802368000 131071 3200000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5802368000 3200000 9888 32000 15172279437860742596828 u0 u1 (by rw [nullity_exact])
end Source01

namespace Source02
theorem coefficient_exact : coefficientCount 5802368000 131071 2880000 9888 = 2883779611542164382756060 := by
  rw [show 5802368000 = 44268*131071+116972 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 44268 116972 131071 2880000 9888
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 32000 2880000 9888 = 10950008283031849328 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 5802368000 131071 2880000 9888 -
    262144 * localRankBound 32000 2880000 9888 = 13300640195063272516828 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 13300640195063272516828 := by decide
theorem shape : 5802368000+9888 ≤ 131071*(44268+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    13300640195063272516828 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 5802368000 131071 2880000 9888 32000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    5802368000 2880000 9888 32000 13300640195063272516828 u0 u1 (by rw [nullity_exact])
end Source02

namespace Source03
theorem coefficient_exact : coefficientCount 2901184000 131071 1062000 4940 = 132565914242797564000215 := by
  rw [show 2901184000 = 22134*131071+58486 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 22134 58486 131071 1062000 4940
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 16000 1062000 4940 = 503593395806461590 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 2901184000 131071 1062000 4940 -
    262144 * localRankBound 16000 1062000 4940 = 551927092508496951255 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 551927092508496951255 := by decide
theorem shape : 2901184000+4940 ≤ 131071*(22134+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    551927092508496951255 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2901184000 131071 1062000 4940 16000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    2901184000 1062000 4940 16000 551927092508496951255 u0 u1 (by rw [nullity_exact])
end Source03

namespace Source04
theorem coefficient_exact : coefficientCount 1450592000 131071 531000 2470 = 8287494157809777486212 := by
  rw [show 1450592000 = 11067*131071+29243 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 11067 29243 131071 531000 2470
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 8000 531000 2470 = 31483869872329770 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 1450592000 131071 531000 2470 -
    262144 * localRankBound 8000 531000 2470 = 34186573997762259332 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 34186573997762259332 := by decide
theorem shape : 1450592000+2470 ≤ 131071*(11067+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    34186573997762259332 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 1450592000 131071 531000 2470 8000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    1450592000 531000 2470 8000 34186573997762259332 u0 u1 (by rw [nullity_exact])
end Source04

namespace Source05
theorem coefficient_exact : coefficientCount 181324000 131071 88902 308 = 2720528155284438715 := by
  rw [show 181324000 = 1383*131071+52807 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 1383 52807 131071 88902 308
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 1000 88902 308 = 10336494078526 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 181324000 131071 88902 308 -
    262144 * localRankBound 1000 88902 308 = 10878251563318971 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 10878251563318971 := by decide
theorem shape : 181324000+308 ≤ 131071*(1383+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    10878251563318971 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 181324000 131071 88902 308 1000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    181324000 88902 308 1000 10878251563318971 u0 u1 (by rw [nullity_exact])
end Source05

namespace Source06
theorem coefficient_exact : coefficientCount 2538536000 131071 3640000 4267 = 303315500325014380232073 := by
  rw [show 2538536000 = 19367*131071+83943 by decide]
  rw [coefficientCount_eq_oneResidueCoefficientCount 19367 83943 131071 3640000 4267
    (by decide) (by decide) (by decide) (by decide)]
  decide
theorem rank_exact : localRankBound 14000 3640000 4267 = 1150877542707512224 := by
  rw [ClosedRank.localRankBound_eq_closed _ _ _ (by decide) (by decide)]
  decide
theorem nullity_exact : coefficientCount 2538536000 131071 3640000 4267 -
    262144 * localRankBound 14000 3640000 4267 = 1619857769496295783817 := by
  norm_num only [coefficient_exact,rank_exact]
theorem positive_kernel : 0 < 1619857769496295783817 := by decide
theorem shape : 2538536000+4267 ≤ 131071*(19367+1) := by decide
theorem finrank_gap (u0 u1 : IRSProfile.Index → IRSProfile.Field) :
    1619857769496295783817 ≤ Module.finrank IRSProfile.Field
      (ConstraintKernel (K := IRSProfile.Field) 2538536000 131071 3640000 4267 14000
        IRSProfile.domain u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    2538536000 3640000 4267 14000 1619857769496295783817 u0 u1 (by rw [nullity_exact])
end Source06

end ProximityPrize.SubmissionLower.Kernels80820
