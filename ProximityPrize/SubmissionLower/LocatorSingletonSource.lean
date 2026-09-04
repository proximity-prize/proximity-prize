import ProximityPrize.SubmissionLower.LocatorSourceArithmetic

/-! Packed from ProximityPrize.SubmissionLower.LocatorSingletonSource. -/
section PackedLocator_LocatorSingletonSource

/-!
# A compact source for the terminal singleton locator cell

This source is small enough to fit inside the selected ambient coefficient
box, but its kernel nullity is just large enough for the `(6412, 50, 11)`
terminal route.  The local-rank receipt is split into short reductions so the
verifier never has to normalize all 153 contact rows in one expression.
-/

namespace ProximityPrize.SubmissionLower.LocatorSingletonSource

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

abbrev Kernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 27750069 131071 7289 47 153
    IRSProfile.domain u0 u1

theorem weighted_exact : 153 * 181373 = 27750069 := by
  decide

theorem shape : 27750069 + 47 ≤ 131071 * (211 + 1) := by
  decide

theorem coefficientCount_exact :
    coefficientCount 27750069 131071 7289 47 = 811593602962228 := by
  change coefficientCount (211 * 131071 + 94088) 131071 7289 47 =
    811593602962228
  rw [coefficientCount_eq_oneResidueCoefficientCount
    211 94088 131071 7289 47 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

private def rankRow (r : ℕ) : ℕ :=
  let M := min r 7289
  let h := min (r + 1) (153 - r)
  rectangularCount (M + 1) (47 + 1) 0 7289 -
    rectangularCount (M + 1 - h) (47 + 1 - h) h 7289

private theorem rank_0 :
    (∑ i ∈ Finset.range 64, rankRow i) = 723390720 := by
  decide

private theorem rank_64 :
    (∑ i ∈ Finset.range 64, rankRow (64 + i)) = 1979021408 := by
  decide

private theorem rank_128 :
    (∑ i ∈ Finset.range 25, rankRow (128 + i)) = 393026400 := by
  decide

private theorem fastLocalRankBound_exact :
    fastLocalRankBound 153 7289 47 = 3095438528 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 153, rankRow r) = _
  rw [Finset.sum_range_add rankRow 128 25,
    Finset.sum_range_add rankRow 64 64, rank_0, rank_64, rank_128]

theorem localRankBound_exact :
    localRankBound 153 7289 47 = 3095438528 := by
  rw [localRankBound_eq_fastLocalRankBound 153 7289 47 (by decide)]
  exact fastLocalRankBound_exact

theorem nullity_exact :
    coefficientCount 27750069 131071 7289 47 -
      262144 * localRankBound 153 7289 47 = 142965478196 := by
  rw [coefficientCount_exact, localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    142965478196 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    27750069 7289 47 153 142965478196 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorSingletonSource
end PackedLocator_LocatorSingletonSource

namespace ProximityPrize.SubmissionLower
set_option Elab.async false in
theorem PackedLocatorBarrier61 : True := by trivial
end ProximityPrize.SubmissionLower

