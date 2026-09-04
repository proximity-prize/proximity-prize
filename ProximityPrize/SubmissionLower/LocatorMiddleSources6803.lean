import ProximityPrize.SubmissionLower.LocatorCascadeRankBridge6803

/-!
# Direct kernel receipts for the two middle 68.03 phases

The regenerated 68.03 phase tables consume the smaller elementary nullities,
so neither source needs the rank-saving hypotheses used to promote a 68.02
receipt unchanged.  This file exposes the two missing direct kernel bounds.
-/

namespace ProximityPrize.SubmissionLower.LocatorMiddleSources6803

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180
open LocatorFastKernelArithmetic

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

abbrev KernelC (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 217635600 131071 82100 370 1200
    IRSProfile.domain u0 u1

abbrev KernelSplit500 (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 181363000 131071 42000 310 1000
    IRSProfile.domain u0 u1

theorem weightedC_exact : 1200 * 181363 = 217635600 := by decide

theorem weightedSplit500_exact : 1000 * 181363 = 181363000 := by decide

theorem shapeC : 217635600 + 370 ≤ 131071 * (1660 + 1) := by decide

theorem shapeSplit500 :
    181363000 + 310 ≤ 131071 * (1383 + 1) := by decide

theorem middleC_minimal : ¬ 217635600 + 370 ≤ 131071 * 1660 := by decide

theorem middleSplit500_minimal :
    ¬ 181363000 + 310 ≤ 131071 * 1383 := by decide

theorem nullityC_exact :
    coefficientCount 217635600 131071 82100 370 -
      262144 * localRankBound 1200 82100 370 = 18278038734560710 := by
  rw [LocatorCascadeRankBridge6803.coefficientCountC_exact,
    LocatorCascadeRankBridge6803.localBudgetC_exact]
  norm_num [LocatorCascadeRankBridge6803.sourceRankC,
    LocatorCascadeRankBridge6803.localBudgetC]

theorem nullitySplit500_exact :
    coefficientCount 181363000 131071 42000 310 -
      262144 * localRankBound 1000 42000 310 = 4003459072456058 := by
  rw [LocatorCascadeRankBridge6803.coefficientCountSplit500_exact,
    LocatorCascadeRankBridge6803.localBudgetSplit500_exact]
  norm_num [LocatorCascadeRankBridge6803.sourceRankSplit500,
    LocatorCascadeRankBridge6803.localBudgetSplit500]

theorem finrankC_gap (u0 u1 : I → K) :
    18278038734560710 ≤ Module.finrank K (KernelC u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    217635600 82100 370 1200 18278038734560710 u0 u1 (by
      rw [nullityC_exact])

theorem finrankSplit500_gap (u0 u1 : I → K) :
    4003459072456058 ≤ Module.finrank K (KernelSplit500 u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    181363000 42000 310 1000 4003459072456058 u0 u1 (by
      rw [nullitySplit500_exact])

end

end ProximityPrize.SubmissionLower.LocatorMiddleSources6803
