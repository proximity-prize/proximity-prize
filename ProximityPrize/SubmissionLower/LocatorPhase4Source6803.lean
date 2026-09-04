import ProximityPrize.SubmissionLower.LocatorFastKernelArithmetic

/-!
# Retuned fourth-phase kernel receipt for the 68.03 row

This source replaces the inherited `m = 390`, `L = 19500`, `s = 120`
profile.  The larger total cap is offset by substantially smaller middle and
slope caps; the exact phase-envelope search selects this trade at the binding
joint cells.
-/

namespace ProximityPrize.SubmissionLower.LocatorPhase4Source6803

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

abbrev Kernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 63477050 131071 24000 106 350
    IRSProfile.domain u0 u1

theorem weighted_exact : 350 * 181363 = 63477050 := by
  decide

theorem shape : 63477050 + 106 ≤ 131071 * (484 + 1) := by
  decide

theorem middle_minimal : ¬ 63477050 + 106 ≤ 131071 * 484 := by
  decide

theorem localRankBound_exact :
    localRankBound 350 24000 106 = 118994271786 := by
  rw [localRankBound_eq_fastLocalRankBound 350 24000 106 (by decide)]
  decide

theorem coefficientCount_exact :
    coefficientCount 63477050 131071 24000 106 = 31285771686864234 := by
  change coefficientCount (484 * 131071 + 38686) 131071 24000 106 =
    31285771686864234
  rw [coefficientCount_eq_oneResidueCoefficientCount
    484 38686 131071 24000 106 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

theorem nullity_exact :
    coefficientCount 63477050 131071 24000 106 -
      262144 * localRankBound 350 24000 106 = 92137303795050 := by
  rw [coefficientCount_exact, localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    92137303795050 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    63477050 24000 106 350 92137303795050 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorPhase4Source6803
