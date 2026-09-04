import ProximityPrize.SubmissionLower.LocatorR1200Rank

/-!
# Retuned R1200 kernel receipt for the 68.03 row

The lower agreement threshold changes the weighted cutoff from `870590400`
to `870542400`.  Its least admissible middle cap is `6641`, one smaller than
the promoted 68.02 source.  Keeping this integer exact matters: it advances
the binding first-phase route by one total-degree cell.
-/

namespace ProximityPrize.SubmissionLower.LocatorR1200Source6803

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
  ConstraintKernel (K := K) 870542400 131071 328400 1480 4800
    IRSProfile.domain u0 u1

theorem weighted_exact : 4800 * 181363 = 870542400 := by
  decide

/-- `6641` is sufficient; the inherited `6642` cap is not minimal here. -/
theorem shape : 870542400 + 1480 ≤ 131071 * (6641 + 1) := by
  decide

theorem coefficientCount_exact :
    coefficientCount 870542400 131071 328400 1480 =
      1107150758552279760150 := by
  change coefficientCount (6641 * 131071 + 99889) 131071 328400 1480 =
    1107150758552279760150
  rw [coefficientCount_eq_oneResidueCoefficientCount
    6641 99889 131071 328400 1480 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

theorem nullity_exact :
    coefficientCount 870542400 131071 328400 1480 -
      262144 * localRankBound 4800 328400 1480 =
        5090867013182078230 := by
  rw [coefficientCount_exact, LocatorR1200Rank.localRankBound_exact]

theorem finrank_gap (u0 u1 : I → K) :
    5090867013182078230 ≤ Module.finrank K (Kernel u0 u1) := by
  exact challengeConstraintKernel_finrank_lower_bound_of_numeric
    870542400 328400 1480 4800 5090867013182078230 u0 u1 (by
      rw [nullity_exact])

end

end ProximityPrize.SubmissionLower.LocatorR1200Source6803
