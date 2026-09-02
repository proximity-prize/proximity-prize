import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.LocatorGenericPowerAvoidance
import ProximityPrize.SubmissionLower.N5

namespace ProximityPrize.SubmissionLower.LocatorHelperArithmetic6783

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN180

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index

theorem sourceS1_rank :
    localRankBound 355 350000 105 = 1789092129575 := by
  rw [← LocatorKernelEval.localRankBound_eq 355 350000 105 (by decide)]
  decide

theorem sourceS1_nullity :
    coefficientCount 64453445 131071 350000 105 -
      262144 * localRankBound 355 350000 105 = 3180563774424370 := by
  rw [sourceS1_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    64453445 131071 350000 105 492 (by decide) (by decide)]
  decide

theorem sourceS2_rank :
    localRankBound 500 1000000 150 = 14383345717650 := by
  rw [← LocatorKernelEval.localRankBound_eq 500 1000000 150 (by decide)]
  decide

theorem sourceS2_nullity :
    coefficientCount 90779500 131071 1000000 150 -
      262144 * localRankBound 500 1000000 150 = 27918612901329797 := by
  rw [sourceS2_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    90779500 131071 1000000 150 693 (by decide) (by decide)]
  decide

theorem sourceS1_finrank_lower_bound (u0 u1 : I → K) :
    3180563774424370 ≤ Module.finrank K
      (ConstraintKernel (K := K) 64453445 131071 350000 105 355
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    64453445 131071 350000 105 355 IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact sourceS1_nullity ▸ hlo'

theorem sourceS2_finrank_lower_bound (u0 u1 : I → K) :
    27918612901329797 ≤ Module.finrank K
      (ConstraintKernel (K := K) 90779500 131071 1000000 150 500
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    90779500 131071 1000000 150 500 IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact sourceS2_nullity ▸ hlo'

theorem factorial_cast_ne_zero_of_le_eighteen
    {E : Type*} [Field E] [CharP E 2130706433]
    (j : ℕ) (hj : j ≤ 18) : (j.factorial : E) ≠ 0 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      apply mul_ne_zero
      · intro hz
        have hdvd : 2130706433 ∣ j + 1 :=
          (CharP.cast_eq_zero_iff E 2130706433 (j + 1)).mp hz
        exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
      · exact ih (by omega)

theorem sourceS1_stage_capacity (j : ℕ) (hj : j ≤ 13) :
    64453445 - j * 50489 = (355 - j) * 181559 + j * 131070 := by
  omega

theorem sourceS2_stage_capacity (j : ℕ) (hj : j ≤ 18) :
    90779500 - j * 50489 = (500 - j) * 181559 + j * 131070 := by
  omega

theorem sourceS1_shape : 64453445 + 105 ≤ 131071 * (491 + 1) := by decide
theorem sourceS2_shape : 90779500 + 150 ≤ 131071 * (692 + 1) := by decide

theorem sourceS1_low_positive (j : ℕ) (hj : j ≤ 13) :
    0 < 64453445 - j * 50489 := by omega

theorem sourceS2_low_positive (j : ℕ) (hj : j ≤ 18) :
    0 < 90779500 - j * 50489 := by omega

end

end ProximityPrize.SubmissionLower.LocatorHelperArithmetic6783
