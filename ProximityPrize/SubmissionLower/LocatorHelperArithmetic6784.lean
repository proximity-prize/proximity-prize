import ProximityPrize.SubmissionLower.LocatorRankClosed
import ProximityPrize.SubmissionLower.LocatorKernelEval
import ProximityPrize.SubmissionLower.N5

namespace ProximityPrize.SubmissionLower.LocatorHelperArithmetic6784

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
  rw [LocatorRankClosed.localRankBound_eq_fast 355 350000 105 (by decide)]
  decide +kernel

theorem sourceS1_nullity :
    coefficientCount 64446700 131071 350000 105 -
      262144 * localRankBound 355 350000 105 = 3070668257066075 := by
  rw [sourceS1_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    64446700 131071 350000 105 492 (by decide) (by decide)]
  decide

theorem sourceS2_rank :
    localRankBound 500 1000000 150 = 14383345717650 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 500 1000000 150 (by decide)]
  decide +kernel

theorem sourceS2_nullity :
    coefficientCount 90770000 131071 1000000 150 -
      262144 * localRankBound 500 1000000 150 = 27032429632837297 := by
  rw [sourceS2_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    90770000 131071 1000000 150 693 (by decide) (by decide)]
  decide

theorem sourceS3_rank :
    localRankBound 810 350000 243 = 21307937367528 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 810 350000 243 (by decide)]
  decide +kernel

theorem sourceS3_nullity :
    coefficientCount 147047400 131071 350000 243 -
      262144 * localRankBound 810 350000 243 = 41542667661965689 := by
  rw [sourceS3_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    147047400 131071 350000 243 1122 (by decide) (by decide)]
  decide

theorem sourceS4_rank :
    localRankBound 1220 675716 365 = 140022104376745 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 1220 675716 365 (by decide)]
  decide +kernel

theorem sourceS4_nullity :
    coefficientCount 221478800 131071 675716 365 -
      262144 * localRankBound 1220 675716 365 = 283874806582626245 := by
  rw [sourceS4_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    221478800 131071 675716 365 1690 (by decide) (by decide)]
  decide

theorem sourceS5_rank :
    localRankBound 750 669072 225 = 32367495042425 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 750 669072 225 (by decide)]
  decide +kernel

theorem sourceS5_nullity :
    coefficientCount 136155000 131071 669072 225 -
      262144 * localRankBound 750 669072 225 = 63706482303276921 := by
  rw [sourceS5_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    136155000 131071 669072 225 1039 (by decide) (by decide)]
  decide

theorem sourceS6_rank :
    localRankBound 750 219707 225 = 10617903252800 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 750 219707 225 (by decide)]
  decide +kernel

theorem sourceS6_nullity :
    coefficientCount 136155000 131071 219707 225 -
      262144 * localRankBound 750 219707 225 = 20196395213034561 := by
  rw [sourceS6_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    136155000 131071 219707 225 1039 (by decide) (by decide)]
  decide

private theorem kernel_finrank_lower
    (D L s m value : ℕ)
    (hvalue : coefficientCount D 131071 L s -
      262144 * localRankBound m L s = value)
    (u0 u1 : I → K) :
    value ≤ Module.finrank K
      (ConstraintKernel (K := K) D 131071 L s m
        IRSProfile.domain u0 u1) := by
  have hcard : Fintype.card I = 262144 := by
    norm_num [I, IRSProfile.Index]
  have hlo := constraintKernel_finrank_lower_bound
    D 131071 L s m IRSProfile.domain u0 u1
  have hlo' := hcard ▸ hlo
  exact hvalue ▸ hlo'

theorem sourceS1_finrank_lower_bound (u0 u1 : I → K) :
    3070668257066075 ≤ Module.finrank K
      (ConstraintKernel (K := K) 64446700 131071 350000 105 355
        IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 64446700 350000 105 355 3070668257066075
    sourceS1_nullity u0 u1

theorem sourceS2_finrank_lower_bound (u0 u1 : I → K) :
    27032429632837297 ≤ Module.finrank K
      (ConstraintKernel (K := K) 90770000 131071 1000000 150 500
        IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 90770000 1000000 150 500 27032429632837297
    sourceS2_nullity u0 u1

theorem sourceS3_finrank_lower_bound (u0 u1 : I → K) :
    41542667661965689 ≤ Module.finrank K
      (ConstraintKernel (K := K) 147047400 131071 350000 243 810
        IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 147047400 350000 243 810 41542667661965689
    sourceS3_nullity u0 u1

theorem sourceS4_finrank_lower_bound (u0 u1 : I → K) :
    283874806582626245 ≤ Module.finrank K
      (ConstraintKernel (K := K) 221478800 131071 675716 365 1220
        IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 221478800 675716 365 1220 283874806582626245
    sourceS4_nullity u0 u1

theorem sourceS5_finrank_lower_bound (u0 u1 : I → K) :
    63706482303276921 ≤ Module.finrank K
      (ConstraintKernel (K := K) 136155000 131071 669072 225 750
        IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 136155000 669072 225 750 63706482303276921
    sourceS5_nullity u0 u1

theorem sourceS6_finrank_lower_bound (u0 u1 : I → K) :
    20196395213034561 ≤ Module.finrank K
      (ConstraintKernel (K := K) 136155000 131071 219707 225 750
        IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 136155000 219707 225 750 20196395213034561
    sourceS6_nullity u0 u1

theorem factorial_cast_ne_zero_of_le_fortyfive
    {E : Type*} [Field E] [CharP E 2130706433]
    (j : ℕ) (hj : j ≤ 45) : (j.factorial : E) ≠ 0 := by
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
    64446700 - j * 50470 = (355 - j) * 181540 + j * 131070 := by
  omega

theorem sourceS2_stage_capacity (j : ℕ) (hj : j ≤ 18) :
    90770000 - j * 50470 = (500 - j) * 181540 + j * 131070 := by
  omega

theorem sourceS3_stage_capacity (j : ℕ) (hj : j ≤ 30) :
    147047400 - j * 50470 = (810 - j) * 181540 + j * 131070 := by
  omega

theorem sourceS4_stage_capacity (j : ℕ) (hj : j ≤ 45) :
    221478800 - j * 50470 = (1220 - j) * 181540 + j * 131070 := by
  omega

theorem sourceS5_stage_capacity (j : ℕ) (hj : j ≤ 28) :
    136155000 - j * 50470 = (750 - j) * 181540 + j * 131070 := by
  omega

theorem sourceS6_stage_capacity (j : ℕ) (hj : j ≤ 27) :
    136155000 - j * 50470 = (750 - j) * 181540 + j * 131070 := by
  omega

theorem sourceS1_shape : 64446700 + 105 ≤ 131071 * (491 + 1) := by decide
theorem sourceS2_shape : 90770000 + 150 ≤ 131071 * (692 + 1) := by decide
theorem sourceS3_shape : 147047400 + 243 ≤ 131071 * (1121 + 1) := by decide
theorem sourceS4_shape : 221478800 + 365 ≤ 131071 * (1689 + 1) := by decide
theorem sourceS5_shape : 136155000 + 225 ≤ 131071 * (1038 + 1) := by decide
theorem sourceS6_shape : 136155000 + 225 ≤ 131071 * (1038 + 1) := by decide

theorem sourceS1_low_positive (j : ℕ) (hj : j ≤ 13) :
    0 < 64446700 - j * 50470 := by omega

theorem sourceS2_low_positive (j : ℕ) (hj : j ≤ 18) :
    0 < 90770000 - j * 50470 := by omega

theorem sourceS3_low_positive (j : ℕ) (hj : j ≤ 30) :
    0 < 147047400 - j * 50470 := by omega

theorem sourceS4_low_positive (j : ℕ) (hj : j ≤ 45) :
    0 < 221478800 - j * 50470 := by omega

theorem sourceS5_low_positive (j : ℕ) (hj : j ≤ 28) :
    0 < 136155000 - j * 50470 := by omega

theorem sourceS6_low_positive (j : ℕ) (hj : j ≤ 27) :
    0 < 136155000 - j * 50470 := by omega

end

end ProximityPrize.SubmissionLower.LocatorHelperArithmetic6784
