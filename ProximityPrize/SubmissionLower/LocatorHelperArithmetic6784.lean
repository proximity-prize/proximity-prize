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
    coefficientCount 64450250 131071 350000 105 -
      262144 * localRankBound 355 350000 105 = 3128508003044125 := by
  rw [sourceS1_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    64450250 131071 350000 105 492 (by decide) (by decide)]
  decide

theorem sourceS2_rank :
    localRankBound 500 1000000 150 = 14383345717650 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 500 1000000 150 (by decide)]
  decide +kernel

theorem sourceS2_nullity :
    coefficientCount 90775000 131071 1000000 150 -
      262144 * localRankBound 500 1000000 150 = 27498841879412297 := by
  rw [sourceS2_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    90775000 131071 1000000 150 693 (by decide) (by decide)]
  decide

theorem sourceS3_rank :
    localRankBound 810 350000 243 = 21307937367528 := by
  rw [LocatorRankClosed.localRankBound_eq_fast 810 350000 243 (by decide)]
  decide +kernel

theorem sourceS3_nullity :
    coefficientCount 147055500 131071 350000 243 -
      262144 * localRankBound 810 350000 243 = 42233531959641889 := by
  rw [sourceS3_rank, LocatorKernelEval.coefficientCount_eq_cutoff
    147055500 131071 350000 243 1122 (by decide) (by decide)]
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
    3128508003044125 ≤ Module.finrank K
      (ConstraintKernel (K := K) 64450250 131071 350000 105 355
        IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 64450250 350000 105 355 3128508003044125
    sourceS1_nullity u0 u1

theorem sourceS2_finrank_lower_bound (u0 u1 : I → K) :
    27498841879412297 ≤ Module.finrank K
      (ConstraintKernel (K := K) 90775000 131071 1000000 150 500
        IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 90775000 1000000 150 500 27498841879412297
    sourceS2_nullity u0 u1

theorem sourceS3_finrank_lower_bound (u0 u1 : I → K) :
    42233531959641889 ≤ Module.finrank K
      (ConstraintKernel (K := K) 147055500 131071 350000 243 810
        IRSProfile.domain u0 u1) :=
  kernel_finrank_lower 147055500 350000 243 810 42233531959641889
    sourceS3_nullity u0 u1

theorem factorial_cast_ne_zero_of_le_thirty
    {E : Type*} [Field E] [CharP E 2130706433]
    (j : ℕ) (hj : j ≤ 30) : (j.factorial : E) ≠ 0 := by
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
    64450250 - j * 50480 = (355 - j) * 181550 + j * 131070 := by
  omega

theorem sourceS2_stage_capacity (j : ℕ) (hj : j ≤ 18) :
    90775000 - j * 50480 = (500 - j) * 181550 + j * 131070 := by
  omega

theorem sourceS3_stage_capacity (j : ℕ) (hj : j ≤ 30) :
    147055500 - j * 50480 = (810 - j) * 181550 + j * 131070 := by
  omega

theorem sourceS1_shape : 64450250 + 105 ≤ 131071 * (491 + 1) := by decide
theorem sourceS2_shape : 90775000 + 150 ≤ 131071 * (692 + 1) := by decide
theorem sourceS3_shape : 147055500 + 243 ≤ 131071 * (1121 + 1) := by decide

theorem sourceS1_low_positive (j : ℕ) (hj : j ≤ 13) :
    0 < 64450250 - j * 50480 := by omega

theorem sourceS2_low_positive (j : ℕ) (hj : j ≤ 18) :
    0 < 90775000 - j * 50480 := by omega

theorem sourceS3_low_positive (j : ℕ) (hj : j ≤ 30) :
    0 < 147055500 - j * 50480 := by omega

end

end ProximityPrize.SubmissionLower.LocatorHelperArithmetic6784
