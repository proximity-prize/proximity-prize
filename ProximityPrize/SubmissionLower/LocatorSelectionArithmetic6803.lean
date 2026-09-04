import ProximityPrize.SubmissionLower.LocatorSelectionRankChunks6803

/-!
# Arithmetic for the 68.03 selected-pair interpolation sources

These are the smallest profile changes used by the retuned selection layer.
The A profile is promoted to multiplicity 98, the TCap total budget to 6679,
and the middle-preserving B profile needs one extra slope unit and total 14261.
-/

namespace ProximityPrize.SubmissionLower.LocatorSelectionArithmetic6803

open ProximityPrize.Benchmark
open RCN100 RCN119 RCN302 LocatorFastKernelArithmetic LocatorLowQuotient
open LocatorSelectionRankChunks6803
open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def agreements : ℕ := 181363

def weightedA : ℕ := 17773574
def weightedTCap : ℕ := 32826703
def weightedB : ℕ := 20131293

theorem weighted_profiles :
    weightedA = 98 * agreements ∧
    weightedTCap = 181 * agreements ∧
    weightedB = 111 * agreements := by
  decide

theorem coefficientCountA_exact :
    coefficientCount weightedA 131071 130000 29 = 3797049526774600 := by
  change coefficientCount (135 * 131071 + 78989) 131071 130000 29 = _
  rw [coefficientCount_eq_oneResidueCoefficientCount
    135 78989 131071 130000 29 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

theorem coefficientCountTCap_exact :
    coefficientCount weightedTCap 131071 6679 56 = 1228391995298340 := by
  change coefficientCount (250 * 131071 + 58953) 131071 6679 56 = _
  rw [coefficientCount_eq_oneResidueCoefficientCount
    250 58953 131071 6679 56 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

theorem coefficientCountB_exact :
    coefficientCount weightedB 131071 14261 34 = 615495218291835 := by
  change coefficientCount (153 * 131071 + 77430) 131071 14261 34 = _
  rw [coefficientCount_eq_oneResidueCoefficientCount
    153 77430 131071 14261 34 (by decide) (by decide) (by decide)
      (by decide)]
  norm_num [oneResidueCoefficientCount, smallChoose, Nat.descFactorial]

private theorem fastLocalRankBoundA_exact :
    fastLocalRankBound 98 130000 29 = 14484454485 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 98, rankRowA r) = _
  rw [Finset.sum_range_add rankRowA 64 34, rankA_0, rankA_64]

private theorem fastLocalRankBoundTCap_exact :
    fastLocalRankBound 181 6679 56 = 4685942184 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 181, rankRowTCap r) = _
  rw [Finset.sum_range_add rankRowTCap 128 53,
    Finset.sum_range_add rankRowTCap 64 64,
    rankTCap_0, rankTCap_64, rankTCap_128]

private theorem fastLocalRankBoundB_exact :
    fastLocalRankBound 111 14261 34 = 2347927890 := by
  unfold fastLocalRankBound
  rw [kernelSumRange_eq]
  change (∑ r ∈ Finset.range 111, rankRowB r) = _
  rw [Finset.sum_range_add rankRowB 64 47, rankB_0, rankB_64]

theorem kernelA_rank :
    localRankBound 98 130000 29 = 14484454485 := by
  rw [localRankBound_eq_fastLocalRankBound 98 130000 29 (by decide)]
  exact fastLocalRankBoundA_exact

theorem kernelTCap_rank :
    localRankBound 181 6679 56 = 4685942184 := by
  rw [localRankBound_eq_fastLocalRankBound 181 6679 56 (by decide)]
  exact fastLocalRankBoundTCap_exact

theorem kernelB_rank :
    localRankBound 111 14261 34 = 2347927890 := by
  rw [localRankBound_eq_fastLocalRankBound 111 14261 34 (by decide)]
  exact fastLocalRankBoundB_exact

theorem kernelA_nullity :
    coefficientCount weightedA 131071 130000 29 -
      262144 * localRankBound 98 130000 29 = 36690258760 := by
  rw [coefficientCountA_exact, kernelA_rank]

theorem kernelTCap_nullity :
    coefficientCount weightedTCap 131071 6679 56 -
      262144 * localRankBound 181 6679 56 = 367415844 := by
  rw [coefficientCountTCap_exact, kernelTCap_rank]

theorem kernelB_nullity :
    coefficientCount weightedB 131071 14261 34 -
      262144 * localRankBound 111 14261 34 = 9495675 := by
  rw [coefficientCountB_exact, kernelB_rank]

theorem kernelA_gate :
    262144 * localRankBound 98 130000 29 <
      coefficientCount weightedA 131071 130000 29 := by
  apply Nat.sub_pos_iff_lt.mp
  rw [kernelA_nullity]
  norm_num

theorem kernelTCap_gate :
    262144 * localRankBound 181 6679 56 <
      coefficientCount weightedTCap 131071 6679 56 := by
  apply Nat.sub_pos_iff_lt.mp
  rw [kernelTCap_nullity]
  norm_num

theorem kernelB_gate :
    262144 * localRankBound 111 14261 34 <
      coefficientCount weightedB 131071 14261 34 := by
  apply Nat.sub_pos_iff_lt.mp
  rw [kernelB_nullity]
  norm_num

theorem kernelTCap_total_quotient_lt :
    coefficientCount weightedTCap 131071 2 56 <
      coefficientCount weightedTCap 131071 6679 56 -
        262144 * localRankBound 181 6679 56 := by
  rw [kernelTCap_nullity]
  norm_num [coefficientCount, weightedTCap]

end ProximityPrize.SubmissionLower.LocatorSelectionArithmetic6803
