import ProximityPrize.SubmissionLower.CurveList82190Cells0
import ProximityPrize.SubmissionLower.CurveList82190Cells1
import ProximityPrize.SubmissionLower.CurveList82190Cells2
import ProximityPrize.SubmissionLower.CurveList82190Cells3
import ProximityPrize.SubmissionLower.CurveList82190Cells4
import ProximityPrize.SubmissionLower.CurveList82190Cells5
import ProximityPrize.SubmissionLower.CurveList82190Cells6
import ProximityPrize.SubmissionLower.CurveList82190Cells7

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace CurveList82190
open scoped BigOperators
open CJ1 (total total_eq_sum)

private def allowance : ℕ → ℕ → ℕ
  | 33, 18 => 120
  | 34, 17 => 119
  | 35, 16 => 117
  | 36, 15 => 115
  | 36, 16 => 109
  | 37, 14 => 112
  | 37, 15 => 108
  | 38, 13 => 109
  | 38, 14 => 106
  | 39, 12 => 105
  | 39, 13 => 104
  | 39, 14 => 99
  | 40, 11 => 101
  | 40, 12 => 101
  | 40, 13 => 98
  | 41, 11 => 98
  | 41, 12 => 96
  | 42, 10 => 94
  | 42, 11 => 94
  | 42, 12 => 89
  | 43, 10 => 91
  | 43, 11 => 88
  | 44, 9 => 88
  | 44, 10 => 86
  | 45, 9 => 84
  | 45, 10 => 80
  | 46, 8 => 81
  | 46, 9 => 79
  | 47, 8 => 77
  | 48, 7 => 74
  | 48, 8 => 71
  | 49, 7 => 70
  | 50, 6 => 66
  | 51, 6 => 62
  | 52, 5 => 58
  | 53, 5 => 54
  | 54, 4 => 49
  | 54, 5 => 48
  | 55, 4 => 45
  | 56, 3 => 40
  | 56, 4 => 40
  | 57, 3 => 36
  | 57, 4 => 35
  | 58, 2 => 30
  | 58, 3 => 32
  | 59, 2 => 27
  | 59, 3 => 28
  | 60, 1 => 20
  | 60, 2 => 24
  | 60, 3 => 24
  | 61, 1 => 18
  | 61, 2 => 21
  | 62, 0 => 10
  | 62, 1 => 16
  | 62, 2 => 18
  | 63, 0 => 9
  | 63, 1 => 14
  | 63, 2 => 15
  | 64, 0 => 8
  | 64, 1 => 12
  | 65, 0 => 7
  | 65, 1 => 10
  | 66, 0 => 6
  | 66, 1 => 8
  | 67, 0 => 5
  | 68, 0 => 4
  | 69, 0 => 3
  | q, u => nominal q u

private theorem bound (q u : ℕ) : (CJ0.blockMatrix source q ((u : ℤ)-21)).rank ≤ allowance q u := by
  unfold allowance
  split
  · exact rank_33_18
  · exact rank_34_17
  · exact rank_35_16
  · exact rank_36_15
  · exact rank_36_16
  · exact rank_37_14
  · exact rank_37_15
  · exact rank_38_13
  · exact rank_38_14
  · exact rank_39_12
  · exact rank_39_13
  · exact rank_39_14
  · exact rank_40_11
  · exact rank_40_12
  · exact rank_40_13
  · exact rank_41_11
  · exact rank_41_12
  · exact rank_42_10
  · exact rank_42_11
  · exact rank_42_12
  · exact rank_43_10
  · exact rank_43_11
  · exact rank_44_9
  · exact rank_44_10
  · exact rank_45_9
  · exact rank_45_10
  · exact rank_46_8
  · exact rank_46_9
  · exact rank_47_8
  · exact rank_48_7
  · exact rank_48_8
  · exact rank_49_7
  · exact rank_50_6
  · exact rank_51_6
  · exact rank_52_5
  · exact rank_53_5
  · exact rank_54_4
  · exact rank_54_5
  · exact rank_55_4
  · exact rank_56_3
  · exact rank_56_4
  · exact rank_57_3
  · exact rank_57_4
  · exact rank_58_2
  · exact rank_58_3
  · exact rank_59_2
  · exact rank_59_3
  · exact rank_60_1
  · exact rank_60_2
  · exact rank_60_3
  · exact rank_61_1
  · exact rank_61_2
  · exact rank_62_0
  · exact rank_62_1
  · exact rank_62_2
  · exact rank_63_0
  · exact rank_63_1
  · exact rank_63_2
  · exact rank_64_0
  · exact rank_64_1
  · exact rank_65_0
  · exact rank_65_1
  · exact rank_66_0
  · exact rank_66_1
  · exact rank_67_0
  · exact rank_68_0
  · exact rank_69_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def grade (q : ℕ) := total (allowance q) (72-q)
private def gradeTable : Fin 70 → ℕ := ![51, 150, 294, 480, 705, 966, 1260, 1584, 1935, 2310, 2706, 3080, 3393, 3648, 3848, 3996, 4095, 4148, 4158, 4128, 4061, 3960, 3828, 3696, 3564, 3432, 3300, 3168, 3036, 2904, 2772, 2641, 2511, 2382, 2255, 2130, 2007, 1887, 1770, 1656, 1546, 1440, 1337, 1239, 1144, 1053, 966, 883, 803, 728, 656, 588, 524, 464, 407, 355, 306, 261, 220, 183, 149, 120, 94, 72, 54, 39, 27, 18, 11, 6]
private theorem grade_0 : grade 0 = 51 := by decide +kernel
private theorem grade_1 : grade 1 = 150 := by decide +kernel
private theorem grade_2 : grade 2 = 294 := by decide +kernel
private theorem grade_3 : grade 3 = 480 := by decide +kernel
private theorem grade_4 : grade 4 = 705 := by decide +kernel
private theorem grade_5 : grade 5 = 966 := by decide +kernel
private theorem grade_6 : grade 6 = 1260 := by decide +kernel
private theorem grade_7 : grade 7 = 1584 := by decide +kernel
private theorem grade_8 : grade 8 = 1935 := by decide +kernel
private theorem grade_9 : grade 9 = 2310 := by decide +kernel
private theorem grade_10 : grade 10 = 2706 := by decide +kernel
private theorem grade_11 : grade 11 = 3080 := by decide +kernel
private theorem grade_12 : grade 12 = 3393 := by decide +kernel
private theorem grade_13 : grade 13 = 3648 := by decide +kernel
private theorem grade_14 : grade 14 = 3848 := by decide +kernel
private theorem grade_15 : grade 15 = 3996 := by decide +kernel
private theorem grade_16 : grade 16 = 4095 := by decide +kernel
private theorem grade_17 : grade 17 = 4148 := by decide +kernel
private theorem grade_18 : grade 18 = 4158 := by decide +kernel
private theorem grade_19 : grade 19 = 4128 := by decide +kernel
private theorem grade_20 : grade 20 = 4061 := by decide +kernel
private theorem grade_21 : grade 21 = 3960 := by decide +kernel
private theorem grade_22 : grade 22 = 3828 := by decide +kernel
private theorem grade_23 : grade 23 = 3696 := by decide +kernel
private theorem grade_24 : grade 24 = 3564 := by decide +kernel
private theorem grade_25 : grade 25 = 3432 := by decide +kernel
private theorem grade_26 : grade 26 = 3300 := by decide +kernel
private theorem grade_27 : grade 27 = 3168 := by decide +kernel
private theorem grade_28 : grade 28 = 3036 := by decide +kernel
private theorem grade_29 : grade 29 = 2904 := by decide +kernel
private theorem grade_30 : grade 30 = 2772 := by decide +kernel
private theorem grade_31 : grade 31 = 2641 := by decide +kernel
private theorem grade_32 : grade 32 = 2511 := by decide +kernel
private theorem grade_33 : grade 33 = 2382 := by decide +kernel
private theorem grade_34 : grade 34 = 2255 := by decide +kernel
private theorem grade_35 : grade 35 = 2130 := by decide +kernel
private theorem grade_36 : grade 36 = 2007 := by decide +kernel
private theorem grade_37 : grade 37 = 1887 := by decide +kernel
private theorem grade_38 : grade 38 = 1770 := by decide +kernel
private theorem grade_39 : grade 39 = 1656 := by decide +kernel
private theorem grade_40 : grade 40 = 1546 := by decide +kernel
private theorem grade_41 : grade 41 = 1440 := by decide +kernel
private theorem grade_42 : grade 42 = 1337 := by decide +kernel
private theorem grade_43 : grade 43 = 1239 := by decide +kernel
private theorem grade_44 : grade 44 = 1144 := by decide +kernel
private theorem grade_45 : grade 45 = 1053 := by decide +kernel
private theorem grade_46 : grade 46 = 966 := by decide +kernel
private theorem grade_47 : grade 47 = 883 := by decide +kernel
private theorem grade_48 : grade 48 = 803 := by decide +kernel
private theorem grade_49 : grade 49 = 728 := by decide +kernel
private theorem grade_50 : grade 50 = 656 := by decide +kernel
private theorem grade_51 : grade 51 = 588 := by decide +kernel
private theorem grade_52 : grade 52 = 524 := by decide +kernel
private theorem grade_53 : grade 53 = 464 := by decide +kernel
private theorem grade_54 : grade 54 = 407 := by decide +kernel
private theorem grade_55 : grade 55 = 355 := by decide +kernel
private theorem grade_56 : grade 56 = 306 := by decide +kernel
private theorem grade_57 : grade 57 = 261 := by decide +kernel
private theorem grade_58 : grade 58 = 220 := by decide +kernel
private theorem grade_59 : grade 59 = 183 := by decide +kernel
private theorem grade_60 : grade 60 = 149 := by decide +kernel
private theorem grade_61 : grade 61 = 120 := by decide +kernel
private theorem grade_62 : grade 62 = 94 := by decide +kernel
private theorem grade_63 : grade 63 = 72 := by decide +kernel
private theorem grade_64 : grade 64 = 54 := by decide +kernel
private theorem grade_65 : grade 65 = 39 := by decide +kernel
private theorem grade_66 : grade 66 = 27 := by decide +kernel
private theorem grade_67 : grade 67 = 18 := by decide +kernel
private theorem grade_68 : grade 68 = 11 := by decide +kernel
private theorem grade_69 : grade 69 = 6 := by decide +kernel

private theorem grade_table (q : Fin 70) : grade q.val = gradeTable q := by
  fin_cases q
  · exact grade_0
  · exact grade_1
  · exact grade_2
  · exact grade_3
  · exact grade_4
  · exact grade_5
  · exact grade_6
  · exact grade_7
  · exact grade_8
  · exact grade_9
  · exact grade_10
  · exact grade_11
  · exact grade_12
  · exact grade_13
  · exact grade_14
  · exact grade_15
  · exact grade_16
  · exact grade_17
  · exact grade_18
  · exact grade_19
  · exact grade_20
  · exact grade_21
  · exact grade_22
  · exact grade_23
  · exact grade_24
  · exact grade_25
  · exact grade_26
  · exact grade_27
  · exact grade_28
  · exact grade_29
  · exact grade_30
  · exact grade_31
  · exact grade_32
  · exact grade_33
  · exact grade_34
  · exact grade_35
  · exact grade_36
  · exact grade_37
  · exact grade_38
  · exact grade_39
  · exact grade_40
  · exact grade_41
  · exact grade_42
  · exact grade_43
  · exact grade_44
  · exact grade_45
  · exact grade_46
  · exact grade_47
  · exact grade_48
  · exact grade_49
  · exact grade_50
  · exact grade_51
  · exact grade_52
  · exact grade_53
  · exact grade_54
  · exact grade_55
  · exact grade_56
  · exact grade_57
  · exact grade_58
  · exact grade_59
  · exact grade_60
  · exact grade_61
  · exact grade_62
  · exact grade_63
  · exact grade_64
  · exact grade_65
  · exact grade_66
  · exact grade_67
  · exact grade_68
  · exact grade_69

theorem prefix_bound : CJ0.prefixRank source 70 ≤ 119588 := by
  change (∑ q ∈ Finset.range 70, ∑ u ∈ Finset.range (72-q),
    (CJ0.blockMatrix source q ((u : ℤ)-21)).rank) ≤ _
  calc
    _ ≤ ∑ q ∈ Finset.range 70, ∑ u ∈ Finset.range (72-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 70, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade, total_eq_sum]
    _ = ∑ q : Fin 70, gradeTable q := Finset.sum_congr rfl fun q _ => grade_table q
    _ = 119588 := by decide +kernel

end CurveList82190
