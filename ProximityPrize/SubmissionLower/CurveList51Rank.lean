import ProximityPrize.SubmissionLower.CurveList51Cells0
import ProximityPrize.SubmissionLower.CurveList51Cells1
import ProximityPrize.SubmissionLower.CurveList51Cells2
import ProximityPrize.SubmissionLower.CurveList51Cells3
import ProximityPrize.SubmissionLower.CurveList51Cells4
import ProximityPrize.SubmissionLower.CurveList51Cells5
import ProximityPrize.SubmissionLower.CurveList51Cells6
import ProximityPrize.SubmissionLower.CurveList51Cells7

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace CurveList51
open scoped BigOperators
open CJ1 (total total_eq_sum)

private def allowance : ℕ → ℕ → ℕ
  | 12, 39 => 84
  | 13, 38 => 92
  | 14, 37 => 99
  | 15, 36 => 105
  | 16, 35 => 110
  | 17, 34 => 114
  | 18, 33 => 117
  | 19, 32 => 119
  | 20, 31 => 120
  | 21, 30 => 120
  | 22, 29 => 120
  | 23, 28 => 120
  | 24, 27 => 120
  | 25, 26 => 120
  | 26, 25 => 120
  | 27, 24 => 120
  | 28, 23 => 120
  | 29, 22 => 120
  | 30, 21 => 120
  | 31, 20 => 120
  | 32, 19 => 120
  | 33, 18 => 119
  | 34, 17 => 118
  | 35, 16 => 116
  | 36, 15 => 114
  | 36, 16 => 109
  | 37, 14 => 111
  | 37, 15 => 108
  | 38, 13 => 108
  | 38, 14 => 106
  | 39, 12 => 104
  | 39, 13 => 104
  | 39, 14 => 99
  | 40, 12 => 101
  | 40, 13 => 98
  | 41, 11 => 98
  | 41, 12 => 96
  | 42, 11 => 94
  | 42, 12 => 89
  | 43, 10 => 91
  | 43, 11 => 88
  | 44, 10 => 86
  | 45, 9 => 84
  | 45, 10 => 80
  | 46, 9 => 79
  | 47, 8 => 77
  | 48, 8 => 71
  | 49, 7 => 70
  | 51, 6 => 62
  | 53, 5 => 54
  | 54, 5 => 48
  | 55, 4 => 45
  | 56, 4 => 40
  | 57, 3 => 36
  | 57, 4 => 35
  | 58, 3 => 32
  | 59, 2 => 27
  | 59, 3 => 28
  | 60, 2 => 24
  | 60, 3 => 24
  | 61, 1 => 18
  | 61, 2 => 21
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
  · exact rank_12_39
  · exact rank_13_38
  · exact rank_14_37
  · exact rank_15_36
  · exact rank_16_35
  · exact rank_17_34
  · exact rank_18_33
  · exact rank_19_32
  · exact rank_20_31
  · exact rank_21_30
  · exact rank_22_29
  · exact rank_23_28
  · exact rank_24_27
  · exact rank_25_26
  · exact rank_26_25
  · exact rank_27_24
  · exact rank_28_23
  · exact rank_29_22
  · exact rank_30_21
  · exact rank_31_20
  · exact rank_32_19
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
  · exact rank_40_12
  · exact rank_40_13
  · exact rank_41_11
  · exact rank_41_12
  · exact rank_42_11
  · exact rank_42_12
  · exact rank_43_10
  · exact rank_43_11
  · exact rank_44_10
  · exact rank_45_9
  · exact rank_45_10
  · exact rank_46_9
  · exact rank_47_8
  · exact rank_48_8
  · exact rank_49_7
  · exact rank_51_6
  · exact rank_53_5
  · exact rank_54_5
  · exact rank_55_4
  · exact rank_56_4
  · exact rank_57_3
  · exact rank_57_4
  · exact rank_58_3
  · exact rank_59_2
  · exact rank_59_3
  · exact rank_60_2
  · exact rank_60_3
  · exact rank_61_1
  · exact rank_61_2
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
private def gradeTable : Fin 70 → ℕ := ![51, 150, 294, 480, 705, 966, 1260, 1584, 1935, 2310, 2665, 3000, 3315, 3572, 3774, 3924, 4025, 4080, 4092, 4064, 3999, 3900, 3770, 3640, 3510, 3380, 3250, 3120, 2990, 2860, 2730, 2601, 2473, 2346, 2221, 2098, 1977, 1859, 1744, 1632, 1524, 1419, 1318, 1220, 1127, 1036, 951, 868, 790, 715, 645, 577, 515, 455, 400, 348, 301, 256, 217, 180, 148, 119, 94, 72, 54, 39, 27, 18, 11, 6]
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
private theorem grade_10 : grade 10 = 2665 := by decide +kernel
private theorem grade_11 : grade 11 = 3000 := by decide +kernel
private theorem grade_12 : grade 12 = 3315 := by decide +kernel
private theorem grade_13 : grade 13 = 3572 := by decide +kernel
private theorem grade_14 : grade 14 = 3774 := by decide +kernel
private theorem grade_15 : grade 15 = 3924 := by decide +kernel
private theorem grade_16 : grade 16 = 4025 := by decide +kernel
private theorem grade_17 : grade 17 = 4080 := by decide +kernel
private theorem grade_18 : grade 18 = 4092 := by decide +kernel
private theorem grade_19 : grade 19 = 4064 := by decide +kernel
private theorem grade_20 : grade 20 = 3999 := by decide +kernel
private theorem grade_21 : grade 21 = 3900 := by decide +kernel
private theorem grade_22 : grade 22 = 3770 := by decide +kernel
private theorem grade_23 : grade 23 = 3640 := by decide +kernel
private theorem grade_24 : grade 24 = 3510 := by decide +kernel
private theorem grade_25 : grade 25 = 3380 := by decide +kernel
private theorem grade_26 : grade 26 = 3250 := by decide +kernel
private theorem grade_27 : grade 27 = 3120 := by decide +kernel
private theorem grade_28 : grade 28 = 2990 := by decide +kernel
private theorem grade_29 : grade 29 = 2860 := by decide +kernel
private theorem grade_30 : grade 30 = 2730 := by decide +kernel
private theorem grade_31 : grade 31 = 2601 := by decide +kernel
private theorem grade_32 : grade 32 = 2473 := by decide +kernel
private theorem grade_33 : grade 33 = 2346 := by decide +kernel
private theorem grade_34 : grade 34 = 2221 := by decide +kernel
private theorem grade_35 : grade 35 = 2098 := by decide +kernel
private theorem grade_36 : grade 36 = 1977 := by decide +kernel
private theorem grade_37 : grade 37 = 1859 := by decide +kernel
private theorem grade_38 : grade 38 = 1744 := by decide +kernel
private theorem grade_39 : grade 39 = 1632 := by decide +kernel
private theorem grade_40 : grade 40 = 1524 := by decide +kernel
private theorem grade_41 : grade 41 = 1419 := by decide +kernel
private theorem grade_42 : grade 42 = 1318 := by decide +kernel
private theorem grade_43 : grade 43 = 1220 := by decide +kernel
private theorem grade_44 : grade 44 = 1127 := by decide +kernel
private theorem grade_45 : grade 45 = 1036 := by decide +kernel
private theorem grade_46 : grade 46 = 951 := by decide +kernel
private theorem grade_47 : grade 47 = 868 := by decide +kernel
private theorem grade_48 : grade 48 = 790 := by decide +kernel
private theorem grade_49 : grade 49 = 715 := by decide +kernel
private theorem grade_50 : grade 50 = 645 := by decide +kernel
private theorem grade_51 : grade 51 = 577 := by decide +kernel
private theorem grade_52 : grade 52 = 515 := by decide +kernel
private theorem grade_53 : grade 53 = 455 := by decide +kernel
private theorem grade_54 : grade 54 = 400 := by decide +kernel
private theorem grade_55 : grade 55 = 348 := by decide +kernel
private theorem grade_56 : grade 56 = 301 := by decide +kernel
private theorem grade_57 : grade 57 = 256 := by decide +kernel
private theorem grade_58 : grade 58 = 217 := by decide +kernel
private theorem grade_59 : grade 59 = 180 := by decide +kernel
private theorem grade_60 : grade 60 = 148 := by decide +kernel
private theorem grade_61 : grade 61 = 119 := by decide +kernel
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

theorem prefix_bound : CJ0.prefixRank source 70 ≤ 117796 := by
  change (∑ q ∈ Finset.range 70, ∑ u ∈ Finset.range (72-q),
    (CJ0.blockMatrix source q ((u : ℤ)-21)).rank) ≤ _
  calc
    _ ≤ ∑ q ∈ Finset.range 70, ∑ u ∈ Finset.range (72-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 70, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade, total_eq_sum]
    _ = ∑ q : Fin 70, gradeTable q := Finset.sum_congr rfl fun q _ => grade_table q
    _ = 117796 := by decide +kernel

end CurveList51
