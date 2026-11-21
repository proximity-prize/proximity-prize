import ProximityPrize.SubmissionLower.CurveList50Cells0
import ProximityPrize.SubmissionLower.CurveList50Cells1
import ProximityPrize.SubmissionLower.CurveList50Cells2
import ProximityPrize.SubmissionLower.CurveList50Cells3
import ProximityPrize.SubmissionLower.CurveList50Cells4
import ProximityPrize.SubmissionLower.CurveList50Cells5
import ProximityPrize.SubmissionLower.CurveList50Cells6
import ProximityPrize.SubmissionLower.CurveList50Cells7

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace CurveList50
open scoped BigOperators
open CJ1 (total total_eq_sum)

private def allowance : ℕ → ℕ → ℕ
  | 12, 38 => 84
  | 13, 37 => 92
  | 14, 36 => 99
  | 15, 35 => 105
  | 16, 34 => 110
  | 17, 33 => 114
  | 18, 32 => 117
  | 19, 31 => 119
  | 20, 30 => 120
  | 21, 29 => 120
  | 22, 28 => 120
  | 23, 27 => 120
  | 24, 26 => 120
  | 25, 25 => 120
  | 26, 24 => 120
  | 27, 23 => 120
  | 28, 22 => 120
  | 29, 21 => 120
  | 30, 20 => 120
  | 31, 19 => 120
  | 32, 18 => 119
  | 33, 17 => 118
  | 34, 16 => 116
  | 35, 15 => 114
  | 35, 16 => 109
  | 36, 14 => 111
  | 36, 15 => 108
  | 37, 13 => 108
  | 37, 14 => 106
  | 38, 12 => 104
  | 38, 13 => 104
  | 38, 14 => 99
  | 39, 12 => 101
  | 39, 13 => 98
  | 40, 11 => 98
  | 40, 12 => 96
  | 41, 11 => 94
  | 41, 12 => 89
  | 42, 10 => 91
  | 42, 11 => 88
  | 43, 10 => 86
  | 44, 9 => 84
  | 44, 10 => 80
  | 45, 9 => 79
  | 46, 8 => 77
  | 47, 8 => 71
  | 48, 7 => 70
  | 50, 6 => 62
  | 52, 5 => 54
  | 53, 5 => 48
  | 54, 4 => 45
  | 55, 4 => 40
  | 56, 3 => 36
  | 56, 4 => 35
  | 57, 3 => 32
  | 58, 2 => 27
  | 58, 3 => 28
  | 59, 2 => 24
  | 59, 3 => 24
  | 60, 1 => 18
  | 60, 2 => 21
  | 61, 1 => 16
  | 61, 2 => 18
  | 62, 0 => 9
  | 62, 1 => 14
  | 62, 2 => 15
  | 63, 0 => 8
  | 63, 1 => 12
  | 64, 0 => 7
  | 64, 1 => 10
  | 65, 0 => 6
  | 65, 1 => 8
  | 66, 0 => 5
  | 67, 0 => 4
  | 68, 0 => 3
  | q, u => nominal q u

private theorem bound (q u : ℕ) : (CJ0.blockMatrix source q ((u : ℤ)-21)).rank ≤ allowance q u := by
  unfold allowance
  split
  · exact rank_12_38
  · exact rank_13_37
  · exact rank_14_36
  · exact rank_15_35
  · exact rank_16_34
  · exact rank_17_33
  · exact rank_18_32
  · exact rank_19_31
  · exact rank_20_30
  · exact rank_21_29
  · exact rank_22_28
  · exact rank_23_27
  · exact rank_24_26
  · exact rank_25_25
  · exact rank_26_24
  · exact rank_27_23
  · exact rank_28_22
  · exact rank_29_21
  · exact rank_30_20
  · exact rank_31_19
  · exact rank_32_18
  · exact rank_33_17
  · exact rank_34_16
  · exact rank_35_15
  · exact rank_35_16
  · exact rank_36_14
  · exact rank_36_15
  · exact rank_37_13
  · exact rank_37_14
  · exact rank_38_12
  · exact rank_38_13
  · exact rank_38_14
  · exact rank_39_12
  · exact rank_39_13
  · exact rank_40_11
  · exact rank_40_12
  · exact rank_41_11
  · exact rank_41_12
  · exact rank_42_10
  · exact rank_42_11
  · exact rank_43_10
  · exact rank_44_9
  · exact rank_44_10
  · exact rank_45_9
  · exact rank_46_8
  · exact rank_47_8
  · exact rank_48_7
  · exact rank_50_6
  · exact rank_52_5
  · exact rank_53_5
  · exact rank_54_4
  · exact rank_55_4
  · exact rank_56_3
  · exact rank_56_4
  · exact rank_57_3
  · exact rank_58_2
  · exact rank_58_3
  · exact rank_59_2
  · exact rank_59_3
  · exact rank_60_1
  · exact rank_60_2
  · exact rank_61_1
  · exact rank_61_2
  · exact rank_62_0
  · exact rank_62_1
  · exact rank_62_2
  · exact rank_63_0
  · exact rank_63_1
  · exact rank_64_0
  · exact rank_64_1
  · exact rank_65_0
  · exact rank_65_1
  · exact rank_66_0
  · exact rank_67_0
  · exact rank_68_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def grade (q : ℕ) := total (allowance q) (71-q)
private def gradeTable : Fin 69 → ℕ := ![50, 147, 288, 470, 690, 945, 1232, 1548, 1890, 2255, 2600, 2925, 3230, 3478, 3672, 3815, 3910, 3960, 3968, 3937, 3870, 3770, 3640, 3510, 3380, 3250, 3120, 2990, 2860, 2730, 2601, 2473, 2346, 2221, 2098, 1977, 1859, 1744, 1632, 1524, 1419, 1318, 1220, 1127, 1036, 951, 868, 790, 715, 645, 577, 515, 455, 400, 348, 301, 256, 217, 180, 148, 119, 94, 72, 54, 39, 27, 18, 11, 6]
private theorem grade_0 : grade 0 = 50 := by decide +kernel
private theorem grade_1 : grade 1 = 147 := by decide +kernel
private theorem grade_2 : grade 2 = 288 := by decide +kernel
private theorem grade_3 : grade 3 = 470 := by decide +kernel
private theorem grade_4 : grade 4 = 690 := by decide +kernel
private theorem grade_5 : grade 5 = 945 := by decide +kernel
private theorem grade_6 : grade 6 = 1232 := by decide +kernel
private theorem grade_7 : grade 7 = 1548 := by decide +kernel
private theorem grade_8 : grade 8 = 1890 := by decide +kernel
private theorem grade_9 : grade 9 = 2255 := by decide +kernel
private theorem grade_10 : grade 10 = 2600 := by decide +kernel
private theorem grade_11 : grade 11 = 2925 := by decide +kernel
private theorem grade_12 : grade 12 = 3230 := by decide +kernel
private theorem grade_13 : grade 13 = 3478 := by decide +kernel
private theorem grade_14 : grade 14 = 3672 := by decide +kernel
private theorem grade_15 : grade 15 = 3815 := by decide +kernel
private theorem grade_16 : grade 16 = 3910 := by decide +kernel
private theorem grade_17 : grade 17 = 3960 := by decide +kernel
private theorem grade_18 : grade 18 = 3968 := by decide +kernel
private theorem grade_19 : grade 19 = 3937 := by decide +kernel
private theorem grade_20 : grade 20 = 3870 := by decide +kernel
private theorem grade_21 : grade 21 = 3770 := by decide +kernel
private theorem grade_22 : grade 22 = 3640 := by decide +kernel
private theorem grade_23 : grade 23 = 3510 := by decide +kernel
private theorem grade_24 : grade 24 = 3380 := by decide +kernel
private theorem grade_25 : grade 25 = 3250 := by decide +kernel
private theorem grade_26 : grade 26 = 3120 := by decide +kernel
private theorem grade_27 : grade 27 = 2990 := by decide +kernel
private theorem grade_28 : grade 28 = 2860 := by decide +kernel
private theorem grade_29 : grade 29 = 2730 := by decide +kernel
private theorem grade_30 : grade 30 = 2601 := by decide +kernel
private theorem grade_31 : grade 31 = 2473 := by decide +kernel
private theorem grade_32 : grade 32 = 2346 := by decide +kernel
private theorem grade_33 : grade 33 = 2221 := by decide +kernel
private theorem grade_34 : grade 34 = 2098 := by decide +kernel
private theorem grade_35 : grade 35 = 1977 := by decide +kernel
private theorem grade_36 : grade 36 = 1859 := by decide +kernel
private theorem grade_37 : grade 37 = 1744 := by decide +kernel
private theorem grade_38 : grade 38 = 1632 := by decide +kernel
private theorem grade_39 : grade 39 = 1524 := by decide +kernel
private theorem grade_40 : grade 40 = 1419 := by decide +kernel
private theorem grade_41 : grade 41 = 1318 := by decide +kernel
private theorem grade_42 : grade 42 = 1220 := by decide +kernel
private theorem grade_43 : grade 43 = 1127 := by decide +kernel
private theorem grade_44 : grade 44 = 1036 := by decide +kernel
private theorem grade_45 : grade 45 = 951 := by decide +kernel
private theorem grade_46 : grade 46 = 868 := by decide +kernel
private theorem grade_47 : grade 47 = 790 := by decide +kernel
private theorem grade_48 : grade 48 = 715 := by decide +kernel
private theorem grade_49 : grade 49 = 645 := by decide +kernel
private theorem grade_50 : grade 50 = 577 := by decide +kernel
private theorem grade_51 : grade 51 = 515 := by decide +kernel
private theorem grade_52 : grade 52 = 455 := by decide +kernel
private theorem grade_53 : grade 53 = 400 := by decide +kernel
private theorem grade_54 : grade 54 = 348 := by decide +kernel
private theorem grade_55 : grade 55 = 301 := by decide +kernel
private theorem grade_56 : grade 56 = 256 := by decide +kernel
private theorem grade_57 : grade 57 = 217 := by decide +kernel
private theorem grade_58 : grade 58 = 180 := by decide +kernel
private theorem grade_59 : grade 59 = 148 := by decide +kernel
private theorem grade_60 : grade 60 = 119 := by decide +kernel
private theorem grade_61 : grade 61 = 94 := by decide +kernel
private theorem grade_62 : grade 62 = 72 := by decide +kernel
private theorem grade_63 : grade 63 = 54 := by decide +kernel
private theorem grade_64 : grade 64 = 39 := by decide +kernel
private theorem grade_65 : grade 65 = 27 := by decide +kernel
private theorem grade_66 : grade 66 = 18 := by decide +kernel
private theorem grade_67 : grade 67 = 11 := by decide +kernel
private theorem grade_68 : grade 68 = 6 := by decide +kernel

private theorem grade_table (q : Fin 69) : grade q.val = gradeTable q := by
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

theorem prefix_bound : CJ0.prefixRank source 69 ≤ 112531 := by
  change (∑ q ∈ Finset.range 69, ∑ u ∈ Finset.range (71-q),
    (CJ0.blockMatrix source q ((u : ℤ)-21)).rank) ≤ _
  calc
    _ ≤ ∑ q ∈ Finset.range 69, ∑ u ∈ Finset.range (71-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 69, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade, total_eq_sum]
    _ = ∑ q : Fin 69, gradeTable q := Finset.sum_congr rfl fun q _ => grade_table q
    _ = 112531 := by decide +kernel

end CurveList50
