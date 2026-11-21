import ProximityPrize.SubmissionLower.CurveList179876Cells0
import ProximityPrize.SubmissionLower.CurveList179876Cells1
import ProximityPrize.SubmissionLower.CurveList179876Cells2
import ProximityPrize.SubmissionLower.CurveList179876Cells3
import ProximityPrize.SubmissionLower.CurveList179876Cells4
import ProximityPrize.SubmissionLower.CurveList179876Cells5
import ProximityPrize.SubmissionLower.CurveList179876Cells6
import ProximityPrize.SubmissionLower.CurveList179876Cells7

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace CurveList179876
open scoped BigOperators
open CJ1 (total total_eq_sum)

private def allowance : ℕ → ℕ → ℕ
  | 36, 19 => 131
  | 37, 18 => 130
  | 38, 17 => 128
  | 39, 16 => 126
  | 39, 17 => 120
  | 40, 15 => 123
  | 40, 16 => 119
  | 41, 14 => 120
  | 41, 15 => 117
  | 42, 13 => 116
  | 42, 14 => 115
  | 42, 15 => 109
  | 43, 12 => 112
  | 43, 13 => 112
  | 43, 14 => 108
  | 44, 12 => 109
  | 44, 13 => 106
  | 45, 11 => 105
  | 45, 12 => 104
  | 45, 13 => 99
  | 46, 11 => 101
  | 46, 12 => 98
  | 47, 10 => 98
  | 47, 11 => 96
  | 48, 10 => 94
  | 48, 11 => 89
  | 49, 9 => 91
  | 49, 10 => 88
  | 50, 9 => 86
  | 51, 8 => 84
  | 51, 9 => 80
  | 52, 8 => 79
  | 53, 7 => 76
  | 54, 7 => 71
  | 55, 6 => 68
  | 56, 6 => 63
  | 57, 5 => 59
  | 58, 5 => 54
  | 59, 4 => 50
  | 59, 5 => 48
  | 60, 4 => 45
  | 61, 3 => 40
  | 61, 4 => 40
  | 62, 3 => 36
  | 62, 4 => 35
  | 63, 2 => 30
  | 63, 3 => 32
  | 64, 2 => 27
  | 64, 3 => 28
  | 65, 1 => 20
  | 65, 2 => 24
  | 65, 3 => 24
  | 66, 1 => 18
  | 66, 2 => 21
  | 67, 0 => 10
  | 67, 1 => 16
  | 67, 2 => 18
  | 68, 0 => 9
  | 68, 1 => 14
  | 68, 2 => 15
  | 69, 0 => 8
  | 69, 1 => 12
  | 70, 0 => 7
  | 70, 1 => 10
  | 71, 0 => 6
  | 71, 1 => 8
  | 72, 0 => 5
  | 73, 0 => 4
  | 74, 0 => 3
  | q, u => nominal q u

private theorem bound (q u : ℕ) : (CJ0.blockMatrix source q ((u : ℤ)-22)).rank ≤ allowance q u := by
  unfold allowance
  split
  · exact rank_36_19
  · exact rank_37_18
  · exact rank_38_17
  · exact rank_39_16
  · exact rank_39_17
  · exact rank_40_15
  · exact rank_40_16
  · exact rank_41_14
  · exact rank_41_15
  · exact rank_42_13
  · exact rank_42_14
  · exact rank_42_15
  · exact rank_43_12
  · exact rank_43_13
  · exact rank_43_14
  · exact rank_44_12
  · exact rank_44_13
  · exact rank_45_11
  · exact rank_45_12
  · exact rank_45_13
  · exact rank_46_11
  · exact rank_46_12
  · exact rank_47_10
  · exact rank_47_11
  · exact rank_48_10
  · exact rank_48_11
  · exact rank_49_9
  · exact rank_49_10
  · exact rank_50_9
  · exact rank_51_8
  · exact rank_51_9
  · exact rank_52_8
  · exact rank_53_7
  · exact rank_54_7
  · exact rank_55_6
  · exact rank_56_6
  · exact rank_57_5
  · exact rank_58_5
  · exact rank_59_4
  · exact rank_59_5
  · exact rank_60_4
  · exact rank_61_3
  · exact rank_61_4
  · exact rank_62_3
  · exact rank_62_4
  · exact rank_63_2
  · exact rank_63_3
  · exact rank_64_2
  · exact rank_64_3
  · exact rank_65_1
  · exact rank_65_2
  · exact rank_65_3
  · exact rank_66_1
  · exact rank_66_2
  · exact rank_67_0
  · exact rank_67_1
  · exact rank_67_2
  · exact rank_68_0
  · exact rank_68_1
  · exact rank_68_2
  · exact rank_69_0
  · exact rank_69_1
  · exact rank_70_0
  · exact rank_70_1
  · exact rank_71_0
  · exact rank_71_1
  · exact rank_72_0
  · exact rank_73_0
  · exact rank_74_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def grade (q : ℕ) := total (allowance q) (77-q)
private def gradeTable : Fin 76 → ℕ := ![55, 162, 318, 520, 765, 1050, 1372, 1728, 2115, 2530, 2970, 3388, 3784, 4116, 4387, 4600, 4758, 4864, 4921, 4932, 4900, 4828, 4719, 4576, 4433, 4290, 4147, 4004, 3861, 3718, 3575, 3432, 3289, 3146, 3004, 2863, 2723, 2585, 2449, 2315, 2184, 2056, 1931, 1810, 1693, 1579, 1470, 1364, 1263, 1165, 1072, 982, 897, 815, 738, 664, 595, 529, 468, 410, 357, 307, 262, 220, 183, 149, 120, 94, 72, 54, 39, 27, 18, 11, 6, 3]
private theorem grade_0 : grade 0 = 55 := by decide +kernel
private theorem grade_1 : grade 1 = 162 := by decide +kernel
private theorem grade_2 : grade 2 = 318 := by decide +kernel
private theorem grade_3 : grade 3 = 520 := by decide +kernel
private theorem grade_4 : grade 4 = 765 := by decide +kernel
private theorem grade_5 : grade 5 = 1050 := by decide +kernel
private theorem grade_6 : grade 6 = 1372 := by decide +kernel
private theorem grade_7 : grade 7 = 1728 := by decide +kernel
private theorem grade_8 : grade 8 = 2115 := by decide +kernel
private theorem grade_9 : grade 9 = 2530 := by decide +kernel
private theorem grade_10 : grade 10 = 2970 := by decide +kernel
private theorem grade_11 : grade 11 = 3388 := by decide +kernel
private theorem grade_12 : grade 12 = 3784 := by decide +kernel
private theorem grade_13 : grade 13 = 4116 := by decide +kernel
private theorem grade_14 : grade 14 = 4387 := by decide +kernel
private theorem grade_15 : grade 15 = 4600 := by decide +kernel
private theorem grade_16 : grade 16 = 4758 := by decide +kernel
private theorem grade_17 : grade 17 = 4864 := by decide +kernel
private theorem grade_18 : grade 18 = 4921 := by decide +kernel
private theorem grade_19 : grade 19 = 4932 := by decide +kernel
private theorem grade_20 : grade 20 = 4900 := by decide +kernel
private theorem grade_21 : grade 21 = 4828 := by decide +kernel
private theorem grade_22 : grade 22 = 4719 := by decide +kernel
private theorem grade_23 : grade 23 = 4576 := by decide +kernel
private theorem grade_24 : grade 24 = 4433 := by decide +kernel
private theorem grade_25 : grade 25 = 4290 := by decide +kernel
private theorem grade_26 : grade 26 = 4147 := by decide +kernel
private theorem grade_27 : grade 27 = 4004 := by decide +kernel
private theorem grade_28 : grade 28 = 3861 := by decide +kernel
private theorem grade_29 : grade 29 = 3718 := by decide +kernel
private theorem grade_30 : grade 30 = 3575 := by decide +kernel
private theorem grade_31 : grade 31 = 3432 := by decide +kernel
private theorem grade_32 : grade 32 = 3289 := by decide +kernel
private theorem grade_33 : grade 33 = 3146 := by decide +kernel
private theorem grade_34 : grade 34 = 3004 := by decide +kernel
private theorem grade_35 : grade 35 = 2863 := by decide +kernel
private theorem grade_36 : grade 36 = 2723 := by decide +kernel
private theorem grade_37 : grade 37 = 2585 := by decide +kernel
private theorem grade_38 : grade 38 = 2449 := by decide +kernel
private theorem grade_39 : grade 39 = 2315 := by decide +kernel
private theorem grade_40 : grade 40 = 2184 := by decide +kernel
private theorem grade_41 : grade 41 = 2056 := by decide +kernel
private theorem grade_42 : grade 42 = 1931 := by decide +kernel
private theorem grade_43 : grade 43 = 1810 := by decide +kernel
private theorem grade_44 : grade 44 = 1693 := by decide +kernel
private theorem grade_45 : grade 45 = 1579 := by decide +kernel
private theorem grade_46 : grade 46 = 1470 := by decide +kernel
private theorem grade_47 : grade 47 = 1364 := by decide +kernel
private theorem grade_48 : grade 48 = 1263 := by decide +kernel
private theorem grade_49 : grade 49 = 1165 := by decide +kernel
private theorem grade_50 : grade 50 = 1072 := by decide +kernel
private theorem grade_51 : grade 51 = 982 := by decide +kernel
private theorem grade_52 : grade 52 = 897 := by decide +kernel
private theorem grade_53 : grade 53 = 815 := by decide +kernel
private theorem grade_54 : grade 54 = 738 := by decide +kernel
private theorem grade_55 : grade 55 = 664 := by decide +kernel
private theorem grade_56 : grade 56 = 595 := by decide +kernel
private theorem grade_57 : grade 57 = 529 := by decide +kernel
private theorem grade_58 : grade 58 = 468 := by decide +kernel
private theorem grade_59 : grade 59 = 410 := by decide +kernel
private theorem grade_60 : grade 60 = 357 := by decide +kernel
private theorem grade_61 : grade 61 = 307 := by decide +kernel
private theorem grade_62 : grade 62 = 262 := by decide +kernel
private theorem grade_63 : grade 63 = 220 := by decide +kernel
private theorem grade_64 : grade 64 = 183 := by decide +kernel
private theorem grade_65 : grade 65 = 149 := by decide +kernel
private theorem grade_66 : grade 66 = 120 := by decide +kernel
private theorem grade_67 : grade 67 = 94 := by decide +kernel
private theorem grade_68 : grade 68 = 72 := by decide +kernel
private theorem grade_69 : grade 69 = 54 := by decide +kernel
private theorem grade_70 : grade 70 = 39 := by decide +kernel
private theorem grade_71 : grade 71 = 27 := by decide +kernel
private theorem grade_72 : grade 72 = 18 := by decide +kernel
private theorem grade_73 : grade 73 = 11 := by decide +kernel
private theorem grade_74 : grade 74 = 6 := by decide +kernel
private theorem grade_75 : grade 75 = 3 := by decide +kernel

private theorem grade_table (q : Fin 76) : grade q.val = gradeTable q := by
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
  · exact grade_70
  · exact grade_71
  · exact grade_72
  · exact grade_73
  · exact grade_74
  · exact grade_75

theorem prefix_bound : CJ0.prefixRank source 76 ≤ 151799 := by
  change (∑ q ∈ Finset.range 76, ∑ u ∈ Finset.range (77-q),
    (CJ0.blockMatrix source q ((u : ℤ)-22)).rank) ≤ _
  calc
    _ ≤ ∑ q ∈ Finset.range 76, ∑ u ∈ Finset.range (77-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 76, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade, total_eq_sum]
    _ = ∑ q : Fin 76, gradeTable q := Finset.sum_congr rfl fun q _ => grade_table q
    _ = 151799 := by decide +kernel

end CurveList179876
