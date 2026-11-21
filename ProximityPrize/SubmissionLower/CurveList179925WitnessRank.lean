import ProximityPrize.SubmissionLower.CurveList179925WitnessCells0
import ProximityPrize.SubmissionLower.CurveList179925WitnessCells1
import ProximityPrize.SubmissionLower.CurveList179925WitnessCells2
import ProximityPrize.SubmissionLower.CurveList179925WitnessCells3
import ProximityPrize.SubmissionLower.CurveList179925WitnessCells4
import ProximityPrize.SubmissionLower.CurveList179925WitnessCells5
import ProximityPrize.SubmissionLower.CurveList179925WitnessCells6
import ProximityPrize.SubmissionLower.CurveList179925WitnessCells7

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace CurveList179925Witness
open scoped BigOperators
open CJ1 (total total_eq_sum)

private def allowance_35 : ℕ → ℕ
  | 18 => 120
  | u => nominal 35 u

private theorem bound_35 (u : ℕ) :
    (CJ0.blockMatrix source 35 ((u : ℤ)-21)).rank ≤ allowance_35 u := by
  unfold allowance_35
  split
  · exact rank_35_18
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_36 : ℕ → ℕ
  | 17 => 119
  | u => nominal 36 u

private theorem bound_36 (u : ℕ) :
    (CJ0.blockMatrix source 36 ((u : ℤ)-21)).rank ≤ allowance_36 u := by
  unfold allowance_36
  split
  · exact rank_36_17
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_37 : ℕ → ℕ
  | 16 => 117
  | u => nominal 37 u

private theorem bound_37 (u : ℕ) :
    (CJ0.blockMatrix source 37 ((u : ℤ)-21)).rank ≤ allowance_37 u := by
  unfold allowance_37
  split
  · exact rank_37_16
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_38 : ℕ → ℕ
  | 15 => 115
  | 16 => 109
  | u => nominal 38 u

private theorem bound_38 (u : ℕ) :
    (CJ0.blockMatrix source 38 ((u : ℤ)-21)).rank ≤ allowance_38 u := by
  unfold allowance_38
  split
  · exact rank_38_15
  · exact rank_38_16
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_39 : ℕ → ℕ
  | 14 => 112
  | 15 => 108
  | u => nominal 39 u

private theorem bound_39 (u : ℕ) :
    (CJ0.blockMatrix source 39 ((u : ℤ)-21)).rank ≤ allowance_39 u := by
  unfold allowance_39
  split
  · exact rank_39_14
  · exact rank_39_15
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_40 : ℕ → ℕ
  | 13 => 109
  | 14 => 106
  | u => nominal 40 u

private theorem bound_40 (u : ℕ) :
    (CJ0.blockMatrix source 40 ((u : ℤ)-21)).rank ≤ allowance_40 u := by
  unfold allowance_40
  split
  · exact rank_40_13
  · exact rank_40_14
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_41 : ℕ → ℕ
  | 12 => 105
  | 13 => 104
  | 14 => 99
  | u => nominal 41 u

private theorem bound_41 (u : ℕ) :
    (CJ0.blockMatrix source 41 ((u : ℤ)-21)).rank ≤ allowance_41 u := by
  unfold allowance_41
  split
  · exact rank_41_12
  · exact rank_41_13
  · exact rank_41_14
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_42 : ℕ → ℕ
  | 11 => 101
  | 12 => 101
  | 13 => 98
  | u => nominal 42 u

private theorem bound_42 (u : ℕ) :
    (CJ0.blockMatrix source 42 ((u : ℤ)-21)).rank ≤ allowance_42 u := by
  unfold allowance_42
  split
  · exact rank_42_11
  · exact rank_42_12
  · exact rank_42_13
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_43 : ℕ → ℕ
  | 11 => 98
  | 12 => 96
  | u => nominal 43 u

private theorem bound_43 (u : ℕ) :
    (CJ0.blockMatrix source 43 ((u : ℤ)-21)).rank ≤ allowance_43 u := by
  unfold allowance_43
  split
  · exact rank_43_11
  · exact rank_43_12
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_44 : ℕ → ℕ
  | 10 => 94
  | 11 => 94
  | 12 => 89
  | u => nominal 44 u

private theorem bound_44 (u : ℕ) :
    (CJ0.blockMatrix source 44 ((u : ℤ)-21)).rank ≤ allowance_44 u := by
  unfold allowance_44
  split
  · exact rank_44_10
  · exact rank_44_11
  · exact rank_44_12
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_45 : ℕ → ℕ
  | 10 => 91
  | 11 => 88
  | u => nominal 45 u

private theorem bound_45 (u : ℕ) :
    (CJ0.blockMatrix source 45 ((u : ℤ)-21)).rank ≤ allowance_45 u := by
  unfold allowance_45
  split
  · exact rank_45_10
  · exact rank_45_11
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_46 : ℕ → ℕ
  | 9 => 88
  | 10 => 86
  | u => nominal 46 u

private theorem bound_46 (u : ℕ) :
    (CJ0.blockMatrix source 46 ((u : ℤ)-21)).rank ≤ allowance_46 u := by
  unfold allowance_46
  split
  · exact rank_46_9
  · exact rank_46_10
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_47 : ℕ → ℕ
  | 9 => 84
  | 10 => 80
  | u => nominal 47 u

private theorem bound_47 (u : ℕ) :
    (CJ0.blockMatrix source 47 ((u : ℤ)-21)).rank ≤ allowance_47 u := by
  unfold allowance_47
  split
  · exact rank_47_9
  · exact rank_47_10
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_48 : ℕ → ℕ
  | 8 => 81
  | 9 => 79
  | u => nominal 48 u

private theorem bound_48 (u : ℕ) :
    (CJ0.blockMatrix source 48 ((u : ℤ)-21)).rank ≤ allowance_48 u := by
  unfold allowance_48
  split
  · exact rank_48_8
  · exact rank_48_9
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_49 : ℕ → ℕ
  | 8 => 77
  | u => nominal 49 u

private theorem bound_49 (u : ℕ) :
    (CJ0.blockMatrix source 49 ((u : ℤ)-21)).rank ≤ allowance_49 u := by
  unfold allowance_49
  split
  · exact rank_49_8
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_50 : ℕ → ℕ
  | 7 => 74
  | 8 => 71
  | u => nominal 50 u

private theorem bound_50 (u : ℕ) :
    (CJ0.blockMatrix source 50 ((u : ℤ)-21)).rank ≤ allowance_50 u := by
  unfold allowance_50
  split
  · exact rank_50_7
  · exact rank_50_8
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_51 : ℕ → ℕ
  | 7 => 70
  | u => nominal 51 u

private theorem bound_51 (u : ℕ) :
    (CJ0.blockMatrix source 51 ((u : ℤ)-21)).rank ≤ allowance_51 u := by
  unfold allowance_51
  split
  · exact rank_51_7
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_52 : ℕ → ℕ
  | 6 => 66
  | u => nominal 52 u

private theorem bound_52 (u : ℕ) :
    (CJ0.blockMatrix source 52 ((u : ℤ)-21)).rank ≤ allowance_52 u := by
  unfold allowance_52
  split
  · exact rank_52_6
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_53 : ℕ → ℕ
  | 6 => 62
  | u => nominal 53 u

private theorem bound_53 (u : ℕ) :
    (CJ0.blockMatrix source 53 ((u : ℤ)-21)).rank ≤ allowance_53 u := by
  unfold allowance_53
  split
  · exact rank_53_6
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_54 : ℕ → ℕ
  | 5 => 58
  | u => nominal 54 u

private theorem bound_54 (u : ℕ) :
    (CJ0.blockMatrix source 54 ((u : ℤ)-21)).rank ≤ allowance_54 u := by
  unfold allowance_54
  split
  · exact rank_54_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_55 : ℕ → ℕ
  | 5 => 54
  | u => nominal 55 u

private theorem bound_55 (u : ℕ) :
    (CJ0.blockMatrix source 55 ((u : ℤ)-21)).rank ≤ allowance_55 u := by
  unfold allowance_55
  split
  · exact rank_55_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_56 : ℕ → ℕ
  | 4 => 49
  | 5 => 48
  | u => nominal 56 u

private theorem bound_56 (u : ℕ) :
    (CJ0.blockMatrix source 56 ((u : ℤ)-21)).rank ≤ allowance_56 u := by
  unfold allowance_56
  split
  · exact rank_56_4
  · exact rank_56_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_57 : ℕ → ℕ
  | 4 => 45
  | u => nominal 57 u

private theorem bound_57 (u : ℕ) :
    (CJ0.blockMatrix source 57 ((u : ℤ)-21)).rank ≤ allowance_57 u := by
  unfold allowance_57
  split
  · exact rank_57_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_58 : ℕ → ℕ
  | 3 => 40
  | 4 => 40
  | u => nominal 58 u

private theorem bound_58 (u : ℕ) :
    (CJ0.blockMatrix source 58 ((u : ℤ)-21)).rank ≤ allowance_58 u := by
  unfold allowance_58
  split
  · exact rank_58_3
  · exact rank_58_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_59 : ℕ → ℕ
  | 3 => 36
  | 4 => 35
  | u => nominal 59 u

private theorem bound_59 (u : ℕ) :
    (CJ0.blockMatrix source 59 ((u : ℤ)-21)).rank ≤ allowance_59 u := by
  unfold allowance_59
  split
  · exact rank_59_3
  · exact rank_59_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_60 : ℕ → ℕ
  | 2 => 30
  | 3 => 32
  | u => nominal 60 u

private theorem bound_60 (u : ℕ) :
    (CJ0.blockMatrix source 60 ((u : ℤ)-21)).rank ≤ allowance_60 u := by
  unfold allowance_60
  split
  · exact rank_60_2
  · exact rank_60_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_61 : ℕ → ℕ
  | 2 => 27
  | 3 => 28
  | u => nominal 61 u

private theorem bound_61 (u : ℕ) :
    (CJ0.blockMatrix source 61 ((u : ℤ)-21)).rank ≤ allowance_61 u := by
  unfold allowance_61
  split
  · exact rank_61_2
  · exact rank_61_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_62 : ℕ → ℕ
  | 1 => 20
  | 2 => 24
  | 3 => 24
  | u => nominal 62 u

private theorem bound_62 (u : ℕ) :
    (CJ0.blockMatrix source 62 ((u : ℤ)-21)).rank ≤ allowance_62 u := by
  unfold allowance_62
  split
  · exact rank_62_1
  · exact rank_62_2
  · exact rank_62_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_63 : ℕ → ℕ
  | 1 => 18
  | 2 => 21
  | u => nominal 63 u

private theorem bound_63 (u : ℕ) :
    (CJ0.blockMatrix source 63 ((u : ℤ)-21)).rank ≤ allowance_63 u := by
  unfold allowance_63
  split
  · exact rank_63_1
  · exact rank_63_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_64 : ℕ → ℕ
  | 0 => 10
  | 1 => 16
  | 2 => 18
  | u => nominal 64 u

private theorem bound_64 (u : ℕ) :
    (CJ0.blockMatrix source 64 ((u : ℤ)-21)).rank ≤ allowance_64 u := by
  unfold allowance_64
  split
  · exact rank_64_0
  · exact rank_64_1
  · exact rank_64_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_65 : ℕ → ℕ
  | 0 => 9
  | 1 => 14
  | 2 => 15
  | u => nominal 65 u

private theorem bound_65 (u : ℕ) :
    (CJ0.blockMatrix source 65 ((u : ℤ)-21)).rank ≤ allowance_65 u := by
  unfold allowance_65
  split
  · exact rank_65_0
  · exact rank_65_1
  · exact rank_65_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_66 : ℕ → ℕ
  | 0 => 8
  | 1 => 12
  | u => nominal 66 u

private theorem bound_66 (u : ℕ) :
    (CJ0.blockMatrix source 66 ((u : ℤ)-21)).rank ≤ allowance_66 u := by
  unfold allowance_66
  split
  · exact rank_66_0
  · exact rank_66_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_67 : ℕ → ℕ
  | 0 => 7
  | 1 => 10
  | u => nominal 67 u

private theorem bound_67 (u : ℕ) :
    (CJ0.blockMatrix source 67 ((u : ℤ)-21)).rank ≤ allowance_67 u := by
  unfold allowance_67
  split
  · exact rank_67_0
  · exact rank_67_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_68 : ℕ → ℕ
  | 0 => 6
  | 1 => 8
  | u => nominal 68 u

private theorem bound_68 (u : ℕ) :
    (CJ0.blockMatrix source 68 ((u : ℤ)-21)).rank ≤ allowance_68 u := by
  unfold allowance_68
  split
  · exact rank_68_0
  · exact rank_68_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_69 : ℕ → ℕ
  | 0 => 5
  | u => nominal 69 u

private theorem bound_69 (u : ℕ) :
    (CJ0.blockMatrix source 69 ((u : ℤ)-21)).rank ≤ allowance_69 u := by
  unfold allowance_69
  split
  · exact rank_69_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_70 : ℕ → ℕ
  | 0 => 4
  | u => nominal 70 u

private theorem bound_70 (u : ℕ) :
    (CJ0.blockMatrix source 70 ((u : ℤ)-21)).rank ≤ allowance_70 u := by
  unfold allowance_70
  split
  · exact rank_70_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_71 : ℕ → ℕ
  | 0 => 3
  | u => nominal 71 u

private theorem bound_71 (u : ℕ) :
    (CJ0.blockMatrix source 71 ((u : ℤ)-21)).rank ≤ allowance_71 u := by
  unfold allowance_71
  split
  · exact rank_71_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance : ℕ → ℕ → ℕ
  | 35, u => allowance_35 u
  | 36, u => allowance_36 u
  | 37, u => allowance_37 u
  | 38, u => allowance_38 u
  | 39, u => allowance_39 u
  | 40, u => allowance_40 u
  | 41, u => allowance_41 u
  | 42, u => allowance_42 u
  | 43, u => allowance_43 u
  | 44, u => allowance_44 u
  | 45, u => allowance_45 u
  | 46, u => allowance_46 u
  | 47, u => allowance_47 u
  | 48, u => allowance_48 u
  | 49, u => allowance_49 u
  | 50, u => allowance_50 u
  | 51, u => allowance_51 u
  | 52, u => allowance_52 u
  | 53, u => allowance_53 u
  | 54, u => allowance_54 u
  | 55, u => allowance_55 u
  | 56, u => allowance_56 u
  | 57, u => allowance_57 u
  | 58, u => allowance_58 u
  | 59, u => allowance_59 u
  | 60, u => allowance_60 u
  | 61, u => allowance_61 u
  | 62, u => allowance_62 u
  | 63, u => allowance_63 u
  | 64, u => allowance_64 u
  | 65, u => allowance_65 u
  | 66, u => allowance_66 u
  | 67, u => allowance_67 u
  | 68, u => allowance_68 u
  | 69, u => allowance_69 u
  | 70, u => allowance_70 u
  | 71, u => allowance_71 u
  | q, u => nominal q u

private theorem bound (q u : ℕ) :
    (CJ0.blockMatrix source q ((u : ℤ)-21)).rank ≤ allowance q u := by
  unfold allowance
  split
  · exact bound_35 _
  · exact bound_36 _
  · exact bound_37 _
  · exact bound_38 _
  · exact bound_39 _
  · exact bound_40 _
  · exact bound_41 _
  · exact bound_42 _
  · exact bound_43 _
  · exact bound_44 _
  · exact bound_45 _
  · exact bound_46 _
  · exact bound_47 _
  · exact bound_48 _
  · exact bound_49 _
  · exact bound_50 _
  · exact bound_51 _
  · exact bound_52 _
  · exact bound_53 _
  · exact bound_54 _
  · exact bound_55 _
  · exact bound_56 _
  · exact bound_57 _
  · exact bound_58 _
  · exact bound_59 _
  · exact bound_60 _
  · exact bound_61 _
  · exact bound_62 _
  · exact bound_63 _
  · exact bound_64 _
  · exact bound_65 _
  · exact bound_66 _
  · exact bound_67 _
  · exact bound_68 _
  · exact bound_69 _
  · exact bound_70 _
  · exact bound_71 _
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def grade (q : ℕ) := total (allowance q) (74-q)
private def gradeTable : Fin 73 → ℕ := ![53, 156, 306, 500, 735, 1008, 1316, 1656, 2025, 2420, 2838, 3234, 3567, 3840, 4056, 4218, 4329, 4392, 4410, 4386, 4323, 4224, 4092, 3960, 3828, 3696, 3564, 3432, 3300, 3168, 3036, 2904, 2772, 2641, 2511, 2382, 2255, 2130, 2007, 1887, 1770, 1656, 1546, 1440, 1337, 1239, 1144, 1053, 966, 883, 803, 728, 656, 588, 524, 464, 407, 355, 306, 261, 220, 183, 149, 120, 94, 72, 54, 39, 27, 18, 11, 6, 3]
private theorem grade_0 : grade 0 = 53 := by decide +kernel
private theorem grade_1 : grade 1 = 156 := by decide +kernel
private theorem grade_2 : grade 2 = 306 := by decide +kernel
private theorem grade_3 : grade 3 = 500 := by decide +kernel
private theorem grade_4 : grade 4 = 735 := by decide +kernel
private theorem grade_5 : grade 5 = 1008 := by decide +kernel
private theorem grade_6 : grade 6 = 1316 := by decide +kernel
private theorem grade_7 : grade 7 = 1656 := by decide +kernel
private theorem grade_8 : grade 8 = 2025 := by decide +kernel
private theorem grade_9 : grade 9 = 2420 := by decide +kernel
private theorem grade_10 : grade 10 = 2838 := by decide +kernel
private theorem grade_11 : grade 11 = 3234 := by decide +kernel
private theorem grade_12 : grade 12 = 3567 := by decide +kernel
private theorem grade_13 : grade 13 = 3840 := by decide +kernel
private theorem grade_14 : grade 14 = 4056 := by decide +kernel
private theorem grade_15 : grade 15 = 4218 := by decide +kernel
private theorem grade_16 : grade 16 = 4329 := by decide +kernel
private theorem grade_17 : grade 17 = 4392 := by decide +kernel
private theorem grade_18 : grade 18 = 4410 := by decide +kernel
private theorem grade_19 : grade 19 = 4386 := by decide +kernel
private theorem grade_20 : grade 20 = 4323 := by decide +kernel
private theorem grade_21 : grade 21 = 4224 := by decide +kernel
private theorem grade_22 : grade 22 = 4092 := by decide +kernel
private theorem grade_23 : grade 23 = 3960 := by decide +kernel
private theorem grade_24 : grade 24 = 3828 := by decide +kernel
private theorem grade_25 : grade 25 = 3696 := by decide +kernel
private theorem grade_26 : grade 26 = 3564 := by decide +kernel
private theorem grade_27 : grade 27 = 3432 := by decide +kernel
private theorem grade_28 : grade 28 = 3300 := by decide +kernel
private theorem grade_29 : grade 29 = 3168 := by decide +kernel
private theorem grade_30 : grade 30 = 3036 := by decide +kernel
private theorem grade_31 : grade 31 = 2904 := by decide +kernel
private theorem grade_32 : grade 32 = 2772 := by decide +kernel
private theorem grade_33 : grade 33 = 2641 := by decide +kernel
private theorem grade_34 : grade 34 = 2511 := by decide +kernel
private theorem grade_35 : grade 35 = 2382 := by decide +kernel
private theorem grade_36 : grade 36 = 2255 := by decide +kernel
private theorem grade_37 : grade 37 = 2130 := by decide +kernel
private theorem grade_38 : grade 38 = 2007 := by decide +kernel
private theorem grade_39 : grade 39 = 1887 := by decide +kernel
private theorem grade_40 : grade 40 = 1770 := by decide +kernel
private theorem grade_41 : grade 41 = 1656 := by decide +kernel
private theorem grade_42 : grade 42 = 1546 := by decide +kernel
private theorem grade_43 : grade 43 = 1440 := by decide +kernel
private theorem grade_44 : grade 44 = 1337 := by decide +kernel
private theorem grade_45 : grade 45 = 1239 := by decide +kernel
private theorem grade_46 : grade 46 = 1144 := by decide +kernel
private theorem grade_47 : grade 47 = 1053 := by decide +kernel
private theorem grade_48 : grade 48 = 966 := by decide +kernel
private theorem grade_49 : grade 49 = 883 := by decide +kernel
private theorem grade_50 : grade 50 = 803 := by decide +kernel
private theorem grade_51 : grade 51 = 728 := by decide +kernel
private theorem grade_52 : grade 52 = 656 := by decide +kernel
private theorem grade_53 : grade 53 = 588 := by decide +kernel
private theorem grade_54 : grade 54 = 524 := by decide +kernel
private theorem grade_55 : grade 55 = 464 := by decide +kernel
private theorem grade_56 : grade 56 = 407 := by decide +kernel
private theorem grade_57 : grade 57 = 355 := by decide +kernel
private theorem grade_58 : grade 58 = 306 := by decide +kernel
private theorem grade_59 : grade 59 = 261 := by decide +kernel
private theorem grade_60 : grade 60 = 220 := by decide +kernel
private theorem grade_61 : grade 61 = 183 := by decide +kernel
private theorem grade_62 : grade 62 = 149 := by decide +kernel
private theorem grade_63 : grade 63 = 120 := by decide +kernel
private theorem grade_64 : grade 64 = 94 := by decide +kernel
private theorem grade_65 : grade 65 = 72 := by decide +kernel
private theorem grade_66 : grade 66 = 54 := by decide +kernel
private theorem grade_67 : grade 67 = 39 := by decide +kernel
private theorem grade_68 : grade 68 = 27 := by decide +kernel
private theorem grade_69 : grade 69 = 18 := by decide +kernel
private theorem grade_70 : grade 70 = 11 := by decide +kernel
private theorem grade_71 : grade 71 = 6 := by decide +kernel
private theorem grade_72 : grade 72 = 3 := by decide +kernel

private theorem grade_table (q : Fin 73) : grade q.val = gradeTable q := by
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

theorem prefix_bound : CJ0.prefixRank source 73 ≤ 130679 := by
  change (∑ q ∈ Finset.range 73, ∑ u ∈ Finset.range (74-q),
    (CJ0.blockMatrix source q ((u : ℤ)-21)).rank) ≤ _
  calc
    _ ≤ ∑ q ∈ Finset.range 73, ∑ u ∈ Finset.range (74-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 73, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade, total_eq_sum]
    _ = ∑ q : Fin 73, gradeTable q := Finset.sum_congr rfl fun q _ => grade_table q
    _ = 130679 := by decide +kernel

end CurveList179925Witness
