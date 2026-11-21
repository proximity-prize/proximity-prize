import ProximityPrize.SubmissionLower.CurveList179944StructuralRankCells0
import ProximityPrize.SubmissionLower.CurveList179944StructuralRankCells1
import ProximityPrize.SubmissionLower.CurveList179944StructuralRankCells2
import ProximityPrize.SubmissionLower.CurveList179944StructuralRankCells3
import ProximityPrize.SubmissionLower.CurveList179944StructuralRankCells4
import ProximityPrize.SubmissionLower.CurveList179944StructuralRankCells5
import ProximityPrize.SubmissionLower.CurveList179944StructuralRankCells6
import ProximityPrize.SubmissionLower.CurveList179944StructuralRankCells7

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace CurveList179944StructuralRank
open scoped BigOperators
open CJ1 (total total_eq_sum)

private def allowance_12 : ℕ → ℕ
  | 40 => 84
  | u => nominal 12 u

private theorem bound_12 (u : ℕ) :
    (CJ0.blockMatrix source 12 ((u : ℤ)-21)).rank ≤ allowance_12 u := by
  unfold allowance_12
  split
  · exact rank_12_40
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_13 : ℕ → ℕ
  | 39 => 92
  | u => nominal 13 u

private theorem bound_13 (u : ℕ) :
    (CJ0.blockMatrix source 13 ((u : ℤ)-21)).rank ≤ allowance_13 u := by
  unfold allowance_13
  split
  · exact rank_13_39
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_14 : ℕ → ℕ
  | 38 => 99
  | u => nominal 14 u

private theorem bound_14 (u : ℕ) :
    (CJ0.blockMatrix source 14 ((u : ℤ)-21)).rank ≤ allowance_14 u := by
  unfold allowance_14
  split
  · exact rank_14_38
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_15 : ℕ → ℕ
  | 37 => 105
  | u => nominal 15 u

private theorem bound_15 (u : ℕ) :
    (CJ0.blockMatrix source 15 ((u : ℤ)-21)).rank ≤ allowance_15 u := by
  unfold allowance_15
  split
  · exact rank_15_37
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_16 : ℕ → ℕ
  | 36 => 110
  | u => nominal 16 u

private theorem bound_16 (u : ℕ) :
    (CJ0.blockMatrix source 16 ((u : ℤ)-21)).rank ≤ allowance_16 u := by
  unfold allowance_16
  split
  · exact rank_16_36
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_17 : ℕ → ℕ
  | 35 => 114
  | u => nominal 17 u

private theorem bound_17 (u : ℕ) :
    (CJ0.blockMatrix source 17 ((u : ℤ)-21)).rank ≤ allowance_17 u := by
  unfold allowance_17
  split
  · exact rank_17_35
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_18 : ℕ → ℕ
  | 34 => 117
  | u => nominal 18 u

private theorem bound_18 (u : ℕ) :
    (CJ0.blockMatrix source 18 ((u : ℤ)-21)).rank ≤ allowance_18 u := by
  unfold allowance_18
  split
  · exact rank_18_34
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_19 : ℕ → ℕ
  | 33 => 119
  | u => nominal 19 u

private theorem bound_19 (u : ℕ) :
    (CJ0.blockMatrix source 19 ((u : ℤ)-21)).rank ≤ allowance_19 u := by
  unfold allowance_19
  split
  · exact rank_19_33
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_20 : ℕ → ℕ
  | 32 => 120
  | u => nominal 20 u

private theorem bound_20 (u : ℕ) :
    (CJ0.blockMatrix source 20 ((u : ℤ)-21)).rank ≤ allowance_20 u := by
  unfold allowance_20
  split
  · exact rank_20_32
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_21 : ℕ → ℕ
  | 31 => 120
  | u => nominal 21 u

private theorem bound_21 (u : ℕ) :
    (CJ0.blockMatrix source 21 ((u : ℤ)-21)).rank ≤ allowance_21 u := by
  unfold allowance_21
  split
  · exact rank_21_31
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_22 : ℕ → ℕ
  | 30 => 120
  | u => nominal 22 u

private theorem bound_22 (u : ℕ) :
    (CJ0.blockMatrix source 22 ((u : ℤ)-21)).rank ≤ allowance_22 u := by
  unfold allowance_22
  split
  · exact rank_22_30
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_23 : ℕ → ℕ
  | 29 => 120
  | u => nominal 23 u

private theorem bound_23 (u : ℕ) :
    (CJ0.blockMatrix source 23 ((u : ℤ)-21)).rank ≤ allowance_23 u := by
  unfold allowance_23
  split
  · exact rank_23_29
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_24 : ℕ → ℕ
  | 28 => 120
  | u => nominal 24 u

private theorem bound_24 (u : ℕ) :
    (CJ0.blockMatrix source 24 ((u : ℤ)-21)).rank ≤ allowance_24 u := by
  unfold allowance_24
  split
  · exact rank_24_28
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_25 : ℕ → ℕ
  | 27 => 120
  | u => nominal 25 u

private theorem bound_25 (u : ℕ) :
    (CJ0.blockMatrix source 25 ((u : ℤ)-21)).rank ≤ allowance_25 u := by
  unfold allowance_25
  split
  · exact rank_25_27
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_26 : ℕ → ℕ
  | 26 => 120
  | u => nominal 26 u

private theorem bound_26 (u : ℕ) :
    (CJ0.blockMatrix source 26 ((u : ℤ)-21)).rank ≤ allowance_26 u := by
  unfold allowance_26
  split
  · exact rank_26_26
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_27 : ℕ → ℕ
  | 25 => 120
  | u => nominal 27 u

private theorem bound_27 (u : ℕ) :
    (CJ0.blockMatrix source 27 ((u : ℤ)-21)).rank ≤ allowance_27 u := by
  unfold allowance_27
  split
  · exact rank_27_25
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_28 : ℕ → ℕ
  | 24 => 120
  | u => nominal 28 u

private theorem bound_28 (u : ℕ) :
    (CJ0.blockMatrix source 28 ((u : ℤ)-21)).rank ≤ allowance_28 u := by
  unfold allowance_28
  split
  · exact rank_28_24
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_29 : ℕ → ℕ
  | 23 => 120
  | u => nominal 29 u

private theorem bound_29 (u : ℕ) :
    (CJ0.blockMatrix source 29 ((u : ℤ)-21)).rank ≤ allowance_29 u := by
  unfold allowance_29
  split
  · exact rank_29_23
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_30 : ℕ → ℕ
  | 22 => 120
  | u => nominal 30 u

private theorem bound_30 (u : ℕ) :
    (CJ0.blockMatrix source 30 ((u : ℤ)-21)).rank ≤ allowance_30 u := by
  unfold allowance_30
  split
  · exact rank_30_22
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_31 : ℕ → ℕ
  | 21 => 120
  | u => nominal 31 u

private theorem bound_31 (u : ℕ) :
    (CJ0.blockMatrix source 31 ((u : ℤ)-21)).rank ≤ allowance_31 u := by
  unfold allowance_31
  split
  · exact rank_31_21
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_32 : ℕ → ℕ
  | 20 => 120
  | u => nominal 32 u

private theorem bound_32 (u : ℕ) :
    (CJ0.blockMatrix source 32 ((u : ℤ)-21)).rank ≤ allowance_32 u := by
  unfold allowance_32
  split
  · exact rank_32_20
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_33 : ℕ → ℕ
  | 19 => 120
  | u => nominal 33 u

private theorem bound_33 (u : ℕ) :
    (CJ0.blockMatrix source 33 ((u : ℤ)-21)).rank ≤ allowance_33 u := by
  unfold allowance_33
  split
  · exact rank_33_19
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_34 : ℕ → ℕ
  | 18 => 119
  | u => nominal 34 u

private theorem bound_34 (u : ℕ) :
    (CJ0.blockMatrix source 34 ((u : ℤ)-21)).rank ≤ allowance_34 u := by
  unfold allowance_34
  split
  · exact rank_34_18
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_35 : ℕ → ℕ
  | 17 => 118
  | u => nominal 35 u

private theorem bound_35 (u : ℕ) :
    (CJ0.blockMatrix source 35 ((u : ℤ)-21)).rank ≤ allowance_35 u := by
  unfold allowance_35
  split
  · exact rank_35_17
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_36 : ℕ → ℕ
  | 16 => 116
  | u => nominal 36 u

private theorem bound_36 (u : ℕ) :
    (CJ0.blockMatrix source 36 ((u : ℤ)-21)).rank ≤ allowance_36 u := by
  unfold allowance_36
  split
  · exact rank_36_16
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_37 : ℕ → ℕ
  | 15 => 114
  | 16 => 109
  | u => nominal 37 u

private theorem bound_37 (u : ℕ) :
    (CJ0.blockMatrix source 37 ((u : ℤ)-21)).rank ≤ allowance_37 u := by
  unfold allowance_37
  split
  · exact rank_37_15
  · exact rank_37_16
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_38 : ℕ → ℕ
  | 14 => 111
  | 15 => 108
  | u => nominal 38 u

private theorem bound_38 (u : ℕ) :
    (CJ0.blockMatrix source 38 ((u : ℤ)-21)).rank ≤ allowance_38 u := by
  unfold allowance_38
  split
  · exact rank_38_14
  · exact rank_38_15
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_39 : ℕ → ℕ
  | 13 => 108
  | 14 => 106
  | u => nominal 39 u

private theorem bound_39 (u : ℕ) :
    (CJ0.blockMatrix source 39 ((u : ℤ)-21)).rank ≤ allowance_39 u := by
  unfold allowance_39
  split
  · exact rank_39_13
  · exact rank_39_14
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_40 : ℕ → ℕ
  | 12 => 104
  | 13 => 104
  | 14 => 99
  | u => nominal 40 u

private theorem bound_40 (u : ℕ) :
    (CJ0.blockMatrix source 40 ((u : ℤ)-21)).rank ≤ allowance_40 u := by
  unfold allowance_40
  split
  · exact rank_40_12
  · exact rank_40_13
  · exact rank_40_14
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_41 : ℕ → ℕ
  | 12 => 101
  | 13 => 98
  | u => nominal 41 u

private theorem bound_41 (u : ℕ) :
    (CJ0.blockMatrix source 41 ((u : ℤ)-21)).rank ≤ allowance_41 u := by
  unfold allowance_41
  split
  · exact rank_41_12
  · exact rank_41_13
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_42 : ℕ → ℕ
  | 11 => 98
  | 12 => 96
  | u => nominal 42 u

private theorem bound_42 (u : ℕ) :
    (CJ0.blockMatrix source 42 ((u : ℤ)-21)).rank ≤ allowance_42 u := by
  unfold allowance_42
  split
  · exact rank_42_11
  · exact rank_42_12
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_43 : ℕ → ℕ
  | 11 => 94
  | 12 => 89
  | u => nominal 43 u

private theorem bound_43 (u : ℕ) :
    (CJ0.blockMatrix source 43 ((u : ℤ)-21)).rank ≤ allowance_43 u := by
  unfold allowance_43
  split
  · exact rank_43_11
  · exact rank_43_12
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_44 : ℕ → ℕ
  | 10 => 91
  | 11 => 88
  | u => nominal 44 u

private theorem bound_44 (u : ℕ) :
    (CJ0.blockMatrix source 44 ((u : ℤ)-21)).rank ≤ allowance_44 u := by
  unfold allowance_44
  split
  · exact rank_44_10
  · exact rank_44_11
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_45 : ℕ → ℕ
  | 10 => 86
  | u => nominal 45 u

private theorem bound_45 (u : ℕ) :
    (CJ0.blockMatrix source 45 ((u : ℤ)-21)).rank ≤ allowance_45 u := by
  unfold allowance_45
  split
  · exact rank_45_10
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_46 : ℕ → ℕ
  | 9 => 84
  | 10 => 80
  | u => nominal 46 u

private theorem bound_46 (u : ℕ) :
    (CJ0.blockMatrix source 46 ((u : ℤ)-21)).rank ≤ allowance_46 u := by
  unfold allowance_46
  split
  · exact rank_46_9
  · exact rank_46_10
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_47 : ℕ → ℕ
  | 9 => 79
  | u => nominal 47 u

private theorem bound_47 (u : ℕ) :
    (CJ0.blockMatrix source 47 ((u : ℤ)-21)).rank ≤ allowance_47 u := by
  unfold allowance_47
  split
  · exact rank_47_9
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_48 : ℕ → ℕ
  | 8 => 77
  | u => nominal 48 u

private theorem bound_48 (u : ℕ) :
    (CJ0.blockMatrix source 48 ((u : ℤ)-21)).rank ≤ allowance_48 u := by
  unfold allowance_48
  split
  · exact rank_48_8
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_49 : ℕ → ℕ
  | 8 => 71
  | u => nominal 49 u

private theorem bound_49 (u : ℕ) :
    (CJ0.blockMatrix source 49 ((u : ℤ)-21)).rank ≤ allowance_49 u := by
  unfold allowance_49
  split
  · exact rank_49_8
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_50 : ℕ → ℕ
  | 7 => 70
  | u => nominal 50 u

private theorem bound_50 (u : ℕ) :
    (CJ0.blockMatrix source 50 ((u : ℤ)-21)).rank ≤ allowance_50 u := by
  unfold allowance_50
  split
  · exact rank_50_7
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_52 : ℕ → ℕ
  | 6 => 62
  | u => nominal 52 u

private theorem bound_52 (u : ℕ) :
    (CJ0.blockMatrix source 52 ((u : ℤ)-21)).rank ≤ allowance_52 u := by
  unfold allowance_52
  split
  · exact rank_52_6
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_54 : ℕ → ℕ
  | 5 => 54
  | u => nominal 54 u

private theorem bound_54 (u : ℕ) :
    (CJ0.blockMatrix source 54 ((u : ℤ)-21)).rank ≤ allowance_54 u := by
  unfold allowance_54
  split
  · exact rank_54_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_55 : ℕ → ℕ
  | 5 => 48
  | u => nominal 55 u

private theorem bound_55 (u : ℕ) :
    (CJ0.blockMatrix source 55 ((u : ℤ)-21)).rank ≤ allowance_55 u := by
  unfold allowance_55
  split
  · exact rank_55_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_56 : ℕ → ℕ
  | 4 => 45
  | u => nominal 56 u

private theorem bound_56 (u : ℕ) :
    (CJ0.blockMatrix source 56 ((u : ℤ)-21)).rank ≤ allowance_56 u := by
  unfold allowance_56
  split
  · exact rank_56_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_57 : ℕ → ℕ
  | 4 => 40
  | u => nominal 57 u

private theorem bound_57 (u : ℕ) :
    (CJ0.blockMatrix source 57 ((u : ℤ)-21)).rank ≤ allowance_57 u := by
  unfold allowance_57
  split
  · exact rank_57_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_58 : ℕ → ℕ
  | 3 => 36
  | 4 => 35
  | u => nominal 58 u

private theorem bound_58 (u : ℕ) :
    (CJ0.blockMatrix source 58 ((u : ℤ)-21)).rank ≤ allowance_58 u := by
  unfold allowance_58
  split
  · exact rank_58_3
  · exact rank_58_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_59 : ℕ → ℕ
  | 3 => 32
  | u => nominal 59 u

private theorem bound_59 (u : ℕ) :
    (CJ0.blockMatrix source 59 ((u : ℤ)-21)).rank ≤ allowance_59 u := by
  unfold allowance_59
  split
  · exact rank_59_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_60 : ℕ → ℕ
  | 2 => 27
  | 3 => 28
  | u => nominal 60 u

private theorem bound_60 (u : ℕ) :
    (CJ0.blockMatrix source 60 ((u : ℤ)-21)).rank ≤ allowance_60 u := by
  unfold allowance_60
  split
  · exact rank_60_2
  · exact rank_60_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_61 : ℕ → ℕ
  | 2 => 24
  | 3 => 24
  | u => nominal 61 u

private theorem bound_61 (u : ℕ) :
    (CJ0.blockMatrix source 61 ((u : ℤ)-21)).rank ≤ allowance_61 u := by
  unfold allowance_61
  split
  · exact rank_61_2
  · exact rank_61_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_62 : ℕ → ℕ
  | 1 => 18
  | 2 => 21
  | u => nominal 62 u

private theorem bound_62 (u : ℕ) :
    (CJ0.blockMatrix source 62 ((u : ℤ)-21)).rank ≤ allowance_62 u := by
  unfold allowance_62
  split
  · exact rank_62_1
  · exact rank_62_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_63 : ℕ → ℕ
  | 1 => 16
  | 2 => 18
  | u => nominal 63 u

private theorem bound_63 (u : ℕ) :
    (CJ0.blockMatrix source 63 ((u : ℤ)-21)).rank ≤ allowance_63 u := by
  unfold allowance_63
  split
  · exact rank_63_1
  · exact rank_63_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_64 : ℕ → ℕ
  | 0 => 9
  | 1 => 14
  | 2 => 15
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
  | 0 => 8
  | 1 => 12
  | u => nominal 65 u

private theorem bound_65 (u : ℕ) :
    (CJ0.blockMatrix source 65 ((u : ℤ)-21)).rank ≤ allowance_65 u := by
  unfold allowance_65
  split
  · exact rank_65_0
  · exact rank_65_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_66 : ℕ → ℕ
  | 0 => 7
  | 1 => 10
  | u => nominal 66 u

private theorem bound_66 (u : ℕ) :
    (CJ0.blockMatrix source 66 ((u : ℤ)-21)).rank ≤ allowance_66 u := by
  unfold allowance_66
  split
  · exact rank_66_0
  · exact rank_66_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_67 : ℕ → ℕ
  | 0 => 6
  | 1 => 8
  | u => nominal 67 u

private theorem bound_67 (u : ℕ) :
    (CJ0.blockMatrix source 67 ((u : ℤ)-21)).rank ≤ allowance_67 u := by
  unfold allowance_67
  split
  · exact rank_67_0
  · exact rank_67_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_68 : ℕ → ℕ
  | 0 => 5
  | u => nominal 68 u

private theorem bound_68 (u : ℕ) :
    (CJ0.blockMatrix source 68 ((u : ℤ)-21)).rank ≤ allowance_68 u := by
  unfold allowance_68
  split
  · exact rank_68_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_69 : ℕ → ℕ
  | 0 => 4
  | u => nominal 69 u

private theorem bound_69 (u : ℕ) :
    (CJ0.blockMatrix source 69 ((u : ℤ)-21)).rank ≤ allowance_69 u := by
  unfold allowance_69
  split
  · exact rank_69_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_70 : ℕ → ℕ
  | 0 => 3
  | u => nominal 70 u

private theorem bound_70 (u : ℕ) :
    (CJ0.blockMatrix source 70 ((u : ℤ)-21)).rank ≤ allowance_70 u := by
  unfold allowance_70
  split
  · exact rank_70_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance : ℕ → ℕ → ℕ
  | 12, u => allowance_12 u
  | 13, u => allowance_13 u
  | 14, u => allowance_14 u
  | 15, u => allowance_15 u
  | 16, u => allowance_16 u
  | 17, u => allowance_17 u
  | 18, u => allowance_18 u
  | 19, u => allowance_19 u
  | 20, u => allowance_20 u
  | 21, u => allowance_21 u
  | 22, u => allowance_22 u
  | 23, u => allowance_23 u
  | 24, u => allowance_24 u
  | 25, u => allowance_25 u
  | 26, u => allowance_26 u
  | 27, u => allowance_27 u
  | 28, u => allowance_28 u
  | 29, u => allowance_29 u
  | 30, u => allowance_30 u
  | 31, u => allowance_31 u
  | 32, u => allowance_32 u
  | 33, u => allowance_33 u
  | 34, u => allowance_34 u
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
  | 52, u => allowance_52 u
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
  | q, u => nominal q u

private theorem bound (q u : ℕ) :
    (CJ0.blockMatrix source q ((u : ℤ)-21)).rank ≤ allowance q u := by
  unfold allowance
  split
  · exact bound_12 _
  · exact bound_13 _
  · exact bound_14 _
  · exact bound_15 _
  · exact bound_16 _
  · exact bound_17 _
  · exact bound_18 _
  · exact bound_19 _
  · exact bound_20 _
  · exact bound_21 _
  · exact bound_22 _
  · exact bound_23 _
  · exact bound_24 _
  · exact bound_25 _
  · exact bound_26 _
  · exact bound_27 _
  · exact bound_28 _
  · exact bound_29 _
  · exact bound_30 _
  · exact bound_31 _
  · exact bound_32 _
  · exact bound_33 _
  · exact bound_34 _
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
  · exact bound_52 _
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
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def grade (q : ℕ) := total (allowance q) (73-q)
private def gradeTable : Fin 72 → ℕ := ![52, 153, 300, 490, 720, 987, 1288, 1620, 1980, 2365, 2730, 3075, 3400, 3666, 3876, 4033, 4140, 4200, 4216, 4191, 4128, 4030, 3900, 3770, 3640, 3510, 3380, 3250, 3120, 2990, 2860, 2730, 2601, 2473, 2346, 2221, 2098, 1977, 1859, 1744, 1632, 1524, 1419, 1318, 1220, 1127, 1036, 951, 868, 790, 715, 645, 577, 515, 455, 400, 348, 301, 256, 217, 180, 148, 119, 94, 72, 54, 39, 27, 18, 11, 6, 3]
private theorem grade_0 : grade 0 = 52 := by decide +kernel
private theorem grade_1 : grade 1 = 153 := by decide +kernel
private theorem grade_2 : grade 2 = 300 := by decide +kernel
private theorem grade_3 : grade 3 = 490 := by decide +kernel
private theorem grade_4 : grade 4 = 720 := by decide +kernel
private theorem grade_5 : grade 5 = 987 := by decide +kernel
private theorem grade_6 : grade 6 = 1288 := by decide +kernel
private theorem grade_7 : grade 7 = 1620 := by decide +kernel
private theorem grade_8 : grade 8 = 1980 := by decide +kernel
private theorem grade_9 : grade 9 = 2365 := by decide +kernel
private theorem grade_10 : grade 10 = 2730 := by decide +kernel
private theorem grade_11 : grade 11 = 3075 := by decide +kernel
private theorem grade_12 : grade 12 = 3400 := by decide +kernel
private theorem grade_13 : grade 13 = 3666 := by decide +kernel
private theorem grade_14 : grade 14 = 3876 := by decide +kernel
private theorem grade_15 : grade 15 = 4033 := by decide +kernel
private theorem grade_16 : grade 16 = 4140 := by decide +kernel
private theorem grade_17 : grade 17 = 4200 := by decide +kernel
private theorem grade_18 : grade 18 = 4216 := by decide +kernel
private theorem grade_19 : grade 19 = 4191 := by decide +kernel
private theorem grade_20 : grade 20 = 4128 := by decide +kernel
private theorem grade_21 : grade 21 = 4030 := by decide +kernel
private theorem grade_22 : grade 22 = 3900 := by decide +kernel
private theorem grade_23 : grade 23 = 3770 := by decide +kernel
private theorem grade_24 : grade 24 = 3640 := by decide +kernel
private theorem grade_25 : grade 25 = 3510 := by decide +kernel
private theorem grade_26 : grade 26 = 3380 := by decide +kernel
private theorem grade_27 : grade 27 = 3250 := by decide +kernel
private theorem grade_28 : grade 28 = 3120 := by decide +kernel
private theorem grade_29 : grade 29 = 2990 := by decide +kernel
private theorem grade_30 : grade 30 = 2860 := by decide +kernel
private theorem grade_31 : grade 31 = 2730 := by decide +kernel
private theorem grade_32 : grade 32 = 2601 := by decide +kernel
private theorem grade_33 : grade 33 = 2473 := by decide +kernel
private theorem grade_34 : grade 34 = 2346 := by decide +kernel
private theorem grade_35 : grade 35 = 2221 := by decide +kernel
private theorem grade_36 : grade 36 = 2098 := by decide +kernel
private theorem grade_37 : grade 37 = 1977 := by decide +kernel
private theorem grade_38 : grade 38 = 1859 := by decide +kernel
private theorem grade_39 : grade 39 = 1744 := by decide +kernel
private theorem grade_40 : grade 40 = 1632 := by decide +kernel
private theorem grade_41 : grade 41 = 1524 := by decide +kernel
private theorem grade_42 : grade 42 = 1419 := by decide +kernel
private theorem grade_43 : grade 43 = 1318 := by decide +kernel
private theorem grade_44 : grade 44 = 1220 := by decide +kernel
private theorem grade_45 : grade 45 = 1127 := by decide +kernel
private theorem grade_46 : grade 46 = 1036 := by decide +kernel
private theorem grade_47 : grade 47 = 951 := by decide +kernel
private theorem grade_48 : grade 48 = 868 := by decide +kernel
private theorem grade_49 : grade 49 = 790 := by decide +kernel
private theorem grade_50 : grade 50 = 715 := by decide +kernel
private theorem grade_51 : grade 51 = 645 := by decide +kernel
private theorem grade_52 : grade 52 = 577 := by decide +kernel
private theorem grade_53 : grade 53 = 515 := by decide +kernel
private theorem grade_54 : grade 54 = 455 := by decide +kernel
private theorem grade_55 : grade 55 = 400 := by decide +kernel
private theorem grade_56 : grade 56 = 348 := by decide +kernel
private theorem grade_57 : grade 57 = 301 := by decide +kernel
private theorem grade_58 : grade 58 = 256 := by decide +kernel
private theorem grade_59 : grade 59 = 217 := by decide +kernel
private theorem grade_60 : grade 60 = 180 := by decide +kernel
private theorem grade_61 : grade 61 = 148 := by decide +kernel
private theorem grade_62 : grade 62 = 119 := by decide +kernel
private theorem grade_63 : grade 63 = 94 := by decide +kernel
private theorem grade_64 : grade 64 = 72 := by decide +kernel
private theorem grade_65 : grade 65 = 54 := by decide +kernel
private theorem grade_66 : grade 66 = 39 := by decide +kernel
private theorem grade_67 : grade 67 = 27 := by decide +kernel
private theorem grade_68 : grade 68 = 18 := by decide +kernel
private theorem grade_69 : grade 69 = 11 := by decide +kernel
private theorem grade_70 : grade 70 = 6 := by decide +kernel
private theorem grade_71 : grade 71 = 3 := by decide +kernel

private theorem grade_table (q : Fin 72) : grade q.val = gradeTable q := by
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

theorem prefix_bound : CJ0.prefixRank source 72 ≤ 123194 := by
  change (∑ q ∈ Finset.range 72, ∑ u ∈ Finset.range (73-q),
    (CJ0.blockMatrix source q ((u : ℤ)-21)).rank) ≤ _
  calc
    _ ≤ ∑ q ∈ Finset.range 72, ∑ u ∈ Finset.range (73-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 72, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade, total_eq_sum]
    _ = ∑ q : Fin 72, gradeTable q := Finset.sum_congr rfl fun q _ => grade_table q
    _ = 123194 := by decide +kernel

end CurveList179944StructuralRank
