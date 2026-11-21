import ProximityPrize.SubmissionLower.KoalaScalarListDefs
import ProximityPrize.SubmissionLower.KoalaScalarListCells0
import ProximityPrize.SubmissionLower.KoalaScalarListCells1
import ProximityPrize.SubmissionLower.KoalaScalarListCells2
import ProximityPrize.SubmissionLower.KoalaScalarListCells3
import ProximityPrize.SubmissionLower.KoalaScalarListCells4
import ProximityPrize.SubmissionLower.KoalaScalarListCells5

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
open scoped BigOperators
open CJ1 (total total_eq_sum)

private def allowance_12 : ℕ → ℕ
  | 41 => 84
  | u => nominal 12 u

private theorem bound_12 (u : ℕ) :
    (CJ0.blockMatrix source 12 ((u : ℤ)-21)).rank ≤ allowance_12 u := by
  unfold allowance_12
  split
  · exact improved_12_41
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_13 : ℕ → ℕ
  | 40 => 92
  | u => nominal 13 u

private theorem bound_13 (u : ℕ) :
    (CJ0.blockMatrix source 13 ((u : ℤ)-21)).rank ≤ allowance_13 u := by
  unfold allowance_13
  split
  · exact improved_13_40
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_14 : ℕ → ℕ
  | 39 => 99
  | u => nominal 14 u

private theorem bound_14 (u : ℕ) :
    (CJ0.blockMatrix source 14 ((u : ℤ)-21)).rank ≤ allowance_14 u := by
  unfold allowance_14
  split
  · exact improved_14_39
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_15 : ℕ → ℕ
  | 38 => 105
  | u => nominal 15 u

private theorem bound_15 (u : ℕ) :
    (CJ0.blockMatrix source 15 ((u : ℤ)-21)).rank ≤ allowance_15 u := by
  unfold allowance_15
  split
  · exact improved_15_38
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_16 : ℕ → ℕ
  | 37 => 110
  | u => nominal 16 u

private theorem bound_16 (u : ℕ) :
    (CJ0.blockMatrix source 16 ((u : ℤ)-21)).rank ≤ allowance_16 u := by
  unfold allowance_16
  split
  · exact improved_16_37
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_17 : ℕ → ℕ
  | 36 => 114
  | u => nominal 17 u

private theorem bound_17 (u : ℕ) :
    (CJ0.blockMatrix source 17 ((u : ℤ)-21)).rank ≤ allowance_17 u := by
  unfold allowance_17
  split
  · exact improved_17_36
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_18 : ℕ → ℕ
  | 35 => 117
  | u => nominal 18 u

private theorem bound_18 (u : ℕ) :
    (CJ0.blockMatrix source 18 ((u : ℤ)-21)).rank ≤ allowance_18 u := by
  unfold allowance_18
  split
  · exact improved_18_35
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_19 : ℕ → ℕ
  | 34 => 119
  | u => nominal 19 u

private theorem bound_19 (u : ℕ) :
    (CJ0.blockMatrix source 19 ((u : ℤ)-21)).rank ≤ allowance_19 u := by
  unfold allowance_19
  split
  · exact improved_19_34
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_20 : ℕ → ℕ
  | 33 => 120
  | u => nominal 20 u

private theorem bound_20 (u : ℕ) :
    (CJ0.blockMatrix source 20 ((u : ℤ)-21)).rank ≤ allowance_20 u := by
  unfold allowance_20
  split
  · exact improved_20_33
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_21 : ℕ → ℕ
  | 32 => 120
  | u => nominal 21 u

private theorem bound_21 (u : ℕ) :
    (CJ0.blockMatrix source 21 ((u : ℤ)-21)).rank ≤ allowance_21 u := by
  unfold allowance_21
  split
  · exact improved_21_32
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_22 : ℕ → ℕ
  | 31 => 120
  | u => nominal 22 u

private theorem bound_22 (u : ℕ) :
    (CJ0.blockMatrix source 22 ((u : ℤ)-21)).rank ≤ allowance_22 u := by
  unfold allowance_22
  split
  · exact improved_22_31
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_23 : ℕ → ℕ
  | 30 => 120
  | u => nominal 23 u

private theorem bound_23 (u : ℕ) :
    (CJ0.blockMatrix source 23 ((u : ℤ)-21)).rank ≤ allowance_23 u := by
  unfold allowance_23
  split
  · exact improved_23_30
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_24 : ℕ → ℕ
  | 29 => 120
  | u => nominal 24 u

private theorem bound_24 (u : ℕ) :
    (CJ0.blockMatrix source 24 ((u : ℤ)-21)).rank ≤ allowance_24 u := by
  unfold allowance_24
  split
  · exact improved_24_29
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_25 : ℕ → ℕ
  | 28 => 120
  | u => nominal 25 u

private theorem bound_25 (u : ℕ) :
    (CJ0.blockMatrix source 25 ((u : ℤ)-21)).rank ≤ allowance_25 u := by
  unfold allowance_25
  split
  · exact improved_25_28
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_33 : ℕ → ℕ
  | 20 => 120
  | u => nominal 33 u

private theorem bound_33 (u : ℕ) :
    (CJ0.blockMatrix source 33 ((u : ℤ)-21)).rank ≤ allowance_33 u := by
  unfold allowance_33
  split
  · exact improved_33_20
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_34 : ℕ → ℕ
  | 19 => 120
  | u => nominal 34 u

private theorem bound_34 (u : ℕ) :
    (CJ0.blockMatrix source 34 ((u : ℤ)-21)).rank ≤ allowance_34 u := by
  unfold allowance_34
  split
  · exact improved_34_19
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_35 : ℕ → ℕ
  | 18 => 119
  | u => nominal 35 u

private theorem bound_35 (u : ℕ) :
    (CJ0.blockMatrix source 35 ((u : ℤ)-21)).rank ≤ allowance_35 u := by
  unfold allowance_35
  split
  · exact improved_35_18
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_36 : ℕ → ℕ
  | 17 => 118
  | u => nominal 36 u

private theorem bound_36 (u : ℕ) :
    (CJ0.blockMatrix source 36 ((u : ℤ)-21)).rank ≤ allowance_36 u := by
  unfold allowance_36
  split
  · exact improved_36_17
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_37 : ℕ → ℕ
  | 16 => 116
  | u => nominal 37 u

private theorem bound_37 (u : ℕ) :
    (CJ0.blockMatrix source 37 ((u : ℤ)-21)).rank ≤ allowance_37 u := by
  unfold allowance_37
  split
  · exact improved_37_16
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_38 : ℕ → ℕ
  | 15 => 114
  | 16 => 109
  | u => nominal 38 u

private theorem bound_38 (u : ℕ) :
    (CJ0.blockMatrix source 38 ((u : ℤ)-21)).rank ≤ allowance_38 u := by
  unfold allowance_38
  split
  · exact improved_38_15
  · exact improved_38_16
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_39 : ℕ → ℕ
  | 14 => 111
  | 15 => 108
  | u => nominal 39 u

private theorem bound_39 (u : ℕ) :
    (CJ0.blockMatrix source 39 ((u : ℤ)-21)).rank ≤ allowance_39 u := by
  unfold allowance_39
  split
  · exact improved_39_14
  · exact improved_39_15
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_40 : ℕ → ℕ
  | 13 => 108
  | 14 => 106
  | u => nominal 40 u

private theorem bound_40 (u : ℕ) :
    (CJ0.blockMatrix source 40 ((u : ℤ)-21)).rank ≤ allowance_40 u := by
  unfold allowance_40
  split
  · exact improved_40_13
  · exact improved_40_14
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_41 : ℕ → ℕ
  | 12 => 104
  | 13 => 104
  | 14 => 99
  | u => nominal 41 u

private theorem bound_41 (u : ℕ) :
    (CJ0.blockMatrix source 41 ((u : ℤ)-21)).rank ≤ allowance_41 u := by
  unfold allowance_41
  split
  · exact improved_41_12
  · exact improved_41_13
  · exact improved_41_14
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_42 : ℕ → ℕ
  | 12 => 101
  | 13 => 98
  | u => nominal 42 u

private theorem bound_42 (u : ℕ) :
    (CJ0.blockMatrix source 42 ((u : ℤ)-21)).rank ≤ allowance_42 u := by
  unfold allowance_42
  split
  · exact improved_42_12
  · exact improved_42_13
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_43 : ℕ → ℕ
  | 11 => 98
  | 12 => 96
  | u => nominal 43 u

private theorem bound_43 (u : ℕ) :
    (CJ0.blockMatrix source 43 ((u : ℤ)-21)).rank ≤ allowance_43 u := by
  unfold allowance_43
  split
  · exact improved_43_11
  · exact improved_43_12
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_44 : ℕ → ℕ
  | 11 => 94
  | 12 => 89
  | u => nominal 44 u

private theorem bound_44 (u : ℕ) :
    (CJ0.blockMatrix source 44 ((u : ℤ)-21)).rank ≤ allowance_44 u := by
  unfold allowance_44
  split
  · exact improved_44_11
  · exact improved_44_12
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_45 : ℕ → ℕ
  | 10 => 91
  | 11 => 88
  | u => nominal 45 u

private theorem bound_45 (u : ℕ) :
    (CJ0.blockMatrix source 45 ((u : ℤ)-21)).rank ≤ allowance_45 u := by
  unfold allowance_45
  split
  · exact improved_45_10
  · exact improved_45_11
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_46 : ℕ → ℕ
  | 10 => 86
  | u => nominal 46 u

private theorem bound_46 (u : ℕ) :
    (CJ0.blockMatrix source 46 ((u : ℤ)-21)).rank ≤ allowance_46 u := by
  unfold allowance_46
  split
  · exact improved_46_10
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_47 : ℕ → ℕ
  | 9 => 84
  | 10 => 80
  | u => nominal 47 u

private theorem bound_47 (u : ℕ) :
    (CJ0.blockMatrix source 47 ((u : ℤ)-21)).rank ≤ allowance_47 u := by
  unfold allowance_47
  split
  · exact improved_47_9
  · exact improved_47_10
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_48 : ℕ → ℕ
  | 9 => 79
  | u => nominal 48 u

private theorem bound_48 (u : ℕ) :
    (CJ0.blockMatrix source 48 ((u : ℤ)-21)).rank ≤ allowance_48 u := by
  unfold allowance_48
  split
  · exact improved_48_9
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_49 : ℕ → ℕ
  | 8 => 77
  | u => nominal 49 u

private theorem bound_49 (u : ℕ) :
    (CJ0.blockMatrix source 49 ((u : ℤ)-21)).rank ≤ allowance_49 u := by
  unfold allowance_49
  split
  · exact improved_49_8
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_50 : ℕ → ℕ
  | 8 => 71
  | u => nominal 50 u

private theorem bound_50 (u : ℕ) :
    (CJ0.blockMatrix source 50 ((u : ℤ)-21)).rank ≤ allowance_50 u := by
  unfold allowance_50
  split
  · exact improved_50_8
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_51 : ℕ → ℕ
  | 7 => 70
  | u => nominal 51 u

private theorem bound_51 (u : ℕ) :
    (CJ0.blockMatrix source 51 ((u : ℤ)-21)).rank ≤ allowance_51 u := by
  unfold allowance_51
  split
  · exact improved_51_7
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_53 : ℕ → ℕ
  | 6 => 62
  | u => nominal 53 u

private theorem bound_53 (u : ℕ) :
    (CJ0.blockMatrix source 53 ((u : ℤ)-21)).rank ≤ allowance_53 u := by
  unfold allowance_53
  split
  · exact improved_53_6
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_55 : ℕ → ℕ
  | 5 => 54
  | u => nominal 55 u

private theorem bound_55 (u : ℕ) :
    (CJ0.blockMatrix source 55 ((u : ℤ)-21)).rank ≤ allowance_55 u := by
  unfold allowance_55
  split
  · exact improved_55_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_56 : ℕ → ℕ
  | 5 => 48
  | u => nominal 56 u

private theorem bound_56 (u : ℕ) :
    (CJ0.blockMatrix source 56 ((u : ℤ)-21)).rank ≤ allowance_56 u := by
  unfold allowance_56
  split
  · exact improved_56_5
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_57 : ℕ → ℕ
  | 4 => 45
  | u => nominal 57 u

private theorem bound_57 (u : ℕ) :
    (CJ0.blockMatrix source 57 ((u : ℤ)-21)).rank ≤ allowance_57 u := by
  unfold allowance_57
  split
  · exact improved_57_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_58 : ℕ → ℕ
  | 4 => 40
  | u => nominal 58 u

private theorem bound_58 (u : ℕ) :
    (CJ0.blockMatrix source 58 ((u : ℤ)-21)).rank ≤ allowance_58 u := by
  unfold allowance_58
  split
  · exact improved_58_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_59 : ℕ → ℕ
  | 3 => 36
  | 4 => 35
  | u => nominal 59 u

private theorem bound_59 (u : ℕ) :
    (CJ0.blockMatrix source 59 ((u : ℤ)-21)).rank ≤ allowance_59 u := by
  unfold allowance_59
  split
  · exact improved_59_3
  · exact improved_59_4
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_60 : ℕ → ℕ
  | 3 => 32
  | u => nominal 60 u

private theorem bound_60 (u : ℕ) :
    (CJ0.blockMatrix source 60 ((u : ℤ)-21)).rank ≤ allowance_60 u := by
  unfold allowance_60
  split
  · exact improved_60_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_61 : ℕ → ℕ
  | 2 => 27
  | 3 => 28
  | u => nominal 61 u

private theorem bound_61 (u : ℕ) :
    (CJ0.blockMatrix source 61 ((u : ℤ)-21)).rank ≤ allowance_61 u := by
  unfold allowance_61
  split
  · exact improved_61_2
  · exact improved_61_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_62 : ℕ → ℕ
  | 2 => 24
  | 3 => 24
  | u => nominal 62 u

private theorem bound_62 (u : ℕ) :
    (CJ0.blockMatrix source 62 ((u : ℤ)-21)).rank ≤ allowance_62 u := by
  unfold allowance_62
  split
  · exact improved_62_2
  · exact improved_62_3
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_63 : ℕ → ℕ
  | 1 => 18
  | 2 => 21
  | u => nominal 63 u

private theorem bound_63 (u : ℕ) :
    (CJ0.blockMatrix source 63 ((u : ℤ)-21)).rank ≤ allowance_63 u := by
  unfold allowance_63
  split
  · exact improved_63_1
  · exact improved_63_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_64 : ℕ → ℕ
  | 1 => 16
  | 2 => 18
  | u => nominal 64 u

private theorem bound_64 (u : ℕ) :
    (CJ0.blockMatrix source 64 ((u : ℤ)-21)).rank ≤ allowance_64 u := by
  unfold allowance_64
  split
  · exact improved_64_1
  · exact improved_64_2
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
  · exact improved_65_0
  · exact improved_65_1
  · exact improved_65_2
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_66 : ℕ → ℕ
  | 0 => 8
  | 1 => 12
  | u => nominal 66 u

private theorem bound_66 (u : ℕ) :
    (CJ0.blockMatrix source 66 ((u : ℤ)-21)).rank ≤ allowance_66 u := by
  unfold allowance_66
  split
  · exact improved_66_0
  · exact improved_66_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_67 : ℕ → ℕ
  | 0 => 7
  | 1 => 10
  | u => nominal 67 u

private theorem bound_67 (u : ℕ) :
    (CJ0.blockMatrix source 67 ((u : ℤ)-21)).rank ≤ allowance_67 u := by
  unfold allowance_67
  split
  · exact improved_67_0
  · exact improved_67_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_68 : ℕ → ℕ
  | 0 => 6
  | 1 => 8
  | u => nominal 68 u

private theorem bound_68 (u : ℕ) :
    (CJ0.blockMatrix source 68 ((u : ℤ)-21)).rank ≤ allowance_68 u := by
  unfold allowance_68
  split
  · exact improved_68_0
  · exact improved_68_1
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_69 : ℕ → ℕ
  | 0 => 5
  | u => nominal 69 u

private theorem bound_69 (u : ℕ) :
    (CJ0.blockMatrix source 69 ((u : ℤ)-21)).rank ≤ allowance_69 u := by
  unfold allowance_69
  split
  · exact improved_69_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_70 : ℕ → ℕ
  | 0 => 4
  | u => nominal 70 u

private theorem bound_70 (u : ℕ) :
    (CJ0.blockMatrix source 70 ((u : ℤ)-21)).rank ≤ allowance_70 u := by
  unfold allowance_70
  split
  · exact improved_70_0
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def allowance_71 : ℕ → ℕ
  | 0 => 3
  | u => nominal 71 u

private theorem bound_71 (u : ℕ) :
    (CJ0.blockMatrix source 71 ((u : ℤ)-21)).rank ≤ allowance_71 u := by
  unfold allowance_71
  split
  · exact improved_71_0
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
  | 51, u => allowance_51 u
  | 53, u => allowance_53 u
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
  · exact bound_51 _
  · exact bound_53 _
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
private def gradeTable : Fin 73 → ℕ := ![53,156,306,500,735,1008,1316,1656,2025,2420,2795,3150,3485,3760,3978,4142,4255,4320,4340,4318,4257,4160,4030,3900,3770,3640,3511,3381,3251,3121,2991,2861,2731,2601,2473,2346,2221,2098,1977,1859,1744,1632,1524,1419,1318,1220,1127,1036,951,868,790,715,645,577,515,455,400,348,301,256,217,180,148,119,94,72,54,39,27,18,11,6,3]
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
private theorem grade_10 : grade 10 = 2795 := by decide +kernel
private theorem grade_11 : grade 11 = 3150 := by decide +kernel
private theorem grade_12 : grade 12 = 3485 := by decide +kernel
private theorem grade_13 : grade 13 = 3760 := by decide +kernel
private theorem grade_14 : grade 14 = 3978 := by decide +kernel
private theorem grade_15 : grade 15 = 4142 := by decide +kernel
private theorem grade_16 : grade 16 = 4255 := by decide +kernel
private theorem grade_17 : grade 17 = 4320 := by decide +kernel
private theorem grade_18 : grade 18 = 4340 := by decide +kernel
private theorem grade_19 : grade 19 = 4318 := by decide +kernel
private theorem grade_20 : grade 20 = 4257 := by decide +kernel
private theorem grade_21 : grade 21 = 4160 := by decide +kernel
private theorem grade_22 : grade 22 = 4030 := by decide +kernel
private theorem grade_23 : grade 23 = 3900 := by decide +kernel
private theorem grade_24 : grade 24 = 3770 := by decide +kernel
private theorem grade_25 : grade 25 = 3640 := by decide +kernel
private theorem grade_26 : grade 26 = 3511 := by decide +kernel
private theorem grade_27 : grade 27 = 3381 := by decide +kernel
private theorem grade_28 : grade 28 = 3251 := by decide +kernel
private theorem grade_29 : grade 29 = 3121 := by decide +kernel
private theorem grade_30 : grade 30 = 2991 := by decide +kernel
private theorem grade_31 : grade 31 = 2861 := by decide +kernel
private theorem grade_32 : grade 32 = 2731 := by decide +kernel
private theorem grade_33 : grade 33 = 2601 := by decide +kernel
private theorem grade_34 : grade 34 = 2473 := by decide +kernel
private theorem grade_35 : grade 35 = 2346 := by decide +kernel
private theorem grade_36 : grade 36 = 2221 := by decide +kernel
private theorem grade_37 : grade 37 = 2098 := by decide +kernel
private theorem grade_38 : grade 38 = 1977 := by decide +kernel
private theorem grade_39 : grade 39 = 1859 := by decide +kernel
private theorem grade_40 : grade 40 = 1744 := by decide +kernel
private theorem grade_41 : grade 41 = 1632 := by decide +kernel
private theorem grade_42 : grade 42 = 1524 := by decide +kernel
private theorem grade_43 : grade 43 = 1419 := by decide +kernel
private theorem grade_44 : grade 44 = 1318 := by decide +kernel
private theorem grade_45 : grade 45 = 1220 := by decide +kernel
private theorem grade_46 : grade 46 = 1127 := by decide +kernel
private theorem grade_47 : grade 47 = 1036 := by decide +kernel
private theorem grade_48 : grade 48 = 951 := by decide +kernel
private theorem grade_49 : grade 49 = 868 := by decide +kernel
private theorem grade_50 : grade 50 = 790 := by decide +kernel
private theorem grade_51 : grade 51 = 715 := by decide +kernel
private theorem grade_52 : grade 52 = 645 := by decide +kernel
private theorem grade_53 : grade 53 = 577 := by decide +kernel
private theorem grade_54 : grade 54 = 515 := by decide +kernel
private theorem grade_55 : grade 55 = 455 := by decide +kernel
private theorem grade_56 : grade 56 = 400 := by decide +kernel
private theorem grade_57 : grade 57 = 348 := by decide +kernel
private theorem grade_58 : grade 58 = 301 := by decide +kernel
private theorem grade_59 : grade 59 = 256 := by decide +kernel
private theorem grade_60 : grade 60 = 217 := by decide +kernel
private theorem grade_61 : grade 61 = 180 := by decide +kernel
private theorem grade_62 : grade 62 = 148 := by decide +kernel
private theorem grade_63 : grade 63 = 119 := by decide +kernel
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

theorem prefix_bound : CJ0.prefixRank source 73 ≤ 128726 := by
  change (∑ q ∈ Finset.range 73, ∑ u ∈ Finset.range (74-q),
    (CJ0.blockMatrix source q ((u : ℤ)-21)).rank) ≤ _
  calc
    _ ≤ ∑ q ∈ Finset.range 73, ∑ u ∈ Finset.range (74-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 73, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade, total_eq_sum]
    _ = ∑ q : Fin 73, gradeTable q := Finset.sum_congr rfl fun q _ => grade_table q
    _ = 128726 := by decide +kernel

end KoalaScalarListBank
