import ProximityPrize.SubmissionLower.Bundle6970_a1fecc36884a8483
import ProximityPrize.SubmissionLower.Bundle6970_a1fecc36884a8483
import ProximityPrize.SubmissionLower.Bundle6970_a1fecc36884a8483
import ProximityPrize.SubmissionLower.Bundle6970_a1fecc36884a8483

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
namespace R6970Scalar84Rank
open CJ0 (Surplus RankCertificate)
open CJ1 (total total_eq_sum)
open Finset
open scoped BigOperators

theorem surplus : Surplus 179730 source 253996 := by
  obtain ⟨hT, hQ, hV⟩ := moments
  unfold Surplus
  rw [hT, hQ, hV]
  exact (by decide : 262144*253996+131071*667280 < 62*179730*13824+228784)

private def allowance : ℕ → ℕ → ℕ
  | 14, 49 => 113
  | 15, 47 => 125
  | 15, 48 => 123
  | 16, 46 => 135
  | 16, 47 => 132
  | 17, 45 => 144
  | 17, 46 => 140
  | 18, 44 => 152
  | 18, 45 => 147
  | 19, 43 => 159
  | 19, 44 => 153
  | 20, 42 => 165
  | 20, 43 => 158
  | 21, 41 => 170
  | 21, 42 => 162
  | 22, 40 => 174
  | 22, 41 => 165
  | 23, 39 => 177
  | 23, 40 => 167
  | 24, 38 => 179
  | 24, 39 => 168
  | 25, 37 => 180
  | 25, 38 => 168
  | 26, 36 => 180
  | 26, 37 => 168
  | 27, 35 => 180
  | 27, 36 => 168
  | 28, 34 => 180
  | 28, 35 => 168
  | 29, 33 => 180
  | 29, 34 => 168
  | 30, 32 => 180
  | 30, 33 => 168
  | 31, 31 => 180
  | 31, 32 => 168
  | 32, 30 => 180
  | 32, 31 => 168
  | 33, 29 => 180
  | 33, 30 => 168
  | 34, 28 => 180
  | 34, 29 => 168
  | 35, 27 => 180
  | 35, 28 => 168
  | 36, 26 => 180
  | 36, 27 => 168
  | 37, 25 => 180
  | 37, 26 => 168
  | 38, 24 => 180
  | 38, 25 => 168
  | 39, 23 => 180
  | 39, 24 => 168
  | 40, 22 => 180
  | 40, 23 => 168
  | 41, 21 => 180
  | 41, 22 => 168
  | 42, 20 => 174
  | 42, 21 => 168
  | 43, 19 => 171
  | 43, 20 => 168
  | 44, 18 => 168
  | 44, 19 => 168
  | 45, 17 => 164
  | 45, 18 => 168
  | 46, 16 => 160
  | 46, 17 => 159
  | 46, 18 => 154
  | 47, 16 => 156
  | 47, 17 => 152
  | 48, 15 => 152
  | 48, 16 => 150
  | 49, 14 => 148
  | 49, 15 => 147
  | 49, 16 => 142
  | 50, 14 => 144
  | 50, 15 => 140
  | 51, 13 => 140
  | 51, 14 => 138
  | 52, 13 => 135
  | 52, 14 => 130
  | 53, 12 => 132
  | 53, 13 => 128
  | 54, 12 => 126
  | 55, 11 => 123
  | 55, 12 => 119
  | 56, 11 => 117
  | 57, 10 => 115
  | 57, 11 => 109
  | 58, 10 => 108
  | 59, 9 => 106
  | 60, 9 => 99
  | 61, 8 => 97
  | 63, 7 => 88
  | 64, 7 => 80
  | 65, 6 => 77
  | 66, 6 => 70
  | 67, 5 => 66
  | 67, 6 => 63
  | 68, 5 => 60
  | 69, 4 => 55
  | 69, 5 => 54
  | 70, 4 => 50
  | 70, 5 => 48
  | 71, 3 => 44
  | 71, 4 => 45
  | 72, 3 => 40
  | 72, 4 => 40
  | 73, 2 => 33
  | 73, 3 => 36
  | 73, 4 => 35
  | 74, 2 => 30
  | 74, 3 => 32
  | 75, 1 => 22
  | 75, 2 => 27
  | 75, 3 => 28
  | 76, 1 => 20
  | 76, 2 => 24
  | 76, 3 => 24
  | 77, 0 => 11
  | 77, 1 => 18
  | 77, 2 => 21
  | 78, 0 => 10
  | 78, 1 => 16
  | 78, 2 => 18
  | 79, 0 => 9
  | 79, 1 => 14
  | 79, 2 => 15
  | 80, 0 => 8
  | 80, 1 => 12
  | 81, 0 => 7
  | 81, 1 => 10
  | 82, 0 => 6
  | 82, 1 => 8
  | 83, 0 => 5
  | 84, 0 => 4
  | q, u => nominal q u

private theorem bound (q u : ℕ) : (CJ0.blockMatrix source q ((u : ℤ)-26)).rank ≤ allowance q u := by
  unfold allowance
  split
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 14 49 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 15 47 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 15 48 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 16 46 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 16 47 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 17 45 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 17 46 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 18 44 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 18 45 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 19 43 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 19 44 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 20 42 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 20 43 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 21 41 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 21 42 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 22 40 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 22 41 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 23 39 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 23 40 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 24 38 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 24 39 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 25 37 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 25 38 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 26 36 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 26 37 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 27 35 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 27 36 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 28 34 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 28 35 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 29 33 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 29 34 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 30 32 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 30 33 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 31 31 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 31 32 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 32 30 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 32 31 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 33 29 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 33 30 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 34 28 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 34 29 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 35 27 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 35 28 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 36 26 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 36 27 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 37 25 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 37 26 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 38 24 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 38 25 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 39 23 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 39 24 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 40 22 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 40 23 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 41 21 (by decide)).trans (by decide +kernel)
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 41 22 (by decide)).trans (by decide +kernel)
  · exact rank_42_20
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 42 21 (by decide)).trans (by decide +kernel)
  · exact rank_43_19
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 43 20 (by decide)).trans (by decide +kernel)
  · exact rank_44_18
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 44 19 (by decide)).trans (by decide +kernel)
  · exact rank_45_17
  · exact (Beyond70Slice.block_rank_le_slices_nat source native_shape 45 18 (by decide)).trans (by decide +kernel)
  · exact rank_46_16
  · exact rank_46_17
  · exact rank_46_18
  · exact rank_47_16
  · exact rank_47_17
  · exact rank_48_15
  · exact rank_48_16
  · exact rank_49_14
  · exact rank_49_15
  · exact rank_49_16
  · exact rank_50_14
  · exact rank_50_15
  · exact rank_51_13
  · exact rank_51_14
  · exact rank_52_13
  · exact rank_52_14
  · exact rank_53_12
  · exact rank_53_13
  · exact rank_54_12
  · exact rank_55_11
  · exact rank_55_12
  · exact rank_56_11
  · exact rank_57_10
  · exact rank_57_11
  · exact rank_58_10
  · exact rank_59_9
  · exact rank_60_9
  · exact rank_61_8
  · exact (block_rank_le 63 7).trans ((rank_le_cut 63 7 2).trans (by decide +kernel))
  · exact (block_rank_le 64 7).trans ((rank_le_cut 64 7 1).trans (by decide +kernel))
  · exact (block_rank_le 65 6).trans ((rank_le_cut 65 6 3).trans (by decide +kernel))
  · exact (block_rank_le 66 6).trans ((rank_le_cut 66 6 2).trans (by decide +kernel))
  · exact (block_rank_le 67 5).trans ((rank_le_cut 67 5 4).trans (by decide +kernel))
  · exact (block_rank_le 67 6).trans ((rank_le_cut 67 6 1).trans (by decide +kernel))
  · exact (block_rank_le 68 5).trans ((rank_le_cut 68 5 3).trans (by decide +kernel))
  · exact (block_rank_le 69 4).trans ((rank_le_cut 69 4 5).trans (by decide +kernel))
  · exact (block_rank_le 69 5).trans ((rank_le_cut 69 5 2).trans (by decide +kernel))
  · exact (block_rank_le 70 4).trans ((rank_le_cut 70 4 4).trans (by decide +kernel))
  · exact (block_rank_le 70 5).trans ((rank_le_cut 70 5 1).trans (by decide +kernel))
  · exact (block_rank_le 71 3).trans ((rank_le_cut 71 3 6).trans (by decide +kernel))
  · exact (block_rank_le 71 4).trans ((rank_le_cut 71 4 3).trans (by decide +kernel))
  · exact (block_rank_le 72 3).trans ((rank_le_cut 72 3 5).trans (by decide +kernel))
  · exact (block_rank_le 72 4).trans ((rank_le_cut 72 4 2).trans (by decide +kernel))
  · exact (block_rank_le 73 2).trans ((rank_le_cut 73 2 7).trans (by decide +kernel))
  · exact (block_rank_le 73 3).trans ((rank_le_cut 73 3 4).trans (by decide +kernel))
  · exact (block_rank_le 73 4).trans ((rank_le_cut 73 4 1).trans (by decide +kernel))
  · exact (block_rank_le 74 2).trans ((rank_le_cut 74 2 6).trans (by decide +kernel))
  · exact (block_rank_le 74 3).trans ((rank_le_cut 74 3 3).trans (by decide +kernel))
  · exact (block_rank_le 75 1).trans ((rank_le_cut 75 1 8).trans (by decide +kernel))
  · exact (block_rank_le 75 2).trans ((rank_le_cut 75 2 5).trans (by decide +kernel))
  · exact (block_rank_le 75 3).trans ((rank_le_cut 75 3 2).trans (by decide +kernel))
  · exact (block_rank_le 76 1).trans ((rank_le_cut 76 1 7).trans (by decide +kernel))
  · exact (block_rank_le 76 2).trans ((rank_le_cut 76 2 4).trans (by decide +kernel))
  · exact (block_rank_le 76 3).trans ((rank_le_cut 76 3 1).trans (by decide +kernel))
  · exact (block_rank_le 77 0).trans ((rank_le_cut 77 0 9).trans (by decide +kernel))
  · exact (block_rank_le 77 1).trans ((rank_le_cut 77 1 6).trans (by decide +kernel))
  · exact (block_rank_le 77 2).trans ((rank_le_cut 77 2 3).trans (by decide +kernel))
  · exact (block_rank_le 78 0).trans ((rank_le_cut 78 0 8).trans (by decide +kernel))
  · exact (block_rank_le 78 1).trans ((rank_le_cut 78 1 5).trans (by decide +kernel))
  · exact (block_rank_le 78 2).trans ((rank_le_cut 78 2 2).trans (by decide +kernel))
  · exact (block_rank_le 79 0).trans ((rank_le_cut 79 0 7).trans (by decide +kernel))
  · exact (block_rank_le 79 1).trans ((rank_le_cut 79 1 4).trans (by decide +kernel))
  · exact (block_rank_le 79 2).trans ((rank_le_cut 79 2 1).trans (by decide +kernel))
  · exact (block_rank_le 80 0).trans ((rank_le_cut 80 0 6).trans (by decide +kernel))
  · exact (block_rank_le 80 1).trans ((rank_le_cut 80 1 3).trans (by decide +kernel))
  · exact (block_rank_le 81 0).trans ((rank_le_cut 81 0 5).trans (by decide +kernel))
  · exact (block_rank_le 81 1).trans ((rank_le_cut 81 1 2).trans (by decide +kernel))
  · exact (block_rank_le 82 0).trans ((rank_le_cut 82 0 4).trans (by decide +kernel))
  · exact (block_rank_le 82 1).trans ((rank_le_cut 82 1 1).trans (by decide +kernel))
  · exact (block_rank_le 83 0).trans ((rank_le_cut 83 0 3).trans (by decide +kernel))
  · exact (block_rank_le 84 0).trans ((rank_le_cut 84 0 2).trans (by decide +kernel))
  · exact (block_rank_le _ _).trans (rank_le_nominal _ _)

private def grade (q : ℕ) := total (allowance q) (88-q)
private def gradeTable : Fin 85 → ℕ := ![62, 183, 360, 590, 870, 1197, 1568, 1980, 2430, 2915, 3432, 3978, 4500, 4998, 5472, 5922, 6302, 6615, 6864, 7052, 7182, 7257, 7280, 7254, 7182, 7067, 6912, 6720, 6528, 6336, 6144, 5952, 5760, 5568, 5376, 5184, 4992, 4801, 4611, 4423, 4237, 4054, 3868, 3689, 3514, 3343, 3166, 3001, 2839, 2680, 2527, 2378, 2233, 2092, 1958, 1825, 1700, 1577, 1461, 1348, 1241, 1137, 1040, 946, 857, 772, 693, 617, 548, 481, 421, 364, 313, 265, 223, 184, 150, 120, 94, 72, 54, 39, 27, 18, 11]
private theorem grade_0 : grade 0 = 62 := by decide +kernel
private theorem grade_1 : grade 1 = 183 := by decide +kernel
private theorem grade_2 : grade 2 = 360 := by decide +kernel
private theorem grade_3 : grade 3 = 590 := by decide +kernel
private theorem grade_4 : grade 4 = 870 := by decide +kernel
private theorem grade_5 : grade 5 = 1197 := by decide +kernel
private theorem grade_6 : grade 6 = 1568 := by decide +kernel
private theorem grade_7 : grade 7 = 1980 := by decide +kernel
private theorem grade_8 : grade 8 = 2430 := by decide +kernel
private theorem grade_9 : grade 9 = 2915 := by decide +kernel
private theorem grade_10 : grade 10 = 3432 := by decide +kernel
private theorem grade_11 : grade 11 = 3978 := by decide +kernel
private theorem grade_12 : grade 12 = 4500 := by decide +kernel
private theorem grade_13 : grade 13 = 4998 := by decide +kernel
private theorem grade_14 : grade 14 = 5472 := by decide +kernel
private theorem grade_15 : grade 15 = 5922 := by decide +kernel
private theorem grade_16 : grade 16 = 6302 := by decide +kernel
private theorem grade_17 : grade 17 = 6615 := by decide +kernel
private theorem grade_18 : grade 18 = 6864 := by decide +kernel
private theorem grade_19 : grade 19 = 7052 := by decide +kernel
private theorem grade_20 : grade 20 = 7182 := by decide +kernel
private theorem grade_21 : grade 21 = 7257 := by decide +kernel
private theorem grade_22 : grade 22 = 7280 := by decide +kernel
private theorem grade_23 : grade 23 = 7254 := by decide +kernel
private theorem grade_24 : grade 24 = 7182 := by decide +kernel
private theorem grade_25 : grade 25 = 7067 := by decide +kernel
private theorem grade_26 : grade 26 = 6912 := by decide +kernel
private theorem grade_27 : grade 27 = 6720 := by decide +kernel
private theorem grade_28 : grade 28 = 6528 := by decide +kernel
private theorem grade_29 : grade 29 = 6336 := by decide +kernel
private theorem grade_30 : grade 30 = 6144 := by decide +kernel
private theorem grade_31 : grade 31 = 5952 := by decide +kernel
private theorem grade_32 : grade 32 = 5760 := by decide +kernel
private theorem grade_33 : grade 33 = 5568 := by decide +kernel
private theorem grade_34 : grade 34 = 5376 := by decide +kernel
private theorem grade_35 : grade 35 = 5184 := by decide +kernel
private theorem grade_36 : grade 36 = 4992 := by decide +kernel
private theorem grade_37 : grade 37 = 4801 := by decide +kernel
private theorem grade_38 : grade 38 = 4611 := by decide +kernel
private theorem grade_39 : grade 39 = 4423 := by decide +kernel
private theorem grade_40 : grade 40 = 4237 := by decide +kernel
private theorem grade_41 : grade 41 = 4054 := by decide +kernel
private theorem grade_42 : grade 42 = 3868 := by decide +kernel
private theorem grade_43 : grade 43 = 3689 := by decide +kernel
private theorem grade_44 : grade 44 = 3514 := by decide +kernel
private theorem grade_45 : grade 45 = 3343 := by decide +kernel
private theorem grade_46 : grade 46 = 3166 := by decide +kernel
private theorem grade_47 : grade 47 = 3001 := by decide +kernel
private theorem grade_48 : grade 48 = 2839 := by decide +kernel
private theorem grade_49 : grade 49 = 2680 := by decide +kernel
private theorem grade_50 : grade 50 = 2527 := by decide +kernel
private theorem grade_51 : grade 51 = 2378 := by decide +kernel
private theorem grade_52 : grade 52 = 2233 := by decide +kernel
private theorem grade_53 : grade 53 = 2092 := by decide +kernel
private theorem grade_54 : grade 54 = 1958 := by decide +kernel
private theorem grade_55 : grade 55 = 1825 := by decide +kernel
private theorem grade_56 : grade 56 = 1700 := by decide +kernel
private theorem grade_57 : grade 57 = 1577 := by decide +kernel
private theorem grade_58 : grade 58 = 1461 := by decide +kernel
private theorem grade_59 : grade 59 = 1348 := by decide +kernel
private theorem grade_60 : grade 60 = 1241 := by decide +kernel
private theorem grade_61 : grade 61 = 1137 := by decide +kernel
private theorem grade_62 : grade 62 = 1040 := by decide +kernel
private theorem grade_63 : grade 63 = 946 := by decide +kernel
private theorem grade_64 : grade 64 = 857 := by decide +kernel
private theorem grade_65 : grade 65 = 772 := by decide +kernel
private theorem grade_66 : grade 66 = 693 := by decide +kernel
private theorem grade_67 : grade 67 = 617 := by decide +kernel
private theorem grade_68 : grade 68 = 548 := by decide +kernel
private theorem grade_69 : grade 69 = 481 := by decide +kernel
private theorem grade_70 : grade 70 = 421 := by decide +kernel
private theorem grade_71 : grade 71 = 364 := by decide +kernel
private theorem grade_72 : grade 72 = 313 := by decide +kernel
private theorem grade_73 : grade 73 = 265 := by decide +kernel
private theorem grade_74 : grade 74 = 223 := by decide +kernel
private theorem grade_75 : grade 75 = 184 := by decide +kernel
private theorem grade_76 : grade 76 = 150 := by decide +kernel
private theorem grade_77 : grade 77 = 120 := by decide +kernel
private theorem grade_78 : grade 78 = 94 := by decide +kernel
private theorem grade_79 : grade 79 = 72 := by decide +kernel
private theorem grade_80 : grade 80 = 54 := by decide +kernel
private theorem grade_81 : grade 81 = 39 := by decide +kernel
private theorem grade_82 : grade 82 = 27 := by decide +kernel
private theorem grade_83 : grade 83 = 18 := by decide +kernel
private theorem grade_84 : grade 84 = 11 := by decide +kernel
private theorem grade_table (q : Fin 85) : grade q.val = gradeTable q := by
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
  · exact grade_76
  · exact grade_77
  · exact grade_78
  · exact grade_79
  · exact grade_80
  · exact grade_81
  · exact grade_82
  · exact grade_83
  · exact grade_84

theorem prefix_bound : CJ0.prefixRank source 85 ≤ 253996 := by
  change (∑ q ∈ range 85, ∑ u ∈ range (88-q),
    (CJ0.blockMatrix source q ((u : ℤ)-26)).rank) ≤ _
  calc
    _ ≤ ∑ q ∈ range 85, ∑ u ∈ range (88-q), allowance q u :=
      Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun u _ => bound q u
    _ = ∑ q : Fin 85, grade q.val := by
      rw [Fin.sum_univ_eq_sum_range]
      simp only [grade, total_eq_sum]
    _ = ∑ q : Fin 85, gradeTable q := Finset.sum_congr rfl fun q _ => grade_table q
    _ = 253996 := by decide +kernel

theorem certificate : RankCertificate 179730 source 253996 := by
  refine Or.inr ⟨85, le_rfl, ?_, prefix_bound⟩
  intro x hx hq
  have hb : x.q ≤ 84 := (native_shape.support x hx).1
  omega

#print axioms prefix_bound
end R6970Scalar84Rank
