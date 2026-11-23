import ProximityPrize.SubmissionLower.R6960Front6960ListBank

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_70_1 : CJ1.Block where
  bank := .rightLow
  cap := 18
  free := [(2, 0), (3, 0), (5, 0), (7, 0)]
  vectors := [
    [[], [], [1]],
    [[], [], [], [1]],
    [[], [], [], [], [2130706432], [1]],
    [[], [], [], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_70_1 : (CJ0.blockMatrix source 70 ((1 : ℤ)-23)).rank ≤ 18 :=
  Fast.cell (z := matrix_70_1) (Fast.bands [(0, 61, 10), (1, 62, 8), (2, 63, 6), (3, 64, 4), (4, 65, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_70_2 : CJ1.Block where
  bank := .leftLow
  cap := 21
  free := [(3, 0), (3, 1), (3, 2), (4, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130685608, 2130588833, 2130264257], [0, 0, 0, 0, 1225, 4655, 13248], [0, 0, 2130706384, 2130706339, 2130706253], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130686833, 2130595889], [0, 0, 0, 0, 0, 1176, 4464], [0, 0, 0, 2130706385, 2130706341], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130688009], [0, 0, 0, 0, 0, 0, 1128], [0, 0, 0, 0, 2130706386], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 2130070805], [0, 0, 0, 0, 0, 0, 34592], [0, 0, 0, 0, 2130705352], [], [1]]
  ]
private theorem cell_70_2 : (CJ0.blockMatrix source 70 ((2 : ℤ)-23)).rank ≤ 21 :=
  Fast.cell (z := matrix_70_2) (Fast.bands [(47, 47, 1), (48, 48, 2), (49, 49, 3), (50, 51, 3), (51, 53, 3), (52, 55, 3), (53, 57, 3), (54, 59, 3), (55, 61, 3), (56, 63, 3), (57, 65, 3), (58, 67, 2), (59, 69, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_70 (u : ℕ) : ℕ :=
  match u with
  | 1 => 18
  | 2 => 21
  | u => nominal 70 u

private theorem bound_70 (u : ℕ) :
    (CJ0.blockMatrix source 70 ((u : ℤ)-23)).rank ≤ allowance_70 u := by
  unfold allowance_70
  split
  · exact cell_70_1
  · exact cell_70_2
  · exact (block_rank_le 70 _).trans (rank_le_nominal 70 _)

theorem grade_70 : (∑ u ∈ Finset.range (81-70), (CJ0.blockMatrix source 70 ((u : ℤ)-23)).rank) ≤ 120 := by
  refine (Finset.sum_le_sum fun u _ => bound_70 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_70)]
  decide +kernel

private def matrix_71_0 : CJ1.Block where
  bank := .rightLow
  cap := 10
  free := [(3, 0)]
  vectors := [
    [[], [], [], [1]]
  ]
private theorem cell_71_0 : (CJ0.blockMatrix source 71 ((0 : ℤ)-23)).rank ≤ 10 :=
  Fast.cell (z := matrix_71_0) (Fast.bands [(0, 62, 10), (1, 63, 8), (2, 64, 6), (3, 65, 4), (4, 66, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_71_1 : CJ1.Block where
  bank := .rightLow
  cap := 16
  free := [(2, 0), (3, 0), (4, 0), (5, 0), (7, 0), (9, 0)]
  vectors := [
    [[], [], [1]],
    [[], [], [], [1]],
    [[], [], [], [], [1]],
    [[], [], [], [], [], [1]],
    [[], [], [], [], [], [], [2130706432], [1]],
    [[], [], [], [], [], [], [2130706432], [], [2130706432], [1]]
  ]
private theorem cell_71_1 : (CJ0.blockMatrix source 71 ((1 : ℤ)-23)).rank ≤ 16 :=
  Fast.cell (z := matrix_71_1) (Fast.bands [(0, 63, 9), (1, 64, 7), (2, 65, 5), (3, 66, 3), (4, 67, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_71_2 : CJ1.Block where
  bank := .leftLow
  cap := 18
  free := [(3, 0), (3, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130685608, 2130588833], [0, 0, 0, 0, 1225, 4655], [0, 0, 2130706384, 2130706339], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 2130686833], [0, 0, 0, 0, 0, 1176], [0, 0, 0, 2130706385], [0, 1]]
  ]
private theorem cell_71_2 : (CJ0.blockMatrix source 71 ((2 : ℤ)-23)).rank ≤ 18 :=
  Fast.cell (z := matrix_71_2) (Fast.bands [(48, 48, 1), (49, 49, 2), (50, 50, 3), (51, 52, 3), (52, 54, 3), (53, 56, 3), (54, 58, 3), (55, 60, 3), (56, 62, 3), (57, 64, 3), (58, 66, 3), (59, 68, 2), (60, 70, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_71 (u : ℕ) : ℕ :=
  match u with
  | 0 => 10
  | 1 => 16
  | 2 => 18
  | u => nominal 71 u

private theorem bound_71 (u : ℕ) :
    (CJ0.blockMatrix source 71 ((u : ℤ)-23)).rank ≤ allowance_71 u := by
  unfold allowance_71
  split
  · exact cell_71_0
  · exact cell_71_1
  · exact cell_71_2
  · exact (block_rank_le 71 _).trans (rank_le_nominal 71 _)

theorem grade_71 : (∑ u ∈ Finset.range (81-71), (CJ0.blockMatrix source 71 ((u : ℤ)-23)).rank) ≤ 94 := by
  refine (Finset.sum_le_sum fun u _ => bound_71 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_71)]
  decide +kernel

private def matrix_72_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(3, 0), (5, 0)]
  vectors := [
    [[], [], [], [1]],
    [[], [], [], [], [], [1]]
  ]
private theorem cell_72_0 : (CJ0.blockMatrix source 72 ((0 : ℤ)-23)).rank ≤ 9 :=
  Fast.cell (z := matrix_72_0) (Fast.bands [(0, 64, 9), (1, 65, 7), (2, 66, 5), (3, 67, 3), (4, 68, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_72_1 : CJ1.Block where
  bank := .leftLow
  cap := 14
  free := [(2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1)]
  vectors := [
    [[0, 0, 0, 0, 1378, 5304, 15300, 39200], [0, 0, 2130706381, 2130706332, 2130706237, 2130706053], [1]],
    [[0, 0, 0, 0, 0, 1326, 5100, 14700], [0, 0, 0, 2130706382, 2130706334, 2130706241], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 1275, 4900], [0, 0, 0, 0, 2130706383, 2130706336], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 0, 1225], [0, 0, 0, 0, 0, 2130706384], [0, 0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 41650, 237650], [0, 0, 0, 0, 2130705208, 2130701729], [], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 39200], [0, 0, 0, 0, 0, 2130705257], [], [0, 1]]
  ]
private theorem cell_72_1 : (CJ0.blockMatrix source 72 ((1 : ℤ)-23)).rank ≤ 14 :=
  Fast.cell (z := matrix_72_1) (Fast.bands [(49, 49, 1), (50, 50, 2), (51, 52, 2), (52, 54, 2), (53, 56, 2), (54, 58, 2), (55, 60, 2), (56, 62, 2), (57, 64, 2), (58, 66, 2), (59, 68, 2), (60, 70, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_72_2 : CJ1.Block where
  bank := .leftLow
  cap := 15
  free := [(3, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 2130685608], [0, 0, 0, 0, 1225], [0, 0, 2130706384], [1]]
  ]
private theorem cell_72_2 : (CJ0.blockMatrix source 72 ((2 : ℤ)-23)).rank ≤ 15 :=
  Fast.cell (z := matrix_72_2) (Fast.bands [(49, 49, 1), (50, 50, 2), (51, 51, 3), (52, 53, 3), (53, 55, 3), (54, 57, 3), (55, 59, 3), (56, 61, 3), (57, 63, 3), (58, 65, 3), (59, 67, 3), (60, 69, 2), (61, 71, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_72 (u : ℕ) : ℕ :=
  match u with
  | 0 => 9
  | 1 => 14
  | 2 => 15
  | u => nominal 72 u

private theorem bound_72 (u : ℕ) :
    (CJ0.blockMatrix source 72 ((u : ℤ)-23)).rank ≤ allowance_72 u := by
  unfold allowance_72
  split
  · exact cell_72_0
  · exact cell_72_1
  · exact cell_72_2
  · exact (block_rank_le 72 _).trans (rank_le_nominal 72 _)

theorem grade_72 : (∑ u ∈ Finset.range (81-72), (CJ0.blockMatrix source 72 ((u : ℤ)-23)).rank) ≤ 72 := by
  refine (Finset.sum_le_sum fun u _ => bound_72 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_72)]
  decide +kernel

private def matrix_73_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(3, 0), (5, 0), (7, 0)]
  vectors := [
    [[], [], [], [1]],
    [[], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [1]]
  ]
private theorem cell_73_0 : (CJ0.blockMatrix source 73 ((0 : ℤ)-23)).rank ≤ 8 :=
  Fast.cell (z := matrix_73_0) (Fast.bands [(0, 66, 8), (1, 67, 6), (2, 68, 4), (3, 69, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_73_1 : CJ1.Block where
  bank := .leftLow
  cap := 12
  free := [(2, 0), (2, 1), (2, 2), (3, 0)]
  vectors := [
    [[0, 0, 0, 0, 1378, 5304, 15300], [0, 0, 2130706381, 2130706332, 2130706237], [1]],
    [[0, 0, 0, 0, 0, 1326, 5100], [0, 0, 0, 2130706382, 2130706334], [0, 1]],
    [[0, 0, 0, 0, 0, 0, 1275], [0, 0, 0, 0, 2130706383], [0, 0, 1]],
    [[0, 0, 0, 0, 0, 0, 41650], [0, 0, 0, 0, 2130705208], [], [1]]
  ]
private theorem cell_73_1 : (CJ0.blockMatrix source 73 ((1 : ℤ)-23)).rank ≤ 12 :=
  Fast.cell (z := matrix_73_1) (Fast.bands [(50, 50, 1), (51, 51, 2), (52, 53, 2), (53, 55, 2), (54, 57, 2), (55, 59, 2), (56, 61, 2), (57, 63, 2), (58, 65, 2), (59, 67, 2), (60, 69, 2), (61, 71, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_73 (u : ℕ) : ℕ :=
  match u with
  | 0 => 8
  | 1 => 12
  | u => nominal 73 u

private theorem bound_73 (u : ℕ) :
    (CJ0.blockMatrix source 73 ((u : ℤ)-23)).rank ≤ allowance_73 u := by
  unfold allowance_73
  split
  · exact cell_73_0
  · exact cell_73_1
  · exact (block_rank_le 73 _).trans (rank_le_nominal 73 _)

theorem grade_73 : (∑ u ∈ Finset.range (81-73), (CJ0.blockMatrix source 73 ((u : ℤ)-23)).rank) ≤ 54 := by
  refine (Finset.sum_le_sum fun u _ => bound_73 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_73)]
  decide +kernel

private def matrix_74_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(3, 0), (5, 0), (7, 0), (9, 0)]
  vectors := [
    [[], [], [], [1]],
    [[], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_74_0 : (CJ0.blockMatrix source 74 ((0 : ℤ)-23)).rank ≤ 7 :=
  Fast.cell (z := matrix_74_0) (Fast.bands [(0, 68, 7), (1, 69, 5), (2, 70, 3), (3, 71, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_74_1 : CJ1.Block where
  bank := .leftLow
  cap := 10
  free := [(2, 0), (2, 1)]
  vectors := [
    [[0, 0, 0, 0, 1378, 5304], [0, 0, 2130706381, 2130706332], [1]],
    [[0, 0, 0, 0, 0, 1326], [0, 0, 0, 2130706382], [0, 1]]
  ]
private theorem cell_74_1 : (CJ0.blockMatrix source 74 ((1 : ℤ)-23)).rank ≤ 10 :=
  Fast.cell (z := matrix_74_1) (Fast.bands [(51, 51, 1), (52, 52, 2), (53, 54, 2), (54, 56, 2), (55, 58, 2), (56, 60, 2), (57, 62, 2), (58, 64, 2), (59, 66, 2), (60, 68, 2), (61, 70, 2), (62, 72, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_74 (u : ℕ) : ℕ :=
  match u with
  | 0 => 7
  | 1 => 10
  | u => nominal 74 u

private theorem bound_74 (u : ℕ) :
    (CJ0.blockMatrix source 74 ((u : ℤ)-23)).rank ≤ allowance_74 u := by
  unfold allowance_74
  split
  · exact cell_74_0
  · exact cell_74_1
  · exact (block_rank_le 74 _).trans (rank_le_nominal 74 _)

theorem grade_74 : (∑ u ∈ Finset.range (81-74), (CJ0.blockMatrix source 74 ((u : ℤ)-23)).rank) ≤ 39 := by
  refine (Finset.sum_le_sum fun u _ => bound_74 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_74)]
  decide +kernel

private def matrix_75_0 : CJ1.Block where
  bank := .rightLow
  cap := 6
  free := [(3, 0), (5, 0), (7, 0), (9, 0), (11, 0)]
  vectors := [
    [[], [], [], [1]],
    [[], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_75_0 : (CJ0.blockMatrix source 75 ((0 : ℤ)-23)).rank ≤ 6 :=
  Fast.cell (z := matrix_75_0) (Fast.bands [(0, 70, 6), (1, 71, 4), (2, 72, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_75_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2, 0)]
  vectors := [
    [[0, 0, 0, 0, 1378], [0, 0, 2130706381], [1]]
  ]
private theorem cell_75_1 : (CJ0.blockMatrix source 75 ((1 : ℤ)-23)).rank ≤ 8 :=
  Fast.cell (z := matrix_75_1) (Fast.bands [(52, 52, 1), (53, 53, 2), (54, 55, 2), (55, 57, 2), (56, 59, 2), (57, 61, 2), (58, 63, 2), (59, 65, 2), (60, 67, 2), (61, 69, 2), (62, 71, 2), (63, 73, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_75 (u : ℕ) : ℕ :=
  match u with
  | 0 => 6
  | 1 => 8
  | u => nominal 75 u

private theorem bound_75 (u : ℕ) :
    (CJ0.blockMatrix source 75 ((u : ℤ)-23)).rank ≤ allowance_75 u := by
  unfold allowance_75
  split
  · exact cell_75_0
  · exact cell_75_1
  · exact (block_rank_le 75 _).trans (rank_le_nominal 75 _)

theorem grade_75 : (∑ u ∈ Finset.range (81-75), (CJ0.blockMatrix source 75 ((u : ℤ)-23)).rank) ≤ 27 := by
  refine (Finset.sum_le_sum fun u _ => bound_75 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_75)]
  decide +kernel

private def matrix_76_0 : CJ1.Block where
  bank := .leftLow
  cap := 5
  free := [(1, 0), (1, 1), (1, 2), (2, 0)]
  vectors := [
    [[0, 0, 2130706378, 2130706325, 2130706221], [1]],
    [[0, 0, 0, 2130706379, 2130706327], [0, 1]],
    [[0, 0, 0, 0, 2130706380], [0, 0, 1]],
    [[0, 0, 0, 0, 2130705055], [], [1]]
  ]
private theorem cell_76_0 : (CJ0.blockMatrix source 76 ((0 : ℤ)-23)).rank ≤ 5 :=
  Fast.cell (z := matrix_76_0) (Fast.bands [(53, 53, 1), (54, 55, 1), (55, 57, 1), (56, 59, 1), (57, 61, 1), (58, 63, 1), (59, 65, 1), (60, 67, 1), (61, 69, 1), (62, 71, 1), (63, 73, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_76 (u : ℕ) : ℕ :=
  match u with
  | 0 => 5
  | u => nominal 76 u

private theorem bound_76 (u : ℕ) :
    (CJ0.blockMatrix source 76 ((u : ℤ)-23)).rank ≤ allowance_76 u := by
  unfold allowance_76
  split
  · exact cell_76_0
  · exact (block_rank_le 76 _).trans (rank_le_nominal 76 _)

theorem grade_76 : (∑ u ∈ Finset.range (81-76), (CJ0.blockMatrix source 76 ((u : ℤ)-23)).rank) ≤ 18 := by
  refine (Finset.sum_le_sum fun u _ => bound_76 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_76)]
  decide +kernel

private def matrix_77_0 : CJ1.Block where
  bank := .leftLow
  cap := 4
  free := [(1, 0), (1, 1)]
  vectors := [
    [[0, 0, 2130706378, 2130706325], [1]],
    [[0, 0, 0, 2130706379], [0, 1]]
  ]
private theorem cell_77_0 : (CJ0.blockMatrix source 77 ((0 : ℤ)-23)).rank ≤ 4 :=
  Fast.cell (z := matrix_77_0) (Fast.bands [(54, 54, 1), (55, 56, 1), (56, 58, 1), (57, 60, 1), (58, 62, 1), (59, 64, 1), (60, 66, 1), (61, 68, 1), (62, 70, 1), (63, 72, 1), (64, 74, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_77 (u : ℕ) : ℕ :=
  match u with
  | 0 => 4
  | u => nominal 77 u

private theorem bound_77 (u : ℕ) :
    (CJ0.blockMatrix source 77 ((u : ℤ)-23)).rank ≤ allowance_77 u := by
  unfold allowance_77
  split
  · exact cell_77_0
  · exact (block_rank_le 77 _).trans (rank_le_nominal 77 _)

theorem grade_77 : (∑ u ∈ Finset.range (81-77), (CJ0.blockMatrix source 77 ((u : ℤ)-23)).rank) ≤ 11 := by
  refine (Finset.sum_le_sum fun u _ => bound_77 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_77)]
  decide +kernel

private def matrix_78_0 : CJ1.Block where
  bank := .leftLow
  cap := 3
  free := [(1, 0)]
  vectors := [
    [[0, 0, 2130706378], [1]]
  ]
private theorem cell_78_0 : (CJ0.blockMatrix source 78 ((0 : ℤ)-23)).rank ≤ 3 :=
  Fast.cell (z := matrix_78_0) (Fast.bands [(55, 55, 1), (56, 57, 1), (57, 59, 1), (58, 61, 1), (59, 63, 1), (60, 65, 1), (61, 67, 1), (62, 69, 1), (63, 71, 1), (64, 73, 1), (65, 75, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_78 (u : ℕ) : ℕ :=
  match u with
  | 0 => 3
  | u => nominal 78 u

private theorem bound_78 (u : ℕ) :
    (CJ0.blockMatrix source 78 ((u : ℤ)-23)).rank ≤ allowance_78 u := by
  unfold allowance_78
  split
  · exact cell_78_0
  · exact (block_rank_le 78 _).trans (rank_le_nominal 78 _)

theorem grade_78 : (∑ u ∈ Finset.range (81-78), (CJ0.blockMatrix source 78 ((u : ℤ)-23)).rank) ≤ 6 := by
  refine (Finset.sum_le_sum fun u _ => bound_78 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_78)]
  decide +kernel

private def allowance_79 (u : ℕ) : ℕ :=
  nominal 79 u

private theorem bound_79 (u : ℕ) :
    (CJ0.blockMatrix source 79 ((u : ℤ)-23)).rank ≤ allowance_79 u := by
  unfold allowance_79
  exact (block_rank_le 79 _).trans (rank_le_nominal 79 _)

theorem grade_79 : (∑ u ∈ Finset.range (81-79), (CJ0.blockMatrix source 79 ((u : ℤ)-23)).rank) ≤ 3 := by
  refine (Finset.sum_le_sum fun u _ => bound_79 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_79)]
  decide +kernel

end Front6960ListBank
