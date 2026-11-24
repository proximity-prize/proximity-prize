import ProximityPrize.SubmissionLower.Front6963ListBank

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6963ListBank
open scoped BigOperators

private def matrix_76_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(4, 0), (6, 0), (8, 0), (10, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_76_0 : (CJ0.blockMatrix source 76 ((0 : ℤ)-24)).rank ≤ 7 :=
  Fast.cell (z := matrix_76_0) (Fast.bands [(0, 70, 7), (1, 71, 5), (2, 72, 3), (3, 73, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_76_1 : CJ1.Block where
  bank := .leftLow
  cap := 10
  free := [(2, 0), (2, 1)]
  vectors := [
    [[0, 0, 0, 0, 1431, 5512], [0, 0, 2130706380, 2130706330], [1]],
    [[0, 0, 0, 0, 0, 1378], [0, 0, 0, 2130706381], [0, 1]]
  ]
private theorem cell_76_1 : (CJ0.blockMatrix source 76 ((1 : ℤ)-24)).rank ≤ 10 :=
  Fast.cell (z := matrix_76_1) (Fast.bands [(52, 52, 1), (53, 53, 2), (54, 55, 2), (55, 57, 2), (56, 59, 2), (57, 61, 2), (58, 63, 2), (59, 65, 2), (60, 67, 2), (61, 69, 2), (62, 71, 2), (63, 73, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_76 (u : ℕ) : ℕ :=
  match u with
  | 0 => 7
  | 1 => 10
  | u => nominal 76 u

private theorem bound_76 (u : ℕ) :
    (CJ0.blockMatrix source 76 ((u : ℤ)-24)).rank ≤ allowance_76 u := by
  unfold allowance_76
  split
  · exact cell_76_0
  · exact cell_76_1
  · exact (block_rank_le 76 _).trans (rank_le_nominal 76 _)

theorem grade_76 : (∑ u ∈ Finset.range (83-76), (CJ0.blockMatrix source 76 ((u : ℤ)-24)).rank) ≤ 39 := by
  refine (Finset.sum_le_sum fun u _ => bound_76 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_76)]
  decide +kernel

private def matrix_77_0 : CJ1.Block where
  bank := .rightLow
  cap := 6
  free := [(4, 0), (6, 0), (8, 0), (10, 0), (12, 0)]
  vectors := [
    [[], [], [], [], [1]],
    [[], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [1]],
    [[], [], [], [], [], [], [], [], [], [], [], [], [1]]
  ]
private theorem cell_77_0 : (CJ0.blockMatrix source 77 ((0 : ℤ)-24)).rank ≤ 6 :=
  Fast.cell (z := matrix_77_0) (Fast.bands [(0, 72, 6), (1, 73, 4), (2, 74, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_77_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2, 0)]
  vectors := [
    [[0, 0, 0, 0, 1431], [0, 0, 2130706380], [1]]
  ]
private theorem cell_77_1 : (CJ0.blockMatrix source 77 ((1 : ℤ)-24)).rank ≤ 8 :=
  Fast.cell (z := matrix_77_1) (Fast.bands [(53, 53, 1), (54, 54, 2), (55, 56, 2), (56, 58, 2), (57, 60, 2), (58, 62, 2), (59, 64, 2), (60, 66, 2), (61, 68, 2), (62, 70, 2), (63, 72, 2), (64, 74, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_77 (u : ℕ) : ℕ :=
  match u with
  | 0 => 6
  | 1 => 8
  | u => nominal 77 u

private theorem bound_77 (u : ℕ) :
    (CJ0.blockMatrix source 77 ((u : ℤ)-24)).rank ≤ allowance_77 u := by
  unfold allowance_77
  split
  · exact cell_77_0
  · exact cell_77_1
  · exact (block_rank_le 77 _).trans (rank_le_nominal 77 _)

theorem grade_77 : (∑ u ∈ Finset.range (83-77), (CJ0.blockMatrix source 77 ((u : ℤ)-24)).rank) ≤ 27 := by
  refine (Finset.sum_le_sum fun u _ => bound_77 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_77)]
  decide +kernel

private def matrix_78_0 : CJ1.Block where
  bank := .leftLow
  cap := 5
  free := [(1, 0), (1, 1), (1, 2), (2, 0)]
  vectors := [
    [[0, 0, 2130706377, 2130706323, 2130706217], [1]],
    [[0, 0, 0, 2130706378, 2130706325], [0, 1]],
    [[0, 0, 0, 0, 2130706379], [0, 0, 1]],
    [[0, 0, 0, 0, 2130705002], [], [1]]
  ]
private theorem cell_78_0 : (CJ0.blockMatrix source 78 ((0 : ℤ)-24)).rank ≤ 5 :=
  Fast.cell (z := matrix_78_0) (Fast.bands [(54, 54, 1), (55, 56, 1), (56, 58, 1), (57, 60, 1), (58, 62, 1), (59, 64, 1), (60, 66, 1), (61, 68, 1), (62, 70, 1), (63, 72, 1), (64, 74, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_78 (u : ℕ) : ℕ :=
  match u with
  | 0 => 5
  | u => nominal 78 u

private theorem bound_78 (u : ℕ) :
    (CJ0.blockMatrix source 78 ((u : ℤ)-24)).rank ≤ allowance_78 u := by
  unfold allowance_78
  split
  · exact cell_78_0
  · exact (block_rank_le 78 _).trans (rank_le_nominal 78 _)

theorem grade_78 : (∑ u ∈ Finset.range (83-78), (CJ0.blockMatrix source 78 ((u : ℤ)-24)).rank) ≤ 18 := by
  refine (Finset.sum_le_sum fun u _ => bound_78 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_78)]
  decide +kernel

private def matrix_79_0 : CJ1.Block where
  bank := .leftLow
  cap := 4
  free := [(1, 0), (1, 1)]
  vectors := [
    [[0, 0, 2130706377, 2130706323], [1]],
    [[0, 0, 0, 2130706378], [0, 1]]
  ]
private theorem cell_79_0 : (CJ0.blockMatrix source 79 ((0 : ℤ)-24)).rank ≤ 4 :=
  Fast.cell (z := matrix_79_0) (Fast.bands [(55, 55, 1), (56, 57, 1), (57, 59, 1), (58, 61, 1), (59, 63, 1), (60, 65, 1), (61, 67, 1), (62, 69, 1), (63, 71, 1), (64, 73, 1), (65, 75, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_79 (u : ℕ) : ℕ :=
  match u with
  | 0 => 4
  | u => nominal 79 u

private theorem bound_79 (u : ℕ) :
    (CJ0.blockMatrix source 79 ((u : ℤ)-24)).rank ≤ allowance_79 u := by
  unfold allowance_79
  split
  · exact cell_79_0
  · exact (block_rank_le 79 _).trans (rank_le_nominal 79 _)

theorem grade_79 : (∑ u ∈ Finset.range (83-79), (CJ0.blockMatrix source 79 ((u : ℤ)-24)).rank) ≤ 11 := by
  refine (Finset.sum_le_sum fun u _ => bound_79 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_79)]
  decide +kernel

private def matrix_80_0 : CJ1.Block where
  bank := .leftLow
  cap := 3
  free := [(1, 0)]
  vectors := [
    [[0, 0, 2130706377], [1]]
  ]
private theorem cell_80_0 : (CJ0.blockMatrix source 80 ((0 : ℤ)-24)).rank ≤ 3 :=
  Fast.cell (z := matrix_80_0) (Fast.bands [(56, 56, 1), (57, 58, 1), (58, 60, 1), (59, 62, 1), (60, 64, 1), (61, 66, 1), (62, 68, 1), (63, 70, 1), (64, 72, 1), (65, 74, 1), (66, 76, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_80 (u : ℕ) : ℕ :=
  match u with
  | 0 => 3
  | u => nominal 80 u

private theorem bound_80 (u : ℕ) :
    (CJ0.blockMatrix source 80 ((u : ℤ)-24)).rank ≤ allowance_80 u := by
  unfold allowance_80
  split
  · exact cell_80_0
  · exact (block_rank_le 80 _).trans (rank_le_nominal 80 _)

theorem grade_80 : (∑ u ∈ Finset.range (83-80), (CJ0.blockMatrix source 80 ((u : ℤ)-24)).rank) ≤ 6 := by
  refine (Finset.sum_le_sum fun u _ => bound_80 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_80)]
  decide +kernel

end Front6963ListBank
