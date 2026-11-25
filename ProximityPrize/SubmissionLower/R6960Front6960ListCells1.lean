import ProximityPrize.SubmissionLower.R6960Front6960ListCells0

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def allowance_10 (u : ℕ) : ℕ :=
  nominal 10 u

private theorem bound_10 (u : ℕ) :
    (CJ0.blockMatrix source 10 ((u : ℤ)-24)).rank ≤ allowance_10 u := by
  unfold allowance_10
  exact (block_rank_le 10 _).trans (rank_le_nominal 10 _)

theorem grade_10 : (∑ u ∈ Finset.range (83-10), (CJ0.blockMatrix source 10 ((u : ℤ)-24)).rank) ≤ 3234 := by
  refine (Finset.sum_le_sum fun u _ => bound_10 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_10)]
  decide +kernel

private def allowance_11 (u : ℕ) : ℕ :=
  nominal 11 u

private theorem bound_11 (u : ℕ) :
    (CJ0.blockMatrix source 11 ((u : ℤ)-24)).rank ≤ allowance_11 u := by
  unfold allowance_11
  exact (block_rank_le 11 _).trans (rank_le_nominal 11 _)

theorem grade_11 : (∑ u ∈ Finset.range (83-11), (CJ0.blockMatrix source 11 ((u : ℤ)-24)).rank) ≤ 3696 := by
  refine (Finset.sum_le_sum fun u _ => bound_11 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_11)]
  decide +kernel

private def allowance_12 (u : ℕ) : ℕ :=
  nominal 12 u

private theorem bound_12 (u : ℕ) :
    (CJ0.blockMatrix source 12 ((u : ℤ)-24)).rank ≤ allowance_12 u := by
  unfold allowance_12
  exact (block_rank_le 12 _).trans (rank_le_nominal 12 _)

theorem grade_12 : (∑ u ∈ Finset.range (83-12), (CJ0.blockMatrix source 12 ((u : ℤ)-24)).rank) ≤ 4136 := by
  refine (Finset.sum_le_sum fun u _ => bound_12 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_12)]
  decide +kernel

private def matrix_13_47 : CJ1.Block where
  bank := .leftLow
  cap := 98
  free := [(11, 0)]
  vectors := [
    [[0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_13_47 : (CJ0.blockMatrix source 13 ((47 : ℤ)-24)).rank ≤ 98 :=
  Fast.cell (z := matrix_13_47) (Fast.bands [(0, 0, 11), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 10), (5, 5, 9), (6, 6, 8), (7, 7, 7), (8, 8, 6), (9, 9, 5), (10, 10, 4), (11, 11, 3), (12, 12, 2), (13, 13, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_13 (u : ℕ) : ℕ :=
  match u with
  | 47 => 98
  | u => nominal 13 u

private theorem bound_13 (u : ℕ) :
    (CJ0.blockMatrix source 13 ((u : ℤ)-24)).rank ≤ allowance_13 u := by
  unfold allowance_13
  split
  · exact cell_13_47
  · exact (block_rank_le 13 _).trans (rank_le_nominal 13 _)

theorem grade_13 : (∑ u ∈ Finset.range (83-13), (CJ0.blockMatrix source 13 ((u : ℤ)-24)).rank) ≤ 4554 := by
  refine (Finset.sum_le_sum fun u _ => bound_13 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_13)]
  decide +kernel

private def matrix_14_45 : CJ1.Block where
  bank := .rightLow
  cap := 109
  free := [(14, 0)]
  vectors := [
    [[1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1], [2130706419, 2130706303, 2130705893, 2130705113, 2130704333, 2130704165, 2130704753, 2130705593, 2130706163, 2130706383, 2130706429], [91, 780, 2970, 6600, 9450, 9072, 5880, 2520, 675, 100, 6], [2130706069, 2130703573, 2130696533, 2130686633, 2130681233, 2130685265, 2130694673, 2130702233, 2130705533, 2130706333, 2130706429], [1001, 7150, 22275, 39600, 44100, 31752, 14700, 4200, 675, 50, 1], [2130704431, 2130693563, 2130670793, 2130650993, 2130653513, 2130674681, 2130694673, 2130703913, 2130706163, 2130706423], [3003, 17160, 41580, 55440, 44100, 21168, 5880, 840, 45], [2130703001, 2130689273, 2130670793, 2130666833, 2130681233, 2130697361, 2130704753, 2130706313], [3003, 12870, 22275, 19800, 9450, 2268, 210], [2130704431, 2130699283, 2130696533, 2130699833, 2130704333, 2130706181], [1001, 2860, 2970, 1320, 210], [2130706069, 2130705653, 2130705893, 2130706313], [91, 130, 45], [2130706419, 2130706423], [1]]
  ]
private theorem cell_14_45 : (CJ0.blockMatrix source 14 ((45 : ℤ)-24)).rank ≤ 109 :=
  Fast.cell (z := matrix_14_45) (Fast.bands [(0, 0, 15), (1, 0, 14), (2, 0, 13), (3, 0, 12), (4, 0, 11), (5, 0, 10), (6, 0, 9), (7, 0, 8), (8, 0, 7), (9, 0, 6), (10, 1, 4), (11, 2, 2)]) (by decide +kernel) (by decide +kernel)

private def matrix_14_46 : CJ1.Block where
  bank := .leftLow
  cap := 107
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_14_46 : (CJ0.blockMatrix source 14 ((46 : ℤ)-24)).rank ≤ 107 :=
  Fast.cell (z := matrix_14_46) (Fast.bands [(0, 0, 11), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 10), (6, 6, 9), (7, 7, 8), (8, 8, 7), (9, 9, 6), (10, 10, 5), (11, 11, 4), (12, 12, 3), (13, 13, 2), (14, 14, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_14 (u : ℕ) : ℕ :=
  match u with
  | 45 => 109
  | 46 => 107
  | u => nominal 14 u

private theorem bound_14 (u : ℕ) :
    (CJ0.blockMatrix source 14 ((u : ℤ)-24)).rank ≤ allowance_14 u := by
  unfold allowance_14
  split
  · exact cell_14_45
  · exact cell_14_46
  · exact (block_rank_le 14 _).trans (rank_le_nominal 14 _)

theorem grade_14 : (∑ u ∈ Finset.range (83-14), (CJ0.blockMatrix source 14 ((u : ℤ)-24)).rank) ≤ 4950 := by
  refine (Finset.sum_le_sum fun u _ => bound_14 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_14)]
  decide +kernel

private def matrix_15_44 : CJ1.Block where
  bank := .leftLow
  cap := 118
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 12], [0, 0, 0, 11], [0, 0, 0, 10], [0, 0, 0, 9], [0, 0, 0, 8], [0, 0, 0, 7], [0, 0, 0, 6], [0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_15_44 : (CJ0.blockMatrix source 15 ((44 : ℤ)-24)).rank ≤ 118 :=
  Fast.cell (z := matrix_15_44) (Fast.bands [(0, 0, 10), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 10), (7, 7, 9), (8, 8, 8), (9, 9, 7), (10, 10, 6), (11, 11, 5), (12, 12, 4), (13, 13, 3), (14, 14, 2), (15, 15, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_15_45 : CJ1.Block where
  bank := .leftLow
  cap := 115
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_15_45 : (CJ0.blockMatrix source 15 ((45 : ℤ)-24)).rank ≤ 115 :=
  Fast.cell (z := matrix_15_45) (Fast.bands [(0, 0, 10), (1, 1, 11), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 10), (7, 7, 9), (8, 8, 8), (9, 9, 7), (10, 10, 6), (11, 11, 5), (12, 12, 4), (13, 13, 3), (14, 14, 2), (15, 15, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_15 (u : ℕ) : ℕ :=
  match u with
  | 44 => 118
  | 45 => 115
  | u => nominal 15 u

private theorem bound_15 (u : ℕ) :
    (CJ0.blockMatrix source 15 ((u : ℤ)-24)).rank ≤ allowance_15 u := by
  unfold allowance_15
  split
  · exact cell_15_44
  · exact cell_15_45
  · exact (block_rank_le 15 _).trans (rank_le_nominal 15 _)

theorem grade_15 : (∑ u ∈ Finset.range (83-15), (CJ0.blockMatrix source 15 ((u : ℤ)-24)).rank) ≤ 5280 := by
  refine (Finset.sum_le_sum fun u _ => bound_15 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_15)]
  decide +kernel

private def matrix_16_43 : CJ1.Block where
  bank := .leftLow
  cap := 126
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 12], [0, 0, 0, 0, 11], [0, 0, 0, 0, 10], [0, 0, 0, 0, 9], [0, 0, 0, 0, 8], [0, 0, 0, 0, 7], [0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_16_43 : (CJ0.blockMatrix source 16 ((43 : ℤ)-24)).rank ≤ 126 :=
  Fast.cell (z := matrix_16_43) (Fast.bands [(0, 0, 9), (1, 1, 10), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 10), (8, 8, 9), (9, 9, 8), (10, 10, 7), (11, 11, 6), (12, 12, 5), (13, 13, 4), (14, 14, 3), (15, 15, 2), (16, 16, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_16_44 : CJ1.Block where
  bank := .leftLow
  cap := 122
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_16_44 : (CJ0.blockMatrix source 16 ((44 : ℤ)-24)).rank ≤ 122 :=
  Fast.cell (z := matrix_16_44) (Fast.bands [(0, 0, 9), (1, 1, 10), (2, 2, 11), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 10), (8, 8, 9), (9, 9, 8), (10, 10, 7), (11, 11, 6), (12, 12, 5), (13, 13, 4), (14, 14, 3), (15, 15, 2), (16, 16, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_16 (u : ℕ) : ℕ :=
  match u with
  | 43 => 126
  | 44 => 122
  | u => nominal 16 u

private theorem bound_16 (u : ℕ) :
    (CJ0.blockMatrix source 16 ((u : ℤ)-24)).rank ≤ allowance_16 u := by
  unfold allowance_16
  split
  · exact cell_16_43
  · exact cell_16_44
  · exact (block_rank_le 16 _).trans (rank_le_nominal 16 _)

theorem grade_16 : (∑ u ∈ Finset.range (83-16), (CJ0.blockMatrix source 16 ((u : ℤ)-24)).rank) ≤ 5547 := by
  refine (Finset.sum_le_sum fun u _ => bound_16 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_16)]
  decide +kernel

private def matrix_17_42 : CJ1.Block where
  bank := .leftLow
  cap := 133
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_17_42 : (CJ0.blockMatrix source 17 ((42 : ℤ)-24)).rank ≤ 133 :=
  Fast.cell (z := matrix_17_42) (Fast.bands [(0, 0, 8), (1, 1, 9), (2, 2, 10), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 10), (9, 9, 9), (10, 10, 8), (11, 11, 7), (12, 12, 6), (13, 13, 5), (14, 14, 4), (15, 15, 3), (16, 16, 2), (17, 17, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_17_43 : CJ1.Block where
  bank := .leftLow
  cap := 128
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_17_43 : (CJ0.blockMatrix source 17 ((43 : ℤ)-24)).rank ≤ 128 :=
  Fast.cell (z := matrix_17_43) (Fast.bands [(0, 0, 8), (1, 1, 9), (2, 2, 10), (3, 3, 11), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 10), (9, 9, 9), (10, 10, 8), (11, 11, 7), (12, 12, 6), (13, 13, 5), (14, 14, 4), (15, 15, 3), (16, 16, 2), (17, 17, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_17 (u : ℕ) : ℕ :=
  match u with
  | 42 => 133
  | 43 => 128
  | u => nominal 17 u

private theorem bound_17 (u : ℕ) :
    (CJ0.blockMatrix source 17 ((u : ℤ)-24)).rank ≤ allowance_17 u := by
  unfold allowance_17
  split
  · exact cell_17_42
  · exact cell_17_43
  · exact (block_rank_le 17 _).trans (rank_le_nominal 17 _)

theorem grade_17 : (∑ u ∈ Finset.range (83-17), (CJ0.blockMatrix source 17 ((u : ℤ)-24)).rank) ≤ 5754 := by
  refine (Finset.sum_le_sum fun u _ => bound_17 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_17)]
  decide +kernel

private def matrix_18_41 : CJ1.Block where
  bank := .leftLow
  cap := 139
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_18_41 : (CJ0.blockMatrix source 18 ((41 : ℤ)-24)).rank ≤ 139 :=
  Fast.cell (z := matrix_18_41) (Fast.bands [(0, 0, 7), (1, 1, 8), (2, 2, 9), (3, 3, 10), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 10), (10, 10, 9), (11, 11, 8), (12, 12, 7), (13, 13, 6), (14, 14, 5), (15, 15, 4), (16, 16, 3), (17, 17, 2), (18, 18, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_18_42 : CJ1.Block where
  bank := .leftLow
  cap := 133
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_18_42 : (CJ0.blockMatrix source 18 ((42 : ℤ)-24)).rank ≤ 133 :=
  Fast.cell (z := matrix_18_42) (Fast.bands [(0, 0, 7), (1, 1, 8), (2, 2, 9), (3, 3, 10), (4, 4, 11), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 10), (10, 10, 9), (11, 11, 8), (12, 12, 7), (13, 13, 6), (14, 14, 5), (15, 15, 4), (16, 16, 3), (17, 17, 2), (18, 18, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_18 (u : ℕ) : ℕ :=
  match u with
  | 41 => 139
  | 42 => 133
  | u => nominal 18 u

private theorem bound_18 (u : ℕ) :
    (CJ0.blockMatrix source 18 ((u : ℤ)-24)).rank ≤ allowance_18 u := by
  unfold allowance_18
  split
  · exact cell_18_41
  · exact cell_18_42
  · exact (block_rank_le 18 _).trans (rank_le_nominal 18 _)

theorem grade_18 : (∑ u ∈ Finset.range (83-18), (CJ0.blockMatrix source 18 ((u : ℤ)-24)).rank) ≤ 5904 := by
  refine (Finset.sum_le_sum fun u _ => bound_18 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_18)]
  decide +kernel

private def matrix_19_40 : CJ1.Block where
  bank := .leftLow
  cap := 144
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_19_40 : (CJ0.blockMatrix source 19 ((40 : ℤ)-24)).rank ≤ 144 :=
  Fast.cell (z := matrix_19_40) (Fast.bands [(0, 0, 6), (1, 1, 7), (2, 2, 8), (3, 3, 9), (4, 4, 10), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 10), (11, 11, 9), (12, 12, 8), (13, 13, 7), (14, 14, 6), (15, 15, 5), (16, 16, 4), (17, 17, 3), (18, 18, 2), (19, 19, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_19_41 : CJ1.Block where
  bank := .leftLow
  cap := 137
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_19_41 : (CJ0.blockMatrix source 19 ((41 : ℤ)-24)).rank ≤ 137 :=
  Fast.cell (z := matrix_19_41) (Fast.bands [(0, 0, 6), (1, 1, 7), (2, 2, 8), (3, 3, 9), (4, 4, 10), (5, 5, 11), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 10), (11, 11, 9), (12, 12, 8), (13, 13, 7), (14, 14, 6), (15, 15, 5), (16, 16, 4), (17, 17, 3), (18, 18, 2), (19, 19, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_19 (u : ℕ) : ℕ :=
  match u with
  | 40 => 144
  | 41 => 137
  | u => nominal 19 u

private theorem bound_19 (u : ℕ) :
    (CJ0.blockMatrix source 19 ((u : ℤ)-24)).rank ≤ allowance_19 u := by
  unfold allowance_19
  split
  · exact cell_19_40
  · exact cell_19_41
  · exact (block_rank_le 19 _).trans (rank_le_nominal 19 _)

theorem grade_19 : (∑ u ∈ Finset.range (83-19), (CJ0.blockMatrix source 19 ((u : ℤ)-24)).rank) ≤ 6000 := by
  refine (Finset.sum_le_sum fun u _ => bound_19 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_19)]
  decide +kernel

end Front6960ListBank
