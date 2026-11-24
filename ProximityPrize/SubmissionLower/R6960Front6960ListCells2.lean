import ProximityPrize.SubmissionLower.R6960Front6960ListCells0

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

namespace Front6960ListBank
open scoped BigOperators

private def matrix_20_37 : CJ1.Block where
  bank := .leftLow
  cap := 148
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_20_37 : (CJ0.blockMatrix source 20 ((37 : ℤ)-24)).rank ≤ 148 :=
  Fast.cell (z := matrix_20_37) (Fast.bands [(0, 0, 5), (1, 1, 6), (2, 2, 7), (3, 3, 8), (4, 4, 9), (5, 5, 10), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 10), (12, 12, 9), (13, 13, 8), (14, 14, 7), (15, 15, 6), (16, 16, 5), (17, 17, 4), (18, 18, 3), (19, 19, 2), (20, 20, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_20_38 : CJ1.Block where
  bank := .leftLow
  cap := 140
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_20_38 : (CJ0.blockMatrix source 20 ((38 : ℤ)-24)).rank ≤ 140 :=
  Fast.cell (z := matrix_20_38) (Fast.bands [(0, 0, 5), (1, 1, 6), (2, 2, 7), (3, 3, 8), (4, 4, 9), (5, 5, 10), (6, 6, 11), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 10), (12, 12, 9), (13, 13, 8), (14, 14, 7), (15, 15, 6), (16, 16, 5), (17, 17, 4), (18, 18, 3), (19, 19, 2), (20, 20, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_20 (u : ℕ) : ℕ :=
  match u with
  | 37 => 148
  | 38 => 140
  | u => nominal 20 u

private theorem bound_20 (u : ℕ) :
    (CJ0.blockMatrix source 20 ((u : ℤ)-24)).rank ≤ allowance_20 u := by
  unfold allowance_20
  split
  · exact cell_20_37
  · exact cell_20_38
  · exact (block_rank_le 20 _).trans (rank_le_nominal 20 _)

theorem grade_20 : (∑ u ∈ Finset.range (81-20), (CJ0.blockMatrix source 20 ((u : ℤ)-24)).rank) ≤ 5735 := by
  refine (Finset.sum_le_sum fun u _ => bound_20 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_20)]
  decide +kernel

private def matrix_21_36 : CJ1.Block where
  bank := .leftLow
  cap := 151
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_21_36 : (CJ0.blockMatrix source 21 ((36 : ℤ)-24)).rank ≤ 151 :=
  Fast.cell (z := matrix_21_36) (Fast.bands [(0, 0, 4), (1, 1, 5), (2, 2, 6), (3, 3, 7), (4, 4, 8), (5, 5, 9), (6, 6, 10), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 10), (13, 13, 9), (14, 14, 8), (15, 15, 7), (16, 16, 6), (17, 17, 5), (18, 18, 4), (19, 19, 3), (20, 20, 2), (21, 21, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_21_37 : CJ1.Block where
  bank := .leftLow
  cap := 142
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_21_37 : (CJ0.blockMatrix source 21 ((37 : ℤ)-24)).rank ≤ 142 :=
  Fast.cell (z := matrix_21_37) (Fast.bands [(0, 0, 4), (1, 1, 5), (2, 2, 6), (3, 3, 7), (4, 4, 8), (5, 5, 9), (6, 6, 10), (7, 7, 11), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 10), (13, 13, 9), (14, 14, 8), (15, 15, 7), (16, 16, 6), (17, 17, 5), (18, 18, 4), (19, 19, 3), (20, 20, 2), (21, 21, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_21 (u : ℕ) : ℕ :=
  match u with
  | 36 => 151
  | 37 => 142
  | u => nominal 21 u

private theorem bound_21 (u : ℕ) :
    (CJ0.blockMatrix source 21 ((u : ℤ)-24)).rank ≤ allowance_21 u := by
  unfold allowance_21
  split
  · exact cell_21_36
  · exact cell_21_37
  · exact (block_rank_le 21 _).trans (rank_le_nominal 21 _)

theorem grade_21 : (∑ u ∈ Finset.range (81-21), (CJ0.blockMatrix source 21 ((u : ℤ)-24)).rank) ≤ 5724 := by
  refine (Finset.sum_le_sum fun u _ => bound_21 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_21)]
  decide +kernel

private def matrix_22_35 : CJ1.Block where
  bank := .leftLow
  cap := 153
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_22_35 : (CJ0.blockMatrix source 22 ((35 : ℤ)-24)).rank ≤ 153 :=
  Fast.cell (z := matrix_22_35) (Fast.bands [(0, 0, 3), (1, 1, 4), (2, 2, 5), (3, 3, 6), (4, 4, 7), (5, 5, 8), (6, 6, 9), (7, 7, 10), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 10), (14, 14, 9), (15, 15, 8), (16, 16, 7), (17, 17, 6), (18, 18, 5), (19, 19, 4), (20, 20, 3), (21, 21, 2), (22, 22, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_22_36 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_22_36 : (CJ0.blockMatrix source 22 ((36 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_22_36) (Fast.bands [(0, 0, 3), (1, 1, 4), (2, 2, 5), (3, 3, 6), (4, 4, 7), (5, 5, 8), (6, 6, 9), (7, 7, 10), (8, 8, 11), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 10), (14, 14, 9), (15, 15, 8), (16, 16, 7), (17, 17, 6), (18, 18, 5), (19, 19, 4), (20, 20, 3), (21, 21, 2), (22, 22, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_22 (u : ℕ) : ℕ :=
  match u with
  | 35 => 153
  | 36 => 143
  | u => nominal 22 u

private theorem bound_22 (u : ℕ) :
    (CJ0.blockMatrix source 22 ((u : ℤ)-24)).rank ≤ allowance_22 u := by
  unfold allowance_22
  split
  · exact cell_22_35
  · exact cell_22_36
  · exact (block_rank_le 22 _).trans (rank_le_nominal 22 _)

theorem grade_22 : (∑ u ∈ Finset.range (81-22), (CJ0.blockMatrix source 22 ((u : ℤ)-24)).rank) ≤ 5670 := by
  refine (Finset.sum_le_sum fun u _ => bound_22 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_22)]
  decide +kernel

private def matrix_23_34 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_23_34 : (CJ0.blockMatrix source 23 ((34 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_23_34) (Fast.bands [(0, 0, 2), (1, 1, 3), (2, 2, 4), (3, 3, 5), (4, 4, 6), (5, 5, 7), (6, 6, 8), (7, 7, 9), (8, 8, 10), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 10), (15, 15, 9), (16, 16, 8), (17, 17, 7), (18, 18, 6), (19, 19, 5), (20, 20, 4), (21, 21, 3), (22, 22, 2), (23, 23, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_23_35 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_23_35 : (CJ0.blockMatrix source 23 ((35 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_23_35) (Fast.bands [(0, 0, 2), (1, 1, 3), (2, 2, 4), (3, 3, 5), (4, 4, 6), (5, 5, 7), (6, 6, 8), (7, 7, 9), (8, 8, 10), (9, 9, 11), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 10), (15, 15, 9), (16, 16, 8), (17, 17, 7), (18, 18, 6), (19, 19, 5), (20, 20, 4), (21, 21, 3), (22, 22, 2), (23, 23, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_23 (u : ℕ) : ℕ :=
  match u with
  | 34 => 154
  | 35 => 143
  | u => nominal 23 u

private theorem bound_23 (u : ℕ) :
    (CJ0.blockMatrix source 23 ((u : ℤ)-24)).rank ≤ allowance_23 u := by
  unfold allowance_23
  split
  · exact cell_23_34
  · exact cell_23_35
  · exact (block_rank_le 23 _).trans (rank_le_nominal 23 _)

theorem grade_23 : (∑ u ∈ Finset.range (81-23), (CJ0.blockMatrix source 23 ((u : ℤ)-24)).rank) ≤ 5576 := by
  refine (Finset.sum_le_sum fun u _ => bound_23 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_23)]
  decide +kernel

private def matrix_24_33 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_24_33 : (CJ0.blockMatrix source 24 ((33 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_24_33) (Fast.bands [(0, 0, 1), (1, 1, 2), (2, 2, 3), (3, 3, 4), (4, 4, 5), (5, 5, 6), (6, 6, 7), (7, 7, 8), (8, 8, 9), (9, 9, 10), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 10), (16, 16, 9), (17, 17, 8), (18, 18, 7), (19, 19, 6), (20, 20, 5), (21, 21, 4), (22, 22, 3), (23, 23, 2), (24, 24, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_24_34 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_24_34 : (CJ0.blockMatrix source 24 ((34 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_24_34) (Fast.bands [(0, 0, 1), (1, 1, 2), (2, 2, 3), (3, 3, 4), (4, 4, 5), (5, 5, 6), (6, 6, 7), (7, 7, 8), (8, 8, 9), (9, 9, 10), (10, 10, 11), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 10), (16, 16, 9), (17, 17, 8), (18, 18, 7), (19, 19, 6), (20, 20, 5), (21, 21, 4), (22, 22, 3), (23, 23, 2), (24, 24, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_24 (u : ℕ) : ℕ :=
  match u with
  | 33 => 154
  | 34 => 143
  | u => nominal 24 u

private theorem bound_24 (u : ℕ) :
    (CJ0.blockMatrix source 24 ((u : ℤ)-24)).rank ≤ allowance_24 u := by
  unfold allowance_24
  split
  · exact cell_24_33
  · exact cell_24_34
  · exact (block_rank_le 24 _).trans (rank_le_nominal 24 _)

theorem grade_24 : (∑ u ∈ Finset.range (81-24), (CJ0.blockMatrix source 24 ((u : ℤ)-24)).rank) ≤ 5445 := by
  refine (Finset.sum_le_sum fun u _ => bound_24 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_24)]
  decide +kernel

private def matrix_25_32 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_25_32 : (CJ0.blockMatrix source 25 ((32 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_25_32) (Fast.bands [(1, 1, 1), (2, 2, 2), (3, 3, 3), (4, 4, 4), (5, 5, 5), (6, 6, 6), (7, 7, 7), (8, 8, 8), (9, 9, 9), (10, 10, 10), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 10), (17, 17, 9), (18, 18, 8), (19, 19, 7), (20, 20, 6), (21, 21, 5), (22, 22, 4), (23, 23, 3), (24, 24, 2), (25, 25, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_25_33 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_25_33 : (CJ0.blockMatrix source 25 ((33 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_25_33) (Fast.bands [(1, 1, 1), (2, 2, 2), (3, 3, 3), (4, 4, 4), (5, 5, 5), (6, 6, 6), (7, 7, 7), (8, 8, 8), (9, 9, 9), (10, 10, 10), (11, 11, 11), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 10), (17, 17, 9), (18, 18, 8), (19, 19, 7), (20, 20, 6), (21, 21, 5), (22, 22, 4), (23, 23, 3), (24, 24, 2), (25, 25, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_25 (u : ℕ) : ℕ :=
  match u with
  | 32 => 154
  | 33 => 143
  | u => nominal 25 u

private theorem bound_25 (u : ℕ) :
    (CJ0.blockMatrix source 25 ((u : ℤ)-24)).rank ≤ allowance_25 u := by
  unfold allowance_25
  split
  · exact cell_25_32
  · exact cell_25_33
  · exact (block_rank_le 25 _).trans (rank_le_nominal 25 _)

theorem grade_25 : (∑ u ∈ Finset.range (81-25), (CJ0.blockMatrix source 25 ((u : ℤ)-24)).rank) ≤ 5280 := by
  refine (Finset.sum_le_sum fun u _ => bound_25 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_25)]
  decide +kernel

private def matrix_26_31 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_26_31 : (CJ0.blockMatrix source 26 ((31 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_26_31) (Fast.bands [(2, 2, 1), (3, 3, 2), (4, 4, 3), (5, 5, 4), (6, 6, 5), (7, 7, 6), (8, 8, 7), (9, 9, 8), (10, 10, 9), (11, 11, 10), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 10), (18, 18, 9), (19, 19, 8), (20, 20, 7), (21, 21, 6), (22, 22, 5), (23, 23, 4), (24, 24, 3), (25, 25, 2), (26, 26, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_26_32 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_26_32 : (CJ0.blockMatrix source 26 ((32 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_26_32) (Fast.bands [(2, 2, 1), (3, 3, 2), (4, 4, 3), (5, 5, 4), (6, 6, 5), (7, 7, 6), (8, 8, 7), (9, 9, 8), (10, 10, 9), (11, 11, 10), (12, 12, 11), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 10), (18, 18, 9), (19, 19, 8), (20, 20, 7), (21, 21, 6), (22, 22, 5), (23, 23, 4), (24, 24, 3), (25, 25, 2), (26, 26, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_26 (u : ℕ) : ℕ :=
  match u with
  | 31 => 154
  | 32 => 143
  | u => nominal 26 u

private theorem bound_26 (u : ℕ) :
    (CJ0.blockMatrix source 26 ((u : ℤ)-24)).rank ≤ allowance_26 u := by
  unfold allowance_26
  split
  · exact cell_26_31
  · exact cell_26_32
  · exact (block_rank_le 26 _).trans (rank_le_nominal 26 _)

theorem grade_26 : (∑ u ∈ Finset.range (81-26), (CJ0.blockMatrix source 26 ((u : ℤ)-24)).rank) ≤ 5115 := by
  refine (Finset.sum_le_sum fun u _ => bound_26 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_26)]
  decide +kernel

private def matrix_27_30 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_27_30 : (CJ0.blockMatrix source 27 ((30 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_27_30) (Fast.bands [(3, 3, 1), (4, 4, 2), (5, 5, 3), (6, 6, 4), (7, 7, 5), (8, 8, 6), (9, 9, 7), (10, 10, 8), (11, 11, 9), (12, 12, 10), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 10), (19, 19, 9), (20, 20, 8), (21, 21, 7), (22, 22, 6), (23, 23, 5), (24, 24, 4), (25, 25, 3), (26, 26, 2), (27, 27, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_27_31 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_27_31 : (CJ0.blockMatrix source 27 ((31 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_27_31) (Fast.bands [(3, 3, 1), (4, 4, 2), (5, 5, 3), (6, 6, 4), (7, 7, 5), (8, 8, 6), (9, 9, 7), (10, 10, 8), (11, 11, 9), (12, 12, 10), (13, 13, 11), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 10), (19, 19, 9), (20, 20, 8), (21, 21, 7), (22, 22, 6), (23, 23, 5), (24, 24, 4), (25, 25, 3), (26, 26, 2), (27, 27, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_27 (u : ℕ) : ℕ :=
  match u with
  | 30 => 154
  | 31 => 143
  | u => nominal 27 u

private theorem bound_27 (u : ℕ) :
    (CJ0.blockMatrix source 27 ((u : ℤ)-24)).rank ≤ allowance_27 u := by
  unfold allowance_27
  split
  · exact cell_27_30
  · exact cell_27_31
  · exact (block_rank_le 27 _).trans (rank_le_nominal 27 _)

theorem grade_27 : (∑ u ∈ Finset.range (81-27), (CJ0.blockMatrix source 27 ((u : ℤ)-24)).rank) ≤ 4950 := by
  refine (Finset.sum_le_sum fun u _ => bound_27 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_27)]
  decide +kernel

private def matrix_28_29 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_28_29 : (CJ0.blockMatrix source 28 ((29 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_28_29) (Fast.bands [(4, 4, 1), (5, 5, 2), (6, 6, 3), (7, 7, 4), (8, 8, 5), (9, 9, 6), (10, 10, 7), (11, 11, 8), (12, 12, 9), (13, 13, 10), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 10), (20, 20, 9), (21, 21, 8), (22, 22, 7), (23, 23, 6), (24, 24, 5), (25, 25, 4), (26, 26, 3), (27, 27, 2), (28, 28, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_28_30 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_28_30 : (CJ0.blockMatrix source 28 ((30 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_28_30) (Fast.bands [(4, 4, 1), (5, 5, 2), (6, 6, 3), (7, 7, 4), (8, 8, 5), (9, 9, 6), (10, 10, 7), (11, 11, 8), (12, 12, 9), (13, 13, 10), (14, 14, 11), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 10), (20, 20, 9), (21, 21, 8), (22, 22, 7), (23, 23, 6), (24, 24, 5), (25, 25, 4), (26, 26, 3), (27, 27, 2), (28, 28, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_28 (u : ℕ) : ℕ :=
  match u with
  | 29 => 154
  | 30 => 143
  | u => nominal 28 u

private theorem bound_28 (u : ℕ) :
    (CJ0.blockMatrix source 28 ((u : ℤ)-24)).rank ≤ allowance_28 u := by
  unfold allowance_28
  split
  · exact cell_28_29
  · exact cell_28_30
  · exact (block_rank_le 28 _).trans (rank_le_nominal 28 _)

theorem grade_28 : (∑ u ∈ Finset.range (81-28), (CJ0.blockMatrix source 28 ((u : ℤ)-24)).rank) ≤ 4785 := by
  refine (Finset.sum_le_sum fun u _ => bound_28 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_28)]
  decide +kernel

private def matrix_29_28 : CJ1.Block where
  bank := .leftLow
  cap := 154
  free := [(11, 0), (11, 1)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11], [0, 0, 0, 0, 0, 0, 0, 0, 0, 10], [0, 0, 0, 0, 0, 0, 0, 0, 9], [0, 0, 0, 0, 0, 0, 0, 8], [0, 0, 0, 0, 0, 0, 7], [0, 0, 0, 0, 0, 6], [0, 0, 0, 0, 5], [0, 0, 0, 4], [0, 0, 3], [0, 2], [1]],
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1]]
  ]
private theorem cell_29_28 : (CJ0.blockMatrix source 29 ((28 : ℤ)-24)).rank ≤ 154 :=
  Fast.cell (z := matrix_29_28) (Fast.bands [(5, 5, 1), (6, 6, 2), (7, 7, 3), (8, 8, 4), (9, 9, 5), (10, 10, 6), (11, 11, 7), (12, 12, 8), (13, 13, 9), (14, 14, 10), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 11), (20, 20, 10), (21, 21, 9), (22, 22, 8), (23, 23, 7), (24, 24, 6), (25, 25, 5), (26, 26, 4), (27, 27, 3), (28, 28, 2), (29, 29, 1)]) (by decide +kernel) (by decide +kernel)

private def matrix_29_29 : CJ1.Block where
  bank := .leftLow
  cap := 143
  free := [(11, 0)]
  vectors := [
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 0, 1], [0, 0, 1], [0, 1], [1]]
  ]
private theorem cell_29_29 : (CJ0.blockMatrix source 29 ((29 : ℤ)-24)).rank ≤ 143 :=
  Fast.cell (z := matrix_29_29) (Fast.bands [(5, 5, 1), (6, 6, 2), (7, 7, 3), (8, 8, 4), (9, 9, 5), (10, 10, 6), (11, 11, 7), (12, 12, 8), (13, 13, 9), (14, 14, 10), (15, 15, 11), (16, 16, 11), (17, 17, 11), (18, 18, 11), (19, 19, 11), (20, 20, 10), (21, 21, 9), (22, 22, 8), (23, 23, 7), (24, 24, 6), (25, 25, 5), (26, 26, 4), (27, 27, 3), (28, 28, 2), (29, 29, 1)]) (by decide +kernel) (by decide +kernel)

private def allowance_29 (u : ℕ) : ℕ :=
  match u with
  | 28 => 154
  | 29 => 143
  | u => nominal 29 u

private theorem bound_29 (u : ℕ) :
    (CJ0.blockMatrix source 29 ((u : ℤ)-24)).rank ≤ allowance_29 u := by
  unfold allowance_29
  split
  · exact cell_29_28
  · exact cell_29_29
  · exact (block_rank_le 29 _).trans (rank_le_nominal 29 _)

theorem grade_29 : (∑ u ∈ Finset.range (81-29), (CJ0.blockMatrix source 29 ((u : ℤ)-24)).rank) ≤ 4620 := by
  refine (Finset.sum_le_sum fun u _ => bound_29 u).trans_eq ?_
  rw [← CJ1.total_eq_sum (allowance_29)]
  decide +kernel

end Front6960ListBank
